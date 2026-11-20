use crate::actions::ActionExecutor;
use crate::types::*;
use crossbeam_channel::{Receiver, Sender};
use parking_lot::RwLock;
use std::collections::{HashMap, HashSet, VecDeque};
use std::fs::OpenOptions;
use std::io::Write;
use std::path::PathBuf;
use std::sync::atomic::{AtomicBool, AtomicPtr, AtomicU32, Ordering};
use std::sync::Arc;
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};
use tauri::{AppHandle, Emitter};
use windows_sys::Win32::Foundation::*;
use windows_sys::Win32::System::LibraryLoader::GetModuleHandleW;
use windows_sys::Win32::System::Threading::{GetCurrentProcessId, GetCurrentThreadId};
use windows_sys::Win32::UI::Input::KeyboardAndMouse::*;
use windows_sys::Win32::UI::Input::*;
use windows_sys::Win32::UI::WindowsAndMessaging::*;

const LLKHF_EXTENDED_FLAG: u32 = 0x00000001;
const LLKHF_INJECTED_FLAG: u32 = 0x00000010;
const LLKHF_UP_FLAG: u32 = 0x00000080;

// Global Raw Input sink window and device tracking
static RAW_INPUT_HWND: AtomicPtr<std::ffi::c_void> = AtomicPtr::new(std::ptr::null_mut());
static LAST_HARDWARE_KEYBOARD: parking_lot::RwLock<Option<String>> = parking_lot::RwLock::new(None);
static DETECTING_KEYBOARD: AtomicBool = AtomicBool::new(false);
static DEVICE_HANDLE_CACHE: parking_lot::RwLock<Option<HashMap<isize, String>>> = parking_lot::RwLock::new(None);

// ---- Deferred device attribution (fix for "first press goes through") ----
// Raw Input "sink" events (sent when NumDeck is NOT the foreground app) arrive AFTER the
// low-level hook has already run, so inside the hook we cannot know which keyboard produced
// the key. Instead of guessing from the previous key, the hook parks matched deck keys here
// (and suppresses them); once the WM_INPUT for the same key arrives we know the real device
// and either run the deck action (target device) or re-inject the key (any other keyboard).
const RI_KEY_BREAK_FLAG: u32 = 0x01;
const RI_KEY_E0_FLAG: u32 = 0x02;
const PENDING_EXPIRY_MS: u64 = 150;

static RAW_REGISTERED: AtomicBool = AtomicBool::new(false);
static PENDING_KEYS: parking_lot::Mutex<VecDeque<PendingKey>> = parking_lot::Mutex::new(VecDeque::new());

struct PendingKey {
    key_id: String,
    vk_code: u32,
    scan_code: u32,
    is_extended: bool,
    is_key_down: bool,
    queued_at: Instant,
}

/// Diagnostic telemetry record capturing all 12 requested fields
#[derive(Debug, Clone)]
pub struct TelemetryRecord {
    pub timestamp_ms: u64,
    pub fg_window: String,
    pub fg_pid: u32,
    pub is_self_foreground: bool,
    pub vk_code: u32,
    pub vk_name: String,
    pub scan_code: u32,
    pub is_extended: bool,
    pub is_key_down: bool,
    pub is_injected: bool,
    pub numlock_on: bool,
    pub matched_logical_key: Option<String>,
    pub deck_mode_enabled: bool,
    pub event_suppressed: bool,
    pub queued_action: Option<String>,
    pub hook_duration_us: u64,
}

/// Messages routed from the fast Win32 hook procedure to the asynchronous worker thread
pub enum WorkerMessage {
    ExecuteAction {
        key_id: String,
        action: ActionConfig,
    },
    Telemetry(TelemetryRecord),
    CalibrationKeyCaptured(KeySignature),
    EmergencyReset,
    KeyboardDeviceDetected(String),
}

/// State shared between Tauri commands, Low-Level Hook, and Action Executor
pub struct KeyboardEngineState {
    pub mode: RwLock<EngineMode>,
    pub calibration: RwLock<CalibrationProfile>,
    pub active_profile: RwLock<Profile>,
    pub active_folder_id: RwLock<Option<String>>,
    pub pressed_keys: RwLock<HashSet<String>>,
    pub emergency_shortcut_enabled: AtomicBool,
    pub sound_feedback: AtomicBool,
    pub esc_press_count: AtomicU32,
    pub last_esc_time: RwLock<Instant>,
    pub diagnostics_active: AtomicBool,
    pub target_keyboard_device: RwLock<Option<String>>,
}

impl KeyboardEngineState {
    pub fn new(
        calibration: CalibrationProfile,
        default_profile: Profile,
        initial_deck_mode: bool,
        target_keyboard_device: Option<String>,
    ) -> Self {
        Self {
            mode: RwLock::new(if initial_deck_mode {
                EngineMode::Deck
            } else {
                EngineMode::Normal
            }),
            calibration: RwLock::new(calibration),
            active_profile: RwLock::new(default_profile),
            active_folder_id: RwLock::new(None),
            pressed_keys: RwLock::new(HashSet::new()),
            emergency_shortcut_enabled: AtomicBool::new(true),
            sound_feedback: AtomicBool::new(true),
            esc_press_count: AtomicU32::new(0),
            last_esc_time: RwLock::new(Instant::now()),
            diagnostics_active: AtomicBool::new(true),
            target_keyboard_device: RwLock::new(target_keyboard_device),
        }
    }
}

pub fn start_detecting_keyboard() {
    DETECTING_KEYBOARD.store(true, Ordering::SeqCst);
}

pub fn stop_detecting_keyboard() {
    DETECTING_KEYBOARD.store(false, Ordering::SeqCst);
}

/// Enumerate all connected physical and virtual keyboards on Windows using Raw Input
pub fn enumerate_keyboards() -> Vec<KeyboardDeviceInfo> {
    let mut results = Vec::new();
    unsafe {
        let mut num_devices = 0u32;
        let cb_size = std::mem::size_of::<RAWINPUTDEVICELIST>() as u32;
        let _ = GetRawInputDeviceList(std::ptr::null_mut(), &mut num_devices, cb_size);
        if num_devices == 0 {
            return results;
        }
        let mut devices: Vec<RAWINPUTDEVICELIST> = vec![std::mem::zeroed(); num_devices as usize];
        let count = GetRawInputDeviceList(devices.as_mut_ptr(), &mut num_devices, cb_size);
        if count == u32::MAX {
            return results;
        }

        let mut seen_ids = HashSet::new();

        for dev in devices.iter().take(count as usize) {
            if dev.dwType != RIM_TYPEKEYBOARD {
                continue;
            }
            let mut name_size = 0u32;
            GetRawInputDeviceInfoW(dev.hDevice, RIDI_DEVICENAME, std::ptr::null_mut(), &mut name_size);
            if name_size == 0 {
                continue;
            }
            let mut name_buf = vec![0u16; name_size as usize];
            let read_len = GetRawInputDeviceInfoW(dev.hDevice, RIDI_DEVICENAME, name_buf.as_mut_ptr() as _, &mut name_size);
            if read_len == u32::MAX {
                continue;
            }
            let raw_path = String::from_utf16_lossy(&name_buf)
                .trim_end_matches('\0')
                .trim()
                .to_string();

            if raw_path.is_empty() {
                continue;
            }

            let upper_path = raw_path.to_uppercase();
            let is_virtual = upper_path.contains("MICROSOFT KEYBOARD RID") || upper_path.contains("ROOT#");
            let is_internal = upper_path.contains("ACPI#MSFT") || upper_path.contains("PNP0303") || upper_path.contains("I8042PRT");

            let id = if let Some(vid_idx) = upper_path.find("VID_") {
                let from_vid = &upper_path[vid_idx..];
                let end = if let Some(mi_idx) = from_vid.find("&MI_") {
                    mi_idx
                } else if let Some(hash_idx) = from_vid.find('#') {
                    hash_idx
                } else if let Some(slash_idx) = from_vid.find('/') {
                    slash_idx
                } else {
                    from_vid.len()
                };
                from_vid[..end].to_string()
            } else if is_internal {
                "INTERNAL_KEYBOARD".to_string()
            } else if is_virtual {
                "VIRTUAL_KEYBOARD".to_string()
            } else {
                raw_path.clone()
            };

            // Avoid duplicate entries for composite device interfaces
            if seen_ids.contains(&id) {
                continue;
            }
            seen_ids.insert(id.clone());

            let name = if is_internal {
                "Internal Laptop Keyboard (Standard PS/2)".to_string()
            } else if is_virtual {
                "Virtual / Remote Desktop Keyboard".to_string()
            } else if id.starts_with("VID_") {
                let parts: Vec<&str> = id.split('&').collect();
                let vid = parts.get(0).unwrap_or(&"VID_????").replace("VID_", "");
                let pid = parts.get(1).unwrap_or(&"PID_????").replace("PID_", "");
                format!("USB Keyboard / Numpad [VID: {}, PID: {}]", vid, pid)
            } else {
                format!("Keyboard Device [{}]", id)
            };

            results.push(KeyboardDeviceInfo {
                id,
                name,
                raw_path,
                is_internal,
                is_virtual,
            });
        }
    }

    results.sort_by_key(|d| if d.is_virtual { 2 } else if d.is_internal { 1 } else { 0 });
    results
}

/// Convert a device handle from Raw Input into a unique normalized device identifier
fn resolve_device_id_from_handle(hdevice: HANDLE) -> String {
    if hdevice.is_null() {
        return "SYNTHETIC".to_string();
    }
    let key = hdevice as isize;
    {
        let cache = DEVICE_HANDLE_CACHE.read();
        if let Some(ref map) = *cache {
            if let Some(cached) = map.get(&key) {
                return cached.clone();
            }
        }
    }

    let mut name_size = 0u32;
    unsafe {
        GetRawInputDeviceInfoW(hdevice, RIDI_DEVICENAME, std::ptr::null_mut(), &mut name_size);
        if name_size > 0 {
            let mut name_buf = vec![0u16; name_size as usize];
            let read_len = GetRawInputDeviceInfoW(hdevice, RIDI_DEVICENAME, name_buf.as_mut_ptr() as _, &mut name_size);
            if read_len != u32::MAX {
                let raw_path = String::from_utf16_lossy(&name_buf)
                    .trim_end_matches('\0')
                    .trim()
                    .to_uppercase();

                let id = if let Some(vid_idx) = raw_path.find("VID_") {
                    let from_vid = &raw_path[vid_idx..];
                    let end = if let Some(mi_idx) = from_vid.find("&MI_") {
                        mi_idx
                    } else if let Some(hash_idx) = from_vid.find('#') {
                        hash_idx
                    } else if let Some(slash_idx) = from_vid.find('/') {
                        slash_idx
                    } else {
                        from_vid.len()
                    };
                    from_vid[..end].to_string()
                } else if raw_path.contains("ACPI#MSFT") || raw_path.contains("PNP0303") || raw_path.contains("I8042PRT") {
                    "INTERNAL_KEYBOARD".to_string()
                } else if raw_path.contains("MICROSOFT KEYBOARD RID") || raw_path.contains("ROOT#") {
                    "VIRTUAL_KEYBOARD".to_string()
                } else {
                    raw_path
                };

                let mut cache = DEVICE_HANDLE_CACHE.write();
                if cache.is_none() {
                    *cache = Some(HashMap::new());
                }
                cache.as_mut().unwrap().insert(key, id.clone());
                return id;
            }
        }
    }
    "UNKNOWN".to_string()
}

/// Process a WM_INPUT lParam, update the most recent hardware keyboard, trigger detection if active,
/// and (when `resolve_pending` is true) resolve deck keys that were parked by the hook.
fn process_raw_input_lparam(lparam: LPARAM, ctx: Option<&HookContext>, resolve_pending: bool) {
    unsafe {
        let mut size = std::mem::size_of::<RAWINPUT>() as u32;
        let mut raw: RAWINPUT = std::mem::zeroed();
        let res = GetRawInputData(
            lparam as _,
            RID_INPUT,
            &mut raw as *mut _ as _,
            &mut size,
            std::mem::size_of::<RAWINPUTHEADER>() as u32,
        );
        if res != u32::MAX && raw.header.dwType == RIM_TYPEKEYBOARD {
            let dev_id = resolve_device_id_from_handle(raw.header.hDevice);
            *LAST_HARDWARE_KEYBOARD.write() = Some(dev_id.clone());

            if DETECTING_KEYBOARD.swap(false, Ordering::SeqCst) {
                if let Some(c) = ctx {
                    let _ = c.worker_tx.send(WorkerMessage::KeyboardDeviceDetected(dev_id.clone()));
                }
            }

            if resolve_pending {
                if let Some(c) = ctx {
                    let kb = raw.data.keyboard;
                    let flags = kb.Flags as u32;
                    resolve_pending_key(
                        c,
                        &dev_id,
                        kb.MakeCode as u32,
                        (flags & RI_KEY_BREAK_FLAG) != 0,
                        (flags & RI_KEY_E0_FLAG) != 0,
                    );
                }
            }
        }
    }
}

/// Re-send a key that the hook suppressed but that turned out NOT to belong to the target device.
/// The event is marked injected by Windows, so our hook lets it straight through.
fn reinject_key(p: &PendingKey) {
    unsafe {
        let mut input: INPUT = std::mem::zeroed();
        input.r#type = INPUT_KEYBOARD;
        input.Anonymous.ki.wVk = p.vk_code as u16;
        input.Anonymous.ki.wScan = p.scan_code as u16;
        let mut flags = 0u32;
        if p.is_extended {
            flags |= KEYEVENTF_EXTENDEDKEY;
        }
        if !p.is_key_down {
            flags |= KEYEVENTF_KEYUP;
        }
        input.Anonymous.ki.dwFlags = flags;
        SendInput(1, &mut input, std::mem::size_of::<INPUT>() as i32);
    }
}

/// Called for every keyboard WM_INPUT: pair it with the parked key it belongs to (if any).
fn resolve_pending_key(ctx: &HookContext, dev_id: &str, make_code: u32, is_break: bool, is_e0: bool) {
    let mut stale: Vec<PendingKey> = Vec::new();
    let matched: Option<PendingKey>;
    {
        let mut q = PENDING_KEYS.lock();
        let pos = q.iter().position(|p| {
            p.scan_code == make_code && p.is_key_down == !is_break && p.is_extended == is_e0
        });
        if let Some(i) = pos {
            // Anything parked before this one never got its raw event: let it through.
            for _ in 0..i {
                if let Some(old) = q.pop_front() {
                    stale.push(old);
                }
            }
            matched = q.pop_front();
        } else {
            matched = None;
        }
    }
    for old in &stale {
        reinject_key(old);
    }
    if let Some(p) = matched {
        finish_pending_key(ctx, p, dev_id);
    }
}

/// Safety net: if a parked key never gets its raw event, release it after a short time.
fn flush_expired_pending() {
    let mut expired: Vec<PendingKey> = Vec::new();
    {
        let mut q = PENDING_KEYS.lock();
        while let Some(front) = q.front() {
            if front.queued_at.elapsed() > Duration::from_millis(PENDING_EXPIRY_MS) {
                if let Some(p) = q.pop_front() {
                    expired.push(p);
                }
            } else {
                break;
            }
        }
    }
    for p in &expired {
        reinject_key(p);
    }
}

/// The device is now known: run the deck action for the target keyboard, or pass the key on.
fn finish_pending_key(ctx: &HookContext, p: PendingKey, dev_id: &str) {
    let target_device = ctx.state.target_keyboard_device.read().clone();
    let is_target = match target_device {
        Some(ref target) if target != "all" && !target.is_empty() => {
            dev_id.eq_ignore_ascii_case(target) || dev_id.contains(target.as_str())
        }
        _ => true,
    };

    if !is_target || *ctx.state.mode.read() != EngineMode::Deck {
        reinject_key(&p);
        return;
    }

    let mut queued_action_str = None;

    if p.is_key_down {
        let is_first_press = ctx.state.pressed_keys.write().insert(p.key_id.clone());
        if is_first_press {
            let profile = ctx.state.active_profile.read();
            let active_folder = ctx.state.active_folder_id.read();
            let assignment = if let Some(folder_id) = active_folder.as_ref() {
                profile
                    .folders
                    .iter()
                    .find(|f| f.id == *folder_id)
                    .and_then(|f| f.keys.get(&p.key_id))
                    .or_else(|| profile.keys.get(&p.key_id))
            } else {
                profile.keys.get(&p.key_id)
            };
            if let Some(assign) = assignment {
                if let Some(action) = &assign.action {
                    queued_action_str = Some(format!("{:?}", action));
                    let _ = ctx.worker_tx.send(WorkerMessage::ExecuteAction {
                        key_id: p.key_id.clone(),
                        action: action.clone(),
                    });
                }
            }
        }
    } else {
        ctx.state.pressed_keys.write().remove(&p.key_id);
    }

    let (fg_window, fg_pid, is_self_foreground) = get_foreground_info();
    let numlock_on = unsafe { (GetKeyState(VK_NUMLOCK as i32) & 1) != 0 };
    let _ = ctx.worker_tx.send(WorkerMessage::Telemetry(TelemetryRecord {
        timestamp_ms: current_time_ms(),
        fg_window,
        fg_pid,
        is_self_foreground,
        vk_code: p.vk_code,
        vk_name: vk_code_to_name(p.vk_code),
        scan_code: p.scan_code,
        is_extended: p.is_extended,
        is_key_down: p.is_key_down,
        is_injected: false,
        numlock_on,
        matched_logical_key: Some(p.key_id.clone()),
        deck_mode_enabled: true,
        event_suppressed: true,
        queued_action: queued_action_str,
        hook_duration_us: 0,
    }));
}

// Global static holder for hook context accessed by the Win32 C-callback
static HOOK_DATA: parking_lot::RwLock<Option<HookContext>> = parking_lot::RwLock::new(None);

struct HookContext {
    state: Arc<KeyboardEngineState>,
    worker_tx: Sender<WorkerMessage>,
}

pub struct KeyboardEngine {
    state: Arc<KeyboardEngineState>,
    hook_thread_id: Arc<AtomicU32>,
    pub worker_tx: Sender<WorkerMessage>,
}

impl KeyboardEngine {
    pub fn start(
        app_handle: AppHandle,
        calibration: CalibrationProfile,
        default_profile: Profile,
        initial_deck_mode: bool,
        target_keyboard_device: Option<String>,
    ) -> Self {
        let state = Arc::new(KeyboardEngineState::new(
            calibration,
            default_profile,
            initial_deck_mode,
            target_keyboard_device,
        ));
        let (worker_tx, worker_rx) = crossbeam_channel::unbounded::<WorkerMessage>();
        let hook_thread_id = Arc::new(AtomicU32::new(0));

        // 1. Start Off-Thread Worker Loop (handles File I/O, IPC emissions, and Action execution)
        let worker_state = Arc::clone(&state);
        let worker_app = app_handle.clone();
        thread::Builder::new()
            .name("numdeck-action-worker".to_string())
            .spawn(move || {
                Self::worker_loop(worker_rx, worker_state, worker_app);
            })
            .expect("Failed to spawn action worker thread");

        // 2. Set up global hook context (only lightweight sender and shared state)
        *HOOK_DATA.write() = Some(HookContext {
            state: Arc::clone(&state),
            worker_tx: worker_tx.clone(),
        });

        // 3. Start Dedicated Win32 Keyboard Hook Thread with Message Pump
        let thread_id_clone = Arc::clone(&hook_thread_id);
        thread::Builder::new()
            .name("numdeck-hook-thread".to_string())
            .spawn(move || {
                Self::hook_thread_loop(thread_id_clone);
            })
            .expect("Failed to spawn hook thread");

        Self {
            state,
            hook_thread_id,
            worker_tx,
        }
    }

    pub fn state(&self) -> Arc<KeyboardEngineState> {
        Arc::clone(&self.state)
    }

    /// Background thread that handles logging, action execution, and UI IPC emissions
    /// Completely decoupling heavy work and IPC from the critical low-level keyboard hook.
    fn worker_loop(
        rx: Receiver<WorkerMessage>,
        state: Arc<KeyboardEngineState>,
        app: AppHandle,
    ) {
        log::info!("Off-thread action/telemetry worker initialized.");

        // Open local debug log file for streaming telemetry
        let local_log_path = PathBuf::from("engine_debug.log");
        let appdata_log_path = std::env::var("APPDATA")
            .ok()
            .map(|p| PathBuf::from(p).join("NumpadDeck").join("engine_debug.log"));

        let mut log_file = OpenOptions::new()
            .create(true)
            .append(true)
            .open(&local_log_path)
            .ok();

        while let Ok(msg) = rx.recv() {
            match msg {
                WorkerMessage::ExecuteAction { key_id, action } => {
                    log::info!("Executing assigned action for key '{}': {:?}", key_id, action);
                    let action_summary = format!("{:?}", action);

                    match action {
                        ActionConfig::ToggleDeckMode => {
                            let mut mode_guard = state.mode.write();
                            let new_mode = match *mode_guard {
                                EngineMode::Deck => EngineMode::Normal,
                                _ => EngineMode::Deck,
                            };
                            *mode_guard = new_mode;
                            drop(mode_guard);

                            let is_deck = new_mode == EngineMode::Deck;
                            log::info!("Deck mode toggled via action to: {:?}", new_mode);
                            let _ = app.emit("deck-mode-changed", is_deck);
                        }
                        ActionConfig::SwitchProfile { profile_id } => {
                            log::info!("Switching profile to: {}", profile_id);
                            let _ = app.emit("request-switch-profile", profile_id);
                        }
                        ActionConfig::NavigateFolder { folder_id } => {
                            *state.active_folder_id.write() = Some(folder_id.clone());
                            let _ = app.emit("folder-changed", Some(folder_id));
                        }
                        ActionConfig::BackToRootFolder => {
                            *state.active_folder_id.write() = None;
                            let _ = app.emit("folder-changed", None::<String>);
                        }
                        other => {
                            if let Err(e) = ActionExecutor::execute(other) {
                                log::error!("Action execution failed: {}", e);
                                let _ = app.emit("action-error", e.clone());
                                if let Some(ref mut f) = log_file {
                                    let _ = writeln!(f, "   └─ [ACTION ERROR] for key '{}': {}", key_id, e);
                                }
                            } else {
                                if let Some(ref mut f) = log_file {
                                    let _ = writeln!(f, "   └─ [ACTION EXECUTED] for key '{}' ({}) -> SUCCESS", key_id, action_summary);
                                }
                            }
                        }
                    }

                    // Emit key triggered event to UI for visual illumination
                    let _ = app.emit("deck-key-triggered", key_id);
                }

                WorkerMessage::Telemetry(t) => {
                    // Format detailed single-line log
                    let line = format!(
                        "[{}] FG: \"{}\" (PID {}, SELF={}) | VK: 0x{:02X} ({}) | Scan: 0x{:02X} | Ext: {} | Down: {} | Injected: {} | NumLock: {} | Matched: {:?} | DeckMode: {} | Suppressed: {} | ActionQueued: {:?} | HookDuration: {}us",
                        format_timestamp(t.timestamp_ms),
                        t.fg_window,
                        t.fg_pid,
                        t.is_self_foreground,
                        t.vk_code,
                        t.vk_name,
                        t.scan_code,
                        if t.is_extended { 1 } else { 0 },
                        t.is_key_down,
                        t.is_injected,
                        if t.numlock_on { "ON" } else { "OFF" },
                        t.matched_logical_key,
                        t.deck_mode_enabled,
                        t.event_suppressed,
                        t.queued_action,
                        t.hook_duration_us
                    );

                    // Write to debug log and stdout only when diagnostics active or in debug builds
                    if cfg!(debug_assertions) || state.diagnostics_active.load(Ordering::Relaxed) {
                        if let Some(ref mut f) = log_file {
                            let _ = writeln!(f, "{}", line);
                            let _ = f.flush();
                        }

                        if let Some(ref ap_path) = appdata_log_path {
                            if let Ok(mut ap_file) = OpenOptions::new().create(true).append(true).open(ap_path) {
                                let _ = writeln!(ap_file, "{}", line);
                            }
                        }

                        println!("{}", line);
                    }

                    // Emit diagnostic event to UI if viewer active
                    if state.diagnostics_active.load(Ordering::Relaxed) {
                        let diag = DiagnosticEvent {
                            timestamp: t.timestamp_ms,
                            event_type: if t.is_key_down { "keydown".to_string() } else { "keyup".to_string() },
                            vk_code: t.vk_code,
                            vk_name: t.vk_name,
                            scan_code: t.scan_code,
                            is_extended: t.is_extended,
                            is_injected: t.is_injected,
                            numlock_on: t.numlock_on,
                            is_suppressed: t.event_suppressed,
                            matched_logical_key: t.matched_logical_key,
                        };
                        let _ = app.emit("diagnostic-key-event", diag);
                    }
                }

                WorkerMessage::CalibrationKeyCaptured(sig) => {
                    let _ = app.emit("calibration-key-captured", sig);
                }

                WorkerMessage::EmergencyReset => {
                    log::warn!("Off-thread worker processing EmergencyReset...");
                    *state.mode.write() = EngineMode::Normal;
                    let _ = app.emit("deck-mode-changed", false);
                    let _ = app.emit("emergency-reset", ());
                }

                WorkerMessage::KeyboardDeviceDetected(device_id) => {
                    log::info!("Hardware keyboard device detected: {}", device_id);
                    let keyboards = enumerate_keyboards();
                    let detected = keyboards
                        .iter()
                        .find(|k| k.id.eq_ignore_ascii_case(&device_id) || k.raw_path.contains(&device_id))
                        .cloned()
                        .unwrap_or_else(|| KeyboardDeviceInfo {
                            id: device_id.clone(),
                            name: format!("Keyboard Device [{}]", device_id),
                            raw_path: device_id.clone(),
                            is_internal: device_id.contains("INTERNAL"),
                            is_virtual: device_id.contains("VIRTUAL"),
                        });
                    let _ = app.emit("keyboard-device-detected", detected);
                }
            }
        }
        log::info!("Off-thread action/telemetry worker terminated.");
    }

    /// Dedicated hook thread running Windows message loop with Raw Input Device Sink
    fn hook_thread_loop(thread_id_store: Arc<AtomicU32>) {
        unsafe {
            let tid = GetCurrentThreadId();
            thread_id_store.store(tid, Ordering::SeqCst);

            // Correctly obtain current executable module handle for global WH_KEYBOARD_LL hook
            let hmod = GetModuleHandleW(std::ptr::null());

            // 1. Create message-only window for Raw Input keyboard sink
            let static_class: Vec<u16> = "STATIC\0".encode_utf16().collect();
            let raw_hwnd = CreateWindowExW(
                0,
                static_class.as_ptr(),
                std::ptr::null(),
                0,
                0, 0, 0, 0,
                HWND_MESSAGE,
                0 as _,
                hmod,
                std::ptr::null(),
            );

            if raw_hwnd != 0 as _ {
                RAW_INPUT_HWND.store(raw_hwnd as _, Ordering::SeqCst);
                let rid = RAWINPUTDEVICE {
                    usUsagePage: 1, // Generic Desktop Controls
                    usUsage: 6,     // Keyboard
                    dwFlags: RIDEV_INPUTSINK,
                    hwndTarget: raw_hwnd,
                };
                let reg_res = RegisterRawInputDevices(&rid, 1, std::mem::size_of::<RAWINPUTDEVICE>() as u32);
                log::info!("Raw Input keyboard sink registered on HWND {:?}: success={}", raw_hwnd, reg_res != 0);
                RAW_REGISTERED.store(reg_res != 0, Ordering::SeqCst);
                // Periodic tick used only to release parked keys whose raw event never arrives
                SetTimer(raw_hwnd, 1, 40, None);
            } else {
                log::warn!("Failed to create HWND_MESSAGE for Raw Input sink: {}", GetLastError());
            }

            // 2. Install low-level keyboard hook
            let hook = SetWindowsHookExW(
                WH_KEYBOARD_LL,
                Some(low_level_keyboard_proc),
                hmod,
                0,
            );

            if hook.is_null() {
                log::error!("Failed to install WH_KEYBOARD_LL hook! Error: {}", GetLastError());
                if raw_hwnd != 0 as _ {
                    DestroyWindow(raw_hwnd);
                    RAW_INPUT_HWND.store(std::ptr::null_mut(), Ordering::SeqCst);
                }
                return;
            }

            log::info!("WH_KEYBOARD_LL hook successfully installed with hMod on thread {}", tid);

            let mut msg: MSG = std::mem::zeroed();
            while GetMessageW(&mut msg, 0 as _, 0, 0) > 0 {
                if msg.message == WM_INPUT {
                    let hook_guard = HOOK_DATA.read();
                    process_raw_input_lparam(msg.lParam, hook_guard.as_ref(), true);
                } else if msg.message == WM_TIMER {
                    flush_expired_pending();
                }
                TranslateMessage(&msg);
                DispatchMessageW(&msg);
            }

            log::info!("Unhooking WH_KEYBOARD_LL...");
            RAW_REGISTERED.store(false, Ordering::SeqCst);
            flush_expired_pending();
            UnhookWindowsHookEx(hook);
            if raw_hwnd != 0 as _ {
                DestroyWindow(raw_hwnd);
                RAW_INPUT_HWND.store(std::ptr::null_mut(), Ordering::SeqCst);
            }
            log::info!("WH_KEYBOARD_LL cleanly unhooked.");
        }
    }

    /// Graceful shutdown
    pub fn shutdown(&self) {
        let tid = self.hook_thread_id.load(Ordering::SeqCst);
        if tid != 0 {
            unsafe {
                PostThreadMessageW(tid, WM_QUIT, 0, 0);
            }
        }
    }
}

impl Drop for KeyboardEngine {
    fn drop(&mut self) {
        self.shutdown();
    }
}

/// Fast foreground window query (pure memory read in user32, sub-microsecond)
fn get_foreground_info() -> (String, u32, bool) {
    unsafe {
        let fg_hwnd = GetForegroundWindow();
        if fg_hwnd.is_null() {
            return ("None".to_string(), 0, false);
        }
        let mut fg_pid = 0u32;
        GetWindowThreadProcessId(fg_hwnd, &mut fg_pid);
        let my_pid = GetCurrentProcessId();
        let is_self = fg_pid == my_pid;

        let mut title_buf = [0u16; 128];
        let len = GetWindowTextW(fg_hwnd, title_buf.as_mut_ptr(), 128);
        let title = if len > 0 {
            String::from_utf16_lossy(&title_buf[..len as usize])
        } else {
            "Untitled / System".to_string()
        };

        (title, fg_pid, is_self)
    }
}

/// The Low-Level Keyboard Hook Callback
/// GUARANTEED SUB-5-MICROSECOND EXECUTION.
/// ZERO disk I/O, ZERO IPC to webviews, ZERO COM calls, ZERO heavy locks.
unsafe extern "system" fn low_level_keyboard_proc(
    n_code: i32,
    w_param: WPARAM,
    l_param: LPARAM,
) -> LRESULT {
    let hook_start = Instant::now();

    unsafe {
        if n_code < 0 {
            return CallNextHookEx(0 as _, n_code, w_param, l_param);
        }

        let hook_guard = HOOK_DATA.read();
        let hook_data = match hook_guard.as_ref() {
            Some(data) => data,
            None => return CallNextHookEx(0 as _, n_code, w_param, l_param),
        };

        let kbd = *(l_param as *const KBDLLHOOKSTRUCT);
        let vk_code = kbd.vkCode;
        let scan_code = kbd.scanCode;
        let flags = kbd.flags;

        // Check injected flag: ALWAYS ignore synthetic input generated by SendInput
        let is_injected = (flags & LLKHF_INJECTED_FLAG) != 0;
        let is_extended = (flags & LLKHF_EXTENDED_FLAG) != 0;
        let is_key_up = (flags & LLKHF_UP_FLAG) != 0;
        let is_key_down = !is_key_up;

        // Check NumLock state via GetKeyState
        let numlock_on = (GetKeyState(VK_NUMLOCK as i32) & 1) != 0;

        // Query foreground window info
        let (fg_window, fg_pid, is_self_foreground) = get_foreground_info();

        if is_injected {
            // Synthetic input generated by our own SendInput; pass through immediately without delay
            let duration_us = hook_start.elapsed().as_micros() as u64;
            let _ = hook_data.worker_tx.send(WorkerMessage::Telemetry(TelemetryRecord {
                timestamp_ms: current_time_ms(),
                fg_window,
                fg_pid,
                is_self_foreground,
                vk_code,
                vk_name: vk_code_to_name(vk_code),
                scan_code,
                is_extended,
                is_key_down,
                is_injected: true,
                numlock_on,
                matched_logical_key: None,
                deck_mode_enabled: false,
                event_suppressed: false,
                queued_action: None,
                hook_duration_us: duration_us,
            }));
            return CallNextHookEx(0 as _, n_code, w_param, l_param);
        }

        // Emergency shortcut check: triple-Esc
        if is_key_down && hook_data.state.emergency_shortcut_enabled.load(Ordering::Relaxed) {
            if vk_code == VK_ESCAPE as u32 {
                let mut last_time = hook_data.state.last_esc_time.write();
                let now = Instant::now();
                if now.duration_since(*last_time) < Duration::from_millis(1200) {
                    let count = hook_data.state.esc_press_count.fetch_add(1, Ordering::SeqCst) + 1;
                    if count >= 3 {
                        *hook_data.state.mode.write() = EngineMode::Normal;
                        hook_data.state.esc_press_count.store(0, Ordering::SeqCst);
                        log::warn!("EMERGENCY DISABLE TRIGGERED: Deck Mode forcibly reset to Normal!");
                        let _ = hook_data.worker_tx.send(WorkerMessage::EmergencyReset);
                    }
                } else {
                    hook_data.state.esc_press_count.store(1, Ordering::SeqCst);
                }
                *last_time = now;
            }
        }

        // Drain any pending Raw Input messages to update hardware device attribution
        let raw_hwnd = RAW_INPUT_HWND.load(Ordering::Relaxed) as HWND;
        if raw_hwnd != 0 as _ {
            // PM_NOREMOVE: only refresh LAST_HARDWARE_KEYBOARD here; the message loop still
            // receives the same WM_INPUT and resolves parked keys from there.
            let mut raw_msg: MSG = std::mem::zeroed();
            if PeekMessageW(&mut raw_msg, raw_hwnd, WM_INPUT, WM_INPUT, PM_NOREMOVE) != 0 {
                process_raw_input_lparam(raw_msg.lParam, Some(hook_data), false);
            }
        }

        // Check if user is in "Detect Keyboard" mode:
        if DETECTING_KEYBOARD.load(Ordering::Relaxed) {
            if is_key_down {
                DETECTING_KEYBOARD.store(false, Ordering::SeqCst);
                let current_dev = LAST_HARDWARE_KEYBOARD.read().clone().unwrap_or_else(|| "UNKNOWN".to_string());
                let _ = hook_data.worker_tx.send(WorkerMessage::KeyboardDeviceDetected(current_dev));
            }
            return 1; // Suppress the detection keystroke
        }

        // Deferred device attribution: in Deck mode with a specific target keyboard, park matched keys
        // (suppressed) until Raw Input tells us which keyboard they really came from.
        if RAW_REGISTERED.load(Ordering::Relaxed) {
            let target_device = hook_data.state.target_keyboard_device.read().clone();
            let target_active = if let Some(ref target) = target_device {
                target != "all" && !target.is_empty()
            } else {
                false
            };
            if target_active && *hook_data.state.mode.read() == EngineMode::Deck {
                let matched_key = hook_data
                    .state
                    .calibration
                    .read()
                    .find_matched_key(vk_code, scan_code, is_extended);
                if let Some(key_id) = matched_key {
                    PENDING_KEYS.lock().push_back(PendingKey {
                        key_id,
                        vk_code,
                        scan_code,
                        is_extended,
                        is_key_down,
                        queued_at: Instant::now(),
                    });
                    return 1;
                }
            }
        }

        // Target device filter: If a specific keyboard is chosen, allow other keyboards to type freely
        let target_device = hook_data.state.target_keyboard_device.read().clone();
        if let Some(ref target) = target_device {
            if target != "all" && !target.is_empty() {
                let current_dev = LAST_HARDWARE_KEYBOARD.read().clone().unwrap_or_default();
                // If device is known and DOES NOT match target, pass through to Windows immediately
                if !current_dev.is_empty() && !current_dev.eq_ignore_ascii_case(target) && !current_dev.contains(target) {
                    let duration_us = hook_start.elapsed().as_micros() as u64;
                    let _ = hook_data.worker_tx.send(WorkerMessage::Telemetry(TelemetryRecord {
                        timestamp_ms: current_time_ms(),
                        fg_window,
                        fg_pid,
                        is_self_foreground,
                        vk_code,
                        vk_name: vk_code_to_name(vk_code),
                        scan_code,
                        is_extended,
                        is_key_down,
                        is_injected: false,
                        numlock_on,
                        matched_logical_key: None,
                        deck_mode_enabled: false,
                        event_suppressed: false,
                        queued_action: None,
                        hook_duration_us: duration_us,
                    }));
                    return CallNextHookEx(0 as _, n_code, w_param, l_param);
                }
            }
        }

        let current_mode = *hook_data.state.mode.read();

        // 1. Calibrating Mode
        if current_mode == EngineMode::Calibrating {
            if is_key_down {
                let signature = KeySignature::new(vk_code, scan_code, is_extended);
                let _ = hook_data.worker_tx.send(WorkerMessage::CalibrationKeyCaptured(signature));
            }
            let duration_us = hook_start.elapsed().as_micros() as u64;
            let _ = hook_data.worker_tx.send(WorkerMessage::Telemetry(TelemetryRecord {
                timestamp_ms: current_time_ms(),
                fg_window,
                fg_pid,
                is_self_foreground,
                vk_code,
                vk_name: vk_code_to_name(vk_code),
                scan_code,
                is_extended,
                is_key_down,
                is_injected: false,
                numlock_on,
                matched_logical_key: None,
                deck_mode_enabled: false,
                event_suppressed: true,
                queued_action: None,
                hook_duration_us: duration_us,
            }));
            // Suppress key during calibration
            return 1;
        }

        // 2. Deck Mode
        if current_mode == EngineMode::Deck {
            let cal = hook_data.state.calibration.read();
            let matched_key = cal.find_matched_key(vk_code, scan_code, is_extended);
            drop(cal);

            if let Some(key_id) = matched_key {
                let mut queued_action_str = None;

                if is_key_down {
                    let mut pressed = hook_data.state.pressed_keys.write();
                    let is_first_press = pressed.insert(key_id.clone());
                    drop(pressed);

                    if is_first_press {
                        let profile = hook_data.state.active_profile.read();
                        let active_folder = hook_data.state.active_folder_id.read();

                        let assignment = if let Some(folder_id) = active_folder.as_ref() {
                            profile
                                .folders
                                .iter()
                                .find(|f| f.id == *folder_id)
                                .and_then(|f| f.keys.get(&key_id))
                                .or_else(|| profile.keys.get(&key_id))
                        } else {
                            profile.keys.get(&key_id)
                        };

                        if let Some(assign) = assignment {
                            if let Some(action) = &assign.action {
                                queued_action_str = Some(format!("{:?}", action));
                                let _ = hook_data.worker_tx.send(WorkerMessage::ExecuteAction {
                                    key_id: key_id.clone(),
                                    action: action.clone(),
                                });
                            }
                        }
                    }
                } else {
                    let mut pressed = hook_data.state.pressed_keys.write();
                    pressed.remove(&key_id);
                }

                let duration_us = hook_start.elapsed().as_micros() as u64;
                let _ = hook_data.worker_tx.send(WorkerMessage::Telemetry(TelemetryRecord {
                    timestamp_ms: current_time_ms(),
                    fg_window,
                    fg_pid,
                    is_self_foreground,
                    vk_code,
                    vk_name: vk_code_to_name(vk_code),
                    scan_code,
                    is_extended,
                    is_key_down,
                    is_injected: false,
                    numlock_on,
                    matched_logical_key: Some(key_id),
                    deck_mode_enabled: true,
                    event_suppressed: true,
                    queued_action: queued_action_str,
                    hook_duration_us: duration_us,
                }));

                // SUPPRESS THIS KEY FROM PASSING TO WINDOWS: Return 1
                return 1;
            }
        }

        // 3. Normal Mode or unmapped keys: Pass through
        let cal = hook_data.state.calibration.read();
        let matched = cal.find_matched_key(vk_code, scan_code, is_extended);
        drop(cal);

        let duration_us = hook_start.elapsed().as_micros() as u64;
        let _ = hook_data.worker_tx.send(WorkerMessage::Telemetry(TelemetryRecord {
            timestamp_ms: current_time_ms(),
            fg_window,
            fg_pid,
            is_self_foreground,
            vk_code,
            vk_name: vk_code_to_name(vk_code),
            scan_code,
            is_extended,
            is_key_down,
            is_injected: false,
            numlock_on,
            matched_logical_key: matched,
            deck_mode_enabled: current_mode == EngineMode::Deck,
            event_suppressed: false,
            queued_action: None,
            hook_duration_us: duration_us,
        }));

        CallNextHookEx(0 as _, n_code, w_param, l_param)
    }
}

fn current_time_ms() -> u64 {
    SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis() as u64
}

fn format_timestamp(ms: u64) -> String {
    let secs = ms / 1000;
    let millis = ms % 1000;
    let s = secs % 60;
    let m = (secs / 60) % 60;
    let h = (secs / 3600) % 24;
    format!("{:02}:{:02}:{:02}.{:03}", h, m, s, millis)
}

pub fn vk_code_to_name(vk: u32) -> String {
    match vk as u16 {
        VK_NUMPAD0 => "NUMPAD 0".to_string(),
        VK_NUMPAD1 => "NUMPAD 1".to_string(),
        VK_NUMPAD2 => "NUMPAD 2".to_string(),
        VK_NUMPAD3 => "NUMPAD 3".to_string(),
        VK_NUMPAD4 => "NUMPAD 4".to_string(),
        VK_NUMPAD5 => "NUMPAD 5".to_string(),
        VK_NUMPAD6 => "NUMPAD 6".to_string(),
        VK_NUMPAD7 => "NUMPAD 7".to_string(),
        VK_NUMPAD8 => "NUMPAD 8".to_string(),
        VK_NUMPAD9 => "NUMPAD 9".to_string(),
        VK_MULTIPLY => "NUMPAD *".to_string(),
        VK_ADD => "NUMPAD +".to_string(),
        VK_SUBTRACT => "NUMPAD -".to_string(),
        VK_DECIMAL => "NUMPAD .".to_string(),
        VK_DIVIDE => "NUMPAD /".to_string(),
        VK_NUMLOCK => "NUM LOCK".to_string(),
        VK_RETURN => "ENTER".to_string(),
        VK_HOME => "HOME".to_string(),
        VK_UP => "UP ARROW".to_string(),
        VK_PRIOR => "PAGE UP".to_string(),
        VK_LEFT => "LEFT ARROW".to_string(),
        VK_CLEAR => "CLEAR".to_string(),
        VK_RIGHT => "RIGHT ARROW".to_string(),
        VK_END => "END".to_string(),
        VK_DOWN => "DOWN ARROW".to_string(),
        VK_NEXT => "PAGE DOWN".to_string(),
        VK_INSERT => "INSERT".to_string(),
        VK_DELETE => "DELETE".to_string(),
        VK_ESCAPE => "ESCAPE".to_string(),
        VK_TAB => "TAB".to_string(),
        VK_SPACE => "SPACE".to_string(),
        VK_BACK => "BACKSPACE".to_string(),
        0x30..=0x39 => format!("KEY {}", (vk as u8 as char)),
        0x41..=0x5A => format!("KEY {}", (vk as u8 as char)),
        VK_F1..=VK_F12 => format!("F{}", vk - (VK_F1 as u32) + 1),
        _ => format!("0x{:02X}", vk),
    }
}
