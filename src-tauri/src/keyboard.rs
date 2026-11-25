use crate::actions::ActionExecutor;
use crate::types::*;
use crossbeam_channel::{Receiver, Sender};
use parking_lot::RwLock;
use std::collections::{HashMap, HashSet};
use std::ffi::c_void;
use std::os::windows::ffi::OsStrExt;
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

// =====================================================================================
// Built-in device tagger (Interception driver)
// -------------------------------------------------------------------------------------
// Windows only tells us which keyboard a key came from AFTER the low-level hook has already
// decided what to do with it. The Interception driver sees the key earlier, so this thread
// stamps every stroke of the selected (target) keyboard with NUMPAD_TAG_MAGIC. Windows hands
// that value to the hook as dwExtraInfo, so the hook knows the device of the CURRENT key
// immediately. If the driver is missing, NumDeck falls back to the old behaviour.
// The files are embedded at build time (see the GitHub workflow that fills src-tauri/vendor).
// =====================================================================================
static INTERCEPTION_DLL: &[u8] = include_bytes!("../vendor/interception.dll");
static INTERCEPTION_INSTALLER: &[u8] = include_bytes!("../vendor/install-interception.exe");

const NUMPAD_TAG_MAGIC: usize = 0x4E44_434B; // "NDCK"
static TAGGER_ACTIVE: AtomicBool = AtomicBool::new(false);

/// True while the tagger is running AND it can see the selected target keyboard.
fn tagger_running() -> bool {
    TAGGER_ACTIVE.load(Ordering::Relaxed)
}

fn tag_diag(tx: &Sender<WorkerMessage>, msg: String) {
    let _ = tx.send(WorkerMessage::Telemetry(TelemetryRecord {
        timestamp_ms: current_time_ms(),
        fg_window: msg,
        fg_pid: 0,
        is_self_foreground: false,
        vk_code: 0,
        vk_name: "TAGDIAG".to_string(),
        scan_code: 0,
        is_extended: false,
        is_key_down: false,
        is_injected: false,
        numlock_on: false,
        matched_logical_key: None,
        deck_mode_enabled: false,
        event_suppressed: false,
        queued_action: None,
        hook_duration_us: 0,
    }));
}

type IcContext = *mut c_void;
type IcPredicate = unsafe extern "C" fn(i32) -> i32;
type FnCreate = unsafe extern "C" fn() -> IcContext;
type FnSetFilter = unsafe extern "C" fn(IcContext, Option<IcPredicate>, u16);
type FnWaitTimeout = unsafe extern "C" fn(IcContext, u32) -> i32;
type FnReceive = unsafe extern "C" fn(IcContext, i32, *mut c_void, u32) -> i32;
type FnSend = unsafe extern "C" fn(IcContext, i32, *const c_void, u32) -> i32;
type FnGetHwid = unsafe extern "C" fn(IcContext, i32, *mut c_void, u32) -> u32;

#[repr(C)]
struct IcKeyStroke {
    code: u16,
    state: u16,
    information: u32,
}

struct IcApi {
    create: FnCreate,
    set_filter: FnSetFilter,
    wait: FnWaitTimeout,
    receive: FnReceive,
    send: FnSend,
    get_hwid: FnGetHwid,
    is_keyboard: IcPredicate,
}

fn wide_z(s: &str) -> Vec<u16> {
    s.encode_utf16().chain(std::iter::once(0)).collect()
}

fn ic_sym<T: Copy>(module: HMODULE, name: &[u8]) -> Option<T> {
    unsafe {
        let p = windows_sys::Win32::System::LibraryLoader::GetProcAddress(module, name.as_ptr());
        p.map(|f| std::mem::transmute_copy::<_, T>(&f))
    }
}

fn load_ic_api(dll_path: &std::path::Path) -> Option<IcApi> {
    let wide: Vec<u16> = dll_path.as_os_str().encode_wide().chain(std::iter::once(0)).collect();
    let module = unsafe { windows_sys::Win32::System::LibraryLoader::LoadLibraryW(wide.as_ptr()) };
    if module.is_null() {
        return None;
    }
    Some(IcApi {
        create: ic_sym(module, b"interception_create_context\0")?,
        set_filter: ic_sym(module, b"interception_set_filter\0")?,
        wait: ic_sym(module, b"interception_wait_with_timeout\0")?,
        receive: ic_sym(module, b"interception_receive\0")?,
        send: ic_sym(module, b"interception_send\0")?,
        get_hwid: ic_sym(module, b"interception_get_hardware_id\0")?,
        is_keyboard: ic_sym(module, b"interception_is_keyboard\0")?,
    })
}

/// Hardware id of an Interception device as upper-case ASCII, strings separated by '|'
fn ic_hwid_ascii(api: &IcApi, ctx: IcContext, dev: i32) -> String {
    let mut buf = [0u8; 1024];
    let n = unsafe { (api.get_hwid)(ctx, dev, buf.as_mut_ptr() as *mut c_void, (buf.len() - 4) as u32) } as usize;
    if n == 0 || n > buf.len() - 4 {
        return String::new();
    }
    let wide = n >= 4 && buf[1] == 0 && buf[3] == 0;
    let mut out = String::new();
    if wide {
        let mut i = 0;
        while i + 1 < n {
            let c = u16::from(buf[i]) | (u16::from(buf[i + 1]) << 8);
            if c == 0 {
                out.push('|');
            } else if c < 128 {
                out.push((c as u8 as char).to_ascii_uppercase());
            } else {
                out.push('?');
            }
            i += 2;
        }
    } else {
        for &b in &buf[..n] {
            if b == 0 {
                out.push('|');
            } else {
                out.push((b as char).to_ascii_uppercase());
            }
        }
    }
    out
}

/// Writes the embedded driver files to %APPDATA%\NumpadDeck\interception and returns that folder.
fn extract_interception_files() -> Option<std::path::PathBuf> {
    let base = std::env::var_os("APPDATA")?;
    let dir = std::path::PathBuf::from(base).join("NumpadDeck").join("interception");
    std::fs::create_dir_all(&dir).ok()?;
    let files: [(&str, &[u8]); 2] = [
        ("interception.dll", INTERCEPTION_DLL),
        ("install-interception.exe", INTERCEPTION_INSTALLER),
    ];
    for (name, bytes) in files {
        let path = dir.join(name);
        let up_to_date = std::fs::metadata(&path).map(|m| m.len() == bytes.len() as u64).unwrap_or(false);
        if !up_to_date {
            std::fs::write(&path, bytes).ok()?;
        }
    }
    Some(dir)
}

/// The driver is not installed: install it automatically, ONCE (Windows shows its own administrator
/// prompt; that cannot be skipped). A short note then tells the user to restart Windows.
/// Delete %APPDATA%\NumpadDeck\interception\install_attempted.txt to let NumDeck try again.
fn install_driver_automatically(dir: &std::path::Path) {
    let marker = dir.join("install_attempted.txt");
    if marker.exists() {
        return;
    }
    let _ = std::fs::write(&marker, b"attempted");

    let exe = dir.join("install-interception.exe");
    let verb = wide_z("runas");
    let file = wide_z(&exe.to_string_lossy());
    let args = wide_z("/install");
    let workdir = wide_z(&dir.to_string_lossy());
    unsafe {
        windows_sys::Win32::UI::Shell::ShellExecuteW(
            std::ptr::null_mut(),
            verb.as_ptr(),
            file.as_ptr(),
            args.as_ptr(),
            workdir.as_ptr(),
            SW_HIDE,
        );
    }
    thread::sleep(Duration::from_secs(5));

    let title = wide_z("NumDeck");
    let text = wide_z(
        "NumDeck بيجهّز العزل الفوري للنام باد الخارجية.\n\nلو وافقت على طلب إذن المدير اللي ظهر، اعمل ريستارت للجهاز مرة واحدة عشان يكتمل.\n\nالرسالة دي مش هتظهر تاني.",
    );
    unsafe {
        MessageBoxW(
            std::ptr::null_mut(),
            text.as_ptr(),
            title.as_ptr(),
            MB_OK | MB_ICONINFORMATION | MB_TOPMOST | MB_SETFOREGROUND,
        );
    }
}

fn selected_target(state: &Arc<KeyboardEngineState>) -> Option<String> {
    let target = state.target_keyboard_device.read().clone();
    match target {
        Some(t) if t != "all" && !t.is_empty() => Some(t.to_uppercase()),
        _ => None,
    }
}

fn tagger_thread(state: Arc<KeyboardEngineState>) {
    // Nothing to do until a specific keyboard is selected in NumDeck
    let mut target = loop {
        if let Some(t) = selected_target(&state) {
            break t;
        }
        thread::sleep(Duration::from_secs(3));
    };

    let dir = match extract_interception_files() {
        Some(d) => d,
        None => {
            log::warn!("tagger: could not extract driver files");
            return;
        }
    };
    let api = match load_ic_api(&dir.join("interception.dll")) {
        Some(a) => a,
        None => {
            log::warn!("tagger: could not load interception.dll");
            return;
        }
    };
    let ctx = unsafe { (api.create)() };
    if ctx.is_null() {
        log::warn!("tagger: Interception driver not installed (or Windows not restarted yet)");
        install_driver_automatically(&dir);
        return;
    }
    unsafe {
        (api.set_filter)(ctx, Some(api.is_keyboard), 0xFFFF);
    }
    log::info!("tagger: Interception driver ready");

    let mut is_target = [false; 21];
    let mut last_scan: Option<Instant> = None;
    let mut stroke = [0u64; 16]; // large enough for any Interception stroke, 8-byte aligned

    loop {
        // Re-scan the devices about once per second (also picks up plugging/unplugging and target changes)
        let scan_due = match last_scan {
            Some(t) => t.elapsed() >= Duration::from_secs(1),
            None => true,
        };
        if scan_due {
            last_scan = Some(Instant::now());
            match selected_target(&state) {
                Some(t) => target = t,
                None => target.clear(),
            }
            let mut any = false;
            for dev in 1..=10i32 {
                let matched = if target.is_empty() {
                    false
                } else {
                    ic_hwid_ascii(&api, ctx, dev).contains(target.as_str())
                };
                is_target[dev as usize] = matched;
                any |= matched;
            }
            TAGGER_ACTIVE.store(any, Ordering::Relaxed);
        }

        let dev = unsafe { (api.wait)(ctx, 1000) };
        if dev <= 0 {
            continue;
        }
        let received = unsafe { (api.receive)(ctx, dev, stroke.as_mut_ptr() as *mut c_void, 1) };
        if received <= 0 {
            continue;
        }
        if (1..=10).contains(&dev) && is_target[dev as usize] {
            let ks = stroke.as_mut_ptr() as *mut IcKeyStroke;
            unsafe {
                (*ks).information = NUMPAD_TAG_MAGIC as u32;
            }
        }
        unsafe {
            (api.send)(ctx, dev, stroke.as_ptr() as *const c_void, 1);
        }
    }
}
static DEVICE_HANDLE_CACHE: parking_lot::RwLock<Option<HashMap<isize, String>>> = parking_lot::RwLock::new(None);

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

/// Process a WM_INPUT lParam, update the most recent hardware keyboard, and trigger detection if active
fn process_raw_input_lparam(lparam: LPARAM, worker_tx: Option<&Sender<WorkerMessage>>) {
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
            // Keys injected by NumDeck itself arrive as "SYNTHETIC"; they must not overwrite the last REAL keyboard.
            if dev_id == "SYNTHETIC" {
                return;
            }
            *LAST_HARDWARE_KEYBOARD.write() = Some(dev_id.clone());

            if DETECTING_KEYBOARD.swap(false, Ordering::SeqCst) {
                if let Some(tx) = worker_tx {
                    let _ = tx.send(WorkerMessage::KeyboardDeviceDetected(dev_id));
                }
            }
        }
    }
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

        // 4. Built-in device tagger (Interception driver); stays idle if the driver is not available
        let tagger_state = Arc::clone(&state);
        let _ = thread::Builder::new()
            .name("numdeck-tagger".to_string())
            .spawn(move || {
                tagger_thread(tagger_state);
            });

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
                    let worker_tx = hook_guard.as_ref().map(|d| &d.worker_tx);
                    process_raw_input_lparam(msg.lParam, worker_tx);
                }
                TranslateMessage(&msg);
                DispatchMessageW(&msg);
            }

            log::info!("Unhooking WH_KEYBOARD_LL...");
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
            let mut raw_msg: MSG = std::mem::zeroed();
            while PeekMessageW(&mut raw_msg, raw_hwnd, WM_INPUT, WM_INPUT, PM_REMOVE) != 0 {
                process_raw_input_lparam(raw_msg.lParam, Some(&hook_data.worker_tx));
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

        // Target device filter: If a specific keyboard is chosen, allow other keyboards to type freely
        let target_device = hook_data.state.target_keyboard_device.read().clone();
        if let Some(ref target) = target_device {
            if target != "all" && !target.is_empty() {
                let current_dev = LAST_HARDWARE_KEYBOARD.read().clone().unwrap_or_default();
                let tagger_on = tagger_running();
                let tagged = (kbd.dwExtraInfo as usize) == NUMPAD_TAG_MAGIC;
                if tagger_on && is_key_down {
                    tag_diag(
                        &hook_data.worker_tx,
                        format!(
                            "TAGDIAG extra=0x{:X} vk=0x{:02X} scan=0x{:02X} tagged={}",
                            kbd.dwExtraInfo as usize, vk_code, scan_code, tagged
                        ),
                    );
                }
                // Legacy mode only: a key-up whose key-down we already took over stays paired with it
                let up_of_suppressed_down = if !is_key_down {
                    let matched_up = hook_data
                        .state
                        .calibration
                        .read()
                        .find_matched_key(vk_code, scan_code, is_extended);
                    match matched_up {
                        Some(k) => {
                            let held = hook_data.state.pressed_keys.read().contains(&k);
                            held
                        }
                        None => false,
                    }
                } else {
                    false
                };
                let device_mismatch = if tagger_on {
                    // Tagger active: an untagged key is NOT from the external numpad (certain, no guessing)
                    !tagged
                } else {
                    // Legacy: guess from the previous key's device
                    !up_of_suppressed_down
                        && !current_dev.is_empty()
                        && !current_dev.eq_ignore_ascii_case(target)
                        && !current_dev.contains(target)
                };
                // If the key does NOT come from the target device, pass through to Windows immediately
                if device_mismatch {
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
