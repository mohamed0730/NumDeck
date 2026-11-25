use crate::types::ActionConfig;
use std::ffi::OsStr;
use std::os::windows::ffi::OsStrExt;
use std::process::Command;
use std::ptr;
use std::thread;
use std::time::{Duration, Instant};
use windows_sys::Win32::UI::Input::KeyboardAndMouse::*;
use windows_sys::Win32::UI::Shell::ShellExecuteW;
use windows_sys::Win32::UI::WindowsAndMessaging::SW_SHOWNORMAL;

pub struct ActionExecutor;

impl ActionExecutor {
    pub fn execute(action: ActionConfig) -> Result<(), String> {
        match action {
            ActionConfig::LaunchApp { path, arguments } => {
                Self::launch_app(&path, arguments.as_deref())
            }
            ActionConfig::OpenPath { path } => Self::open_path(&path),
            ActionConfig::Hotkey { modifiers, key } => Self::send_hotkey(&modifiers, &key),
            ActionConfig::TypeText { text } => Self::type_unicode_text(&text),
            ActionConfig::SystemMedia { command } => Self::send_system_media(&command),
            ActionConfig::MultiAction { steps } => {
                for step in steps {
                    if let Err(e) = Self::execute(step.action) {
                        log::warn!("MultiAction step failed: {}", e);
                    }
                    if step.delay_ms > 0 {
                        thread::sleep(Duration::from_millis(step.delay_ms));
                    }
                }
                Ok(())
            }
            // State-only actions are handled by the controller
            ActionConfig::SwitchProfile { .. }
            | ActionConfig::NavigateFolder { .. }
            | ActionConfig::BackToRootFolder
            | ActionConfig::ToggleDeckMode => Ok(()),
        }
    }

    /// Launch executable or process
    fn launch_app(path: &str, arguments: Option<&str>) -> Result<(), String> {
        let mut cmd = Command::new(path);
        if let Some(args) = arguments {
            if !args.trim().is_empty() {
                cmd.args(args.split_whitespace());
            }
        }
        cmd.spawn()
            .map_err(|e| format!("Failed to launch '{}': {}", path, e))?;
        Ok(())
    }

    /// Open file, folder, URL, or protocol link using Windows ShellExecuteW
    fn open_path(path: &str) -> Result<(), String> {
        let wide_path: Vec<u16> = OsStr::new(path).encode_wide().chain(Some(0)).collect();
        let wide_op: Vec<u16> = OsStr::new("open").encode_wide().chain(Some(0)).collect();

        unsafe {
            let res = ShellExecuteW(
                ptr::null_mut(),
                wide_op.as_ptr(),
                wide_path.as_ptr(),
                ptr::null(),
                ptr::null(),
                SW_SHOWNORMAL,
            );
            if (res as isize) <= 32 {
                return Err(format!("ShellExecuteW failed with error code: {}", res as isize));
            }
        }
        Ok(())
    }

    /// Send System Media keys
    fn send_system_media(command: &str) -> Result<(), String> {
        let vk = match command.to_lowercase().as_str() {
            "volume_up" => VK_VOLUME_UP,
            "volume_down" => VK_VOLUME_DOWN,
            "mute" => VK_VOLUME_MUTE,
            "play_pause" => VK_MEDIA_PLAY_PAUSE,
            "next_track" => VK_MEDIA_NEXT_TRACK,
            "prev_track" => VK_MEDIA_PREV_TRACK,
            _ => return Err(format!("Unknown media command: {}", command)),
        };

        Self::tap_vk(vk);
        Ok(())
    }

    /// Simulate key-down followed by key-up for a virtual key code
    fn tap_vk(vk: u16) {
        unsafe {
            let mut inputs: [INPUT; 2] = std::mem::zeroed();

            // Key Down
            inputs[0].r#type = INPUT_KEYBOARD;
            inputs[0].Anonymous.ki.wVk = vk;
            inputs[0].Anonymous.ki.dwFlags = KEYEVENTF_EXTENDEDKEY;

            // Key Up
            inputs[1].r#type = INPUT_KEYBOARD;
            inputs[1].Anonymous.ki.wVk = vk;
            inputs[1].Anonymous.ki.dwFlags = KEYEVENTF_EXTENDEDKEY | KEYEVENTF_KEYUP;

            SendInput(2, inputs.as_mut_ptr(), std::mem::size_of::<INPUT>() as i32);
        }
    }

    /// Type arbitrary Unicode string directly without layout quirks
    fn type_unicode_text(text: &str) -> Result<(), String> {
        for ch in text.chars() {
            if ch == '\n' {
                Self::tap_vk(VK_RETURN);
                continue;
            }

            let mut utf16_buf = [0u16; 2];
            let encoded = ch.encode_utf16(&mut utf16_buf);

            for &code_unit in encoded.iter() {
                unsafe {
                    let mut inputs: [INPUT; 2] = std::mem::zeroed();

                    // Key Down Unicode
                    inputs[0].r#type = INPUT_KEYBOARD;
                    inputs[0].Anonymous.ki.wScan = code_unit;
                    inputs[0].Anonymous.ki.dwFlags = KEYEVENTF_UNICODE;

                    // Key Up Unicode
                    inputs[1].r#type = INPUT_KEYBOARD;
                    inputs[1].Anonymous.ki.wScan = code_unit;
                    inputs[1].Anonymous.ki.dwFlags = KEYEVENTF_UNICODE | KEYEVENTF_KEYUP;

                    SendInput(2, inputs.as_mut_ptr(), std::mem::size_of::<INPUT>() as i32);
                }
            }
            thread::sleep(Duration::from_millis(5));
        }
        Ok(())
    }

    /// Keyboard INPUT carrying BOTH the virtual key and its scan code, like real hardware does.
    /// (Many programs that implement their own hotkeys read the scan code or the left/right modifier keys.)
    fn key_input(vk: u16, key_up: bool) -> INPUT {
        unsafe {
            let mut input: INPUT = std::mem::zeroed();
            input.r#type = INPUT_KEYBOARD;
            input.Anonymous.ki.wVk = vk;
            input.Anonymous.ki.wScan = MapVirtualKeyW(vk as u32, MAPVK_VK_TO_VSC) as u16;
            let mut flags = 0u32;
            if Self::is_extended_vk(vk) {
                flags |= KEYEVENTF_EXTENDEDKEY;
            }
            if key_up {
                flags |= KEYEVENTF_KEYUP;
            }
            input.Anonymous.ki.dwFlags = flags;
            input
        }
    }

    fn is_extended_vk(vk: u16) -> bool {
        matches!(
            vk,
            VK_UP
                | VK_DOWN
                | VK_LEFT
                | VK_RIGHT
                | VK_INSERT
                | VK_DELETE
                | VK_HOME
                | VK_END
                | VK_PRIOR
                | VK_NEXT
                | VK_LWIN
                | VK_RWIN
                | VK_RMENU
                | VK_RCONTROL
        )
    }

    /// Send several key events in ONE call (they enter the system together, in order)
    fn send_batch(inputs: &mut [INPUT]) {
        if inputs.is_empty() {
            return;
        }
        unsafe {
            SendInput(
                inputs.len() as u32,
                inputs.as_mut_ptr(),
                std::mem::size_of::<INPUT>() as i32,
            );
        }
    }

    /// Very short, precise pause (a few milliseconds) without waiting for the OS timer
    fn pause_ms(ms: u64) {
        let end = Instant::now() + Duration::from_millis(ms);
        while Instant::now() < end {
            std::hint::spin_loop();
        }
    }

    /// Press a hotkey combo: Modifiers Down -> Key Down -> Key Up -> Modifiers Up.
    /// Total time is only a few milliseconds; the tiny pauses let programs that poll the keyboard notice each step.
    fn send_hotkey(modifiers: &[String], key: &str) -> Result<(), String> {
        const MOD_SETTLE_MS: u64 = 3; // after the modifiers go down, before the main key
        const KEY_HOLD_MS: u64 = 3; // how long the main key stays down

        let mut mod_vks = Vec::new();
        for m in modifiers {
            match m.to_lowercase().as_str() {
                "ctrl" | "control" => mod_vks.push(VK_LCONTROL),
                "alt" => mod_vks.push(VK_LMENU),
                "shift" => mod_vks.push(VK_LSHIFT),
                "win" | "meta" | "super" => mod_vks.push(VK_LWIN),
                _ => {}
            }
        }

        let main_vk = Self::parse_key_to_vk(key)
            .ok_or_else(|| format!("Unknown key for hotkey: {}", key))?;

        // 1. All modifiers down (one batch)
        if !mod_vks.is_empty() {
            let mut downs: Vec<INPUT> = mod_vks.iter().map(|&vk| Self::key_input(vk, false)).collect();
            Self::send_batch(&mut downs);
            Self::pause_ms(MOD_SETTLE_MS);
        }

        // 2. Main key: down, short hold, up
        Self::send_batch(&mut [Self::key_input(main_vk, false)]);
        Self::pause_ms(KEY_HOLD_MS);
        Self::send_batch(&mut [Self::key_input(main_vk, true)]);

        // 3. All modifiers up, in reverse order (one batch)
        if !mod_vks.is_empty() {
            Self::pause_ms(1);
            let mut ups: Vec<INPUT> = mod_vks.iter().rev().map(|&vk| Self::key_input(vk, true)).collect();
            Self::send_batch(&mut ups);
        }

        Ok(())
    }

    /// Convert common key name to VK code
    fn parse_key_to_vk(key_name: &str) -> Option<u16> {
        let upper = key_name.trim().to_uppercase();
        if upper.len() == 1 {
            let ch = upper.chars().next().unwrap();
            if ch.is_ascii_alphanumeric() {
                return Some(ch as u16);
            }
        }

        match upper.as_str() {
            "ESCAPE" | "ESC" => Some(VK_ESCAPE),
            "ENTER" | "RETURN" => Some(VK_RETURN),
            "TAB" => Some(VK_TAB),
            "SPACE" => Some(VK_SPACE),
            "BACKSPACE" => Some(VK_BACK),
            "DELETE" | "DEL" => Some(VK_DELETE),
            "INSERT" | "INS" => Some(VK_INSERT),
            "HOME" => Some(VK_HOME),
            "END" => Some(VK_END),
            "PAGEUP" | "PGUP" => Some(VK_PRIOR),
            "PAGEDOWN" | "PGDN" => Some(VK_NEXT),
            "UP" => Some(VK_UP),
            "DOWN" => Some(VK_DOWN),
            "LEFT" => Some(VK_LEFT),
            "RIGHT" => Some(VK_RIGHT),
            "F1" => Some(VK_F1),
            "F2" => Some(VK_F2),
            "F3" => Some(VK_F3),
            "F4" => Some(VK_F4),
            "F5" => Some(VK_F5),
            "F6" => Some(VK_F6),
            "F7" => Some(VK_F7),
            "F8" => Some(VK_F8),
            "F9" => Some(VK_F9),
            "F10" => Some(VK_F10),
            "F11" => Some(VK_F11),
            "F12" => Some(VK_F12),
            _ => None,
        }
    }
}
