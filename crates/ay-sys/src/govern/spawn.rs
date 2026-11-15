// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Final-image native footprint policy and owned self-replacement.

use super::{fail_closed, ARMED_ENV, ROOT_PID_ENV};
use std::ffi::{CString, OsStr, OsString};
use std::mem::MaybeUninit;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use trust_exec_policy::FootprintLimit;

/// An initialized spawn attribute. Destroying it releases libSystem's storage.
struct SpawnAttr(libc::posix_spawnattr_t);

impl Drop for SpawnAttr {
    fn drop(&mut self) {
        // SAFETY: `SpawnAttr` is constructed only after `posix_spawnattr_init`
        // succeeds, and `drop` has exclusive access to the still-live value.
        let _ = unsafe { libc::posix_spawnattr_destroy(&raw mut self.0) };
    }
}

/// The absolute path of the running executable, sourced from the kernel rather
/// than `argv[0]` so copied or renamed solver images relaunch themselves.
pub(super) fn self_path() -> Option<CString> {
    let exe = std::env::current_exe().ok()?;
    CString::new(OsString::from(exe).into_vec()).ok()
}

/// Build an initialized spawn attribute carrying a fatal jetsam limit.
fn jetsam_attr(limit: FootprintLimit) -> SpawnAttr {
    let mut raw = MaybeUninit::<libc::posix_spawnattr_t>::uninit();
    // SAFETY: `posix_spawnattr_init` accepts writable storage for an
    // uninitialized attribute and initializes it completely on success.
    if unsafe { libc::posix_spawnattr_init(raw.as_mut_ptr()) } != 0 {
        fail_closed("could not initialise posix_spawnattr_t for the jetsam limit");
    }
    // SAFETY: the successful initialization immediately above initialized all
    // of `raw`; `SpawnAttr` will destroy the value exactly once.
    let mut attr = SpawnAttr(unsafe { raw.assume_init() });
    // SETEXEC replaces this process rather than leaving a waiting parent.
    // This preserves the caller-visible pid and normal exec
    // signal semantics while still letting the kernel apply spawn attributes.
    // SAFETY: `attr` is initialized and exclusively borrowed; SETEXEC is a
    // Darwin spawn flag whose 0x0040 value is exported by `libc`.
    let flags_rc = unsafe {
        libc::posix_spawnattr_setflags(&raw mut attr.0, libc::POSIX_SPAWN_SETEXEC as libc::c_short)
    };
    if flags_rc != 0 {
        drop(attr);
        fail_closed("could not configure posix_spawn to replace this process");
    }
    // SAFETY: `attr` is initialized and exclusively borrowed for this call;
    // the canonical policy leaf validates and prepares only footprint fields.
    if let Err(error) = unsafe { limit.prepare(&mut attr.0) } {
        drop(attr);
        fail_closed(&format!(
            "native footprint policy refused the budget: {error}"
        ));
    }
    attr
}

fn child_arguments(exe: &CString) -> Vec<CString> {
    let mut arguments = vec![exe.clone()];
    for argument in std::env::args_os().skip(1) {
        match CString::new(argument.into_vec()) {
            Ok(argument) => arguments.push(argument),
            Err(_) => fail_closed("an argument contains an interior NUL byte"),
        }
    }
    arguments
}

fn environment_entry(key: &OsStr, value: &OsStr) -> CString {
    let mut entry = key.as_bytes().to_vec();
    entry.push(b'=');
    entry.extend_from_slice(value.as_bytes());
    match CString::new(entry) {
        Ok(entry) => entry,
        Err(_) => fail_closed("an environment entry contains an interior NUL byte"),
    }
}

/// Copy the parent's environment while installing markers only in the child.
/// This avoids process-global mutation in the safe public [`super::arm`] API.
fn child_environment() -> Vec<CString> {
    let armed = OsStr::new(ARMED_ENV);
    let root_pid = OsStr::new(ROOT_PID_ENV);
    let mut environment: Vec<CString> = std::env::vars_os()
        .filter(|(key, _)| key != armed && key != root_pid)
        .map(|(key, value)| environment_entry(&key, &value))
        .collect();
    environment.push(environment_entry(armed, OsStr::new("1")));
    let pid = std::process::id().to_string();
    environment.push(environment_entry(root_pid, OsStr::new(&pid)));
    environment
}

fn nul_terminated_pointers(strings: &[CString]) -> Vec<*const libc::c_char> {
    let mut pointers: Vec<_> = strings.iter().map(|value| value.as_ptr()).collect();
    pointers.push(std::ptr::null());
    pointers
}

/// Validate before computing L2 or modifying any native process policy.
pub(super) fn footprint_limit(budget: u64) -> FootprintLimit {
    let Ok(limit_mb) = u32::try_from(budget) else {
        fail_closed("footprint budget does not fit in the jetsam limit type");
    };
    match FootprintLimit::new(limit_mb) {
        Ok(limit) => limit,
        Err(error) => fail_closed(&format!("invalid native footprint budget: {error}")),
    }
}

/// Replace this image with a fatal footprint limit, retaining PID and birth.
pub(super) fn reexec_self_governed(limit: FootprintLimit, exe: &CString) -> ! {
    let attr = jetsam_attr(limit);
    let arguments = child_arguments(exe);
    let argument_pointers = nul_terminated_pointers(&arguments);
    let environment = child_environment();
    let environment_pointers = nul_terminated_pointers(&environment);

    let mut pid: libc::pid_t = 0;
    // SAFETY: the path and both pointer arrays are NUL-terminated; every string
    // backing their pointers remains live and immutable for the whole call.
    let rc = unsafe {
        libc::posix_spawn(
            &raw mut pid,
            exe.as_ptr(),
            std::ptr::null(),
            &raw const attr.0,
            argument_pointers.as_ptr().cast(),
            environment_pointers.as_ptr().cast(),
        )
    };
    drop(attr);
    if rc != 0 {
        fail_closed(&format!(
            "posix_spawn SETEXEC of the governed image failed (rc {rc})"
        ));
    }
    fail_closed("posix_spawn SETEXEC unexpectedly returned success")
}

#[cfg(test)]
mod tests;
