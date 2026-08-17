// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! macOS L1 capability detection and self-spawn support.

use super::{fail_closed, ARMED_ENV, ROOT_PID_ENV, TASKPOLICY};
use std::ffi::{CString, OsStr, OsString};
use std::mem::{zeroed, MaybeUninit};
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::process::{Command, Stdio};

/// Darwin major version of macOS 14 (Sonoma), the first release whose
/// `taskpolicy` accepts `-m <MB>`. Used only to skip the probe in
/// [`l1_installable`], never to conclude that the flag is missing.
const DARWIN_SONOMA: u32 = 23;

/// Program the `taskpolicy` probe runs. It only needs to exist and exit 0, so a
/// non-zero status isolates `taskpolicy`'s own rejection of `-m`.
const PROBE_PROGRAM: &str = "/usr/bin/true";

unsafe extern "C" {
    /// Private libSystem API (`spawn_private.h`), exported from
    /// `libsystem_kernel.dylib` as `_posix_spawnattr_setjetsam_ext`.
    ///
    /// This is what `taskpolicy -m` itself calls — confirmed by
    /// `strings /usr/sbin/taskpolicy` containing no `memorystatus` symbols.
    /// Using it directly gets the same kernel-enforced cap on hosts whose
    /// `taskpolicy` predates the `-m` flag.
    fn posix_spawnattr_setjetsam_ext(
        attr: *mut libc::posix_spawnattr_t,
        flags: libc::c_short,
        priority: libc::c_int,
        memlimit_active: libc::c_int,
        memlimit_inactive: libc::c_int,
    ) -> libc::c_int;
}

/// Exceeding the active limit kills rather than merely deprioritising.
const POSIX_SPAWN_JETSAM_MEMLIMIT_ACTIVE_FATAL: u16 = 0x0004;
/// Same for the inactive limit; a backgrounded solver must be capped too.
const POSIX_SPAWN_JETSAM_MEMLIMIT_INACTIVE_FATAL: u16 = 0x0008;

/// Apple XNU's `bsd/sys/spawn_internal.h` defines the two fatal flags as 0x04
/// and 0x08. `posix_spawnattr_setjetsam_ext` adds the private 0x8000 "set" bit
/// itself, so callers pass only these two flags, as `taskpolicy` does.
const JETSAM_FATAL_FLAGS: u16 =
    POSIX_SPAWN_JETSAM_MEMLIMIT_ACTIVE_FATAL | POSIX_SPAWN_JETSAM_MEMLIMIT_INACTIVE_FATAL;

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

/// This kernel's Darwin major version, e.g. `22` for `22.6.0`.
fn darwin_major() -> Option<u32> {
    // SAFETY: `libc::utsname` consists of fixed-size `c_char` arrays, for which
    // the all-zero bit pattern is valid.
    let mut name = unsafe { zeroed::<libc::utsname>() };
    // SAFETY: `name` is an owned, aligned `utsname` and the pointer is exclusive
    // for the call. The return value is checked before populated fields are read.
    if unsafe { libc::uname(&raw mut name) } != 0 {
        return None;
    }
    let release: Vec<u8> = name
        .release
        .iter()
        .take_while(|&&byte| byte != 0)
        .map(|&byte| byte as u8)
        .collect();
    std::str::from_utf8(&release)
        .ok()?
        .split('.')
        .next()?
        .parse()
        .ok()
}

/// Build an initialized spawn attribute carrying a fatal jetsam limit.
fn jetsam_attr(limit_mb: i32) -> SpawnAttr {
    let mut raw = MaybeUninit::<libc::posix_spawnattr_t>::uninit();
    // SAFETY: `posix_spawnattr_init` accepts writable storage for an
    // uninitialized attribute and initializes it completely on success.
    if unsafe { libc::posix_spawnattr_init(raw.as_mut_ptr()) } != 0 {
        fail_closed("could not initialise posix_spawnattr_t for the jetsam limit");
    }
    // SAFETY: the successful initialization immediately above initialized all
    // of `raw`; `SpawnAttr` will destroy the value exactly once.
    let mut attr = SpawnAttr(unsafe { raw.assume_init() });
    // `taskpolicy` uses SETEXEC so `posix_spawn` replaces it instead of leaving
    // a waiting parent. This preserves the caller-visible pid and normal exec
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
    // all other arguments are values in the private API's documented domains.
    let rc = unsafe {
        posix_spawnattr_setjetsam_ext(
            &raw mut attr.0,
            JETSAM_FATAL_FLAGS as libc::c_short,
            0,
            limit_mb,
            limit_mb,
        )
    };
    if rc != 0 {
        drop(attr);
        fail_closed("posix_spawnattr_setjetsam_ext refused the footprint budget");
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

/// Replace this process with the same image carrying a fatal jetsam memlimit.
/// This is the `taskpolicy`-free form of L1 for hosts whose `taskpolicy` has no
/// `-m`. Darwin's `POSIX_SPAWN_SETEXEC` makes the call an exec operation, which
/// preserves the caller-visible pid and does not leave a supervising process.
pub(super) fn reexec_self_governed(budget: u64, exe: &CString) -> ! {
    let Ok(limit_mb) = i32::try_from(budget) else {
        fail_closed("footprint budget does not fit in the jetsam limit type");
    };
    let attr = jetsam_attr(limit_mb);
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

/// Whether L1 can be installed through this host's `taskpolicy` executable.
/// The Darwin version is only a fast path; older or unknown versions are
/// decided by running the exact command before the point of no return.
pub(super) fn l1_installable(budget: u64) -> bool {
    if darwin_major().is_some_and(|major| major >= DARWIN_SONOMA) {
        return true;
    }
    Command::new(TASKPOLICY)
        .arg("-m")
        .arg(budget.to_string())
        .arg(PROBE_PROGRAM)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .is_ok_and(|status| status.success())
}

#[cfg(test)]
mod tests {
    use super::{
        child_environment, darwin_major, l1_installable, Command, Stdio, ARMED_ENV, PROBE_PROGRAM,
        ROOT_PID_ENV, TASKPOLICY,
    };

    #[test]
    fn child_environment_installs_exact_governance_markers() {
        let environment = child_environment();
        let entries: Vec<&[u8]> = environment.iter().map(|entry| entry.as_bytes()).collect();
        let armed = format!("{ARMED_ENV}=1");
        let root_pid = format!("{ROOT_PID_ENV}={}", std::process::id());

        assert_eq!(
            entries
                .iter()
                .filter(|entry| **entry == armed.as_bytes())
                .count(),
            1
        );
        assert_eq!(
            entries
                .iter()
                .filter(|entry| **entry == root_pid.as_bytes())
                .count(),
            1
        );
    }

    #[test]
    fn darwin_fast_path_agrees_with_the_taskpolicy_probe() {
        let authority = Command::new(TASKPOLICY)
            .arg("-m")
            .arg("64")
            .arg(PROBE_PROGRAM)
            .stdin(Stdio::null())
            .stdout(Stdio::null())
            .stderr(Stdio::null())
            .status()
            .is_ok_and(|status| status.success());

        assert_eq!(
            l1_installable(64),
            authority,
            "the Darwin {} fast path disagrees with actually running \
             `{TASKPOLICY} -m`; DARWIN_SONOMA is wrong for this host",
            darwin_major().map_or_else(|| "?".to_owned(), |major| major.to_string())
        );
    }

    #[test]
    fn darwin_major_is_readable() {
        assert!(
            darwin_major().is_some_and(|major| major >= 8),
            "uname gave no usable Darwin major version: {:?}",
            darwin_major()
        );
    }
}
