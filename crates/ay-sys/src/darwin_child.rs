// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Non-consuming observations of an owned Darwin child.

use std::{io, process::Child};

/// Events requested from the kernel; neither choice consumes wait status.
#[derive(Clone, Copy, Debug)]
pub enum Events {
    ExitOnly,
    ExitOrStop,
}

/// A native child event, with exit codes and signals kept distinct.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Event {
    Exited(i32),
    Killed(i32),
    Dumped(i32),
    Stopped(i32),
    Continued,
}

/// Observe `child` without reaping it. The caller retains sole responsibility
/// for its final consuming wait and must not reap concurrently with this call.
/// A reported event always belongs to this child's positive PID. Darwin may
/// report a pending stop even for [`Events::ExitOnly`]; it remains a stop.
pub fn observe(child: &Child, events: Events) -> io::Result<Option<Event>> {
    let pid = libc::pid_t::try_from(child.id())
        .ok()
        .filter(|pid| *pid > 0)
        .ok_or_else(|| io::Error::new(io::ErrorKind::InvalidInput, "invalid child PID"))?;
    let mut flags = libc::WEXITED | libc::WNOHANG | libc::WNOWAIT;
    if matches!(events, Events::ExitOrStop) {
        flags |= libc::WSTOPPED;
    }
    // SAFETY: Darwin's siginfo_t contains scalar fields and padding, for which
    // zero is valid. Zeroing also distinguishes a WNOHANG call with no event.
    let mut info: libc::siginfo_t = unsafe { std::mem::zeroed() };
    // SAFETY: info is writable siginfo_t storage, and P_PID selects only this
    // Child's positive PID. WNOWAIT preserves its final owner's wait status.
    let status = unsafe { libc::waitid(libc::P_PID, pid as libc::id_t, &raw mut info, flags) };
    if status != 0 {
        return Err(io::Error::last_os_error());
    }
    if info.si_pid == 0 {
        return Ok(None);
    }
    if info.si_pid != pid || info.si_signo != libc::SIGCHLD {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "waitid returned a foreign child notification",
        ));
    }
    let event = match info.si_code {
        libc::CLD_EXITED => Event::Exited(info.si_status),
        libc::CLD_KILLED => Event::Killed(info.si_status),
        libc::CLD_DUMPED => Event::Dumped(info.si_status),
        libc::CLD_STOPPED => Event::Stopped(info.si_status),
        libc::CLD_CONTINUED => Event::Continued,
        _ => {
            return Err(io::Error::new(
                io::ErrorKind::InvalidData,
                "waitid returned an unknown child event",
            ));
        }
    };
    Ok(Some(event))
}

#[cfg(test)]
mod tests;
