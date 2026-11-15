// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Darwin's native waitid interface, without consuming the child's wait status.
//! The syscall stays in ay-sys; this module applies MaxSAT custody policy.

use super::{Child, Duration, Instant, MaxSatUnreapedChildState};
use anyhow::{bail, Context, Result};
use ay_sys::darwin_child::{Event, Events};
use nix::libc;

fn observation(child: &Child, include_stopped: bool, label: &str) -> Result<Option<Event>> {
    let events = if include_stopped {
        Events::ExitOrStop
    } else {
        Events::ExitOnly
    };
    ay_sys::darwin_child::observe(child, events)
        .with_context(|| format!("{label}: observing child without reaping failed"))
}

pub(super) fn observe_maxsat_child_unreaped(
    child: &Child,
    include_stopped: bool,
    label: &str,
) -> Result<MaxSatUnreapedChildState> {
    match observation(child, include_stopped, label)? {
        Some(Event::Exited(_) | Event::Killed(_) | Event::Dumped(_)) => {
            Ok(MaxSatUnreapedChildState::Exited)
        }
        Some(Event::Stopped(_)) if include_stopped => Ok(MaxSatUnreapedChildState::Stopped),
        // Darwin can return a pending stop even without WSTOPPED. An exit-only
        // observer must treat it as alive, as WEXITED-only does on other Unix
        // hosts; it must neither consume that stop nor mistake it for exit.
        None | Some(Event::Stopped(_) | Event::Continued) => Ok(MaxSatUnreapedChildState::Running),
    }
}

pub(super) fn wait_for_maxsat_guard_stop(child: &Child, label: &str) -> Result<()> {
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        if let Some(event) = observation(child, true, label)? {
            if event == Event::Stopped(libc::SIGSTOP) {
                return Ok(());
            }
            bail!("{label}: child exited or changed state before watchdog arming: {event:?}");
        }
        if Instant::now() >= deadline {
            bail!("{label}: MaxSAT child did not enter its watchdog safety stop");
        }
        std::thread::sleep(Duration::from_millis(5));
    }
}
