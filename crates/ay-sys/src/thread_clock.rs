// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One thread's CPU clock, readable from any thread.
//!
//! [`crate::thread_cpu_time`] reads the CALLING thread's clock. A solve that
//! is stopped by a watchdog is the opposite shape: the watchdog polls on its
//! own thread and must ask how much CPU the SOLVING thread has spent. That is
//! the reading a work budget needs, because a wall-clock slice is also spent
//! by every interval in which the scheduler ran somebody else — under CPU
//! contention a slice that would have finished the solve is exhausted before
//! the solve has done the work, and the caller's verdict then depends on the
//! machine's load rather than on the problem.

use std::time::Duration;

/// A captured handle on one thread's CPU clock.
///
/// Capture it on the thread to be measured with [`Self::current`]; read it
/// from any thread with [`Self::elapsed`] while that thread is alive. A
/// reading after the thread has exited is `None` or meaningless, so callers
/// must scope the handle to work they join before the thread moves on.
#[derive(Clone, Copy, Debug)]
pub struct ThreadCpuClock {
    #[cfg(target_os = "macos")]
    port: libc::mach_port_t,
    #[cfg(target_os = "linux")]
    clock: libc::clockid_t,
}

impl ThreadCpuClock {
    /// The calling thread's clock; `None` on a platform without per-thread
    /// CPU accounting, or when the platform refuses the handle.
    #[must_use]
    pub fn current() -> Option<Self> {
        current_impl()
    }

    /// CPU time (user plus system) the captured thread has consumed since it
    /// started; `None` when the read fails.
    #[must_use]
    pub fn elapsed(&self) -> Option<Duration> {
        elapsed_impl(self)
    }
}

#[cfg(target_os = "macos")]
fn current_impl() -> Option<ThreadCpuClock> {
    // SAFETY: `pthread_self` has no preconditions; `pthread_mach_thread_np`
    // returns the kernel port name of a live pthread without adding a port
    // reference, so there is nothing to deallocate.
    let port = unsafe { libc::pthread_mach_thread_np(libc::pthread_self()) };
    (port != 0).then_some(ThreadCpuClock { port })
}

#[cfg(target_os = "macos")]
fn elapsed_impl(clock: &ThreadCpuClock) -> Option<Duration> {
    let mut info = std::mem::MaybeUninit::<libc::thread_basic_info>::zeroed();
    let mut count = libc::THREAD_BASIC_INFO_COUNT;
    let flavor = libc::thread_flavor_t::try_from(libc::THREAD_BASIC_INFO).ok()?;
    // SAFETY: `info` is writable storage for one `thread_basic_info`, and
    // `count` states its size in `integer_t` words, which the kernel checks
    // before writing. A stale port name makes the call fail, not write.
    let ret = unsafe {
        libc::thread_info(
            clock.port,
            flavor,
            info.as_mut_ptr().cast::<libc::integer_t>(),
            &raw mut count,
        )
    };
    if ret != libc::KERN_SUCCESS {
        return None;
    }
    // SAFETY: KERN_SUCCESS means the kernel filled the structure; it was
    // zero-initialised before the call in any case.
    let info = unsafe { info.assume_init() };
    let user = time_value(info.user_time)?;
    let system = time_value(info.system_time)?;
    user.checked_add(system)
}

#[cfg(target_os = "macos")]
fn time_value(value: libc::time_value_t) -> Option<Duration> {
    let seconds = u64::try_from(value.seconds).ok()?;
    let micros = u64::try_from(value.microseconds).ok()?;
    Duration::from_secs(seconds).checked_add(Duration::from_micros(micros))
}

#[cfg(target_os = "linux")]
fn current_impl() -> Option<ThreadCpuClock> {
    let mut clock: libc::clockid_t = 0;
    // SAFETY: `pthread_self` has no preconditions and `clock` is valid
    // writable storage for the returned clock id.
    let ret = unsafe { libc::pthread_getcpuclockid(libc::pthread_self(), &raw mut clock) };
    (ret == 0).then_some(ThreadCpuClock { clock })
}

#[cfg(target_os = "linux")]
fn elapsed_impl(clock: &ThreadCpuClock) -> Option<Duration> {
    // SAFETY: `libc::timespec` is plain old data; zero-init is a valid value
    // before `clock_gettime` overwrites every field.
    let mut ts: libc::timespec = unsafe { std::mem::zeroed() };
    // SAFETY: `ts` is valid writable memory for the duration of the call.
    let ret = unsafe { libc::clock_gettime(clock.clock, &raw mut ts) };
    if ret != 0 {
        return None;
    }
    let secs = u64::try_from(ts.tv_sec).ok()?;
    let nanos = u32::try_from(ts.tv_nsec).ok()?;
    Some(Duration::new(secs, nanos))
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn current_impl() -> Option<ThreadCpuClock> {
    None
}

#[cfg(not(any(target_os = "macos", target_os = "linux")))]
fn elapsed_impl(_clock: &ThreadCpuClock) -> Option<Duration> {
    None
}

#[cfg(test)]
mod tests;
