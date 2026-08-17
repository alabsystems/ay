// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `resource` to preserve item DefPaths.

/// The signal a `Stopped` observation carries.
///
/// `nix` is declared `[target.'cfg(unix)'.dependencies]`, so naming
/// `nix::sys::signal::Signal` in this enum unconditionally is what stopped
/// `ay-bench` compiling off Unix at all. Off Unix there is no
/// `waitid(..., WNOWAIT)` and no `nix`, and the only `observe_child_unreaped`
/// that compiles there fails closed without ever producing a state — so
/// `Infallible` is the accurate payload: it keeps the variant type-checked
/// while saying in the type system that nothing can construct it.
#[cfg(unix)]
type StopSignal = nix::sys::signal::Signal;
#[cfg(not(unix))]
type StopSignal = std::convert::Infallible;

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum UnreapedChildState {
    Running,
    Stopped(StopSignal),
    Exited,
}

// On UNIX platforms without `waitid(..., WNOWAIT)`, observation fails closed
// before producing a state. Keep an exhaustive compile-time witness so all
// variants remain type-checked on those targets as well as on the supported
// ones. Off Unix the witness cannot exist — `Stopped` is uninhabited there, by
// construction — and it is not needed: the enum declaration alone type-checks
// every variant.
#[cfg(all(
    unix,
    not(any(
        target_os = "android",
        target_os = "freebsd",
        target_os = "haiku",
        target_os = "macos",
        all(target_os = "linux", not(target_env = "uclibc")),
    ))
))]
const UNREAPED_CHILD_STATE_TYPE_WITNESS: [UnreapedChildState; 3] = [
    UnreapedChildState::Running,
    UnreapedChildState::Stopped(nix::sys::signal::Signal::SIGSTOP),
    UnreapedChildState::Exited,
];
