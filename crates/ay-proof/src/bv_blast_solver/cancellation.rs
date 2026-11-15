// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One irreversible caller refusal across expression export and proof production.

pub(super) fn run<T>(
    keep_going: &mut dyn FnMut() -> bool,
    operation: impl FnOnce(&mut dyn FnMut() -> bool) -> T,
) -> T {
    let mut refused = false;
    let mut sticky = || {
        if refused {
            return false;
        }
        // Pre-latch so catching a callback panic cannot revive this attempt.
        refused = true;
        let accepted = keep_going();
        if accepted {
            refused = false;
        }
        accepted
    };
    operation(&mut sticky)
}
