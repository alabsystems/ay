// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Borrowed caller cancellation for one planning and emission attempt.

use std::cell::{Cell, RefCell};
use std::rc::Rc;

#[derive(Clone, Copy, PartialEq, Eq)]
enum State {
    Open,
    Polling,
    Refused,
}

struct Shared<'a> {
    caller: RefCell<Option<&'a mut dyn FnMut() -> bool>>,
    state: Cell<State>,
}

#[derive(Clone, Default)]
pub(super) struct EmissionProgress<'a> {
    shared: Option<Rc<Shared<'a>>>,
}

impl<'a> EmissionProgress<'a> {
    pub(super) fn with_caller(caller: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            shared: Some(Rc::new(Shared {
                caller: RefCell::new(Some(caller)),
                state: Cell::new(State::Open),
            })),
        }
    }

    pub(super) fn poll(&self) -> bool {
        let Some(shared) = &self.shared else {
            return true;
        };
        if shared.state.get() != State::Open {
            shared.state.set(State::Refused);
            return false;
        }
        let Ok(mut caller) = shared.caller.try_borrow_mut() else {
            shared.state.set(State::Refused);
            return false;
        };
        let Some(caller) = caller.as_mut() else {
            return true;
        };
        // Polling is already a refusal if the callback unwinds or re-enters.
        shared.state.set(State::Polling);
        let accepted = caller();
        if accepted && shared.state.get() == State::Polling {
            shared.state.set(State::Open);
            true
        } else {
            shared.state.set(State::Refused);
            false
        }
    }

    pub(super) fn refused(&self) -> bool {
        self.shared
            .as_ref()
            .is_some_and(|shared| shared.state.get() != State::Open)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn a_refused_callback_is_never_polled_again() {
        let calls = Cell::new(0);
        let mut callback = || {
            calls.set(calls.get() + 1);
            calls.get() != 1
        };
        let progress = EmissionProgress::with_caller(&mut callback);
        assert!(!progress.poll());
        assert!(!progress.poll());
        assert_eq!(calls.get(), 1);
    }

    #[test]
    fn nested_observations_share_the_original_refusal() {
        let mut callback = || false;
        let owner = EmissionProgress::with_caller(&mut callback);
        let nested = owner.clone();
        assert!(!nested.poll());
        assert!(owner.refused());
        assert!(!owner.poll());
    }

    #[test]
    fn a_caught_callback_panic_cannot_revive_the_attempt() {
        let mut callback = || panic!("cancel callback unwound");
        let progress = EmissionProgress::with_caller(&mut callback);
        assert!(
            std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| progress.poll())).is_err()
        );
        assert!(!progress.poll());
    }
}

#[cfg(test)]
#[path = "emission_progress_export_tests.rs"]
mod export_tests;
