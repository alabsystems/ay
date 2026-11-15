// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Call-local, sticky cancellation for ground-evidence validation.
//!
//! The control also carries one lexical mode bit that selects the work
//! envelope of the whole-problem source preflight (wire artifact or native
//! validation); see `with_native_whole_source_scope`. The bit never grants a
//! capability and adds no poll.
//!
//! This is not resource accounting or a wall-clock latency guarantee. Opaque
//! evaluator, normalization, arithmetic, allocator and destructor operations
//! may run between polls. A refused poll must never be converted to an
//! indeterminate value, a malformed artifact, or a successful capability.

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct GroundValidationInterrupted;

pub(super) struct GroundValidationControl<'a> {
    progress: &'a mut dyn FnMut() -> bool,
    stopped: bool,
    /// Set only inside `with_native_whole_source_scope`.
    native_whole_source: bool,
    /// NATIVE (in-process) validation of a derivation AY built itself, as
    /// opposed to a wire artifact: the per-derivation source-surface cache
    /// then admits against `CHC_GROUND_DERIVATION_NATIVE_SOURCE_WORK` instead
    /// of the wire cap. Set only by `new_native`; never changes what a
    /// derivation must prove.
    native: bool,
}

impl<'a> GroundValidationControl<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            progress,
            stopped: false,
            native_whole_source: false,
            native: false,
        }
    }

    /// A control for NATIVE validation (`validate_ground_derivation`): the
    /// same polls and the same semantic checks as a wire control, with the
    /// native source-surface envelope for the derivation's clauses.
    pub(super) fn new_native(progress: &'a mut dyn FnMut() -> bool) -> Self {
        Self {
            native: true,
            ..Self::new(progress)
        }
    }

    /// Whether this is native (in-process) validation.
    pub(super) fn is_native(&self) -> bool {
        self.native
    }

    /// Run `body` with the whole-problem source preflight in NATIVE mode.
    ///
    /// The wire envelope prices the artifact's canonical whole-problem
    /// identity, which native validation never renders or orders. Inside this
    /// scope the preflight admits against the larger, still FINITE native
    /// envelope (`source_identity::NATIVE_WHOLE_SOURCE_WORK`) and remains the
    /// size bound for the tree-walking live validators behind it. Artifact
    /// encode/decode run their wire-limited preflight outside this scope
    /// first, so their admission and error order are unchanged. The previous
    /// mode is restored on return and on unwind; this adds no poll.
    pub(super) fn with_native_whole_source_scope<T>(
        &mut self,
        body: impl FnOnce(&mut Self) -> T,
    ) -> T {
        let outer = std::mem::replace(&mut self.native_whole_source, true);
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| body(&mut *self)));
        self.native_whole_source = outer;
        match result {
            Ok(value) => value,
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    /// Whether the whole-problem source preflight runs in native mode.
    pub(super) fn native_whole_source(&self) -> bool {
        self.native_whole_source
    }

    pub(super) fn poll(&mut self) -> Result<(), GroundValidationInterrupted> {
        if !self.stopped && (self.progress)() {
            return Ok(());
        }
        self.stopped = true;
        Err(GroundValidationInterrupted)
    }

    pub(super) fn is_stopped(&self) -> bool {
        self.stopped
    }
}

impl From<GroundValidationInterrupted> for super::GroundDerivationError {
    fn from(_: GroundValidationInterrupted) -> Self {
        Self::Interrupted
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn refusal_is_sticky_even_if_the_callback_would_resume() {
        let mut calls = 0;
        let mut progress = || {
            calls += 1;
            calls != 2
        };
        let mut control = GroundValidationControl::new(&mut progress);
        assert_eq!(control.poll(), Ok(()));
        assert!(!control.is_stopped());
        assert_eq!(control.poll(), Err(GroundValidationInterrupted));
        assert!(control.is_stopped());
        assert_eq!(control.poll(), Err(GroundValidationInterrupted));
        assert_eq!(calls, 2);
    }

    #[test]
    fn native_whole_source_scope_is_lexical_and_adds_no_poll() {
        let mut calls = 0;
        let mut progress = || {
            calls += 1;
            true
        };
        let mut control = GroundValidationControl::new(&mut progress);
        assert!(!control.native_whole_source());
        let inside =
            control.with_native_whole_source_scope(|control| control.native_whole_source());
        assert!(inside);
        assert!(!control.native_whole_source());
        // A control shared with a later wire-limited caller must not inherit
        // native mode from an unwinding body.
        let unwound = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            control.with_native_whole_source_scope(|_| -> bool { panic!("native scope unwinds") })
        }));
        assert!(unwound.is_err());
        assert!(!control.native_whole_source());
        assert_eq!(calls, 0);
    }
}
