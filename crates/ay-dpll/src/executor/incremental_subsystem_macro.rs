// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by executor to preserve item paths.

/// Central registry of incremental subsystems (#5992).
///
/// Adding a new incremental subsystem requires:
/// 1. Implementing `IncrementalSubsystem` for the type
/// 2. Adding the field to this macro (and whether it's `Option<T>` or direct)
///
/// The macro dispatches push/pop/reset to all subsystems uniformly,
/// eliminating the 4×N shotgun surgery pattern.
macro_rules! for_each_incremental_subsystem {
    // Push: init-or-get for Option fields, call directly for non-Option.
    (push $self:expr, $n:expr) => {{
        let bv = $self
            .incr_bv_state
            .get_or_insert_with(IncrementalBvState::new);
        for _ in 0..$n {
            bv.push();
        }
        // NOTE: Theory state has special pre-push assertion logic handled
        // by the caller before this macro invocation. The push itself is
        // dispatched here.
        let fp = $self
            .incr_fp_state
            .get_or_insert_with(IncrementalFpState::new);
        fp.record_incremental_entry(&$self.ctx.assertions);
        for _ in 0..$n {
            fp.push();
        }
        let ts = $self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        for _ in 0..$n {
            ts.push();
        }
        let qm = $self
            .quantifier_manager
            .get_or_insert_with(QuantifierManager::new);
        for _ in 0..$n {
            qm.push();
        }
        for _ in 0..$n {
            $self.proof_tracker.push();
        }
    }};
    // Pop: if-let for Option fields, call directly for non-Option.
    // Returns true if all subsystems popped successfully.
    (pop $self:expr, $n:expr) => {{
        let mut ok = true;
        if let Some(ref mut s) = $self.incr_bv_state {
            for _ in 0..$n {
                ok &= s.pop();
            }
        }
        if let Some(ref mut s) = $self.incr_fp_state {
            for _ in 0..$n {
                ok &= s.pop();
            }
        }
        if let Some(ref mut s) = $self.incr_theory_state {
            for _ in 0..$n {
                let popped = s.pop();
                ok &= popped;
            }
        }
        if let Some(ref mut s) = $self.quantifier_manager {
            for _ in 0..$n {
                let popped = s.pop();
                ok &= popped;
            }
        }
        for _ in 0..$n {
            let popped = $self.proof_tracker.pop();
            ok &= popped;
        }
        ok
    }};
    // Reset: if-let for Option fields, call directly for non-Option.
    (reset $self:expr) => {{
        if let Some(ref mut s) = $self.incr_bv_state {
            s.reset();
        }
        if let Some(ref mut s) = $self.incr_fp_state {
            s.reset();
        }
        if let Some(ref mut s) = $self.incr_theory_state {
            s.reset();
        }
        if let Some(ref mut s) = $self.quantifier_manager {
            s.reset();
        }
        $self.proof_tracker.reset();
    }};
    // Drop: set Option fields to None, reset non-Option fields.
    // Used by ResetAssertions which discards all state.
    (drop $self:expr) => {{
        $self.incr_bv_state = None;
        $self.incr_fp_state = None;
        $self.incr_theory_state = None;
        $self.quantifier_manager = None;
        $self.proof_tracker.reset();
    }};
}
