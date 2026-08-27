// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guarded scaled-equality discovery: `mode = g  =>  B - k*A = c`.
//!
//! # The gap this closes
//!
//! An accumulator's closed form often depends on a MODE that is fixed at entry
//! and never written again. `dillig12_m_000` is the canonical shape: one loop
//! advances two accumulators, and the fifth argument `J` selects how fast the
//! second one climbs.
//!
//! ```text
//! (= H (+ C F))                          ; C' = C + A + 1
//! (= I (ite (= J 1) (+ E F) E))          ; D' = D + B + 1, twice over when J = 1
//! ```
//!
//! so after `n` steps `C = n(n+1)/2` and `D` is `n(n+1)` when `J = 1` and
//! `n(n+1)/2` otherwise. Both are exact linear relations between `C` and `D`,
//! but each holds only on ITS OWN branch:
//!
//! ```text
//! J  = 1  =>  D - 2*C = 0
//! J != 1  =>  D - 1*C = 0
//! ```
//!
//! The pass enumerates equality guards such as `J = 1`; the complementary
//! relation above explains why the corresponding unguarded candidate is
//! invalid, but is not itself synthesized as a `J != 1` candidate.
//!
//! Neither is an invariant unguarded — one step with `J != 1` reaches
//! `C = D = 1`, where `D - 2*C = -1`, and one step with `J = 1` reaches
//! `C = 1, D = 2`, where `D - C = 1`. Discovering them WITHOUT the guard is
//! therefore not merely imprecise, it is wrong, and a pass that emits both
//! unguarded contradicts itself (the two agree only at `C = 0`).
//!
//! The unguarded scaled-difference pass (`bounds_scaled_diff.rs`) can only say
//! `B - k*A >= c`, so it cannot express either of these, and the safety proof
//! needs one of them: the exit clause publishes
//! `(ite (= C 1) (+ 2 D (* (- 2) E)) 1)`, which is pinned at 2 exactly when
//! `D = 2*C`, and that bound on the downstream counter is what blocks the query.
//!
//! # What makes it sound
//!
//! The guard is not assumed — the WHOLE implication is the candidate, and it is
//! checked as one formula on both obligations:
//!
//! * INIT: for every fact clause, `constraint AND NOT lemma[head]` is UNSAT.
//! * PRESERVATION: for every self-loop, the current survivor conjunction at the
//!   body, the transition constraint, and `NOT candidate[head]` are UNSAT.
//!   Emitted survivors then pass the ordinary full admission checks, including
//!   incoming transitions and actual-frame self-induction.
//!
//! `Unknown` from the solver rejects, exactly as the sibling passes do. Because
//! the implication is validated as a unit, a candidate that only holds on one
//! branch is admitted with the branch attached, and one that holds on neither is
//! not admitted at all. The mode is required to be a LATCH (every self-loop passes
//! it through unchanged), so `guard[body]` and `guard[head]` denote the same
//! condition and preservation is not vacuous.

use super::*;

/// Cap on Houdini refinement rounds. The loop shrinks a finite candidate set
/// and so terminates on its own; this only bounds pathological cost, and giving
/// up discards the whole set rather than emitting a half-pruned one.
const GUARDED_EQ_MAX_HOUDINI_ROUNDS: usize = 8;

/// A candidate `B - k*A = c`, optionally guarded, over canonical arguments.
#[derive(Clone, Copy)]
pub(in crate::pdr::solver) struct GuardedEquality {
    /// `None` means the equality holds unconditionally.
    ///
    /// The unguarded case is needed after adaptive case splitting specializes
    /// away the mode test. The same INIT and preservation checks validate both
    /// forms; only the antecedent differs.
    guard: Option<ModeGuard>,
    a_idx: usize,
    b_idx: usize,
    k: i128,
    c: i128,
}

/// A candidate mode guard: canonical argument `idx` equal to `value`.
#[derive(Clone, Copy, PartialEq, Eq)]
pub(in crate::pdr::solver) struct ModeGuard {
    idx: usize,
    value: i128,
}

mod candidates;
mod discovery;
mod validation;

#[cfg(test)]
mod tests;
