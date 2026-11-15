// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What the deferred-trust discharge's fresh re-decisions read, and the work
//! they no longer redo (R30 point 3, #nested-certification-reuse).
//!
//! # What the funnel reads from a re-decision
//!
//! Steps (4) and (4a) of the deferred-trust discharge, and the ground-core
//! re-decision before them, accept on a fresh executor's `unsat` whose proof
//! passes [`Executor::reconfirm_unsat_within`]'s structural screen: the plain
//! strict check, which accepts a trust-kind rejection as the arm's entry
//! condition. Those callers read only whether the screen declined. A
//! `Checked` nested proof and a `DischargedTrust` one admit the same
//! `discharged-trust` verdict, with the same corroboration record. Only the
//! closed-sentence certificates read the class, because they seal it into a
//! certificate of their own ([`ReconfirmationReading::SealedClass`]).
//!
//! # What the fresh executor spent, and on what
//!
//! The fresh executor is built by `Executor::new()` and a context clone, so
//! it never had the outer query's proof posture: not since the step-(4)
//! re-solve was added (1d9420344, 2026-08-04, after the #A2b meter of
//! a833386c3) and given its proof screen (607b19b5c); `afc9341b1` only moved
//! the two lines into `new_derived_query_executor`. In the CLI's default
//! posture the outer solve runs with the best-effort reconstruction budget
//! (`set_best_effort_produce_proofs`), whose search-time bookkeeping meter
//! runs out early on a large search; the SAT solver then drops its LRAT trace
//! and continues without it. The re-decision had no meter: its whole search
//! kept the trace, with level-0 unit-proof materialization under `reduce_db`
//! and `collect_level0_garbage`. Measured at 85f8d30d3 (release, loaded host):
//! on `fac28` the outer search took 2.0 s and the re-decisions' searches
//! 11.9 s (step 4) and 25.8 s (step 4a); the OUTER search itself takes 15.9 s
//! with the meter removed (`AY_A2B_BUDGET_SCALE=inf`). On `four_dividers`:
//! 3.2 s outer, 8.7 s step (4), 18.4 s for an unmetered outer search.
//!
//! Its proof assembly then ran the trust-elimination members, which exist to
//! replace a trust leaf with a checked derivation or to let the Alethe
//! document print without a `hole`. On `fac28` that took 30.8 s of the
//! step-(4) re-decision, inside `recognize_bv_bitblast_until_stopped` and
//! `replace_with_authored_bv_bitblast_refutation`, and ended in a bare trust
//! closer anyway. The outer assembly had just spent 26 s on the same members
//! of the same problem.
//!
//! # The posture
//!
//! A re-decision whose class nobody reads ([`ReconfirmationReading::EitherClass`])
//! gets three things, and nothing of the outer solve's state:
//!
//! * The outer query's reconstruction budget, so its SAT searches are metered
//!   as the outer's were (`search_proof_bookkeeping_budget`). Under an explicit
//!   proof demand the outer has no budget, and the re-decision keeps none.
//! * A [`ay_sat::keep_proof_inprocessing_after_exhaustion`] scope around it,
//!   so a SAT solver whose meter runs out drops its trace but KEEPS the
//!   proof-mode inprocessing controls. By default exhaustion restores the
//!   controls proof mode disabled (BVE, decompose, factor, SBVA, congruence,
//!   sweep: the transforms with no LRAT support), and that is what the outer
//!   search ran after its own exhaustion. The unmetered re-decision never
//!   exhausted, so it never ran them; with the scope it still does not. The
//!   re-decision therefore does NOT replay the outer's degraded search: an
//!   unproved transform that produced a wrong `unsat` in the outer solve is
//!   not on the re-decision's path, exactly as before.
//! * Proof assembly without the trust-elimination members, through
//!   [`Executor::skips_trust_elimination_repairs`]: the guarded collapse before
//!   promotion and the semantic promotion of Generic bit-vector lemmas (both
//!   in `reassert_final_promotion_boundaries`), the pure bit-vector ground
//!   closure and the authored replacement cascade, the late wire-gap conjunct
//!   repair, the checked-SAT wire-gap retention, and the Final guarded
//!   collapse in `finalize_bv_source_proof`. Everything else in the assembly
//!   still runs: `promote_certified_theory_lemma_kinds`, the folded-assertion
//!   collapses (the small-width bit-vector identity collapse among them),
//!   `rescue_residual_trust_steps`, `certify_euf_and_array_leaves`, the
//!   RM-domain and `str.len` promotions, the exact authored `false`
//!   replacement, the arithmetic reconstruction fallbacks, the derivation
//!   family and the div/mod last resort.
//!
//! # Why this weakens no admission, and what the screen now sees
//!
//! * The verdict is still a fresh executor's own: a new `Executor`, its own
//!   search, the same allowances, controls and stops. The budget and the
//!   kept controls are configuration; no decision of the outer solve crosses
//!   over. The documented evidence of these arms is that reproduction (E1),
//!   never the nested proof's trust-freeness.
//! * The screen is unchanged, and it accepts no proof shape it did not
//!   accept before. A skipped member leaves the proof exactly as a member
//!   that declines leaves it, and every member can decline today (each is
//!   bounded). A meter that runs out leaves a bare trust closer, a shape the
//!   screen already accepted from re-decisions whose reconstruction failed
//!   for another reason (`fac28` and `four_dividers` at 85f8d30d3: `trace
//!   original 4 references unmapped SAT variable 3`, a closer at step t5).
//! * What does move is how far the screen's structural walk gets before its
//!   first trust-kind step, because both changes put that step earlier: the
//!   members no longer promote the Generic bit-vector lemmas past which the
//!   walk would have continued, and an exhausted meter leaves no resolution
//!   steps to walk. The walk was added on top of an arm that accepted a bare
//!   `unsat` for months, and it stays as it was on every re-decision whose
//!   meter does not run out and whose members would have declined.
//!
//! The closed-sentence certificates ([`ReconfirmationReading::SealedClass`])
//! keep the unchanged executor: a `Checked` refutation is authority there.

use super::Executor;

/// What the caller of [`Executor::reconfirm_unsat_within`] reads from the
/// nested proof's screen.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum ReconfirmationReading {
    /// Only whether the screen declined: the deferred-trust discharge's
    /// steps (4) and (4a) and the ground-core re-decision. The fresh executor
    /// runs metered, keeps the proof-mode inprocessing controls past the
    /// meter, and skips the trust-elimination members (module documentation).
    EitherClass,
    /// The class too: the closed-sentence certificates seal it into their
    /// own. The fresh executor runs exactly as it always has.
    SealedClass,
}

impl Executor {
    /// Put `nested`, a fresh re-decision's executor, in the posture `reading`
    /// asks for (module documentation), returning the inprocessing scope its
    /// solve must run inside. [`ReconfirmationReading::SealedClass`] leaves it
    /// untouched and opens no scope.
    pub(super) fn arm_reconfirmation_posture(
        &self,
        nested: &mut Executor,
        reading: ReconfirmationReading,
    ) -> Option<ay_sat::ProofInprocessingKeptAfterExhaustion> {
        if reading == ReconfirmationReading::SealedClass {
            return None;
        }
        nested.set_proof_reconstruction_step_budget(self.proof_reconstruction_step_budget);
        nested.trust_accepting_reconfirmation = true;
        Some(ay_sat::keep_proof_inprocessing_after_exhaustion())
    }

    /// Whether this executor is a re-decision whose proof feeds only a screen
    /// that accepts trust, so its proof assembly skips the members that only
    /// replace trust leaves with checked derivations or repair the printed
    /// document (module documentation names them).
    pub(in crate::executor) fn skips_trust_elimination_repairs(&self) -> bool {
        self.trust_accepting_reconfirmation
    }
}

#[cfg(test)]
#[path = "screened_reconfirmation/tests.rs"]
mod tests;
