// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Finalize-time promotion of the residual intrinsic-tautology leaves.
//!
//! # The gap this closes
//!
//! `SatProofManager` adds an original clause it cannot pedigree as an
//! `assume` (`derivation.rs`: unit → `assume l`; multi-literal →
//! `assume (or l1 .. ln)` + an `or` step). When that assume is not on the
//! problem whitelist, `demote_non_problem_assumptions` rewrites it into a
//! premiseless `Step { rule: Trust }`, and the mandatory strict check then
//! refuses the whole proof with "uses unverified trust rule".
//!
//! The emission-time lane
//! (`sat_proof_manager::exact_fragment::intrinsic_authority`) already answers
//! exactly this question for the exact fragment: if the clause is valid ON ITS
//! OWN, emit the checker's rule for it instead of an `assume`. That lane is
//! only reachable on the exact-fragment route, so on every other route the
//! same clauses arrive here as premiseless `trust`. Measured corpus-wide over
//! the repository's 639 in-tree `.smt2` benchmarks, this is the single largest
//! class of rejected steps that an EXISTING validator already accepts.
//!
//! # Why relabelling is not an authority claim
//!
//! Each battery entry is `validate_*(..).is_ok()` — the strict checker's own
//! validator, run on the clause exactly as recorded, in exactly the recorded
//! order. So:
//!
//! * an accepted clause is one `check_proof_strict` re-derives from scratch,
//!   with no premise, no payload and no problem context. The producer states
//!   a rule; the checker re-runs it and is the only authority;
//! * a clause the battery declines keeps the byte-identical `trust` step it
//!   had, so the pass can only ever move a proof from "rejected" toward
//!   "checked" — never the reverse. In particular it cannot convert a
//!   RESCUABLE trust-kind rejection into a HARD `InvalidTheoryLemma` one,
//!   because a promoted kind's validator has already accepted the clause.
//!
//! Two guards keep that argument honest and are mutation-checked in
//! `intrinsic_leaf_promotion_tests.rs` (`GUARD_MUTATION_LEDGER` there):
//!
//! 1. **Premiseless and argument-free only.** A `trust` step WITH premises is
//!    a failed derivation, not a leaf; its clause is not claimed to be valid
//!    on its own, and relabelling it would drop the premises the consumer
//!    still references. Same for `args`.
//! 2. **No surviving arithmetic payload.** A `TheoryLemma` that still carries
//!    a `farkas`/`lia` annotation has POSITIONAL evidence; the battery's
//!    validators do not consume it while trace rebinding and the external
//!    printer do. Relabelling under a kind that ignores the payload would
//!    create split authority — the same rule
//!    `promote_generic_theory_lemma_kinds_after_rewrite` already states.
//!
//! The third condition, `!clause.is_empty()`, is honestly classified as SCOPE
//! rather than soundness: deleting it was MEASURED not to change any verdict,
//! because every battery entry already declines an empty clause
//! (`the_intrinsic_battery_declines_the_empty_clause`). It stays because the
//! empty clause is the refutation itself and reading it as a leaf is a
//! category error, not because anything unsound would follow.
//!
//! # Placement
//!
//! Dead last among the repair lanes, after every authored-root reconstruction
//! has had first refusal. A leaf re-derived from the problem's own assertions
//! is preferable to a bare tautology label (it carries provenance a reader can
//! follow), so this pass only ever sees what those lanes declined.

use ay_core::{AletheRule, Proof, ProofStep, TheoryLemmaKind};

use crate::theory_inference::intrinsic::recognize_intrinsic_tautology_kind;

use super::super::Executor;

impl Executor {
    /// Relabel every residual leaf whose clause an existing strict validator
    /// accepts as recorded. Returns the number of promotions (0 on the common
    /// path), which the tests assert on.
    pub(in crate::executor) fn promote_intrinsic_tautology_leaves(
        &self,
        proof: &mut Proof,
    ) -> usize {
        let terms = &self.ctx.terms;
        let mut promoted = 0usize;
        for step in &mut proof.steps {
            match step {
                // Guard 1: a premiseless, argument-free `trust` LEAF.
                ProofStep::Step {
                    rule: AletheRule::Trust,
                    clause,
                    premises,
                    args,
                } if premises.is_empty() && args.is_empty() && !clause.is_empty() => {
                    let Some((theory, kind)) = recognize_intrinsic_tautology_kind(terms, clause)
                    else {
                        continue;
                    };
                    *step = ProofStep::TheoryLemma {
                        theory: theory.to_owned(),
                        clause: std::mem::take(clause),
                        farkas: None,
                        kind,
                        lia: None,
                    };
                    promoted += 1;
                }
                // The trust-kind theory lemma the funnel normalized for want
                // of a certificate. Guard 2: only with no surviving payload.
                ProofStep::TheoryLemma {
                    kind,
                    clause,
                    farkas,
                    lia,
                    ..
                } if kind.is_trust() && farkas.is_none() && lia.is_none() && !clause.is_empty() => {
                    let Some((_, inferred)) = recognize_intrinsic_tautology_kind(terms, clause)
                    else {
                        continue;
                    };
                    debug_assert!(
                        !matches!(inferred, TheoryLemmaKind::Generic),
                        "BUG: the intrinsic battery returned the trust kind it is meant to replace"
                    );
                    *kind = inferred;
                    promoted += 1;
                }
                _ => {}
            }
        }
        promoted
    }
}

#[cfg(test)]
#[path = "intrinsic_leaf_promotion_tests.rs"]
mod tests;

#[cfg(test)]
#[path = "intrinsic_leaf_promotion_array_tests.rs"]
mod array_tests;
