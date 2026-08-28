// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! [`SemanticChargeClass::AndPosShallowMatch`] — its admission test, its work
//! factor and its charge.
//!
//! `AletheRule::AndPos(i)` on a step whose two negation matchers are
//! STRUCTURALLY UNABLE to recurse — the decision is
//! [`crate::checker::boolean_and_pos_shape::and_pos_matchers_are_shallow`],
//! which lives beside the validator and states the control-flow claim there.
//!
//! `and_pos` is NOT `and_neg`. `crates/ay-proof/src/quality_tests/
//! metering_and_neg*.rs` refused a DAG-bounded charge for `and_neg` on the
//! strength of a doubling DAG that costs `2^k` matcher calls over a DAG of
//! `2k + 2` nodes, and that refutation is still correct — for the WHOLE
//! rule. This class does not overturn it. It carves out the steps on which
//! the recursion is unreachable: `matches_negation_of_term`'s two De Morgan
//! arms each demand the literal be headed by the DUAL connective, so an
//! `and`-headed source with no `or`-headed literal (and no `or`-headed
//! negand) leaves the validator with a clause scan and one slice
//! comparison. Every step that does NOT prove that keeps `General`,
//! including the doubling DAG, which is `or`-headed at the gate and is
//! pinned still-`General` in `metering_and_pos.rs`.
//!
//! MEASURED, and this is why the class exists. On
//! `benchmarks/smt/regression/soundness_qf_uf_incremental/
//! clearsy_0000_00307_falsesat13.smt2` and `..._0001_00310_falsesat44.smt2`
//! (`--no-proof -T:10 --probe-strict-check`), TWO two-literal steps —
//! `AndPos(29)` and `AndPos(37)`, each with
//! `payload(work = 40_922, unfolded_work = 5_502)` — precharge
//! **225_152_844** apiece of a 350_000_000 envelope:
//!
//! ```text
//! semantic precharge class=General on rule AndPos(29): work=225152844 …
//!   from payload(work=40922, unfolded_work=5502, bytes=579130)
//! semantic precharge class=General on rule AndPos(37): work=225152844 …
//! strict-check envelope refused: budget: work 239178107+225152848 of 350000000
//! ```
//!
//! So 450_305_688 of the ~464 M the refusal had reached is those two steps
//! alone, and everything else in the proof is ~14 M. (The payload and the
//! per-step charge reproduce EXACTLY run to run; the running total the refusal
//! prints does not, because which proofs the incremental lanes have built by
//! then is timing-dependent.) The validator's real cost on each of those steps
//! is one pass over the source's ~60-element argument list.
//!
//! Note WHICH limb binds: `work * unfolded_work`, not `unfolded_work^2`
//! (`5_502^2` is only 30 M). The DAG payload EXCEEDS the tree unfolding
//! here — 7.4x — so this is not the sharing-squared story the
//! `ClauseIdentityRoute` and `BoundedAssignmentEval` classes were built for.
//! The product is simply unrelated to what the validator does, exactly as
//! [`SemanticChargeClass::TrustKindProgressMetered`] records for its own
//! population.
//! See [`AND_POS_SHALLOW_WORK_FACTOR`].

use super::semantic_charge::replaced_general_product;
use super::*;

/// Work factor for [`SemanticChargeClass::AndPosShallowMatch`], applied to the
/// step's DAG payload `work` (NOT the tree-unfolded payload).
///
/// COUNTED, not estimated. One "primitive" is one `TermStore::get`, one name
/// comparison, one `TermId` comparison, one length comparison, or one
/// `matched`-bitmap probe — the granularity
/// `quality_tests/metering_and_pos_mirror.rs` counts in, so the table below and
/// that file's `tight >= ops` assertions measure the same unit.
///
/// Write `n = args.len()` for the source conjunction's arity. On a step
/// [`crate::checker::boolean_and_pos_shape::and_pos_matchers_are_shallow`]
/// admits, `validate_and_pos` performs, primitive by primitive:
///
/// | site | primitives |
/// |---|---|
/// | `clause.len()` guard | 1 |
/// | `decode_and_source` — one `terms.get` + one name compare, first branch | 2 |
/// | `index >= args.len()` guard | 1 |
/// | gate scan, per literal: `matches_negation_of_term` = `strip_not` (1) + `TermId` compare (1) + `decode_ite` (2) + `terms.get(source)` + name compare (2) + `decode_app(lit, "or")` (2) | 8 |
/// | gate scan, per literal: `strip_not` (1) + `decode_app(inner, "and")` (2) + the `inner_args == args` slice compare (`1 + n`) | `4 + n` |
/// | conjunct scan, per literal: `matches_positive_literal_of_term` = `lit == term` (1) + `terms.get` + name compare (2) + `strip_not` (1) + one bounded `matches_negation_of_term` (8) | 12 |
/// | the final `has_gate && has_conjunct` | 1 |
///
/// Both scans run over at most 2 literals, so the total is at most
/// `2*(8 + 4 + n) + 2*12 + 5 = 53 + 2n`.
///
/// `payload.work >= n + 3` on every such step: the payload walk's
/// `push_term_slice` debits one unit per clause literal and one per `args`
/// entry (2 + 1 = 3) before the DAG walk starts, and `append_term_children`
/// then debits `args.len()` when it expands the source's `and` node — which it
/// must, because the source is a root of that walk. (The walk debits strictly
/// more than that — the stack pushes, the membership probes and the tree
/// unfolding all land on the same counter — so `n + 3` is a floor, not an
/// estimate; `the_payload_walk_floor_the_derivation_rests_on_holds` measures
/// it.) So the charge is at least `32*(n + 3) + 32 = 32n + 128`, which exceeds
/// the worst-case `53 + 2n` by at least 75 primitives at every arity.
///
/// The charge stays LINEAR in the step's real DAG payload, so a genuinely huge
/// `and_pos` still grows its charge and is still refused: the class runs out of
/// a 350 M envelope at `work > 10_937_500`.
pub(super) const AND_POS_SHALLOW_WORK_FACTOR: usize = 32;

/// Recognize an `and_pos` step whose two negation matchers cannot recurse.
///
/// Unlike every other route predicate here this one reads TERMS, because the
/// question is not "which rule is this" — `and_pos` in general reaches the same
/// unmemoized De Morgan recursion `and_neg` does, and
/// `quality_tests/metering_and_neg*.rs` correctly refused a DAG bound for the
/// rule as a whole. What is decidable per STEP, in `O(1)`, is whether the
/// recursion's entry conditions are structurally absent, and that decision is
/// [`crate::checker::boolean_and_pos_shape::and_pos_matchers_are_shallow`] — deliberately sited next to
/// `validate_and_pos` so the claim cannot drift from the control flow it
/// describes.
///
/// Grants no proof authority; a step it declines keeps the conservative
/// `General` product.
pub(super) fn is_and_pos_shallow_match(step: &ProofStep, terms: &TermStore) -> bool {
    let ProofStep::Step {
        rule: AletheRule::AndPos(position),
        clause,
        args,
        ..
    } = step
    else {
        return false;
    };
    // `args.first()` is exactly what `validate_step` hands the validator as its
    // `source_term`; reading anything else here would decide a different step.
    //
    // TWO admission arms, each with its own no-recursion argument:
    //  * `and_pos_matchers_are_shallow` — no `or`-headed literal or negand, so
    //    neither De Morgan arm can open on ANY probe;
    //  * `and_pos_is_emitted_identity_shape` — the clause is EXACTLY
    //    `(cl (not source) args[index])` by `TermId` identity in that order, so
    //    both ordered scans terminate on their FIRST probe and no matcher can
    //    recurse whatever the conjunct's headedness is. This is the arm that
    //    admits the QF_IDL `EqDiffVar`-spliced population, whose conjuncts are
    //    `or`-headed and which the first arm therefore declines — measured at
    //    39.7M-511.5M `General` work units per step for an O(1) validation.
    crate::checker::boolean_and_pos_shape::and_pos_matchers_are_shallow(
        terms,
        clause,
        args.first().copied(),
    ) || crate::checker::boolean_and_pos_shape::and_pos_is_emitted_identity_shape(
        terms,
        clause,
        *position,
        args.first().copied(),
    )
}

/// Exact worst case of [`crate::checker::boolean::validate_and_pos`] on a step
/// [`crate::checker::boolean_and_pos_shape::and_pos_matchers_are_shallow`] or
/// [`crate::checker::boolean_and_pos_shape::and_pos_is_emitted_identity_shape`]
/// admits.
///
/// On a step the FIRST arm admits both negation matchers return in `O(1)` —
/// the derivation is on that predicate — and the whole validator costs at most
/// `53 + 2n` primitives for a source arity `n`, which
/// [`AND_POS_SHALLOW_WORK_FACTOR`] copies of `payload.work` dominate because
/// `payload.work >= n + 3`. See that constant for the primitive-by-primitive
/// count. On a step the SECOND arm admits, both ordered scans terminate on
/// their FIRST probe (the identity derivation is on that predicate), so the
/// validator costs a CONSTANT ~25 primitives — below even this model's
/// `+ AND_POS_SHALLOW_WORK_FACTOR` tail on its own, and far below `53 + 2n`.
/// The same charge therefore covers both arms without change.
///
/// The `+ AND_POS_SHALLOW_WORK_FACTOR` tail is not decoration: a payload with
/// `work = 0` must still be charged for the constant-time guards, and the meter
/// may never bill zero for work that happens.
///
/// Capped by [`replaced_general_product`] so this is a TIGHTENING at every
/// payload: the cap can only ever select the value the shipped `General` model
/// already charges, so no proof that fits a caller's envelope today can stop
/// fitting it. Bytes are left at the `General`/private model
/// (`payload.bytes`) — `validate_and_pos` allocates NOTHING on this route (it
/// borrows the source's argument slice and never builds the `matched` bitmap
/// `matches_negated_components` would), so the byte limb is already generous and
/// leaving it alone makes this a pure work-side correction that cannot newly
/// refuse on bytes.
pub(super) fn and_pos_shallow_match_charge(
    payload: PayloadStats,
) -> Result<(usize, usize), ProofCheckError> {
    let modelled = checked_mul_usize(payload.work, AND_POS_SHALLOW_WORK_FACTOR)?;
    let modelled = checked_add_usize(modelled, AND_POS_SHALLOW_WORK_FACTOR)?;
    Ok((
        modelled.min(replaced_general_product(payload, 1)),
        payload.bytes,
    ))
}
