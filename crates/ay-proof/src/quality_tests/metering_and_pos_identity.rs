// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `and_pos_is_emitted_identity_shape` — the SECOND admission arm of
//! `SemanticChargeClass::AndPosShallowMatch`, its fixtures, its refutations
//! and its guard-mutation ledger.
//!
//! # Why the first arm was not enough, measured
//!
//! `and_pos_matchers_are_shallow` declines any step with an `or`-headed
//! clause literal, because the gate scan's `matches_negation_of_term` can
//! open its De Morgan arm on one. But the EMITTED `and_pos` shape —
//! `(cl (not source) source_args[i])`, gate first, indexed conjunct second,
//! both by `TermId` identity — is O(1) for the validator REGARDLESS of the
//! conjunct's headedness: both ordered scans terminate on their FIRST probe
//! (the derivation is on the predicate in `boolean_and_pos_shape.rs`).
//!
//! On QF_IDL's folded assertion bodies the indexed conjunct is routinely an
//! `or` of guards, so the emitted step fell into `General` and was billed the
//! tree product. Measured with per-class charge attribution
//! (`ay solve --no-proof -T:10 --probe-strict-check`, EqDiffVar lane
//! unbounded):
//!
//!  * `sal/bakery/inf-bakery-mutex-8`: SEVEN such steps (`AndPos(24..30)`)
//!    billed 39,695,940 EACH — 277.9M of a 385M refused total whose real
//!    validator-dynamic work was 35,650 units;
//!  * `mathsat/fischer/FISCHER5-3-ninc`: ONE step (`AndPos(46)`) billed
//!    511,491,267 — 1.46x the whole 350M envelope in a single precharge
//!    (`payload(work=32_469, unfolded_work=10_077)` shape on the sibling
//!    `FISCHER4-3-ninc` file: `32_469 * 10_077 = 327,190,113`);
//!  * the strict check's real wall on these proofs is 3-78 ms.
//!
//! The refusal turned a trust-family rejection into `ResourceLimit`, which
//! starves `discharge_trust_steps_for_certification` and falls through to a
//! whole-problem re-solve — the entire reason the EqDiffVar retention-off
//! lane carried a 4,096-step call-site bound.
//!
//! # What this arm must NOT admit
//!
//! The doubling refutations in `metering_and_pos.rs` stand untouched: their
//! clauses are not the emitted identity shape, and the two identity halves
//! are each load-bearing AGAINST them (see the ledger). The new refutations
//! here pin the ORDER and the INDEX, the two conditions the existing
//! fixtures do not isolate.

use super::metering_and_pos::{
    and_pos_step, app, charge, doubling_conjunction, emitted_and_pos, general_charge,
    measured_payload, shallow_model, validate_one,
};
use super::metering_and_pos_mirror::mirror_and_pos;
use super::*;

/// The population fixture: the EMITTED shape whose indexed conjunct is an
/// `or` of guards — exactly what the EqDiffVar lane splices on QF_IDL.
///
/// Asserts the full contract:
///  * the step is genuinely VALID, so the validator really runs all of it;
///  * the FIRST arm declines it (this is the second arm's population, not a
///    re-test of the first);
///  * the class is `AndPosShallowMatch`;
///  * the mirror's primitive count is CONSTANT-small; and
///  * the levied charge dominates the mirror's count — the no-under-bill
///    bound, asserted against the real validator mirror rather than claimed.
#[test]
fn an_emitted_and_pos_with_an_or_headed_conjunct_is_dag_bounded() {
    let mut terms = TermStore::new();
    // Wide enough that the General product genuinely exceeds the linear
    // model, mirroring the QF_IDL population: many conjuncts, the indexed one
    // an `or` of guards.
    let conjuncts: Vec<TermId> = (0..48)
        .map(|index| {
            let guards: Vec<TermId> = (0..4)
                .map(|guard| terms.mk_var(format!("idnt_g{index}_{guard}"), Sort::Bool))
                .collect();
            app(&mut terms, "or", guards)
        })
        .collect();
    let source = app(&mut terms, "and", conjuncts);
    let (step, _gate) = emitted_and_pos(&mut terms, source, 1);
    let ProofStep::Step { clause, .. } = &step else {
        unreachable!("and_pos_step builds a Step");
    };
    let clause = clause.clone();

    validate_one(&terms, &step)
        .expect("the emitted shape with an or-headed conjunct is a valid and_pos step");

    assert!(
        !crate::checker::boolean_and_pos_shape::and_pos_matchers_are_shallow(
            &terms,
            &clause,
            Some(source)
        ),
        "the or-headed conjunct must decline the FIRST arm, or this test \
         is not exercising the identity arm at all"
    );
    assert!(
        crate::checker::boolean_and_pos_shape::and_pos_is_emitted_identity_shape(
            &terms,
            &clause,
            1,
            Some(source)
        ),
        "the emitted identity shape must be admitted by the second arm"
    );
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::AndPosShallowMatch,
        "the emitted shape must reach the DAG-bounded class whatever its \
         conjunct's headedness"
    );

    let (ok, ops) = mirror_and_pos(&terms, &clause, 1, Some(source));
    assert!(ok, "the mirror must agree the step is valid");
    assert!(
        ops <= 64,
        "both ordered scans must terminate on their first probe: ops={ops}"
    );

    let stats = measured_payload(&step, &terms);
    let (work, bytes) = charge(&step, &terms, stats);
    assert!(
        work >= ops,
        "the levied charge must dominate the mirror's primitive count: \
         charge={work} ops={ops}"
    );
    assert_eq!(
        work,
        shallow_model(stats),
        "and it must BE the shallow model, not the General product"
    );
    assert!(
        work < general_charge(stats),
        "the fix must actually bind: General={} shallow={work}",
        general_charge(stats)
    );
    assert_eq!(bytes, stats.bytes, "pure work-side correction: bytes stay");
}

/// ORDER refutation. The identity arm admits `(cl (not source) conjunct)` and
/// must decline the REVERSED clause `(cl conjunct (not source))` — because
/// with the conjunct evaluated FIRST, `has_gate`'s
/// `matches_negation_of_term(conjunct, source)` opens the De Morgan arm
/// whenever the conjunct is `or`-headed with the source's arity, and that
/// recursion is real: this fixture makes it cost >= 2^(k-1) primitives.
///
/// Construction: `T_j`/`C_j` are the doubling pair (`T_j` an `and` of two
/// shared copies, `C_j` its `or`-shaped De Morgan complement). The source is
/// `(and C_k T_k)` — arity 2, MATCHING `C_k`'s own arity — and the clause is
/// `[C_k, (not source)]` at position 0, so `C_k` IS the indexed conjunct by
/// identity and the step is VALID; only the order distinguishes it from the
/// emitted shape. `has_gate` must first try `C_k` against the source: the
/// bipartite scan matches `C_{k-1}` against `T_k` (a full doubling descent
/// that SUCCEEDS at the shared leaves), then fails to cover the second
/// `C_{k-1}`, all before the real gate literal is reached.
///
/// A mutant that treats the two identity conditions as an unordered SET
/// admits this clause and under-bills it by the factor the failure message
/// names; the assertion below is what turns that mutant RED.
#[test]
fn a_reversed_emitted_clause_with_a_matching_arity_disjunct_is_still_refused() {
    const DEPTH: usize = 18;
    let mut terms = TermStore::new();
    let (conjunction, complement) = doubling_conjunction(&mut terms, "rev", DEPTH);
    let source = app(&mut terms, "and", vec![complement, conjunction]);
    let gate = terms.mk_not_raw(source);
    let clause = vec![complement, gate];
    let step = and_pos_step(clause.clone(), 0, source);

    validate_one(&terms, &step).expect(
        "C_k IS args[0] by identity and (not source) is the gate: the step is \
         valid; only the ORDER differs from the emitted shape",
    );

    let (ok, ops) = mirror_and_pos(&terms, &clause, 0, Some(source));
    assert!(ok, "the mirror must agree the step is valid");
    assert!(
        ops >= (1_usize << (DEPTH - 1)),
        "the reversed order must really reach the De Morgan recursion: ops={ops}"
    );

    assert!(
        !crate::checker::boolean_and_pos_shape::and_pos_is_emitted_identity_shape(
            &terms,
            &clause,
            0,
            Some(source)
        ),
        "the identity arm is ORDER-pinned; a reversed clause must be refused"
    );
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::General,
        "and the step must keep the tree-unfolded product"
    );

    let stats = measured_payload(&step, &terms);
    let would_have_billed = shallow_model(stats);
    assert!(
        would_have_billed < ops,
        "the order pin is load-bearing: admitting this clause would bill \
         {would_have_billed} for {ops} primitives"
    );
    assert!(
        general_charge(stats) > ops,
        "the General product it keeps must still bound the real work"
    );
}

/// INDEX refutation. The identity arm compares `clause[1]` against
/// `args[position]`, not against `args.first()` or "any argument": with the
/// clause literal identical to args[0] but the POSITION naming args[1], the
/// conjunct scan must match `clause[1] = (not C_k)` against
/// `args[1] = T_k` through the negand recursion — a full doubling descent.
///
/// A mutant that reads `args.first()` (or ignores the index) admits this step
/// and under-bills it by the factor the failure message names.
#[test]
fn an_index_mismatched_identity_clause_is_still_refused() {
    const DEPTH: usize = 18;
    let mut terms = TermStore::new();
    let (conjunction, complement) = doubling_conjunction(&mut terms, "idx", DEPTH);
    let negand_literal = terms.mk_not_raw(complement);
    // args[0] is the literal itself; args[1] is the doubling conjunction the
    // validator must actually walk when position = 1.
    let source = app(&mut terms, "and", vec![negand_literal, conjunction]);
    let gate = terms.mk_not_raw(source);
    let clause = vec![gate, negand_literal];
    let step = and_pos_step(clause.clone(), 1, source);

    validate_one(&terms, &step).expect(
        "(not C_k) IS T_k's De Morgan negation, so the conjunct scan accepts \
         it for position 1 after the full descent: the step is valid",
    );

    let (ok, ops) = mirror_and_pos(&terms, &clause, 1, Some(source));
    assert!(ok, "the mirror must agree the step is valid");
    assert!(
        ops >= (1_usize << (DEPTH - 1)),
        "position 1 must really reach the negand recursion: ops={ops}"
    );

    assert!(
        crate::checker::boolean_and_pos_shape::and_pos_is_emitted_identity_shape(
            &terms,
            &clause,
            0,
            Some(source)
        ),
        "sanity: at position 0 this clause IS the emitted identity shape \
         (which is what makes the index the only thing this fixture varies)"
    );
    assert!(
        !crate::checker::boolean_and_pos_shape::and_pos_is_emitted_identity_shape(
            &terms,
            &clause,
            1,
            Some(source)
        ),
        "the identity arm must compare against args[position], not args[0]"
    );
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::General,
        "and the position-1 step must keep the tree-unfolded product"
    );

    let stats = measured_payload(&step, &terms);
    let would_have_billed = shallow_model(stats);
    assert!(
        would_have_billed < ops,
        "the index pin is load-bearing: admitting this step would bill \
         {would_have_billed} for {ops} primitives"
    );
}

/// The guard-mutation ledger for the identity arm. Each row is a mutation
/// applied, `cargo test -p ay-proof --lib` run UNFILTERED, the failures
/// OBSERVED, then restored. Every per-row test list is the harness's own
/// output, not a prediction.
pub(super) const AND_POS_IDENTITY_LEDGER: &[(&str, &str)] = &[
    (
        "and_pos_is_emitted_identity_shape: made unconditionally true past \
         the structural guards (two literals, and-headed source, index in \
         range)",
        "RED x6 — both doubling refutations in metering_and_pos.rs, the \
         routing test, the wire-text test, and BOTH new refutations here. \
         SOUNDNESS-RELEVANT: the doubling steps are billed a few thousand \
         work units for >= 2^18 real matcher primitives.",
    ),
    (
        "and_pos_is_emitted_identity_shape: gate half \
         `strip_not(clause[0]) == Some(source)` DELETED",
        "RED x2 — a_doubling_and_pos_still_keeps_the_general_product (its \
         clause `[C_k, T_{k-1}]` has the conjunct half by identity, so the \
         2^k doubling step is admitted) and the routing test.",
    ),
    (
        "and_pos_is_emitted_identity_shape: conjunct half \
         `clause[1] == target` DELETED",
        "RED x3 — a_doubling_negand_reaches_the_second_call_site_and_is_still_\
         refused (its clause `[(not source), (not C_k)]` has the gate half by \
         identity, so the 2^k negand step is admitted), \
         an_index_mismatched_identity_clause_is_still_refused, and the \
         routing test.",
    ),
    (
        "and_pos_is_emitted_identity_shape: identity halves made UNORDERED \
         (either literal may be the gate)",
        "RED x2 — a_reversed_emitted_clause_with_a_matching_arity_disjunct_is_\
         still_refused (reversal makes has_gate evaluate the or-headed \
         conjunct first, and the bipartite scan costs >= 2^(k-1); the \
         under-bill assertion names the factor) and the wire-text test's \
         reversed declined fixture.",
    ),
    (
        "and_pos_is_emitted_identity_shape: `args.get(position)` replaced by \
         `args.first()`",
        "RED x2 — an_index_mismatched_identity_clause_is_still_refused (the \
         position-1 step matches its negand by a full doubling descent while \
         the args[0] identity still holds) and \
         an_emitted_and_pos_with_an_or_headed_conjunct_is_dag_bounded (its \
         position-1 emitted step stops being admitted).",
    ),
    (
        "and_pos_is_emitted_identity_shape: `clause.len() != 2` guard \
         weakened to `< 2`",
        "RED — and_pos_routes_to_the_shallow_class_only_when_the_matchers_\
         cannot_recurse (NEGATIVE 5): the three-literal clause has both \
         identity halves in the first two positions and is admitted.",
    ),
    (
        "is_and_pos_shallow_match: the identity arm consulted for \
         `AletheRule::AndNeg` too (position 0)",
        "RED — and_pos_routes_to_the_shallow_class_only_when_the_matchers_\
         cannot_recurse (NEGATIVE 6): and_neg keeps General; \
         metering_and_neg.rs is the evidence.",
    ),
];

#[test]
fn and_pos_identity_ledger_is_present() {
    assert!(AND_POS_IDENTITY_LEDGER.len() >= 7);
}
