// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `SemanticChargeClass::AndPosShallowMatch` — the module argument, the
//! op-counting mirror, the fixtures, and the REFUTATION that keeps the class
//! narrow.
//!
//! # What is being pinned, and why it does not overturn the `and_neg` refusal
//!
//! `metering_and_neg*.rs` refused a DAG-bounded charge for `and_neg` and its
//! refutation is still correct: `matches_negation_of_term` carries no memo
//! table, so a doubling DAG costs `2^k` matcher calls over `2k + 2` nodes and
//! any charge that ignores `unfolded_work` under-charges it without bound.
//! `and_pos` reaches THE SAME matcher, so the same refutation applies to the
//! rule as a whole — and this file re-checks it, on an `and_pos` step, in
//! [`a_doubling_and_pos_still_keeps_the_general_product`].
//!
//! What is decidable per STEP is whether the recursion's ENTRY CONDITIONS are
//! structurally absent. Both De Morgan arms of `matches_negation_of_term` open
//! by demanding the literal be headed by the DUAL connective, so an `and`-headed
//! source with no `or`-headed literal and no `or`-headed negand leaves
//! `validate_and_pos` with a two-literal scan and one slice comparison.
//! [`crate::checker::boolean_and_pos_shape::and_pos_matchers_are_shallow`] decides exactly that, in
//! `O(1)`, beside the validator whose control flow it describes.
//!
//! # The measurement that motivated it, and where the ask's framing was wrong
//!
//! On `benchmarks/smt/regression/soundness_qf_uf_incremental/
//! clearsy_0000_00307_falsesat13.smt2` and `..._0001_00310_falsesat44.smt2`
//! under `--no-proof -T:10 --probe-strict-check`, TWO two-literal steps —
//! `AndPos(29)` and `AndPos(37)`, each with
//! `payload(work = 40_922, unfolded_work = 5_502)` — precharged
//! **225_152_844** apiece of a 350_000_000 envelope
//! (`budget: work 239178107+225152848 of 350000000`).
//!
//! The binding limb is `work * unfolded_work`, **not** `unfolded_work^2`:
//! `5_502^2` is 30_272_004, an order of magnitude too small to explain the
//! charge. The DAG payload EXCEEDS the tree unfolding by 7.4x here, so this is
//! NOT the "deeply shared DAG" / sharing-squared pathology
//! `ClauseIdentityRoute` and `BoundedAssignmentEval` were built for. The
//! product is simply unrelated to what the validator does.
//! [`super::metering_and_pos_bounds::the_measured_clearsy_payload_is_the_one_this_class_fixes`]
//! pins both numbers.

use super::super::and_pos_charge::AND_POS_SHALLOW_WORK_FACTOR;
use super::metering_and_pos_mirror::mirror_and_pos;
use super::*;

/// `MAX_CHECK_WORK`, the envelope every claim below is measured against.
pub(super) const PRODUCTION_ENVELOPE: usize = 350_000_000;

/// The charge `and_pos` took before this class existed: the `General` recursive
/// tree product with no private per-rule scale (`AletheRule::AndPos` falls
/// through `private_validator_charge`'s `_ => (0, 0)` arm).
pub(super) fn general_charge(stats: PayloadStats) -> usize {
    let named = stats.work.saturating_mul(stats.unfolded_work);
    let paired = stats.unfolded_work.saturating_mul(stats.unfolded_work);
    named.max(paired)
}

/// The DAG-bounded model this class charges, computed here so a refutation can
/// name the number it WOULD have billed on a step it must not claim.
pub(super) fn shallow_model(stats: PayloadStats) -> usize {
    let modelled = stats
        .work
        .saturating_mul(AND_POS_SHALLOW_WORK_FACTOR)
        .saturating_add(AND_POS_SHALLOW_WORK_FACTOR);
    modelled.min(general_charge(stats))
}

pub(super) fn and_pos_step(clause: Vec<TermId>, position: u32, source: TermId) -> ProofStep {
    ProofStep::Step {
        rule: AletheRule::AndPos(position),
        clause,
        premises: Vec::new(),
        args: vec![source],
    }
}

/// Run ONE step through the real strict validator, so every claim below is
/// about a step the checker genuinely accepts or genuinely rejects.
pub(super) fn validate_one(terms: &TermStore, step: &ProofStep) -> Result<(), ProofCheckError> {
    let mut table: Vec<Option<Vec<TermId>>> = Vec::new();
    let mut unbounded = |_: usize, _: usize| true;
    validate_step_with_datatypes_and_progress(
        terms,
        &mut table,
        ProofId(0),
        step,
        true,
        None,
        None,
        None,
        None,
        None,
        None,
        None,
        &mut unbounded,
    )
}

/// Run the REAL per-step metering walk, so the tests are pinned against
/// production `PayloadStats` and not against numbers chosen to pass.
pub(super) fn measured_payload(step: &ProofStep, terms: &TermStore) -> PayloadStats {
    let mut memo = TermCostMemo::default();
    let mut unbounded = |_: usize, _: usize| true;
    meter_step_term_payload(step, terms, &[], &mut memo, &mut unbounded)
        .expect("an unbounded envelope always completes the payload walk")
}

pub(super) fn app(terms: &mut TermStore, name: &str, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

pub(super) fn charge(step: &ProofStep, terms: &TermStore, stats: PayloadStats) -> (usize, usize) {
    let class = select_semantic_charge_class(step, terms);
    semantic_validator_charge(step, stats, class)
        .expect("the modelled charge stays far below usize overflow")
}

// ---------------------------------------------------------------------------
// Fixtures
// ---------------------------------------------------------------------------

/// The EMITTED shape, which is what the corpus population actually looks like:
/// `proof_tracker::mod.rs` builds `(cl (not source) source_args[i])` with
/// `args = [source]`, so the gate literal is a bare `Not` of the source and the
/// conjunct literal is the indexed argument itself.
pub(super) fn emitted_and_pos(
    terms: &mut TermStore,
    source: TermId,
    position: u32,
) -> (ProofStep, TermId) {
    let TermData::App(_, args) = terms.get(source).clone() else {
        panic!("the source of an and_pos step must be an application");
    };
    let conjunct = args[position as usize];
    let gate = terms.mk_not_raw(source);
    (and_pos_step(vec![gate, conjunct], position, source), gate)
}

/// A conjunction whose reachable DAG grows by ONE node per level while its tree
/// unfolding DOUBLES: `T_0 = leaf`, `T_k = (and T_{k-1} T_{k-1})` with BOTH
/// arguments the same interned `TermId`, plus its De Morgan complement
/// `C_0 = (not leaf)`, `C_k = (or C_{k-1} C_{k-1})`.
pub(super) fn doubling_conjunction(
    terms: &mut TermStore,
    tag: &str,
    depth: usize,
) -> (TermId, TermId) {
    let leaf = terms.mk_var(format!("{tag}_leaf"), Sort::Bool);
    let mut conjunction = leaf;
    let mut complement = terms.mk_not(leaf);
    for _ in 0..depth {
        conjunction = app(terms, "and", vec![conjunction, conjunction]);
        complement = app(terms, "or", vec![complement, complement]);
    }
    (conjunction, complement)
}

/// The `clearsy` population's shape: `(and (= TRUE (bool b_0)) ..)` over an
/// uninterpreted sort, `n` conjuncts, every conjunct a distinct small term.
pub(super) fn clearsy_shaped_conjunction(terms: &mut TermStore, n: usize) -> TermId {
    let universe = Sort::Uninterpreted("U".to_string());
    let truth = terms.mk_var("TRUE", universe.clone());
    let conjuncts: Vec<TermId> = (0..n)
        .map(|index| {
            let arg = terms.mk_var(format!("boolarg_{index}"), Sort::Bool);
            let boxed = terms.mk_app(Symbol::named("bool"), vec![arg], universe.clone());
            terms.mk_app(Symbol::named("="), vec![truth, boxed], Sort::Bool)
        })
        .collect();
    app(terms, "and", conjuncts)
}

/// A conjunction over a `store` chain whose VALUE at each level reads the chain
/// below it, so the reachable DAG grows LINEARLY while the tree unfolding
/// DOUBLES per level — the `storeinv` shape the `ClauseIdentityRoute` class was
/// built for, here as an `and_pos` source.
pub(super) fn shared_store_chain_conjunction(
    terms: &mut TermStore,
    tag: &str,
    depth: usize,
    width: usize,
) -> TermId {
    let element = Sort::Uninterpreted("Elem".to_string());
    let array = Sort::Array(Box::new(ay_core::ArraySort {
        index_sort: Sort::Int,
        element_sort: element.clone(),
    }));
    let key = terms.mk_var(format!("{tag}_k"), Sort::Int);
    let mut chain = terms.mk_var(format!("{tag}_a"), array.clone());
    let mut conjuncts = Vec::new();
    for level in 0..depth {
        let index = terms.mk_var(format!("{tag}_i{level}"), Sort::Int);
        let value = terms.mk_app(Symbol::named("select"), vec![chain, key], element.clone());
        chain = terms.mk_app(
            Symbol::named("store"),
            vec![chain, index, value],
            array.clone(),
        );
        if conjuncts.len() < width {
            let read = terms.mk_app(Symbol::named("select"), vec![chain, key], element.clone());
            conjuncts.push(terms.mk_app(Symbol::named("="), vec![read, read], Sort::Bool));
        }
    }
    app(terms, "and", conjuncts)
}

// ---------------------------------------------------------------------------
// Routing
// ---------------------------------------------------------------------------

/// The emitted `and_pos` shape routes to the DAG-bounded class, and EVERY shape
/// that can reach the unmemoized De Morgan recursion is refused entry.
///
/// Each negative names the exact entry condition it restores.
#[test]
fn and_pos_routes_to_the_shallow_class_only_when_the_matchers_cannot_recurse() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("route_a", Sort::Bool);
    let b = terms.mk_var("route_b", Sort::Bool);
    let c = terms.mk_var("route_c", Sort::Bool);
    let source = app(&mut terms, "and", vec![a, b, c]);
    let (emitted, gate) = emitted_and_pos(&mut terms, source, 1);
    validate_one(&terms, &emitted).expect("the emitted shape is a valid and_pos step");
    assert_eq!(
        select_semantic_charge_class(&emitted, &terms),
        SemanticChargeClass::AndPosShallowMatch,
        "the shape every emitter produces must reach the DAG-bounded class"
    );

    // NEGATIVE 1 — an `or`-headed clause literal. `matches_negation_of_term`'s
    // `and` arm decodes it and enters `matches_negated_components`.
    let disjunction = app(&mut terms, "or", vec![a, b]);
    let or_literal = and_pos_step(vec![gate, disjunction], 1, source);
    assert_eq!(
        select_semantic_charge_class(&or_literal, &terms),
        SemanticChargeClass::General,
        "an or-headed literal opens the De Morgan arm and must keep General"
    );

    // NEGATIVE 2 — an `or`-headed NEGAND. `matches_positive_literal_of_term`
    // strips the `not` and hands the inner `or` to the same arm.
    let not_disjunction = terms.mk_not_raw(disjunction);
    let or_negand = and_pos_step(vec![not_disjunction, b], 1, source);
    assert_eq!(
        select_semantic_charge_class(&or_negand, &terms),
        SemanticChargeClass::General,
        "an or-headed negand reaches the same recursion one level down"
    );

    // NEGATIVE 3 — a source that is not an `and` application. `decode_ite` is
    // then no longer structurally `None`, and `decode_and_source` no longer
    // pins which argument list the slice comparison ranges over.
    let ite_source = terms.mk_ite(a, b, c);
    let ite_step = and_pos_step(vec![gate, b], 0, ite_source);
    assert_eq!(
        select_semantic_charge_class(&ite_step, &terms),
        SemanticChargeClass::General,
        "a non-and source must keep General"
    );

    // NEGATIVE 4 — no `args` at all, so `source_term` is `None` and
    // `decode_and_source` falls through to its clause scans.
    let sourceless = ProofStep::Step {
        rule: AletheRule::AndPos(1),
        clause: vec![gate, b],
        premises: Vec::new(),
        args: Vec::new(),
    };
    assert_eq!(
        select_semantic_charge_class(&sourceless, &terms),
        SemanticChargeClass::General,
        "a step with no source argument must keep General"
    );

    // NEGATIVE 5 — a clause that is not two literals. The bound is stated over
    // exactly two, so anything else keeps the conservative product.
    let three = and_pos_step(vec![gate, b, c], 1, source);
    assert_eq!(
        select_semantic_charge_class(&three, &terms),
        SemanticChargeClass::General
    );

    // NEGATIVE 6 — the SIBLING rule. `and_neg` reaches the same matcher with no
    // shape gate at all and its refusal stands; this class must not claim it.
    let and_neg = ProofStep::Step {
        rule: AletheRule::AndNeg,
        clause: vec![gate, b],
        premises: Vec::new(),
        args: vec![source],
    };
    assert_eq!(
        select_semantic_charge_class(&and_neg, &terms),
        SemanticChargeClass::General,
        "and_neg keeps General: metering_and_neg.rs is the evidence"
    );

    // The classes that must keep winning the ordering race above this one.
    let or_pos = ProofStep::Step {
        rule: AletheRule::OrPos(0),
        clause: vec![gate, b],
        premises: Vec::new(),
        args: vec![source],
    };
    assert_eq!(
        select_semantic_charge_class(&or_pos, &terms),
        SemanticChargeClass::UnorderedClauseMatch
    );
}

/// THE SECOND CALL SITE'S refutation, and the one the guard ledger needs.
///
/// `a_doubling_and_pos_still_keeps_the_general_product` refutes admitting an
/// `or`-headed LITERAL, which is what the gate scan's `matches_negation_of_term`
/// opens on. It says nothing about the conjunct scan, where
/// `matches_positive_literal_of_term` strips a `not` FIRST and hands the inner
/// term to the same De Morgan arm one level down — so a clause with no
/// `or`-headed literal at all can still reach the unmemoized recursion.
///
/// This fixture is that clause, and it is refused by the negand guard ALONE:
/// source `(and T_k Y)`, gate `(not (and T_k Y))`, conjunct literal
/// `(not C_k)`. No literal is `or`-headed (both are `Not`), so deleting the
/// LITERAL guard leaves it declined; deleting the NEGAND guard admits it.
///
/// Checked here, as a complete refutation:
///  * the step is genuinely VALID — `C_k` is the De Morgan complement of `T_k`,
///    so `(not C_k)` is the indexed conjunct and the validator walks all of it;
///  * the mirror's primitive count is at least `2^k`;
///  * the step is NOT admitted; and
///  * had it been admitted the model would UNDER-charge it, by a factor the
///    failure message names.
#[test]
fn a_doubling_negand_reaches_the_second_call_site_and_is_still_refused() {
    const DEPTH: usize = 18;
    let mut terms = TermStore::new();
    let (conjunction, complement) = doubling_conjunction(&mut terms, "negand", DEPTH);
    let spare = terms.mk_var("negand_spare", Sort::Bool);
    let source = app(&mut terms, "and", vec![conjunction, spare]);
    let gate = terms.mk_not_raw(source);
    let negand_literal = terms.mk_not_raw(complement);

    let clause = vec![gate, negand_literal];
    let step = and_pos_step(clause.clone(), 0, source);
    validate_one(&terms, &step).expect(
        "(not C_k) IS the indexed conjunct T_k under De Morgan: the step is \
         valid and the conjunct scan must walk all of it",
    );

    // The LITERAL guard is silent here — neither literal is `or`-headed — so
    // this fixture isolates the NEGAND guard.
    for &lit in &clause {
        assert!(
            !matches!(
                terms.get(lit),
                TermData::App(Symbol::Named(name), _) if name == "or"
            ),
            "no clause literal may be or-headed, or this refutes the wrong guard"
        );
    }

    let (ok, ops) = mirror_and_pos(&terms, &clause, 0, Some(source));
    assert!(ok, "the mirror must agree the step is valid");
    assert!(
        ops >= (1_usize << DEPTH),
        "the conjunct scan must really make ~2^depth recursive calls: ops={ops}"
    );

    assert!(
        !crate::checker::boolean_and_pos_shape::and_pos_matchers_are_shallow(
            &terms,
            &clause,
            Some(source)
        ),
        "an or-headed NEGAND must be refused entry to the shallow class"
    );
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::General
    );

    let stats = measured_payload(&step, &terms);
    let would_have_billed = shallow_model(stats);
    assert!(
        would_have_billed < ops,
        "the negand guard is load-bearing: admitting this step would bill \
         {would_have_billed} for {ops} primitives"
    );
    assert!(
        general_charge(stats) > ops,
        "the `General` product it keeps must still bound the real work"
    );
}

/// THE REFUTATION this class must survive: the `and_neg` pass's doubling DAG,
/// re-aimed at `and_pos`.
///
/// `T_k = (and T_{k-1} T_{k-1})` and `C_k = (or C_{k-1} C_{k-1})`, both built
/// from ONE interned child. The step `(cl C_k T_{k-1})` with `:args (T_k)` and
/// position 0 is a genuinely VALID `and_pos`: `C_k` IS the De Morgan complement
/// of `T_k`, and the validator has to walk all `2^k` leaf pairs to see it.
///
/// Checked here:
///  * the step is genuinely valid, so the validator really does all of it;
///  * the measured DAG payload stays tiny while the unfolded payload explodes;
///  * the mirror's primitive count is at least `2^k`;
///  * **the step is NOT admitted to this class** — the `or`-headed gate literal
///    is exactly what `and_pos_matchers_are_shallow` refuses; and
///  * **had it been admitted, the model would UNDER-charge it** — the number is
///    named in the failure message, so the guard's necessity is a measurement
///    and not an assertion.
#[test]
fn a_doubling_and_pos_still_keeps_the_general_product() {
    const DEPTH: usize = 20;
    let mut terms = TermStore::new();
    let (conjunction, complement) = doubling_conjunction(&mut terms, "dbl", DEPTH);
    let TermData::App(_, children) = terms.get(conjunction) else {
        panic!("the doubling fixture must build an `and` application");
    };
    assert_eq!(children[0], children[1], "both arguments must be SHARED");
    let inner_conjunct = children[0];

    let clause = vec![complement, inner_conjunct];
    let step = and_pos_step(clause.clone(), 0, conjunction);
    validate_one(&terms, &step).expect(
        "(or C C) IS the De Morgan negation of (and T T) at every level: the \
         step is valid and the validator must walk all of it",
    );

    let stats = measured_payload(&step, &terms);
    assert!(
        stats.work < 4_096,
        "the reachable DAG must stay tiny: work={}",
        stats.work
    );
    assert!(
        stats.unfolded_work > (1_usize << DEPTH),
        "the tree unfolding must explode: unfolded={}",
        stats.unfolded_work
    );

    let (ok, ops) = mirror_and_pos(&terms, &clause, 0, Some(conjunction));
    assert!(ok, "the mirror must agree the step is valid");
    assert!(
        ops >= (1_usize << DEPTH),
        "the matcher must really make ~2^depth recursive calls: ops={ops}"
    );

    assert!(
        !crate::checker::boolean_and_pos_shape::and_pos_matchers_are_shallow(
            &terms,
            &clause,
            Some(conjunction)
        ),
        "an or-headed gate literal must be refused entry to the shallow class"
    );
    assert_eq!(
        select_semantic_charge_class(&step, &terms),
        SemanticChargeClass::General,
        "and so the step must keep the tree-unfolded product"
    );

    let would_have_billed = shallow_model(stats);
    assert!(
        would_have_billed < ops,
        "the guard is load-bearing: admitting this step would bill \
         {would_have_billed} for {ops} primitives"
    );
    let general = general_charge(stats);
    assert!(
        general > ops,
        "the `General` product it keeps must still bound the real work: \
         {general} vs {ops}"
    );
    assert_eq!(
        charge(&step, &terms, stats).0,
        general,
        "and the levied charge must BE that product"
    );
}
