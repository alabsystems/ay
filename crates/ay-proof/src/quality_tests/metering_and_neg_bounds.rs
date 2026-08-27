// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The BOUND half of the `and_neg` charge evidence: the upper-bound sweep, the
//! mirror's agreement with the real validator, the measured `clearsy`
//! population, the oversize refusal, and the charge ledger.
//!
//! Split from `metering_and_neg.rs` so each file stays inside the repository's
//! 500-line ceiling. That file owns the module-level argument, the independent
//! mirror, the fixtures, and the two tests that REFUTE a reachable-DAG bound.

use super::metering_and_neg::{
    and_neg_step, app, clearsy_shaped_conjunction, doubling_conjunction, general_charge,
    measured_payload, mirror_and_neg, validate_one, PRODUCTION_ENVELOPE,
};
use super::*;

/// The UPPER-BOUND direction, over a sweep of shapes: the `General` product is
/// at least the number of recursive matcher calls the step costs.
///
/// This is the reason `and_neg` is left where it is rather than given a new
/// model — the shipped charge already has the right shape.
#[test]
fn the_general_product_bounds_the_measured_matcher_work() {
    let mut checked = 0_usize;
    for depth in 1..=10_usize {
        let mut terms = TermStore::new();
        let (conjunction, complement) = doubling_conjunction(&mut terms, "sweep", depth);
        let TermData::App(_, complement_children) = terms.get(complement) else {
            panic!("the complement must be an `or` application");
        };
        let inner = complement_children[0];
        let clause = vec![conjunction, inner, inner];
        let step = and_neg_step(clause.clone(), conjunction);
        let stats = measured_payload(&step, &terms);
        let (ok, calls) = mirror_and_neg(&terms, &clause, conjunction);
        assert!(ok, "depth={depth}");
        assert!(
            general_charge(stats) >= calls,
            "depth={depth}: general={} calls={calls}",
            general_charge(stats)
        );
        checked += 1;
    }
    for width in [2_usize, 3, 8, 64, 512] {
        let mut terms = TermStore::new();
        let (conjunction, conjuncts) = clearsy_shaped_conjunction(&mut terms, width);
        let mut clause = vec![conjunction];
        for &conjunct in &conjuncts {
            let negated = terms.mk_not(conjunct);
            clause.push(negated);
        }
        let step = and_neg_step(clause.clone(), conjunction);
        validate_one(&terms, &step).expect("a plain negation of every conjunct is valid");
        let stats = measured_payload(&step, &terms);
        let (ok, calls) = mirror_and_neg(&terms, &clause, conjunction);
        assert!(ok, "width={width}");
        assert!(
            general_charge(stats) >= calls,
            "width={width}: general={} calls={calls}",
            general_charge(stats)
        );
        checked += 1;
    }
    assert!(checked >= 15);
}

/// The mirror is only evidence if it answers the same question the checker
/// does. Every case here is put to BOTH, and the two verdicts must agree —
/// including the rejecting ones, so the mirror cannot be a function that says
/// "valid" to everything.
#[test]
fn the_mirror_agrees_with_the_real_validator() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("mir_a", Sort::Bool);
    let b = terms.mk_var("mir_b", Sort::Bool);
    let c = terms.mk_var("mir_c", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let not_c = terms.mk_not(c);
    let disjunction = app(&mut terms, "or", vec![a, b]);
    let dual = app(&mut terms, "and", vec![not_a, not_b]);
    let half_dual = app(&mut terms, "and", vec![not_a, b]);
    let source = app(&mut terms, "and", vec![disjunction, c]);
    let plain = app(&mut terms, "and", vec![a, b]);
    let not_plain_a = app(&mut terms, "or", vec![not_a, not_b]);

    let cases: Vec<(&str, TermId, Vec<TermId>)> = vec![
        ("de morgan dual", source, vec![source, dual, not_c]),
        ("wrong polarity", source, vec![source, half_dual, not_c]),
        ("missing gate", source, vec![dual, not_c, not_c]),
        ("duplicated negation", plain, vec![plain, not_a, not_a]),
        ("plain negations", plain, vec![plain, not_a, not_b]),
        ("reordered", plain, vec![not_b, plain, not_a]),
        ("wrong arity", plain, vec![plain, not_a]),
        (
            "nested dual as gate",
            plain,
            vec![not_plain_a, not_a, not_b],
        ),
    ];
    let mut accepted = 0_usize;
    let mut rejected = 0_usize;
    for (label, source, clause) in cases {
        let step = and_neg_step(clause.clone(), source);
        let real = validate_one(&terms, &step).is_ok();
        let (mirrored, _) = mirror_and_neg(&terms, &clause, source);
        assert_eq!(real, mirrored, "{label}: checker={real} mirror={mirrored}");
        if real {
            accepted += 1;
        } else {
            rejected += 1;
        }
    }
    assert!(accepted >= 3, "the sweep must contain ACCEPTS");
    assert!(rejected >= 3, "and REJECTS, or the agreement is vacuous");
}

/// The measured population, rebuilt: a 29-conjunct `clearsy`-shaped
/// conjunction costs a fraction of a percent of the envelope, so METERING was
/// never what blocked the `and_neg` decomposition of those leaves.
///
/// The in-corpus measurement this replicates is in the module docs:
/// `work = 2_134, unfolded_work = 303, General = 646_602`.
#[test]
fn a_clearsy_shaped_conjunction_costs_a_fraction_of_the_envelope() {
    let mut terms = TermStore::new();
    let (conjunction, conjuncts) = clearsy_shaped_conjunction(&mut terms, 29);
    let mut clause = vec![conjunction];
    for &conjunct in &conjuncts {
        let negated = terms.mk_not(conjunct);
        clause.push(negated);
    }
    let step = and_neg_step(clause, conjunction);
    validate_one(&terms, &step).expect("the decomposition's own and_neg step must be valid");
    let stats = measured_payload(&step, &terms);
    let general = general_charge(stats);
    assert!(
        stats.unfolded_work < 1_000,
        "a QF_UF conjunction of small equalities unfolds to hundreds of nodes, \
         not millions: unfolded={}",
        stats.unfolded_work
    );
    assert!(
        general < PRODUCTION_ENVELOPE / 100,
        "the whole precharge must be under 1% of the envelope: {general}"
    );
    // And the corpus figure is the same order of magnitude, which is the claim
    // the lane's design rests on.
    assert!(
        (100_000..10_000_000).contains(&general),
        "measured in-corpus at 646_602; this replica must land in the same \
         decade: {general}"
    );
}

/// PARITY: the charge is not a blanket exemption in the other direction
/// either. A genuinely enormous `and_neg` still grows its charge past the
/// envelope, and the end-to-end metered entry point still refuses one.
#[test]
fn the_metering_still_refuses_an_oversized_and_neg_proof() {
    let mut terms = TermStore::new();
    let (conjunction, conjuncts) = clearsy_shaped_conjunction(&mut terms, 2_048);
    let mut clause = vec![conjunction];
    for &conjunct in &conjuncts {
        let negated = terms.mk_not(conjunct);
        clause.push(negated);
    }
    let step = and_neg_step(clause.clone(), conjunction);
    let stats = measured_payload(&step, &terms);
    let wide = general_charge(stats);
    let narrow = {
        let mut narrow_terms = TermStore::new();
        let (small, small_conjuncts) = clearsy_shaped_conjunction(&mut narrow_terms, 8);
        let mut small_clause = vec![small];
        for &conjunct in &small_conjuncts {
            let negated = narrow_terms.mk_not(conjunct);
            small_clause.push(negated);
        }
        general_charge(measured_payload(
            &and_neg_step(small_clause, small),
            &narrow_terms,
        ))
    };
    assert!(
        wide > narrow,
        "the charge must grow with the step's payload: {narrow} -> {wide}"
    );
    // A genuinely huge payload still exhausts the envelope up front.
    let huge = general_charge(PayloadStats {
        work: 20_000,
        bytes: 0,
        unfolded_work: 20_000,
        order_assignments: 0,
    });
    assert!(
        huge > PRODUCTION_ENVELOPE,
        "a genuinely huge payload must still exhaust the envelope: {huge}"
    );

    let mut proof = Proof::new();
    proof.add_step(step);
    let mut spent = 0_usize;
    let mut tiny = |work: usize, _bytes: usize| {
        spent += work;
        spent <= 64
    };
    let refused =
        check_proof_strict_with_context_and_progress(&proof, &terms, None, None, None, &mut tiny)
            .expect_err("a 64-unit envelope cannot afford a 2048-conjunct and_neg");
    assert_eq!(refused, ProofCheckError::ResourceLimit);

    let mut unbounded = |_: usize, _: usize| true;
    let accepted = check_proof_strict_with_context_and_progress(
        &proof,
        &terms,
        None,
        None,
        None,
        &mut unbounded,
    );
    assert!(
        !matches!(accepted, Err(ProofCheckError::ResourceLimit)),
        "the same proof must not be resource-refused under an unbounded \
         envelope, or the test above proves nothing about the METER: {accepted:?}"
    );
}

/// Each guard deleted or weakened, the named test OBSERVED failing, then
/// restored. `NEGATIVE` rows are results, not omissions.
pub(super) const AND_NEG_CHARGE_LEDGER: &[(&str, &str)] = &[
    (
        "is_clause_identity_route: AndNeg ADDED to the rule list",
        "RED — and_neg_is_not_admitted_to_any_dag_bounded_class AND \
         a_doubling_dag_refutes_any_reachable_dag_bound. SOUNDNESS-RELEVANT: \
         with `and_neg` in that list the doubling fixture is billed a few \
         thousand work units for >= 2^18 recursive matcher calls.",
    ),
    (
        "is_euf_identity_route: AndNeg ADDED to the rule list",
        "RED — and_neg_is_not_admitted_to_any_dag_bounded_class. The EUF route \
         charges `8 * payload.work`, which is likewise blind to the unfolding.",
    ),
    (
        "checker/boolean.rs `matches_negation_of_term`: the De Morgan `and`/`or` \
         arms deleted",
        "RED — validate_and_neg_decides_on_a_position_two_levels_below_the_literal \
         and a_doubling_dag_refutes_any_reachable_dag_bound. Deleting them is \
         what a DAG-bounded charge would REQUIRE to be sound, and it changes \
         what the checker accepts — which is why the charge, not the validator, \
         is the thing that had to stay.",
    ),
    (
        "checker/boolean.rs `matches_negated_components`: the `matched` bitmap \
         replaced by a count",
        "RED — the_mirror_agrees_with_the_real_validator, on the `duplicated \
         negation` case. That is the meta-false-PROVE the rule's own comment \
         records; the mirror reproduces the rejection independently.",
    ),
    (
        "metering_and_neg mirror: `mirror_negation`'s De Morgan arms deleted",
        "RED — the_mirror_agrees_with_the_real_validator (the `de morgan dual` \
         case flips to a disagreement). The mirror is only evidence while it \
         answers the same question, and this is the test that keeps it honest.",
    ),
    (
        "a_doubling_dag_refutes_any_reachable_dag_bound: the `general > calls` \
         assertion",
        "NEGATIVE — deleting it fails nothing, because the `dag_bounded < calls` \
         assertion above it already carries the refutation. It is kept as the \
         POSITIVE half of the same measurement: the class that is being kept \
         must be shown to bound the work, not merely to exceed the one being \
         refused.",
    ),
    (
        "select_semantic_charge_class: no change at all (this pass changes NO \
         charge model)",
        "NEGATIVE by construction — the corpus A/B for the lane that consumes \
         `and_neg` was run against an UNCHANGED meter, and the `ResourceLimit` \
         file set is reported with it.",
    ),
];

#[test]
fn and_neg_charge_ledger_is_present() {
    assert!(AND_NEG_CHARGE_LEDGER.len() >= 6);
}
