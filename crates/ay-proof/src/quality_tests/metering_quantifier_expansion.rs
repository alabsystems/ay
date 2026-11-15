// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `SemanticChargeClass::QuantifierProgressMetered` and
//! `SemanticChargeClass::EquivPosIdentityShape` (`quality/quantifier_charge.rs`).
//!
//! Every claim is pinned on steps the REAL strict validator accepts (or, for
//! the forgery, rejects), with `PayloadStats` from the REAL payload walk:
//!
//!  * both classes charge less than the `General` model they replace, at every
//!    payload (a tightening), and linearly in the payload;
//!  * the quantifier validators debit their real work through the envelope as
//!    they run, so a step too large for the envelope is still refused — by the
//!    validator, not by an estimate;
//!  * the `equiv_pos` class admits ONLY the emitted identity shape; the
//!    double-negation-collapsed and reordered spellings, which the validator
//!    also accepts but reaches through `matches_negation_of_term`'s deeper
//!    arms, keep `General`.

use super::super::quantifier_charge::EQUIV_POS_IDENTITY_WORK_FACTOR;
use super::metering_and_pos::{charge, general_charge, measured_payload, validate_one};
use super::*;

/// Width of the fixture body: an `and` of this many distinct atoms over the
/// bound variable, so the payload (and the `General` product) grows with it.
const WIDTH: usize = 2_000;

struct Expansion {
    terms: TermStore,
    quantified: TermId,
    instance: TermId,
    witness: TermId,
}

/// `forall x. (and (p0 x) ... (pN x))` and its instance at a registered
/// Skolem witness `w`.
fn expansion(width: usize) -> Expansion {
    let mut terms = TermStore::new();
    let x = terms.mk_var("qx_x", Sort::Int);
    let witness = terms.mk_var("qx_w", Sort::Int);
    terms.mark_skolem_symbol("qx_w");
    let atoms = |terms: &mut TermStore, v: TermId| -> Vec<TermId> {
        (0..width)
            .map(|i| terms.mk_app(Symbol::named(format!("qx_p{i}")), vec![v], Sort::Bool))
            .collect()
    };
    let body_atoms = atoms(&mut terms, x);
    let instance_atoms = atoms(&mut terms, witness);
    let body = terms.mk_app(Symbol::named("and"), body_atoms, Sort::Bool);
    let instance = terms.mk_app(Symbol::named("and"), instance_atoms, Sort::Bool);
    let quantified = terms.mk_forall(vec![("qx_x".to_string(), Sort::Int)], body);
    Expansion {
        terms,
        quantified,
        instance,
        witness,
    }
}

fn forall_inst_step(e: &mut Expansion, instance: TermId) -> ProofStep {
    let not_quantified = e.terms.mk_not_raw(e.quantified);
    let implication = e.terms.mk_app(
        Symbol::named("or"),
        vec![not_quantified, instance],
        Sort::Bool,
    );
    ProofStep::Step {
        rule: AletheRule::ForallInst,
        clause: vec![implication],
        premises: Vec::new(),
        args: vec![e.witness],
    }
}

fn skolem_step(e: &mut Expansion) -> (ProofStep, TermId) {
    let equality = e.terms.mk_app(
        Symbol::named("="),
        vec![e.quantified, e.instance],
        Sort::Bool,
    );
    let step = ProofStep::Step {
        rule: AletheRule::Skolem,
        clause: vec![equality],
        premises: Vec::new(),
        args: vec![e.witness],
    };
    (step, equality)
}

fn equiv_pos_step(rule: AletheRule, clause: Vec<TermId>) -> ProofStep {
    ProofStep::Step {
        rule,
        clause,
        premises: Vec::new(),
        args: Vec::new(),
    }
}

/// The `General` charge the `Skolem` rule paid before this class: the product
/// and the private `(100_000, 8 MiB)` reservation.
fn old_skolem_charge(stats: PayloadStats) -> usize {
    general_charge(stats).max(100_000)
}

#[test]
fn forall_inst_and_skolem_are_progress_metered_and_charged_linearly() {
    let mut e = expansion(WIDTH);
    let instance = e.instance;
    let forall_inst = forall_inst_step(&mut e, instance);
    let (skolem, _) = skolem_step(&mut e);
    for (step, old) in [
        (&forall_inst, general_charge as fn(PayloadStats) -> usize),
        (&skolem, old_skolem_charge),
    ] {
        validate_one(&e.terms, step).expect("the fixture step is valid");
        assert_eq!(
            select_semantic_charge_class(step, &e.terms),
            SemanticChargeClass::QuantifierProgressMetered
        );
        let stats = measured_payload(step, &e.terms);
        let (work, bytes) = charge(step, &e.terms, stats);
        let linear = stats.work + stats.unfolded_work;
        assert!(
            work <= linear.max(100_000),
            "linear charge: {work} vs {linear}"
        );
        assert!(work <= old(stats), "a tightening: {work} vs {}", old(stats));
        assert!(
            old(stats) > 10 * work,
            "the fixture is wide enough to show the product: {} vs {work}",
            old(stats)
        );
        assert!(bytes >= stats.bytes, "the byte limb is unchanged");
    }
}

#[test]
fn quantifier_validators_debit_their_real_work_and_fail_closed() {
    let mut e = expansion(WIDTH);
    let instance = e.instance;
    let forall_inst = forall_inst_step(&mut e, instance);
    let (skolem, _) = skolem_step(&mut e);
    for step in [&forall_inst, &skolem] {
        let mut debited = 0usize;
        let mut table: Vec<Option<Vec<TermId>>> = Vec::new();
        validate_step_with_datatypes_and_progress(
            &e.terms,
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
            &mut |work, _| {
                debited += work;
                true
            },
        )
        .expect("valid under an unbounded envelope");
        // The substitution match visits every node of the instance pair.
        assert!(debited >= WIDTH, "the validator meters its walk: {debited}");
        // A caller envelope smaller than that walk refuses the step.
        let mut left = debited / 2;
        let mut table: Vec<Option<Vec<TermId>>> = Vec::new();
        let refused = validate_step_with_datatypes_and_progress(
            &e.terms,
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
            &mut |work, _| match left.checked_sub(work) {
                Some(rest) => {
                    left = rest;
                    true
                }
                None => false,
            },
        );
        assert_eq!(refused, Err(ProofCheckError::ResourceLimit));
    }
}

#[test]
fn a_forged_instance_is_still_refused_under_the_new_class() {
    let mut e = expansion(8);
    let x = e.terms.mk_var("qx_other", Sort::Int);
    let forged = e.terms.mk_app(Symbol::named("qx_p0"), vec![x], Sort::Bool);
    let step = forall_inst_step(&mut e, forged);
    assert_eq!(
        select_semantic_charge_class(&step, &e.terms),
        SemanticChargeClass::QuantifierProgressMetered
    );
    assert!(
        validate_one(&e.terms, &step).is_err(),
        "charge routing grants no authority"
    );
}

#[test]
fn equiv_pos_identity_shape_is_admitted_and_charged_linearly() {
    let mut e = expansion(WIDTH);
    let (_, equality) = skolem_step(&mut e);
    let (a, b) = (e.quantified, e.instance);
    let gate = e.terms.mk_not_raw(equality);
    let not_a = e.terms.mk_not_raw(a);
    let not_b = e.terms.mk_not_raw(b);
    for step in [
        equiv_pos_step(AletheRule::EquivPos2, vec![gate, not_a, b]),
        equiv_pos_step(AletheRule::EquivPos1, vec![gate, a, not_b]),
    ] {
        validate_one(&e.terms, &step).expect("the emitted shape is valid");
        assert_eq!(
            select_semantic_charge_class(&step, &e.terms),
            SemanticChargeClass::EquivPosIdentityShape
        );
        let stats = measured_payload(&step, &e.terms);
        let (work, bytes) = charge(&step, &e.terms, stats);
        assert_eq!(
            work,
            (stats.work * EQUIV_POS_IDENTITY_WORK_FACTOR + EQUIV_POS_IDENTITY_WORK_FACTOR)
                .min(general_charge(stats))
        );
        assert!(general_charge(stats) > 10 * work);
        assert_eq!(bytes, stats.bytes);
    }
}

#[test]
fn other_equiv_pos_spellings_keep_the_general_product() {
    let mut e = expansion(8);
    let (_, equality) = skolem_step(&mut e);
    let (a, b) = (e.quantified, e.instance);
    let gate = e.terms.mk_not_raw(equality);
    let not_a = e.terms.mk_not_raw(a);
    // Reordered operand literals: valid, but not the emitted order.
    let reordered = equiv_pos_step(AletheRule::EquivPos2, vec![gate, b, not_a]);
    // A double-negation-collapsed operand: `a = (not X)` with literal `X`,
    // which the validator reaches through `matches_positive_literal_of_term`.
    let inner = e.terms.mk_var("qx_inner", Sort::Bool);
    let negated = e.terms.mk_not_raw(inner);
    let collapsed_eq = e
        .terms
        .mk_app(Symbol::named("="), vec![negated, b], Sort::Bool);
    let collapsed_gate = e.terms.mk_not_raw(collapsed_eq);
    let collapsed = equiv_pos_step(AletheRule::EquivPos2, vec![collapsed_gate, inner, b]);
    // Gate not first.
    let gate_last = equiv_pos_step(AletheRule::EquivPos2, vec![not_a, b, gate]);
    for step in [reordered, collapsed, gate_last] {
        validate_one(&e.terms, &step).expect("the validator accepts this spelling");
        assert_eq!(
            select_semantic_charge_class(&step, &e.terms),
            SemanticChargeClass::General
        );
    }
}

#[test]
fn both_classes_are_tightenings_at_every_payload() {
    let mut e = expansion(4);
    let instance = e.instance;
    let forall_inst = forall_inst_step(&mut e, instance);
    let (skolem, equality) = skolem_step(&mut e);
    let gate = e.terms.mk_not_raw(equality);
    let not_a = e.terms.mk_not_raw(e.quantified);
    let equiv = equiv_pos_step(AletheRule::EquivPos2, vec![gate, not_a, e.instance]);
    for work in [0, 1, 3, 17, 1_000, 40_000] {
        for unfolded_work in [0, 1, 2, 5, 900, 50_000] {
            let stats = PayloadStats {
                work,
                bytes: 64,
                unfolded_work,
                fp_assignments: 0,
                order_assignments: 0,
            };
            assert!(charge(&forall_inst, &e.terms, stats).0 <= general_charge(stats));
            assert!(charge(&skolem, &e.terms, stats).0 <= old_skolem_charge(stats));
            assert!(charge(&equiv, &e.terms, stats).0 <= general_charge(stats));
        }
    }
}
