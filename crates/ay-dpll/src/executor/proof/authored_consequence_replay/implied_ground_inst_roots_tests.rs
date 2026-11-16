// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit pins for the Boolean-equality roots and CEGQI witnesses of the
//! implied-universal lane (#iff-split-implied-authority).

use super::*;
use crate::executor::Executor;

fn loaded(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("fixture parses");
    let mut exec = Executor::new();
    assert!(
        exec.execute_all(&commands)
            .expect("fixture loads")
            .is_empty(),
        "fixture must contain declarations and assertions only"
    );
    exec.begin_unsat_query_epoch(&exec.ctx.assertions.clone());
    exec.bind_unsat_query_assumptions(&[]);
    exec
}

fn int_hint(exec: &mut Executor, value: i64) -> TermId {
    exec.ctx.terms.mk_int(BigInt::from(value))
}

fn has_rule(proof: &Proof, wanted: &AletheRule) -> bool {
    proof
        .steps
        .iter()
        .any(|step| matches!(step, ProofStep::Step { rule, .. } if rule == wanted))
}

/// The installed proof is complete under the strict checker and assumes only
/// authored roots.
fn assert_strict_authored_derivation(exec: &mut Executor, proof: &Proof) {
    assert!(has_rule(proof, &AletheRule::ForallInst));
    let quality = exec
        .check_proof_strict_with_datatypes(proof)
        .expect("the stitched proof is strictly checkable");
    assert!(quality.is_complete(), "no trust and no hole: {quality:?}");
    let authored = exec.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(proof, &authored).is_ok());
}

/// [`assert_strict_authored_derivation`], and the document exports without
/// `trust` or `hole`.
fn assert_strict_authored_certificate(exec: &mut Executor, proof: &Proof) {
    assert_strict_authored_derivation(exec, proof);
    let authored = exec.exact_concrete_authored_scope();
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        proof,
        &exec.ctx.terms,
        &authored,
        None,
    )
    .expect("the certificate is resolvable from the problem scope");
    assert!(
        !document.contains(":rule trust") && !document.contains(":rule hole"),
        "no unchecked rule may survive: {document}"
    );
}

/// `(assert p)` and `(assert (= p (forall ((x Int)) (> x 10))))` with the
/// ground fact `(< a 0)`: the slot witness `0` refutes the universal, and the
/// universal is reachable only through the authored Boolean equality.
///
/// MUTATION: make `implied_forall_root_orientations` return only the
/// implication reading (or `apply_implied_root_unit` return `None` for an
/// equality) and this fails.
#[test]
fn an_authored_boolean_equality_yields_its_universal_by_equiv_pos() {
    let mut exec = loaded(
        r#"
            (set-logic AUFLIA)
            (declare-const p Bool)
            (declare-const a Int)
            (assert p)
            (assert (= p (forall ((x Int)) (> x 10))))
            (assert (< a 0))
        "#,
    );
    assert!(
        exec.try_translate_implied_forall_ground_instantiation_unsat(),
        "the universal equated with the authored fact p fails at x := 0"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(
        has_rule(&proof, &AletheRule::EquivPos2) || has_rule(&proof, &AletheRule::EquivPos1),
        "the stitched proof reaches the universal through the equality"
    );
    assert!(!has_rule(&proof, &AletheRule::ImpliesPos));
    assert_strict_authored_certificate(&mut exec, &proof);
}

/// Both sides orders of the equality are read: `(= F p)` uses `equiv_pos1`.
#[test]
fn the_universal_may_sit_on_either_side_of_the_equality() {
    let mut exec = loaded(
        r#"
            (set-logic AUFLIA)
            (declare-const p Bool)
            (declare-const a Int)
            (assert p)
            (assert (= (forall ((x Int)) (> x 10)) p))
            (assert (< a 0))
        "#,
    );
    assert!(exec.try_translate_implied_forall_ground_instantiation_unsat());
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert_strict_authored_certificate(&mut exec, &proof);
}

/// FAILS CLOSED: `(= q F)` with `q` never asserted does not entail `F`.
#[test]
fn an_equality_with_an_unasserted_side_proposes_nothing() {
    let mut exec = loaded(
        r#"
            (set-logic AUFLIA)
            (declare-const q Bool)
            (declare-const a Int)
            (assert (= q (forall ((x Int)) (> x 10))))
            (assert (< a 0))
        "#,
    );
    let zero = int_hint(&mut exec, 0);
    exec.cegqi_witness_hints.push((Sort::Int, zero));
    assert!(!exec.try_translate_implied_forall_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());
}

/// The w1_51_00049 shape: every Int term of the problem sits under the
/// binder, so neither the slot scan nor the authored scan proposes a witness.
/// The CEGQI binder value `-2` refutes both branches of the `ite`.
const BODY_ONLY_WITNESS: &str = r#"
    (set-logic ALL)
    (declare-fun p () Bool)
    (declare-fun q () Bool)
    (assert (= q (forall ((v Int)) (> (+ (* v (ite p 0 2)) v) (- 2)))))
    (assert q)
"#;

#[test]
fn a_cegqi_witness_hint_closes_an_equated_universal() {
    // GUARD-REMOVAL PROOF for the hint source: without a hint the lane has no
    // `Int` witness and declines without touching proof state.
    let mut exec = loaded(BODY_ONLY_WITNESS);
    assert!(!exec.try_translate_implied_forall_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());

    let mut exec = loaded(BODY_ONLY_WITNESS);
    let witness = int_hint(&mut exec, -2);
    exec.cegqi_witness_hints.push((Sort::Int, witness));
    assert!(
        exec.try_translate_implied_forall_ground_instantiation_unsat(),
        "v := -2 refutes the universal for either value of p"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step { rule: AletheRule::ForallInst, args, .. } if args == &[witness]
        )),
        "the certificate instantiates the universal at the hinted value"
    );
    // Derivation only: the ground step over `(ite p 0 2)` is validated by
    // the strict checker, but the printer has no pinned-checker spelling for
    // it and exports it as `hole` (`printer-rule-without-external-spelling`),
    // the same document the CLI writes for w1_51 file 49.
    assert_strict_authored_derivation(&mut exec, &proof);
}

/// A hint that does not refute (`v := 0` satisfies the body for either value
/// of `p`) only costs a declined candidate.
#[test]
fn a_non_refuting_hint_installs_nothing() {
    let mut exec = loaded(BODY_ONLY_WITNESS);
    let wrong = int_hint(&mut exec, 0);
    exec.cegqi_witness_hints.push((Sort::Int, wrong));
    assert!(!exec.try_translate_implied_forall_ground_instantiation_unsat());
    assert!(exec.last_proof.is_none());
}

/// A CEGQI counterexample constant is closed but not problem-closed: it is
/// never proposed, so no certificate can name it.
#[test]
fn a_hint_naming_a_foreign_symbol_is_not_proposed() {
    let mut exec = loaded(BODY_ONLY_WITNESS);
    let foreign = exec.ctx.terms.mk_var("ce_v_foreign", Sort::Int);
    exec.cegqi_witness_hints.push((Sort::Int, foreign));
    let bound = exec.authored_binder_names(&exec.exact_concrete_authored_scope());
    let authored = exec.exact_concrete_authored_scope();
    let ledger = exec.cegqi_witness_hints.clone();
    assert_eq!(
        exec.authored_witness_hint_terms(&ledger, &authored, &Sort::Int, &bound, 8),
        [] as [TermId; 0]
    );
}

/// The measured w1_51 source: the refuting value is an E-MATCHED binder
/// value, not a CEGQI one; a non-refuting closed term recorded before it
/// costs nothing.
///
/// MUTATION: drop the `instance_witness_hints` read from
/// `implied_binder_witnesses` and this fails.
#[test]
fn an_ematched_witness_hint_closes_an_equated_universal() {
    let mut exec = loaded(BODY_ONLY_WITNESS);
    let p = exec.ctx.terms.mk_var("p", Sort::Bool);
    let zero = int_hint(&mut exec, 0);
    let two = int_hint(&mut exec, 2);
    let larger = exec.ctx.terms.mk_ite(p, zero, two);
    let witness = int_hint(&mut exec, -2);
    exec.instance_witness_hints.push((Sort::Int, larger));
    exec.instance_witness_hints.push((Sort::Int, witness));
    assert!(
        exec.try_translate_implied_forall_ground_instantiation_unsat(),
        "v := -2 refutes the universal for either value of p"
    );
    let proof = exec
        .last_proof
        .clone()
        .expect("translation installs last_proof");
    assert!(proof.steps.iter().any(|step| matches!(
        step,
        ProofStep::Step { rule: AletheRule::ForallInst, args, .. } if args == &[witness]
    )));
    // Derivation only, as above: the `ite` ground step prints as `hole`.
    assert_strict_authored_derivation(&mut exec, &proof);
}
