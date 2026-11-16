// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
use super::*;
use crate::api::{Logic, Model, ModelValue, Solver, Tactic};
fn fixture(body: &str) -> (Solver, Vec<crate::api::Term>) {
    let mut solver = Solver::new(Logic::All);
    let roots = solver.parse_smtlib2(body).unwrap();
    (solver, roots)
}
const HEADER: &str = "(set-logic QF_FF) (declare-const p Bool) (declare-const x (_ FiniteField 7))";
fn decided(body: &str, sat: bool) -> Option<Model> {
    let (mut solver, roots) = fixture(body);
    let goal = solver
        .apply_tactic_subgoals_converted(&Tactic::FieldSat, &roots, 0, None)
        .unwrap()
        .remove(0);
    assert_eq!(
        solver.assertions(),
        roots,
        "tactics must not assert a different source problem"
    );
    if sat {
        assert_eq!(goal.formulas.as_slice(), &[] as &[crate::api::Term]);
        Some(
            solver
                .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &Model::empty())
                .unwrap(),
        )
    } else {
        assert_eq!(goal.formulas.len(), 1);
        assert!(matches!(
            solver.terms().get(goal.formulas[0].id()),
            TermData::Const(Constant::Bool(false))
        ));
        None
    }
}
#[test]
fn field_sat_boolean_and_algebra_branches_reconstruct_actual_typed_models() {
    let input = format!("{HEADER} (assert (or p (= x #f1m7))) (assert (or (not p) (= x #f2m7))) (assert (= x #f2m7))");
    let model = decided(&input, true).unwrap();
    assert_eq!(model.bool_val("p"), Some(true));
    assert!(matches!(
        model.finite_field_val("x"),
        Some(ModelValue::FiniteField { value: 2, .. })
    ));
    decided(&format!("{HEADER} (assert (or p (= x #f1m7))) (assert (or (not p) (= x #f2m7))) (assert (= x #f3m7))"), false);
    decided("(declare-const p Bool) (declare-const q Bool) (assert (or p q)) (assert (or (not p) q)) (assert (not q))", false);
    let model = decided(
        "(declare-const p Bool) (declare-const q Bool) (assert (or p q))",
        true,
    )
    .unwrap();
    let (p, q) = (model.bool_val("p").unwrap(), model.bool_val("q").unwrap());
    assert!(p || q);
    decided("(assert false)", false);
    decided("", true);
}
#[test]
fn field_sat_nonlinear_branch_conflicts_are_not_propositional_assumptions() {
    let header = "(declare-const p Bool) (declare-const x (_ FiniteField 65537))";
    decided(&format!("{header} (assert (or p (= (ff.mul x x) #f1m65537))) (assert (or (not p) (= (ff.mul x x) #f4m65537))) (assert (= x #f3m65537))"), false);
    let model = decided(&format!("{header} (assert (or p (= (ff.mul x x) #f1m65537))) (assert (or (not p) (= (ff.mul x x) #f4m65537))) (assert (= x #f2m65537))"), true).unwrap();
    assert_eq!(model.bool_val("p"), Some(true));
}
#[test]
fn field_sat_model_reconstruction_rejects_wrong_bool_or_field_and_foreign_source() {
    let input = format!("{HEADER} (assert p) (assert (= x #f3m7))");
    let (mut solver, roots) = fixture(&input);
    let goal = solver
        .apply_tactic_subgoals_converted(&Tactic::FieldSat, &roots, 0, None)
        .unwrap()
        .remove(0);
    let converter = goal.model_converter.unwrap();
    let mut bad = Model::empty();
    bad.bool_values.insert("p".into(), false);
    assert!(solver.convert_tactic_model(&converter, &bad).is_err());
    let good = solver
        .convert_tactic_model(&converter, &Model::empty())
        .unwrap();
    assert_eq!(good.bool_val("p"), Some(true));
    let (other, _) = fixture(&input);
    assert!(other.convert_tactic_model(&converter, &good).is_err());
    let mut bad = Model::empty();
    bad.field_values.insert(
        "x".into(),
        ModelValue::FiniteField {
            value: 4,
            field: ay_core::FiniteFieldSort::new(7).unwrap(),
        },
    );
    assert!(solver.convert_tactic_model(&converter, &bad).is_err());
}
#[test]
fn field_sat_exact_small_domains_match_independent_enumeration() {
    for modulus in [2u32, 3, 7] {
        for a in 0..modulus {
            for b in 0..modulus {
                let input = format!("(declare-const p Bool) (declare-const x (_ FiniteField {modulus})) (assert (or p (= (ff.mul x x) #f{a}m{modulus}))) (assert (or (not p) (= (ff.mul x x) #f{b}m{modulus}))) (assert (not (= x #f0m{modulus})))");
                let exists = [false, true].into_iter().any(|p| {
                    (1..modulus)
                        .any(|x| (p || x * x % modulus == a) && (!p || x * x % modulus == b))
                });
                decided(&input, exists);
            }
        }
    }
}
#[test]
fn field_sat_original_owner_stays_stopped_but_new_request_recovers() {
    let (mut solver, roots) = fixture(&format!("{HEADER} (assert (or p (= x #f1m7)))"));
    let request = solver.begin_model_evaluation_read();
    solver.interrupt();
    assert!(solver
        .apply_tactic_subgoals_converted(&Tactic::FieldSat, &roots, 0, None)
        .is_err());
    solver.clear_interrupt();
    assert!(solver
        .apply_tactic_subgoals_converted(&Tactic::FieldSat, &roots, 0, None)
        .is_err());
    assert_eq!(
        solver.executor.tactic_refusal_origin(),
        Some(crate::UnknownOrigin::InterruptFlag)
    );
    drop(request);
    assert!(solver
        .apply_tactic_subgoals_converted(&Tactic::FieldSat, &roots, 0, None)
        .is_ok());
    solver.set_term_memory_limit(Some(0));
    let request = solver.begin_model_evaluation_read();
    assert!(solver
        .apply_tactic_subgoals_converted(&Tactic::FieldSat, &roots, 0, None)
        .is_err());
    solver.set_term_memory_limit(None);
    assert!(solver
        .apply_tactic_subgoals_converted(&Tactic::FieldSat, &roots, 0, None)
        .is_err());
    assert_eq!(
        solver.executor.tactic_refusal_origin(),
        Some(crate::UnknownOrigin::MemoryBudget)
    );
    drop(request);
}
#[test]
fn field_sat_unsupported_source_never_gains_a_satisfiable_goal() {
    for input in [
        "(declare-const x Int) (assert (= x 1))",
        "(declare-const x (_ FiniteField 7)) (declare-const y (_ FiniteField 11)) (assert (= x #f1m7)) (assert (= y #f1m11))",
        "(declare-fun f (Bool) Bool) (declare-const p Bool) (assert (f p))",
    ] {
        let (mut solver, roots) = fixture(input);
        assert!(solver.apply_tactic_subgoals_converted(&Tactic::FieldSat, &roots, 0, None).is_err());
        assert_eq!(solver.assertions(), roots);
    }
}

#[test]
fn field_sat_native_resolution_checker_rejects_forged_authored_premise() {
    let (mut solver, roots) =
        fixture("(declare-const p Bool) (declare-const q Bool) (assert p) (assert (not p))");
    let original: Vec<_> = roots.iter().map(|term| term.id()).collect();
    let operation = solver.begin_tactic_operation().unwrap();
    let owner = operation.admission();
    let terms = &mut solver.executor.ctx.terms;
    let mut prepared = source(terms, &original, owner).unwrap();
    assert!(matches!(
        decide(terms, &mut prepared, owner).unwrap(),
        BooleanDecision::Unsat
    ));
    check_refutation(terms, &original, &prepared.proof, owner).unwrap();
    let borrowed = super::super::field_to_bv::Borrowed(owner);
    let forged = CountedTermBuilder::with_admission(terms, &borrowed)
        .unwrap()
        .boolean(false)
        .unwrap();
    prepared.proof.steps[0] = ProofStep::Assume(forged);
    assert!(check_refutation(terms, &original, &prepared.proof, owner).is_err());
}

#[test]
fn field_sat_native_boolean_gate_certificates_compose_with_field_atoms() {
    for a in [false, true] {
        for b in [false, true] {
            for (form, expected) in [
                ("(=> (= x #f1m7) p)", !a || b),
                ("(xor (= x #f1m7) p)", a != b),
                ("(= (= x #f1m7) p)", a == b),
                ("(ite (= x #f1m7) p (not p))", if a { b } else { !b }),
            ] {
                let value = if a { 1 } else { 2 };
                let boolean = if b { "p" } else { "(not p)" };
                decided(
                    &format!(
                        "{HEADER} (assert (= x #f{value}m7)) (assert {boolean}) (assert {form})"
                    ),
                    expected,
                );
            }
        }
    }
}

#[test]
fn field_sat_rejects_malformed_field_atoms_before_boolean_refutation() {
    let mut solver = Solver::new(Logic::All);
    let terms = &mut solver.executor.ctx.terms;
    let x = terms.mk_var(
        "x",
        Sort::FiniteField(ay_core::FiniteFieldSort::new(7).unwrap()),
    );
    let y = terms.mk_var(
        "y",
        Sort::FiniteField(ay_core::FiniteFieldSort::new(11).unwrap()),
    );
    let bad = terms.mk_app(Symbol::Named("=".into()), [x, y], Sort::Bool);
    let not_bad = terms.mk_not_raw(bad);
    let operation = solver.begin_tactic_operation().unwrap();
    assert!(source(
        &mut solver.executor.ctx.terms,
        &[bad, not_bad],
        operation.admission()
    )
    .is_err());
}

#[test]
fn field_sat_inverse_names_preserve_unrelated_original_assignments() {
    let (mut solver, roots) =
        fixture("(declare-const x (_ FiniteField 7)) (assert (not (= x #f0m7)))");
    let TermData::Not(atom) = solver.terms().get(roots[0].id()) else {
        panic!("negated field atom")
    };
    let collision = format!("@ay.ffsat.inverse.{}.0", atom.index());
    solver
        .parse_smtlib2(&format!("(declare-const {collision} (_ FiniteField 7))"))
        .unwrap();
    let goal = solver
        .apply_tactic_subgoals_converted(&Tactic::FieldSat, &roots, 0, None)
        .unwrap()
        .remove(0);
    assert_eq!(goal.formulas.as_slice(), &[] as &[crate::api::Term]);
    let mut input = Model::empty();
    input.field_values.insert(
        collision.clone(),
        ModelValue::FiniteField {
            value: 6,
            field: ay_core::FiniteFieldSort::new(7).unwrap(),
        },
    );
    let model = solver
        .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &input)
        .unwrap();
    assert!(
        matches!(model.finite_field_val("x"), Some(ModelValue::FiniteField {value, ..}) if *value != 0)
    );
    assert!(matches!(
        model.finite_field_val(&collision),
        Some(ModelValue::FiniteField { value: 6, .. })
    ));
}

#[test]
fn field_sat_composed_and_repeated_solved_goals_keep_the_original_typed_witness() {
    for tactic in [
        Tactic::FieldSat.then(Tactic::FieldSat),
        Tactic::FieldSat.repeat(),
        Tactic::FieldSolve.then(Tactic::FieldSat),
        Tactic::FieldSat.then(Tactic::SolveEqs),
        Tactic::FieldSolve.then(Tactic::SolveEqs),
    ] {
        let (mut solver, roots) =
            fixture("(declare-const x (_ FiniteField 7)) (assert (= x #f3m7))");
        let goal = solver
            .apply_tactic_subgoals_converted(&tactic, &roots, 0, None)
            .unwrap()
            .remove(0);
        assert_eq!(goal.formulas.as_slice(), &[] as &[crate::api::Term]);
        let model = solver
            .convert_tactic_model(goal.model_converter.as_ref().unwrap(), &Model::empty())
            .unwrap();
        assert!(matches!(
            model.finite_field_val("x"),
            Some(ModelValue::FiniteField { value: 3, .. })
        ));
        assert_eq!(solver.assertions(), roots);
    }
}

#[test]
fn converted_field_decision_keeps_original_witness_and_operation() {
    let (mut solver, roots) = fixture(&format!("{HEADER} (assert p) (assert (= x #f3m7))"));
    let operation = solver.begin_tactic_operation().unwrap();
    let mut goals = solver
        .apply_tactic_subgoals_in_operation(
            &operation,
            &Tactic::FieldSat.then(Tactic::SolveEqs),
            &roots,
            0,
            None,
        )
        .unwrap();
    let goal = goals.pop().unwrap();
    let decision = solver
        .check_converted_tactic_goal_in_operation(
            operation,
            goal.model_converter.as_ref().unwrap(),
            &goal.formulas,
            &[],
        )
        .unwrap();
    assert!(matches!(
        decision.result.result(),
        crate::api::SolveResult::Sat
    ));
    assert!(decision.validate(&solver));
    let model = decision.model.as_ref().unwrap();
    assert_eq!(model.bool_val("p"), Some(true));
    assert!(matches!(
        model.finite_field_val("x"),
        Some(ModelValue::FiniteField { value: 3, .. })
    ));
}

#[test]
fn converted_field_decision_does_not_revive_an_interrupted_original_operation() {
    let (mut solver, roots) = fixture(&format!("{HEADER} (assert (= x #f3m7))"));
    let operation = solver.begin_tactic_operation().unwrap();
    let goal = solver
        .apply_tactic_subgoals_in_operation(&operation, &Tactic::FieldSat, &roots, 0, None)
        .unwrap()
        .remove(0);
    solver.interrupt();
    // Clearing the public flag does not clear this already stopped operation.
    assert!(!operation.validate(&solver));
    solver.clear_interrupt();
    assert!(solver
        .check_converted_tactic_goal_in_operation(
            operation,
            goal.model_converter.as_ref().unwrap(),
            &goal.formulas,
            &[]
        )
        .is_err());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::executor_types::UnknownReason::Interrupted)
    );
    assert!(
        solver.model().is_none(),
        "failed request retires every preceding model"
    );
    // A separately requested public operation may proceed after that failure.
    let operation = solver.begin_tactic_operation().unwrap();
    let goal = solver
        .apply_tactic_subgoals_in_operation(&operation, &Tactic::FieldSat, &roots, 0, None)
        .unwrap()
        .remove(0);
    let decision = solver
        .check_converted_tactic_goal_in_operation(
            operation,
            goal.model_converter.as_ref().unwrap(),
            &goal.formulas,
            &[],
        )
        .unwrap();
    assert!(matches!(
        decision.result.result(),
        crate::api::SolveResult::Sat
    ));
}

#[test]
fn converted_field_decision_constructor_publishes_original_interrupt_and_retires_model() {
    let (mut solver, _) = fixture("(assert true)");
    assert!(matches!(
        solver.check_sat().result(),
        crate::api::SolveResult::Sat
    ));
    assert!(solver.model().is_some());
    solver.interrupt();
    assert!(solver.begin_tactic_operation_for_check().is_err());
    assert_eq!(
        solver.unknown_reason(),
        Some(crate::executor_types::UnknownReason::Interrupted)
    );
    assert!(solver.model().is_none());
    solver.clear_interrupt();
    assert!(matches!(
        solver.check_sat().result(),
        crate::api::SolveResult::Sat
    ));
}
