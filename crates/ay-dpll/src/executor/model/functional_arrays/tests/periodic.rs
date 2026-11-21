// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

const PERIODIC_DECL: &str = "
    (declare-const m (Array Int Int))
    (assert (= m (lambda ((z Int)) (ite (= (mod z 2) 0) 1 0))))";

fn periodic_prepared(extra: &str) -> Executor {
    let mut exec = Executor::new();
    let commands = parse(&format!("{PERIODIC_DECL}{extra}")).unwrap();
    exec.execute_all(&commands).unwrap();
    exec
}

#[test]
fn periodic_int_candidate_owns_the_complete_alias_and_every_authored_root() {
    let exec = periodic_prepared(
        "(declare-const alias (Array Int Int))
        (assert (= alias m))
        (assert (= (select alias (- 2)) 1))
        (assert (= (select m (- 1)) 0))
        (assert (= (select m 0) 1))
        (assert (= (select m 1) 0))",
    );
    let model = installed(&exec);
    assert!(matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
    let text = exec
        .functional_array_render(&model, variable(&exec, "m"))
        .unwrap()
        .unwrap();
    assert!(text.contains("(mod ay!model!index 2)"));
    for name in ["m", "alias"] {
        for (index, expected) in [(-3, 0), (-2, 1), (1000, 1)] {
            let key = EvalValue::Rational(num_rational::BigRational::from_integer(index.into()));
            let result = exec.functional_array_read(&model, variable(&exec, name), &key);
            assert_eq!(
                result,
                Some(EvalValue::Rational(
                    num_rational::BigRational::from_integer(expected.into())
                ))
            );
        }
    }
}

#[test]
fn periodic_int_conflicting_read_and_forged_residue_never_confirm() {
    let exec = periodic_prepared("(assert (= (select m 0) 0))");
    let model = installed(&exec);
    assert!(!matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));

    let exec = periodic_prepared("");
    let mut model = installed(&exec);
    let sort = Sort::array(Sort::Int, Sort::Int);
    let wrong = ArraySnapshot::periodic(
        &[ModelValue::Int(0.into()), ModelValue::Int(1.into())],
        &sort,
        &mut 100_000,
    )
    .unwrap();
    for (_, entry) in &mut model.functional_arrays.as_mut().unwrap().entries {
        *entry = Arc::clone(&wrong);
    }
    assert!(!matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
}

#[test]
fn periodic_int_conflicting_alias_definitions_cannot_select_one_silently() {
    let exec = periodic_prepared(
        "(declare-const alias (Array Int Int))
        (assert (= alias m))
        (assert (= alias (lambda ((z Int)) (ite (= (mod z 2) 0) 0 1))))",
    );
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_none());
}

#[test]
fn periodic_int_raw_binder_modulus_and_source_change_preserve_refusal() {
    for body in ["(+ z 1)", "(mod z 0)", "(mod z (- 2))"] {
        let mut exec = Executor::new();
        exec.execute_all(
            &parse(&format!(
                "(declare-const a (Array Int Int))
            (assert (= a (lambda ((z Int)) {body})))"
            ))
            .unwrap(),
        )
        .unwrap();
        let mut model = Model::empty();
        exec.install_functional_array_candidate(&mut model);
        assert!(model.functional_arrays.is_none(), "{body}");
    }
    let mut old_epoch = periodic_prepared("");
    let old_model = installed(&old_epoch);
    old_epoch.begin_public_solve(false);
    assert!(old_model
        .functional_array_value(&old_epoch, variable(&old_epoch, "m"))
        .is_err());
    let mut exec = periodic_prepared("");
    let model = installed(&exec);
    exec.execute_all(&parse("(push 1)(assert true)").unwrap())
        .unwrap();
    assert!(model
        .functional_array_value(&exec, variable(&exec, "m"))
        .is_err());
    assert!(!matches!(confirm(&exec, &model), GateVerdict::ConfirmedSat));
    exec.execute_all(&parse("(pop 1)").unwrap()).unwrap();
    assert!(model
        .functional_array_value(&exec, variable(&exec, "m"))
        .is_err());
}

#[test]
fn periodic_int_completion_proposes_a_checked_ground_witness_through_full_emit() {
    let mut exec = periodic_prepared(
        "(declare-const x Int)
        (assert (= (select m x) 1))",
    );
    exec.last_unknown_reason = Some(crate::executor_types::UnknownReason::UnsupportedArithmetic);
    assert!(exec.try_periodic_array_model_completion());
    assert!(
        !exec.last_model_validated,
        "the ordinary emitter still owns validation authority"
    );
    assert!(exec.last_sat_certificate.is_none());
    let model = exec.last_model.as_ref().unwrap();
    assert!(matches!(confirm(&exec, model), GateVerdict::ConfirmedSat));
    assert_eq!(
        exec.emit_sat_verdict(crate::executor_types::SolveResult::Sat, &[])
            .unwrap(),
        crate::executor_types::SolveResult::Sat
    );
    assert!(exec.last_model_validated);
    assert!(exec.last_sat_certificate.is_some());
}

#[test]
fn periodic_int_completion_keeps_conflicting_scalar_and_missing_uf_unknown() {
    for extra in [
        "(declare-const x Int)(assert (= x 0))(assert (= x 1))",
        "(declare-const x Int)(assert (= x 1))(assert (= (select m x) 1))",
        "(declare-fun missing (Int) Int)(assert (= (missing 0) 1))",
    ] {
        let mut exec = periodic_prepared(extra);
        exec.last_unknown_reason =
            Some(crate::executor_types::UnknownReason::UnsupportedArithmetic);
        assert!(!exec.try_periodic_array_model_completion(), "{extra}");
        assert_eq!(
            exec.last_unknown_reason,
            Some(crate::executor_types::UnknownReason::UnsupportedArithmetic)
        );
        assert!(exec.last_sat_certificate.is_none());
    }
}

#[test]
fn periodic_int_completion_honors_stop_and_missing_search_budget() {
    for reason in [
        crate::executor_types::UnknownReason::Timeout,
        crate::executor_types::UnknownReason::Interrupted,
        crate::executor_types::UnknownReason::MemoryLimit,
        crate::executor_types::UnknownReason::ResourceLimit,
    ] {
        let mut exec = periodic_prepared("");
        exec.last_unknown_reason = Some(reason);
        assert!(!exec.try_periodic_array_model_completion());
        assert_eq!(exec.last_unknown_reason, Some(reason));
        assert!(exec.last_sat_certificate.is_none());
    }
    let mut exec = periodic_prepared("");
    exec.solve_deadline.set(Some(ay_core::time::Instant::now()));
    assert!(!exec.try_periodic_array_model_completion());
    assert!(exec.last_sat_certificate.is_none());
    let mut exec = periodic_prepared("");
    exec.record_evaluation_stop(UnknownOrigin::IncompleteSolverLane);
    assert!(!exec.try_periodic_array_model_completion());
    assert!(exec.last_sat_certificate.is_none());
}

#[test]
fn periodic_int_producer_admits_all_borrowed_edges_before_reserving_a_wide_walk() {
    let mut exec = Executor::new();
    let bound = exec.ctx.terms.mk_fresh_named_var("wide_index", Sort::Int);
    let two = exec.ctx.terms.mk_int(2.into());
    let residue = exec
        .ctx
        .terms
        .mk_app(Symbol::named("mod"), [bound, two], Sort::Int);
    let body =
        exec.ctx
            .terms
            .mk_app_structural(Symbol::named("+"), vec![residue; 10_000], Sort::Int);
    let lambda = exec.ctx.terms.mk_lambda_array(bound, body);
    let array = exec
        .ctx
        .terms
        .mk_fresh_named_var("wide_array", Sort::array(Sort::Int, Sort::Int));
    let root = exec.ctx.terms.mk_eq(array, lambda);
    exec.ctx.assertions.push(root);
    let used = exec.evaluation_attempt().functional_work_counter();
    used.store(MAX_FUNCTIONAL_WORK - 100, Ordering::Release);
    let mut model = Model::empty();
    exec.install_functional_array_candidate(&mut model);
    assert!(model.functional_arrays.is_none());
    assert_eq!(used.load(Ordering::Acquire), work_counter::REFUSED);
}

fn recovery_owner(
    exec: &Executor,
    allowance: usize,
) -> crate::executor::model::recovery_admission::RecoveryScope {
    use crate::executor::model::recovery_admission::RecoveryScope;
    let counter = exec.evaluation_attempt().functional_work_counter();
    RecoveryScope::enter_with_work_owner(
        exec,
        allowance,
        allowance,
        Box::new(move |work, bytes| {
            work.checked_add(bytes)
                .is_some_and(|amount| work_counter::debit(&counter, amount))
        }),
    )
    .expect("one original recovery owner")
}

#[test]
fn periodic_int_scalar_evaluation_reuses_the_original_recovery_meter() {
    let exec = periodic_prepared("(declare-const x Int)(assert (= x 5))");
    let variable = variable(&exec, "x");
    let roots = exec.independent_gate_query_roots().unwrap();
    let counter = exec.evaluation_attempt().functional_work_counter();
    let model = Model::empty();
    let scope = recovery_owner(&exec, 16_384);
    let mut successes = 0;
    for _ in 0..1000 {
        if super::super::periodic_candidate::scalar_value(&exec, &model, variable, &roots).is_none()
        {
            break;
        }
        successes += 1;
    }
    assert!(successes > 0 && successes < 1000);
    assert!(counter.load(Ordering::Acquire) > 0);
    assert!(
        !scope.admission().pay(0, 0),
        "the original refusal remains sticky"
    );
}

#[test]
fn periodic_int_shared_meter_has_no_snapshot_double_debit_or_legacy_activation() {
    let exec = periodic_prepared("");
    let empty = Model::empty();
    let counter = exec.evaluation_attempt().functional_work_counter();
    let before = counter.load(Ordering::Acquire);
    empty.charge_functional_array_work(&exec, 7).unwrap();
    assert_eq!(counter.load(Ordering::Acquire), before);
    {
        let _scope = recovery_owner(&exec, 100);
        empty.charge_functional_array_work(&exec, 7).unwrap();
        assert_eq!(counter.load(Ordering::Acquire), before + 7);
    }
    let model = installed(&exec);
    let before = counter.load(Ordering::Acquire);
    let _scope = recovery_owner(&exec, 100);
    model.charge_functional_array_work(&exec, 7).unwrap();
    assert_eq!(counter.load(Ordering::Acquire), before + 7);
}

#[test]
fn periodic_int_late_scalar_payload_copy_refuses_under_the_same_owner() {
    use num_bigint::BigInt;
    let exec = periodic_prepared("(declare-const x Int)");
    let x = variable(&exec, "x");
    let roots = exec.independent_gate_query_roots().unwrap();
    let mut model = Model::empty();
    model.completed_values.insert(
        x,
        EvalValue::Rational(num_rational::BigRational::from_integer(
            BigInt::from(1) << 4096usize,
        )),
    );
    let scope = recovery_owner(&exec, 64);
    assert!(super::super::periodic_candidate::scalar_value(&exec, &model, x, &roots).is_none());
    assert!(!scope.admission().pay(0, 0));
    assert!(exec.last_sat_certificate.is_none());
}

#[test]
fn periodic_int_nonzero_equality_and_modulus_proposal_checks_all_roots() {
    let mut exec = Executor::new();
    exec.execute_all(
        &parse(
            "(declare-const m (Array Int Int))
        (declare-const x Int)(declare-const k Int)
        (assert (= x 5))(assert (= k 3))
        (assert (= m (lambda ((z Int)) (ite (= (mod z k) 0) 1 0))))
        (assert (= (select m x) 0))(assert (= (select m (- 3)) 1))",
        )
        .unwrap(),
    )
    .unwrap();
    exec.last_unknown_reason = Some(crate::executor_types::UnknownReason::UnsupportedArithmetic);
    assert!(exec.try_periodic_array_model_completion());
    let model = exec.last_model.as_ref().unwrap();
    assert_eq!(
        exec.evaluate_term(model, variable(&exec, "x")),
        EvalValue::Rational(num_rational::BigRational::from_integer(5.into()))
    );
    assert_eq!(
        exec.evaluate_term(model, variable(&exec, "k")),
        EvalValue::Rational(num_rational::BigRational::from_integer(3.into()))
    );
    assert!(matches!(confirm(&exec, model), GateVerdict::ConfirmedSat));
    assert_eq!(
        exec.emit_sat_verdict(crate::executor_types::SolveResult::Sat, &[])
            .unwrap(),
        crate::executor_types::SolveResult::Sat
    );
}

#[test]
fn periodic_int_explicit_conflicts_and_cancelled_source_cannot_gain_a_witness() {
    let mut conflict = periodic_prepared("(declare-const x Int)(assert (= x 5))");
    let x = variable(&conflict, "x");
    let mut model = Model::empty();
    model.completed_values.insert(
        x,
        EvalValue::Rational(num_rational::BigRational::from_integer(0.into())),
    );
    conflict.last_model = Some(model);
    assert!(!conflict.try_periodic_array_model_completion());
    assert!(conflict.last_sat_certificate.is_none());

    let mut cancelled = periodic_prepared("(declare-const x Int)(assert (= x 5))");
    cancelled.set_interrupt(Arc::new(std::sync::atomic::AtomicBool::new(true)));
    assert!(!cancelled.try_periodic_array_model_completion());
    assert!(cancelled.last_sat_certificate.is_none());
}
