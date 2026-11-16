// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ground UF+LIA assumptions must use the same complete conjunction as the
//! ordinary solver, while keeping query-local state and core provenance.

use std::collections::{BTreeMap, BTreeSet};
use std::time::Duration;

use ay_dpll::api::{Logic, Solver};
use ay_dpll::CounterexampleStyle;

#[path = "native_regressions/mod.rs"]
mod native_regressions;

// Keep the solver's nested debug-build passes independent of the test
// harness's small default thread stack.
fn on_solver_stack(test: impl FnOnce() + Send + 'static) {
    let result = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(test)
        .expect("start solver test thread")
        .join();
    if let Err(panic) = result {
        std::panic::resume_unwind(panic);
    }
}

fn solver() -> Solver {
    let mut solver = Solver::new(Logic::All);
    solver.set_timeout(Some(Duration::from_secs(10)));
    solver.set_counterexample_style(CounterexampleStyle::Readable);
    solver.set_quantifier_deadline_backstop(false);
    solver
        .try_set_option("rlimit", "400000")
        .expect("conflict budget");
    solver.set_memory_limit(Some(512 * 1024 * 1024));
    solver
}

#[derive(Clone, Copy, Debug)]
enum AssertionRoute {
    Direct,
    Named,
}

#[derive(Clone, Copy)]
enum StageExpectation {
    Any,
    Required,
}

fn check_recursive_query(input: &'static str, sat: bool) {
    check_recursive_query_stage(input, sat, StageExpectation::Any);
}

fn check_recursive_query_with_primary(input: &'static str, sat: bool) {
    check_recursive_query_stage(input, sat, StageExpectation::Required);
}

fn check_recursive_query_stage(input: &'static str, sat: bool, stage: StageExpectation) {
    on_solver_stack(move || {
        for route in [AssertionRoute::Direct, AssertionRoute::Named] {
            let mut solver = solver();
            solver.set_produce_unsat_cores(matches!(route, AssertionRoute::Named));
            let roots = solver.parse_smtlib2(input).expect("fixture parses");
            solver.try_reset_assertions().expect("reset assertions");
            let (goal, hypotheses) = roots.split_last().expect("fixture has assertions");
            let details = match route {
                AssertionRoute::Direct => {
                    solver.try_assert_term(*goal).expect("assert goal");
                    solver.check_sat_assuming_with_details(hypotheses).solve
                }
                AssertionRoute::Named => {
                    for (index, &term) in hypotheses.iter().enumerate() {
                        solver
                            .try_assert_named(term, &format!("qh{index}"))
                            .expect("assert named hypothesis");
                    }
                    solver.try_assert_term(*goal).expect("assert goal");
                    solver.check_sat_with_details()
                }
            };
            if matches!(stage, StageExpectation::Required) {
                assert!(
                    details
                        .statistics
                        .get_int("uf.primary_congruence_clauses")
                        .is_some_and(|count| count > 0 && count <= 512),
                    "primary stage did not run: {route:?}: {details:?}"
                );
            }
            assert_eq!(details.result.is_sat(), sat, "{route:?}: {details:?}");
            assert_eq!(details.result.is_unsat(), !sat, "{route:?}: {details:?}");
            if sat {
                assert_uf_getters_congruent(&solver, &roots);
                solver.try_get_model_str().expect("validated SAT model");
            } else if matches!(route, AssertionRoute::Named) {
                let core = solver.try_get_unsat_core().expect("named core");
                assert_ne!(core, [] as [String; 0]);
                assert!(core.iter().all(|name| name.starts_with("qh")));
            }
        }
    });
}

fn assert_uf_getters_congruent(solver: &Solver, roots: &[ay_dpll::api::Term]) {
    let mut pending = roots.to_vec();
    let mut seen = BTreeSet::new();
    let mut points = BTreeMap::new();
    while let Some(term) = pending.pop() {
        if !seen.insert(solver.format_term(term)) {
            continue;
        }
        let children = solver.term_children(term);
        if let ay_dpll::api::TermKind::App { name, .. } = solver.term_kind(term) {
            if matches!(name.as_str(), "rf0" | "sf0" | "f" | "g" | "clip_nat_oob") {
                let args = children
                    .iter()
                    .map(|&arg| format!("{:?}", solver.try_get_value(arg).expect("UF argument")))
                    .collect::<Vec<_>>();
                let value = format!("{:?}", solver.try_get_value(term).expect("UF value"));
                if let Some(previous) = points.insert((name, args), value.clone()) {
                    assert_eq!(previous, value, "congruent public UF reads disagree");
                }
            }
        }
        pending.extend(children);
    }
}

#[test]
fn bounded_uflia_recursive_sat() {
    check_recursive_query(include_str!("fixtures/uflia_recursive_sat.smt2"), true);
}

#[test]
fn bounded_uflia_recursive_contract_unsat() {
    check_recursive_query(
        include_str!("fixtures/uflia_recursive_contract_unsat.smt2"),
        false,
    );
}

#[test]
fn bounded_uflia_recursive_contract_sat() {
    check_recursive_query(
        include_str!("fixtures/uflia_recursive_contract_sat.smt2"),
        true,
    );
}

#[test]
fn bounded_uflia_recursive_natural_return_unsat() {
    check_recursive_query_with_primary(
        include_str!("fixtures/uflia_recursive_natural_return_unsat.smt2"),
        false,
    );
}

#[test]
fn bounded_uflia_recursive_monotonic_context_unsat() {
    check_recursive_query_with_primary(
        include_str!("fixtures/uflia_recursive_monotonic_context_unsat.smt2"),
        false,
    );
}

#[test]
fn bounded_uflia_recursive_implementation_unsat() {
    check_recursive_query_with_primary(
        include_str!("fixtures/uflia_recursive_implementation_unsat.smt2"),
        false,
    );
}

#[test]
fn bounded_uflia_recursive_strict_monotonic_sat() {
    check_recursive_query_with_primary(
        include_str!("fixtures/uflia_recursive_strict_monotonic_sat.smt2"),
        true,
    );
}

#[test]
fn bounded_uflia_nested_call_sat() {
    check_recursive_query(include_str!("fixtures/uflia_nested_call_sat.smt2"), true);
}

#[test]
fn bounded_uflia_integer_division_clip_unsat() {
    check_recursive_query(
        include_str!("fixtures/uflia_integer_division_clip_unsat.smt2"),
        false,
    );
}

#[test]
fn bounded_uflia_integer_division_clip_sat_twin() {
    check_recursive_query(
        include_str!("fixtures/uflia_integer_division_clip_sat.smt2"),
        true,
    );
}

#[test]
fn bounded_uflia_arithmetic_ite_decrease_unsat() {
    check_recursive_query(
        include_str!("fixtures/uflia_arithmetic_ite_decrease_unsat.smt2"),
        false,
    );
}

#[test]
fn bounded_uflia_arithmetic_ite_decrease_sat_twin() {
    check_recursive_query(
        include_str!("fixtures/uflia_arithmetic_ite_decrease_sat.smt2"),
        true,
    );
}

#[test]
fn readable_model_rejects_an_active_uf_argument_collapse() {
    on_solver_stack(|| {
        let mut solver = solver();
        solver.set_produce_unsat_cores(true);
        let roots = solver
            .parse_smtlib2(
                "(set-option :produce-models true)
                 (declare-const x Int) (declare-fun f (Int) Int)
                 (assert (= (f x) 1)) (assert (= (f 0) 0))",
            )
            .expect("script parses");
        solver.try_reset_assertions().expect("reset assertions");
        for (index, &term) in roots.iter().enumerate() {
            solver
                .try_assert_named(term, &format!("premise{index}"))
                .expect("assert named premise");
        }
        let details = solver.check_sat_with_details();
        assert!(details.result.is_sat());
        assert!(details
            .statistics
            .get_int("uf.primary_congruence_clauses")
            .is_some_and(|count| count > 0 && count <= 512));
        let values = solver.try_get_named_values(&["x"]).expect("x value");
        assert!(matches!(&values[0], ay_dpll::api::ModelValue::Int(value) if *value != 0.into()));
        solver
            .try_get_model_str()
            .expect("complete fixed function model");
    });
}

#[test]
fn primary_congruence_keeps_strict_unsat_proof_and_sat_twin() {
    on_solver_stack(|| {
        for omit_bound in [false, true] {
            let mut solver = solver();
            solver.set_produce_proofs(true);
            let roots = solver
                .parse_smtlib2(
                    "(set-option :produce-models true)
                 (declare-const a Int) (declare-const b Int)
                 (declare-fun f (Int) Int)
                 (assert (<= a b)) (assert (<= b a))
                 (assert (not (= (f a) (f b))))",
                )
                .expect("script parses");
            solver.try_reset_assertions().expect("reset assertions");
            solver.try_assert_term(roots[0]).expect("lower bound");
            if !omit_bound {
                solver.try_assert_term(roots[1]).expect("upper bound");
            }
            solver.try_assert_term(roots[2]).expect("goal");
            let before = solver.to_smtlib2();
            let result = solver.check_sat();
            if omit_bound {
                assert!(result.is_sat());
                solver.try_get_model_str().expect("SAT twin model");
            } else {
                assert!(result.is_unsat());
                assert!(result.was_unsat_strictly_verified());
                assert!(solver.last_proof().is_some());
            }
            assert_eq!(solver.to_smtlib2(), before, "temporary lemmas leaked");
            let repeated = solver.check_sat();
            assert_eq!(repeated.is_sat(), omit_bound);
            assert_eq!(repeated.is_unsat(), !omit_bound);
            assert_eq!(solver.to_smtlib2(), before, "repeat changed assertions");
        }
    });
}

#[test]
fn readable_bool_function_rejects_an_active_numeric_argument_collapse() {
    check_recursive_query(
        "(set-option :produce-models true)
         (declare-const x Int) (declare-fun g (Int) Bool)
         (assert (<= 0 x)) (assert (g x)) (assert (not (g 0)))",
        true,
    );
}

#[test]
fn proof_requested_uflia_ite_and_omitted_premise_twin() {
    on_solver_stack(|| {
        for omit_last in [false, true] {
            let mut solver = solver();
            solver.set_produce_proofs(true);
            let roots = solver
                .parse_smtlib2(
                    "(set-option :produce-models true)
                     (declare-const c Bool) (declare-const x Int)
                     (declare-const y Int) (declare-fun f (Int) Int)
                     (assert (= (f (ite c x y)) 1))
                     (assert (= (f x) 0)) (assert (= (f y) 0))",
                )
                .expect("script parses");
            solver.try_reset_assertions().expect("reset assertions");
            let active = if omit_last { &roots[..2] } else { &roots[..] };
            let result = solver.check_sat_assuming(active);
            if omit_last {
                assert!(result.is_sat());
                solver.try_get_model_str().expect("SAT twin model");
            } else {
                assert!(!result.is_sat());
                if result.is_unsat() {
                    assert!(result.was_unsat_strictly_verified());
                    assert!(solver.last_proof().is_some());
                }
            }
        }
    });
}

#[test]
fn native_definition_namespace_collision_preserves_sat() {
    on_solver_stack(|| {
        let mut executor = ay_dpll::Executor::new();
        executor.set_timeout(Some(Duration::from_secs(10)));
        executor.set_resource_limit(Some(400_000));
        executor.set_memory_limit(Some(512 * 1024 * 1024));
        executor
            .execute_all(
                &ay_frontend::parse(
                    "(set-option :produce-models true) (set-logic QF_UFLIA)
                 (declare-const condition Bool) (declare-fun f (Int) Int)",
                )
                .expect("declarations parse"),
            )
            .expect("declare native context");
        let name = {
            let context = executor.context_mut();
            let condition = context.terms.find_var("condition").expect("condition");
            let one = context.terms.mk_int(1.into());
            let two = context.terms.mk_int(2.into());
            let ite = context.terms.mk_ite(condition, one, two);
            let name = format!("__ay_ite_def_{}", ite.0);
            let authored = context.terms.mk_var(&name, ay_core::Sort::Int);
            // This is the global-registration hook used by translated
            // constants, which can carry names ordinary declarations reject.
            context.register_native_global_symbol(name.clone(), authored, ay_core::Sort::Int);
            name
        };
        let script = format!(
            "(assert (= {name} 2))
             (assert (= (f (ite condition 1 2)) 1))
             (assert (= (ite condition 1 2) 1))
             (check-sat) (get-value ({name}))"
        );
        let outputs = executor
            .execute_all(&ay_frontend::parse(&script).expect("query parses"))
            .expect("native query executes");
        assert_eq!(outputs.first().map(String::as_str), Some("sat"));
        assert!(outputs.last().expect("native value").contains(" 2)"));
    });
}

#[test]
fn uflia_assumptions_leave_no_units_after_return_or_pop() {
    on_solver_stack(|| {
        let mut solver = solver();
        let roots = solver
            .parse_smtlib2(
                "(declare-const x Int) (declare-fun f (Int) Int)
                 (assert (= (f x) x)) (assert (< 0 x)) (assert (<= x 0))",
            )
            .expect("script parses");
        solver.try_reset_assertions().expect("reset assertions");
        solver.try_assert_term(roots[0]).expect("assert base");
        for scoped in [false, true] {
            if scoped {
                solver.try_push().expect("push");
            }
            assert!(solver.check_sat_assuming(&[roots[1]]).is_sat());
            assert!(solver.check_sat_assuming(&[roots[2]]).is_sat());
            assert!(solver.check_sat_assuming(&roots[1..]).is_unsat());
            if scoped {
                solver.try_pop().expect("pop");
            }
            assert!(solver.check_sat().is_sat());
        }
    });
}

const CORE_INPUT: &str = "
    (declare-const x Int) (declare-fun f (Int) Int)
    (assert (= (f x) x))
    (assert (<= 1 x))
    (assert (< (f x) 1))
    (assert (= (f 5) 17))";

#[test]
fn uflia_mixed_base_named_core_rechecks_only_its_own_premises() {
    on_solver_stack(|| {
        let mut solver = solver();
        solver.set_produce_unsat_cores(true);
        let roots = solver.parse_smtlib2(CORE_INPUT).expect("script parses");
        solver.try_reset_assertions().expect("reset assertions");
        solver.try_assert_term(roots[0]).expect("unnamed base");
        for (index, &term) in roots[1..].iter().enumerate() {
            solver
                .try_assert_named(term, &format!("premise{index}"))
                .expect("named premise");
        }
        assert!(solver.check_sat().is_unsat());
        let core = solver.try_get_unsat_core().expect("core");
        assert_ne!(core, [] as [String; 0]);

        let mut checker = self::solver();
        let fresh_roots = checker.parse_smtlib2(CORE_INPUT).expect("checker parses");
        checker.try_reset_assertions().expect("checker reset");
        checker.try_assert_term(fresh_roots[0]).expect("base");
        for name in core {
            let index: usize = name
                .strip_prefix("premise")
                .expect("core contains only supplied names")
                .parse()
                .expect("valid core index");
            checker
                .try_assert_term(fresh_roots[index + 1])
                .expect("core premise");
        }
        assert!(checker.check_sat().is_unsat());
    });
}

#[test]
fn proof_requested_uflia_assumptions_never_publish_a_wrong_verdict() {
    on_solver_stack(|| {
        let mut solver = solver();
        solver.set_produce_proofs(true);
        let roots = solver.parse_smtlib2(CORE_INPUT).expect("script parses");
        solver.try_reset_assertions().expect("reset assertions");
        solver.try_assert_term(roots[0]).expect("assert base");
        let result = solver.check_sat_assuming(&roots[1..3]);
        // A proof route may decline this fragment, but cannot accept a model of
        // the contradictory complete conjunction or borrow an omitted premise.
        assert!(!result.is_sat());
        assert!(solver.check_sat_assuming(&[roots[1]]).is_sat());
    });
}
