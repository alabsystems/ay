// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Actual scalar64 false-postcondition query exported by deductive-checks. Its 17
//! hypotheses and negated goal are satisfiable: singleton carrier domains,
//! constant carrier-valued functions, and true Boolean predicates suffice.
//! The pinned Z3 5.3.3 reference also returns SAT on this complete fixture.

use std::time::Duration;

use ay_dpll::api::{Logic, ModelValue, Solver};
use ay_dpll::CounterexampleStyle;

fn on_solver_stack(test: impl FnOnce() + Send + 'static) {
    let result = std::thread::Builder::new()
        .stack_size(64 * 1024 * 1024)
        .spawn(test)
        .expect("solver test thread")
        .join();
    if let Err(panic) = result {
        std::panic::resume_unwind(panic);
    }
}

fn captured_solver(input: &str) -> Solver {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    solver.set_counterexample_style(CounterexampleStyle::Readable);
    solver.set_produce_unsat_cores(true);
    solver.set_timeout(Some(Duration::from_millis(10_000)));
    solver.set_quantifier_deadline_backstop(false);
    solver
        .try_set_option("rlimit", "400000")
        .expect("actual deductive-checks conflict allowance");
    solver.set_memory_limit(Some(512 * 1024 * 1024));
    solver
        .parse_smtlib2(input)
        .expect("complete exported query");
    solver
}

#[test]
fn captured_modern_boolean_boxing_has_a_checked_readable_model() {
    on_solver_stack(|| {
        // Observe existing rejection decisions without changing semantics.
        let mut flags = ay_core::misc_cli_flags().clone();
        flags.model_reject_dump = true;
        let _diagnostics = ay_core::misc_test_override::set(flags);

        let mut solver = captured_solver(include_str!(
            "../fixtures/deductive_checks_modern_bool_model.smt2"
        ));
        let roots = solver.assertions();
        assert_eq!(roots.len(), 18, "17 hypotheses and the negated goal");
        let details = solver.try_check_sat_with_details().expect("solve");
        assert!(details.result.is_sat(), "{details:?}");
        assert!(details.result.was_model_validated(), "{details:?}");
        assert!(details.result.has_sat_emission_witness(), "{details:?}");
        assert!(details.accept_for_consumer().expect("checked SAT").is_sat());
        assert_ne!(solver.try_get_model_str().expect("published model"), "");
        for root in roots {
            assert!(
                matches!(solver.try_get_value(root), Ok(ModelValue::Bool(true))),
                "public model must satisfy {}",
                solver.format_term(root)
            );
        }
    });
}

#[test]
fn captured_positive_update_obligation_keeps_its_checked_refutation() {
    on_solver_stack(|| {
        let mut solver = captured_solver(include_str!(
            "../fixtures/deductive_checks_modern_bool_positive.smt2"
        ));
        assert_eq!(
            solver.assertions().len(),
            29,
            "28 hypotheses and negated goal"
        );
        let details = solver
            .try_check_sat_with_details()
            .expect("positive obligation");
        assert!(details.result.is_unsat(), "{details:?}");
        assert!(details.result.has_unsat_emission_witness(), "{details:?}");
        assert!(details
            .accept_for_consumer()
            .expect("checked UNSAT")
            .is_unsat());
        let core = solver
            .try_get_unsat_core()
            .expect("original hypothesis names");
        assert_ne!(core, [] as [String; 0]);
        assert!(core
            .iter()
            .all(|name| (0..28).any(|i| name == &format!("qh{i}"))));
    });
}

#[test]
fn captured_boxing_hypothesis_keeps_activation_and_original_core_terms() {
    on_solver_stack(|| {
        let mut solver = captured_solver(include_str!(
            "../fixtures/deductive_checks_modern_bool_model.smt2"
        ));
        // A derived API control using the actual future-value roundtrip root,
        // not a different representation of the complete captured obligation.
        let hypothesis = solver.assertions()[4];
        let opposite = solver
            .try_not(hypothesis)
            .expect("complementary assumption");
        solver
            .try_reset_assertions()
            .expect("empty base, same declarations");
        for assumption in [hypothesis, opposite, hypothesis] {
            let details = solver
                .try_check_sat_assuming_with_details(&[assumption])
                .expect("one temporary hypothesis");
            assert!(details.solve.result.is_sat(), "{details:?}");
            assert!(details.solve.result.was_model_validated(), "{details:?}");
            assert!(details.accept_for_consumer().expect("checked SAT").is_sat());
            assert!(matches!(
                solver.try_get_value(assumption),
                Ok(ModelValue::Bool(true))
            ));
            assert!(
                solver.assertions().is_empty(),
                "temporary hypothesis leaked"
            );
        }
        solver.set_produce_proofs(true);
        let details = solver
            .try_check_sat_assuming_with_details(&[hypothesis, opposite])
            .expect("complementary original assumptions");
        assert!(details.solve.result.is_unsat(), "{details:?}");
        assert!(
            details.solve.result.was_unsat_strictly_verified(),
            "{details:?}"
        );
        assert!(details
            .accept_for_consumer()
            .expect("strict UNSAT")
            .is_unsat());
        let core = details
            .unsat_assumptions
            .expect("original assumption handles");
        assert_eq!(core.len(), 2);
        assert!(core.contains(&hypothesis) && core.contains(&opposite));
        assert!(
            solver.assertions().is_empty(),
            "complementary hypotheses leaked"
        );
    });
}
