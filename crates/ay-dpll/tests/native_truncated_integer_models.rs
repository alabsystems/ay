// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Native refutations of the canonical, truncating mathematical question.
//! `deductive-checks` Skolemizes the negated outer forall into this original Int root.

use ay_dpll::api::{Logic, ModelValue, Solver, Sort, Term};
use ay_dpll::CounterexampleStyle;
use std::time::Duration;

fn truncated_remainder(solver: &mut Solver, n: Term, divisor: i64) -> Term {
    let zero = solver.int_const(0);
    let divisor = solver.int_const(divisor);
    let nonnegative = solver.ge(n, zero);
    let positive = solver.modulo(n, divisor);
    let negative_n = solver.neg(n);
    let negative_magnitude = solver.modulo(negative_n, divisor);
    let negative = solver.neg(negative_magnitude);
    solver.ite(nonnegative, positive, negative)
}

#[test]
fn anonymous_integer_witness_keeps_the_complete_mixed_query() {
    for divisor in [5, -5] {
        let mut solver = Solver::new(Logic::All);
        solver.set_timeout(Some(Duration::from_secs(10)));
        solver.set_counterexample_style(CounterexampleStyle::Readable);
        solver.set_produce_unsat_cores(true);
        solver.set_produce_proofs(true);
        let path = solver.declare_const("pc$0", Sort::Bool);
        let returned = solver.declare_const("v1", Sort::bitvec(32));
        let ten = solver.bv_const(10, 32);
        let relation = solver.eq(returned, ten);
        let guarded = solver.implies(path, relation);
        solver.assert_term(path);
        solver.assert_term(guarded);
        let n = solver.fresh_var("__deductive_checks_refute_forall_n", Sort::Int);
        let zero = solver.int_const(0);
        let remainder = truncated_remainder(&mut solver, n, divisor);
        let refuted = solver.lt(remainder, zero);
        solver.push();
        solver.assert_term(refuted);
        let result = solver.check_sat();
        assert!(result.is_sat(), "divisor={divisor}: {result:?}");
        assert!(result.was_model_validated(), "{result:?}");
        assert!(result.accept_for_consumer().unwrap().is_sat());
        assert_eq!(
            solver.try_get_value(refuted).unwrap(),
            ModelValue::Bool(true)
        );
        assert_eq!(solver.try_get_value(path).unwrap(), ModelValue::Bool(true));
        assert_eq!(
            solver.try_get_value(relation).unwrap(),
            ModelValue::Bool(true)
        );
        solver.pop();
        solver.push();
        let nonnegative = solver.ge(n, zero);
        solver.assert_term(nonnegative);
        solver.assert_term(refuted);
        assert!(
            !solver.check_sat().is_sat(),
            "the candidate must not discard the new nonnegative-domain root"
        );
    }
}

#[test]
fn original_truncated_remainder_question_has_a_checked_negative_witness() {
    for divisor in [5, -5] {
        let mut solver = Solver::new(Logic::Uflia);
        solver.set_timeout(Some(Duration::from_secs(10)));
        let n = solver.declare_const("__deductive_checks_refute_forall_n", Sort::Int);
        let zero = solver.int_const(0);
        let remainder = truncated_remainder(&mut solver, n, divisor);
        let claim = solver.ge(remainder, zero);
        let refuted = solver.not(claim);
        solver.push();
        solver.assert_term(refuted);
        let result = solver.check_sat();
        assert!(
            result.is_sat(),
            "original divisor={divisor} root: {result:?}"
        );
        assert!(result.was_model_validated(), "{result:?}");
        assert!(result
            .accept_for_consumer()
            .expect("checked original model")
            .is_sat());
        assert_eq!(
            solver.try_get_value(refuted).unwrap(),
            ModelValue::Bool(true)
        );
        let ModelValue::Int(witness) = solver.try_get_value(n).unwrap() else {
            panic!("the original mathematical binder needs an exact Int witness");
        };
        assert!(witness < 0.into(), "{witness}");
    }
}
