// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_frontend::{parse, Command};

const BOUNDED_FALSE: &str = "(set-logic UFLIA)\
    (declare-fun P (Int) Bool)\
    (assert (forall ((v Int)) (= (P v) (= v 1000))))\
    (assert (exists ((x Int)) (and (<= 0 x) (<= x 500) (P x))))";

fn executor_for(script: &str) -> Executor {
    let commands = parse(script).expect("valid quantified fixture");
    let mut executor = Executor::new();
    executor
        .execute_all(&commands)
        .expect("quantified fixture elaborates");
    executor
}

fn evidence_for(executor: &Executor) -> Option<CheckedExactForallExistsUnsat> {
    executor.try_authorize_exact_forall_exists_roots(&executor.ctx.assertions)
}

fn install_raw_pointwise_pair(
    executor: &mut Executor,
    point: i64,
    lower: i64,
    upper: i64,
    negated: bool,
    definition_trigger: bool,
    existential_trigger: bool,
) {
    let terms = &mut executor.ctx.terms;
    let predicate = Symbol::named("P");

    let v_name = "raw_definition_v".to_string();
    let v = terms.mk_var(&v_name, Sort::Int);
    let p_v = terms.mk_app(predicate.clone(), [v], Sort::Bool);
    let point_term = terms.mk_int(BigInt::from(point));
    let at_point = terms.mk_eq(v, point_term);
    let definition_body = terms.mk_eq(p_v, at_point);
    let definition_vars = vec![(v_name, Sort::Int)];
    let definition = if definition_trigger {
        terms.mk_forall_with_triggers(definition_vars, definition_body, vec![vec![p_v]])
    } else {
        terms.mk_forall(definition_vars, definition_body)
    };

    let x_name = "raw_existential_x".to_string();
    let x = terms.mk_var(&x_name, Sort::Int);
    let lower_term = terms.mk_int(BigInt::from(lower));
    let upper_term = terms.mk_int(BigInt::from(upper));
    let lower_bound = terms.mk_le(lower_term, x);
    let upper_bound = terms.mk_le(x, upper_term);
    let p_x = terms.mk_app(predicate, [x], Sort::Bool);
    let body = terms.mk_and(vec![lower_bound, upper_bound, p_x]);
    let existential_vars = vec![(x_name, Sort::Int)];
    let existential = if existential_trigger {
        terms.mk_exists_with_triggers(existential_vars, body, vec![vec![p_x]])
    } else {
        terms.mk_exists(existential_vars, body)
    };
    let existential_root = if negated {
        terms.mk_not(existential)
    } else {
        existential
    };
    executor.ctx.assertions = vec![definition, existential_root];
}

#[test]
fn recognizes_exact_unsat_theorems() {
    let square = executor_for(
        "(set-logic NIA)\
         (assert (forall ((x Int)) (exists ((y Int)) (= (* y y) x))))",
    );
    assert!(evidence_for(&square).is_some());

    let interval = executor_for(
        "(set-logic LIA)\
         (assert (forall ((x Int)) (exists ((y Int))\
            (and (<= y x) (>= y (+ x 1))))))",
    );
    assert!(evidence_for(&interval).is_some());

    let negated_valid = executor_for(
        "(set-logic LIA)\
         (assert (not (forall ((x Int)) (exists ((y Int))\
            (and (> y x) (> y -17))))))",
    );
    assert!(evidence_for(&negated_valid).is_some());
}

#[test]
fn recognizes_exact_bounded_existential_theorems() {
    for script in [
        "(set-logic UFLIA)\
         (declare-fun P (Int) Bool)\
         (assert (exists ((x Int)) (and (<= 5 x) (<= x 3) (P x))))",
        BOUNDED_FALSE,
        "(set-logic UFLIA)\
         (declare-fun P (Int) Bool)\
         (assert (forall ((v Int)) (= (P v) (= v 200))))\
         (assert (not (exists ((x Int)) (and (<= 0 x) (<= x 300) (P x)))))",
    ] {
        assert!(evidence_for(&executor_for(script)).is_some(), "{script}");
    }

    let mut raw_positive = executor_for("(set-logic UFLIA)(declare-fun P (Int) Bool)");
    install_raw_pointwise_pair(&mut raw_positive, 1000, 0, 500, false, false, false);
    assert!(evidence_for(&raw_positive).is_some());

    let mut raw_negated = executor_for("(set-logic UFLIA)(declare-fun P (Int) Bool)");
    install_raw_pointwise_pair(&mut raw_negated, 200, 0, 300, true, false, false);
    assert!(evidence_for(&raw_negated).is_some());
}

#[test]
fn generic_text_boundary_publishes_all_checked_theorems() {
    for script in [
        "(set-logic NIA)\
         (assert (forall ((x Int)) (exists ((y Int)) (= (* y y) x))))\
         (check-sat)",
        "(set-logic LIA)\
         (assert (forall ((x Int)) (exists ((y Int))\
            (and (<= y x) (>= y (+ x 1))))))\
         (check-sat)",
        "(set-logic LIA)\
         (assert (not (forall ((x Int)) (exists ((y Int))\
            (and (> y x) (> y 5))))))\
         (check-sat)",
    ] {
        let commands = parse(script).expect("valid exact theorem script");
        let mut executor = Executor::new();
        assert_eq!(
            executor
                .execute_all(&commands)
                .expect("checked exact theorem must execute"),
            vec!["unsat"]
        );
        assert!(executor.last_command_unsat_was_exact_semantically_verified());
    }
}

#[test]
fn satisfiable_near_misses_and_private_operator_identity_decline() {
    for script in [
        "(set-logic LIA)\
         (assert (forall ((x Int)) (exists ((y Int)) (= y x))))",
        "(set-logic NIA)\
         (assert (forall ((x Int)) (exists ((y Int)) (= (* y y) (* x x)))))",
        "(set-logic LIA)\
         (assert (forall ((x Int)) (exists ((y Int))\
            (and (<= y x) (>= y x)))))",
        "(set-logic LIA)\
         (assert (not (forall ((x Int)) (exists ((y Int))\
            (and (> y x) (< y 5))))))",
        "(set-logic LIA)\
         (assert (forall ((x Int)) (exists ((y Int))\
            (and (> y x) (> y 5)))))",
        "(set-logic ALL)\
         (declare-fun * (Int Int) Int)\
         (assert (forall ((x Int)) (exists ((y Int)) (= (* y y) x))))",
        "(set-logic ALL)\
         (declare-fun < (Int Int) Bool)\
         (assert (not (forall ((x Int)) (exists ((y Int))\
            (and (< x y) (< 5 y))))))",
        "(set-logic ALL)\
         (declare-fun <= (Int Int) Bool)\
         (declare-fun P (Int) Bool)\
         (assert (exists ((x Int)) (and (<= 5 x) (<= x 3) (P x))))",
        "(set-logic ALL)\
         (declare-fun - (Int) Int)\
         (declare-fun P (Int) Bool)\
         (assert (exists ((x Int))\
            (and (<= (- 5) x) (<= x (- 7)) (P x))))",
    ] {
        let executor = executor_for(script);
        assert!(evidence_for(&executor).is_none(), "{script}");
    }
}

#[test]
fn bounded_polarity_flips_decline() {
    for script in [
        "(set-logic UFLIA)\
         (declare-fun P (Int) Bool)\
         (assert (exists ((x Int)) (and (<= 0 x) (<= x 3) (P x))))",
        "(set-logic UFLIA)\
         (declare-fun P (Int) Bool)\
         (assert (forall ((v Int)) (= (P v) (= v 2))))\
         (assert (exists ((x Int)) (and (<= 0 x) (<= x 3) (P x))))",
        "(set-logic UFLIA)\
         (declare-fun P (Int) Bool)\
         (assert (forall ((v Int)) (= (P v) (= v 5))))\
         (assert (not (exists ((x Int)) (and (<= 0 x) (<= x 3) (P x)))))",
        "(set-logic UFLIA)\
         (declare-fun P (Int) Bool)\
         (assert (not (exists ((x Int)) (and (<= 5 x) (<= x 3) (P x)))))",
    ] {
        assert!(evidence_for(&executor_for(script)).is_none(), "{script}");
    }

    let mut raw_positive = executor_for("(set-logic UFLIA)(declare-fun P (Int) Bool)");
    install_raw_pointwise_pair(&mut raw_positive, 2, 0, 3, false, false, false);
    assert!(evidence_for(&raw_positive).is_none());

    let mut raw_negated = executor_for("(set-logic UFLIA)(declare-fun P (Int) Bool)");
    install_raw_pointwise_pair(&mut raw_negated, 5, 0, 3, true, false, false);
    assert!(evidence_for(&raw_negated).is_none());
}

#[test]
fn bounded_shape_near_misses_decline() {
    for script in [
        "(set-logic UFLIA)\
         (declare-fun P (Int) Bool)\
         (declare-fun Q (Int) Bool)\
         (assert (forall ((v Int)) (= (P v) (= v 1000))))\
         (assert (exists ((x Int))\
            (and (<= 0 x) (<= x 500) (P x) (Q x))))",
        "(set-logic UFLIA)\
         (declare-fun P (Int) Bool)\
         (assert (exists ((x Int) (y Int))\
            (and (<= 5 x) (<= x 3) (P x))))",
        "(set-logic UFLRA)\
         (declare-fun P (Real) Bool)\
         (assert (exists ((x Real)) (and (<= 5.0 x) (<= x 3.0) (P x))))",
        "(set-logic UFLIA)\
         (declare-fun P (Int) Bool)\
         (assert (forall ((v Int)) (= (P v) (= v 1000))))\
         (assert (forall ((v Int)) (= (P v) (= v 1001))))\
         (assert (exists ((x Int)) (and (<= 0 x) (<= x 500) (P x))))",
    ] {
        assert!(evidence_for(&executor_for(script)).is_none(), "{script}");
    }
}

#[test]
fn raw_definition_requires_triggerless_exact_live_signature() {
    for (definition_trigger, existential_trigger) in [(true, false), (false, true)] {
        let mut executor = executor_for("(set-logic UFLIA)(declare-fun P (Int) Bool)");
        install_raw_pointwise_pair(
            &mut executor,
            1000,
            0,
            500,
            false,
            definition_trigger,
            existential_trigger,
        );
        assert!(evidence_for(&executor).is_none());
    }

    let mut wrong_signature = executor_for("(set-logic ALL)(declare-fun P (Int Int) Bool)");
    install_raw_pointwise_pair(&mut wrong_signature, 1000, 0, 500, false, false, false);
    assert!(evidence_for(&wrong_signature).is_none());
}

fn assert_evidence_stales(script: &str) {
    let mut forged = executor_for(script);
    let evidence = evidence_for(&forged).expect("expected exact UNSAT evidence");
    let sat = forged.ctx.terms.true_term();
    forged.ctx.assertions = vec![sat];
    assert!(!evidence.is_current(&forged));

    let mut epoch = executor_for(script);
    let evidence = evidence_for(&epoch).expect("expected exact UNSAT evidence");
    epoch.advance_query_authority_epoch();
    assert!(!evidence.is_current(&epoch));

    let mut source = executor_for(script);
    let evidence = evidence_for(&source).expect("expected exact UNSAT evidence");
    source
        .ctx
        .process_command(&Command::Push(1))
        .expect("push changes the source/scope stamp");
    assert!(!evidence.is_current(&source));

    let mut snapshot = executor_for(script);
    let evidence = evidence_for(&snapshot).expect("expected exact UNSAT evidence");
    let _ = snapshot.ctx.terms.mk_var("later", Sort::Int);
    assert!(!evidence.is_current(&snapshot));
}

#[test]
fn evidence_rejects_forged_roots_and_stale_epoch_source_and_snapshot() {
    assert_evidence_stales(
        "(set-logic LIA)\
         (assert (forall ((x Int)) (exists ((y Int))\
            (and (<= y x) (>= y (+ x 1))))))",
    );
    assert_evidence_stales(BOUNDED_FALSE);

    let mut reordered = executor_for(BOUNDED_FALSE);
    let evidence = evidence_for(&reordered).expect("expected bounded UNSAT evidence");
    reordered.ctx.assertions.reverse();
    assert!(!evidence.is_current(&reordered));
}
