// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_frontend::{parse, Command};

fn interval_context(gap: i64) -> (Context, TermId) {
    let mut ctx = Context::new();
    let x = ctx.terms.mk_fresh_named_var("x", Sort::Int);
    let y = ctx.terms.mk_var("y", Sort::Int);
    let upper = if gap == 0 {
        y
    } else {
        let gap = ctx.terms.mk_int(BigInt::from(gap));
        ctx.terms.mk_add(vec![y, gap])
    };
    let lower_bound = ctx.terms.mk_gt(x, y);
    let upper_bound = ctx.terms.mk_lt(x, upper);
    let body = ctx.terms.mk_and(vec![lower_bound, upper_bound]);
    let root = ctx
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], body);
    ctx.assertions.push(root);
    (ctx, root)
}

fn evidence_for_test(executor: &Executor) -> Option<ExactExistsDecision> {
    let permit = executor.detached_authored_plain_hard_permit_for_test()?;
    let truth = check_constant_truth(&executor.ctx, &executor.ctx.assertions)?;
    let common = CheckedExactExistsCommon {
        permit,
        term_snapshot: executor.ctx.terms.snapshot_stamp(),
    };
    Some(if truth {
        ExactExistsDecision::Sat(CheckedExactExistsSat(common))
    } else {
        ExactExistsDecision::Unsat(CheckedExactExistsUnsat(common))
    })
}

#[test]
fn integer_gap_boundary_is_exact() {
    let (gap_one, _) = interval_context(1);
    assert_eq!(
        check_constant_truth(&gap_one, &gap_one.assertions),
        Some(false)
    );

    let (gap_two, _) = interval_context(2);
    assert_eq!(
        check_constant_truth(&gap_two, &gap_two.assertions),
        Some(true)
    );

    let (gap_ten, _) = interval_context(10);
    assert_eq!(
        check_constant_truth(&gap_ten, &gap_ten.assertions),
        Some(true)
    );

    // Raw `>` nodes are accepted with the same orientation discipline;
    // the ordinary builders canonicalize them to `<`, so construct this
    // spelling explicitly to cover the checker arm.
    let mut greater = Context::new();
    let x = greater.terms.mk_fresh_named_var("x", Sort::Int);
    let y = greater.terms.mk_var("y", Sort::Int);
    let two = greater.terms.mk_int(BigInt::from(2));
    let upper = greater.terms.mk_add(vec![y, two]);
    let lower = greater
        .terms
        .mk_app(Symbol::named(">"), vec![x, y], Sort::Bool);
    let upper = greater
        .terms
        .mk_app(Symbol::named(">"), vec![upper, x], Sort::Bool);
    let body = greater.terms.mk_and(vec![lower, upper]);
    let root = greater
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], body);
    greater.assertions.push(root);
    assert_eq!(
        check_constant_truth(&greater, &greater.assertions),
        Some(true)
    );
}

#[test]
fn extra_roots_and_triggers_decline() {
    let (mut extra, _root) = interval_context(2);
    extra.assertions.push(extra.terms.true_term());
    assert_eq!(check_constant_truth(&extra, &extra.assertions), None);

    let (mut triggered, root) = interval_context(2);
    let TermData::Exists(vars, body, _) = triggered.terms.get(root).clone() else {
        panic!("interval root is existential");
    };
    let triggered_root = triggered
        .terms
        .mk_exists_with_triggers(vars, body, vec![vec![body]]);
    triggered.assertions = vec![triggered_root];
    assert_eq!(
        check_constant_truth(&triggered, &triggered.assertions),
        None
    );
}

#[test]
fn affine_mismatch_declines() {
    let mut ctx = Context::new();
    let x = ctx.terms.mk_fresh_named_var("x", Sort::Int);
    let y = ctx.terms.mk_var("y", Sort::Int);
    let z = ctx.terms.mk_var("z", Sort::Int);
    let one = ctx.terms.mk_int(BigInt::from(1));
    let upper = ctx.terms.mk_add(vec![z, one]);
    let lower = ctx.terms.mk_gt(x, y);
    let upper = ctx.terms.mk_lt(x, upper);
    let body = ctx.terms.mk_and(vec![lower, upper]);
    let root = ctx
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], body);
    ctx.assertions.push(root);
    assert_eq!(check_constant_truth(&ctx, &ctx.assertions), None);
}

#[test]
fn ambiguous_binder_identity_declines() {
    let mut ctx = Context::new();
    let bound = ctx.terms.mk_fresh_named_var("x", Sort::Int);
    let same_name_free = ctx.terms.mk_fresh_named_var("x", Sort::Int);
    let lower = ctx.terms.mk_lt(same_name_free, bound);
    let upper = ctx.terms.mk_lt(bound, same_name_free);
    let body = ctx.terms.mk_and(vec![lower, upper]);
    let root = ctx
        .terms
        .mk_exists(vec![("x".to_string(), Sort::Int)], body);
    ctx.assertions.push(root);
    assert_eq!(check_constant_truth(&ctx, &ctx.assertions), None);
}

#[test]
fn malformed_operator_arity_and_sort_decline() {
    let (mut wrong_arity, _) = interval_context(2);
    let x = wrong_arity.terms.mk_fresh_named_var("q", Sort::Int);
    let malformed = wrong_arity
        .terms
        .mk_app(Symbol::named("+"), vec![x], Sort::Int);
    let lt = wrong_arity.terms.mk_lt(x, malformed);
    let gt = wrong_arity.terms.mk_gt(x, malformed);
    let body = wrong_arity.terms.mk_and(vec![lt, gt]);
    let root = wrong_arity
        .terms
        .mk_exists(vec![("q".to_string(), Sort::Int)], body);
    wrong_arity.assertions = vec![root];
    assert_eq!(
        check_constant_truth(&wrong_arity, &wrong_arity.assertions),
        None
    );

    let (mut wrong_sort, _) = interval_context(2);
    let x = wrong_sort.terms.mk_fresh_named_var("q", Sort::Int);
    let y = wrong_sort.terms.mk_var("r", Sort::Int);
    let bad_add = wrong_sort
        .terms
        .mk_app(Symbol::named("+"), vec![y, y], Sort::Bool);
    let lower = wrong_sort
        .terms
        .mk_app(Symbol::named("<"), vec![y, x], Sort::Bool);
    let upper = wrong_sort
        .terms
        .mk_app(Symbol::named("<"), vec![x, bad_add], Sort::Bool);
    let body = wrong_sort.terms.mk_and(vec![lower, upper]);
    let root = wrong_sort
        .terms
        .mk_exists(vec![("q".to_string(), Sort::Int)], body);
    wrong_sort.assertions = vec![root];
    assert_eq!(
        check_constant_truth(&wrong_sort, &wrong_sort.assertions),
        None
    );
}

#[test]
fn declared_operator_collision_uses_private_identity_and_declines() {
    let mut executor = Executor::new();
    let commands = parse(
        "(set-logic ALL)\
         (declare-const y Int)\
         (declare-fun + (Int Int) Int)\
         (assert (exists ((x Int)) (and (< y x) (< x (+ y 2)))))",
    )
    .expect("valid operator-collision script");
    for command in &commands {
        executor
            .context_mut_internal()
            .process_command(command)
            .expect("operator-collision command elaborates");
    }
    assert_eq!(
        check_constant_truth(&executor.ctx, &executor.ctx.assertions),
        None,
        "a declared `+` application has a private core identity and is not arithmetic authority"
    );
}

#[test]
fn evidence_rejects_stale_epoch_source_roots_and_term_snapshot() {
    let (ctx, _) = interval_context(2);
    let mut epoch = Executor::new();
    epoch.ctx = ctx.clone();
    let ExactExistsDecision::Sat(evidence) = evidence_for_test(&epoch).expect("evidence") else {
        panic!("expected SAT evidence");
    };
    epoch.advance_query_authority_epoch();
    assert!(!evidence.is_current(&epoch));

    let mut source = Executor::new();
    source.ctx = ctx.clone();
    let ExactExistsDecision::Sat(evidence) = evidence_for_test(&source).expect("evidence") else {
        panic!("expected SAT evidence");
    };
    source
        .ctx
        .process_command(&Command::Push(1))
        .expect("push mutates source epoch");
    assert!(!evidence.is_current(&source));

    let mut roots = Executor::new();
    roots.ctx = ctx.clone();
    let ExactExistsDecision::Sat(evidence) = evidence_for_test(&roots).expect("evidence") else {
        panic!("expected SAT evidence");
    };
    roots.ctx.assertions[0] = roots.ctx.terms.true_term();
    assert!(!evidence.is_current(&roots));

    let mut snapshot = Executor::new();
    snapshot.ctx = ctx;
    let ExactExistsDecision::Sat(evidence) = evidence_for_test(&snapshot).expect("evidence") else {
        panic!("expected SAT evidence");
    };
    let _ = snapshot.ctx.terms.mk_var("later", Sort::Int);
    assert!(!evidence.is_current(&snapshot));
}
