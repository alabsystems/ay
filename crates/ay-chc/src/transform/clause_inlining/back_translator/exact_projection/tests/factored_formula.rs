// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Closed conjuncts do not multiply the branches needed to eliminate locals.

use super::*;

#[test]
fn sixteen_retained_disjunctions_and_a_local_alias_need_only_one_branch() {
    let (guards, keep) = retained_formula::disjunctions(16);
    let local = var("old", 2);
    let formula = op(ChcOp::And, vec![guards, eq(expr(&keep[0]), expr(&local))]);
    let mut scope = Scope::new(
        Limits {
            branches: 1,
            ..Limits::default()
        },
        &|| true,
    );
    let Projection::Closed(projected) = run(&formula, &keep, &mut scope) else {
        panic!("retained disjunctions must not consume residual branch credit")
    };
    assert_eq!(scope.remaining.branches, 0);
    assert_eq!(shift::operation_count(&projected, ChcOp::Or), 16);
    assert!(projected.vars().iter().all(|v| keep.contains(v)));
}

fn image_with_retained_guards() -> (ChcExpr, Vec<ChcVar>) {
    let a = var("a", 2);
    let b = var("b", 2);
    let local = var("local", 2);
    let guard = op(
        ChcOp::Or,
        vec![
            eq(expr(&a), ChcExpr::BitVec(0, 2)),
            eq(expr(&b), ChcExpr::BitVec(1, 2)),
        ],
    );
    let mut atoms = vec![guard; 16];
    atoms.push(eq(expr(&a), quotient(&local, 2)));
    (op(ChcOp::And, atoms), vec![a, b])
}

#[test]
fn factored_projection_matches_every_original_existential_assignment() {
    let (formula, keep) = image_with_retained_guards();
    let projected = closed(&formula, &keep);
    assert_eq!(shift::operation_count(&projected, ChcOp::Or), 16);
    let mut accepted = 0;
    for a in 0..4 {
        for b in 0..4 {
            let expected = (0..4)
                .any(|local| oracle::truth(&formula, &[("a", a), ("b", b), ("local", local)]));
            accepted += usize::from(expected);
            assert_eq!(oracle::truth(&projected, &[("a", a), ("b", b)]), expected);
        }
    }
    assert_eq!(
        accepted, 5,
        "neither the image nor its retained guards may disappear"
    );
}

#[test]
fn a_mixed_disjunction_is_never_factored_into_a_partial_local_image() {
    let (guards, keep) = retained_formula::disjunctions(16);
    let local = var("local", 2);
    let mixed = op(
        ChcOp::Or,
        vec![
            eq(expr(&keep[0]), quotient(&local, 2)),
            op(ChcOp::BvULt, vec![expr(&local), expr(&keep[0])]),
        ],
    );
    declined(&op(ChcOp::And, vec![guards.clone(), mixed.clone()]), &keep);
    // A local-dependent OR stays whole and can legitimately exhaust branches.
    assert!(!matches!(
        run(
            &op(ChcOp::Or, vec![guards, mixed]),
            &keep,
            &mut Scope::new(Limits::default(), &|| true)
        ),
        Projection::Closed(_)
    ));
}

#[test]
fn mixed_local_and_kept_arms_preserve_existential_disjunction_semantics() {
    let a = var("a", 2);
    let b = var("b", 2);
    let local = var("local", 2);
    let guard = op(ChcOp::BvULt, vec![expr(&b), ChcExpr::BitVec(2, 2)]);
    let mixed = op(
        ChcOp::Or,
        vec![
            eq(expr(&a), ChcExpr::BitVec(3, 2)),
            eq(expr(&a), quotient(&local, 2)),
        ],
    );
    let formula = op(ChcOp::And, vec![guard, mixed]);
    let projected = closed(&formula, &[a, b]);
    for a in 0..4 {
        for b in 0..4 {
            let expected = (0..4)
                .any(|local| oracle::truth(&formula, &[("a", a), ("b", b), ("local", local)]));
            assert_eq!(oracle::truth(&projected, &[("a", a), ("b", b)]), expected);
        }
    }
}

#[test]
fn typed_closed_false_still_discharges_an_unsupported_local_residual() {
    let a = var("a", 2);
    let local = var("local", 2);
    let guard = op(
        ChcOp::Or,
        vec![
            eq(expr(&a), ChcExpr::BitVec(0, 2)),
            eq(expr(&a), ChcExpr::BitVec(1, 2)),
        ],
    );
    let unsupported = op(ChcOp::BvULt, vec![expr(&local), expr(&a)]);
    for atoms in [
        vec![guard.clone(), ChcExpr::Bool(false), unsupported.clone()],
        vec![unsupported, ChcExpr::Bool(false), guard],
    ] {
        let projected = closed(&op(ChcOp::And, atoms), std::slice::from_ref(&a));
        for a in 0..4 {
            assert!(!oracle::truth(&projected, &[("a", a)]));
        }
    }
    let malformed = op(ChcOp::BvAdd, vec![expr(&local)]);
    declined(
        &op(
            ChcOp::And,
            vec![ChcExpr::Bool(false), eq(expr(&a), malformed)],
        ),
        &[a],
    );
}

#[test]
fn factoring_retains_one_original_scope_for_work_growth_and_stop() {
    let a = var("a", 2);
    let local = var("local", 2);
    let guard = op(
        ChcOp::Or,
        vec![
            eq(expr(&a), ChcExpr::BitVec(0, 2)),
            eq(expr(&a), ChcExpr::BitVec(1, 2)),
        ],
    );
    let formula = op(ChcOp::And, vec![guard, eq(expr(&a), quotient(&local, 2))]);
    resources::assert_poll_boundaries(&formula, std::slice::from_ref(&a));
    resources::assert_numeric_boundaries(&formula, std::slice::from_ref(&a));
}

#[test]
fn original_callback_can_stop_at_factored_publication_after_tls_replacement() {
    use ay_core::resource::enter_check_stop;
    use std::sync::atomic::{AtomicUsize, Ordering};

    let (formula, keep) = image_with_retained_guards();
    let count = Arc::new(AtomicUsize::new(0));
    let stop_at = Arc::new(AtomicUsize::new(usize::MAX));
    let seen = Arc::clone(&count);
    let limit = Arc::clone(&stop_at);
    let entered = enter_check_stop(Arc::new(move || {
        seen.fetch_add(1, Ordering::SeqCst) + 1 == limit.load(Ordering::SeqCst)
    }));
    let mut baseline = Scope::new(Limits::default(), &|| true);
    let mut stopped = Scope::new(Limits::default(), &|| true);
    drop(entered);
    let _replacement = enter_check_stop(Arc::new(|| false));
    assert!(matches!(
        run(&formula, &keep, &mut baseline),
        Projection::Closed(_)
    ));
    let total = count.swap(0, Ordering::SeqCst);
    stop_at.store(total, Ordering::SeqCst);
    assert!(matches!(
        run(&formula, &keep, &mut stopped),
        Projection::Stopped
    ));
    assert_eq!(count.load(Ordering::SeqCst), total);
    stop_at.store(usize::MAX, Ordering::SeqCst);
    assert_eq!(stopped.poll(), Err(Failure::Stopped));
    assert_eq!(count.load(Ordering::SeqCst), total);
}

#[test]
fn factoring_cannot_spend_a_replacement_trees_work_allowance() {
    use ay_core::resource::{ChildSpec, Guard, NodeLabel};

    let (formula, keep) = image_with_retained_guards();
    let full = Limits::default();
    let mut baseline = Scope::new(full, &|| true);
    assert!(matches!(
        run(&formula, &keep, &mut baseline),
        Projection::Closed(_)
    ));
    let work = full.work - baseline.remaining.work;
    let original =
        Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some((work - 1) as u64)));
    let entered = original.enter();
    let mut scope = Scope::new(full, &|| true);
    drop(entered);
    let replacement = Guard::new();
    let _entered = replacement.enter();
    assert!(matches!(
        run(&formula, &keep, &mut scope),
        Projection::Stopped
    ));
    assert!(original.poll().is_some());
    assert!(replacement.poll().is_none());
    assert_eq!(scope.work(0), Err(Failure::Stopped));
}

#[test]
fn realloc_successor_alias_preserves_the_stack_fact_during_reconstruction() {
    // Original bb5 line529 passes all seven stack bases but renames the
    // unconstrained region43 value to region43_out. It becomes a local only
    // after applying the predecessor interpretation, which retains 15 ORs.
    let (fact, mut predecessor_vars) = retained_formula::realloc_fact_shape();
    let old = var("region43_old", 32);
    let next = var("region43_out", 32);
    predecessor_vars.push(old.clone());
    let mut keep = predecessor_vars.clone();
    *keep.last_mut().unwrap() = next.clone();
    let mut problem = crate::ChcProblem::new();
    let predecessor = problem.declare_predicate(
        "bb27",
        predecessor_vars.iter().map(|v| v.sort.clone()).collect(),
    );
    let successor = problem.declare_predicate("bb5", keep.iter().map(|v| v.sort.clone()).collect());
    let mut model = crate::InvariantModel::new();
    model.set(
        predecessor,
        crate::PredicateInterpretation::new(predecessor_vars.clone(), fact),
    );
    let clause = crate::HornClause::new(
        crate::ClauseBody::new(
            vec![(predecessor, predecessor_vars.iter().map(expr).collect())],
            Some(eq(expr(&next), expr(&old))),
        ),
        crate::ClauseHead::Predicate(successor, keep.iter().map(expr).collect()),
    );
    let reconstructed =
        super::super::super::InliningBackTranslator::synthesize_interpretation(&clause, &model)
            .expect("a successor alias must not multiply already retained stack constraints");
    assert_eq!(reconstructed.vars, keep);
    assert_eq!(
        shift::operation_count(&reconstructed.formula, ChcOp::Or),
        15
    );
    assert!(reconstructed
        .formula
        .vars()
        .iter()
        .all(|v| keep.contains(v)));
}
