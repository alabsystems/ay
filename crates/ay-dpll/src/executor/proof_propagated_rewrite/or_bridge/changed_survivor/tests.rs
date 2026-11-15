// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod fixtures;
use fixtures::Fixture;

#[test]
fn actual_recorded_scalar_parent_and_projected_guard_are_strictly_derived() {
    let mut fixture = Fixture::recorded();
    assert!(!fixture.records.contains_key(&fixture.target));
    for target in [fixture.after, fixture.target] {
        let (proof, conclusion) = fixture
            .plan(target, PLAN_NODE_BUDGET)
            .expect("derive exact recorded parent before projection");
        fixture.authenticate(&proof, conclusion, target);
    }
}

#[test]
fn changed_survivor_requires_original_licenses_current_stamps_and_exact_target() {
    for mutation in 0..3 {
        let mut fixture = Fixture::recorded();
        let target = match mutation {
            0 => {
                fixture.originals.remove(0);
                fixture.target
            }
            1 => {
                for (_, _, stamp) in fixture.entries.values_mut() {
                    *stamp = u32::MAX;
                }
                fixture.target
            }
            _ => fixture.terms.mk_var("not the recorded guard", Sort::Bool),
        };
        assert!(fixture.plan(target, PLAN_NODE_BUDGET).is_none());
    }
}

#[test]
fn changed_survivor_refusal_rolls_back_both_attempts_without_refunding_work() {
    let mut fixture = Fixture::recorded();
    let wrong = fixture.terms.mk_var("wrong after", Sort::Bool);
    let source_set = fixture.originals.iter().copied().collect();
    let mut cx = PlanCx::new(
        &source_set,
        &fixture.originals,
        &fixture.records,
        &fixture.entries,
        &[],
        true,
    );
    let before_id = cx.chain.add_assume(fixture.before, None);
    let mark = cx.mark();
    let mut planner = PropagationChainPlanner {
        terms: &mut fixture.terms,
    };
    assert!(planner
        .plan_or_elimination_bridge(&mut cx, fixture.before, before_id, wrong, 1)
        .is_none());
    assert_eq!(cx.mark(), mark);
    assert!(
        cx.budget < PLAN_NODE_BUDGET,
        "failed legacy and changed-survivor work remains spent"
    );
    assert!(cx.clause_memo.values().all(|id| (id.0 as usize) < mark));
    assert!(cx
        .eq_memo
        .values()
        .all(|value| !matches!(value, Some(EqRes::Changed { id, .. }) if id.0 as usize >= mark)));
    assert!(cx.in_progress.is_empty() && cx.eq_in_progress.is_empty());

    cx.budget = 0;
    assert!(planner
        .plan_or_elimination_bridge(&mut cx, fixture.before, before_id, fixture.after, 1)
        .is_none());
    assert_eq!(cx.mark(), mark);
    assert_eq!(cx.budget, 0);
    drop(planner);
    drop(cx);
    let target = fixture.target;
    let (proof, conclusion) = fixture
        .plan(target, PLAN_NODE_BUDGET)
        .expect("fresh allowance replays");
    fixture.authenticate(&proof, conclusion, target);
}

#[test]
fn changed_survivor_fanout_is_refused_before_new_walk_or_proof_growth() {
    let mut terms = TermStore::new();
    let args: Vec<_> = (0..=MAX_CHANGED_SURVIVOR_ARGS)
        .map(|i| terms.mk_var(&format!("wide{i}"), Sort::Bool))
        .collect();
    let before = terms.mk_app(Symbol::named("or"), &args, Sort::Bool);
    let roots = [before];
    let source_set = roots.into_iter().collect();
    let records = HashMap::default();
    let entries = HashMap::default();
    let mut cx = PlanCx::new(&source_set, &roots, &records, &entries, &[], true);
    let before_id = cx.chain.add_assume(before, None);
    let mark = cx.mark();
    assert!(PropagationChainPlanner { terms: &mut terms }
        .plan_changed_or_survivor(&mut cx, before, before_id, args[0], 1)
        .is_none());
    assert_eq!(cx.mark(), mark);
    assert_eq!(cx.budget, PLAN_NODE_BUDGET);
    assert!(cx.eq_memo.is_empty());
}

#[test]
fn non_and_recorded_parent_and_unlicensed_record_cycles_cannot_project_units() {
    for cyclic in [false, true] {
        let mut terms = TermStore::new();
        let source = terms.mk_var("source", Sort::Bool);
        let target = terms.mk_var("target", Sort::Bool);
        let other = terms.mk_var("other", Sort::Bool);
        let after = terms.mk_app(
            Symbol::named(if cyclic { "and" } else { "or" }),
            [target, other],
            Sort::Bool,
        );
        let license = terms.mk_app(Symbol::named("="), [source, after], Sort::Bool);
        let roots = if cyclic {
            Vec::new()
        } else {
            vec![source, license]
        };
        let source_set = roots.iter().copied().collect();
        let mut records = HashMap::from_iter([(after, (source, 1))]);
        let entries = HashMap::from_iter([(source, (after, license, 1))]);
        if cyclic {
            records.insert(source, (after, 1));
        }
        let mut cx = PlanCx::new(&source_set, &roots, &records, &entries, &[], true);
        assert!(PropagationChainPlanner { terms: &mut terms }
            .plan_derive_clause(&mut cx, target)
            .is_none());
        assert!(cx.in_progress.is_empty() && cx.eq_in_progress.is_empty());
        cx.rollback(0);
        assert!(cx.chain.steps.is_empty());
    }
}

/// Neither connective bridges a node whose arguments did not change (the
/// positional rebuild IS the node), and AND never bridges to a different
/// argument set.
#[test]
fn exact_reorder_needs_a_changed_argument_and_the_exact_argument_set() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let empty = HashMap::default();
    let entries = HashMap::default();
    let source_set = HashSet::default();
    let mut cx = PlanCx::new(&source_set, &[], &empty, &entries, &[], true);
    let symbol = Symbol::named("or");
    let original = terms.mk_app(symbol.clone(), [b, a], Sort::Bool);
    let canonical = terms.mk_or(vec![a, b]);
    assert!(PropagationChainPlanner { terms: &mut terms }
        .plan_connective_reorder_fold(
            &mut cx,
            original,
            canonical,
            &symbol,
            &[b, a],
            &[b, a],
            &[EqRes::Unchanged, EqRes::Unchanged]
        )
        .is_none());
    let symbol = Symbol::named("and");
    let original = terms.mk_app(symbol.clone(), [b, a], Sort::Bool);
    let forged = terms.mk_and(vec![a, c]);
    assert!(PropagationChainPlanner { terms: &mut terms }
        .plan_connective_reorder_fold(
            &mut cx,
            original,
            forged,
            &symbol,
            &[b, a],
            &[b, a],
            &[EqRes::Unchanged, EqRes::Unchanged]
        )
        .is_none());
    assert!(cx.chain.steps.is_empty());
}
