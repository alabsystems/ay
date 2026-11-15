// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::cell::Cell;

fn boolean_child(f: &mut Fixture) -> (Proof, EqRes, TermId) {
    let set = f.roots.iter().copied().collect();
    let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
        .with_array_units(&f.units, &allow);
    cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
    let child = PropagationChainPlanner {
        terms: &mut f.terms,
    }
    .plan_derive_eq(&mut cx, f.scalar, f.stamp)
    .expect("source-derived canonical scalar child");
    let EqRes::Changed { to, .. } = child else {
        panic!("changed child")
    };
    assert!(matches!(f.terms.get(to), TermData::App(head, args)
        if head.name() == "=" && args.as_slice() == [f.high, f.payload]));
    authenticate(&f.terms, &f.roots, &cx.chain).unwrap();
    (cx.chain, child, to)
}

#[test]
fn array_duplicate_and_collapse_has_explicit_strict_contraction() {
    let mut f = Fixture::new(129);
    let (prefix, child, atom) = boolean_child(&mut f);
    let source = app(&mut f.terms, "and", &[f.scalar, f.scalar]);
    let set = f.roots.iter().copied().collect();
    let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
        .with_array_units(&f.units, &allow);
    cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
    cx.chain = prefix;
    let (equality, id) = PropagationChainPlanner {
        terms: &mut f.terms,
    }
    .plan_connective_reorder_fold(
        &mut cx,
        source,
        atom,
        &Symbol::named("and"),
        &[f.scalar, f.scalar],
        &[atom, atom],
        &[child, child],
    )
    .expect("bounded singleton collapse");
    assert_eq!(
        authenticate(&f.terms, &f.roots, &cx.chain)
            .unwrap()
            .clause(id),
        Some([equality].as_slice())
    );
    let contraction = cx
        .chain
        .steps
        .iter()
        .position(|step| {
            matches!(
                step,
                ProofStep::Step {
                    rule: AletheRule::Contraction,
                    ..
                }
            )
        })
        .unwrap();
    let mut wrong = cx.chain.clone();
    let ProofStep::Step { clause, .. } = &mut wrong.steps[contraction] else {
        unreachable!()
    };
    *clause = vec![f.terms.false_term()];
    assert!(authenticate(&f.terms, &f.roots, &wrong).is_err());
}

#[test]
fn array_duplicate_and_refusals_preserve_prefix_and_do_not_refund_work() {
    let mut f = Fixture::new(8);
    let (prefix, child, atom) = boolean_child(&mut f);
    let source = app(&mut f.terms, "and", &[f.scalar, f.scalar]);
    let set = f.roots.iter().copied().collect();
    // Change 6 used to be a 65-wide collapse, refused by the bridge's
    // 64-argument cap; the cap is gone, so the wide case is the positive
    // test below.
    for change in [0, 1, 2, 3, 4, 5, 7] {
        let charged = Cell::new((0usize, 0usize, 0usize));
        let progress = |work, bytes| {
            charged.set((charged.get().0 + 1, work, bytes));
            change != 3
        };
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
            .with_array_units(&f.units, &progress);
        cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
        cx.chain = prefix.clone();
        match change {
            0 => cx.scalar_equality_mode = ScalarEqualityMode::Legacy,
            1 => cx.array_units = &[],
            2 => cx.array_progress = None,
            4 => cx.budget = 0,
            // Callback/local precharge = 48 + ceil(4608/64) = 120.
            // The existing equivalence primitive needs five more units.
            5 => cx.budget = 124,
            _ => {}
        }
        let (term, args, rewritten, children) =
            (source, vec![f.scalar; 2], vec![atom; 2], vec![child; 2]);
        let target = if change == 7 { f.guard } else { atom };
        assert!(PropagationChainPlanner {
            terms: &mut f.terms
        }
        .plan_connective_reorder_fold(
            &mut cx,
            term,
            target,
            &Symbol::named("and"),
            &args,
            &rewritten,
            &children
        )
        .is_none());
        assert_eq!(cx.chain, prefix);
        assert!(cx.eq_memo.is_empty() && cx.clause_memo.is_empty());
        if change == 5 {
            assert_eq!(cx.budget, 4);
        }
    }
    let mut retry = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
        .with_array_units(&f.units, &allow);
    retry.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
    retry.chain = prefix;
    retry.budget = 125;
    let (_, id) = PropagationChainPlanner {
        terms: &mut f.terms,
    }
    .plan_connective_reorder_fold(
        &mut retry,
        source,
        atom,
        &Symbol::named("and"),
        &[f.scalar; 2],
        &[atom; 2],
        &[child; 2],
    )
    .unwrap();
    assert_eq!(retry.budget, 0);
    assert!(authenticate(&f.terms, &f.roots, &retry.chain)
        .unwrap()
        .clause(id)
        .is_some());
}

/// A 1,000-wide duplicate `and` collapses with no arity cap: one `and_neg`
/// and one `contraction`, a constant number of steps however wide.
#[test]
fn a_wide_array_duplicate_and_collapses_without_an_arity_cap() {
    let mut f = Fixture::new(8);
    let (prefix, child, atom) = boolean_child(&mut f);
    let wide_args = vec![f.scalar; 1_000];
    let wide = app(&mut f.terms, "and", &wide_args);
    let set = f.roots.iter().copied().collect();
    let mut wide_cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
        .with_array_units(&f.units, &allow);
    wide_cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
    let prefix_steps = prefix.steps.len();
    wide_cx.chain = prefix;
    let (_, wide_id) = PropagationChainPlanner {
        terms: &mut f.terms,
    }
    .plan_connective_reorder_fold(
        &mut wide_cx,
        wide,
        atom,
        &Symbol::named("and"),
        &wide_args,
        &vec![atom; 1_000],
        &vec![child; 1_000],
    )
    .expect("a 1,000-wide duplicate collapse bridges with no arity cap");
    assert!(
        wide_cx.chain.steps.len() - prefix_steps < 32,
        "the collapse is a constant number of steps, not one per argument"
    );
    assert!(authenticate(&f.terms, &f.roots, &wide_cx.chain)
        .unwrap()
        .clause(wide_id)
        .is_some());
}

/// The OR reorder bridge runs in the array lane's canonical retry (charged to
/// its shared progress callback) and in the no-array scalar lane (charged to
/// the plan budget alone, like AND), never in the array lane's positional
/// first attempt, and only for the exact argument set.
#[test]
fn canonical_or_reorder_skips_the_positional_array_attempt_and_needs_the_exact_argument_set() {
    let mut f = Fixture::new(8);
    let (prefix, child, atom) = boolean_child(&mut f);
    let other = f.terms.mk_not_raw(f.guard);
    let source = app(&mut f.terms, "or", &[f.scalar, other]);
    let canonical = f.terms.mk_or(vec![atom, other]);
    assert!(matches!(f.terms.get(canonical), TermData::App(head, args)
        if head.name() == "or" && args.as_slice() == [other, atom]));
    let wrong = app(&mut f.terms, "or", &[other, f.activation]);
    let oversized_args = vec![f.scalar; 65];
    let oversized = app(&mut f.terms, "or", &oversized_args);
    let set = f.roots.iter().copied().collect();
    for change in 0..8 {
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
            .with_array_units(&f.units, &allow);
        cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
        cx.chain = prefix.clone();
        match change {
            0 => cx.scalar_equality_mode = ScalarEqualityMode::Legacy,
            1 => cx.array_units = &[],
            2 => cx.array_progress = None,
            // Shared/local precharge144 + set-reorder16 consumes160;
            // fail at the equivalence's five-unit charge after emitting both
            // implications, then remove that entire suffix without refund.
            5 => cx.budget = 164,
            _ => {}
        }
        let target = if change == 3 { wrong } else { canonical };
        let input = if change == 6 { oversized } else { source };
        let args = if change == 6 {
            oversized_args.as_slice()
        } else {
            &[f.scalar, other]
        };
        let children = if change == 7 {
            &[child][..]
        } else {
            &[child, EqRes::Unchanged][..]
        };
        let result = PropagationChainPlanner {
            terms: &mut f.terms,
        }
        .plan_connective_reorder_fold(
            &mut cx,
            input,
            target,
            &Symbol::named("or"),
            args,
            &[atom, other],
            children,
        );
        if change == 4 || change == 1 {
            // 4: the array retry; 1: no array units, the scalar lane.
            let (equality, id) = result.expect("exact canonical OR permutation");
            assert_eq!(
                authenticate(&f.terms, &f.roots, &cx.chain)
                    .unwrap()
                    .clause(id),
                Some([equality].as_slice())
            );
        } else {
            assert!(result.is_none());
            assert_eq!(cx.chain, prefix);
            if change == 5 {
                assert_eq!(cx.budget, 4);
            }
            if change >= 6 {
                assert_eq!(cx.budget, PLAN_NODE_BUDGET);
            }
        }
    }
}

#[test]
fn legacy_array_and_keeps_positional_replay_before_canonical_retry() {
    let mut f = Fixture::new(8);
    let (prefix, child, atom) = boolean_child(&mut f);
    let other = f.activation;
    let source = app(&mut f.terms, "and", &[f.scalar, other]);
    let canonical = f.terms.mk_and(vec![atom, other]);
    assert!(matches!(f.terms.get(canonical), TermData::App(head, args)
        if head.name() == "and" && args.as_slice() == [other, atom]));
    let set = f.roots.iter().copied().collect();
    for lane in 0..3 {
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
            .with_array_units(&f.units, &allow);
        cx.chain = prefix.clone();
        if lane == 1 {
            cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
        } else if lane == 2 {
            // The generic no-array channel still needs the checked AND bridge.
            cx.array_units = &[];
            cx.array_progress = None;
        }
        let result = PropagationChainPlanner {
            terms: &mut f.terms,
        }
        .plan_connective_reorder_fold(
            &mut cx,
            source,
            canonical,
            &Symbol::named("and"),
            &[f.scalar, other],
            &[atom, other],
            &[child, EqRes::Unchanged],
        );
        if lane == 0 {
            assert!(
                result.is_none(),
                "legacy array replay must reach raw fallback"
            );
            assert_eq!(cx.chain, prefix);
            assert_eq!(cx.budget, PLAN_NODE_BUDGET);
        } else {
            let (equality, id) = result.expect("exact canonical AND permutation");
            assert_eq!(
                authenticate(&f.terms, &f.roots, &cx.chain)
                    .unwrap()
                    .clause(id),
                Some([equality].as_slice())
            );
        }
    }
}
