// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod fixtures;
use fixtures::*;

#[test]
fn matching_key_select_replays_from_the_exact_original_array_definition() {
    for width in [8, 136] {
        let mut f = Fixture::new(width);
        let read = f.read(f.variable, f.key);
        let before = raw_eq(&mut f.terms, read, f.right);
        let after = f.terms.mk_eq_coerce_no_ite_expand(f.left, f.right);
        f.roots.push(before);
        f.records.insert(after, (before, 1));
        let (proof, conclusion) = f.plan(after).expect("matching-key array fold");
        assert!(proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
                ..
            }
        )));
        assert_source(&f.terms, &f.roots, &proof, conclusion, after);
        let mut missing_source = f.roots.clone();
        missing_source.remove(0);
        assert!(authenticate(&f.terms, &missing_source, &proof).is_err());
    }
}

#[test]
fn common_store_equality_uses_array_injectivity_and_euf_reverse_not_boolean_guessing() {
    let mut f = Fixture::new(136);
    let second = f.store(f.base, f.key, f.right);
    let before = raw_eq(&mut f.terms, f.variable, second);
    let after = f.terms.mk_eq_coerce_no_ite_expand(f.left, f.right);
    f.roots.push(before);
    f.records.insert(after, (before, 1));
    let (proof, conclusion) = f.plan(after).expect("exact common-store equality");
    for expected in [
        TheoryLemmaKind::ArrayRowChain,
        TheoryLemmaKind::EufCongruent,
    ] {
        assert!(proof.steps.iter().any(|step| matches!(step,
            ProofStep::TheoryLemma { kind, .. } if *kind == expected)));
    }
    assert_source(&f.terms, &f.roots, &proof, conclusion, after);
    let mut mutation = proof.clone();
    let false_term = f.terms.false_term();
    let step = mutation
        .steps
        .iter_mut()
        .find(|step| {
            matches!(
                step,
                ProofStep::TheoryLemma {
                    kind: TheoryLemmaKind::ArrayRowChain,
                    ..
                }
            )
        })
        .expect("forward array implication");
    let ProofStep::TheoryLemma { clause, .. } = step else {
        unreachable!()
    };
    clause[1] = false_term;
    assert!(authenticate(&f.terms, &f.roots, &mutation).is_err());
}

#[test]
fn raw_ite_payload_retry_matches_only_the_recorded_supported_spelling() {
    let mut f = Fixture::new(8);
    let guard = f.terms.mk_var("guard", Sort::Bool);
    let conditional = f.terms.mk_ite_raw(guard, f.left, f.right);
    f.replacement = f.store(f.base, f.key, conditional);
    f.source = raw_eq(&mut f.terms, f.variable, f.replacement);
    f.roots[0] = f.source;
    f.entries.insert(f.variable, (f.replacement, f.source, 1));
    let second = f.store(f.base, f.key, f.left);
    let before = raw_eq(&mut f.terms, f.variable, second);
    let exact = f.terms.mk_eq_coerce_no_ite_expand(conditional, f.left);
    let expanded = f.terms.mk_eq_coerce(conditional, f.left);
    assert_ne!(
        exact, expanded,
        "exercise the actual producer spelling difference"
    );
    f.roots.push(before);
    f.records.insert(exact, (before, 1));
    let (proof, conclusion) = f.plan(exact).expect("unexpanded payload equality");
    assert_source(&f.terms, &f.roots, &proof, conclusion, exact);

    // This slice does not add the separate ITE-to-disjunction proof bridge.
    f.records.insert(expanded, (before, 1));
    assert!(f.plan(expanded).is_none());
    let wrong = raw_eq(&mut f.terms, conditional, f.right);
    f.records.insert(wrong, (before, 1));
    assert!(
        f.plan(wrong).is_none(),
        "a different recorded value is not licensed"
    );
}

#[test]
fn unequal_base_or_key_cannot_use_the_two_direction_store_equivalence() {
    for change in 0..2 {
        let mut f = Fixture::new(8);
        let base = if change == 0 {
            f.terms.mk_var("other_base", f.terms.sort(f.base).clone())
        } else {
            f.base
        };
        let key = if change == 1 {
            f.terms.mk_var("other_key", Sort::bitvec(8))
        } else {
            f.key
        };
        let second = f.store(base, key, f.right);
        let before = raw_eq(&mut f.terms, f.variable, second);
        let forged = f.terms.mk_eq_coerce_no_ite_expand(f.left, f.right);
        f.roots.push(before);
        f.records.insert(forged, (before, 1));
        assert!(f.plan(forged).is_none());
    }
    let mut f = Fixture::new(8);
    let other_key = f.terms.mk_var("other_key", Sort::bitvec(8));
    let read = f.read(f.variable, other_key);
    let before = raw_eq(&mut f.terms, read, f.right);
    let forged = raw_eq(&mut f.terms, f.left, f.right);
    f.roots.push(before);
    f.records.insert(forged, (before, 1));
    assert!(f.plan(forged).is_none());
}

#[test]
fn malformed_metadata_dead_ids_and_prefix_only_child_licenses_decline_transactionally() {
    for change in 0..8 {
        let mut f = Fixture::new(8);
        let read = f.read(f.variable, f.key);
        let original_args = [f.variable, f.key];
        let mut store_args = vec![f.base, f.key, f.left];
        let mut store_sort = f.terms.sort(f.base).clone();
        let mut symbol = Symbol::named("store");
        match change {
            0 => store_args[0] = f.left,
            1 => store_args[1] = f.terms.true_term(),
            2 => store_args[2] = f.terms.true_term(),
            3 => store_sort = Sort::Bool,
            4 => {
                store_args.pop();
            }
            5 => symbol = Symbol::indexed("store", vec![0]),
            6 => store_args[1] = TermId(u32::MAX),
            7 => {}
            _ => unreachable!(),
        }
        // Even a malformed root is live; inspect child liveness before
        // asking TermStore for a dead child's sort.
        let malformed = f.terms.mk_app(symbol, store_args, store_sort);
        let new_args = [malformed, f.key];
        let set = f.roots.iter().copied().collect();
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false);
        let source = cx.chain.add_assume(f.source, None);
        let children = [
            EqRes::Changed {
                to: malformed,
                eq_term: f.source,
                id: source,
            },
            EqRes::Unchanged,
        ];
        let children = if change == 7 {
            &children[..1]
        } else {
            &children[..]
        };
        let mark = cx.chain.steps.len();
        let mut planner = PropagationChainPlanner {
            terms: &mut f.terms,
        };
        assert!(planner
            .plan_array_fold(
                &mut cx,
                read,
                f.left,
                &Symbol::named("select"),
                &original_args,
                &new_args,
                children
            )
            .is_none());
        assert_eq!(cx.chain.steps.len(), mark);
    }
}

#[test]
fn budget_refusal_preserves_chain_and_fresh_exact_allowance_authenticates() {
    let mut f = Fixture::new(8);
    let read = f.read(f.variable, f.key);
    let set = f.roots.iter().copied().collect();
    for allowance in [16, 17] {
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false);
        let source = cx.chain.add_assume(f.source, None);
        let children = [
            EqRes::Changed {
                to: f.replacement,
                eq_term: f.source,
                id: source,
            },
            EqRes::Unchanged,
        ];
        cx.budget = allowance;
        let mark = cx.chain.steps.len();
        let mut planner = PropagationChainPlanner {
            terms: &mut f.terms,
        };
        let result = planner.plan_array_fold(
            &mut cx,
            read,
            f.left,
            &Symbol::named("select"),
            &[f.variable, f.key],
            &[f.replacement, f.key],
            &children,
        );
        if allowance == 16 {
            assert!(result.is_none());
            assert_eq!(cx.chain.steps.len(), mark);
        } else {
            let (equality, id) = result.expect("exact fixed bridge allowance");
            assert_source(planner.terms, &f.roots, &cx.chain, id, equality);
        }
    }
}

#[test]
fn constant_target_guard_and_late_source_stamp_are_preserved() {
    let mut f = Fixture::new(8);
    let truth = f.terms.true_term();
    let bool_base = f
        .terms
        .mk_var("bool_array", Sort::array(Sort::bitvec(8), Sort::Bool));
    let bool_variable = f
        .terms
        .mk_var("bool_variable", f.terms.sort(bool_base).clone());
    let store = f.store(bool_base, f.key, truth);
    let read = f.read(bool_variable, f.key);
    let source = raw_eq(&mut f.terms, bool_variable, store);
    let roots = [source];
    let set = roots.iter().copied().collect();
    let mut cx =
        PlanCx::new(&set, &roots, &f.records, &f.entries, &[], false).with_constant_target(truth);
    let source_id = cx.chain.add_assume(source, None);
    let children = [
        EqRes::Changed {
            to: store,
            eq_term: source,
            id: source_id,
        },
        EqRes::Unchanged,
    ];
    let mut planner = PropagationChainPlanner {
        terms: &mut f.terms,
    };
    assert!(planner
        .plan_array_fold(
            &mut cx,
            read,
            truth,
            &Symbol::named("select"),
            &[bool_variable, f.key],
            &[store, f.key],
            &children
        )
        .is_none());
    assert_eq!(cx.chain.steps.len(), 1);
    drop(cx);

    let second = f.store_term_for_right();
    let before = raw_eq(&mut f.terms, f.variable, second);
    let after = raw_eq(&mut f.terms, f.left, f.right);
    f.roots.push(before);
    f.entries.insert(f.variable, (f.replacement, f.source, 2));
    f.records.insert(after, (before, 1));
    assert!(
        f.plan(after).is_none(),
        "future source stamps cannot license a fold"
    );
}
