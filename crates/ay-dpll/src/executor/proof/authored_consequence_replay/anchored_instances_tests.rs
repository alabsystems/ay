// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit pins for the anchored-first consequence subset.

use super::*;
use crate::executor::Executor;

type ReplayPlans = ay_core::kani_compat::DetHashMap<TermId, ConsequencePlan>;

fn subset(
    terms: &TermStore,
    consequences: &[TermId],
    plans: &ReplayPlans,
    closure: &AndConjunctClosure,
) -> Option<Vec<TermId>> {
    let mut stop = || None;
    let mut work = AnchorWork {
        remaining: MAX_ANCHOR_WORK,
        stop: &mut stop,
    };
    anchored_consequence_subset(terms, consequences, plans, closure, &mut work)
        .expect("small relevance fixtures fit the common scan allowance")
}

/// The array-frame self-check shape with the negated goal already Skolemized
/// to the declared constant `j`, so it is an ordinary authored conjunct.
const FRAME: &str = r#"
    (set-logic ALL)
    (declare-fun s () (Array Int Int))
    (declare-fun snew () (Array Int Int))
    (declare-fun val () Int)
    (declare-fun j () Int)
    (assert (= (select s 0) 10))
    (assert (= (select s 1) 20))
    (assert (= (select s 2) 30))
    (assert (>= val 0))
    (assert (forall ((k Int)) (= (select snew k) (ite (= k 1) val (select s k)))))
    (assert (and (<= 0 j) (< j 3) (< (select snew j) 0)))
"#;

fn loaded(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("anchoring fixture parses");
    let mut exec = Executor::new();
    assert!(
        exec.execute_all(&commands)
            .expect("anchoring fixture loads")
            .is_empty(),
        "fixture must contain declarations and assertions only"
    );
    exec
}

/// Record the EXACT structural instance of the forall asserted at
/// `forall_index`, as the write chokepoints do in proof mode.
fn record_instance(
    exec: &mut Executor,
    plans: &mut ReplayPlans,
    forall_index: usize,
    value: TermId,
) -> TermId {
    let forall = exec.ctx.assertions[forall_index];
    let TermData::Forall(vars, body, _) = exec.ctx.terms.get(forall).clone() else {
        panic!("fixture asserts a forall at index {forall_index}");
    };
    let mut subst: ay_core::kani_compat::DetHashMap<String, TermId> =
        ay_core::kani_compat::DetHashMap::default();
    subst.insert(vars[0].0.clone(), value);
    let instance = crate::ematching::subst_vars_exact_qf(&mut exec.ctx.terms, body, &subst)
        .expect("fixture body is quantifier-free");
    plans.insert(
        instance,
        ConsequencePlan::ForallInstance {
            quantifier: forall,
            binding: vec![value],
        },
    );
    instance
}

fn int(exec: &mut Executor, value: i64) -> TermId {
    exec.ctx.terms.mk_int(BigInt::from(value))
}

fn var(exec: &mut Executor, name: &str, sort: Sort) -> TermId {
    exec.ctx.terms.mk_var(name, sort)
}

fn int_array() -> Sort {
    Sort::Array(Box::new(ay_core::ArraySort::new(Sort::Int, Sort::Int)))
}

/// The measured fixture in miniature: of the enumerated instances only
/// `k := 0, 1, 2` share a read with the authored pins `s[0]`, `s[1]`, `s[2]`,
/// and the anchored subset is exactly the authored conjuncts plus those three,
/// in the original order.
#[test]
fn only_the_instances_anchored_to_the_authored_pins_survive() {
    let mut exec = loaded(FRAME);
    let base: Vec<TermId> = [0, 1, 2, 3, 5]
        .iter()
        .map(|&index| exec.ctx.assertions[index])
        .collect();
    let mut plans = ReplayPlans::default();
    let (zero, one, two, ten, minus_one) = (
        int(&mut exec, 0),
        int(&mut exec, 1),
        int(&mut exec, 2),
        int(&mut exec, 10),
        int(&mut exec, -1),
    );
    let s = var(&mut exec, "s", int_array());
    let snew = var(&mut exec, "snew", int_array());
    let val = var(&mut exec, "val", Sort::Int);
    let s_at_0 = exec.ctx.terms.mk_select(s, zero);
    let snew_at_0 = exec.ctx.terms.mk_select(snew, zero);

    let anchored: Vec<TermId> = [zero, one, two]
        .iter()
        .map(|&value| record_instance(&mut exec, &mut plans, 4, value))
        .collect();
    let enumerated: Vec<TermId> = [val, s_at_0, ten, snew_at_0, minus_one]
        .iter()
        .map(|&value| record_instance(&mut exec, &mut plans, 4, value))
        .collect();

    let mut consequences = base.clone();
    // Interleave so the result must be the ORIGINAL order, not a regrouping.
    consequences.extend([enumerated[0], anchored[0], enumerated[1], anchored[1]]);
    consequences.extend([enumerated[2], anchored[2], enumerated[3], enumerated[4]]);

    let subset = subset(
        &exec.ctx.terms,
        &consequences,
        &plans,
        &AndConjunctClosure::default(),
    )
    .expect("a mixed anchored/unanchored instance set yields a subset");

    let mut expected = base;
    expected.extend(anchored);
    assert_eq!(
        subset, expected,
        "the anchored subset must be the authored conjuncts plus k := 0, 1, 2 \
         only; every enumerated instance adds only reads no other consequence makes"
    );
}

/// Anchoring is a fixpoint: an instance whose only link to the goal is a read
/// that ANOTHER anchored instance creates must survive, wherever it sits in
/// the consequence order.
#[test]
fn an_instance_anchored_through_another_instance_survives() {
    let mut exec = loaded(
        r#"
            (set-logic ALL)
            (declare-fun a () (Array Int Int))
            (declare-fun b () (Array Int Int))
            (assert (< (select a 5) 0))
            (assert (forall ((k Int)) (= (select b k) (select a k))))
            (assert (forall ((m Int)) (>= (select b m) 0)))
        "#,
    );
    let goal = exec.ctx.assertions[0];
    let mut plans = ReplayPlans::default();
    let five = int(&mut exec, 5);
    let seven = int(&mut exec, 7);
    let bridge = record_instance(&mut exec, &mut plans, 1, five);
    let chained = record_instance(&mut exec, &mut plans, 2, five);
    let unrelated = record_instance(&mut exec, &mut plans, 2, seven);

    // The chained instance comes FIRST: a single pass would drop it.
    let consequences = vec![goal, chained, unrelated, bridge];
    let subset = subset(
        &exec.ctx.terms,
        &consequences,
        &plans,
        &AndConjunctClosure::default(),
    )
    .expect("one unanchored instance is left out");
    assert_eq!(subset, vec![goal, chained, bridge]);
}

/// No subset is proposed when it could not change the probe: every instance
/// anchored (the subset IS the whole set), or none anchored (the subset is the
/// plain ground problem this lane refuses to re-solve).
#[test]
fn no_subset_when_it_would_equal_the_whole_set_or_drop_every_instance() {
    let mut exec = loaded(FRAME);
    let base: Vec<TermId> = [0, 1, 2, 3, 5]
        .iter()
        .map(|&index| exec.ctx.assertions[index])
        .collect();
    let mut plans = ReplayPlans::default();
    let (zero, one, ten) = (int(&mut exec, 0), int(&mut exec, 1), int(&mut exec, 10));
    let at_zero = record_instance(&mut exec, &mut plans, 4, zero);
    let at_one = record_instance(&mut exec, &mut plans, 4, one);
    let at_ten = record_instance(&mut exec, &mut plans, 4, ten);
    let closure = AndConjunctClosure::default();

    let mut all_anchored = base.clone();
    all_anchored.extend([at_zero, at_one]);
    assert!(subset(&exec.ctx.terms, &all_anchored, &plans, &closure).is_none());

    let mut none_anchored = base;
    none_anchored.push(at_ten);
    assert!(subset(&exec.ctx.terms, &none_anchored, &plans, &closure).is_none());
}

#[test]
fn repeated_child_width_is_admitted_before_child_storage_can_grow() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let root = terms.mk_app(
        Symbol::named("wide"),
        vec![x; MAX_ANCHOR_WORK + 1],
        Sort::Bool,
    );
    let TermData::App(_, args) = terms.get(root) else {
        panic!("raw application")
    };
    let view = AnchorChildren::new(&terms, root).unwrap();
    assert_eq!(
        view.args.as_ptr(),
        args.as_ptr(),
        "children must remain borrowed"
    );
    let mut stop = || None;
    let mut work = AnchorWork {
        remaining: MAX_ANCHOR_WORK,
        stop: &mut stop,
    };
    let mut pending = Vec::new();
    assert_eq!(view.precharge(&mut work), Err(AnchorFailure::WorkLimit));
    assert_eq!(
        pending.capacity(),
        0,
        "no child storage was allocated on refusal"
    );
    // This is the same required precharge-before-growth sequence as the walkers.
    if view.precharge(&mut work).is_ok() {
        pending.extend(view.iter());
    }
    assert_eq!(pending, [] as [TermId; 0]);
    let mut seen = ay_core::kani_compat::DetHashSet::default();
    assert_eq!(
        collect_subterms(&terms, root, &mut seen, &mut work),
        Err(AnchorFailure::WorkLimit)
    );
    assert_eq!(seen.len(), 1);
    assert!(
        !seen.contains(&x),
        "the wide edges were refused before traversal"
    );
}

#[test]
fn duplicate_edges_and_binder_scans_share_the_exact_allowance() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let root = terms.mk_app(Symbol::named("pair"), vec![x, x], Sort::Bool);
    let mut stop = || None;
    for (allowance, succeeds) in [(6, true), (5, false)] {
        let mut work = AnchorWork {
            remaining: allowance,
            stop: &mut stop,
        };
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        assert_eq!(
            collect_subterms(&terms, root, &mut seen, &mut work).is_ok(),
            succeeds
        );
        assert_eq!(work.remaining, 0);
    }
    let binding = vec![x; MAX_ANCHOR_WORK + 1];
    let mut work = AnchorWork {
        remaining: MAX_ANCHOR_WORK,
        stop: &mut stop,
    };
    assert_eq!(
        instantiated_terms(&terms, root, &binding, &mut work),
        Err(AnchorFailure::WorkLimit)
    );
    assert_eq!(
        work.remaining, MAX_ANCHOR_WORK,
        "bulk binder census refuses before its loop"
    );
}

#[test]
fn fixed_point_rounds_debit_every_created_term_from_one_allowance() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let root = terms.mk_app(Symbol::named("pair"), vec![x, x], Sort::Bool);
    let mut known = ay_core::kani_compat::DetHashSet::default();
    let mut stop = || None;
    let mut work = AnchorWork {
        remaining: 8,
        stop: &mut stop,
    };
    let (anchored, pending) = anchor_round(vec![(root, vec![x; 3])], &known, &mut work).unwrap();
    assert_eq!(anchored, [] as [(TermId, Vec<TermId>); 0]);
    assert_eq!(
        work.remaining, 4,
        "one candidate and three occurrence scans"
    );
    known.insert(x);
    let (anchored, pending) = anchor_round(pending, &known, &mut work).unwrap();
    assert_eq!(anchored, vec![(root, vec![x; 3])]);
    assert_eq!(pending, [] as [(TermId, Vec<TermId>); 0]);
    assert_eq!(
        work.remaining, 0,
        "an early match does not refund precharged width"
    );
    assert_eq!(
        anchor_round(anchored, &known, &mut work),
        Err(AnchorFailure::WorkLimit)
    );
}

#[test]
fn local_scan_exhaustion_is_an_ordinary_decline_not_a_query_stop() {
    let mut exec = Executor::new();
    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let root = exec.ctx.terms.mk_app(
        Symbol::named("wide"),
        vec![x; MAX_ANCHOR_WORK + 1],
        Sort::Bool,
    );
    assert!(exec
        .try_anchored_consequence_replay(
            &[root],
            &ReplayPlans::default(),
            &AndConjunctClosure::default(),
            &[root],
            consequence_replay_budget::ProbeCap::STANDARD
        )
        .unwrap()
        .is_none());
    assert!(exec.last_unknown_reason.is_none());
    assert_eq!(exec.consequence_replay_probe_claims(), 0);
    assert_eq!(
        exec.finish_anchor_selection(Err(AnchorFailure::WorkLimit)),
        Ok(None)
    );
    assert!(
        exec.anchored_replay_open(),
        "the original whole-set fallback remains eligible"
    );
}

#[test]
fn every_observed_scan_stop_is_typed_and_terminal() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let root = terms.mk_app(Symbol::named("pair"), vec![x; 7], Sort::Bool);
    let plans = ReplayPlans::default();
    let closure = AndConjunctClosure::default();
    let mut count = 0;
    {
        let mut stop = || {
            count += 1;
            None
        };
        let mut work = AnchorWork {
            remaining: MAX_ANCHOR_WORK,
            stop: &mut stop,
        };
        assert!(
            anchored_consequence_subset(&terms, &[root], &plans, &closure, &mut work)
                .unwrap()
                .is_none()
        );
    }
    assert!(count > 10);
    for reason in [
        crate::UnknownReason::Interrupted,
        crate::UnknownReason::Timeout,
    ] {
        for ordinal in 1..=count {
            let mut calls = 0;
            let mut stop = || {
                calls += 1;
                (calls == ordinal).then_some(reason)
            };
            let mut work = AnchorWork {
                remaining: MAX_ANCHOR_WORK,
                stop: &mut stop,
            };
            assert_eq!(
                anchored_consequence_subset(&terms, &[root], &plans, &closure, &mut work),
                Err(AnchorFailure::Stopped(reason))
            );
            assert_eq!(
                calls, ordinal,
                "do not continue scanning after the observed stop"
            );
        }
    }
}

#[path = "anchored_instances_tests/terminal_stops.rs"]
mod terminal_stops;
