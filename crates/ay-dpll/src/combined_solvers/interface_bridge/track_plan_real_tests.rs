// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Planned LRA-lane interface tracking against the interleaved walks it
//! replaced (#combiner-carry-other-lanes).
//!
//! `reference_collect_real_constants` is the pre-plan `collect_real_constants`
//! kept verbatim as an oracle (walk and insert in one go, including its
//! `contains_key` guard). The LRA lane's combined plan
//! (`track_real_literal`: interface terms, then rational constants, then UF
//! arithmetic arguments), memoised and possibly carried from an earlier
//! bridge, must leave the bridge exactly as the three passes do.

use super::*;
use ay_core::Sort;

/// Pre-plan `collect_real_constants`, verbatim.
fn reference_collect_real_constants(
    bridge: &mut InterfaceBridge,
    terms: &TermStore,
    term: TermId,
    visited: &mut HashSet<TermId>,
) {
    if !visited.insert(term) {
        return;
    }
    match terms.get(term) {
        TermData::Const(Constant::Rational(r)) if !bridge.real_const_terms.contains_key(&r.0) => {
            bridge.real_const_terms.insert(r.0.clone(), term);
            bridge
                .interface_trail
                .push(InterfaceTrailEntry::RealConstTerm(r.0.clone()));
        }
        TermData::Const(Constant::Int(n)) => {
            let rational = BigRational::from(n.clone());
            if !bridge.real_const_terms.contains_key(&rational) {
                bridge.real_const_terms.insert(rational.clone(), term);
                bridge
                    .interface_trail
                    .push(InterfaceTrailEntry::RealConstTerm(rational));
            }
        }
        TermData::App(_, args) => {
            for &arg in args {
                reference_collect_real_constants(bridge, terms, arg, visited);
            }
        }
        TermData::Not(inner) => reference_collect_real_constants(bridge, terms, *inner, visited),
        TermData::Ite(c, t, e) => {
            reference_collect_real_constants(bridge, terms, *c, visited);
            reference_collect_real_constants(bridge, terms, *t, visited);
            reference_collect_real_constants(bridge, terms, *e, visited);
        }
        _ => {}
    }
}

/// The LRA lane's three passes, with the real-constant pass verbatim.
fn reference_track_real(bridge: &mut InterfaceBridge, terms: &TermStore, literal: TermId) {
    bridge.track_interface_term(terms, literal);
    reference_collect_real_constants(bridge, terms, literal, &mut HashSet::default());
    bridge.track_uf_arith_args(terms, literal);
}

/// Everything the LRA-lane tracking can change, in iteration order.
fn state(bridge: &InterfaceBridge) -> (Vec<TermId>, Vec<(BigRational, TermId)>, Vec<String>) {
    let arith: Vec<TermId> = bridge.interface_arith_terms.iter().copied().collect();
    let consts: Vec<(BigRational, TermId)> = bridge
        .real_const_terms
        .iter()
        .map(|(value, term)| (value.clone(), *term))
        .collect();
    let trail: Vec<String> = bridge
        .interface_trail
        .iter()
        .map(|entry| match entry {
            InterfaceTrailEntry::ScopeMarker => "scope".to_string(),
            InterfaceTrailEntry::ArithTerm(t) => format!("arith {}", t.0),
            InterfaceTrailEntry::ConstTerm(n) => format!("const {n}"),
            InterfaceTrailEntry::RealConstTerm(r) => format!("real {r}"),
            InterfaceTrailEntry::PropagatedEq(a, b) => format!("eq {} {}", a.0, b.0),
            InterfaceTrailEntry::PropagatedValue(t) => format!("value {}", t.0),
        })
        .collect();
    (arith, consts, trail)
}

fn rational(numer: i64, denom: i64) -> BigRational {
    BigRational::new(BigInt::from(numer), BigInt::from(denom))
}

/// Real UF, Real array, ite, negation, shared sub-DAGs, constants that
/// collide as rationals (`2` and `2/1`, `1/2` twice), and an Int constant with
/// no rational twin (`3`, which takes the Int-constant insert): every branch of
/// the three passes and the `contains_key` guard.
fn literals(terms: &mut TermStore) -> Vec<TermId> {
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let p = terms.mk_var("p", Sort::Bool);
    let a = terms.mk_var("a", Sort::array(Sort::Real, Sort::Real));
    let half = terms.mk_rational(rational(1, 2));
    let two_int = terms.mk_int(BigInt::from(2));
    let two = terms.mk_rational(rational(2, 1));
    let three_halves = terms.mk_rational(rational(3, 2));
    let f =
        |terms: &mut TermStore, arg: TermId| terms.mk_app(Symbol::named("f"), [arg], Sort::Real);
    let plus = |terms: &mut TermStore, l: TermId, r: TermId| {
        terms.mk_app(Symbol::named("+"), [l, r], Sort::Real)
    };
    let eq = |terms: &mut TermStore, l: TermId, r: TermId| {
        terms.mk_app(Symbol::named("="), [l, r], Sort::Bool)
    };
    let fx = f(terms, x);
    let fy = f(terms, y);
    let x_half = plus(terms, x, half);
    let fx_half = f(terms, x_half);
    let sel = terms.mk_app(Symbol::named("select"), [a, x_half], Sort::Real);
    let fx_y = plus(terms, fx, y);
    let fy_x = plus(terms, fy, x);
    let ite = terms.mk_ite(p, x, fy);
    let f_two = f(terms, two_int);
    let le_atom = terms.mk_app(Symbol::named("<="), [fx_y, three_halves], Sort::Bool);
    let l1 = eq(terms, fx, x_half);
    let e2 = eq(terms, fy, two);
    let l2 = terms.mk_not(e2);
    let l3 = eq(terms, sel, fx_half);
    let e4 = eq(terms, fx_y, fy_x);
    let l4 = terms.mk_not(e4);
    let l5 = eq(terms, ite, f_two);
    let three_int = terms.mk_int(BigInt::from(3));
    let f_three = f(terms, three_int);
    let l6 = eq(terms, fy, f_three);
    vec![l1, l2, l6, l3, le_atom, l4, l5, l1, l3]
}

#[test]
fn planned_real_tracking_leaves_the_bridge_exactly_as_the_interleaved_walks() {
    let mut terms = TermStore::new();
    let lits = literals(&mut terms);
    let mut reference = InterfaceBridge::new();
    let mut planned = InterfaceBridge::new();
    let mut by_pass = InterfaceBridge::new();
    for (step, &literal) in lits.iter().enumerate() {
        if step == 3 {
            reference.push();
            planned.push();
            by_pass.push();
        }
        reference_track_real(&mut reference, &terms, literal);
        planned.track_real_literal(&terms, literal);
        by_pass.track_interface_term(&terms, literal);
        by_pass.collect_real_constants(&terms, literal);
        by_pass.track_uf_arith_args(&terms, literal);
        assert_eq!(state(&planned), state(&reference), "step {step}");
        assert_eq!(state(&by_pass), state(&reference), "step {step}");
    }
    reference.pop();
    planned.pop();
    by_pass.pop();
    assert_eq!(state(&planned), state(&reference));
    assert_eq!(state(&by_pass), state(&reference));
    assert!(!reference.interface_arith_terms.is_empty());
    // `2` (Int) and `2/1` collide: exactly one of them is registered.
    assert!(reference.real_const_terms.contains_key(&rational(2, 1)));
    assert!(reference.real_const_terms.contains_key(&rational(1, 2)));
    // `3` (Int) has no rational twin: registered through the Int-constant arm.
    assert!(reference.real_const_terms.contains_key(&rational(3, 1)));
    // Plans are term-level facts: the pop keeps them, on the real lane only.
    assert!(!planned.real_track_plans.is_empty());
    assert!(planned.track_plans.is_empty());
}

#[test]
fn carried_real_plans_reproduce_the_tracking_of_a_cold_bridge() {
    let mut terms = TermStore::new();
    let lits = literals(&mut terms);
    let mut source = InterfaceBridge::new();
    for &literal in &lits {
        source.track_real_literal(&terms, literal);
    }
    let carried = source
        .export_track_plans(&terms)
        .expect("real plans to carry");
    assert!(
        source.real_track_plans.is_empty(),
        "export moves the plans out"
    );

    // A later round's fresh bridge over the grown store.
    let _split = terms.mk_var("split_atom", Sort::Bool);
    let mut warm = InterfaceBridge::new();
    warm.import_track_plans(&terms, carried);
    assert_eq!(warm.real_track_plans.len(), {
        let mut distinct = lits.clone();
        distinct.sort_unstable();
        distinct.dedup();
        distinct.len()
    });
    let mut reference = InterfaceBridge::new();
    for &literal in &lits {
        warm.track_real_literal(&terms, literal);
        reference_track_real(&mut reference, &terms, literal);
    }
    assert_eq!(state(&warm), state(&reference));
}

/// The two lanes' memos never stand in for each other: the LIA plan of a
/// literal collects Int constants, the LRA plan rational ones.
#[test]
fn lia_and_lra_plans_of_one_literal_stay_apart() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let fx = terms.mk_app(Symbol::named("f"), [x], Sort::Int);
    let seven = terms.mk_int(BigInt::from(7));
    let lit = terms.mk_app(Symbol::named("="), [fx, seven], Sort::Bool);
    let mut source = InterfaceBridge::new();
    source.track_int_literal(&terms, lit);
    let carried = source.export_track_plans(&terms).expect("lia plan");

    let mut bridge = InterfaceBridge::new();
    bridge.import_track_plans(&terms, carried);
    bridge.track_real_literal(&terms, lit);
    let mut reference = InterfaceBridge::new();
    reference_track_real(&mut reference, &terms, lit);
    assert_eq!(state(&bridge), state(&reference));
    assert!(bridge.int_const_terms.is_empty());
    assert!(bridge.real_const_terms.contains_key(&rational(7, 1)));
}

/// Negative twin: real plans computed on a store that was rolled back must not
/// be replayed for the term that re-minted the same id. Without the stamp
/// check the stale plan would register `1/2 -> (old term id)`.
#[test]
fn real_plans_from_a_rolled_back_store_are_dropped() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let half = terms.mk_rational(rational(1, 2));
    let checkpoint = terms.rollback_checkpoint();
    let fx = terms.mk_app(Symbol::named("f"), [x], Sort::Real);
    let old = terms.mk_app(Symbol::named("="), [fx, half], Sort::Bool);
    let carried = {
        let mut source = InterfaceBridge::new();
        source.track_real_literal(&terms, old);
        assert!(source.interface_arith_terms.contains(&fx));
        source.export_track_plans(&terms).expect("plan")
    };
    terms.rollback_to(checkpoint);
    let _filler = terms.mk_var("z", Sort::Real);
    let reminted = terms.mk_app(Symbol::named("="), [y, x], Sort::Bool);
    assert_eq!(reminted, old, "the rollback re-minted the literal's id");

    let mut bridge = InterfaceBridge::new();
    bridge.import_track_plans(&terms, carried);
    assert!(bridge.real_track_plans.is_empty());
    let mut reference = InterfaceBridge::new();
    bridge.track_real_literal(&terms, reminted);
    reference_track_real(&mut reference, &terms, reminted);
    assert_eq!(state(&bridge), state(&reference));
    assert!(bridge.real_const_terms.is_empty());
}
