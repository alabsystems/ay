// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Planned interface tracking against the interleaved walks it replaced
//! (#lazy-auflia-persistent-structure).
//!
//! `reference_track` is the pre-plan implementation of the three per-literal
//! passes, kept verbatim as an oracle: it walks and inserts in one go. The
//! planned path (memoised, possibly carried from an earlier bridge) must leave
//! the bridge in exactly the same state: same interface terms, same constant
//! map, same undo trail, in the same order.

use super::*;
use crate::term_helpers::{
    decode_non_bool_eq, extract_interface_arith_term, extract_uf_mixed_eq_operands,
    extract_uf_mixed_interface_term,
};
use ay_core::Sort;

/// Pre-plan `track_interface_term` + `collect_int_constants` +
/// `track_uf_arith_args`, interleaving the walks with the insertions.
fn reference_track(bridge: &mut InterfaceBridge, terms: &TermStore, literal: TermId) {
    let add = |bridge: &mut InterfaceBridge, term: TermId| {
        if bridge.interface_arith_terms.insert(term) {
            bridge
                .interface_trail
                .push(InterfaceTrailEntry::ArithTerm(term));
        }
    };
    if let Some(term) = extract_interface_arith_term(terms, literal) {
        add(bridge, term);
    }
    if let Some(term) = extract_uf_mixed_interface_term(terms, literal) {
        add(bridge, term);
    }
    let (mixed_lhs, mixed_rhs) = extract_uf_mixed_eq_operands(terms, literal);
    for term in [mixed_lhs, mixed_rhs].into_iter().flatten() {
        add(bridge, term);
    }
    if let TermData::Not(inner) = terms.get(literal) {
        if let Some((lhs, rhs)) = decode_non_bool_eq(terms, *inner) {
            for arg in [lhs, rhs] {
                if matches!(terms.sort(arg), Sort::Int | Sort::Real)
                    && is_arith_evaluable(terms, arg)
                {
                    add(bridge, arg);
                }
            }
        }
    }

    fn constants(
        bridge: &mut InterfaceBridge,
        terms: &TermStore,
        term: TermId,
        visited: &mut HashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        match terms.get(term) {
            TermData::Const(Constant::Int(n)) if !bridge.int_const_terms.contains_key(n) => {
                bridge.int_const_terms.insert(n.clone(), term);
                bridge
                    .interface_trail
                    .push(InterfaceTrailEntry::ConstTerm(n.clone()));
            }
            TermData::App(_, args) => {
                for &arg in args {
                    constants(bridge, terms, arg, visited);
                }
            }
            TermData::Not(inner) => constants(bridge, terms, *inner, visited),
            TermData::Ite(c, t, e) => {
                constants(bridge, terms, *c, visited);
                constants(bridge, terms, *t, visited);
                constants(bridge, terms, *e, visited);
            }
            _ => {}
        }
    }
    constants(bridge, terms, literal, &mut HashSet::default());

    let mut stack = vec![literal];
    let mut visited = HashSet::default();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                let track_args =
                    !BUILTIN_OPS.contains(&name.as_str()) || name == "select" || name == "store";
                if track_args && !args.is_empty() {
                    if !BUILTIN_OPS.contains(&name.as_str())
                        && matches!(terms.sort(term), Sort::Int | Sort::Real)
                    {
                        add(bridge, term);
                    }
                    for &arg in args {
                        if is_arith_evaluable(terms, arg) {
                            add(bridge, arg);
                        }
                    }
                }
                stack.extend(args.iter().copied());
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(c, t, e) => stack.extend([*c, *t, *e]),
            _ => {}
        }
    }
}

/// Everything the tracking can change, in iteration order.
fn state(bridge: &InterfaceBridge) -> (Vec<TermId>, Vec<(BigInt, TermId)>, Vec<String>) {
    let arith: Vec<TermId> = bridge.interface_arith_terms.iter().copied().collect();
    let consts: Vec<(BigInt, TermId)> = bridge
        .int_const_terms
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

/// UF, array, ite, negation, shared sub-DAGs and repeated constants: the
/// shapes every branch of the three passes reacts to.
fn literals(terms: &mut TermStore) -> Vec<TermId> {
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let p = terms.mk_var("p", Sort::Bool);
    let a = terms.mk_var("a", Sort::array(Sort::Int, Sort::Int));
    let one = terms.mk_int(BigInt::from(1));
    let three = terms.mk_int(BigInt::from(3));
    let five = terms.mk_int(BigInt::from(5));
    let f = |terms: &mut TermStore, arg: TermId| terms.mk_app(Symbol::named("f"), [arg], Sort::Int);
    let plus = |terms: &mut TermStore, l: TermId, r: TermId| {
        terms.mk_app(Symbol::named("+"), [l, r], Sort::Int)
    };
    let eq = |terms: &mut TermStore, l: TermId, r: TermId| {
        terms.mk_app(Symbol::named("="), [l, r], Sort::Bool)
    };
    let fx = f(terms, x);
    let fy = f(terms, y);
    let x3 = plus(terms, x, three);
    let x1 = plus(terms, x, one);
    let fx1 = f(terms, x1);
    let sel = terms.mk_app(Symbol::named("select"), [a, x1], Sort::Int);
    let fx_y = plus(terms, fx, y);
    let fy_x = plus(terms, fy, x);
    let ite = terms.mk_ite(p, x, fy);
    let f3 = f(terms, three);
    let le_atom = terms.mk_app(Symbol::named("<="), [fx_y, five], Sort::Bool);
    let l1 = eq(terms, fx, x3);
    let e2 = eq(terms, fy, five);
    let l2 = terms.mk_not(e2);
    let l3 = eq(terms, sel, fx1);
    let e4 = eq(terms, fx_y, fy_x);
    let l4 = terms.mk_not(e4);
    let l5 = eq(terms, ite, f3);
    vec![l1, l2, l3, le_atom, l4, l5, l1, l3]
}

#[test]
fn planned_tracking_leaves_the_bridge_exactly_as_the_interleaved_walks() {
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
        reference_track(&mut reference, &terms, literal);
        planned.track_int_literal(&terms, literal);
        by_pass.track_interface_term(&terms, literal);
        by_pass.collect_int_constants(&terms, literal);
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
    assert!(!reference.int_const_terms.is_empty());
    // Plans are term-level facts: the pop keeps them.
    assert!(!planned.track_plans.is_empty());
}

#[test]
fn carried_plans_reproduce_the_tracking_of_a_cold_bridge() {
    let mut terms = TermStore::new();
    let lits = literals(&mut terms);
    let mut source = InterfaceBridge::new();
    for &literal in &lits {
        source.track_int_literal(&terms, literal);
    }
    let carried = source.export_track_plans(&terms).expect("plans to carry");
    assert!(source.track_plans.is_empty(), "export moves the plans out");

    // A later round's fresh bridge over the grown store.
    let _split = terms.mk_var("split_atom", Sort::Bool);
    let mut warm = InterfaceBridge::new();
    warm.import_track_plans(&terms, carried);
    assert_eq!(warm.track_plans.len(), {
        let mut distinct = lits.clone();
        distinct.sort_unstable();
        distinct.dedup();
        distinct.len()
    });
    let mut reference = InterfaceBridge::new();
    for &literal in &lits {
        warm.track_int_literal(&terms, literal);
        reference_track(&mut reference, &terms, literal);
    }
    assert_eq!(state(&warm), state(&reference));
}

/// Negative twin: plans computed on a store that was rolled back must not be
/// replayed for the term that re-minted the same id.
#[test]
fn plans_from_a_rolled_back_store_are_dropped() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let seven = terms.mk_int(BigInt::from(7));
    let eight = terms.mk_int(BigInt::from(8));
    let checkpoint = terms.rollback_checkpoint();
    let fx = terms.mk_app(Symbol::named("f"), [x], Sort::Int);
    let old = terms.mk_app(Symbol::named("="), [fx, seven], Sort::Bool);
    let carried = {
        let mut source = InterfaceBridge::new();
        source.track_int_literal(&terms, old);
        assert!(source.interface_arith_terms.contains(&fx));
        source.export_track_plans(&terms).expect("plan")
    };
    terms.rollback_to(checkpoint);
    let _filler = terms.mk_var("z", Sort::Int);
    let reminted = terms.mk_app(Symbol::named("="), [y, eight], Sort::Bool);
    assert_eq!(reminted, old, "the rollback re-minted the literal's id");

    let mut bridge = InterfaceBridge::new();
    bridge.import_track_plans(&terms, carried);
    assert!(bridge.track_plans.is_empty());
    let mut reference = InterfaceBridge::new();
    bridge.track_int_literal(&terms, reminted);
    reference_track(&mut reference, &terms, reminted);
    assert_eq!(state(&bridge), state(&reference));
}
