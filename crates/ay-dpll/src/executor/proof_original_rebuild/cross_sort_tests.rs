// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The equality planner never interns an `=` across two sorts.
//!
//! The substitution bridge pairs a polymorphic head's arguments position by
//! position, so an authored `(= nil (tl a))` (both sides `L`) tried as the
//! source of the goal `(= u (hd b))` (both sides `U`) asked `plan_eq` for
//! `(= nil u)`. `plan_eq` interned that equality raw before trying any leg,
//! and the shared store kept it. A consequence-replay probe's datatype (F3)
//! bridge then read `(= nil u)` as a live atom, asserted
//! `(= (= nil u) (is-nil u))`, and the probe's variable substitution rebuilt
//! it through `mk_eq_coerce_no_ite_expand`, which panics on the sort clash
//! (`hunt_quantifier_wrong_verdicts::d1_recursive_list_cells_are_never_sat`).

use super::*;

/// Every `=` application in the store whose two sides differ in sort.
fn ill_sorted_equalities(terms: &TermStore) -> Vec<TermId> {
    (0..terms.len())
        .map(|idx| TermId::new(idx as u32))
        .filter(|&term| {
            matches!(
                terms.get(term),
                TermData::App(sym, args)
                    if sym.name() == "=" && args.len() == 2
                        && terms.sort(args[0]) != terms.sort(args[1])
            )
        })
        .collect()
}

struct ListCells {
    nil: TermId,
    a: TermId,
    b: TermId,
    u: TermId,
    tl_a: TermId,
    hd_a: TermId,
    hd_b: TermId,
}

/// The D1 list-cell vocabulary: `L` cells with an `hd : L -> U` field.
fn list_cells(exec: &mut Executor) -> ListCells {
    let list = Sort::Uninterpreted("L".to_string());
    let element = Sort::Uninterpreted("U".to_string());
    let terms = &mut exec.ctx.terms;
    let nil = terms.mk_var("nil", list.clone());
    let a = terms.mk_var("a", list.clone());
    let b = terms.mk_var("b", list.clone());
    let u = terms.mk_var("u", element.clone());
    let tl_a = terms.mk_app(Symbol::named("tl"), [a], list);
    let hd_a = terms.mk_app(Symbol::named("hd"), [a], element.clone());
    let hd_b = terms.mk_app(Symbol::named("hd"), [b], element);
    ListCells {
        nil,
        a,
        b,
        u,
        tl_a,
        hd_a,
        hd_b,
    }
}

#[test]
fn plan_eq_refuses_cross_sort_sides_without_interning() {
    let mut exec = Executor::new();
    let cells = list_cells(&mut exec);
    let before = exec.ctx.terms.len();
    let mut budget = EQ_PLAN_BUDGET;
    assert!(
        exec.plan_eq(cells.nil, cells.u, &[], 0, &mut budget)
            .is_none(),
        "an equality across two sorts has no derivation"
    );
    assert_eq!(
        exec.ctx.terms.len(),
        before,
        "a refused cross-sort plan must not intern anything"
    );
    assert!(ill_sorted_equalities(&exec.ctx.terms).is_empty());
}

/// The D1 shape: the only same-head source pairs `L` arguments with `U`
/// arguments, so the bridge declines without leaving `(= nil u)` behind.
#[test]
fn substitution_bridge_never_pairs_arguments_across_sorts() {
    let mut exec = Executor::new();
    let cells = list_cells(&mut exec);
    let (source, goal) = {
        let terms = &mut exec.ctx.terms;
        let source = terms.mk_app(Symbol::named("="), [cells.nil, cells.tl_a], Sort::Bool);
        let goal = terms.mk_app(Symbol::named("="), [cells.u, cells.hd_b], Sort::Bool);
        (source, goal)
    };
    assert!(exec.plan_substitution_bridge(goal, &[source]).is_none());
    assert_eq!(
        ill_sorted_equalities(&exec.ctx.terms),
        Vec::<TermId>::new(),
        "the bridge minted an equality across sorts into the shared store"
    );
}

/// The twin: the guard refuses only the cross-sort pairing. A cross-sort
/// candidate (`(= a b)` against the `U`-sided goal) is tried first and
/// declined; the same-sorted source after it still bridges by congruence.
#[test]
fn substitution_bridge_still_plans_a_same_sorted_congruence() {
    let mut exec = Executor::new();
    let cells = list_cells(&mut exec);
    let (definition, source, goal) = {
        let terms = &mut exec.ctx.terms;
        let definition = terms.mk_app(Symbol::named("="), [cells.a, cells.b], Sort::Bool);
        let source = terms.mk_app(Symbol::named("="), [cells.u, cells.hd_a], Sort::Bool);
        let goal = terms.mk_app(Symbol::named("="), [cells.u, cells.hd_b], Sort::Bool);
        (definition, source, goal)
    };
    assert!(
        exec.plan_substitution_bridge(goal, &[definition, source])
            .is_some(),
        "`(= u (hd a))` and `(= a b)` derive `(= u (hd b))` by congruence"
    );
    assert!(ill_sorted_equalities(&exec.ctx.terms).is_empty());
}
