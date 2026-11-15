// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The (F3) constructor-equality bridge reads only well-sorted equalities.
//!
//! The bridge scans the term store for `(= t C)` atoms and asserts
//! `(= (= t C) (is-C t))`. A raw `mk_app` can intern an `=` whose sides
//! differ in sort (the equality planner did so for `(= nil u)` until it
//! learned to refuse cross-sort sides); the scan then read the `U` constant
//! `u` as a value of the list datatype and minted `(is-nil u)`, an
//! ill-sorted axiom that later panicked the probe's variable substitution.

use ay_core::kani_compat::DetHashSet;
use ay_core::term::Symbol;
use ay_core::{Sort, TermData, TermId, TermStore};
use ay_frontend::parse;

use crate::executor::Executor;

const LIST_CELLS: &str = r#"
(set-logic ALL)
(declare-sort U 0)
(declare-datatypes ((L 0)) (((nil) (cons (hd U) (tl L)))))
(declare-const a L)
(declare-const u U)
(declare-const w U)
(assert (= a nil))
(assert (= u w))
"#;

fn contains(terms: &TermStore, root: TermId, needle: TermId) -> bool {
    let mut stack = vec![root];
    let mut seen: DetHashSet<TermId> = DetHashSet::default();
    while let Some(term) = stack.pop() {
        if term == needle {
            return true;
        }
        if seen.insert(term) {
            stack.extend(terms.children(term));
        }
    }
    false
}

/// `(= x y)` in either orientation.
fn is_equality_of(terms: &TermStore, term: TermId, x: TermId, y: TermId) -> bool {
    matches!(
        terms.get(term),
        TermData::App(sym, args)
            if sym.name() == "=" && args.len() == 2
                && ((args[0] == x && args[1] == y) || (args[0] == y && args[1] == x))
    )
}

/// A nullary constructor is a `Var` the context declares as a constructor.
fn is_nullary_constructor(exec: &Executor, term: TermId) -> bool {
    let TermData::Var(name, _) = exec.ctx.terms.get(term) else {
        return false;
    };
    exec.ctx.is_constructor(name).is_some()
}

#[test]
fn constructor_equality_bridge_skips_an_equality_across_sorts() {
    let commands = parse(LIST_CELLS).expect("parse");
    let mut exec = Executor::new();
    assert!(exec.execute_all(&commands).expect("execute").is_empty());
    let &[a_is_nil, u_is_w] = exec.ctx.assertions.as_slice() else {
        panic!("expected the two authored assertions");
    };
    let TermData::App(_, sides) = exec.ctx.terms.get(a_is_nil).clone() else {
        panic!("`(= a nil)` must stay an equality");
    };
    let TermData::App(_, elements) = exec.ctx.terms.get(u_is_w).clone() else {
        panic!("`(= u w)` must stay an equality");
    };
    let (nil, a) = if is_nullary_constructor(&exec, sides[0]) {
        (sides[0], sides[1])
    } else {
        (sides[1], sides[0])
    };
    assert!(
        is_nullary_constructor(&exec, nil),
        "`(= a nil)` names `nil`"
    );
    let u = elements[0];
    assert_eq!(
        exec.ctx.terms.sort(u),
        &Sort::Uninterpreted("U".to_string())
    );

    // Store residue: an `=` across `L` and `U`, reachable from the problem so
    // the scan reads it whatever the session's epoch bookkeeping says.
    let cross_sort = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [nil, u], Sort::Bool);
    let reaching = exec.ctx.terms.mk_or(vec![cross_sort, u_is_w]);
    exec.ctx.assertions.push(reaching);

    let base: DetHashSet<TermId> = exec.ctx.assertions.iter().copied().collect();
    let axioms = exec.dt_selector_axioms(&base);

    let is_nil_u = exec
        .ctx
        .terms
        .mk_app(Symbol::named("is-nil"), [u], Sort::Bool);
    let is_nil_a = exec
        .ctx
        .terms
        .mk_app(Symbol::named("is-nil"), [a], Sort::Bool);
    assert!(
        !axioms
            .iter()
            .any(|&axiom| contains(&exec.ctx.terms, axiom, is_nil_u)),
        "the bridge read the `U` constant as a list value and minted `(is-nil u)`"
    );
    // The twin: the well-sorted atom `(= a nil)` is still bridged to its tester.
    assert!(
        axioms
            .iter()
            .any(|&axiom| is_equality_of(&exec.ctx.terms, axiom, a_is_nil, is_nil_a)),
        "the well-sorted `(= a nil)` must still get `(= (= a nil) (is-nil a))`"
    );
}

/// #dt-frontier-tester-diet: at unroll depth 1 the frontier term
/// `(tl a)` — created by `a`'s reconstruction axiom, receiving no (C)
/// of its own — gets no exhaustiveness (D) or mutual-exclusion (G)
/// clause: its tester atoms occur nowhere else, so those clauses only
/// constrain otherwise-unreferenced atoms. At depth 2 the same term
/// receives (C), and its testers must appear.
#[test]
fn frontier_terms_get_no_tester_clauses_until_they_receive_constructor_axioms() {
    // Fresh executor per depth: frontier detection keys on term IDs
    // minted during the call, so reusing one store across depths would
    // make the depth-1 frontier pre-existing (never frontier) at depth 2.
    let run = |depth: usize| -> (Vec<TermId>, TermId, TermId, Executor) {
        let commands = parse(LIST_CELLS).expect("parse");
        let mut exec = Executor::new();
        assert!(exec.execute_all(&commands).expect("execute").is_empty());
        let &[a_is_nil, _] = exec.ctx.assertions.as_slice() else {
            panic!("expected the two authored assertions");
        };
        let TermData::App(_, sides) = exec.ctx.terms.get(a_is_nil).clone() else {
            panic!("`(= a nil)` must stay an equality");
        };
        let a = if is_nullary_constructor(&exec, sides[0]) {
            sides[1]
        } else {
            sides[0]
        };
        let a_sort = exec.ctx.terms.sort(a).clone();
        let base: DetHashSet<TermId> = exec.ctx.assertions.iter().copied().collect();
        // The diet is BV-route-armed; arm it as `solve_dt_ufbv` would.
        exec.dt_frontier_tester_diet_armed = true;
        let axioms = exec.dt_selector_axioms_to_depth(&base, depth);
        let tl_a = exec.ctx.terms.mk_app(Symbol::named("tl"), [a], a_sort);
        let is_cons_tl_a = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-cons"), [tl_a], Sort::Bool);
        let is_cons_a = exec
            .ctx
            .terms
            .mk_app(Symbol::named("is-cons"), [a], Sort::Bool);
        (axioms, is_cons_tl_a, is_cons_a, exec)
    };

    let (axioms1, is_cons_tl_a1, is_cons_a1, exec1) = run(1);
    assert!(
        !axioms1
            .iter()
            .any(|&axiom| contains(&exec1.ctx.terms, axiom, is_cons_tl_a1)),
        "depth-1 frontier `(tl a)` must not get tester clauses before it gets (C)"
    );
    assert!(
        axioms1
            .iter()
            .any(|&axiom| contains(&exec1.ctx.terms, axiom, is_cons_a1)),
        "the seed variable `a` keeps its tester clauses"
    );

    let (axioms2, is_cons_tl_a2, _, exec2) = run(2);
    assert!(
        axioms2
            .iter()
            .any(|&axiom| contains(&exec2.ctx.terms, axiom, is_cons_tl_a2)),
        "at depth 2 `(tl a)` receives (C), so its testers must be axiomatized"
    );
}
