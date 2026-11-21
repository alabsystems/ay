// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{Sort, TermStore, TheoryResult};

fn carrier() -> Sort {
    Sort::Uninterpreted("OwnedR".into())
}
fn configured(terms: &TermStore) -> DtSolver<'_> {
    let mut solver = DtSolver::new(terms);
    solver.register_datatype("OwnedR", &["owned_r".into()]);
    solver.register_ctor_selectors("owned_r", &["children".into()]);
    solver
}

#[test]
fn owned_sequence_dt_solver_detects_unit_parent_cycle_with_actual_equality_explanation() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let children = terms.mk_app(Symbol::named("seq.unit"), [r], Sort::seq(carrier()));
    let parent = terms.mk_app(Symbol::named("owned_r"), [children], carrier());
    let equality = terms.mk_eq(r, parent);
    let mut solver = configured(&terms);
    solver.assert_literal(equality, true);
    let TheoryResult::Unsat(reasons) = solver.check() else {
        panic!("native owned cycle must refute");
    };
    assert!(reasons.contains(&TheoryLit::new(equality, true)));
    let mut replay = configured(&terms);
    for literal in reasons {
        replay.assert_literal(literal.term, literal.value);
    }
    assert!(matches!(replay.check(), TheoryResult::Unsat(_)));
}

#[test]
fn owned_sequence_dt_solver_keeps_empty_and_finite_children_satisfiable() {
    let mut terms = TermStore::new();
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], Sort::seq(carrier()));
    let leaf = terms.mk_app(Symbol::named("owned_r"), [empty], carrier());
    let children = terms.mk_app(Symbol::named("seq.unit"), [leaf], Sort::seq(carrier()));
    let parent = terms.mk_app(Symbol::named("owned_r"), [children], carrier());
    let value = terms.mk_var("value", carrier());
    let equality = terms.mk_eq(value, parent);
    let mut solver = configured(&terms);
    solver.assert_literal(equality, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn owned_sequence_dt_solver_nth_guards_are_scoped_and_explained() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let children = terms.mk_var("children_value", Sort::seq(carrier()));
    let index = terms.mk_var("i", Sort::Int);
    let parent = terms.mk_app(Symbol::named("owned_r"), [children], carrier());
    let nth = terms.mk_app(Symbol::named("seq.nth"), [children, index], carrier());
    let parent_eq = terms.mk_eq(r, parent);
    let nth_eq = terms.mk_eq(r, nth);
    let zero = terms.mk_int(0.into());
    let len = terms.mk_app(Symbol::named("seq.len"), [children], Sort::Int);
    let lower = terms.mk_app(Symbol::named("<="), [zero, index], Sort::Bool);
    let upper = terms.mk_app(Symbol::named("<"), [index, len], Sort::Bool);
    let mut solver = configured(&terms);
    solver.assert_literal(parent_eq, true);
    solver.assert_literal(nth_eq, true);
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "no in-bounds membership has been established"
    );
    solver.push();
    solver.assert_literal(lower, true);
    solver.assert_literal(upper, true);
    let TheoryResult::Unsat(reasons) = solver.check() else {
        panic!("guarded native owned cycle must refute");
    };
    assert!(
        reasons.contains(&TheoryLit::new(lower, true))
            && reasons.contains(&TheoryLit::new(upper, true))
    );
    solver.pop();
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "popped guards cannot remain membership authority"
    );
    solver.push();
    solver.assert_literal(lower, true);
    solver.assert_literal(upper, false);
    assert!(
        matches!(solver.check(), TheoryResult::Sat),
        "an OOB read need not be an owned element"
    );
}

#[test]
fn owned_sequence_dt_solver_concat_self_identity_does_not_refute() {
    let mut terms = TermStore::new();
    let sequence = terms.mk_var("sequence", Sort::seq(carrier()));
    let empty = terms.mk_app(Symbol::named("seq.empty"), [], Sort::seq(carrier()));
    let concat = terms.mk_app(
        Symbol::named("seq.++"),
        [sequence, empty],
        Sort::seq(carrier()),
    );
    let parent = terms.mk_app(Symbol::named("owned_r"), [sequence], carrier());
    let value = terms.mk_var("value", carrier());
    let parent_eq = terms.mk_eq(value, parent);
    let identity = terms.mk_eq(sequence, concat);
    let mut solver = configured(&terms);
    solver.assert_literal(parent_eq, true);
    solver.assert_literal(identity, true);
    assert!(matches!(solver.check(), TheoryResult::Sat));
}

#[test]
fn owned_sequence_dt_solver_false_upper_guard_and_alias_explanations_are_exact() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", carrier());
    let children = terms.mk_var("children", Sort::seq(carrier()));
    let alias = terms.mk_var("alias", Sort::seq(carrier()));
    let index = terms.mk_var("i", Sort::Int);
    let index_alias = terms.mk_var("j", Sort::Int);
    let zero = terms.mk_int(0.into());
    let len = terms.mk_app(Symbol::named("seq.len"), [children], Sort::Int);
    let parent = terms.mk_app(Symbol::named("owned_r"), [children], carrier());
    let nth = terms.mk_app(Symbol::named("seq.nth"), [alias, index_alias], carrier());
    let parent_eq = terms.mk_eq(r, parent);
    let nth_eq = terms.mk_eq(r, nth);
    let sequence_eq = terms.mk_eq(children, alias);
    let index_eq = terms.mk_eq(index, index_alias);
    let lower = terms.mk_app(Symbol::named(">="), [index, zero], Sort::Bool);
    let not_upper = terms.mk_app(Symbol::named("<="), [len, index], Sort::Bool);
    let premises = [
        TheoryLit::new(parent_eq, true),
        TheoryLit::new(nth_eq, true),
        TheoryLit::new(sequence_eq, true),
        TheoryLit::new(index_eq, true),
        TheoryLit::new(lower, true),
        TheoryLit::new(not_upper, false),
    ];
    let mut solver = configured(&terms);
    for premise in premises {
        solver.assert_literal(premise.term, premise.value);
    }
    let TheoryResult::Unsat(reasons) = solver.check() else {
        panic!("actual alias equalities and the false upper comparison close the owned cycle");
    };
    for premise in premises {
        assert!(reasons.contains(&premise));
    }
    for omitted in [sequence_eq, index_eq] {
        let mut replay = configured(&terms);
        for premise in &reasons {
            if premise.term != omitted {
                replay.assert_literal(premise.term, premise.value);
            }
        }
        assert!(
            matches!(replay.check(), TheoryResult::Sat),
            "removing an actual alias premise defeats this explanation"
        );
    }
}
