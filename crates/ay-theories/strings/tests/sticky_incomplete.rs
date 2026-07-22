// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::term::{Symbol, TermStore};
use ay_core::{Sort, TheoryResult, TheorySolver};
use ay_strings::StringSolver;

/// Internal equality merge resolves incompleteness when it eliminates
/// the variable causing it.
///
/// Round 1 infers `x = y` from `str.++(x, "a") = str.++(y, "a")` when
/// lengths are known equal (N-UNIFY). That merge triggers round 2, where
/// both sides have identical NFs in the same EQC — no incompleteness.
/// Z3 also returns sat for this formula.
///
/// The sticky_incomplete latch is correctly reset on merge (#3930):
/// if the merge resolves the variable component, re-evaluation in the
/// next round will not re-detect incompleteness, so Sat is correct.
#[test]
fn internal_equality_merge_resolves_incompleteness() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let a = terms.mk_string("a".to_string());

    let concat_x = terms.mk_app(Symbol::named("str.++"), vec![x, a], Sort::String);
    let concat_y = terms.mk_app(Symbol::named("str.++"), vec![y, a], Sort::String);
    let concat_eq = terms.mk_eq(concat_x, concat_y);

    let len_x = terms.mk_app(Symbol::named("str.len"), vec![x], Sort::Int);
    let len_y = terms.mk_app(Symbol::named("str.len"), vec![y], Sort::Int);
    let len_eq = terms.mk_eq(len_x, len_y);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(concat_eq, true);
    solver.assert_literal(len_eq, true);

    let result = solver.check();
    // N-UNIFY infers x = y, which resolves all variable NF components.
    // Round 2 sees matching NFs with no incompleteness → Sat (confirmed by Z3).
    assert!(
        matches!(result, TheoryResult::Sat),
        "N-UNIFY x=y resolves incompleteness, should be Sat, got {result:?}"
    );
}

/// Regression #3807: prefix-sharing word equation must NOT return false Sat.
///
/// Formula: str.++("ab", x) = str.++("a", y) requires VarSplit to solve
/// because x and y are unresolved variables. The sticky_incomplete flag
/// (lib.rs:107) ensures that core.clear() in round N+1 doesn't erase
/// incompleteness detected in round N of the internal fact loop.
#[test]
fn prefix_sharing_word_equation_not_false_sat() {
    let mut terms = TermStore::new();
    let ab = terms.mk_string("ab".to_string());
    let a = terms.mk_string("a".to_string());
    let x = terms.mk_var("x", Sort::String);
    let y = terms.mk_var("y", Sort::String);
    let lhs = terms.mk_app(Symbol::named("str.++"), vec![ab, x], Sort::String);
    let rhs = terms.mk_app(Symbol::named("str.++"), vec![a, y], Sort::String);
    let eq = terms.mk_eq(lhs, rhs);

    let mut solver = StringSolver::new(&terms);
    solver.assert_literal(eq, true);

    let result = solver.check();
    // Must NOT return Sat — the formula has unresolved variable components
    // that require split reasoning (EmptySplit/ConstSplit/VarSplit).
    assert!(
        !matches!(result, TheoryResult::Sat),
        "str.++(\"ab\",x) = str.++(\"a\",y) must NOT return Sat (requires split), got {result:?}"
    );
}
