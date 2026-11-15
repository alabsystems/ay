// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The NRA check ends with the check it runs in.
//!
//! The DPLL(T) caller polls its deadline only between theory checks, and one
//! NRA check can run the multivariate witness search and hundreds of
//! refinement rounds. A QF_NRA query under a 1 s per-check `:timeout` ran
//! until the `-T:20` watchdog's hard exit at 22 s. The check now polls
//! `ay_core::resource::check_stop_requested`, which reads the thread's
//! current GuardTree node: the Check node the executor enters around every
//! check-sat, with its live per-check deadline.

use ay_core::resource::{ChildSpec, Guard, NodeLabel};
use ay_core::term::TermStore;
use ay_core::{Sort, TheoryResult, TheorySolver};
use num_bigint::BigInt;
use num_rational::BigRational;

use crate::NraSolver;

fn rational(value: i64) -> BigRational {
    BigRational::from_integer(BigInt::from(value))
}

/// `x*y > 5`, `x >= 1`, `y >= 1`: satisfiable, and only by the nonlinear
/// machinery (no single-variable shortcut applies).
fn check_product(terms: &mut TermStore) -> TheoryResult {
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let one = terms.mk_rational(rational(1));
    let five = terms.mk_rational(rational(5));
    let product = terms.mk_mul(vec![x, y]);
    let big = terms.mk_gt(product, five);
    let x_pos = terms.mk_ge(x, one);
    let y_pos = terms.mk_ge(y, one);
    let mut solver = NraSolver::new(terms);
    solver.assert_literal(big, true);
    solver.assert_literal(x_pos, true);
    solver.assert_literal(y_pos, true);
    solver.check()
}

#[test]
fn a_fired_check_stop_ends_the_nra_check_with_unknown() {
    let mut terms = TermStore::new();
    let stopped = {
        let check = Guard::root_child(ChildSpec::new(NodeLabel::Check));
        check.cancel();
        let _scope = check.enter();
        check_product(&mut terms)
    };
    assert!(
        matches!(stopped, TheoryResult::Unknown),
        "a stopped check answers unknown, got {stopped:?}"
    );

    // Control: the same check with no stop decides it.
    let mut terms = TermStore::new();
    let decided = check_product(&mut terms);
    assert!(
        matches!(decided, TheoryResult::Sat),
        "the unstopped check is decided, got {decided:?}"
    );
}
