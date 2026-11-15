// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::super::validation_formula_proves_unsat;
use crate::{ChcExpr, ChcSort, ChcVar};
use ntest::timeout;

fn int_var(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

/// `min(x, depth)` as the ask's chain spells it, one condition per link:
/// `(ite (not (>= 0 x)) (ite (not (>= 1 x)) ... 1) 0)`.
fn distinct_condition_chain(depth: usize) -> ChcExpr {
    let mut chain = ChcExpr::int(depth as i64);
    for link in (0..depth).rev() {
        let link = link as i64;
        let condition = ChcExpr::not(ChcExpr::ge(ChcExpr::int(link), int_var("x")));
        chain = ChcExpr::ite(condition, chain, ChcExpr::int(link));
    }
    chain
}

/// `(ite c (ite c ... (ite c depth (depth - 1)) ...) 0)` over one condition.
fn same_condition_chain(depth: usize) -> ChcExpr {
    let condition = ChcExpr::ge(int_var("x"), ChcExpr::int(5));
    let mut chain = ChcExpr::int(depth as i64);
    for link in (0..depth).rev() {
        chain = ChcExpr::ite(condition.clone(), chain, ChcExpr::int(link as i64));
    }
    chain
}

/// Both chains, 64 deep, come back at once: before each branch evaluation
/// returned its branch results, the distinct-condition chain cost `2^64`
/// branch evaluations and the same-condition chain Fibonacci(64). The timeout
/// is what discriminates. Both formulas are satisfiable (`x = y = 0`), so the
/// assertion is only that the fast path does not call them unsat.
#[test]
#[timeout(60_000)]
fn deep_ite_chains_are_evaluated_once_per_link() {
    let depth = 64;
    let bounds = ChcExpr::and(
        ChcExpr::ge(int_var("x"), ChcExpr::int(0)),
        ChcExpr::le(int_var("x"), ChcExpr::int(depth as i64 - 1)),
    );
    for chain in [distinct_condition_chain(depth), same_condition_chain(depth)] {
        let formula = ChcExpr::and_all([
            bounds.clone(),
            ChcExpr::eq(int_var("y"), chain),
            ChcExpr::eq(int_var("y"), int_var("x")),
        ]);
        assert!(!validation_formula_proves_unsat(&formula));
    }
}

/// `y` is 0 or 1, so `(>= y 7)` is false and `(<= y 1)` is true.
fn bounded_y(ite: ChcExpr) -> ChcExpr {
    ChcExpr::and_all([
        ChcExpr::ge(int_var("y"), ChcExpr::int(0)),
        ChcExpr::le(int_var("y"), ChcExpr::int(1)),
        ite,
    ])
}

/// The peel still decides through a branch's own evaluation. With `c`
/// undecided, `(ite c (ite c F T) (ite c T F))` is `F` under `c` (then branch,
/// peeled to its then) and `F` under `(not c)` (else branch, peeled to its
/// else), so the formula is unsat. Its twin `(ite c (ite c F T) (ite c F T2))`
/// peels to `F` and to the true `T2` = `(<= y 2)`, and is satisfiable
/// (`x < 5`), so it must stay undecided. `T2` is not `T` on purpose: with
/// equal branches `simplify_constants` folds the outer `ite` and the peel
/// never runs, and a peel that stopped comparing its two values would pass.
#[test]
fn same_condition_peel_reads_the_branch_evaluation() {
    let c = ChcExpr::ge(int_var("x"), ChcExpr::int(5));
    let f = ChcExpr::ge(int_var("y"), ChcExpr::int(7));
    let t = ChcExpr::le(int_var("y"), ChcExpr::int(1));
    let unsat = ChcExpr::ite(
        c.clone(),
        ChcExpr::ite(c.clone(), f.clone(), t.clone()),
        ChcExpr::ite(c.clone(), t.clone(), f.clone()),
    );
    assert!(validation_formula_proves_unsat(&bounded_y(unsat)));

    let t2 = ChcExpr::le(int_var("y"), ChcExpr::int(2));
    let sat = ChcExpr::ite(
        c.clone(),
        ChcExpr::ite(c.clone(), f.clone(), t),
        ChcExpr::ite(c, f, t2),
    );
    assert!(!validation_formula_proves_unsat(&bounded_y(sat)));
}
