// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Bounded model-checking harnesses for the PB CDCL covering-bound logic.
//!
//! Written in the `kani`-attribute format and gated behind `#[cfg(kani)]`, but
//! **executed by Trust's `model-checker-consumer` bounded model checker**, not the standalone
//! `kani` tool. Extracted verbatim from `cdcl.rs`.

use super::*;

/// Single positive-coefficient linear term `coeff * x_var`.
fn pos_term(coeff: i128, var: u32) -> PbTerm {
    PbTerm {
        coeff,
        lits: vec![PbLit {
            var,
            negated: false,
        }],
    }
}

/// For every `Some(F)` returned, `F <= objective(x)` for every feasible `x`.
/// Fixed n=2 structure; only the integer coefficients are symbolic, bounded so
/// the internal i128 checked arithmetic and knapsack DP (vec sized `rhs+1`,
/// rhs<=3) stay tiny. The 2^2 assignments are enumerated CONCRETELY.
#[kani::proof]
fn objective_lower_bound_never_overshoots() {
    let c1: i128 = kani::any();
    let c2: i128 = kani::any();
    kani::assume((1..=3).contains(&c1));
    kani::assume((1..=3).contains(&c2));
    let objective = PbObjective {
        terms: vec![pos_term(c1, 1), pos_term(c2, 2)],
    };

    let a1: i128 = kani::any();
    let a2: i128 = kani::any();
    let rhs: i128 = kani::any();
    kani::assume((0..=3).contains(&a1));
    kani::assume((0..=3).contains(&a2));
    kani::assume((1..=3).contains(&rhs));
    let constraints = vec![PbConstraint {
        terms: vec![pos_term(a1, 1), pos_term(a2, 2)],
        rel: PbRel::Ge,
        rhs,
    }];

    if let Some(f) = objective_lower_bound_from_constraints(&constraints, &objective, &|| false) {
        for mask in 0u32..4 {
            let x = [mask & 1 == 1, mask & 2 == 2];
            if crate::eval::verify_all_constraints(&constraints, &x) {
                assert!(f <= eval_objective(&objective, &x));
            }
        }
    }
}
