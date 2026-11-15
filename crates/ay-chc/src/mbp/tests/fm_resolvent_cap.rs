// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `project_real_var`'s Fourier-Motzkin resolvent cap (2026-09-24,
//! `LRA_memouts_2026-09-24.md`): eliminating a Real variable with L lower
//! bounds and U upper bounds must not always produce their full L*U cross
//! product -- PDKIND's `generalize -> Mbp::project` on wide, ITE-heavy
//! transition relations (`om1_with_relays_general_*`, `cav12/*`) hit exactly
//! this shape and drove RSS past a 16 GiB budget with no per-iteration
//! checkpoint for any memory guard to act on.

use std::time::{Duration, Instant};

use super::*;

/// `x >= y_i` for `i in 0..n` and `x <= z_j` for `j in 0..n`, with `y_i`/`z_j`
/// distinct free variables (not eliminated) so a resolved literal like
/// `y_i <= z_j` cannot fold to a boolean constant -- the exact resolution's
/// literal count is therefore observable as `n * n`, not silently dropped by
/// `simplify_constants`.
fn real_value(n: i64) -> SmtValue {
    use num_bigint::BigInt;
    use num_rational::BigRational;
    SmtValue::Real(BigRational::from_integer(BigInt::from(n)))
}

fn many_bounds(n: i64) -> (ChcVar, Vec<Literal>, FxHashMap<String, SmtValue>) {
    let x = ChcVar::new("x", ChcSort::Real);
    let mut literals = Vec::new();
    let mut model = FxHashMap::default();
    model.insert("x".to_string(), real_value(n));
    for i in 0..n {
        let y = ChcVar::new(format!("y{i}"), ChcSort::Real);
        literals.push(Literal::new(
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::var(y)),
            true,
        ));
        model.insert(format!("y{i}"), real_value(i));
    }
    for j in 0..n {
        let z = ChcVar::new(format!("z{j}"), ChcSort::Real);
        literals.push(Literal::new(
            ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::var(z)),
            true,
        ));
        model.insert(format!("z{j}"), real_value(n + 1 + j));
    }
    (x, literals, model)
}

#[test]
fn project_real_var_caps_the_fourier_motzkin_cross_product() {
    let mbp = Mbp::new();
    let n = 100; // n*n = 10,000 > MAX_REAL_MBP_RESOLVENTS (4096)
    let (x, with_var, model) = many_bounds(n);

    let start = Instant::now();
    let result = mbp.project_single_var(&x, with_var, &model);
    assert!(
        start.elapsed() < Duration::from_secs(5),
        "capped projection took {:?}",
        start.elapsed()
    );

    // Bounded by the input size (2n), nowhere near the n*n = 10,000 the
    // uncapped cross product would produce.
    assert!(
        result.len() <= 2 * n as usize,
        "{} literals (expected <= {})",
        result.len(),
        2 * n
    );

    // `x` is gone.
    assert!(
        result.iter().all(|lit| !lit.atom.contains_var_name("x")),
        "projected result still mentions x"
    );

    // The fallback substitutes the model's own value for `x`: every result
    // literal mentions exactly one of the original `y_i`/`z_j` (never both --
    // that shape is the exact cross product's signature, checked negatively
    // below), confirming this took the O(with_var.len()) substitution path
    // rather than a truncated cross product.
    for lit in &result {
        let vars: std::collections::HashSet<String> =
            lit.atom.vars().into_iter().map(|v| v.name).collect();
        let mentions_y = vars.iter().any(|v| v.starts_with('y'));
        let mentions_z = vars.iter().any(|v| v.starts_with('z'));
        assert!(
            mentions_y != mentions_z,
            "literal {:?} should mention exactly one of y*/z* (substitution path), vars={:?}",
            lit.atom,
            vars
        );
    }
}

#[test]
fn project_real_var_is_unchanged_below_the_cap() {
    let mbp = Mbp::new();
    let n = 3; // n*n = 9, far below MAX_REAL_MBP_RESOLVENTS (4096)
    let (x, with_var, model) = many_bounds(n);

    let result = mbp.project_single_var(&x, with_var, &model);

    // Below the cap the exact resolution runs: every (lower, upper) pair
    // resolves to one literal, none of which are ground (each mentions one
    // `y_i` and one `z_j`), so none simplify away.
    assert_eq!(
        result.len(),
        (n * n) as usize,
        "expected the exact n*n cross product below the cap"
    );
    assert!(result.iter().all(|lit| !lit.atom.contains_var_name("x")));
    // Each resolvent pairs one lower bound (a `y_i`) with one upper bound (a
    // `z_j`): the exact cross product's signature, distinct from the
    // resolvent cap's single-variable substitution (checked above).
    for lit in &result {
        let vars: std::collections::HashSet<String> =
            lit.atom.vars().into_iter().map(|v| v.name).collect();
        assert!(
            vars.iter().any(|v| v.starts_with('y')) && vars.iter().any(|v| v.starts_with('z')),
            "literal {:?} should mention both a y* and a z* var, vars={:?}",
            lit.atom,
            vars
        );
    }
}
