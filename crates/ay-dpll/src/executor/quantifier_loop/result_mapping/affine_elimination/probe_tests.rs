// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The affinity test sees every occurrence of the binder (2026-09-25 verify,
//! B1): one under a nested quantifier or a `let` is not affine, whatever the
//! helpers that do not enter those nodes say. Built directly — the parser
//! expands `let`, so no source file reaches the probe with one.

use ay_core::Sort;
use num_bigint::BigInt;

use crate::executor::Executor;

/// `(= (* v c) 0)` for the given coefficient term `c`.
fn product_equation(
    exec: &mut Executor,
    v: ay_core::TermId,
    c: ay_core::TermId,
) -> ay_core::TermId {
    let product = exec.ctx.terms.mk_mul(vec![v, c]);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    exec.ctx.terms.mk_eq(product, zero)
}

#[test]
fn the_probe_declines_a_binder_under_a_nested_quantifier_or_a_let() {
    let mut exec = Executor::new();
    let vars = vec![("v".to_string(), Sort::Int)];
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let minus_one = exec.ctx.terms.mk_int(BigInt::from(-1));

    // c = ite(exists u. u = v, 1, -1): never 0, and it depends on v.
    let u = exec.ctx.terms.mk_var("u", Sort::Int);
    let u_is_v = exec.ctx.terms.mk_eq(u, v);
    let exists = exec
        .ctx
        .terms
        .mk_exists(vec![("u".to_string(), Sort::Int)], u_is_v);
    let nested = exec.ctx.terms.mk_ite(exists, one, minus_one);
    let atom = product_equation(&mut exec, v, nested);
    assert!(
        exec.affine_binder_probe(atom, &vars).is_none(),
        "v under a nested exists is not a constant factor"
    );

    // c = (let ((s v)) (+ s 1)): depends on v through the binding.
    let s = exec.ctx.terms.mk_var("s", Sort::Int);
    let s_plus_one = exec.ctx.terms.mk_add(vec![s, one]);
    let bound = exec
        .ctx
        .terms
        .mk_let(vec![("s".to_string(), v)], s_plus_one);
    let atom = product_equation(&mut exec, v, bound);
    assert!(
        exec.affine_binder_probe(atom, &vars).is_none(),
        "v bound by a let is not a constant factor"
    );

    // Control: a factor free of v splits, with a coefficient that never
    // vanishes (4w + 1 is odd).
    let w = exec.ctx.terms.mk_var("w", Sort::Int);
    let four = exec.ctx.terms.mk_int(BigInt::from(4));
    let four_w = exec.ctx.terms.mk_mul(vec![four, w]);
    let odd = exec.ctx.terms.mk_add(vec![four_w, one]);
    let atom = product_equation(&mut exec, v, odd);
    let probe = exec.affine_binder_probe(atom, &vars);
    assert!(
        probe.as_ref().is_some_and(|probe| probe.never_vanishes),
        "v * (4w + 1) = 0 splits, and 4w + 1 never vanishes"
    );
}

/// `(REL (+ (* v c) r) 0)` for the given coefficient and rest terms.
fn affine_relation(
    exec: &mut Executor,
    relation: &str,
    v: ay_core::TermId,
    c: ay_core::TermId,
    r: ay_core::TermId,
) -> ay_core::TermId {
    let product = exec.ctx.terms.mk_mul(vec![v, c]);
    let lhs = exec.ctx.terms.mk_add(vec![product, r]);
    let zero = exec.ctx.terms.mk_int(BigInt::from(0));
    match relation {
        "<" => exec.ctx.terms.mk_lt(lhs, zero),
        "<=" => exec.ctx.terms.mk_le(lhs, zero),
        _ => exec.ctx.terms.mk_eq(lhs, zero),
    }
}

/// A symbolic coefficient whose vanishing falsifies the rest refutes the
/// conjunct (2026-09-25 fix-up: family file w1_62501_00322, where the exact
/// elimination left `(f a) = 0 ∧ (f a) < 0` under a quantifier and lost
/// main's `unsat`; `w = −3 ∧ w = 4` is w1_62501_00000's equality form).
#[test]
fn a_vanishing_coefficient_that_falsifies_the_rest_refutes() {
    let mut exec = Executor::new();
    let vars = vec![("v".to_string(), Sort::Int)];
    let v = exec.ctx.terms.mk_var("v", Sort::Int);
    let w = exec.ctx.terms.mk_var("w", Sort::Int);
    let z = exec.ctx.terms.mk_var("z", Sort::Int);
    let refutes = |exec: &mut Executor, atom| {
        let probe = exec.affine_binder_probe(atom, &vars).expect("affine in v");
        assert!(!probe.never_vanishes, "the coefficient may vanish");
        probe.vanishing_refutes
    };

    // v·w + w < 0: w = 0 leaves 0 < 0.
    let atom = affine_relation(&mut exec, "<", v, w, w);
    assert!(refutes(&mut exec, atom), "v·w + w < 0 fails at every w");
    // v·w + w <= 0 holds at w = 0, for every v.
    let atom = affine_relation(&mut exec, "<=", v, w, w);
    assert!(!refutes(&mut exec, atom), "v·w + w <= 0 holds at w = 0");
    // v·(w + 3) + (w − 4) = 0: w = −3 leaves −7 = 0.
    let three = exec.ctx.terms.mk_int(BigInt::from(3));
    let minus_four = exec.ctx.terms.mk_int(BigInt::from(-4));
    let c = exec.ctx.terms.mk_add(vec![w, three]);
    let r = exec.ctx.terms.mk_add(vec![w, minus_four]);
    let atom = affine_relation(&mut exec, "=", v, c, r);
    assert!(refutes(&mut exec, atom), "w = −3 forces w − 4 = −7");
    // v·w + z = 0: w = 0 leaves z = 0, which some z satisfies.
    let atom = affine_relation(&mut exec, "=", v, w, z);
    assert!(
        !refutes(&mut exec, atom),
        "the rest does not follow the coefficient"
    );
}
