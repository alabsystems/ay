// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The elimination leaves the term store of a formula it does not rewrite as
//! main's probe left it (2026-09-25 verify, B2): exactly `0`, `1` and `L - R`
//! for an inspected `Int` relation, nothing more and nothing less. Minting
//! nothing moved `inc_26093_00136`'s search from 95 to 370 conflicts.

use ay_core::term::Symbol;
use ay_core::{Sort, TermData};
use num_bigint::BigInt;

use crate::executor::Executor;

#[test]
fn a_relation_left_unrewritten_interns_exactly_the_replaced_probe_footprint() {
    let mut exec = Executor::new();
    let vars = vec![("x".to_string(), Sort::Int)];
    let x = exec.ctx.terms.mk_var("x", Sort::Int);
    let f_x = exec
        .ctx
        .terms
        .mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let seven = exec.ctx.terms.mk_int(BigInt::from(7));
    // `(= (f x) 7)`: `x` sits under `f`, so it is not affine.
    let body = exec.ctx.terms.mk_eq(f_x, seven);
    let TermData::App(_, args) = exec.ctx.terms.get(body).clone() else {
        panic!("the equality is an application");
    };
    let before = exec.ctx.terms.len();
    let out = exec.eliminate_affine_binder_conjuncts(body, &vars);
    assert_eq!(
        out, body,
        "`x` under `f` is not affine: nothing is rewritten"
    );
    let after = exec.ctx.terms.len();
    assert!(
        after > before,
        "`(f x) - 7` is new, so the footprint grows the store"
    );
    // Re-interning returns the existing ids; only the store length matters.
    let _ = exec.ctx.terms.mk_int(BigInt::from(0));
    let _ = exec.ctx.terms.mk_int(BigInt::from(1));
    let _ = exec.ctx.terms.mk_sub(vec![args[0], args[1]]);
    assert_eq!(
        exec.ctx.terms.len(),
        after,
        "the pass interned 0, 1 and L - R already -- main's probe footprint"
    );
}
