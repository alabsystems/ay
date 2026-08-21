// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! External lowering tests for the guarded arithmetic disequality split.
//!
//! The `la_disequality` lowering re-expresses the lemma through the GUARD's own
//! operands — `(<= lhs rhs)` and `(<= rhs lhs)` — and pairs each with a branch.
//! That pairing is licensed only while the guard and the branches share one
//! linear form (`k = 1`). Once the checker accepts a guard scaled by `k >= 2`
//! (`q <= -1 ∨ q >= 1 ∨ 2q+1 = 4q+1`), those two `la_generic` sub-steps stop
//! holding — `(cl (<= 2q+1 4q+1) (<= 1 q))` is `q >= 0 ∨ q >= 1`, false at
//! `q = -1` — so the scaled clause must keep the honest `hole` wire instead.

use super::*;
use ay_core::{Sort, Symbol, TermStore, TheoryLemmaKind};
use num_bigint::BigInt;

fn split_step(clause: Vec<TermId>) -> ProofStep {
    ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::ArithDisequalitySplit,
        lia: None,
    }
}

fn raw2(terms: &mut TermStore, op: &str, a: TermId, b: TermId, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(op), [a, b], sort)
}

#[test]
fn primitive_guard_still_lowers_to_la_disequality() {
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let zero = terms.mk_int(BigInt::from(0));
    let first = raw2(&mut terms, "<=", q, minus_one, Sort::Bool);
    let second = raw2(&mut terms, "<=", one, q, Sort::Bool);
    let guard = raw2(&mut terms, "=", q, zero, Sort::Bool);
    let step = split_step(vec![first, second, guard]);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(3))
        .expect("primitive guarded split must render");
    assert!(rendered.contains("la_disequality"), "{rendered}");
    assert!(!rendered.contains("hole"), "{rendered}");
}

#[test]
fn scaled_guard_keeps_the_hole_wire() {
    // The dillig12_m clause. The internal strict checker certifies it; the
    // external lowering cannot reconstruct it, so it must NOT be printed as a
    // `la_disequality` derivation whose sub-steps do not hold.
    let mut terms = TermStore::new();
    let q = terms.mk_var("_mod_q_0", Sort::Int);
    let minus_one = terms.mk_int(BigInt::from(-1));
    let one = terms.mk_int(BigInt::from(1));
    let two = terms.mk_int(BigInt::from(2));
    let four = terms.mk_int(BigInt::from(4));
    let first = raw2(&mut terms, "<=", q, minus_one, Sort::Bool);
    let second = raw2(&mut terms, "<=", one, q, Sort::Bool);
    let two_q = raw2(&mut terms, "*", q, two, Sort::Int);
    let four_q = raw2(&mut terms, "*", q, four, Sort::Int);
    let lhs = raw2(&mut terms, "+", two_q, one, Sort::Int);
    let rhs = raw2(&mut terms, "+", four_q, one, Sort::Int);
    let guard = raw2(&mut terms, "=", lhs, rhs, Sort::Bool);
    let step = split_step(vec![first, second, guard]);

    let rendered = AlethePrinter::new(&terms)
        .format_step(&step, ProofId(4))
        .expect("scaled guarded split must still render");
    assert!(
        !rendered.contains("la_disequality"),
        "a scaled guard must not claim the la_disequality lowering: {rendered}"
    );
    assert!(rendered.contains("hole"), "{rendered}");
}
