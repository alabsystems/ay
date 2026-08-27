// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive sweeps for sub-schema (P).
//!
//! Every clause in each box is decided TWICE — once by the recognizer, once by
//! the independent quotient-model evaluator — and the sweep asserts
//! `accept => valid` on every one of them, plus a floor on the number of
//! accepts so a sweep can never pass vacuously by rejecting everything.

use super::*;

/// Every subset of `pool` of size `2..=max_len`, as index vectors.
fn subsets(pool_len: usize, max_len: usize, mut visit: impl FnMut(&[usize])) {
    let mut chosen: Vec<usize> = Vec::new();
    fn rec(
        start: usize,
        pool_len: usize,
        max_len: usize,
        chosen: &mut Vec<usize>,
        visit: &mut impl FnMut(&[usize]),
    ) {
        if chosen.len() >= 2 {
            visit(chosen);
        }
        if chosen.len() == max_len {
            return;
        }
        for index in start..pool_len {
            chosen.push(index);
            rec(index + 1, pool_len, max_len, chosen, visit);
            chosen.pop();
        }
    }
    rec(0, pool_len, max_len, &mut chosen, &mut visit);
}

/// Sweep 1 — a predicate alphabet: two elements, two unary predicates and the
/// one equality atom over them, in BOTH polarities.
#[test]
fn sweep_predicate_alphabet_accepts_only_valid_clauses() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let pa = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let pb = mk_fun(&mut terms, "p", vec![b], Sort::Bool);
    let qa = mk_fun(&mut terms, "q", vec![a], Sort::Bool);
    let qb = mk_fun(&mut terms, "q", vec![b], Sort::Bool);
    let eq_ab = mk_eq(&mut terms, a, b);
    let atoms = [pa, pb, qa, qb, eq_ab];
    let mut pool: Vec<TermId> = Vec::new();
    for atom in atoms {
        pool.push(atom);
        let negated = terms.mk_not_raw(atom);
        pool.push(negated);
    }

    let mut clauses = 0usize;
    let mut accepted = 0usize;
    let mut cases: Vec<Vec<TermId>> = Vec::new();
    subsets(pool.len(), 4, |indices| {
        cases.push(indices.iter().map(|&i| pool[i]).collect());
    });
    for clause in cases {
        clauses += 1;
        if accepts(&terms, &clause) {
            accepted += 1;
            assert!(
                is_valid(&terms, &clause),
                "sub-schema (P) accepted a FALSIFIABLE clause: {:?} countermodel {:?}",
                clause,
                falsifying_model(&terms, &clause)
            );
        }
    }
    assert!(clauses > 300, "the sweep must cover a real box: {clauses}");
    assert!(
        accepted > 20,
        "the sweep must not pass vacuously: {accepted} accepts of {clauses}"
    );
}

/// Sweep 2 — a `Bool`-argument alphabet, where the only route to a merge is
/// through one of the two POLARITY classes. This is the measured ten-literal
/// `clearsy` mechanism in miniature.
#[test]
fn sweep_bool_argument_alphabet_accepts_only_valid_clauses() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let y = terms.mk_var("y", Sort::Bool);
    let c = terms.mk_var("c", Sort::Int);
    let gx = mk_fun(&mut terms, "g", vec![x], Sort::Int);
    let gy = mk_fun(&mut terms, "g", vec![y], Sort::Int);
    let eq_gx_c = mk_eq(&mut terms, gx, c);
    let eq_gy_c = mk_eq(&mut terms, gy, c);
    let eq_gx_gy = mk_eq(&mut terms, gx, gy);
    let atoms = [x, y, eq_gx_c, eq_gy_c, eq_gx_gy];
    let mut pool: Vec<TermId> = Vec::new();
    for atom in atoms {
        pool.push(atom);
        let negated = terms.mk_not_raw(atom);
        pool.push(negated);
    }

    let mut clauses = 0usize;
    let mut accepted = 0usize;
    let mut cases: Vec<Vec<TermId>> = Vec::new();
    subsets(pool.len(), 4, |indices| {
        cases.push(indices.iter().map(|&i| pool[i]).collect());
    });
    for clause in cases {
        clauses += 1;
        if accepts(&terms, &clause) {
            accepted += 1;
            assert!(
                is_valid(&terms, &clause),
                "sub-schema (P) accepted a FALSIFIABLE clause: {:?} countermodel {:?}",
                clause,
                falsifying_model(&terms, &clause)
            );
        }
    }
    assert!(clauses > 300, "the sweep must cover a real box: {clauses}");
    assert!(
        accepted > 5,
        "the sweep must not pass vacuously: {accepted} accepts of {clauses}"
    );
}

/// PADDING: an accepted core stays accepted and stays VALID when an irrelevant
/// literal of either polarity is added, over the whole predicate box. Padding a
/// clause with a fresh literal can only weaken the falsifying model's job, so a
/// pad that turned an accept into an unsound one would be a defect this pins.
#[test]
fn sweep_irrelevant_padding_never_makes_an_accept_unsound() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let pa = mk_fun(&mut terms, "p", vec![a], Sort::Bool);
    let pb = mk_fun(&mut terms, "p", vec![b], Sort::Bool);
    let hypothesis = neq(&mut terms, a, b);
    let not_pa = terms.mk_not_raw(pa);
    let core = vec![hypothesis, not_pa, pb];
    assert!(accepts(&terms, &core));

    let r = terms.mk_var("r", Sort::Bool);
    let s = terms.mk_var("s", Sort::Int);
    let ps = mk_fun(&mut terms, "p", vec![s], Sort::Bool);
    let eq_as = mk_eq(&mut terms, a, s);
    let mut pads: Vec<TermId> = vec![r, ps, eq_as];
    for index in 0..pads.len() {
        let negated = terms.mk_not_raw(pads[index]);
        pads.push(negated);
    }
    let mut padded_accepts = 0usize;
    for pad in pads {
        let mut clause = core.clone();
        clause.push(pad);
        if accepts(&terms, &clause) {
            padded_accepts += 1;
            assert!(
                is_valid(&terms, &clause),
                "padding produced a FALSIFIABLE accept: {:?}",
                falsifying_model(&terms, &clause)
            );
        }
    }
    assert!(
        padded_accepts >= 6,
        "an irrelevant pad must not remove the accept: {padded_accepts}"
    );
}
