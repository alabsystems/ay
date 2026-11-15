// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Whole-proof tests for the div/mod purification definition (`divmod_def`).
//!
//! `ay-core`'s `divmod_def_tests.rs` owns the local validity of one atom. What
//! is new HERE is that a `divmod_def` step joins the ONE fresh-definition map:
//! its quotient and remainder are FRESH, INDEPENDENT and singly defined across
//! all three rules. Every negative names the satisfiable problem the
//! "extension" would refute.

use ay_core::{AletheRule, Proof, ProofStep, Sort, TermId};

use super::eq::push_eq;
use super::{fixture, push_bound, reason, Fixture, FreshDefRegistry};
use crate::checker::validate_step_with_datatypes;

struct Pair {
    q: TermId,
    r: TermId,
    d: TermId,
    m: TermId,
}

fn pair(f: &mut Fixture, dividend: TermId, k: i64) -> Pair {
    let q = f.terms.mk_var("_divmod_q_1".to_string(), Sort::Int);
    let r = f.terms.mk_var("_divmod_r_2".to_string(), Sort::Int);
    let k = f.int(k);
    let d = f.terms.mk_intdiv(dividend, k);
    let m = f.terms.mk_mod(dividend, k);
    Pair { q, r, d, m }
}

fn push_divmod(proof: &mut Proof, p: &Pair, atom: TermId) {
    proof.add_step(ProofStep::Step {
        rule: AletheRule::DivModDef,
        clause: vec![atom],
        premises: Vec::new(),
        args: vec![p.q, p.d, p.r, p.m],
    });
}

/// `x = 2*q + r`, `0 <= r`, `r < 2`, as `mod_div_elim` builds them.
fn triple(f: &mut Fixture, p: &Pair, dividend: TermId) -> [TermId; 3] {
    let two = f.int(2);
    let zero = f.int(0);
    let scaled = f.terms.mk_mul(vec![two, p.q]);
    let sum = f.terms.mk_add(vec![scaled, p.r]);
    [
        f.terms.mk_eq(dividend, sum),
        f.terms.mk_ge(p.r, zero),
        f.terms.mk_lt(p.r, two),
    ]
}

fn strict_steps(f: &Fixture, proof: &Proof, authored: &[TermId]) -> Result<(), String> {
    let registry =
        FreshDefRegistry::collect(proof, &f.terms, Some(authored)).map_err(|e| reason(&e))?;
    let mut derived = Vec::new();
    for (idx, step) in proof.steps.iter().enumerate() {
        validate_step_with_datatypes(
            &f.terms,
            &mut derived,
            ay_core::ProofId(idx as u32),
            step,
            true,
            None,
            None,
            None,
            None,
            None,
            Some(&registry),
            None,
        )
        .map_err(|e| format!("{e:?}"))?;
    }
    Ok(())
}

#[test]
fn accepts_the_purification_triple_and_an_adopting_equality() {
    // WITNESS: `q := (div x 2)`, `r := (mod x 2)` satisfies all three atoms and
    // the executor's own bridge `(= (div x 2) q)`.
    let mut f = fixture();
    let x = f.x;
    let p = pair(&mut f, x, 2);
    let zero = f.int(0);
    let authored = f.terms.mk_le(zero, x);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    for atom in triple(&mut f, &p, x) {
        push_divmod(&mut proof, &p, atom);
    }
    push_eq(&mut proof, &mut f.terms, p.q, p.d);
    strict_steps(&f, &proof, &[authored]).expect("a conservative extension");
    let registry = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored])).unwrap();
    assert_eq!(registry.len(), 2);
}

#[test]
fn rejects_a_remainder_also_defined_by_zero() {
    // SINGLE DEFINIENS across rules. FALSIFYING: `A = {x = 1}` is satisfiable;
    // `r := (mod x 2)` together with the bound `r <= 0` forces `(mod 1 2) = 0`.
    let mut f = fixture();
    let x = f.x;
    let p = pair(&mut f, x, 2);
    let one = f.int(1);
    let zero = f.int(0);
    let authored = f.terms.mk_eq(x, one);
    let mut proof = Proof::new();
    proof.add_assume(authored, None);
    for atom in triple(&mut f, &p, x) {
        push_divmod(&mut proof, &p, atom);
    }
    push_bound(&mut proof, &mut f.terms, p.r, zero, false);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("two definientia for one remainder");
    assert!(reason(&error).contains("SECOND definiens"), "{error:?}");
}

#[test]
fn rejects_a_quotient_the_problem_constrains() {
    // FRESH. FALSIFYING: `A = {q = 5, x = 1}` is satisfiable; `x = 2*q + r`,
    // `0 <= r < 2` force `x` into `{10, 11}`.
    let mut f = fixture();
    let x = f.x;
    let p = pair(&mut f, x, 2);
    let five = f.int(5);
    let authored = f.terms.mk_eq(p.q, five);
    let mut proof = Proof::new();
    for atom in triple(&mut f, &p, x) {
        push_divmod(&mut proof, &p, atom);
    }
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[authored]))
        .expect_err("a constrained quotient is not fresh");
    assert!(reason(&error).contains("NOT fresh"), "{error:?}");
}

#[test]
fn rejects_a_dividend_that_mentions_its_own_quotient() {
    // INDEPENDENT. `q := (div (+ q 1) 2)` is a recursive equation, not a
    // definition; the registry must refuse it before any step is trusted.
    let mut f = fixture();
    let q = f.terms.mk_var("_divmod_q_1".to_string(), Sort::Int);
    let one = f.int(1);
    let dividend = f.terms.mk_add(vec![q, one]);
    let p = pair(&mut f, dividend, 2);
    let mut proof = Proof::new();
    let [_, lower, _] = triple(&mut f, &p, dividend);
    push_divmod(&mut proof, &p, lower);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[]))
        .expect_err("a self-referential definiens");
    assert!(reason(&error).contains("inside a definiens"), "{error:?}");
}

#[test]
fn rejects_a_wrong_bound_through_the_registry() {
    // NEGATIVE TWIN. `r < 1` with `k = 2`: FALSIFYING `A = {x = 1}`, where
    // `(mod 1 2) = 1` violates it.
    let mut f = fixture();
    let x = f.x;
    let p = pair(&mut f, x, 2);
    let one = f.int(1);
    let wrong = f.terms.mk_lt(p.r, one);
    let mut proof = Proof::new();
    push_divmod(&mut proof, &p, wrong);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[]))
        .expect_err("an invalid atom never binds");
    assert!(reason(&error).contains("not valid"), "{error:?}");
}

#[test]
fn rejects_a_step_naming_a_different_definiens_than_the_binding() {
    // A second step for the same `q` whose `D` is `(div x 3)`: two definientia.
    let mut f = fixture();
    let x = f.x;
    let p = pair(&mut f, x, 2);
    let other = pair(&mut f, x, 3);
    let mut proof = Proof::new();
    let [equation, _, _] = triple(&mut f, &p, x);
    push_divmod(&mut proof, &p, equation);
    let zero = f.int(0);
    let lower = f.terms.mk_ge(other.r, zero);
    push_divmod(&mut proof, &other, lower);
    let error = FreshDefRegistry::collect(&proof, &f.terms, Some(&[]))
        .expect_err("one symbol, two definientia");
    assert!(reason(&error).contains("SECOND definiens"), "{error:?}");
}
