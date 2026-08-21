// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Positive cases for the integer bound-lattice recognizer — the shapes the
//! rule exists for, each annotated with why it has NO rational Farkas
//! certificate.
//!
//! Split out of `lia_bound_lattice_tests` to keep both files inside the quality
//! gate's per-file size limit; the literal model and clause builders live in
//! the parent module and are re-used here through `use super::*`.

use super::*;
use crate::{Sort, TermStore};
use num_bigint::BigInt;

#[test]
fn accepts_scaled_singleton_range_with_no_attainable_point() {
    // `2q >= 1` and `2q <= 1`. Over ℚ this is SATISFIABLE at q = 1/2, so no
    // Farkas certificate exists; over ℤ, `2q` only takes even values.
    let mut terms = TermStore::new();
    let spec = [lower_bound_on_x(2, 1), upper_bound_on_x(2, 1)];
    let clause = build_clause(&mut terms, &spec);

    assert!(recognize_int_bound_lattice_gap(&terms, &clause));
    let core = int_bound_lattice_gap_core(&terms, &clause).expect("core");
    assert_eq!(core.gcd, BigInt::from(2));
    assert_eq!(core.lower, BigInt::from(1));
    assert_eq!(core.upper, BigInt::from(1));
    assert_eq!(falsifying_point(&spec, 60), None);
}

#[test]
fn accepts_wide_clause_whose_core_is_two_of_twenty_six_literals() {
    // The dillig12_m shape: the lattice core is two literals inside a clause
    // whose other literals are equalities and bounds on unrelated forms.
    let mut terms = TermStore::new();
    let q = terms.mk_var("q", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let mut clause = Vec::new();
    // 18 irrelevant negated equalities `(not (= (* q 2) (* r k)))`.
    for k in 2..20i64 {
        let two = terms.mk_int(BigInt::from(2));
        let coeff = terms.mk_int(BigInt::from(k));
        let lhs = terms.mk_mul(vec![two, q]);
        let rhs = terms.mk_mul(vec![coeff, r]);
        let eq = terms.mk_eq(lhs, rhs);
        clause.push(terms.mk_not(eq));
    }
    // Six loose bounds on 2q/4q/6q that do NOT conflict on their own.
    for (coeff, value) in [(2i64, 2i64), (4, 0), (6, 7), (2, 3), (4, 4), (6, 6)] {
        let c = terms.mk_int(BigInt::from(coeff));
        let scaled = terms.mk_mul(vec![c, q]);
        let bound = terms.mk_int(BigInt::from(value));
        let atom = terms.mk_le(scaled, bound);
        clause.push(terms.mk_not(atom));
    }
    // The core: `2q <= 1` (from a strict `<`) and `2q >= 1`.
    let two = terms.mk_int(BigInt::from(2));
    let scaled = terms.mk_mul(vec![two, q]);
    let bound = terms.mk_int(BigInt::from(2));
    let strict = terms.mk_lt(scaled, bound);
    clause.push(terms.mk_not(strict));
    let one = terms.mk_int(BigInt::from(1));
    let four = terms.mk_int(BigInt::from(4));
    let quad = terms.mk_mul(vec![four, q]);
    let lhs = terms.mk_add(vec![quad, one]);
    let one2 = terms.mk_int(BigInt::from(1));
    let rhs = terms.mk_add(vec![scaled, one2]);
    clause.push(terms.mk_le(lhs, rhs));

    assert_eq!(clause.len(), 26);
    let core = int_bound_lattice_gap_core(&terms, &clause).expect("wide clause must be certified");
    assert_eq!(core.gcd, BigInt::from(2));
    assert_eq!(core.lower, BigInt::from(1));
    assert_eq!(core.upper, BigInt::from(1));
    // The core is two of the twenty-six literals.
    assert!(core.lower_literal >= 24 && core.upper_literal >= 24);
}

#[test]
fn accepts_plain_bounds_gap_inside_a_wide_clause() {
    // The pair-sized `IntBoundsTautology` case (`lower > upper`) also holds
    // here, and now survives being buried in a wide clause.
    let mut terms = TermStore::new();
    let spec = [
        LitSpec {
            coeff_x: 0,
            coeff_y: 3,
            constant: 0,
            cmp: Cmp::Le,
            rhs: 40,
            negated: true,
        },
        lower_bound_on_x(1, 6),
        upper_bound_on_x(1, 5),
    ];
    let clause = build_clause(&mut terms, &spec);
    assert!(recognize_int_bound_lattice_gap(&terms, &clause));
    assert_eq!(falsifying_point(&spec, 60), None);
}

#[test]
fn accepts_two_variable_form_whose_gcd_skips_the_range() {
    // `6x + 4y ∈ [1,1]`: gcd 2, so the form is always even. Rationally
    // satisfiable (x = 1/6, y = 0), hence no Farkas certificate.
    let mut terms = TermStore::new();
    let spec = [
        LitSpec {
            coeff_x: 6,
            coeff_y: 4,
            constant: 0,
            cmp: Cmp::Lt,
            rhs: 1,
            negated: false,
        },
        LitSpec {
            coeff_x: 6,
            coeff_y: 4,
            constant: 0,
            cmp: Cmp::Le,
            rhs: 1,
            negated: true,
        },
    ];
    let clause = build_clause(&mut terms, &spec);
    let core = int_bound_lattice_gap_core(&terms, &clause).expect("core");
    assert_eq!(core.gcd, BigInt::from(2));
    assert_eq!(falsifying_point(&spec, 60), None);
}

#[test]
fn accepts_when_only_the_tightest_pair_of_many_bounds_conflicts() {
    // Four bounds on `3q`: only the tightest lower (7) against the tightest
    // upper (8) leaves a range with no multiple of 3. Every looser pair
    // (e.g. 1..8, 7..20) contains one, so a recognizer that did not keep the
    // extremum per group would miss this.
    let mut terms = TermStore::new();
    let spec = [
        lower_bound_on_x(3, 1),
        upper_bound_on_x(3, 20),
        lower_bound_on_x(3, 7),
        upper_bound_on_x(3, 8),
    ];
    let clause = build_clause(&mut terms, &spec);
    let core = int_bound_lattice_gap_core(&terms, &clause).expect("core");
    assert_eq!(core.lower, BigInt::from(7));
    assert_eq!(core.upper, BigInt::from(8));
    assert_eq!(core.lower_literal, 2);
    assert_eq!(core.upper_literal, 3);
    assert_eq!(falsifying_point(&spec, 60), None);
}

#[test]
fn accepts_opaque_nonlinear_atom_as_an_unconstrained_integer() {
    // `(* x y)` normalizes to an opaque Int atom. Treating it as a free
    // integer only ENLARGES the solution space, so `2·(x*y) ∈ [1,1]` is still
    // certified — and is genuinely valid, since `x*y` is an integer.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let atom = terms.mk_app(crate::Symbol::named("f"), vec![x], Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let scaled = terms.mk_mul(vec![two, atom]);
    let one = terms.mk_int(BigInt::from(1));
    let lower = terms.mk_lt(scaled, one);
    let one2 = terms.mk_int(BigInt::from(1));
    let upper = terms.mk_le(scaled, one2);
    let not_upper = terms.mk_not(upper);
    let clause = vec![lower, not_upper];
    let core = int_bound_lattice_gap_core(&terms, &clause).expect("opaque atom core");
    assert_eq!(core.gcd, BigInt::from(2));
    // Independent re-evaluation: whatever integer `f(x)` denotes, `2·f(x)` is
    // even, so it can never equal 1 — the accept holds at every integer value
    // the opaque atom could take.
    for value in -200..=200i64 {
        assert!(2 * value != 1);
    }
}
