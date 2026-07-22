// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::term::Symbol;
use ay_core::{Sort, TermStore, TheoryLit};
use num_bigint::BigInt;
use num_rational::BigRational;

use super::interface_bridge::InterfaceBridge;

#[test]
fn evaluate_and_propagate_routes_empty_reason_matches_to_speculative_pairs() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let eq_f_x_x = terms.mk_eq(f_x, x);
    let eq_x_three = terms.mk_eq(x, three);

    let mut bridge = InterfaceBridge::new();
    bridge.track_interface_term(&terms, eq_f_x_x);
    bridge.collect_int_constants(&terms, eq_x_three);

    let (eqs, speculative) = bridge.evaluate_and_propagate(
        &terms,
        &|term| {
            if term == x {
                Some((BigInt::from(3), Vec::new()))
            } else {
                None
            }
        },
        false,
        "TEST",
    );

    assert!(eqs.is_empty(), "empty-reason matches must stay speculative");
    assert_eq!(speculative, vec![(x, three)]);
}

#[test]
fn evaluate_and_propagate_emits_reasoned_int_equalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let three = terms.mk_int(BigInt::from(3));
    let f_x = terms.mk_app(Symbol::named("f"), vec![x], Sort::Int);
    let eq_f_x_x = terms.mk_eq(f_x, x);
    let eq_x_three = terms.mk_eq(x, three);
    let reason_lit = TheoryLit::new(x, true);

    let mut bridge = InterfaceBridge::new();
    bridge.track_interface_term(&terms, eq_f_x_x);
    bridge.collect_int_constants(&terms, eq_x_three);

    let (eqs, speculative) = bridge.evaluate_and_propagate(
        &terms,
        &|term| {
            if term == x {
                Some((BigInt::from(3), vec![reason_lit]))
            } else {
                None
            }
        },
        false,
        "TEST",
    );

    assert_eq!(eqs.len(), 1);
    assert_eq!(eqs[0].lhs, x);
    assert_eq!(eqs[0].rhs, three);
    assert_eq!(eqs[0].reason, vec![reason_lit]);
    assert!(speculative.is_empty());
}

#[test]
fn evaluate_and_propagate_real_skips_int_constant_targets() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::Real);
    let i = terms.mk_var("i", Sort::Int);
    let one_int = terms.mk_int(BigInt::from(1));

    let f_r = terms.mk_app(Symbol::named("f"), vec![r], Sort::Real);
    let eq_f_r_r = terms.mk_eq(f_r, r);
    let eq_i_1 = terms.mk_eq(i, one_int);

    let mut bridge = InterfaceBridge::new();
    bridge.track_interface_term(&terms, eq_f_r_r);
    bridge.collect_real_constants(&terms, eq_i_1);

    let (eqs, _speculative) = bridge.evaluate_and_propagate_real(
        &terms,
        &|term| {
            if term == r {
                Some((BigRational::from_integer(BigInt::from(1)), Vec::new()))
            } else {
                None
            }
        },
        false,
        "TEST",
    );

    assert!(
        eqs.is_empty(),
        "real interface propagation must not target Int-sorted constants as proven equalities"
    );
    // Int constants ARE collected as Real constants (W4:3291 intentional).
    // r evaluates to BigRational(1) matching the Int-derived constant with
    // empty reasons, which routes to speculative pairs. This is correct.
}

#[test]
fn evaluate_and_propagate_real_supports_to_real_fallback_to_input_term() {
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let to_real_i = terms.mk_app(Symbol::named("to_real"), vec![i], Sort::Real);
    let three_real = terms.mk_rational(BigRational::from_integer(BigInt::from(3)));
    let f_i = terms.mk_app(Symbol::named("f"), vec![i], Sort::Real);
    let eq_f_i_to_real = terms.mk_eq(f_i, to_real_i);
    // Raw-App equality: mk_eq now FOLDS `to_real(i) = 3` to the Int equality
    // `i = 3` (#to-real-bridge), so the atom this test feeds the bridge would
    // no longer exist. The bridge must still handle such atoms when they reach
    // it through non-constructor routes (deserialized/replayed terms), so build
    // the fixture with a raw App — same discipline as `to_real_i` above.
    let eq_to_real_three =
        terms.mk_app(Symbol::named("="), vec![to_real_i, three_real], Sort::Bool);
    // Use a Boolean-sorted reason (the equality atom itself). Non-Boolean
    // reasons (e.g., bare Int/Real vars) are filtered by the bridge (#6849).
    let reason_lit = TheoryLit::new(eq_to_real_three, true);

    let mut bridge = InterfaceBridge::new();
    bridge.track_interface_term(&terms, eq_f_i_to_real);
    bridge.collect_real_constants(&terms, eq_to_real_three);

    let (eqs, speculative) = bridge.evaluate_and_propagate_real(
        &terms,
        &|term| {
            // Handle both `i` and `to_real(i)` — the evaluator may query
            // either depending on whether it unwraps to_real internally.
            if term == i || term == to_real_i {
                Some((BigRational::from_integer(BigInt::from(3)), vec![reason_lit]))
            } else {
                None
            }
        },
        false,
        "TEST",
    );

    assert_eq!(eqs.len(), 1);
    assert_eq!(eqs[0].lhs, to_real_i);
    assert_eq!(eqs[0].rhs, three_real);
    assert_eq!(eqs[0].reason, vec![reason_lit]);
    // Non-empty Boolean reasons → proven equality, nothing speculative.
    assert!(speculative.is_empty());
}

#[test]
fn evaluate_and_propagate_real_routes_empty_reason_matches_to_speculative_pairs() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::Real);
    let f_r = terms.mk_app(Symbol::named("f"), vec![r], Sort::Real);
    let three_real = terms.mk_rational(BigRational::from_integer(BigInt::from(3)));
    let eq_f_r_r = terms.mk_eq(f_r, r);
    let eq_r_three = terms.mk_eq(r, three_real);

    let mut bridge = InterfaceBridge::new();
    bridge.track_interface_term(&terms, eq_f_r_r);
    bridge.collect_real_constants(&terms, eq_r_three);

    let (eqs, speculative) = bridge.evaluate_and_propagate_real(
        &terms,
        &|term| {
            if term == r {
                Some((BigRational::from_integer(BigInt::from(3)), Vec::new()))
            } else {
                None
            }
        },
        false,
        "TEST",
    );

    assert!(eqs.is_empty(), "empty-reason matches must stay speculative");
    assert_eq!(speculative, vec![(r, three_real)]);
}
