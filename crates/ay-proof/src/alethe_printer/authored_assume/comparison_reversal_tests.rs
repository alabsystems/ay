// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `comparison_reversal_step` against pinned carcara's `comp_simplify`, and
//! the printed-equivalence schema that reaches it for a comparison nested in
//! an authored term (`surface_equivalence/comparison.rs`).

use super::*;
use ay_core::{Symbol, TermStore};
use num_bigint::BigInt;

/// Pinned carcara's `comp_simplify` evaluates `(< c d)` over two numeric
/// constants and `(< t t)` to `false`, so a strict reversal between such
/// operands has no checked `(not (<= ..))` leg. MEASURED: without this
/// decline the confined `forall_inst` instance `(> 3 3)` of
/// `(forall ((w Int)) (> w 3))` shipped `(= (not (<= 3 3)) (< 3 3))`, which
/// pinned carcara rejects, and `--strict-proofs` answered `unsat` with it.
#[test]
fn a_strict_reversal_carcara_would_evaluate_is_declined() {
    for (surface, canonical) in [
        ("(> 3 3)", "(< 3 3)"),
        ("(> 2 0)", "(< 0 2)"),
        ("(< 0 2)", "(> 2 0)"),
        ("(> (- 1) (/ 1 2))", "(< (/ 1 2) (- 1))"),
        ("(> 2.5 (div 7 2))", "(< (div 7 2) 2.5)"),
        // One parsed term in two spellings: quoting, a decimal's trailing
        // zero, a bit-vector literal's base, a `let` an invocation expands.
        ("(> |x| x)", "(< x |x|)"),
        ("(> (f 1.50) (f 1.5))", "(< (f 1.5) (f 1.50))"),
        (
            "(> (bv2nat #x03) (bv2nat #b00000011))",
            "(< (bv2nat #b00000011) (bv2nat #x03))",
        ),
        (
            "(> (bv2nat (_ bv3 8)) (bv2nat #x03))",
            "(< (bv2nat #x03) (bv2nat (_ bv3 8)))",
        ),
        ("(> (f 2) (f 2.0))", "(< (f 2.0) (f 2))"),
        ("(> (let ((q 3)) q) 3)", "(< 3 (let ((q 3)) q))"),
        ("(> (! x :named n) y)", "(< y (! x :named n))"),
        ("(> (- 3 1) (/ 4 2))", "(< (/ 4 2) (- 3 1))"),
    ] {
        let mut steps = Vec::new();
        assert!(
            !comparison_reversal_step(
                "t0",
                surface,
                canonical,
                EquivalenceDirection::SurfaceToCanonical,
                &mut steps,
            ),
            "{surface} over {canonical}: {steps:?}"
        );
        assert!(steps.is_empty(), "{steps:?}");
    }
    // NEGATIVE TWIN: one symbolic operand, or a non-strict pair (whose one
    // `comp_simplify` step rewrites `>=` before any evaluation), still bridges.
    for (surface, canonical, rows) in [
        ("(> x 3)", "(< 3 x)", 3),
        ("(> 3 (f 2))", "(< (f 2) 3)", 3),
        ("(>= 3 3)", "(<= 3 3)", 1),
        ("(>= 2 0)", "(<= 0 2)", 1),
        ("(> (f 1.5) (f 1.25))", "(< (f 1.25) (f 1.5))", 3),
        ("(> (* 2 3) 5)", "(< 5 (* 2 3))", 3),
        (
            "(> (bv2nat #x03) (bv2nat #x04))",
            "(< (bv2nat #x04) (bv2nat #x03))",
            3,
        ),
        (
            "(> (str.len \"a b\") (str.len \"a  b\"))",
            "(< (str.len \"a  b\") (str.len \"a b\"))",
            3,
        ),
        ("(> x!1 x)", "(< x x!1)", 3),
        // One non-constant term twice: both sides meet at `false`
        // (`strict_self_comparison_reversal`; the 8-step chain over `(f a)`
        // is MEASURED `valid` on pinned carcara 1.1.0, git 9a352ee).
        ("(> (f a) (f a))", "(< (f a) (f a))", 8),
    ] {
        let mut steps = Vec::new();
        assert!(
            comparison_reversal_step(
                "t0",
                surface,
                canonical,
                EquivalenceDirection::SurfaceToCanonical,
                &mut steps,
            ),
            "{surface} over {canonical}"
        );
        assert_eq!(steps.len(), rows, "{steps:?}");
    }
}

/// The same decline seen through the printed-equivalence schema
/// (`surface_equivalence/comparison.rs`) that made the helper reachable from a
/// confined `forall_inst` instance: a strict pair over two numerals has no
/// derivation, a non-strict pair over numerals keeps its one `comp_simplify`
/// step, and one non-constant term twice meets at `false`.
#[test]
fn the_printed_comparison_schema_declines_what_carcara_would_evaluate() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let five = terms.mk_int(BigInt::from(5));
    let seven = terms.mk_int(BigInt::from(7));
    let three = terms.mk_int(BigInt::from(3));
    let g_a = terms.mk_app(Symbol::named("g"), [a], Sort::Int);
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let numerals = terms.mk_app(Symbol::named("<"), [seven, five], Sort::Bool);
    let same = terms.mk_app(Symbol::named("<"), [g_a, g_a], Sort::Bool);
    let non_strict = terms.mk_app(Symbol::named("<="), [three, five], Sort::Bool);
    let symbolic = terms.mk_app(Symbol::named("<"), [y, x], Sort::Bool);
    let printer = AlethePrinter::new(&terms);
    assert_eq!(
        printer.printed_surface_equivalence_steps("t0", "(> 5 7)", numerals, "(< 7 5)"),
        None,
    );
    let (steps, _) = printer
        .printed_surface_equivalence_steps("t3", "(> (g a) (g a))", same, "(< (g a) (g a))")
        .expect("one non-constant term twice meets at false");
    assert_eq!(steps.len(), 8, "{steps:?}");
    // NEGATIVE TWIN: the decline is that narrow.
    let (steps, _) = printer
        .printed_surface_equivalence_steps("t1", "(>= 5 3)", non_strict, "(<= 3 5)")
        .expect("a non-strict pair over numerals is one comp_simplify");
    assert_eq!(
        steps,
        ["(step t1 (cl (= (>= 5 3) (<= 3 5))) :rule comp_simplify)"]
    );
    let (steps, _) = printer
        .printed_surface_equivalence_steps("t2", "(> x y)", symbolic, "(< y x)")
        .expect("a strict pair over two variables goes through (not (<= x y))");
    assert_eq!(steps.len(), 3, "{steps:?}");
}

#[test]
fn an_operand_swapped_comparison_is_one_printed_equivalence_schema() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let zero = terms.mk_int(BigInt::from(0));
    let five = terms.mk_int(BigInt::from(5));
    let guard = terms.mk_app(Symbol::named("<="), [zero, y], Sort::Bool);
    let not_guard = terms.mk_not_raw(guard);
    let strict = terms.mk_app(Symbol::named("<"), [five, x], Sort::Bool);
    let printer = AlethePrinter::new(&terms);
    let (steps, _) = printer
        .printed_surface_equivalence_steps("t0", "(not (>= y 0))", not_guard, "(not (<= 0 y))")
        .expect("cong over comp_simplify");
    assert!(
        steps.contains(&"(step t0.c0 (cl (= (>= y 0) (<= 0 y))) :rule comp_simplify)".to_string()),
        "{steps:?}"
    );
    let (steps, _) = printer
        .printed_surface_equivalence_steps("t1", "(> x 5)", strict, "(< 5 x)")
        .expect("the strict pair goes through (not (<= x 5))");
    assert_eq!(
        steps,
        [
            "(step t1.s0 (cl (= (> x 5) (not (<= x 5)))) :rule comp_simplify)",
            "(step t1.s1 (cl (= (not (<= x 5)) (< 5 x))) :rule comp_simplify)",
            "(step t1 (cl (= (> x 5) (< 5 x))) :rule trans :premises (t1.s0 t1.s1))",
        ]
    );
    // NEGATIVE TWIN: a different bound, the same operand order, or a
    // comparison the document does not print is no reversal.
    for (surface, term, canonical) in [
        ("(>= y 1)", guard, "(<= 0 y)"),
        ("(<= 0 y)", guard, "(<= 0 y)"),
        ("(< y 0)", guard, "(<= 0 y)"),
        ("(>= y 0)", guard, "(<= 0 z)"),
    ] {
        assert_eq!(
            printer.printed_surface_equivalence_steps("t2", surface, term, canonical),
            None,
            "{surface} over {canonical}"
        );
    }
}
