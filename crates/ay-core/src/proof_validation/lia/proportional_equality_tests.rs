// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::{Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use num_rational::BigRational;

fn app(t: &mut TermStore, op: &str, a: TermId, b: TermId, sort: Sort) -> TermId {
    t.mk_app_structural(Symbol::named(op), [a, b], sort)
}

fn clause(t: &mut TermStore, p: TermId, pc: TermId, q: TermId, qc: TermId) -> [TermId; 2] {
    let p = app(t, "=", p, pc, Sort::Bool);
    let q = app(t, "=", q, qc, Sort::Bool);
    [t.mk_not_raw(p), q]
}

#[test]
fn proportional_equality_witness_checks_signed_rational_affine_scales() {
    for (k, target, expected) in [(2, 21, (1, 2)), (-2, -21, (-1, 2)), (3, 14, (1, 3))] {
        let mut t = TermStore::new();
        let x = t.mk_var("x", Sort::Int);
        let coefficient = t.mk_int(k.into());
        let p = app(&mut t, "*", coefficient, x, Sort::Int);
        let constant = t.mk_int(42.into());
        let target = t.mk_int(target.into());
        let literals = clause(&mut t, p, constant, x, target);
        for input in [literals, [literals[1], literals[0]]] {
            let witness = arith_proportional_equality_witness(&t, &input).unwrap();
            assert_eq!(witness.ordered, literals);
            assert_eq!(
                witness.multiplier,
                BigRational::new(expected.0.into(), expected.1.into())
            );
        }
    }
}

#[test]
fn proportional_equality_witness_requires_every_affine_coefficient_and_constant() {
    let mut t = TermStore::new();
    let x = t.mk_var("affine_x", Sort::Int);
    let y = t.mk_var("affine_y", Sort::Int);
    let zero = t.mk_int(0.into());
    let mut row = |a: i64, b: i64, c: i64| {
        let a = t.mk_int(a.into());
        let b = t.mk_int(b.into());
        let c = t.mk_int(c.into());
        let ax = app(&mut t, "*", a, x, Sort::Int);
        let by = app(&mut t, "*", b, y, Sort::Int);
        t.mk_app_structural(Symbol::named("+"), [ax, by, c], Sort::Int)
    };
    let p = row(6, -4, 10);
    let q = row(3, -2, 5);
    let wrong_coefficient = row(3, -3, 5);
    let wrong_constant = row(3, -2, 6);
    let good = clause(&mut t, p, zero, q, zero);
    assert_eq!(
        arith_proportional_equality_witness(&t, &good)
            .unwrap()
            .multiplier,
        BigRational::new(1.into(), 2.into())
    );
    for bad in [wrong_coefficient, wrong_constant] {
        let input = clause(&mut t, p, zero, bad, zero);
        assert!(arith_proportional_equality_witness(&t, &input).is_none());
    }
}

#[test]
fn proportional_equality_witness_rejects_offsets_variables_zero_and_sorts() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let y = t.mk_var("y", Sort::Int);
    let two = t.mk_int(2.into());
    let p = app(&mut t, "*", two, x, Sort::Int);
    let n42 = t.mk_int(42.into());
    let n21 = t.mk_int(21.into());
    let n22 = t.mk_int(22.into());
    let n441 = t.mk_int(441.into());
    let zero = t.mk_int(0.into());
    let real = t.mk_var("real", Sort::Real);
    let bad_zero = app(&mut t, "*", zero, x, Sort::Int);
    let square = app(&mut t, "*", x, x, Sort::Int);
    let real_cancel = app(&mut t, "-", real, real, Sort::Int);
    let hidden_real = app(&mut t, "+", x, real_cancel, Sort::Int);
    for (a, b, c, d) in [
        (p, n42, x, n22),
        (p, n42, y, n21),
        (bad_zero, zero, x, n21),
        (square, n441, x, n21),
        (real, real, x, n21),
        (hidden_real, n21, x, n21),
    ] {
        let input = clause(&mut t, a, b, c, d);
        assert!(arith_proportional_equality_witness(&t, &input).is_none());
    }
}

#[test]
fn proportional_equality_normalization_counts_occurrences_depth_and_integer_bits() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let n21 = t.mk_int(21.into());
    let mut doubled = x;
    for _ in 0..9 {
        doubled = app(&mut t, "+", doubled, doubled, Sort::Int);
    }
    let rhs = t.mk_int(BigInt::from(21) << 9usize);
    let repeated = clause(&mut t, doubled, rhs, x, n21);
    assert!(
        arith_proportional_equality_witness(&t, &repeated).is_none(),
        "a tiny DAG must not buy exponential recursive normalization"
    );
    let zero = t.mk_int(0.into());
    let mut deep = x;
    for _ in 0..40 {
        deep = app(&mut t, "+", deep, zero, Sort::Int);
    }
    let input = clause(&mut t, deep, n21, x, n21);
    assert!(arith_proportional_equality_witness(&t, &input).is_none());
    let large = t.mk_int(BigInt::from(1) << 600usize);
    let p = app(&mut t, "*", large, x, Sort::Int);
    let rhs = app(&mut t, "*", large, n21, Sort::Int);
    let input = clause(&mut t, p, rhs, x, n21);
    assert!(arith_proportional_equality_witness(&t, &input).is_none());
}

fn proportional_atom_clause(t: &mut TermStore, atom: TermId) -> [TermId; 2] {
    let two = t.mk_int(2.into());
    let doubled = app(t, "*", two, atom, Sort::Int);
    let source = t.mk_int(42.into());
    let target = t.mk_int(21.into());
    clause(t, doubled, source, atom, target)
}

#[test]
fn proportional_equality_invalid_handles_and_forged_cycles_decline_before_indexing() {
    let mut t = TermStore::new();
    let x = t.mk_var("x", Sort::Int);
    let valid = proportional_atom_clause(&mut t, x);
    for malformed in [[TermId(u32::MAX), valid[1]], [valid[0], TermId(u32::MAX)]] {
        assert!(arith_proportional_equality_witness(&t, &malformed).is_none());
    }
    let invalid_child = t.mk_app_structural(Symbol::named("opaque"), [TermId(u32::MAX)], Sort::Int);
    let input = proportional_atom_clause(&mut t, invalid_child);
    assert!(arith_proportional_equality_witness(&t, &input).is_none());

    let invalid_equality =
        t.mk_app_structural(Symbol::named("="), [TermId(u32::MAX), x], Sort::Bool);
    let negated = t.mk_not_raw(invalid_equality);
    assert!(arith_proportional_equality_witness(&t, &[negated, valid[1]]).is_none());

    let zero = t.mk_int(0.into());
    let future = TermId(u32::try_from(t.len()).unwrap());
    let cycle = t.mk_app(Symbol::named("+"), [future, zero], Sort::Int);
    assert_eq!(future, cycle);
    let input = proportional_atom_clause(&mut t, cycle);
    assert!(arith_proportional_equality_witness(&t, &input).is_none());
}

#[test]
fn proportional_equality_raw_variable_symbol_and_index_payloads_are_bounded() {
    let mut t = TermStore::new();
    let ordinary = t.mk_var("x", Sort::Int);
    let oversized_variable = t.mk_var("v".repeat(257), Sort::Int);
    let oversized_symbol =
        t.mk_app_structural(Symbol::named("f".repeat(257)), [ordinary], Sort::Int);
    let oversized_index_name = t.mk_app_structural(
        Symbol::indexed("i".repeat(257), vec![1]),
        [ordinary],
        Sort::Int,
    );
    let oversized_indices = t.mk_app_structural(
        Symbol::indexed("indexed_atom", vec![1; 9]),
        [ordinary],
        Sort::Int,
    );
    for atom in [
        oversized_variable,
        oversized_symbol,
        oversized_index_name,
        oversized_indices,
    ] {
        let input = proportional_atom_clause(&mut t, atom);
        assert!(arith_proportional_equality_witness(&t, &input).is_none());
    }
    let boundary_name = t.mk_var("v".repeat(256), Sort::Int);
    let input = proportional_atom_clause(&mut t, boundary_name);
    assert!(arith_proportional_equality_witness(&t, &input).is_some());
}

#[test]
fn proportional_equality_preserves_opaque_array_and_mixed_sort_uf_atoms() {
    let mut t = TermStore::new();
    let array = t.mk_var("array", Sort::array(Sort::Int, Sort::Int));
    let index = t.mk_var("index", Sort::Int);
    let select = app(&mut t, "select", array, index, Sort::Int);
    let boolean = t.mk_bool(true);
    let rational = t.mk_rational(BigRational::new(1.into(), 2.into()));
    let bits = t.mk_bitvec(3.into(), 8);
    let string = t.mk_string("opaque argument".into());
    let uninterpreted = t.mk_var("u", Sort::Uninterpreted("U".into()));
    let function = t.mk_app_structural(
        Symbol::named("integer_result"),
        [array, boolean, rational, bits, string, uninterpreted],
        Sort::Int,
    );
    for atom in [select, function] {
        let input = proportional_atom_clause(&mut t, atom);
        assert_eq!(
            arith_proportional_equality_witness(&t, &input)
                .unwrap()
                .multiplier,
            BigRational::new(1.into(), 2.into())
        );
    }
}

#[test]
fn proportional_equality_bounds_opaque_literal_and_sort_metadata_before_rendering() {
    let mut t = TermStore::new();
    let wide_bits = t.mk_bitvec(0.into(), 513);
    let large_rational = t.mk_rational(BigRational::from_integer(BigInt::from(1) << 513usize));
    let large_string = t.mk_string("s".repeat(1_025));
    let large_sort_name = t.mk_var("u", Sort::Uninterpreted("U".repeat(257)));
    let mut deep_sort = Sort::Int;
    for _ in 0..40 {
        deep_sort = Sort::Seq(Box::new(deep_sort));
    }
    let deep_sort = t.mk_var("deep", deep_sort);
    for argument in [
        wide_bits,
        large_rational,
        large_string,
        large_sort_name,
        deep_sort,
    ] {
        let atom = t.mk_app_structural(Symbol::named("opaque_int"), [argument], Sort::Int);
        let input = proportional_atom_clause(&mut t, atom);
        assert!(arith_proportional_equality_witness(&t, &input).is_none());
    }
}
