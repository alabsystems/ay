// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn app(terms: &mut TermStore, name: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app_structural(Symbol::named(name), args, sort)
}

fn eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    app(terms, "=", &[left, right], Sort::Bool)
}

fn neq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    let equality = eq(terms, left, right);
    terms.mk_not_raw(equality)
}

fn max_clause(which: usize, offset: i64) -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let d = terms.mk_var("d", Sort::Int);
    let u1 = terms.mk_var("u1", Sort::Int);
    let u0 = terms.mk_var("u0", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let v3 = terms.mk_var("v3", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let u7 = terms.mk_var("u7", Sort::Int);
    let one = terms.mk_int(offset.into());
    let d1 = app(&mut terms, "+", &[d, one], Sort::Int);
    let c1 = app(&mut terms, "+", &[c, one], Sort::Int);
    let b1 = app(&mut terms, "+", &[b, one], Sort::Int);
    let clause = match which {
        120 => vec![
            neq(&mut terms, d, u1),
            neq(&mut terms, u0, u1),
            neq(&mut terms, u0, d1),
            neq(&mut terms, c, v3),
            eq(&mut terms, v3, c1),
        ],
        121 => vec![
            neq(&mut terms, b, u7),
            neq(&mut terms, u7, b1),
            eq(&mut terms, u0, u1),
            neq(&mut terms, u0, d1),
            neq(&mut terms, d, u1),
        ],
        158 => vec![
            neq(&mut terms, d, u1),
            neq(&mut terms, u0, d1),
            neq(&mut terms, b, u7),
            eq(&mut terms, u7, b1),
            neq(&mut terms, u0, u1),
        ],
        _ => unreachable!(),
    };
    (terms, clause)
}

#[test]
fn inconsistent_equality_subset_recovers_each_actual_maximum_clause() {
    for (step, expected) in [
        (120, vec![0, 1, 2]),
        (121, vec![0, 1]),
        (158, vec![0, 1, 4]),
    ] {
        let (terms, clause) = max_clause(step, 1);
        let witness = arith_inconsistent_equality_subset_witness(&terms, &clause)
            .expect("actual affine cycle");
        assert_eq!(witness.literal_indices, expected);
        assert!(witness.coefficients.iter().all(|weight| !weight.is_zero()));
        let mut progress = |_, _| true;
        let mut control = Control::new(&mut progress);
        assert!(recheck(&terms, &clause, &witness, 128, &mut control).is_some());
    }
}

#[test]
fn inconsistent_equality_subset_checks_rational_scales_and_reversed_rows() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let one = terms.mk_int(1.into());
    let two = terms.mk_int(2.into());
    let three = terms.mk_int(3.into());
    let x2 = app(&mut terms, "*", &[two, x], Sort::Int);
    let y3 = app(&mut terms, "*", &[three, y], Sort::Int);
    let z2 = app(&mut terms, "*", &[two, z], Sort::Int);
    let x3 = app(&mut terms, "*", &[three, x], Sort::Int);
    let x31 = app(&mut terms, "+", &[x3, one], Sort::Int);
    for reverse in [false, true] {
        let first = if reverse {
            neq(&mut terms, y, x2)
        } else {
            neq(&mut terms, x2, y)
        };
        let clause = [first, neq(&mut terms, y3, z2), neq(&mut terms, z, x31)];
        let witness = arith_inconsistent_equality_subset_witness(&terms, &clause).unwrap();
        assert_eq!(witness.literal_indices, [0, 1, 2]);
        assert!(witness
            .coefficients
            .iter()
            .any(|weight| weight.denom() == &BigInt::from(2)));
    }
}

#[test]
fn inconsistent_equality_subset_refuses_satisfiable_cycles_and_forged_coefficients() {
    for step in [120, 121, 158] {
        let (terms, clause) = max_clause(step, 0);
        assert!(arith_inconsistent_equality_subset_witness(&terms, &clause).is_none());
    }
    let (terms, mut clause) = max_clause(120, 1);
    let TermData::Not(equality) = terms.get(clause[0]) else {
        unreachable!()
    };
    clause[0] = *equality;
    assert!(arith_inconsistent_equality_subset_witness(&terms, &clause).is_none());
    let (terms, clause) = max_clause(120, 1);
    let mut witness = arith_inconsistent_equality_subset_witness(&terms, &clause).unwrap();
    witness.coefficients[0] += BigRational::one();
    let mut progress = |_, _| true;
    assert!(recheck(
        &terms,
        &clause,
        &witness,
        64,
        &mut Control::new(&mut progress)
    )
    .is_none());
}

#[test]
fn inconsistent_equality_subset_rejects_real_cancellation_and_invalid_handles() {
    let (mut terms, mut clause) = max_clause(120, 1);
    let real = terms.mk_var("real", Sort::Real);
    let cancel = app(&mut terms, "-", &[real, real], Sort::Real);
    let zero = terms.mk_int(0.into());
    // A forged Int container must not hide Real arithmetic that cancels out.
    let mixed = app(&mut terms, "+", &[zero, cancel], Sort::Int);
    clause.push(eq(&mut terms, mixed, zero));
    assert!(arith_inconsistent_equality_subset_witness(&terms, &clause).is_none());
    let (terms, mut clause) = max_clause(120, 1);
    clause.push(TermId(u32::MAX));
    assert!(arith_inconsistent_equality_subset_witness(&terms, &clause).is_none());
    assert!(arith_inconsistent_equality_subset_witness(&terms, &[TermId(u32::MAX)]).is_none());
}

#[test]
fn inconsistent_equality_subset_input_caps_and_cancellation_precede_normalization() {
    let (mut terms, base) = max_clause(120, 1);
    assert!(arith_inconsistent_equality_subset_witness_with_progress(
        &terms,
        &base,
        &mut |_, _| false
    )
    .is_none());
    let mut too_many = vec![base[0]; 9];
    too_many[1] = base[1];
    too_many[2] = base[2];
    assert!(arith_inconsistent_equality_subset_witness(&terms, &too_many).is_none());
    let truth = terms.mk_bool(true);
    let mut too_long = base.clone();
    too_long.resize(65, truth);
    assert!(arith_inconsistent_equality_subset_witness(&terms, &too_long).is_none());
    let mut malformed = base.clone();
    let integer = terms.mk_int(123.into());
    malformed.push(integer);
    assert!(arith_inconsistent_equality_subset_witness(&terms, &malformed).is_none());
    let indexed = terms.mk_app_structural(Symbol::indexed("indexed", vec![0; 513]), [], Sort::Int);
    let mut indexed_clause = base.clone();
    indexed_clause.push(eq(&mut terms, indexed, integer));
    assert!(arith_inconsistent_equality_subset_witness(&terms, &indexed_clause).is_none());
    let vars: Vec<_> = (0..33)
        .map(|i| terms.mk_var(format!("many_{i}"), Sort::Int))
        .collect();
    let many_atoms = app(&mut terms, "+", &vars, Sort::Int);
    let mut many_clause = base.clone();
    many_clause.push(eq(&mut terms, many_atoms, integer));
    assert!(arith_inconsistent_equality_subset_witness(&terms, &many_clause).is_none());
    let huge = terms.mk_int(BigInt::one() << 129usize);
    let zero = terms.mk_int(0.into());
    let mut clause = base.clone();
    clause.push(eq(&mut terms, huge, zero));
    assert!(arith_inconsistent_equality_subset_witness(&terms, &clause).is_none());
    let mut repeated = terms.mk_var("repeated", Sort::Int);
    for _ in 0..10 {
        repeated = app(&mut terms, "+", &[repeated, repeated], Sort::Int);
    }
    let mut clause = base.clone();
    clause.push(eq(&mut terms, repeated, zero));
    assert!(arith_inconsistent_equality_subset_witness(&terms, &clause).is_none());
    let mut deep = truth;
    for _ in 0..40 {
        deep = terms.mk_not_raw(deep);
    }
    let mut clause = base;
    clause.push(deep);
    assert!(arith_inconsistent_equality_subset_witness(&terms, &clause).is_none());
    let huge_rational = BigRational::from_integer(BigInt::one() << 3_000usize);
    let mut progress = |_, _| true;
    assert!(Control::new(&mut progress)
        .multiply(&huge_rational, &huge_rational)
        .is_none());
}
