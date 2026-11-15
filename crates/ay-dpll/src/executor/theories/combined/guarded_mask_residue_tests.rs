// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The guarded mask residue's mask test against brute force, and the clauses
//! it emits (and refuses) on parsed queries.

use super::*;
use crate::executor::Executor;
use num_traits::ToPrimitive;

/// `c mod 2^w` read as a vector: is it a low-bit mask, and of what width?
/// For every `c` in `[-300, 300]` and `w` in `1..=8`, `Some(k)` exactly when
/// `(x mod 2^w) & (c mod 2^w) == x mod 2^k` for every `x` in `[-300, 300]`,
/// which is the identity the clause asserts.
#[test]
fn low_bit_mask_width_is_the_masks_brute_force_finds() {
    let mut masks = 0;
    for width in 1..=8u32 {
        let modulus = 1i64 << width;
        for c in -300i64..=300 {
            let vector = c.rem_euclid(modulus);
            let identity_width = (0..=width).find(|&k| {
                (-300i64..=300).all(|x| x.rem_euclid(modulus) & vector == x.rem_euclid(1 << k))
            });
            assert_eq!(
                low_bit_mask_width(&BigInt::from(c), width),
                identity_width,
                "c = {c}, w = {width}"
            );
            masks += usize::from(identity_width.is_some());
        }
    }
    assert!(masks > 500, "the sweep reached {masks} masks");
    let wide = (BigInt::one() << 64) - BigInt::one();
    assert_eq!(low_bit_mask_width(&wide, 64), Some(64));
    assert_eq!(low_bit_mask_width(&BigInt::from(-1), 64), Some(64));
    assert_eq!(low_bit_mask_width(&BigInt::from(7), 64), Some(3));
    assert_eq!(low_bit_mask_width(&BigInt::from(7), 0), None);
}

fn clauses_of(query: &str) -> (Executor, Vec<TermId>) {
    let commands = ay_frontend::parse(&format!(
        "(set-logic ALL) (declare-const x Int) (declare-const m Int) (declare-const n Int) \
         (declare-const r Int) (declare-const q Int) (declare-const b (_ BitVec 8)) {query}"
    ))
    .expect("valid query");
    let mut executor = Executor::new();
    executor.execute_all(&commands).expect("install query");
    let roots = executor.ctx.assertions.clone();
    let clauses = executor.collect_guarded_mask_residue_assertions(&roots);
    (executor, clauses)
}

/// `(or (not (= <mask> <c>)) (= <read> (mod <source> 2^k)))`, read back.
fn clause_parts(terms: &TermStore, clause: TermId) -> (TermId, TermId, TermId, i64) {
    let TermData::App(Symbol::Named(or), disjuncts) = terms.get(clause) else {
        panic!("not a disjunction: {clause:?}");
    };
    assert_eq!(or, "or");
    assert_eq!(disjuncts.len(), 2);
    // `mk_or` orders its arguments, so find the negated guard by shape.
    let (negated, equality) = if matches!(terms.get(disjuncts[0]), TermData::Not(_)) {
        (disjuncts[0], disjuncts[1])
    } else {
        (disjuncts[1], disjuncts[0])
    };
    let TermData::Not(guard) = terms.get(negated) else {
        panic!("no disjunct is a negated guard");
    };
    let TermData::App(Symbol::Named(eq), sides) = terms.get(equality) else {
        panic!("the other disjunct is not an equality");
    };
    assert_eq!(eq, "=");
    let (read, residue) = if matches!(terms.get(sides[0]), TermData::App(Symbol::Named(n), _) if n == "bv2nat")
    {
        (sides[0], sides[1])
    } else {
        (sides[1], sides[0])
    };
    let TermData::App(Symbol::Named(md), md_args) = terms.get(residue) else {
        panic!("the residue is not a mod: {residue:?}");
    };
    assert_eq!(md, "mod");
    let modulus = int_const_value(terms, md_args[1])
        .and_then(|m| m.to_i64())
        .expect("a constant modulus");
    (*guard, read, md_args[0], modulus)
}

/// Trust's shape: the mask local pinned only inside each path disjunct. One
/// clause per guard, the residue on the `int2bv` source, the mask either
/// operand; a `bv2nat(v)` source when the value is no `int2bv`.
#[test]
fn a_mask_pinned_under_a_disjunct_gets_its_residue_clause() {
    let read = "(bv2nat (bvand ((_ int2bv 8) x) ((_ int2bv 8) m)))";
    let (executor, clauses) = clauses_of(&format!(
        "(assert (or (and (= m 7) (= r {read})) (and (= m 7) (= q 1) (= r {read}))))"
    ));
    assert_eq!(clauses.len(), 1, "one read, one guard");
    let terms = &executor.ctx.terms;
    let (guard, read_term, source, modulus) = clause_parts(terms, clauses[0]);
    assert_eq!(modulus, 8);
    assert_eq!(source, terms.find_var("x").expect("x"));
    let m = terms.find_var("m").expect("m");
    assert!(
        matches!(terms.get(guard), TermData::App(Symbol::Named(eq), a) if eq == "=" && a.contains(&m))
    );
    assert!(matches!(terms.get(read_term), TermData::App(Symbol::Named(n), _) if n == "bv2nat"));

    // The mask as the first operand, spelled `-1`: `int2bv_8(-1)` is all
    // ones, so the residue is the full width.
    let (executor, clauses) = clauses_of(
        "(assert (or (and (= m (- 1)) (= r (bv2nat (bvand ((_ int2bv 8) m) ((_ int2bv 8) x))))) (= q 2)))",
    );
    assert_eq!(clauses.len(), 1);
    let (_, _, source, modulus) = clause_parts(&executor.ctx.terms, clauses[0]);
    assert_eq!(modulus, 256);
    assert_eq!(source, executor.ctx.terms.find_var("x").expect("x"));

    // A bit-vector value: the residue reads `bv2nat(b)`.
    let (executor, clauses) =
        clauses_of("(assert (or (and (= m 3) (= r (bv2nat (bvand b ((_ int2bv 8) m))))) (= q 2)))");
    assert_eq!(clauses.len(), 1);
    let terms = &executor.ctx.terms;
    let (_, _, source, modulus) = clause_parts(terms, clauses[0]);
    assert_eq!(modulus, 4);
    let b = terms.find_var("b").expect("b");
    assert!(
        matches!(terms.get(source), TermData::App(Symbol::Named(n), a) if n == "bv2nat" && a == &vec![b])
    );
}

/// No clause without a low-bit mask guard on the mask's own source: a mask
/// value that is not `2^k - 1` mod `2^w`, a guard on another variable, a
/// literal mask (`mk_bv2nat` folds it, so no opaque read remains), a mask
/// whose width differs from the value's, and no guard at all.
#[test]
fn no_clause_without_a_low_bit_guard_on_the_mask() {
    let read = "(bv2nat (bvand ((_ int2bv 8) x) ((_ int2bv 8) m)))";
    for query in [
        format!("(assert (or (and (= m 5) (= r {read})) (= q 2)))"),
        format!("(assert (or (and (= m 248) (= r {read})) (= q 2)))"),
        format!("(assert (or (and (= n 7) (= r {read})) (= q 2)))"),
        format!("(assert (= r {read}))"),
        "(assert (or (and (= m 7) (= r (bv2nat (bvand ((_ int2bv 8) x) ((_ int2bv 8) 7))))) (= q 2)))"
            .to_string(),
        "(assert (or (and (= m 7) (= r (bv2nat (bvand ((_ int2bv 8) x) ((_ zero_extend 4) ((_ int2bv 4) m)))))) (= q 2)))"
            .to_string(),
    ] {
        let (_, clauses) = clauses_of(&query);
        assert!(clauses.is_empty(), "{query}: {clauses:?}");
    }
}
