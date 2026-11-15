// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The masked `int2bv` residue identity, through the `bv_lia_tautology`
//! validator that consumes it.

use ay_core::{ProofId, Sort, Symbol, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::One;

use super::super::{
    authenticate_bv_lia_unsat_query, validate_bv_lia_tautology, BvLiaUnsatAuthenticationError,
};

fn int2bv(terms: &mut TermStore, width: u32, arg: TermId) -> TermId {
    terms.mk_app(
        Symbol::indexed("int2bv", vec![width]),
        [arg],
        Sort::bitvec(width),
    )
}

/// The authored `(conversion (bvand ((_ int2bv w) x) ((_ int2bv mask_width) mask)))`,
/// interned raw (the typed `mk_bv2nat` would rewrite it).
fn raw_masked(
    terms: &mut TermStore,
    conversion: &str,
    x: TermId,
    width: u32,
    mask_width: u32,
    mask: i64,
) -> TermId {
    let mask = terms.mk_int(BigInt::from(mask));
    let value = int2bv(terms, width, x);
    let mask = int2bv(terms, mask_width, mask);
    let and = terms.mk_app(Symbol::named("bvand"), [value, mask], Sort::bitvec(width));
    terms.mk_app(Symbol::named(conversion), [and], Sort::Int)
}

fn raw_mod(terms: &mut TermStore, x: TermId, modulus: i64) -> TermId {
    let modulus = terms.mk_int(BigInt::from(modulus));
    terms.mk_app(Symbol::named("mod"), [x, modulus], Sort::Int)
}

/// `(cl (not (= (= left right) false)))`: the lemma the transport emits.
fn residue_clause(terms: &mut TermStore, left: TermId, right: TermId) -> Vec<TermId> {
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let false_term = terms.false_term();
    let refuted = terms.mk_app(Symbol::named("="), [equality, false_term], Sort::Bool);
    vec![terms.mk_not_raw(refuted)]
}

/// Trust's `(i & 1)` (deductive-checksgen `uninhabited_arm_realmir`): the authored
/// `(bv2int (bvand ((_ int2bv 8) x) ((_ int2bv 8) 1)))` equals its elaborated
/// residue `(mod x 2)` for EVERY integer `x`, with no bound on `x` in scope —
/// both orientations, `bv2nat` and bit-vector-literal masks, and wider
/// low-bit masks. Every near miss is refused: a mask that is not `2^k - 1`,
/// the wrong modulus, a mask wider than the width (`k > w`), mismatched
/// operand widths, different operands, the signed conversion, and an
/// unnegated clause.
#[test]
fn masked_int2bv_residue_identity_and_its_mutants() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("mask_x", Sort::Int);
    let y = terms.mk_var("mask_y", Sort::Int);
    let accepted = |terms: &mut TermStore, left: TermId, right: TermId| {
        let clause = residue_clause(terms, left, right);
        validate_bv_lia_tautology(terms, ProofId(1), &clause, false, false)
    };

    let authored = raw_masked(&mut terms, "bv2int", x, 8, 8, 1);
    let residue = raw_mod(&mut terms, x, 2);
    accepted(&mut terms, authored, residue).expect("(i & 1) is i mod 2");
    accepted(&mut terms, residue, authored).expect("either orientation");
    let nat = raw_masked(&mut terms, "bv2nat", x, 8, 8, 1);
    accepted(&mut terms, nat, residue).expect("bv2nat is the same conversion");
    let low_nibble = raw_masked(&mut terms, "bv2int", x, 32, 32, 15);
    let residue_16 = raw_mod(&mut terms, x, 16);
    accepted(&mut terms, low_nibble, residue_16).expect("(i & 15) is i mod 16");
    let full = raw_masked(&mut terms, "bv2nat", x, 8, 8, 255);
    let residue_256 = raw_mod(&mut terms, x, 256);
    accepted(&mut terms, full, residue_256).expect("an all-ones mask is i mod 2^w");
    let literal_mask = {
        let value = int2bv(&mut terms, 8, x);
        let one = terms.mk_bitvec(BigInt::one(), 8);
        let and = terms.mk_app(Symbol::named("bvand"), [one, value], Sort::bitvec(8));
        terms.mk_app(Symbol::named("bv2nat"), [and], Sort::Int)
    };
    accepted(&mut terms, literal_mask, residue).expect("a literal mask, operands swapped");

    // A mask that is not a contiguous low-bit mask.
    let mask_two = raw_masked(&mut terms, "bv2int", x, 8, 8, 2);
    assert!(accepted(&mut terms, mask_two, residue).is_err());
    let mask_three = raw_masked(&mut terms, "bv2int", x, 8, 8, 3);
    assert!(accepted(&mut terms, mask_three, residue).is_err());
    let mask_five = raw_masked(&mut terms, "bv2int", x, 8, 8, 5);
    let residue_6 = raw_mod(&mut terms, x, 6);
    assert!(accepted(&mut terms, mask_five, residue_6).is_err());
    // The right mask, the wrong modulus.
    let residue_4 = raw_mod(&mut terms, x, 4);
    assert!(accepted(&mut terms, authored, residue_4).is_err());
    let residue_1 = raw_mod(&mut terms, x, 1);
    assert!(accepted(&mut terms, authored, residue_1).is_err());
    // A mask of k = 9 bits cannot fit width 8 (int2bv 8 of 511 is out of range).
    let too_wide = raw_masked(&mut terms, "bv2int", x, 8, 8, 511);
    let residue_512 = raw_mod(&mut terms, x, 512);
    assert!(accepted(&mut terms, too_wide, residue_512).is_err());
    // The whole width with a modulus one bit wider.
    assert!(accepted(&mut terms, full, residue_512).is_err());
    // Mismatched operand widths are ill-sorted.
    let mixed = raw_masked(&mut terms, "bv2int", x, 8, 4, 1);
    assert!(accepted(&mut terms, mixed, residue).is_err());
    // Different operands.
    let other = raw_mod(&mut terms, y, 2);
    assert!(accepted(&mut terms, authored, other).is_err());
    // The signed conversion is not the unsigned one (and is not in the
    // fragment); `sbv_to_int` of the all-ones mask is `x mod 256 - 256` for
    // odd-high `x`, never `x mod 256`.
    let signed = raw_masked(&mut terms, "sbv_to_int", x, 8, 8, 255);
    assert!(accepted(&mut terms, signed, residue_256).is_err());
    // The identity itself, unnegated, is not a tautology clause.
    let equality = terms.mk_app(Symbol::named("="), [authored, residue], Sort::Bool);
    assert!(validate_bv_lia_tautology(&terms, ProofId(2), &[equality], false, false).is_err());
    // Asserting the identity TRUE is satisfiable, not a refutation.
    let asserted = terms.mk_app(Symbol::named("="), [authored, residue], Sort::Bool);
    let clause = [terms.mk_not_raw(asserted)];
    assert!(validate_bv_lia_tautology(&terms, ProofId(3), &clause, false, false).is_err());
}

/// `bv2int` in the finite interpreter is the UNSIGNED conversion: on
/// `x` in `[128, 255]` the all-ones-masked value is `x`, never `x - 256`.
#[test]
fn bounded_interpreter_reads_bv2int_unsigned() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("unsigned_x", Sort::Int);
    let lo = terms.mk_int(BigInt::from(128));
    let hi = terms.mk_int(BigInt::from(255));
    let lower = terms.mk_app(Symbol::named("<="), [lo, x], Sort::Bool);
    let upper = terms.mk_app(Symbol::named("<="), [x, hi], Sort::Bool);
    let bv = int2bv(&mut terms, 8, x);
    let value = terms.mk_app(Symbol::named("bv2int"), [bv], Sort::Int);
    let unsigned = terms.mk_app(Symbol::named("="), [value, x], Sort::Bool);
    let not_unsigned = terms.mk_not_raw(unsigned);
    authenticate_bv_lia_unsat_query(&terms, &[lower, upper, not_unsigned], None)
        .expect("bv2int of int2bv on [128, 255] is x");
    let modulus = terms.mk_int(BigInt::from(256));
    let shifted = terms.mk_sub(vec![x, modulus]);
    let signed = terms.mk_app(Symbol::named("="), [value, shifted], Sort::Bool);
    authenticate_bv_lia_unsat_query(&terms, &[lower, upper, signed], None)
        .expect("under the unsigned reading the value is never x - 256");
    let error = authenticate_bv_lia_unsat_query(&terms, &[lower, upper, unsigned], None)
        .expect_err("x itself is the value");
    assert!(
        matches!(error, BvLiaUnsatAuthenticationError::Satisfiable),
        "{error}"
    );
}
