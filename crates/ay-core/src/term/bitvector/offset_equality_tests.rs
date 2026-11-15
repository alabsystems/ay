// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn raw(terms: &mut TermStore, op: &str, args: Vec<TermId>, width: u32) -> TermId {
    terms.mk_app(Symbol::named(op), args, Sort::bitvec(width))
}

fn constant(terms: &mut TermStore, value: u64, width: u32) -> TermId {
    terms.mk_bitvec(BigInt::from(value), width)
}

/// Value of a term over the walk's operators, with `x`/`y`/`z` assigned.
fn eval(terms: &TermStore, term: TermId, env: &[(TermId, u64)], width: u32) -> u64 {
    let mask = (1_u64 << width) - 1;
    match terms.get(term) {
        TermData::Const(Constant::BitVec { value, .. }) => {
            u64::try_from(value.clone()).expect("narrow literal") & mask
        }
        TermData::App(Symbol::Named(op), args) => {
            let values: Vec<u64> = args.iter().map(|&a| eval(terms, a, env, width)).collect();
            match (op.as_str(), values.as_slice()) {
                ("bvadd", _) => values.iter().fold(0_u64, |acc, v| acc.wrapping_add(*v)) & mask,
                ("bvsub", [a, b]) => a.wrapping_sub(*b) & mask,
                ("bvneg", [a]) => a.wrapping_neg() & mask,
                other => panic!("unexpected operator {other:?}"),
            }
        }
        _ => env
            .iter()
            .find(|(word, _)| *word == term)
            .map(|(_, value)| *value)
            .expect("assigned word"),
    }
}

#[test]
fn coroutine_byte_address_atom_reads_one_difference() {
    let mut terms = TermStore::new();
    let vbase = terms.mk_var("vbase", Sort::bitvec(64));
    let frame = terms.mk_var("frame", Sort::bitvec(64));
    let (c24, c7, c1) = (
        constant(&mut terms, 24, 64),
        constant(&mut terms, 7, 64),
        constant(&mut terms, 1, 64),
    );
    // (= (bvadd (bvadd 24 7) frame) (bvadd 1 vbase)), as authored.
    let slot = raw(&mut terms, "bvadd", vec![c24, c7], 64);
    let lhs = raw(&mut terms, "bvadd", vec![slot, frame], 64);
    let rhs = raw(&mut terms, "bvadd", vec![c1, vbase], 64);
    let reading = terms.bv_offset_equality(lhs, rhs).expect("offset equality");
    assert_eq!(reading.minuend, vbase);
    assert_eq!(reading.subtrahend, frame);
    // frame + 31 = vbase + 1  <=>  vbase - frame = 30.
    assert_eq!(reading.constant, BigInt::from(30));
    assert_eq!(reading.width, 64);
    // A bare word on one side reads the same pair.
    let bare = terms.bv_offset_equality(lhs, vbase).expect("bare side");
    assert_eq!(
        (bare.minuend, bare.subtrahend, bare.constant),
        (vbase, frame, BigInt::from(31))
    );
    // Either orientation of the equality reads the same difference.
    assert_eq!(terms.bv_offset_equality(rhs, lhs), Some(reading));
}

#[test]
fn declines_what_is_not_two_opposite_unit_words() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let z = terms.mk_var("z", Sort::bitvec(8));
    let one = constant(&mut terms, 1, 8);
    // Already the bare comparison, or already a difference of the two words
    // against a literal, in either order and at zero too: re-read, it would
    // name a difference the authored subtractor does not share.
    assert_eq!(terms.bv_offset_equality(x, y), None);
    let difference = raw(&mut terms, "bvsub", vec![x, y], 8);
    assert_eq!(terms.bv_offset_equality(difference, one), None);
    assert_eq!(terms.bv_offset_equality(one, difference), None);
    let reversed = raw(&mut terms, "bvsub", vec![y, x], 8);
    assert_eq!(terms.bv_offset_equality(reversed, one), None);
    let zero = constant(&mut terms, 0, 8);
    assert_eq!(terms.bv_offset_equality(difference, zero), None);
    assert_eq!(terms.bv_offset_equality(zero, reversed), None);
    // Three words, a doubled word, and a sum of words are not differences.
    let xy = raw(&mut terms, "bvadd", vec![x, y], 8);
    assert_eq!(terms.bv_offset_equality(xy, z), None);
    let xx = raw(&mut terms, "bvadd", vec![x, x], 8);
    assert_eq!(terms.bv_offset_equality(xx, y), None);
    let negated = raw(&mut terms, "bvneg", vec![x], 8);
    assert_eq!(terms.bv_offset_equality(negated, y), None);
    // One surviving word is not a pair. Exact cancellation is a zero
    // difference, whereas a pair of constants still keeps its authored form.
    let x1 = raw(&mut terms, "bvadd", vec![x, one], 8);
    assert_eq!(terms.bv_offset_equality(x1, one), None);
    let cancelled = terms.bv_offset_equality(x1, x).expect("exact cancellation");
    assert_eq!((cancelled.minuend, cancelled.subtrahend), (x, x));
    assert_eq!(cancelled.constant, BigInt::from(255));
    assert!(cancelled.cancels);
    assert_eq!(terms.bv_offset_equality(one, zero), None);
    // Non-bit-vector operands.
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    assert_eq!(terms.bv_offset_equality(p, q), None);
}

#[test]
fn cancelled_words_drop_out() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(16));
    let y = terms.mk_var("y", Sort::bitvec(16));
    let z = terms.mk_var("z", Sort::bitvec(16));
    let xy = raw(&mut terms, "bvadd", vec![x, y], 16);
    let zx = raw(&mut terms, "bvadd", vec![z, x], 16);
    let reading = terms.bv_offset_equality(xy, zx).expect("x cancels");
    assert_eq!(
        (reading.minuend, reading.subtrahend, reading.constant),
        (y, z, BigInt::zero())
    );
}

#[test]
fn exact_full_cancellation_retains_a_real_word_and_constant() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let y = terms.mk_var("y", Sort::bitvec(8));
    let one = constant(&mut terms, 1, 8);
    let two = constant(&mut terms, 2, 8);
    let xy = raw(&mut terms, "bvadd", vec![x, y], 8);
    let yx = raw(&mut terms, "bvadd", vec![y, x], 8);
    let lhs = raw(&mut terms, "bvadd", vec![xy, one], 8);
    let rhs = raw(&mut terms, "bvadd", vec![two, yx], 8);
    let reading = terms
        .bv_offset_equality(lhs, rhs)
        .expect("all words cancel exactly");
    assert_eq!((reading.minuend, reading.subtrahend), (x, x));
    assert_eq!(reading.constant, BigInt::from(1));
    assert!(reading.cancels);
    let flipped = terms
        .bv_offset_equality(rhs, lhs)
        .expect("flipped exact cancellation");
    assert_eq!((flipped.minuend, flipped.subtrahend), (x, x));
    assert_eq!(flipped.constant, BigInt::from(255));

    // A foreign word cannot be claimed cancelled, and a malformed width or
    // non-literal arithmetic operand never borrows the source witness.
    let z = terms.mk_var("z", Sort::bitvec(8));
    let yz = raw(&mut terms, "bvadd", vec![y, z], 8);
    let foreign = terms
        .bv_offset_equality(lhs, yz)
        .expect("two actual survivors");
    assert_ne!(foreign.minuend, foreign.subtrahend);
    let wrong_width = terms.mk_var("wrong_width", Sort::bitvec(16));
    let malformed = raw(&mut terms, "bvadd", vec![x, wrong_width], 8);
    assert_eq!(terms.bv_offset_equality(malformed, x), None);
    let boolean = terms.mk_var("boolean", Sort::Bool);
    let malformed = raw(&mut terms, "bvadd", vec![x, boolean], 8);
    assert_eq!(terms.bv_offset_equality(malformed, x), None);
}

#[test]
fn modular_zero_coefficients_are_not_integer_cancellation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(1));
    let zero = constant(&mut terms, 0, 1);
    let doubled = raw(&mut terms, "bvadd", vec![x, x], 1);
    // 2*x is zero modulo2, but poly_simp preserves the nonzero integer
    // monomial. This new exact cancellation lane must not admit it.
    assert_eq!(terms.bv_offset_equality(doubled, zero), None);
    let negative = raw(&mut terms, "bvneg", vec![doubled], 1);
    assert_eq!(terms.bv_offset_equality(negative, zero), None);
}

#[test]
fn an_oversized_side_is_declined() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(32));
    let y = terms.mk_var("y", Sort::bitvec(32));
    let one = constant(&mut terms, 1, 32);
    let mut chain = x;
    for _ in 0..MAX_OFFSET_WALK {
        chain = raw(&mut terms, "bvadd", vec![chain, one], 32);
    }
    assert_eq!(terms.bv_offset_equality(chain, y), None);
}

/// Every reading is the identity it claims: over all assignments at width 3,
/// `lhs = rhs` holds exactly when `minuend - subtrahend = constant`.
#[test]
fn every_reading_is_exact_at_width_three() {
    const W: u32 = 3;
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(W));
    let y = terms.mk_var("y", Sort::bitvec(W));
    let z = terms.mk_var("z", Sort::bitvec(W));
    let mut sides = vec![x, y, z];
    for value in 0..8 {
        let c = constant(&mut terms, value, W);
        sides.push(c);
        for word in [x, y, z] {
            let plus = raw(&mut terms, "bvadd", vec![c, word], W);
            let minus = raw(&mut terms, "bvsub", vec![word, c], W);
            let from = raw(&mut terms, "bvsub", vec![c, word], W);
            let negated = raw(&mut terms, "bvneg", vec![plus], W);
            sides.extend([plus, minus, from, negated]);
        }
    }
    for (a, b) in [(x, y), (y, z), (x, z)] {
        sides.push(raw(&mut terms, "bvadd", vec![a, b], W));
        sides.push(raw(&mut terms, "bvsub", vec![a, b], W));
    }
    let mut readings = 0;
    for &lhs in &sides {
        for &rhs in &sides {
            let Some(reading) = terms.bv_offset_equality(lhs, rhs) else {
                continue;
            };
            readings += 1;
            assert!(reading.minuend.index() <= reading.subtrahend.index());
            let k = u64::try_from(reading.constant.clone()).expect("narrow constant");
            for vx in 0..8 {
                for vy in 0..8 {
                    for vz in 0..8 {
                        let env = [(x, vx), (y, vy), (z, vz)];
                        let holds = eval(&terms, lhs, &env, W) == eval(&terms, rhs, &env, W);
                        let m = eval(&terms, reading.minuend, &env, W);
                        let s = eval(&terms, reading.subtrahend, &env, W);
                        assert_eq!(holds, m.wrapping_sub(s) & 7 == k, "{lhs:?} = {rhs:?}");
                    }
                }
            }
        }
    }
    assert!(readings > 1000, "only {readings} readings exercised");
}

#[test]
fn full_cancellation_never_hides_malformed_or_unsupported_source_nodes() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(8));
    let zero = constant(&mut terms, 0, 8);
    let unary = raw(&mut terms, "bvadd", vec![x], 8);
    assert_eq!(terms.bv_offset_equality(unary, x), None);
    let opaque = raw(&mut terms, "unsupported", vec![x], 8);
    let from = raw(&mut terms, "bvadd", vec![opaque, zero], 8);
    assert_eq!(
        terms.bv_offset_equality(from, opaque),
        None,
        "an opaque cancelled subtree still requires its ordinary validation"
    );
    for value in [BigInt::from(-1), BigInt::from(256)] {
        let invalid = terms.intern(
            TermData::Const(Constant::BitVec { value, width: 8 }),
            Sort::bitvec(8),
        );
        let left = raw(&mut terms, "bvadd", vec![x, invalid], 8);
        assert_eq!(terms.bv_offset_equality(left, x), None);
    }
}
