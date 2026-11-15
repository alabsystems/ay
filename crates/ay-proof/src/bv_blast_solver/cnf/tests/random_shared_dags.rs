// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The memoized encoder builds the per-occurrence CNF on random, heavily
//! shared expressions over EVERY `BvExpr` operator and over constants — not
//! only the add/xor/mul/or shape `shared_blast.rs` checks. A node memo keyed
//! too coarsely (for instance one that forgot a constant's value) would hand
//! one node's bits to a different node; this compares the two encoders'
//! complete CNFs instead of trusting the key.
//!
//! A test, not a proof: 400 seeds, each checked on its two sides and on one
//! side against itself. Adversarial probe of the 2026-09-29 challenge,
//! landed after its review.

use super::*;

/// xorshift64: deterministic, so a failing seed reproduces.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }

    fn pick(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

/// Two roots over one pool of 8-, 4- and 1-bit expressions that `steps`
/// random operators grow; every operand is a clone of an earlier member, so
/// structurally equal subtrees recur throughout both roots.
fn random_pair(seed: u64, steps: usize) -> (BvExpr, BvExpr) {
    let mut rng = Rng(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1);
    let mut w8 = vec![
        BvExpr::leaf("a", 8),
        BvExpr::leaf("b", 8),
        BvExpr::const_val(0x80, 8),
        BvExpr::const_val(3, 8),
    ];
    let mut w4 = vec![BvExpr::leaf("c", 4), BvExpr::const_val(9, 4)];
    let mut w1 = vec![BvExpr::leaf("p", 1)];
    for _ in 0..steps {
        let x = w8[rng.pick(w8.len())].clone();
        let y = w8[rng.pick(w8.len())].clone();
        let half = w4[rng.pick(w4.len())].clone();
        let bit = w1[rng.pick(w1.len())].clone();
        match rng.pick(21) {
            0 => w8.push(BvExpr::add(x, y)),
            1 => w8.push(BvExpr::sub(x, y)),
            2 => w8.push(BvExpr::mul(x, y)),
            3 => w8.push(BvExpr::and(x, y)),
            4 => w8.push(BvExpr::or(x, y)),
            5 => w8.push(BvExpr::xor(x, y)),
            6 => w8.push(BvExpr::not(x)),
            7 => w8.push(BvExpr::shl(x, y)),
            8 => w8.push(BvExpr::lshr(x, BvExpr::const_val(rng.pick(9) as u128, 8))),
            9 => w8.push(BvExpr::ashr(x, y)),
            10 => w8.push(BvExpr::udiv(x, y)),
            11 => w8.push(BvExpr::urem(x, y)),
            12 => w8.push(BvExpr::zero_ext(half, 4)),
            13 => w8.push(BvExpr::sign_ext(half, 4)),
            14 => w4.push(BvExpr::extract(x, 7, 4)),
            15 => w4.push(BvExpr::extract(x, 3, 0)),
            16 => w1.push(BvExpr::eq(x, y)),
            17 => w1.push(BvExpr::Ult(Box::new(x), Box::new(y))),
            18 => w1.push(BvExpr::carry_out_add(x, y)),
            19 => w1.push(BvExpr::carry_out_sub(x, y)),
            _ => w8.push(BvExpr::zero_ext(bit, 7)),
        }
    }
    let last = w8.len() - 1;
    let lhs = BvExpr::xor(w8[last].clone(), w8[rng.pick(w8.len())].clone());
    let rhs = BvExpr::add(w8[rng.pick(w8.len())].clone(), w8[last].clone());
    (lhs, rhs)
}

#[test]
fn the_memoized_cnf_is_the_per_occurrence_cnf_on_random_shared_dags() {
    let (mut compared, mut heavily_shared) = (0, 0);
    for seed in 1..=400_u64 {
        let (lhs, rhs) = random_pair(seed, 6 + (seed as usize % 18));
        for (left, right) in [(&lhs, &rhs), (&lhs, &lhs)] {
            let preflight = preflight_bv_equality(left, right, &limits(), &mut || true)
                .unwrap_or_else(|error| panic!("seed {seed}: preflight refused: {error:?}"));
            if preflight.occurrences > 2 * preflight.nodes {
                heavily_shared += 1;
            }
            let memoized = build(left, right, Some((&limits(), preflight)), &mut || true)
                .unwrap_or_else(|error| panic!("seed {seed}: memoized encoder refused: {error:?}"));
            let unshared = build(left, right, None, &mut || true)
                .unwrap_or_else(|error| panic!("seed {seed}: unshared encoder refused: {error:?}"));
            assert_eq!(memoized, unshared, "seed {seed}: the memoized CNF differs");
            compared += 1;
        }
    }
    assert_eq!(compared, 800);
    // Most pairs repeat structure heavily (491 of 800 when written).
    assert!(
        heavily_shared > 400,
        "{heavily_shared} heavily shared pairs"
    );
}
