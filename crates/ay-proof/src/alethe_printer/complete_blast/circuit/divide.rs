// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The checkers' long-division circuits (`bitblast_udiv` / `bitblast_urem`),
//! spelled term for term like the rest of [`super`].
//!
//! The two checkers AY is replayed with build DIFFERENT dividers
//! (`super::super::super::dialect`), and only Clean's is `bvudiv`/`bvurem`:
//!
//! * Clean `5390f432b8` (DOWNSTREAM.md fix 1) compares against the carry OUT
//!   of the top bit and replaces the remainder by the difference `r - y`
//!   when `r >= y`.
//! * Pinned Carcara 9a352ee compares against the carry INTO the top bit (its
//!   `ripple_carry_adder` returns `carries[size - 1]`) and replaces the
//!   remainder by ALL ONES (`(ite sign bit true)`). That circuit is false for
//!   most operand pairs: `(bvudiv #x80 #x02)` evaluates to `#x00`, and for
//!   every non-zero divisor some dividend is divided wrongly. Pinned Carcara
//!   accepts it all the same, because it compares the terms, not their
//!   meaning. AY prints it only where it is true (`super::super::division`).

use super::{Circuit, GateKind, SRef, MAX_CIRCUIT_BITS};

/// Which checker's long-division circuit a divider step spells.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in super::super) enum Divider {
    /// Clean `5390f432b8`'s fixed divider: SMT-LIB's quotient and remainder
    /// for every operand pair (the default dialect's spelling).
    Clean,
    /// Pinned Carcara 9a352ee's divider: true only on the domain
    /// `super::super::division::pinned_divider_is_true` admits.
    Pinned,
}

impl Circuit {
    /// carcara `ripple_carry_adder` WITH its incoming carry: `carries[0]` is
    /// `carry_in` (or `false`), `carry_i` is
    /// `(or (and x_{i-1} y_{i-1}) (and (xor x_{i-1} y_{i-1}) carry_{i-1}))`,
    /// and `res_i` is `(xor (xor x_i y_i) carry_i)`. The carry returned is the
    /// carry OUT of the top bit, `carries[size]`, for [`Divider::Clean`] (as
    /// clean `5390f432b8` returns it, DOWNSTREAM.md fix 1), and the carry INTO
    /// the top bit, `carries[size - 1]`, for [`Divider::Pinned`] (pinned
    /// 9a352ee builds no carry past it).
    fn ripple_carry_adder_carrying(
        &mut self,
        x: &[SRef],
        y: &[SRef],
        carry_in: Option<SRef>,
        divider: Divider,
    ) -> Option<(Vec<SRef>, SRef)> {
        let size = x.len();
        if size == 0 || size > MAX_CIRCUIT_BITS || y.len() != size {
            return None;
        }
        let last = match divider {
            Divider::Clean => size,
            Divider::Pinned => size - 1,
        };
        let mut carries = Vec::with_capacity(last + 1);
        carries.push(match carry_in {
            Some(carry) => carry,
            None => self.constant(false),
        });
        for i in 1..=last {
            let generate = self.and(vec![x[i - 1], y[i - 1]]);
            let propagate = self.xor(x[i - 1], y[i - 1]);
            let carried = self.and(vec![propagate, carries[i - 1]]);
            carries.push(self.or(vec![generate, carried]));
        }
        let mut out = Vec::with_capacity(size);
        for i in 0..size {
            let half = self.xor(x[i], y[i]);
            out.push(self.xor(half, carries[i]));
        }
        Some((out, carries[last]))
    }

    /// carcara `bitblast_udiv_urem`: the quotient and remainder bits the
    /// `divider`'s checker expects for `(bvudiv x y)` / `(bvurem x y)`, TERM
    /// FOR TERM. A zero divisor gives the all-ones quotient and the dividend
    /// as remainder, via `(ite (and (= y_0 false) ..) ..)`, in both.
    ///
    /// `None` below two bits: the checker spells a one-bit `y_is_zero` as a
    /// unary `(and ..)`, which this DAG does not build.
    pub(in super::super) fn udiv_urem_spelled(
        &mut self,
        x: &[SRef],
        y: &[SRef],
        divider: Divider,
    ) -> Option<(Vec<SRef>, Vec<SRef>)> {
        let size = x.len();
        if size < 2 || size > MAX_CIRCUIT_BITS || y.len() != size {
            return None;
        }
        let (quot, rem) = self.udiv_urem_rec(x, y, size, divider)?;
        let false_ref = self.constant(false);
        let true_ref = self.constant(true);
        let mut zero_tests = Vec::with_capacity(size);
        for yi in y {
            zero_tests.push(self.iff(*yi, false_ref));
        }
        let y_is_zero = self.and(zero_tests);
        let mut out_quot = Vec::with_capacity(size);
        for q in quot {
            out_quot.push(self.ite(y_is_zero, true_ref, q));
        }
        let mut out_rem = Vec::with_capacity(size);
        for (r, xi) in rem.into_iter().zip(x) {
            out_rem.push(self.ite(y_is_zero, *xi, r));
        }
        Some((out_quot, out_rem))
    }

    /// carcara `bitblast_udiv_urem_rec`: long division, one dividend bit per
    /// level. Its base case is SYNTACTIC — every dividend bit the literal
    /// `false` (the checker's `is_bool_false`) — and the recursion shifts in
    /// literal `false` bits, so both are mirrored exactly. That base case is
    /// the only place either divider reads the SPELLING of an operand rather
    /// than its value.
    fn udiv_urem_rec(
        &mut self,
        x: &[SRef],
        y: &[SRef],
        n: usize,
        divider: Divider,
    ) -> Option<(Vec<SRef>, Vec<SRef>)> {
        let size = x.len();
        let false_ref = self.constant(false);
        let literally_false = |circuit: &Self, bit: &SRef| {
            bit.nots == 0 && matches!(circuit.kind(bit.gate), GateKind::Const(false))
        };
        if n == 0 || x.iter().all(|bit| literally_false(self, bit)) {
            return Some((vec![false_ref; size], vec![false_ref; size]));
        }
        // `shift_right`: bit i takes bit i+1, the top bit becomes `false`.
        let mut shifted = x[1..].to_vec();
        shifted.push(false_ref);
        let (mut q1, mut r1) = self.udiv_urem_rec(&shifted, y, n - 1, divider)?;
        // `shift_left`: bit 0 becomes `false`, bit i takes bit i-1.
        q1.pop();
        q1.insert(0, false_ref);
        r1.pop();
        r1.insert(0, false_ref);

        let true_ref = self.constant(true);
        let low_is_true = self.iff(x[0], true_ref);
        let one_if_odd = self.ite(low_is_true, true_ref, false_ref);
        let zeros = vec![false_ref; size];
        let (mut r1_shift_add, _) =
            self.ripple_carry_adder_carrying(&r1, &zeros, Some(one_if_odd), divider)?;
        let not_y = y.iter().map(|bit| bit.not()).collect::<Option<Vec<_>>>()?;
        let (r_minus_y, carry_1) =
            self.ripple_carry_adder_carrying(&r1_shift_add, &not_y, Some(true_ref), divider)?;
        let sign = carry_1.not()?;
        q1[0] = self.ite(sign, q1[0], true_ref);
        for (bit, difference) in r1_shift_add.iter_mut().zip(r_minus_y) {
            // Clean keeps the difference; pinned 9a352ee fills with `true`.
            let otherwise = match divider {
                Divider::Clean => difference,
                Divider::Pinned => true_ref,
            };
            *bit = self.ite(sign, *bit, otherwise);
        }
        let (_, carry_2) = self.ripple_carry_adder_carrying(x, &not_y, Some(true_ref), divider)?;
        let x_lt_y = carry_2.not()?;
        let mut quot = Vec::with_capacity(size);
        let mut rem = Vec::with_capacity(size);
        for i in 0..size {
            quot.push(self.ite(x_lt_y, false_ref, q1[i]));
            rem.push(self.ite(x_lt_y, x[i], r1_shift_add[i]));
        }
        Some((quot, rem))
    }
}
