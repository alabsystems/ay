// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The word-wise constraint steps: one clause or XOR visit evaluated across
//! all `ENUM_WIDTH` columns at once, plus the column-pattern helpers the
//! block reset installs.
//!
//! Each visit is two passes over the `ENUM_WORDS` words of the constraint's
//! literals. The READ pass computes, per word, the columns where the
//! constraint is satisfied / falsified / unit / still ambiguous, folds the
//! falsified columns into `prop_unsat` and leaves the unit columns in
//! `assign`. The WRITE pass — skipped entirely when no column is unit — then
//! ORs the forced literal in, one literal at a time (a literal and its
//! negation are adjacent by construction, so one `split_at_mut` hands out
//! both halves without aliasing).
//!
//! Width 2 and width 3 are unrolled because that is the whole family (a
//! ternary XOR gate and the AND gate's binaries); everything else takes the
//! generic accumulator path.

use super::*;

/// Immutable view of one literal's column bitset.
#[inline]
fn blk(pos: &[u64], lit: u32) -> &Bits {
    let b = lit as usize * ENUM_WORDS;
    pos[b..b + ENUM_WORDS]
        .try_into()
        .expect("literal bitset slice is ENUM_WORDS long by construction")
}

/// Column pattern of bit `i` of the column index (bit `c` set iff
/// `(c >> i) & 1 == 1`).
pub(super) fn period_pattern(i: u32) -> Bits {
    if i < 6 {
        // Within-word periodic pattern, identical in every word.
        let mut word = 0u64;
        for c in 0..64u32 {
            if (c >> i) & 1 == 1 {
                word |= 1u64 << c;
            }
        }
        return [word; ENUM_WORDS];
    }
    let mut out = [0u64; ENUM_WORDS];
    for (w, slot) in out.iter_mut().enumerate() {
        if ((w as u32) >> (i - 6)) & 1 == 1 {
            *slot = !0;
        }
    }
    out
}

/// Columns `>= 2^bits` (the ones a short support does not reach).
pub(super) fn dead_pattern(bits: u32) -> Bits {
    let mut out = [!0u64; ENUM_WORDS];
    let live = 1usize << bits.min(ENUM_BITS);
    for c in 0..live {
        out[c / 64] &= !(1u64 << (c % 64));
    }
    out
}

/// Result of one constraint visit.
pub(super) struct Step {
    /// Some column propagated (resets the saturation counter).
    pub(super) assigned: bool,
    /// Some column still has >= 2 unassigned literals — requeue.
    pub(super) invalid: bool,
    /// `prop_unsat` is now all ones: the whole block is refuted.
    pub(super) all_refuted: bool,
}

/// Index of the first zero bit, if any.
pub(super) fn first_zero(bits: &Bits) -> Option<usize> {
    for (w, &word) in bits.iter().enumerate() {
        if word != !0 {
            return Some(w * 64 + (!word).trailing_zeros() as usize);
        }
    }
    None
}

/// Mutable pair `(pos[lit], pos[¬lit])` for one literal.
///
/// The two bitsets are adjacent by construction (`lit` and `lit ^ 1` differ in
/// the low bit), so one split of one subslice hands out both halves.
macro_rules! lit_pair_mut {
    ($pos:expr, $lit:expr, $t:ident, $f:ident, $body:block) => {{
        let lit = $lit;
        let base = (lit & !1) as usize * ENUM_WORDS;
        let (lo, hi) = $pos[base..base + 2 * ENUM_WORDS].split_at_mut(ENUM_WORDS);
        let (lo, hi): (&mut Bits, &mut Bits) = (
            lo.try_into()
                .expect("half a literal pair is ENUM_WORDS long"),
            hi.try_into()
                .expect("half a literal pair is ENUM_WORDS long"),
        );
        let ($t, $f) = if lit & 1 == 0 { (lo, hi) } else { (hi, lo) };
        $body
    }};
}

/// OR `mask` into a literal's TRUE bitset (clause propagation).
fn write_clause_lit(pos: &mut [u64], lit: u32, assign: &Bits) -> bool {
    lit_pair_mut!(pos, lit, t, f, {
        let mut wrote = 0u64;
        for w in 0..ENUM_WORDS {
            let m = !(t[w] | f[w]) & assign[w];
            wrote |= m;
            t[w] |= m;
        }
        wrote != 0
    })
}

/// Force a literal to the polarity that makes the XOR odd.
fn write_xor_lit(pos: &mut [u64], lit: u32, assign: &Bits, x: &Bits) -> bool {
    lit_pair_mut!(pos, lit, t, f, {
        let mut wrote = 0u64;
        for w in 0..ENUM_WORDS {
            let m = !(t[w] | f[w]) & assign[w];
            wrote |= m;
            t[w] |= m & !x[w];
            f[w] |= m & x[w];
        }
        wrote != 0
    })
}

/// Mark a dense variable as needing a block reset.
#[inline]
fn touch(dirty: &mut [bool], touched: &mut Vec<u32>, lit: u32) {
    let v = (lit >> 1) as usize;
    if !dirty[v] {
        dirty[v] = true;
        touched.push(v as u32);
    }
}

/// One clause visit over all columns.
pub(super) fn visit_clause(
    pos: &mut [u64],
    lits: &[u32],
    dirty: &mut [bool],
    touched: &mut Vec<u32>,
    prop_unsat: &mut Bits,
    assign: &mut Bits,
) -> Step {
    let mut assign_any = 0u64;
    let mut invalid_any = 0u64;
    let mut refuted = !0u64;
    match lits {
        [l0, l1, l2] => {
            let (p0, n0) = (blk(pos, *l0), blk(pos, *l0 ^ 1));
            let (p1, n1) = (blk(pos, *l1), blk(pos, *l1 ^ 1));
            let (p2, n2) = (blk(pos, *l2), blk(pos, *l2 ^ 1));
            for w in 0..ENUM_WORDS {
                let (a0, b0) = (p0[w], n0[w]);
                let (a1, b1) = (p1[w], n1[w]);
                let (a2, b2) = (p2[w], n2[w]);
                let sat = a0 | a1 | a2;
                let unsat = b0 & b1 & b2;
                let (u0, u1, u2) = (!(a0 | b0), !(a1 | b1), !(a2 | b2));
                let invalid = ((u0 & u1) | (u0 & u2) | (u1 & u2)) & !sat;
                let pu = prop_unsat[w] | unsat;
                prop_unsat[w] = pu;
                refuted &= pu;
                let a = !sat & !invalid & (u0 | u1 | u2);
                assign[w] = a;
                assign_any |= a;
                invalid_any |= invalid;
            }
        }
        [l0, l1] => {
            let (p0, n0) = (blk(pos, *l0), blk(pos, *l0 ^ 1));
            let (p1, n1) = (blk(pos, *l1), blk(pos, *l1 ^ 1));
            for w in 0..ENUM_WORDS {
                let (a0, b0) = (p0[w], n0[w]);
                let (a1, b1) = (p1[w], n1[w]);
                let sat = a0 | a1;
                let unsat = b0 & b1;
                let (u0, u1) = (!(a0 | b0), !(a1 | b1));
                let invalid = u0 & u1 & !sat;
                let pu = prop_unsat[w] | unsat;
                prop_unsat[w] = pu;
                refuted &= pu;
                let a = !sat & !invalid & (u0 | u1);
                assign[w] = a;
                assign_any |= a;
                invalid_any |= invalid;
            }
        }
        _ => {
            let mut sat = [0u64; ENUM_WORDS];
            let mut unsat = [!0u64; ENUM_WORDS];
            let mut unassign = [0u64; ENUM_WORDS];
            let mut invalid = [0u64; ENUM_WORDS];
            for &lit in lits {
                let (p, n) = (blk(pos, lit), blk(pos, lit ^ 1));
                for w in 0..ENUM_WORDS {
                    sat[w] |= p[w];
                    unsat[w] &= n[w];
                    let u = !(p[w] | n[w]);
                    invalid[w] |= unassign[w] & u;
                    unassign[w] |= u;
                }
            }
            for w in 0..ENUM_WORDS {
                let inv = invalid[w] & !sat[w];
                let pu = prop_unsat[w] | unsat[w];
                prop_unsat[w] = pu;
                refuted &= pu;
                let a = !sat[w] & !inv & unassign[w];
                assign[w] = a;
                assign_any |= a;
                invalid_any |= inv;
            }
        }
    }
    if assign_any != 0 {
        for &lit in lits {
            if write_clause_lit(pos, lit, assign) {
                touch(dirty, touched, lit);
            }
        }
    }
    Step {
        assigned: assign_any != 0,
        invalid: invalid_any != 0,
        all_refuted: refuted == !0,
    }
}

/// One XOR visit over all columns ("an odd number of these literals is true").
pub(super) fn visit_xor(
    pos: &mut [u64],
    lits: &[u32],
    dirty: &mut [bool],
    touched: &mut Vec<u32>,
    prop_unsat: &mut Bits,
    assign: &mut Bits,
    xbuf: &mut Bits,
) -> Step {
    let mut assign_any = 0u64;
    let mut invalid_any = 0u64;
    let mut refuted = !0u64;
    match lits {
        [l0, l1, l2] => {
            let (p0, n0) = (blk(pos, *l0), blk(pos, *l0 ^ 1));
            let (p1, n1) = (blk(pos, *l1), blk(pos, *l1 ^ 1));
            let (p2, n2) = (blk(pos, *l2), blk(pos, *l2 ^ 1));
            for w in 0..ENUM_WORDS {
                let (a0, b0) = (p0[w], n0[w]);
                let (a1, b1) = (p1[w], n1[w]);
                let (a2, b2) = (p2[w], n2[w]);
                let x = a0 ^ a1 ^ a2;
                let (u0, u1, u2) = (!(a0 | b0), !(a1 | b1), !(a2 | b2));
                let unassign = u0 | u1 | u2;
                let invalid = (u0 & u1) | (u0 & u2) | (u1 & u2);
                let pu = prop_unsat[w] | (!x & !unassign);
                prop_unsat[w] = pu;
                refuted &= pu;
                let a = !invalid & unassign;
                xbuf[w] = x;
                assign[w] = a;
                assign_any |= a;
                invalid_any |= invalid;
            }
        }
        _ => {
            let mut x = [0u64; ENUM_WORDS];
            let mut unassign = [0u64; ENUM_WORDS];
            let mut invalid = [0u64; ENUM_WORDS];
            for &lit in lits {
                let (p, n) = (blk(pos, lit), blk(pos, lit ^ 1));
                for w in 0..ENUM_WORDS {
                    x[w] ^= p[w];
                    let u = !(p[w] | n[w]);
                    invalid[w] |= unassign[w] & u;
                    unassign[w] |= u;
                }
            }
            for w in 0..ENUM_WORDS {
                let pu = prop_unsat[w] | (!x[w] & !unassign[w]);
                prop_unsat[w] = pu;
                refuted &= pu;
                let a = !invalid[w] & unassign[w];
                xbuf[w] = x[w];
                assign[w] = a;
                assign_any |= a;
                invalid_any |= invalid[w];
            }
        }
    }
    if assign_any != 0 {
        for &lit in lits {
            if write_xor_lit(pos, lit, assign, xbuf) {
                touch(dirty, touched, lit);
            }
        }
    }
    Step {
        assigned: assign_any != 0,
        invalid: invalid_any != 0,
        all_refuted: refuted == !0,
    }
}

/// OR `set_true` into a literal's TRUE bitset and `set_false` into its FALSE
/// bitset (both masks already exclude assigned columns).
fn write_and_lit(pos: &mut [u64], lit: u32, set_true: &Bits, set_false: &Bits) -> bool {
    lit_pair_mut!(pos, lit, t, f, {
        let mut wrote = 0u64;
        for w in 0..ENUM_WORDS {
            wrote |= set_true[w] | set_false[w];
            t[w] |= set_true[w];
            f[w] |= set_false[w];
        }
        wrote != 0
    })
}

/// One AND-gate visit over all columns: `lits = [o, a, b]` with `o <-> a & b`.
///
/// Exactly the unit propagation of the gate's three clauses from one read of
/// the state: `(¬o ∨ a)` and `(¬o ∨ b)` force `a`/`b` true under `o` and `o`
/// false under `¬a`/`¬b`; `(o ∨ ¬a ∨ ¬b)` forces `o` true under `a ∧ b` and
/// `¬a`/`¬b` under `¬o` with the other input true. A column is refuted if
/// any of the three is falsified, and requeued (`invalid`) if any is
/// unsatisfied with two literals unassigned, the clause visits' own rule. In
/// a consistent column no two forced writes contradict each other (each pair
/// would need a variable both true and false), so one visit reaches the same
/// fixpoint the three clause visits would, in one pass over three literals.
pub(super) fn visit_and(
    pos: &mut [u64],
    lits: &[u32],
    dirty: &mut [bool],
    touched: &mut Vec<u32>,
    prop_unsat: &mut Bits,
) -> Step {
    let (o, a, b) = (lits[0], lits[1], lits[2]);
    let mut m = [[0u64; ENUM_WORDS]; 6]; // o_t, o_f, a_t, a_f, b_t, b_f
    let mut assign_any = 0u64;
    let mut invalid_any = 0u64;
    let mut refuted = !0u64;
    {
        let (po_, no_) = (blk(pos, o), blk(pos, o ^ 1));
        let (pa_, na_) = (blk(pos, a), blk(pos, a ^ 1));
        let (pb_, nb_) = (blk(pos, b), blk(pos, b ^ 1));
        for w in 0..ENUM_WORDS {
            let (po, no) = (po_[w], no_[w]);
            let (pa, na) = (pa_[w], na_[w]);
            let (pb, nb) = (pb_[w], nb_[w]);
            let (uo, ua, ub) = (!(po | no), !(pa | na), !(pb | nb));
            let unsat = (po & (na | nb)) | (no & pa & pb);
            let pu = prop_unsat[w] | unsat;
            prop_unsat[w] = pu;
            refuted &= pu;
            let sat3 = po | na | nb;
            let invalid = (uo & ua) | (uo & ub) | (((ua & ub) | (uo & (ua | ub))) & !sat3);
            let o_t = pa & pb & uo;
            let o_f = (na | nb) & uo;
            let a_t = po & ua;
            let a_f = no & pb & ua;
            let b_t = po & ub;
            let b_f = no & pa & ub;
            m[0][w] = o_t;
            m[1][w] = o_f;
            m[2][w] = a_t;
            m[3][w] = a_f;
            m[4][w] = b_t;
            m[5][w] = b_f;
            assign_any |= o_t | o_f | a_t | a_f | b_t | b_f;
            invalid_any |= invalid;
        }
    }
    if assign_any != 0 {
        for (lit, (t, f)) in [(o, (0, 1)), (a, (2, 3)), (b, (4, 5))] {
            if write_and_lit(pos, lit, &m[t], &m[f]) {
                touch(dirty, touched, lit);
            }
        }
    }
    Step {
        assigned: assign_any != 0,
        invalid: invalid_any != 0,
        all_refuted: refuted == !0,
    }
}
