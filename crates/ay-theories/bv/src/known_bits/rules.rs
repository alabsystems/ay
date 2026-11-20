// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Known-bits transfer rules, each stated in both directions.
//!
//! A rule never derives more than unit propagation derives on the
//! bit-level encoding that [`super::replay`] checks: the rules are what makes
//! a region's verdict cheap, and the encoding is what makes it checkable. The
//! forward half of a rule refines the node from its operands; the backward
//! half refines each operand from the node and the other operands.
//!
//! Every value has width `1..=64`; bits above the width are always clear.
//! A conflict is a bit set in both `zero` and `one`; rules do not detect it,
//! the engine does when it merges a rule's contribution.

/// What is known about the bits of one value: bits set in `zero` are known
/// 0, bits set in `one` are known 1.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, Hash)]
pub struct KnownBits {
    /// Bits known to be 0.
    pub zero: u64,
    /// Bits known to be 1.
    pub one: u64,
}

impl KnownBits {
    /// Nothing known.
    pub const UNKNOWN: Self = Self { zero: 0, one: 0 };

    /// The fully known value `value` of width `width`.
    #[must_use]
    pub fn constant(value: u64, width: u32) -> Self {
        let m = mask(width);
        Self {
            zero: !value & m,
            one: value & m,
        }
    }

    /// Bits whose value is known.
    #[must_use]
    pub fn known(self) -> u64 {
        self.zero | self.one
    }

    /// True when some bit is known to be both 0 and 1.
    #[must_use]
    pub fn is_conflict(self) -> bool {
        self.zero & self.one != 0
    }

    /// True when every bit below `width` is known.
    #[must_use]
    pub fn is_fully_known(self, width: u32) -> bool {
        self.known() & mask(width) == mask(width)
    }

    /// Both facts.
    #[must_use]
    pub fn union(self, other: Self) -> Self {
        Self {
            zero: self.zero | other.zero,
            one: self.one | other.one,
        }
    }

    /// The bitwise complement's knowledge.
    #[must_use]
    pub fn complement(self) -> Self {
        Self {
            zero: self.one,
            one: self.zero,
        }
    }

    /// Knowledge with the bits in `bits` complemented.
    #[must_use]
    pub fn flip(self, bits: u64) -> Self {
        Self {
            zero: (self.zero & !bits) | (self.one & bits),
            one: (self.one & !bits) | (self.zero & bits),
        }
    }

    /// Knowledge restricted to `bits`.
    #[must_use]
    pub fn restrict(self, bits: u64) -> Self {
        Self {
            zero: self.zero & bits,
            one: self.one & bits,
        }
    }

    /// True when `value` agrees with every known bit.
    #[must_use]
    pub fn admits(self, value: u64) -> bool {
        value & self.zero == 0 && !value & self.one == 0
    }
}

/// The low `width` bits set; `width` is `0..=64`.
#[must_use]
pub fn mask(width: u32) -> u64 {
    if width >= 64 {
        u64::MAX
    } else {
        (1u64 << width) - 1
    }
}

/// Bitwise complement: forward.
#[must_use]
pub fn not_fwd(a: KnownBits) -> KnownBits {
    a.complement()
}

/// Bitwise complement: backward to the operand.
#[must_use]
pub fn not_bwd(z: KnownBits) -> KnownBits {
    z.complement()
}

/// Bitwise and: forward.
#[must_use]
pub fn and_fwd(a: KnownBits, b: KnownBits) -> KnownBits {
    KnownBits {
        zero: a.zero | b.zero,
        one: a.one & b.one,
    }
}

/// Bitwise and: backward to `a`, given the result `z` and the other operand
/// `b`. A 1 in `z` forces both operands; a 0 in `z` forces `a` where `b` is 1.
#[must_use]
pub fn and_bwd(z: KnownBits, b: KnownBits) -> KnownBits {
    KnownBits {
        zero: z.zero & b.one,
        one: z.one,
    }
}

/// Bitwise or: forward.
#[must_use]
pub fn or_fwd(a: KnownBits, b: KnownBits) -> KnownBits {
    KnownBits {
        zero: a.zero & b.zero,
        one: a.one | b.one,
    }
}

/// Bitwise or: backward to `a`, given `z` and the other operand `b`.
#[must_use]
pub fn or_bwd(z: KnownBits, b: KnownBits) -> KnownBits {
    KnownBits {
        zero: z.zero,
        one: z.one & b.zero,
    }
}

/// Bitwise exclusive or over `width` bits: forward, and also backward (the
/// relation is symmetric: any two of `a`, `b`, `a ^ b` give the third).
#[must_use]
pub fn xor_fwd(a: KnownBits, b: KnownBits, width: u32) -> KnownBits {
    let both = a.known() & b.known();
    let value = a.one ^ b.one;
    KnownBits {
        zero: !value & both & mask(width),
        one: value & both,
    }
}

/// If-then-else with a one-bit condition: forward. A known condition selects
/// its branch; an unknown one keeps the bits on which both branches agree.
#[must_use]
pub fn ite_fwd(c: KnownBits, t: KnownBits, e: KnownBits) -> KnownBits {
    if c.one & 1 != 0 {
        t
    } else if c.zero & 1 != 0 {
        e
    } else {
        KnownBits {
            zero: t.zero & e.zero,
            one: t.one & e.one,
        }
    }
}

/// If-then-else: backward to the condition. A result that contradicts a
/// branch rules that branch out.
#[must_use]
pub fn ite_bwd_cond(z: KnownBits, t: KnownBits, e: KnownBits) -> KnownBits {
    let refutes_then = (z.one & t.zero) | (z.zero & t.one) != 0;
    let refutes_else = (z.one & e.zero) | (z.zero & e.one) != 0;
    KnownBits {
        zero: u64::from(refutes_then),
        one: u64::from(refutes_else),
    }
}

/// If-then-else: backward to the branch selected by `select` (1 for the
/// then-branch, 0 for the else-branch), given the condition `c`.
#[must_use]
pub fn ite_bwd_branch(z: KnownBits, c: KnownBits, select: u64) -> KnownBits {
    let taken = if select == 1 { c.one } else { c.zero };
    if taken & 1 != 0 {
        z
    } else {
        KnownBits::UNKNOWN
    }
}

/// Equality of two `width`-bit values as a one-bit result: forward. A known
/// differing bit makes it 0; every bit known and equal makes it 1.
#[must_use]
pub fn eq_fwd(a: KnownBits, b: KnownBits, width: u32) -> KnownBits {
    let differ = (a.one & b.zero) | (a.zero & b.one);
    let same = (a.one & b.one) | (a.zero & b.zero);
    if differ != 0 {
        KnownBits { zero: 1, one: 0 }
    } else if same & mask(width) == mask(width) {
        KnownBits { zero: 0, one: 1 }
    } else {
        KnownBits::UNKNOWN
    }
}

/// Equality: backward to `a`, given the one-bit result `z` and the other
/// operand `b`. Equal operands share their known bits; unequal operands
/// that agree everywhere but one bit differ there.
#[must_use]
pub fn eq_bwd(z: KnownBits, a: KnownBits, b: KnownBits, width: u32) -> KnownBits {
    if z.one & 1 != 0 {
        return b;
    }
    if z.zero & 1 == 0 {
        return KnownBits::UNKNOWN;
    }
    let differ = (a.one & b.zero) | (a.zero & b.one);
    let same = (a.one & b.one) | (a.zero & b.zero);
    let open = mask(width) & !same;
    if differ != 0 || open.count_ones() != 1 || b.known() & open == 0 {
        return KnownBits::UNKNOWN;
    }
    KnownBits {
        zero: b.one & open,
        one: b.zero & open,
    }
}

/// Logical shift left by a fully known amount `amount`: forward.
#[must_use]
pub fn shl_fwd(a: KnownBits, amount: u64, width: u32) -> KnownBits {
    let m = mask(width);
    if amount >= u64::from(width) {
        return KnownBits { zero: m, one: 0 };
    }
    let k = amount as u32;
    KnownBits {
        zero: ((a.zero << k) | mask(k)) & m,
        one: (a.one << k) & m,
    }
}

/// Logical shift left by a fully known amount: backward to the shifted value.
#[must_use]
pub fn shl_bwd(z: KnownBits, amount: u64, width: u32) -> KnownBits {
    if amount >= u64::from(width) {
        return KnownBits::UNKNOWN;
    }
    let k = amount as u32;
    KnownBits {
        zero: z.zero >> k,
        one: z.one >> k,
    }
}

/// Logical shift right by a fully known amount: forward.
#[must_use]
pub fn lshr_fwd(a: KnownBits, amount: u64, width: u32) -> KnownBits {
    let m = mask(width);
    if amount >= u64::from(width) {
        return KnownBits { zero: m, one: 0 };
    }
    let k = amount as u32;
    KnownBits {
        zero: (a.zero >> k) | (m & !(m >> k)),
        one: a.one >> k,
    }
}

/// Logical shift right by a fully known amount: backward.
#[must_use]
pub fn lshr_bwd(z: KnownBits, amount: u64, width: u32) -> KnownBits {
    let m = mask(width);
    if amount >= u64::from(width) {
        return KnownBits::UNKNOWN;
    }
    let k = amount as u32;
    KnownBits {
        zero: (z.zero << k) & m,
        one: (z.one << k) & m,
    }
}

/// Arithmetic shift right by a fully known amount: forward. An amount at or
/// past the width fills every bit with the sign, as a shift by `width - 1`.
#[must_use]
pub fn ashr_fwd(a: KnownBits, amount: u64, width: u32) -> KnownBits {
    let m = mask(width);
    let k = amount.min(u64::from(width - 1)) as u32;
    let sign = 1u64 << (width - 1);
    let fill = m & !(m >> k);
    KnownBits {
        zero: (a.zero >> k) | if a.zero & sign != 0 { fill } else { 0 },
        one: (a.one >> k) | if a.one & sign != 0 { fill } else { 0 },
    }
}

/// Arithmetic shift right by a fully known amount: backward. Every result
/// bit at or above `width - 1 - k` is a copy of the sign bit.
#[must_use]
pub fn ashr_bwd(z: KnownBits, amount: u64, width: u32) -> KnownBits {
    let m = mask(width);
    let k = amount.min(u64::from(width - 1)) as u32;
    let sign = 1u64 << (width - 1);
    let copies = m & !mask(width - 1 - k);
    KnownBits {
        zero: ((z.zero << k) & m) | if z.zero & copies != 0 { sign } else { 0 },
        one: ((z.one << k) & m) | if z.one & copies != 0 { sign } else { 0 },
    }
}

/// `((_ extract hi lo) a)`: forward. `width` is the result width.
#[must_use]
pub fn extract_fwd(a: KnownBits, lo: u32, width: u32) -> KnownBits {
    let m = mask(width);
    KnownBits {
        zero: (a.zero >> lo) & m,
        one: (a.one >> lo) & m,
    }
}

/// `((_ extract hi lo) a)`: backward.
#[must_use]
pub fn extract_bwd(z: KnownBits, lo: u32) -> KnownBits {
    KnownBits {
        zero: z.zero << lo,
        one: z.one << lo,
    }
}

/// `(concat a b)` with `b` of width `low_width` in the low bits: forward.
#[must_use]
pub fn concat_fwd(a: KnownBits, b: KnownBits, low_width: u32) -> KnownBits {
    KnownBits {
        zero: (a.zero << low_width) | b.zero,
        one: (a.one << low_width) | b.one,
    }
}

/// `(concat a b)`: backward to the high operand `a`.
#[must_use]
pub fn concat_bwd_high(z: KnownBits, low_width: u32) -> KnownBits {
    KnownBits {
        zero: z.zero >> low_width,
        one: z.one >> low_width,
    }
}

/// `(concat a b)`: backward to the low operand `b` of width `low_width`.
#[must_use]
pub fn concat_bwd_low(z: KnownBits, low_width: u32) -> KnownBits {
    z.restrict(mask(low_width))
}

/// `((_ zero_extend n) a)` from `from_width` to `width`: forward.
#[must_use]
pub fn zext_fwd(a: KnownBits, from_width: u32, width: u32) -> KnownBits {
    KnownBits {
        zero: a.zero | (mask(width) & !mask(from_width)),
        one: a.one,
    }
}

/// `((_ sign_extend n) a)` from `from_width` to `width`: forward.
#[must_use]
pub fn sext_fwd(a: KnownBits, from_width: u32, width: u32) -> KnownBits {
    let sign = 1u64 << (from_width - 1);
    let fill = mask(width) & !mask(from_width);
    KnownBits {
        zero: a.zero | if a.zero & sign != 0 { fill } else { 0 },
        one: a.one | if a.one & sign != 0 { fill } else { 0 },
    }
}

/// `((_ sign_extend n) a)`: backward. Every result bit at or above
/// `from_width - 1` is a copy of the operand's sign bit.
#[must_use]
pub fn sext_bwd(z: KnownBits, from_width: u32, width: u32) -> KnownBits {
    let sign = 1u64 << (from_width - 1);
    let copies = mask(width) & !mask(from_width - 1);
    let low = z.restrict(mask(from_width));
    KnownBits {
        zero: low.zero | if z.zero & copies != 0 { sign } else { 0 },
        one: low.one | if z.one & copies != 0 { sign } else { 0 },
    }
}

/// The operands of a ripple-carry chain `x + y + carry_in`, with the sum
/// `sum` when the chain is an adder (comparators use only the carry out).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CarryChain {
    /// First addend.
    pub x: KnownBits,
    /// Second addend.
    pub y: KnownBits,
    /// The sum's bits, when the chain has one.
    pub sum: Option<KnownBits>,
    /// The carry out of the top bit, as a one-bit value.
    pub carry_out: KnownBits,
}

/// Unit propagation to a fixpoint through the full-adder chain
/// `x + y + carry_in` of `width` bits: per bit, `sum = x ^ y ^ c` (any three
/// of the four give the fourth) and `c' = maj(x, y, c)` (two equal inputs
/// give the output; an output contradicted by one input forces the other
/// two). These are exactly the literals unit propagation derives on the
/// chain's XOR3 and six-clause majority encoding. The carries are internal:
/// they are re-derived on every call, so the result depends only on the
/// chain's operands.
///
/// Every bit position is propagated at once, one 64-bit word per literal
/// polarity, until a pass changes nothing. Unit propagation has one least
/// fixpoint, so the result does not depend on the schedule; the compiled
/// region runs the same word program. `None` is a contradiction: no operands
/// consistent with the input knowledge satisfy the chain.
#[must_use]
pub fn carry_chain_closure(chain: CarryChain, carry_in: bool, width: u32) -> Option<CarryChain> {
    let words = ChainWords::new(chain, carry_in, width);
    let closed = words.close(width)?;
    Some(closed.finish(chain.sum.is_some(), width))
}

/// The chain's knowledge as words: `x`, `y`, `sum`; `c` holds the carry into
/// each position (bit 0 is the carry in), `d` the carry out of each position
/// (bit `width - 1` is the chain's carry out). `d` bit `j` and `c` bit
/// `j + 1` are one variable.
#[derive(Clone, Copy, PartialEq, Eq)]
struct ChainWords {
    /// Known zeros, in the order x, y, sum, c, d.
    zero: [u64; 5],
    /// Known ones, in the same order.
    one: [u64; 5],
    /// Whether the chain has a sum.
    has_sum: bool,
}

const X: usize = 0;
const Y: usize = 1;
const S: usize = 2;
const C: usize = 3;
const D: usize = 4;

impl ChainWords {
    fn new(chain: CarryChain, carry_in: bool, width: u32) -> Self {
        let top = 1u64 << (width - 1);
        let sum = chain.sum.unwrap_or_default();
        let (cz, co) = if carry_in { (0, 1) } else { (1, 0) };
        let dz = if chain.carry_out.zero & 1 != 0 {
            top
        } else {
            0
        };
        let d1 = if chain.carry_out.one & 1 != 0 { top } else { 0 };
        Self {
            zero: [chain.x.zero, chain.y.zero, sum.zero, cz, dz],
            one: [chain.x.one, chain.y.one, sum.one, co, d1],
            has_sum: chain.sum.is_some(),
        }
    }

    fn is_conflict(&self) -> bool {
        (0..5).any(|i| self.zero[i] & self.one[i] != 0)
    }

    /// One pass of every rule over every position.
    fn pass(&mut self, width: u32) {
        let m = mask(width);
        let below_top = mask(width - 1);
        let (z, o) = (&mut self.zero, &mut self.one);
        // The carry out of position j is the carry into j + 1.
        z[C] |= (z[D] << 1) & m;
        o[C] |= (o[D] << 1) & m;
        z[D] |= (z[C] >> 1) & below_top;
        o[D] |= (o[C] >> 1) & below_top;
        // Sum: any three of x, y, c, s give the fourth.
        if self.has_sum {
            let known: [u64; 5] = std::array::from_fn(|i| z[i] | o[i]);
            for (target, a, b, c) in [(S, X, Y, C), (C, X, Y, S), (Y, X, C, S), (X, Y, C, S)] {
                let fixed = known[a] & known[b] & known[c];
                let value = o[a] ^ o[b] ^ o[c];
                o[target] |= fixed & value;
                z[target] |= fixed & !value;
            }
        }
        // Majority forward: two equal known inputs give the carry out.
        o[D] |= (o[X] & o[Y]) | (o[X] & o[C]) | (o[Y] & o[C]);
        z[D] |= (z[X] & z[Y]) | (z[X] & z[C]) | (z[Y] & z[C]);
        // Majority backward: a carry out contradicted by one input forces the
        // other two to the carry out's value.
        let (d1, d0) = (o[D], z[D]);
        let (x0, y0, c0, x1, y1, c1) = (z[X], z[Y], z[C], o[X], o[Y], o[C]);
        o[Y] |= d1 & (x0 | c0);
        o[X] |= d1 & (y0 | c0);
        o[C] |= d1 & (x0 | y0);
        z[Y] |= d0 & (x1 | c1);
        z[X] |= d0 & (y1 | c1);
        z[C] |= d0 & (x1 | y1);
    }

    /// Passes until nothing changes; `None` on a contradiction.
    fn close(mut self, width: u32) -> Option<Self> {
        loop {
            if self.is_conflict() {
                return None;
            }
            let before = self;
            self.pass(width);
            if self == before {
                return Some(self);
            }
        }
    }

    fn finish(self, has_sum: bool, width: u32) -> CarryChain {
        let top = width - 1;
        let get = |i: usize| KnownBits {
            zero: self.zero[i],
            one: self.one[i],
        };
        CarryChain {
            x: get(X),
            y: get(Y),
            sum: has_sum.then(|| get(S)),
            carry_out: KnownBits {
                zero: (self.zero[D] >> top) & 1,
                one: (self.one[D] >> top) & 1,
            },
        }
    }
}

/// The comparison's chain operands: `a < b` (or `<=` with carry in 1) is the
/// carry out of `~a + b`; the signed forms flip both sign bits first.
#[must_use]
pub fn compare_operands(
    a: KnownBits,
    b: KnownBits,
    signed: bool,
    width: u32,
) -> (KnownBits, KnownBits) {
    let sign = if signed { 1u64 << (width - 1) } else { 0 };
    (
        a.complement().restrict(mask(width)).flip(sign),
        b.flip(sign),
    )
}

/// Inverse of [`compare_operands`] for the chain's refined operands.
#[must_use]
pub fn compare_results(
    x: KnownBits,
    y: KnownBits,
    signed: bool,
    width: u32,
) -> (KnownBits, KnownBits) {
    let sign = if signed { 1u64 << (width - 1) } else { 0 };
    (
        x.flip(sign).complement().restrict(mask(width)),
        y.flip(sign),
    )
}
