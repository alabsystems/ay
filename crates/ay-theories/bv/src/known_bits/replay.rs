// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Independent replay of a region's refutation.
//!
//! A region that ends in a contradiction claims the assertions have no
//! model. This module checks that claim without the region: it encodes the
//! assertions to clauses with its own bit-blaster, written against SMT-LIB
//! semantics and sharing no code with the transfer rules or the cone
//! builder, and asks `ay-drat-check` to derive the empty clause by reverse
//! unit propagation. The region's rules never derive more than unit
//! propagation derives on this encoding, so every sound region refutation
//! replays; a rule that overreached, or a cone built wrong, fails here and
//! the verdict is not accepted.
//!
//! Terms this encoder does not interpret (wider than [`MAX_REPLAY_WIDTH`],
//! or outside its vocabulary) get fresh, unconstrained bits: the clauses then
//! describe a weakening of the assertions, whose refutation still refutes
//! them. Integers certified by [`super::ints::IntRanges`] are encoded as
//! 64-bit two's-complement values; that certification (interval arithmetic
//! over the top-level bounds) is the one piece the replay shares with the
//! cone, and its soundness is tested against brute-force evaluation.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::Sort;
use ay_drat_check::checker::DratChecker;
use ay_drat_check::ConcludeResult;
use ay_proof_common::literal::{Literal, Variable};
use num_bigint::BigInt;

use super::ints::{int_constant, pattern_bigint, IntRanges, INT_WIDTH};

/// Widest bit-vector term the encoder interprets.
pub const MAX_REPLAY_WIDTH: u32 = 64;

/// What a successful replay checked.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct ReplayStats {
    /// Variables in the encoding.
    pub variables: usize,
    /// Clauses in the encoding.
    pub clauses: usize,
}

/// Why a refutation was not confirmed.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ReplayRefusal {
    /// Unit propagation on the encoding does not reach a contradiction.
    NotRefuted,
    /// The checker refused for another reason.
    Checker(String),
}

/// Check that unit propagation refutes the bit-level encoding of
/// `assertions`.
///
/// # Errors
///
/// [`ReplayRefusal`] when the refutation does not replay.
pub fn replay_refutation(
    terms: &TermStore,
    assertions: &[TermId],
) -> Result<ReplayStats, ReplayRefusal> {
    let mut encoder = Encoder::new(terms, assertions);
    for &assertion in assertions {
        if !matches!(terms.sort(assertion), Sort::Bool) {
            continue;
        }
        let bit = encoder.bits(assertion)[0];
        encoder.clause(vec![bit]);
    }
    let stats = ReplayStats {
        variables: encoder.next_var as usize,
        clauses: encoder.clauses.len(),
    };
    let mut checker = DratChecker::new(encoder.next_var as usize, false);
    for clause in &encoder.clauses {
        checker.add_original(clause);
    }
    checker
        .add_derived(&[])
        .map_err(|_| ReplayRefusal::NotRefuted)?;
    match checker.conclude_unsat() {
        ConcludeResult::Verified => Ok(stats),
        other => Err(ReplayRefusal::Checker(format!("{other:?}"))),
    }
}

/// The encoder's bits for one term, least significant first (a Boolean has
/// one bit). Literals of the constant-true variable stand for constants.
type Bits = Vec<Literal>;

struct Encoder<'a> {
    terms: &'a TermStore,
    ints: IntRanges<'a>,
    next_var: u32,
    clauses: Vec<Vec<Literal>>,
    memo: HashMap<TermId, Bits>,
    truth: Literal,
}

fn encodable_width(sort: &Sort) -> Option<u32> {
    match sort {
        Sort::Bool => Some(1),
        _ => sort
            .bitvec_width()
            .filter(|w| (1..=MAX_REPLAY_WIDTH).contains(w)),
    }
}

impl<'a> Encoder<'a> {
    fn new(terms: &'a TermStore, assertions: &[TermId]) -> Self {
        let mut encoder = Self {
            terms,
            ints: IntRanges::new(terms, assertions),
            next_var: 0,
            clauses: Vec::new(),
            memo: HashMap::default(),
            truth: Literal::positive(Variable::new(0)),
        };
        encoder.truth = encoder.fresh();
        encoder.clause(vec![encoder.truth]);
        encoder
    }

    fn fresh(&mut self) -> Literal {
        let var = Variable::new(self.next_var);
        self.next_var += 1;
        Literal::positive(var)
    }

    fn fresh_bits(&mut self, width: u32) -> Bits {
        (0..width).map(|_| self.fresh()).collect()
    }

    fn clause(&mut self, lits: Vec<Literal>) {
        self.clauses.push(lits);
    }

    fn constant_bit(&self, value: bool) -> Literal {
        if value {
            self.truth
        } else {
            self.truth.negated()
        }
    }

    /// Bits of a Boolean or bit-vector term of encodable width.
    fn bits(&mut self, term: TermId) -> Bits {
        if let Some(bits) = self.memo.get(&term) {
            return bits.clone();
        }
        let bits = stacker::maybe_grow(64 * 1024, 1024 * 1024, || self.encode(term));
        self.memo.insert(term, bits.clone());
        bits
    }

    /// Bits of every argument, or `None` when one is not encodable.
    fn args(&mut self, args: &[TermId]) -> Option<Vec<Bits>> {
        let mut out = Vec::with_capacity(args.len());
        for &arg in args {
            self.width_of(arg)?;
            out.push(self.bits(arg));
        }
        Some(out)
    }

    /// Width of an encodable term: Booleans, bit-vectors up to
    /// [`MAX_REPLAY_WIDTH`] bits and certified integers.
    fn width_of(&mut self, term: TermId) -> Option<u32> {
        match self.terms.sort(term) {
            Sort::Int => self.ints.certified(term).then_some(INT_WIDTH),
            sort => encodable_width(sort),
        }
    }

    fn encode(&mut self, term: TermId) -> Bits {
        let Some(width) = self.width_of(term) else {
            unreachable!("bits() is only called for encodable terms");
        };
        if matches!(self.terms.sort(term), Sort::Int) {
            return self.encode_int(term);
        }
        match self.terms.get(term).clone() {
            TermData::Const(Constant::Bool(value)) => vec![self.constant_bit(value)],
            TermData::Const(Constant::BitVec { value, .. }) => self.constant(&value, width),
            TermData::Not(a) => match self.args(&[a]) {
                Some(args) => vec![args[0][0].negated()],
                None => self.fresh_bits(width),
            },
            TermData::Ite(c, t, e) => match self.args(&[c, t, e]) {
                Some(args) if args[0].len() == 1 => self.mux(args[0][0], &args[1], &args[2]),
                _ => self.fresh_bits(width),
            },
            TermData::App(symbol, args) => match self.args(&args) {
                Some(bits) => self.app(&symbol, bits, width),
                None => self.fresh_bits(width),
            },
            _ => self.fresh_bits(width),
        }
    }

    fn constant(&mut self, value: &BigInt, width: u32) -> Bits {
        (0..width)
            .map(|i| self.constant_bit(value.bit(u64::from(i))))
            .collect()
    }

    fn app(&mut self, symbol: &Symbol, args: Vec<Bits>, width: u32) -> Bits {
        let indices: &[u32] = match symbol {
            Symbol::Indexed(_, indices) => indices,
            _ => &[],
        };
        let name = symbol.name();
        match (name, args.len(), indices.len()) {
            ("and" | "bvand", 2.., 0) => self.fold(args, Self::and_bits),
            ("or" | "bvor", 2.., 0) => self.fold(args, Self::or_bits),
            ("xor" | "bvxor", 2.., 0) => self.fold(args, Self::xor_bits),
            ("bvadd", 2.., 0) => self.fold(args, |enc, a, b| {
                let carry = enc.constant_bit(false);
                enc.adder(&a, &b, carry)
            }),
            ("and" | "or" | "bvand" | "bvor", 1, 0) => args[0].clone(),
            ("not" | "bvnot", 1, 0) => args[0].iter().map(|l| l.negated()).collect(),
            ("bvneg", 1, 0) => {
                let inverted: Bits = args[0].iter().map(|l| l.negated()).collect();
                let zero = vec![self.constant_bit(false); inverted.len()];
                let carry = self.constant_bit(true);
                self.adder(&inverted, &zero, carry)
            }
            ("bvsub", 2, 0) => {
                let inverted: Bits = args[1].iter().map(|l| l.negated()).collect();
                let carry = self.constant_bit(true);
                self.adder(&args[0], &inverted, carry)
            }
            ("=>", 2, 0) => {
                let not_a = args[0][0].negated();
                vec![self.or_gate(not_a, args[1][0])]
            }
            ("=", 2, 0) => vec![self.equal(&args[0], &args[1])],
            ("distinct", 2, 0) => vec![self.equal(&args[0], &args[1]).negated()],
            ("ite", 3, 0) if args[0].len() == 1 => self.mux(args[0][0], &args[1], &args[2]),
            ("bvult", 2, 0) => vec![self.less(&args[0], &args[1], false, false)],
            ("bvule", 2, 0) => vec![self.less(&args[0], &args[1], false, true)],
            ("bvslt", 2, 0) => vec![self.less(&args[0], &args[1], true, false)],
            ("bvsle", 2, 0) => vec![self.less(&args[0], &args[1], true, true)],
            ("<=", 2, 0) if args[0].len() == INT_WIDTH as usize => {
                vec![self.less(&args[0], &args[1], true, true)]
            }
            ("<", 2, 0) if args[0].len() == INT_WIDTH as usize => {
                vec![self.less(&args[0], &args[1], true, false)]
            }
            (">=", 2, 0) if args[0].len() == INT_WIDTH as usize => {
                vec![self.less(&args[1], &args[0], true, true)]
            }
            (">", 2, 0) if args[0].len() == INT_WIDTH as usize => {
                vec![self.less(&args[1], &args[0], true, false)]
            }
            ("int2bv", 1, 1) => args[0][..width as usize].to_vec(),
            ("bvugt", 2, 0) => vec![self.less(&args[1], &args[0], false, false)],
            ("bvuge", 2, 0) => vec![self.less(&args[1], &args[0], false, true)],
            ("bvsgt", 2, 0) => vec![self.less(&args[1], &args[0], true, false)],
            ("bvsge", 2, 0) => vec![self.less(&args[1], &args[0], true, true)],
            ("bvshl", 2, 0) => self.shift(&args[0], &args[1], Shift::Left),
            ("bvlshr", 2, 0) => self.shift(&args[0], &args[1], Shift::LogicalRight),
            ("bvashr", 2, 0) => self.shift(&args[0], &args[1], Shift::ArithmeticRight),
            ("extract", 1, 2) => {
                let (hi, lo) = (indices[0] as usize, indices[1] as usize);
                args[0][lo..=hi].to_vec()
            }
            ("concat", 2.., 0) => {
                // The last argument is lowest.
                let mut bits = Vec::with_capacity(width as usize);
                for arg in args.iter().rev() {
                    bits.extend_from_slice(arg);
                }
                bits
            }
            ("zero_extend", 1, 1) => {
                let mut bits = args[0].clone();
                bits.resize(width as usize, self.constant_bit(false));
                bits
            }
            ("sign_extend", 1, 1) => {
                let mut bits = args[0].clone();
                let sign = *bits.last().expect("a bit-vector has at least one bit");
                bits.resize(width as usize, sign);
                bits
            }
            _ => self.fresh_bits(width),
        }
    }

    /// A certified integer: SMT-LIB integer semantics on the 64-bit
    /// two's-complement pattern, exact because the term and its certified
    /// operands stay within `[-2^62, 2^62]`.
    fn encode_int(&mut self, term: TermId) -> Bits {
        let w = INT_WIDTH;
        if let Some(value) = int_constant(self.terms, term) {
            return self.constant(&pattern_bigint(value), w);
        }
        let (symbol, args) = match self.terms.get(term).clone() {
            TermData::Ite(c, t, e) => match self.args(&[c, t, e]) {
                Some(bits) if bits[0].len() == 1 => {
                    return self.mux(bits[0][0], &bits[1], &bits[2])
                }
                _ => return self.fresh_bits(w),
            },
            TermData::App(symbol, args) => (symbol, args),
            _ => return self.fresh_bits(w),
        };
        let name = symbol.name();
        match (name, args.as_slice()) {
            ("*", _) => return self.int_product(&args),
            ("div" | "mod", [a, c]) => {
                let Some(c) = int_constant(self.terms, *c).filter(|&c| c > 0 && c & (c - 1) == 0)
                else {
                    return self.fresh_bits(w);
                };
                let Some(bits) = self.args(&[*a]) else {
                    return self.fresh_bits(w);
                };
                let a = &bits[0];
                let k = c.trailing_zeros() as usize;
                let zero = self.constant_bit(false);
                return if name == "div" {
                    // Floor division by 2^k: arithmetic shift right.
                    let sign = a[a.len() - 1];
                    (0..a.len())
                        .map(|i| if i + k < a.len() { a[i + k] } else { sign })
                        .collect()
                } else {
                    // Euclidean remainder by 2^k: the low k bits.
                    (0..a.len())
                        .map(|i| if i < k { a[i] } else { zero })
                        .collect()
                };
            }
            _ => {}
        }
        let Some(bits) = self.args(&args) else {
            return self.fresh_bits(w);
        };
        match (name, bits.len()) {
            ("bv2nat", 1) => {
                let mut out = bits[0].clone();
                out.resize(w as usize, self.constant_bit(false));
                out
            }
            ("+", 2..) => self.fold(bits, |enc, a, b| {
                let carry = enc.constant_bit(false);
                enc.adder(&a, &b, carry)
            }),
            ("+", 1) => bits[0].clone(),
            ("-", 1) => self.negate(&bits[0]),
            ("-", 2..) => self.fold(bits, |enc, a, b| {
                let inverted: Bits = b.iter().map(|l| l.negated()).collect();
                let carry = enc.constant_bit(true);
                enc.adder(&a, &inverted, carry)
            }),
            ("ite", 3) if bits[0].len() == 1 => self.mux(bits[0][0], &bits[1], &bits[2]),
            _ => self.fresh_bits(w),
        }
    }

    /// Two's-complement negation, `~a + 0 + 1`.
    fn negate(&mut self, a: &[Literal]) -> Bits {
        let inverted: Bits = a.iter().map(|l| l.negated()).collect();
        let zero = vec![self.constant_bit(false); inverted.len()];
        let carry = self.constant_bit(true);
        self.adder(&inverted, &zero, carry)
    }

    /// A product with one non-constant factor: shift-and-add over the
    /// constant's set bits, lowest first, negated for a negative constant.
    fn int_product(&mut self, args: &[TermId]) -> Bits {
        let w = INT_WIDTH as usize;
        let mut constant: i128 = 1;
        let mut factor = None;
        for &arg in args {
            match int_constant(self.terms, arg) {
                Some(c) => match constant.checked_mul(c) {
                    Some(p) if p.abs() <= super::ints::INT_LIMIT => constant = p,
                    _ => return self.fresh_bits(INT_WIDTH),
                },
                None if factor.is_none() => factor = Some(arg),
                None => return self.fresh_bits(INT_WIDTH),
            }
        }
        let Some(factor) = factor else {
            return self.constant(&pattern_bigint(constant), INT_WIDTH);
        };
        if constant == 0 {
            return self.constant(&BigInt::from(0u8), INT_WIDTH);
        }
        let Some(bits) = self.args(&[factor]) else {
            return self.fresh_bits(INT_WIDTH);
        };
        let x = &bits[0];
        let zero = self.constant_bit(false);
        let magnitude = constant.unsigned_abs();
        let mut acc: Option<Bits> = None;
        for bit in 0..63usize {
            if magnitude >> bit & 1 == 0 {
                continue;
            }
            let shifted: Bits = (0..w)
                .map(|i| if i >= bit { x[i - bit] } else { zero })
                .collect();
            acc = Some(match acc {
                None => shifted,
                Some(a) => {
                    let carry = self.constant_bit(false);
                    self.adder(&a, &shifted, carry)
                }
            });
        }
        let acc = acc.expect("a nonzero constant has a set bit");
        if constant < 0 {
            self.negate(&acc)
        } else {
            acc
        }
    }

    fn fold(&mut self, args: Vec<Bits>, gate: impl Fn(&mut Self, Bits, Bits) -> Bits) -> Bits {
        let mut iter = args.into_iter();
        let mut acc = iter.next().expect("fold has at least two operands");
        for next in iter {
            acc = gate(self, acc, next);
        }
        acc
    }

    fn and_bits(&mut self, a: Bits, b: Bits) -> Bits {
        a.iter()
            .zip(&b)
            .map(|(&x, &y)| self.and_gate(x, y))
            .collect()
    }

    fn or_bits(&mut self, a: Bits, b: Bits) -> Bits {
        a.iter()
            .zip(&b)
            .map(|(&x, &y)| self.or_gate(x, y))
            .collect()
    }

    fn xor_bits(&mut self, a: Bits, b: Bits) -> Bits {
        a.iter()
            .zip(&b)
            .map(|(&x, &y)| self.xor_gate(x, y))
            .collect()
    }

    /// `z <-> a & b`.
    fn and_gate(&mut self, a: Literal, b: Literal) -> Literal {
        let z = self.fresh();
        self.clause(vec![z.negated(), a]);
        self.clause(vec![z.negated(), b]);
        self.clause(vec![z, a.negated(), b.negated()]);
        z
    }

    /// `z <-> a | b`.
    fn or_gate(&mut self, a: Literal, b: Literal) -> Literal {
        self.and_gate(a.negated(), b.negated()).negated()
    }

    /// `z <-> a ^ b`.
    fn xor_gate(&mut self, a: Literal, b: Literal) -> Literal {
        let z = self.fresh();
        self.clause(vec![z.negated(), a, b]);
        self.clause(vec![z.negated(), a.negated(), b.negated()]);
        self.clause(vec![z, a.negated(), b]);
        self.clause(vec![z, a, b.negated()]);
        z
    }

    /// `z <-> a ^ b ^ c`.
    fn xor3_gate(&mut self, a: Literal, b: Literal, c: Literal) -> Literal {
        let z = self.fresh();
        for mask in 0u8..8 {
            // The clause excluding the assignment a=bit0, b=bit1, c=bit2 with
            // z different from their parity.
            let (va, vb, vc) = (mask & 1 != 0, mask & 2 != 0, mask & 4 != 0);
            let parity = va ^ vb ^ vc;
            let lit = |l: Literal, v: bool| if v { l.negated() } else { l };
            let zl = if parity { z } else { z.negated() };
            self.clause(vec![lit(a, va), lit(b, vb), lit(c, vc), zl]);
        }
        z
    }

    /// `z <-> majority(a, b, c)`, all six clauses.
    fn majority_gate(&mut self, a: Literal, b: Literal, c: Literal) -> Literal {
        let z = self.fresh();
        for (x, y) in [(a, b), (a, c), (b, c)] {
            self.clause(vec![x.negated(), y.negated(), z]);
            self.clause(vec![x, y, z.negated()]);
        }
        z
    }

    /// Ripple-carry `a + b + carry_in`, modulo the width.
    fn adder(&mut self, a: &[Literal], b: &[Literal], carry_in: Literal) -> Bits {
        let mut carry = carry_in;
        let mut sum = Vec::with_capacity(a.len());
        for (i, (&x, &y)) in a.iter().zip(b).enumerate() {
            sum.push(self.xor3_gate(x, y, carry));
            if i + 1 < a.len() {
                carry = self.majority_gate(x, y, carry);
            }
        }
        sum
    }

    /// `z <-> (a == b)` over equal-width bit strings.
    fn equal(&mut self, a: &[Literal], b: &[Literal]) -> Literal {
        let z = self.fresh();
        let mut any_differs = vec![z];
        for (&x, &y) in a.iter().zip(b) {
            let d = self.xor_gate(x, y);
            self.clause(vec![z.negated(), d.negated()]);
            any_differs.push(d);
        }
        self.clause(any_differs);
        z
    }

    /// `a < b` (or `a <= b`), unsigned or two's-complement: the carry out of
    /// `~a + b + [or_equal]` after flipping both sign bits when signed.
    fn less(&mut self, a: &[Literal], b: &[Literal], signed: bool, or_equal: bool) -> Literal {
        let top = a.len() - 1;
        let mut carry = self.constant_bit(or_equal);
        for i in 0..a.len() {
            let flip = signed && i == top;
            let x = if flip { a[i] } else { a[i].negated() };
            let y = if flip { b[i].negated() } else { b[i] };
            carry = self.majority_gate(x, y, carry);
        }
        carry
    }

    /// `z <-> if c then t else e`, with the two clauses that let agreeing
    /// branches decide `z` without the condition.
    fn mux_gate(&mut self, c: Literal, t: Literal, e: Literal) -> Literal {
        let z = self.fresh();
        self.clause(vec![c.negated(), t.negated(), z]);
        self.clause(vec![c.negated(), t, z.negated()]);
        self.clause(vec![c, e.negated(), z]);
        self.clause(vec![c, e, z.negated()]);
        self.clause(vec![t.negated(), e.negated(), z]);
        self.clause(vec![t, e, z.negated()]);
        z
    }

    fn mux(&mut self, c: Literal, t: &[Literal], e: &[Literal]) -> Bits {
        t.iter()
            .zip(e)
            .map(|(&x, &y)| self.mux_gate(c, x, y))
            .collect()
    }

    /// Barrel shifter. Amounts at or past the width give 0 (or the sign for
    /// an arithmetic shift).
    fn shift(&mut self, value: &[Literal], amount: &[Literal], kind: Shift) -> Bits {
        let width = value.len();
        let zero = self.constant_bit(false);
        let fill = match kind {
            Shift::ArithmeticRight => *value.last().expect("non-empty"),
            Shift::Left | Shift::LogicalRight => zero,
        };
        let mut current = value.to_vec();
        let mut stage = 0;
        while (1usize << stage) < width && stage < amount.len() {
            let distance = 1usize << stage;
            let shifted: Bits = (0..width)
                .map(|i| match kind {
                    Shift::Left => {
                        if i >= distance {
                            current[i - distance]
                        } else {
                            zero
                        }
                    }
                    Shift::LogicalRight | Shift::ArithmeticRight => {
                        if i + distance < width {
                            current[i + distance]
                        } else {
                            fill
                        }
                    }
                })
                .collect();
            current = self.mux(amount[stage], &shifted, &current);
            stage += 1;
        }
        // Out of range: amount >= width.
        let limit = BigInt::from(width);
        let limit_bits = self.constant(&limit, amount.len() as u32);
        let out_of_range = if BigInt::from(1u8) << amount.len() <= limit {
            self.constant_bit(false)
        } else {
            self.less(&limit_bits, amount, false, true)
        };
        let fills = vec![fill; width];
        self.mux(out_of_range, &fills, &current)
    }
}

#[derive(Clone, Copy)]
enum Shift {
    Left,
    LogicalRight,
    ArithmeticRight,
}
