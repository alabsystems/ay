// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The cone of an obligation: the Boolean and bit-vector terms under its
//! assertions, as a [`KbRegion`] plus the initial knowledge.
//!
//! A term outside the region's vocabulary (a variable multiplication, an
//! array read, an unbounded integer, anything wider than 64 bits) becomes a
//! leaf: the region forgets what it means, which can only cost it a verdict,
//! never make one wrong. Certified bounded integers ([`super::ints`]) are
//! 64-bit two's-complement nodes. Associative operators with more than two
//! operands are folded to the left, the same way the replay's encoder folds
//! them.

use std::collections::hash_map::DefaultHasher;
use std::hash::{Hash, Hasher};

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::Sort;
use ay_jit::known_bits_region::{KbNode, KbOp, KbRegion, MAX_REGION_WIDTH};
use num_bigint::BigInt;

use super::ints::{int_constant, twos_complement, IntRanges, INT_WIDTH};
use super::rules::KnownBits;

/// Largest cone a region is built for.
pub const MAX_CONE_NODES: usize = 1 << 16;

/// A region with its initial knowledge.
#[derive(Clone, Debug)]
pub struct Cone {
    /// The program.
    pub region: KbRegion,
    /// Initial knowledge, one entry per node: constants are fully known and
    /// every asserted root is known true.
    pub initial: Vec<KnownBits>,
    /// The term each node stands for; `None` for the intermediate nodes of a
    /// folded operator.
    pub sources: Vec<Option<TermId>>,
    /// Nodes that stand for a term the region does not interpret.
    pub opaque: usize,
}

/// Why no cone was built.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum ConeRefusal {
    /// The cone exceeds [`MAX_CONE_NODES`].
    TooLarge,
    /// No assertion is a Boolean term the region can hold.
    Empty,
}

impl Cone {
    /// Build the cone of `assertions`.
    ///
    /// # Errors
    ///
    /// [`ConeRefusal`] when the cone is too large or empty.
    pub fn build(terms: &TermStore, assertions: &[TermId]) -> Result<Self, ConeRefusal> {
        let mut builder = Builder {
            terms,
            ints: IntRanges::new(terms, assertions),
            nodes: Vec::new(),
            initial: Vec::new(),
            memo: HashMap::default(),
            sources: Vec::new(),
            opaque: 0,
        };
        let mut roots = Vec::new();
        for &assertion in assertions {
            if !matches!(terms.sort(assertion), Sort::Bool) {
                continue;
            }
            roots.push(builder.node(assertion)?);
        }
        if roots.is_empty() {
            return Err(ConeRefusal::Empty);
        }
        for root in roots {
            let seed = KnownBits { zero: 0, one: 1 };
            builder.initial[root as usize] = builder.initial[root as usize].union(seed);
        }
        Ok(Self {
            region: KbRegion {
                nodes: builder.nodes,
            },
            initial: builder.initial,
            sources: builder.sources,
            opaque: builder.opaque,
        })
    }

    /// The obligation family: a hash of the region's shape and which nodes
    /// start known, but not of the constants' values. Two obligations of one
    /// family run the same compiled region.
    #[must_use]
    pub fn family_key(&self) -> u64 {
        let mut hasher = DefaultHasher::new();
        self.region.hash(&mut hasher);
        for (node, bits) in self.region.nodes.iter().zip(&self.initial) {
            if !matches!(node.op, KbOp::Const) {
                bits.hash(&mut hasher);
            }
        }
        hasher.finish()
    }
}

struct Builder<'a> {
    terms: &'a TermStore,
    ints: IntRanges<'a>,
    nodes: Vec<KbNode>,
    initial: Vec<KnownBits>,
    memo: HashMap<TermId, u32>,
    sources: Vec<Option<TermId>>,
    opaque: usize,
}

/// Width of a Boolean or bit-vector term the region can hold.
fn region_width(sort: &Sort) -> Option<u32> {
    match sort {
        Sort::Bool => Some(1),
        _ => sort
            .bitvec_width()
            .filter(|w| (1..=MAX_REGION_WIDTH).contains(w)),
    }
}

fn bigint_to_u64(value: &BigInt, width: u32) -> Option<u64> {
    let (sign, digits) = value.to_u64_digits();
    if sign == num_bigint::Sign::Minus || digits.len() > 1 {
        return None;
    }
    let v = digits.first().copied().unwrap_or(0);
    (v & !super::rules::mask(width) == 0).then_some(v)
}

impl Builder<'_> {
    fn push(&mut self, op: KbOp, width: u32, initial: KnownBits) -> Result<u32, ConeRefusal> {
        if self.nodes.len() >= MAX_CONE_NODES {
            return Err(ConeRefusal::TooLarge);
        }
        self.nodes.push(KbNode { op, width });
        self.initial.push(initial);
        self.sources.push(None);
        Ok((self.nodes.len() - 1) as u32)
    }

    fn leaf(&mut self, width: u32) -> Result<u32, ConeRefusal> {
        self.opaque += 1;
        self.push(KbOp::Leaf, width, KnownBits::UNKNOWN)
    }

    /// The node of a Boolean or bit-vector term of width at most 64.
    fn node(&mut self, term: TermId) -> Result<u32, ConeRefusal> {
        if let Some(&index) = self.memo.get(&term) {
            return Ok(index);
        }
        let index = stacker::maybe_grow(64 * 1024, 1024 * 1024, || self.build_node(term))?;
        self.memo.insert(term, index);
        self.sources[index as usize].get_or_insert(term);
        Ok(index)
    }

    /// The region width of `term`: Booleans, bit-vectors up to 64 bits and
    /// certified integers.
    fn width_of(&mut self, term: TermId) -> Option<u32> {
        match self.terms.sort(term) {
            Sort::Int => self.ints.certified(term).then_some(INT_WIDTH),
            sort => region_width(sort),
        }
    }

    /// The node of `term` when it fits the region.
    fn operand(&mut self, term: TermId) -> Result<Option<u32>, ConeRefusal> {
        if self.width_of(term).is_none() {
            return Ok(None);
        }
        self.node(term).map(Some)
    }

    fn constant(&mut self, value: u64, width: u32) -> Result<u32, ConeRefusal> {
        self.push(KbOp::Const, width, KnownBits::constant(value, width))
    }

    /// Nodes of all operands, or `None` when one does not fit.
    fn operands(&mut self, args: &[TermId]) -> Result<Option<Vec<u32>>, ConeRefusal> {
        let mut out = Vec::with_capacity(args.len());
        for &arg in args {
            match self.operand(arg)? {
                Some(index) => out.push(index),
                None => return Ok(None),
            }
        }
        Ok(Some(out))
    }

    fn build_node(&mut self, term: TermId) -> Result<u32, ConeRefusal> {
        let width = self
            .width_of(term)
            .expect("node() is only called for terms that fit the region");
        if matches!(self.terms.sort(term), Sort::Int) {
            return self.int_node(term);
        }
        match self.terms.get(term).clone() {
            TermData::Const(Constant::Bool(value)) => {
                self.push(KbOp::Const, 1, KnownBits::constant(u64::from(value), 1))
            }
            TermData::Const(Constant::BitVec { value, width: w }) => {
                match bigint_to_u64(&value, w) {
                    Some(v) => self.push(KbOp::Const, width, KnownBits::constant(v, width)),
                    None => self.leaf(width),
                }
            }
            TermData::Not(a) => match self.operand(a)? {
                Some(a) => self.push(KbOp::Not { a }, 1, KnownBits::UNKNOWN),
                None => self.leaf(width),
            },
            TermData::Ite(c, t, e) => match self.operands(&[c, t, e])? {
                Some(ops) if self.nodes[ops[0] as usize].width == 1 => self.push(
                    KbOp::Ite {
                        c: ops[0],
                        t: ops[1],
                        e: ops[2],
                    },
                    width,
                    KnownBits::UNKNOWN,
                ),
                _ => self.leaf(width),
            },
            TermData::App(symbol, args) => self.app(&symbol, &args, width),
            _ => self.leaf(width),
        }
    }

    fn app(&mut self, symbol: &Symbol, args: &[TermId], width: u32) -> Result<u32, ConeRefusal> {
        let Some(ops) = self.operands(args)? else {
            return self.leaf(width);
        };
        let indices = match symbol {
            Symbol::Indexed(_, indices) => indices.as_slice(),
            _ => &[],
        };
        let unknown = KnownBits::UNKNOWN;
        let w_of = |nodes: &[KbNode], i: u32| nodes[i as usize].width;
        match (symbol.name(), ops.as_slice(), indices) {
            ("and" | "bvand", [_, _, ..], []) => self.fold(&ops, width, |a, b| KbOp::And { a, b }),
            ("or" | "bvor", [_, _, ..], []) => self.fold(&ops, width, |a, b| KbOp::Or { a, b }),
            ("xor" | "bvxor", [_, _, ..], []) => self.fold(&ops, width, |a, b| KbOp::Xor { a, b }),
            ("bvadd", [_, _, ..], []) => self.fold(&ops, width, |a, b| KbOp::Add { a, b }),
            ("and" | "or" | "bvand" | "bvor", [a], []) => Ok(*a),
            ("not" | "bvnot", [a], []) => self.push(KbOp::Not { a: *a }, width, unknown),
            ("bvneg", [a], []) => self.push(KbOp::Neg { a: *a }, width, unknown),
            ("bvsub", [a, b], []) => self.push(KbOp::Sub { a: *a, b: *b }, width, unknown),
            ("=>", [a, b], []) => {
                let not_a = self.push(KbOp::Not { a: *a }, 1, unknown)?;
                self.push(KbOp::Or { a: not_a, b: *b }, 1, unknown)
            }
            ("=", [a, b], []) => self.push(KbOp::Eq { a: *a, b: *b }, 1, unknown),
            ("distinct", [a, b], []) => {
                let eq = self.push(KbOp::Eq { a: *a, b: *b }, 1, unknown)?;
                self.push(KbOp::Not { a: eq }, 1, unknown)
            }
            ("ite", [c, t, e], []) if w_of(&self.nodes, *c) == 1 => self.push(
                KbOp::Ite {
                    c: *c,
                    t: *t,
                    e: *e,
                },
                width,
                unknown,
            ),
            (name @ ("bvult" | "bvule" | "bvslt" | "bvsle"), [a, b], []) => {
                self.compare(name, *a, *b)
            }
            ("<=", [a, b], []) if self.is_int(args[0]) => self.compare("bvsle", *a, *b),
            ("<", [a, b], []) if self.is_int(args[0]) => self.compare("bvslt", *a, *b),
            (">=", [a, b], []) if self.is_int(args[0]) => self.compare("bvsle", *b, *a),
            (">", [a, b], []) if self.is_int(args[0]) => self.compare("bvslt", *b, *a),
            ("int2bv", [a], [_]) => self.push(KbOp::Extract { a: *a, lo: 0 }, width, unknown),
            ("bvugt", [a, b], []) => self.compare("bvult", *b, *a),
            ("bvuge", [a, b], []) => self.compare("bvule", *b, *a),
            ("bvsgt", [a, b], []) => self.compare("bvslt", *b, *a),
            ("bvsge", [a, b], []) => self.compare("bvsle", *b, *a),
            ("bvshl", [a, s], []) => self.push(KbOp::Shl { a: *a, s: *s }, width, unknown),
            ("bvlshr", [a, s], []) => self.push(KbOp::Lshr { a: *a, s: *s }, width, unknown),
            ("bvashr", [a, s], []) => self.push(KbOp::Ashr { a: *a, s: *s }, width, unknown),
            ("extract", [a], [_hi, lo]) => {
                self.push(KbOp::Extract { a: *a, lo: *lo }, width, unknown)
            }
            ("concat", [_, _, ..], []) => {
                let mut acc = ops[0];
                for &next in &ops[1..] {
                    let w = w_of(&self.nodes, acc) + w_of(&self.nodes, next);
                    acc = self.push(KbOp::Concat { a: acc, b: next }, w, unknown)?;
                }
                Ok(acc)
            }
            ("zero_extend", [a], [_]) => self.push(KbOp::Zext { a: *a }, width, unknown),
            ("sign_extend", [a], [_]) => self.push(KbOp::Sext { a: *a }, width, unknown),
            _ => self.leaf(width),
        }
    }

    fn is_int(&self, term: TermId) -> bool {
        matches!(self.terms.sort(term), Sort::Int)
    }

    /// The node of a certified integer term.
    fn int_node(&mut self, term: TermId) -> Result<u32, ConeRefusal> {
        let w = INT_WIDTH;
        let unknown = KnownBits::UNKNOWN;
        if let Some(value) = int_constant(self.terms, term) {
            return self.constant(twos_complement(value), w);
        }
        let (c, t, e, symbol, args) = match self.terms.get(term).clone() {
            TermData::Ite(c, t, e) => (Some(c), t, e, None, Vec::new()),
            TermData::App(symbol, args) => (None, term, term, Some(symbol), args),
            _ => return self.leaf(w),
        };
        if let Some(c) = c {
            return match self.operands(&[c, t, e])? {
                Some(ops) => self.push(
                    KbOp::Ite {
                        c: ops[0],
                        t: ops[1],
                        e: ops[2],
                    },
                    w,
                    unknown,
                ),
                None => self.leaf(w),
            };
        }
        let symbol = symbol.expect("an application");
        let name = symbol.name();
        if name == "bv2nat" {
            return match self.operands(&args)? {
                Some(ops) if ops.len() == 1 => self.push(KbOp::Zext { a: ops[0] }, w, unknown),
                _ => self.leaf(w),
            };
        }
        // Constant factors and divisors are read before operands are built.
        match (name, args.as_slice()) {
            ("*", _) => return self.int_product(&args),
            ("div" | "mod", [a, c]) => {
                let Some(c) = int_constant(self.terms, *c) else {
                    return self.leaf(w);
                };
                if c <= 0 || c & (c - 1) != 0 {
                    return self.leaf(w);
                }
                let Some(a) = self.operand(*a)? else {
                    return self.leaf(w);
                };
                return if name == "div" {
                    let k = self.constant(u64::from(c.trailing_zeros()), w)?;
                    self.push(KbOp::Ashr { a, s: k }, w, unknown)
                } else {
                    let m = self.constant((c - 1) as u64, w)?;
                    self.push(KbOp::And { a, b: m }, w, unknown)
                };
            }
            _ => {}
        }
        let Some(ops) = self.operands(&args)? else {
            return self.leaf(w);
        };
        match (name, ops.as_slice()) {
            ("+", [_, _, ..]) => self.fold(&ops, w, |a, b| KbOp::Add { a, b }),
            ("+", [a]) => Ok(*a),
            ("-", [a]) => self.push(KbOp::Neg { a: *a }, w, unknown),
            ("-", [_, _, ..]) => self.fold(&ops, w, |a, b| KbOp::Sub { a, b }),
            ("ite", [c, t, e]) if self.nodes[*c as usize].width == 1 => self.push(
                KbOp::Ite {
                    c: *c,
                    t: *t,
                    e: *e,
                },
                w,
                unknown,
            ),
            _ => self.leaf(w),
        }
    }

    /// A product with at most one non-constant factor: shift-and-add over
    /// the constant's set bits, lowest first, negated for a negative
    /// constant. Any other product is a leaf.
    fn int_product(&mut self, args: &[TermId]) -> Result<u32, ConeRefusal> {
        let w = INT_WIDTH;
        let unknown = KnownBits::UNKNOWN;
        let mut constant: i128 = 1;
        let mut factor = None;
        for &arg in args {
            match int_constant(self.terms, arg) {
                Some(c) => match constant.checked_mul(c) {
                    Some(product) if product.abs() <= super::ints::INT_LIMIT => constant = product,
                    _ => return self.leaf(w),
                },
                None if factor.is_none() => factor = Some(arg),
                None => return self.leaf(w),
            }
        }
        let Some(factor) = factor else {
            return self.constant(twos_complement(constant), w);
        };
        if constant == 0 {
            return self.constant(0, w);
        }
        let Some(x) = self.operand(factor)? else {
            return self.leaf(w);
        };
        let magnitude = constant.unsigned_abs();
        let mut acc: Option<u32> = None;
        for bit in 0..63u32 {
            if magnitude >> bit & 1 == 0 {
                continue;
            }
            let term = if bit == 0 {
                x
            } else {
                let k = self.constant(u64::from(bit), w)?;
                self.push(KbOp::Shl { a: x, s: k }, w, unknown)?
            };
            acc = Some(match acc {
                None => term,
                Some(a) => self.push(KbOp::Add { a, b: term }, w, unknown)?,
            });
        }
        let acc = acc.expect("a nonzero constant has a set bit");
        if constant < 0 {
            self.push(KbOp::Neg { a: acc }, w, unknown)
        } else {
            Ok(acc)
        }
    }

    fn compare(&mut self, name: &str, a: u32, b: u32) -> Result<u32, ConeRefusal> {
        let (signed, or_equal) = match name {
            "bvult" => (false, false),
            "bvule" => (false, true),
            "bvslt" => (true, false),
            _ => (true, true),
        };
        self.push(
            KbOp::Cmp {
                a,
                b,
                signed,
                or_equal,
            },
            1,
            KnownBits::UNKNOWN,
        )
    }

    /// Left fold of an associative operator over two or more operands.
    fn fold(
        &mut self,
        ops: &[u32],
        width: u32,
        make: impl Fn(u32, u32) -> KbOp,
    ) -> Result<u32, ConeRefusal> {
        let mut acc = ops[0];
        for &next in &ops[1..] {
            acc = self.push(make(acc, next), width, KnownBits::UNKNOWN)?;
        }
        Ok(acc)
    }
}
