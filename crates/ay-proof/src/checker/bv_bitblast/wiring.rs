// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact acceptance of a bit-vector WIRING identity, with no SAT call.
//!
//! A unit `BvBitBlast` clause `(= l r)` whose two sides differ only in how
//! they route bits — `extract`, `concat`, `zero_extend`, `sign_extend`, a
//! literal, an `ite`, a literal left shift, a reducible bitwise OR, or
//! multiplication of an opaque SSA leaf by literal one — is valid exactly when both sides wire the same bit
//! into every position. Word-level reasoning over translation-validation
//! queries (`extract[31:0](zero_extend[32](v)) = v`, one per register read)
//! produces many such lemmas over 64-bit words, which the bounded evaluator
//! cannot enumerate and the proof-producing bit-blaster prices as one
//! expensive lemma EACH: a proof with two of them already exceeds the
//! strict-check envelope (`MAX_EXPENSIVE_BV_LEMMAS_PER_PROOF` caps it at
//! eight in any case). This module decides them symbolically instead.
//!
//! # The decision
//!
//! Every bit-vector term of width `w` is read as `w` WIRE BITS, each a
//! hash-consed node:
//!
//! * `Const(b)` — a literal bit;
//! * `Leaf(t, i)` — bit `i` of a term `t` this module does not open (a
//!   variable, a `bvmul`, a `select`, anything outside the list above);
//! * `Ite(c, x, y)` — the Boolean term `c` (never opened) selecting between
//!   two wire bits, with `Ite(c, x, x)` built as `x`.
//!
//! following SMT-LIB's definitions exactly: `extract[h:l]` keeps bits
//! `l..=h`, `concat` puts its LAST argument in the low bits, `zero_extend[k]`
//! appends `k` false bits on top, `sign_extend[k]` appends `k` copies of the
//! top bit, a literal contributes its binary expansion, and a bit-vector
//! `ite` selects bitwise. A literal left shift inserts false low bits and
//! discards high bits, becoming zero when the amount is at least the width.
//! An OR routes a bit only when its two inputs are identical, one is false,
//! or one is true. An unresolved OR or a variable shift stays an opaque leaf.
//! No new Boolean circuit or SAT search is built. Multiplication of an opaque BV leaf by a same-width
//! literal one (either operand order) routes that leaf unchanged, because
//! `v * 1 mod 2^w = v` for `0 <= v < 2^w`. General products remain opaque.
//!
//! SOUNDNESS. By induction over that construction, under EVERY interpretation
//! bit `i` of the term's value is the value of its `i`-th wire bit, where a
//! `Leaf(t, i)` takes bit `i` of `t`'s value and an `Ite` node evaluates its
//! condition term. Nodes are hash-consed, so two equal node ids are the same
//! formula and agree under every interpretation. Hence equal wire-bit lists
//! for `l` and `r` mean `l` and `r` have the same value under every
//! interpretation: the clause `(= l r)` is valid. The converse is not claimed
//! (two different leaves may be equal), so a `false` answer is only "not
//! decided here", and the ordinary bounded and proof-producing checks still
//! run. Every walk is bounded; exhaustion is "not decided".

use std::collections::HashMap;

use num_traits::ToPrimitive;

use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};

/// Distinct terms one decision may open.
const MAX_TERMS: usize = 4_096;
/// Wire bits one decision may build (hash-consed nodes plus bit-list slots).
const MAX_BITS: usize = 1 << 18;
/// Widest word this module reads.
const MAX_WIDTH: u32 = 4_096;

#[derive(Clone, Copy, PartialEq, Eq, Hash)]
enum Node {
    Const(bool),
    Leaf(TermId, u32),
    Ite(TermId, u32, u32),
}

#[derive(Default)]
struct Wiring {
    nodes: Vec<Node>,
    interned: HashMap<Node, u32>,
    words: HashMap<TermId, Vec<u32>>,
    budget: usize,
}

impl Wiring {
    fn node(&mut self, node: Node) -> Option<u32> {
        if let Node::Ite(_, then_bit, else_bit) = node {
            if then_bit == else_bit {
                return Some(then_bit);
            }
        }
        if let Some(&id) = self.interned.get(&node) {
            return Some(id);
        }
        self.charge(1)?;
        let id = u32::try_from(self.nodes.len()).ok()?;
        self.nodes.push(node);
        self.interned.insert(node, id);
        Some(id)
    }

    fn charge(&mut self, units: usize) -> Option<()> {
        self.budget = self.budget.checked_add(units)?;
        (self.budget <= MAX_BITS).then_some(())
    }

    /// The wire bits of `term`, least significant first; `None` when a bound
    /// is exceeded or the term is malformed.
    fn bits(&mut self, terms: &TermStore, term: TermId) -> Option<Vec<u32>> {
        if let Some(bits) = self.words.get(&term) {
            return Some(bits.clone());
        }
        if self.words.len() >= MAX_TERMS {
            return None;
        }
        let Sort::BitVec(sort) = terms.sort(term) else {
            return None;
        };
        let width = sort.width;
        if width == 0 || width > MAX_WIDTH {
            return None;
        }
        self.charge(width as usize)?;
        let bits = match terms.get(term) {
            TermData::Const(Constant::BitVec {
                value,
                width: literal_width,
            }) => {
                if *literal_width != width {
                    return None;
                }
                let value = value.clone();
                (0..width)
                    .map(|i| self.node(Node::Const(value.bit(u64::from(i)))))
                    .collect::<Option<Vec<_>>>()?
            }
            TermData::App(Symbol::Named(name), args) if name == "bvor" => {
                let &[left, right] = args.as_slice() else {
                    return None;
                };
                if terms.sort(left) != terms.sort(term) || terms.sort(right) != terms.sort(term) {
                    return None;
                }
                let left = self.bits(terms, left)?;
                let right = self.bits(terms, right)?;
                if left.len() != right.len() {
                    return None;
                }
                let merged = left
                    .into_iter()
                    .zip(right)
                    .map(|(left, right)| {
                        if left == right {
                            Some(left)
                        } else {
                            match (self.nodes[left as usize], self.nodes[right as usize]) {
                                (Node::Const(false), _) => Some(right),
                                (_, Node::Const(false)) => Some(left),
                                (Node::Const(true), _) => Some(left),
                                (_, Node::Const(true)) => Some(right),
                                _ => None,
                            }
                        }
                    })
                    .collect::<Option<Vec<_>>>();
                match merged {
                    Some(bits) => bits,
                    None => self.leaf(term, width)?,
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "bvshl" => {
                let &[value, amount] = args.as_slice() else {
                    return None;
                };
                if terms.sort(value) != terms.sort(term) || terms.sort(amount) != terms.sort(term) {
                    return None;
                }
                if let TermData::Const(Constant::BitVec {
                    value: shift,
                    width: literal_width,
                }) = terms.get(amount)
                {
                    if *literal_width != width
                        || shift.sign() == num_bigint::Sign::Minus
                        || shift.bits() > u64::from(width)
                    {
                        return None;
                    }
                    let zero = self.node(Node::Const(false))?;
                    match shift.to_u32().filter(|&shift| shift < width) {
                        Some(shift) => {
                            let source = self.bits(terms, value)?;
                            let mut shifted = vec![zero; shift as usize];
                            shifted.extend_from_slice(&source[..(width - shift) as usize]);
                            shifted
                        }
                        None => vec![zero; width as usize],
                    }
                } else {
                    self.leaf(term, width)?
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "bvmul" => {
                if let Some(value) = literal_unit_product_leaf(terms, args, width) {
                    self.leaf(value, width)?
                } else {
                    self.leaf(term, width)?
                }
            }
            TermData::App(Symbol::Indexed(name, indices), args) if args.len() == 1 => {
                let (name, indices, arg) = (name.clone(), indices.clone(), args[0]);
                let source = self.bits(terms, arg)?;
                match (name.as_str(), indices.as_slice()) {
                    ("extract", &[high, low]) => {
                        if high < low || high as usize >= source.len() {
                            return None;
                        }
                        source[low as usize..=high as usize].to_vec()
                    }
                    ("zero_extend", &[extra]) => {
                        let zero = self.node(Node::Const(false))?;
                        let mut bits = source;
                        bits.resize(bits.len().checked_add(extra as usize)?, zero);
                        bits
                    }
                    ("sign_extend", &[extra]) => {
                        let sign = *source.last()?;
                        let mut bits = source;
                        bits.resize(bits.len().checked_add(extra as usize)?, sign);
                        bits
                    }
                    _ => self.leaf(term, width)?,
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "concat" && args.len() >= 2 => {
                let args = args.clone();
                let mut bits = Vec::with_capacity(width as usize);
                for &part in args.iter().rev() {
                    bits.extend(self.bits(terms, part)?);
                }
                bits
            }
            TermData::Ite(condition, then_term, else_term) => {
                let (condition, then_term, else_term) = (*condition, *then_term, *else_term);
                if *terms.sort(condition) != Sort::Bool {
                    return None;
                }
                let then_bits = self.bits(terms, then_term)?;
                let else_bits = self.bits(terms, else_term)?;
                if then_bits.len() != else_bits.len() {
                    return None;
                }
                then_bits
                    .iter()
                    .zip(&else_bits)
                    .map(|(&yes, &no)| self.node(Node::Ite(condition, yes, no)))
                    .collect::<Option<Vec<_>>>()?
            }
            _ => self.leaf(term, width)?,
        };
        if bits.len() != width as usize {
            return None;
        }
        self.words.insert(term, bits.clone());
        Some(bits)
    }

    fn leaf(&mut self, term: TermId, width: u32) -> Option<Vec<u32>> {
        (0..width).map(|i| self.node(Node::Leaf(term, i))).collect()
    }
}

/// Multiplication by the literal unit preserves every bit. Keep this extension
/// deliberately on opaque SSA leaves: no additional recursive operation is
/// opened, and the existing word/bit meters still charge the routed word.
fn literal_unit_product_leaf(terms: &TermStore, args: &[TermId], width: u32) -> Option<TermId> {
    let [left, right] = args else {
        return None;
    };
    let sort = Sort::bitvec(width);
    if terms.sort(*left) != &sort || terms.sort(*right) != &sort {
        return None;
    }
    for (unit, value) in [(*left, *right), (*right, *left)] {
        let literal_unit = matches!(terms.get(unit),
            TermData::Const(Constant::BitVec { value, width: literal_width })
                if *literal_width == width && *value == num_bigint::BigInt::from(1_u8));
        let opaque_leaf = match terms.get(value) {
            TermData::Var(..) => true,
            TermData::App(_, arguments) => arguments.is_empty(),
            _ => false,
        };
        if literal_unit && opaque_leaf {
            return Some(value);
        }
    }
    None
}

/// Whether `clause` is one positive equality between two bit-vector terms
/// that wire the same bit into every position (see the module documentation).
/// `false` means "not decided here", never "invalid".
pub(super) fn holds_by_wiring(terms: &TermStore, clause: &[TermId]) -> bool {
    let [literal] = clause else {
        return false;
    };
    let TermData::App(Symbol::Named(name), args) = terms.get(*literal) else {
        return false;
    };
    let [left, right] = args.as_slice() else {
        return false;
    };
    if name != "=" || terms.sort(*left) != terms.sort(*right) {
        return false;
    }
    if left == right {
        return false;
    }
    let mut wiring = Wiring::default();
    match (wiring.bits(terms, *left), wiring.bits(terms, *right)) {
        (Some(left_bits), Some(right_bits)) => left_bits == right_bits,
        _ => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn word(terms: &mut TermStore, name: &str, width: u32) -> TermId {
        terms.mk_var(name, Sort::bitvec(width))
    }

    fn indexed(
        terms: &mut TermStore,
        op: &str,
        indices: Vec<u32>,
        arg: TermId,
        width: u32,
    ) -> TermId {
        terms.mk_app(Symbol::indexed(op, indices), [arg], Sort::bitvec(width))
    }

    fn eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
        terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
    }

    #[test]
    fn the_low_half_of_a_zero_extension_is_its_argument() {
        let mut terms = TermStore::new();
        let x = word(&mut terms, "x", 64);
        let low = indexed(&mut terms, "extract", vec![31, 0], x, 32);
        let wide = indexed(&mut terms, "zero_extend", vec![32], low, 64);
        let back = indexed(&mut terms, "extract", vec![31, 0], wide, 32);
        let identity = eq(&mut terms, back, low);
        assert!(holds_by_wiring(&terms, &[identity]));
    }

    #[test]
    fn an_opaque_product_is_one_word_of_leaves() {
        let mut terms = TermStore::new();
        let (a, b) = (word(&mut terms, "a", 32), word(&mut terms, "b", 32));
        let product = terms.mk_app(Symbol::named("bvmul"), [a, b], Sort::bitvec(32));
        let wide = indexed(&mut terms, "zero_extend", vec![32], product, 64);
        let back = indexed(&mut terms, "extract", vec![31, 0], wide, 32);
        let identity = eq(&mut terms, back, product);
        assert!(holds_by_wiring(&terms, &[identity]));
    }

    #[test]
    fn a_straddled_zero_extension_and_a_concatenation_agree() {
        let mut terms = TermStore::new();
        let r = word(&mut terms, "r", 1);
        let g = word(&mut terms, "g", 56);
        let byte = indexed(&mut terms, "zero_extend", vec![7], r, 8);
        let joined = terms.mk_app(Symbol::named("concat"), [g, byte], Sort::bitvec(64));
        let low = indexed(&mut terms, "extract", vec![7, 0], joined, 8);
        let wide = indexed(&mut terms, "zero_extend", vec![56], low, 64);
        let read = indexed(&mut terms, "extract", vec![31, 0], wide, 32);
        let direct = indexed(&mut terms, "zero_extend", vec![31], r, 32);
        let identity = eq(&mut terms, read, direct);
        assert!(holds_by_wiring(&terms, &[identity]));
    }

    #[test]
    fn a_constant_branch_ite_is_lifted_through_an_extension() {
        let mut terms = TermStore::new();
        let (x, y) = (word(&mut terms, "x", 32), word(&mut terms, "y", 32));
        let condition = eq(&mut terms, x, y);
        let one = terms.mk_bitvec(BigInt::from(1), 8);
        let zero = terms.mk_bitvec(BigInt::from(0), 8);
        let flag = terms.mk_ite_raw(condition, one, zero);
        let wide = indexed(&mut terms, "zero_extend", vec![24], flag, 32);
        let one32 = terms.mk_bitvec(BigInt::from(1), 32);
        let zero32 = terms.mk_bitvec(BigInt::from(0), 32);
        let lifted = terms.mk_ite_raw(condition, one32, zero32);
        let identity = eq(&mut terms, wide, lifted);
        assert!(holds_by_wiring(&terms, &[identity]));
    }

    /// NEGATIVE: the high half of a zero extension is zero, not the argument;
    /// a sign extension's high half is not zero; two different words are
    /// never identified; and only a single positive equality is read.
    #[test]
    fn non_identities_are_never_decided() {
        let mut terms = TermStore::new();
        let x = word(&mut terms, "x", 32);
        let y = word(&mut terms, "y", 32);
        let wide = indexed(&mut terms, "zero_extend", vec![32], x, 64);
        let high = indexed(&mut terms, "extract", vec![63, 32], wide, 32);
        let forged = eq(&mut terms, high, x);
        assert!(!holds_by_wiring(&terms, &[forged]));
        let signed = indexed(&mut terms, "sign_extend", vec![32], x, 64);
        let signed_high = indexed(&mut terms, "extract", vec![63, 32], signed, 32);
        let zero = terms.mk_bitvec(BigInt::from(0), 32);
        let not_zero = eq(&mut terms, signed_high, zero);
        assert!(!holds_by_wiring(&terms, &[not_zero]));
        let different = eq(&mut terms, x, y);
        assert!(!holds_by_wiring(&terms, &[different]));
        let low = indexed(&mut terms, "extract", vec![31, 0], wide, 32);
        let identity = eq(&mut terms, low, x);
        assert!(holds_by_wiring(&terms, &[identity]));
        let negated = terms.mk_not_raw(identity);
        assert!(!holds_by_wiring(&terms, &[negated]));
        assert!(!holds_by_wiring(&terms, &[identity, identity]));
        let zero_high = eq(&mut terms, high, zero);
        assert!(
            holds_by_wiring(&terms, &[zero_high]),
            "the high half IS zero"
        );
    }
}

#[cfg(test)]
#[path = "wiring_unit_tests.rs"]
mod unit_tests;

#[cfg(test)]
#[path = "wiring_packing_tests.rs"]
mod packing_tests;
