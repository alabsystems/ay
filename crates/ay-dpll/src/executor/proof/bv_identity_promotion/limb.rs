// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A two-limb product identity proved over its limbs.
//!
//! A multi-word lowering spells a `2h`-bit product through `h`-bit limbs:
//! external-codegen's i128 multiply (gate row 2023) states
//!
//! ```text
//! (bvmul (concat a1 a0) (concat b1 b0))
//!   = (concat (bvadd (bvadd hi(P) (bvmul a1 b0)) (bvmul a0 b1)) (bvmul a0 b0))
//! P = (bvmul Z(a0) Z(b0)),  Z(y) = ((_ zero_extend h) y),  hi = extract 2h-1 h
//! ```
//!
//! Bit-blasting it whole is a miter of a `2h`-bit multiplier against a sum of
//! differently organized partial products, which no SAT engine here decides
//! in the gate's budget. It is a ring identity once each limb concat is read
//! as `C(x) + Z(y)`, `C(x) = (concat x 0_h)`, and each product of a padded
//! limb as the padded narrow product. The certificate is one transitivity
//! chain whose links are congruences over a few LIMB FACTS and
//! [`TheoryLemmaKind::ArithClauseTautology`] ring steps (printed as
//! `poly_simp`, which reads `concat`, `extract` and `zero_extend` as opaque
//! factors, every coefficient here being 1):
//!
//! ```text
//! L0 = (bvmul A B)
//! L1 = (bvmul (+ C(a1) Z(a0)) B)                      fact A
//! L2 = (+ (bvmul C(a1) B) (bvmul Z(a0) B))            ring
//! L3 = (+ C(a1*b0) (bvmul Z(a0) (+ C(b1) Z(b0))))     facts C(a1)*B, B
//! L4 = (+ C(a1*b0) (+ (bvmul Z(a0) C(b1)) P))         ring
//! L5 = (+ C(a1*b0) (+ C(a0*b1) P))                    fact Z(a0)*C(b1)
//! R1 = (+ (+ P C(a1*b0)) C(a0*b1))                    ring
//! R0 = (concat X (bvmul a0 b0))                       fact R0
//! ```
//!
//! Every fact is chosen so that its two sides bit-blast to one circuit up to
//! constant propagation: a limb concat against its padded sum, the `h`-bit
//! adder spine of `X` against its `2h`-bit padded twin, `P`'s low half
//! against `a0*b0`, and a product with a padded operand against the padded
//! narrow product in the same operand order (the strict checker lowers such a
//! product at the narrow width, `checker/bv_bitblast/padded_product.rs`). No
//! fact multiplies by a power-of-two literal: the printer would re-spell each
//! as a doubling chain of `h` adders (measured: 21 MB of certificate for one).
//!
//! Nothing here is trusted: the facts are proved together by ONE
//! [`TheoryLemmaKind::BvBitBlast`] lemma (see `frontier.rs` for why one),
//! re-derived by the strict checker's bit-blast validator after it agrees on
//! sampled assignments; every ring step by the ring lane and `poly_simp`;
//! every congruence and the chain by their schema checks. A shape outside
//! this reading declines before any lemma is asked for.

use super::Executor;
use ay_core::{Proof, ProofId, Sort, Symbol, TermData, TermId};
use num_bigint::BigInt;
use num_traits::Zero;

mod chain;
use chain::Step;

/// Widest identity read over limbs (the ring lane's coefficients are `u128`).
const MAX_WIDTH: u32 = 128;
/// Summands the high limb of the result may add up.
const MAX_SUMMANDS: usize = 8;

/// The word geometry of one identity: width `2h`, and the `h`-bit zero.
struct Limbs {
    width: u32,
    half: u32,
    zero: TermId,
}

impl Executor {
    /// `(= lhs rhs)` proved in `candidate` over the limbs (module docs), or
    /// `None` when the identity is not a two-limb product against its limbs.
    pub(super) fn bv_limb_identity(
        &mut self,
        candidate: &mut Proof,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<ProofId> {
        let width = self.limb_width_of(lhs)?;
        if width % 2 != 0 || !(2..=MAX_WIDTH).contains(&width) {
            return None;
        }
        if self.limb_width_of(rhs) != Some(width) {
            return None;
        }
        let half = width / 2;
        let zero = self.ctx.terms.mk_bitvec(BigInt::zero(), half);
        let limbs = Limbs { width, half, zero };
        let product_on_left = self.limb_operands(&limbs, lhs).is_some();
        let (product, result) = if product_on_left {
            (lhs, rhs)
        } else {
            (rhs, lhs)
        };
        let mut facts = Vec::new();
        let Some(mut path) = self.limb_product_path(&limbs, product, &mut facts) else {
            chain::decline("no two-limb product side");
            return None;
        };
        let Some(sum) = self.limb_result_sum(&limbs, result, &mut facts) else {
            chain::decline("the other side is not a limb concat of partial products");
            return None;
        };
        path.extend([(Step::Ring, sum), (Step::RewriteBack, result)]);
        let mut unique: Vec<(TermId, TermId)> = Vec::with_capacity(facts.len());
        for fact in facts {
            if !unique.contains(&fact) {
                unique.push(fact);
            }
        }
        if product_on_left {
            self.prove_limb_chain(candidate, &unique, product, &path)
        } else {
            let (start, reversed) = reversed_path(product, &path);
            self.prove_limb_chain(candidate, &unique, start, &reversed)
        }
    }

    /// `L1 .. L5` for `(bvmul A B)`, both operands limb concats (module docs),
    /// recording the facts `A`, `C(a1)*B`, `B` and `Z(a0)*C(b1)`.
    fn limb_product_path(
        &mut self,
        limbs: &Limbs,
        product: TermId,
        facts: &mut Vec<(TermId, TermId)>,
    ) -> Option<Vec<(Step, TermId)>> {
        let w = limbs.width;
        let (left, right) = self.limb_operands(limbs, product)?;
        let (a1, a0) = self.limb_split(limbs, left)?;
        let (b1, b0) = self.limb_split(limbs, right)?;
        let (ca1, za0) = (self.limb_padded(limbs, a1)?, self.limb_widened(limbs, a0)?);
        let (cb1, zb0) = (self.limb_padded(limbs, b1)?, self.limb_widened(limbs, b0)?);
        let left_sum = self.limb_app("bvadd", vec![ca1, za0], w)?;
        let right_sum = self.limb_app("bvadd", vec![cb1, zb0], w)?;
        let high_cross = self.limb_app("bvmul", vec![a1, b0], limbs.half)?;
        let low_cross = self.limb_app("bvmul", vec![a0, b1], limbs.half)?;
        let (high_cross, low_cross) = (
            self.limb_padded(limbs, high_cross)?,
            self.limb_padded(limbs, low_cross)?,
        );
        let l1 = self.limb_app("bvmul", vec![left_sum, right], w)?;
        let high = self.limb_app("bvmul", vec![ca1, right], w)?;
        let low = self.limb_app("bvmul", vec![za0, right], w)?;
        let l2 = self.limb_app("bvadd", vec![high, low], w)?;
        let low_expanded = self.limb_app("bvmul", vec![za0, right_sum], w)?;
        let l3 = self.limb_app("bvadd", vec![high_cross, low_expanded], w)?;
        let padded = self.limb_app("bvmul", vec![za0, cb1], w)?;
        let square = self.limb_app("bvmul", vec![za0, zb0], w)?;
        let tail = self.limb_app("bvadd", vec![padded, square], w)?;
        let l4 = self.limb_app("bvadd", vec![high_cross, tail], w)?;
        let tail = self.limb_app("bvadd", vec![low_cross, square], w)?;
        let l5 = self.limb_app("bvadd", vec![high_cross, tail], w)?;
        facts.extend([
            (left, left_sum),
            (high, high_cross),
            (right, right_sum),
            (padded, low_cross),
        ]);
        Some(vec![
            (Step::Rewrite, l1),
            (Step::Ring, l2),
            (Step::Rewrite, l3),
            (Step::Ring, l4),
            (Step::Rewrite, l5),
        ])
    }

    /// `R1` for the limb concat `(concat X lo)`: the summands of `X` padded,
    /// in `X`'s own order, with the carry `hi(Z(u) * Z(v))` of a low limb
    /// `lo = u * v` replaced by the product `Z(u) * Z(v)` itself (which also
    /// carries `lo`), or `Z(lo)` appended when there is no such carry.
    /// Records the fact `R0 = R1`.
    fn limb_result_sum(
        &mut self,
        limbs: &Limbs,
        result: TermId,
        facts: &mut Vec<(TermId, TermId)>,
    ) -> Option<TermId> {
        let w = limbs.width;
        let (high, low) = self.limb_split(limbs, result)?;
        let mut summands = Vec::new();
        self.limb_summands(high, false, &mut summands)?;
        let narrow = self.limb_narrow_product(limbs, low);
        let carry = narrow.and_then(|narrow| {
            summands.iter().position(|&(negative, summand)| {
                !negative && self.limb_carry_product(limbs, summand).map(|(_, n)| n) == Some(narrow)
            })
        });
        let mut sum: Option<TermId> = None;
        for (index, (negative, summand)) in summands.into_iter().enumerate() {
            let term = if Some(index) == carry {
                self.limb_carry_product(limbs, summand)?.0
            } else {
                self.limb_padded(limbs, summand)?
            };
            sum = Some(match (sum, negative) {
                (None, false) => term,
                (None, true) => return None,
                (Some(acc), false) => self.limb_app("bvadd", vec![acc, term], w)?,
                (Some(acc), true) => self.limb_app("bvsub", vec![acc, term], w)?,
            });
        }
        let mut sum = sum?;
        if carry.is_none() {
            let widened = self.limb_widened(limbs, low)?;
            sum = self.limb_app("bvadd", vec![sum, widened], w)?;
        }
        facts.push((result, sum));
        Some(sum)
    }

    /// The signed summands of an `h`-bit `bvadd`/`bvsub`/`bvneg` spine.
    fn limb_summands(
        &self,
        term: TermId,
        negative: bool,
        summands: &mut Vec<(bool, TermId)>,
    ) -> Option<()> {
        match self.ctx.terms.get(term) {
            TermData::App(Symbol::Named(op), args)
                if matches!(
                    (op.as_str(), args.len()),
                    ("bvadd", 2..) | ("bvsub", 2) | ("bvneg", 1)
                ) =>
            {
                for (index, &arg) in args.iter().enumerate() {
                    let flip = op == "bvneg" || (op == "bvsub" && index > 0);
                    self.limb_summands(arg, negative != flip, summands)?;
                }
                Some(())
            }
            _ => {
                summands.push((negative, term));
                (summands.len() <= MAX_SUMMANDS).then_some(())
            }
        }
    }

    /// `(A, B)` when `term` is a binary `2h`-bit `(bvmul A B)` of two limb
    /// concats.
    fn limb_operands(&self, limbs: &Limbs, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(term) else {
            return None;
        };
        let &[left, right] = args.as_slice() else {
            return None;
        };
        (op == "bvmul"
            && self.limb_split(limbs, left).is_some()
            && self.limb_split(limbs, right).is_some())
        .then_some((left, right))
    }

    /// `(high, low)` when `term` is a `2h`-bit `(concat high low)` of two
    /// `h`-bit limbs.
    fn limb_split(&self, limbs: &Limbs, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(term) else {
            return None;
        };
        let &[high, low] = args.as_slice() else {
            return None;
        };
        (op == "concat"
            && self.limb_width_of(term) == Some(limbs.width)
            && self.limb_width_of(high) == Some(limbs.half)
            && self.limb_width_of(low) == Some(limbs.half))
        .then_some((high, low))
    }

    /// `(u, v)` when `term` is an `h`-bit binary `(bvmul u v)`.
    fn limb_narrow_product(&self, limbs: &Limbs, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(Symbol::Named(op), args) = self.ctx.terms.get(term) else {
            return None;
        };
        let &[u, v] = args.as_slice() else {
            return None;
        };
        (op == "bvmul"
            && self.limb_width_of(term) == Some(limbs.half)
            && self.limb_width_of(u) == Some(limbs.half)
            && self.limb_width_of(v) == Some(limbs.half))
        .then_some((u, v))
    }

    /// `(P, (u, v))` when `term` is `((_ extract 2h-1 h) P)` for the widened
    /// product `P = (bvmul Z(u) Z(v))`.
    fn limb_carry_product(
        &self,
        limbs: &Limbs,
        term: TermId,
    ) -> Option<(TermId, (TermId, TermId))> {
        let TermData::App(Symbol::Indexed(name, indices), args) = self.ctx.terms.get(term) else {
            return None;
        };
        let &[wide] = args.as_slice() else {
            return None;
        };
        if name != "extract" || indices.as_slice() != [limbs.width - 1, limbs.half] {
            return None;
        }
        let TermData::App(Symbol::Named(op), factors) = self.ctx.terms.get(wide) else {
            return None;
        };
        let &[left, right] = factors.as_slice() else {
            return None;
        };
        if op != "bvmul" || self.limb_width_of(wide) != Some(limbs.width) {
            return None;
        }
        Some((
            wide,
            (
                self.limb_narrow_of(limbs, left)?,
                self.limb_narrow_of(limbs, right)?,
            ),
        ))
    }

    /// `y` when `term` is `Z(y)`.
    fn limb_narrow_of(&self, limbs: &Limbs, term: TermId) -> Option<TermId> {
        let TermData::App(Symbol::Indexed(name, indices), args) = self.ctx.terms.get(term) else {
            return None;
        };
        let &[narrow] = args.as_slice() else {
            return None;
        };
        (name == "zero_extend"
            && indices.as_slice() == [limbs.half]
            && self.limb_width_of(narrow) == Some(limbs.half))
        .then_some(narrow)
    }

    /// `Z(y)`.
    fn limb_widened(&mut self, limbs: &Limbs, y: TermId) -> Option<TermId> {
        let symbol = Symbol::indexed("zero_extend", vec![limbs.half]);
        let term = self
            .ctx
            .terms
            .mk_app(symbol, vec![y], Sort::bitvec(limbs.width));
        (self.limb_narrow_of(limbs, term) == Some(y)).then_some(term)
    }

    /// `C(x) = (concat x 0_h)`.
    fn limb_padded(&mut self, limbs: &Limbs, x: TermId) -> Option<TermId> {
        self.limb_app("concat", vec![x, limbs.zero], limbs.width)
    }

    /// The raw application `(op args)` of the given width, or `None` when the
    /// store would fold it into anything else.
    fn limb_app(&mut self, op: &str, args: Vec<TermId>, width: u32) -> Option<TermId> {
        let term = self
            .ctx
            .terms
            .mk_app(Symbol::named(op), args.clone(), Sort::bitvec(width));
        matches!(
            self.ctx.terms.get(term),
            TermData::App(Symbol::Named(name), raw) if name == op && *raw == args
        )
        .then_some(term)
    }

    fn limb_width_of(&self, term: TermId) -> Option<u32> {
        match self.ctx.terms.sort(term) {
            Sort::BitVec(bv) => Some(bv.width),
            _ => None,
        }
    }
}

/// The same chain walked from its last node back to `start`.
fn reversed_path(start: TermId, path: &[(Step, TermId)]) -> (TermId, Vec<(Step, TermId)>) {
    let mut nodes = vec![start];
    nodes.extend(path.iter().map(|&(_, node)| node));
    let end = nodes.pop().unwrap_or(start);
    let reversed = path
        .iter()
        .rev()
        .zip(nodes.into_iter().rev())
        .map(|(&(step, _), node)| {
            let step = match step {
                Step::Rewrite => Step::RewriteBack,
                Step::RewriteBack => Step::Rewrite,
                Step::Ring => Step::Ring,
            };
            (step, node)
        })
        .collect();
    (end, reversed)
}
