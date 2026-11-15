// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact affine identities in Z/(2^width), independently checked from the DAG.
//!
//! Addition, subtraction and negation are normalized, and so, in the direct
//! identity lanes, is multiplication by a nonzero literal. Other BV operations,
//! slices and extensions are distinct atoms; no correlation is ever assumed.
//! Carcara independently replays a [`check`] equality with `poly_simp`. It
//! expands EVERY `bvmul` (including the non-literal products this lane keeps
//! as one atom) into monomials, i.e. sorted multisets of non-arithmetic
//! factors, normalizes over the integers, and then reduces each coefficient
//! modulo `2^width` while KEEPING a monomial whose coefficient became zero
//! that way; the constant term is reduced without being kept (measured on
//! carcara 1.1.0: `(= (bvadd x x) #b0)` over a 1-bit `x` and
//! `(= (bvadd (bvmul #xff (bvmul x y)) (bvmul y x)) ...)` are rejected while
//! `(= (bvadd x (bvneg x)) #b0)` and `(= (bvadd (bvadd x #xff) #x01) x)` are
//! accepted). [`check`] recomputes exactly that expansion and declines an
//! identity that needs such a monomial to vanish.
//!
//! A NONLINEAR identity — `(= (bvmul a b) (bvmul b a))`, a regrouped product
//! chain — differs in the affine form, where each product is its own atom.
//! Both lanes decide it on that same integer expansion instead
//! (`Normalizer::ring_identity`): equal non-constant monomials with equal
//! NONZERO residues modulo 2^width, and equal constant residues. That is an
//! identity of the polynomial ring over Z/(2^width) and one `poly_simp`
//! replays. Measured on external-codegen's `ReductionSplit` / `CSE commutative`
//! obligations, which AY answered `unknown` for want of any printable lemma.
//!
//! [`check_native`], the native strict checker's lane, also reads the shift
//! that elaboration substitutes for a power-of-two multiplier,
//! `concat(extract[w-k-1:0](x), 0_k)`, as `2^k * x`. `poly_simp` has no
//! `concat`, so an identity only this lane accepts is natively certified and
//! prints as an honest `hole`: the wire recognizer keeps using [`check`].

use std::collections::BTreeMap;

use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{ToPrimitive, Zero};

use super::ProofCheckError;

mod complement;
pub(crate) use complement::complement_relation;
mod context;
pub(crate) use context::{context_conditional, context_identity};
mod partition;
pub(crate) use partition::{partition_identity, IntervalLeaf, PartitionIdentity};
mod guarded_mask;
pub(crate) use guarded_mask::{guarded_mask_identity, GuardKind, GuardedMask};
#[cfg(test)]
mod guarded_tests;
#[cfg(test)]
mod ring_tests;
#[cfg(test)]
mod wire_tests;

const MAX_NODES: usize = 2_048;
const MAX_DEPTH: usize = 64;
const MAX_MERGES: usize = 65_536;
// Includes traversal, map balancing, coefficient updates and final comparison.
const MAX_WORK: usize = 2_000_000;
const MAX_ALLOCATION: usize = 8 * 1024 * 1024;
// Same work ceiling and checker, smaller allocation reserve only after a
// bounded, multiplication-free scalar grammar has been completely inspected.
const SMALL_LINEAR_SOURCE_NODES: usize = 32;
const PRICE_SCAN_WORK: usize = 1_024;
const SMALL_LINEAR_ALLOCATION: usize = 4 * 1024 * 1024;
type Affine = BTreeMap<Option<TermId>, u128>;
/// Carcara's integer polynomial: monomial (sorted factor multiset; empty for
/// the constant term) to unreduced coefficient.
type IntegerForm = BTreeMap<Vec<TermId>, BigInt>;

struct Normalizer<'a> {
    terms: &'a TermStore,
    width: u32,
    mask: u128,
    nodes: usize,
    work: usize,
    /// Normalize `bvmul` with a literal-constant operand as that scalar times
    /// the other operand's form, instead of keeping it as an opaque atom.
    scale_constant_products: bool,
    /// Read elaboration's power-of-two shift `concat(extract[w-k-1:0](x),
    /// 0_k)` as `2^k * x` (native lane only; see the module docs).
    accept_elaborated_shifts: bool,
}

impl Normalizer<'_> {
    fn visit(&mut self, term: TermId, depth: usize) -> Option<()> {
        self.terms.entry_stamp(term)?;
        self.nodes = self.nodes.checked_add(1)?;
        (depth <= MAX_DEPTH && self.nodes <= MAX_NODES).then_some(())
    }

    fn validate(&mut self, term: TermId, depth: usize) -> Option<()> {
        self.visit(term, depth)?;
        if self.terms.sort(term) != &Sort::bitvec(self.width) {
            return None;
        }
        match self.terms.get(term) {
            TermData::Var(_, _) => Some(()),
            TermData::Const(Constant::BitVec { value, width })
                if *width == self.width && value.to_u128()? <= self.mask =>
            {
                Some(())
            }
            // A slice or extension is an opaque factor, as `poly_simp` reads it.
            TermData::App(Symbol::Indexed(..), _) => Some(()),
            TermData::App(Symbol::Named(op), args) if op == "concat" => {
                match self.elaborated_shift(term) {
                    Some((operand, _)) if self.accept_elaborated_shifts => {
                        for &part in args {
                            self.visit(part, depth + 1)?;
                        }
                        self.validate(operand, depth + 2)
                    }
                    _ => Some(()),
                }
            }
            TermData::App(Symbol::Named(op), args) => {
                let arity = match op.as_str() {
                    "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor" | "bvshl"
                    | "bvlshr" | "bvashr" => 2,
                    "bvneg" | "bvnot" => 1,
                    _ => return None,
                };
                if args.len() != arity {
                    return None;
                }
                for &arg in args {
                    self.validate(arg, depth + 1)?;
                }
                Some(())
            }
            _ => None,
        }
    }

    fn normalize(&mut self, term: TermId, depth: usize) -> Option<Affine> {
        self.visit(term, depth)?;
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, .. }) => {
                let value = value.to_u128()?;
                Some(if value == 0 {
                    Affine::new()
                } else {
                    BTreeMap::from([(None, value)])
                })
            }
            TermData::App(Symbol::Named(op), args)
                if matches!(op.as_str(), "bvadd" | "bvsub" | "bvneg") =>
            {
                let mut result = if op == "bvneg" {
                    Affine::new()
                } else {
                    self.normalize(args[0], depth + 1)?
                };
                let right = self.normalize(args[usize::from(op != "bvneg")], depth + 1)?;
                for (atom, coefficient) in right {
                    self.work = self.work.checked_add(1)?;
                    if self.work > MAX_MERGES {
                        return None;
                    }
                    let old = result.get(&atom).copied().unwrap_or(0);
                    let next = if op == "bvadd" {
                        old.wrapping_add(coefficient)
                    } else {
                        old.wrapping_sub(coefficient)
                    } & self.mask;
                    if next == 0 {
                        result.remove(&atom);
                    } else {
                        result.insert(atom, next);
                    }
                }
                Some(result)
            }
            TermData::App(Symbol::Named(op), args)
                if self.scale_constant_products && op == "bvmul" =>
            {
                // Only a LITERAL constant operand makes the product linear.
                // Any other product stays one atom, exactly as before, without
                // descending into (and charging for) its operands. So does a
                // product with a zero literal: that family already has its own
                // exact multiplier-circuit certificate (`bv_mul_zero`, Carcara's
                // `bitblast_mult`), which this lane must not displace.
                let (scale, operand) = match (self.literal(args[0]), self.literal(args[1])) {
                    (Some(0), _) | (_, Some(0)) | (None, None) => {
                        return Some(BTreeMap::from([(Some(term), 1)]));
                    }
                    (Some(scale), _) => (scale, args[1]),
                    (None, Some(scale)) => (scale, args[0]),
                };
                self.scaled(operand, scale, depth)
            }
            TermData::App(Symbol::Named(op), _)
                if self.accept_elaborated_shifts && op == "concat" =>
            {
                // `validate` admitted this shape with `k < width`, or an atom.
                match self.elaborated_shift(term) {
                    Some((operand, shift)) => self.scaled(operand, 1u128 << shift, depth),
                    None => Some(BTreeMap::from([(Some(term), 1)])),
                }
            }
            // A LITERAL shift is `2^k * x` mod 2^width (`0` once `k` reaches the
            // width): native-lane semantics only, since `poly_simp` has no
            // `bvshl`. A symbolic amount stays one atom.
            TermData::App(Symbol::Named(op), args)
                if self.accept_elaborated_shifts && op == "bvshl" =>
            {
                match self.literal(args[1]) {
                    Some(shift) if shift < u128::from(self.width) => {
                        self.scaled(args[0], 1u128 << shift, depth)
                    }
                    Some(_) => Some(Affine::new()),
                    None => Some(BTreeMap::from([(Some(term), 1)])),
                }
            }
            _ => Some(BTreeMap::from([(Some(term), 1)])),
        }
    }

    /// `scale` times the form of `operand`, reduced modulo 2^width.
    fn scaled(&mut self, operand: TermId, scale: u128, depth: usize) -> Option<Affine> {
        let mut result = Affine::new();
        for (atom, coefficient) in self.normalize(operand, depth + 1)? {
            self.work = self.work.checked_add(1)?;
            if self.work > MAX_MERGES {
                return None;
            }
            // `u128` wrapping is exact modulo 2^128, a multiple of every
            // admitted modulus 2^width.
            let scaled = coefficient.wrapping_mul(scale) & self.mask;
            if scaled != 0 {
                result.insert(atom, scaled);
            }
        }
        Some(result)
    }

    /// `(x, k)` when `term` is exactly `concat(extract[w-k-1:0](x), 0_k)` with
    /// `x` of this width and `0 < k < width`, which denotes `2^k * x`.
    fn elaborated_shift(&self, term: TermId) -> Option<(TermId, u32)> {
        let TermData::App(Symbol::Named(op), parts) = self.terms.get(term) else {
            return None;
        };
        let [high, low] = parts.as_slice() else {
            return None;
        };
        let TermData::Const(Constant::BitVec {
            value,
            width: shift,
        }) = self.terms.get(*low)
        else {
            return None;
        };
        let TermData::App(Symbol::Indexed(extract, indices), operands) = self.terms.get(*high)
        else {
            return None;
        };
        let ([top, 0], [operand]) = (indices.as_slice(), operands.as_slice()) else {
            return None;
        };
        (op == "concat"
            && extract == "extract"
            && value.to_u128() == Some(0)
            && (1..self.width).contains(shift)
            && *top == self.width - shift - 1
            && self.terms.sort(*operand) == &Sort::bitvec(self.width))
            .then_some((*operand, *shift))
    }

    /// Whether Carcara's normal form of `term` keeps a monomial whose integer
    /// coefficient is a nonzero multiple of 2^width (module docs). The constant
    /// term is reduced without being kept, so it never counts.
    fn wraps_to_zero(&mut self, term: TermId) -> Option<bool> {
        let modulus = BigInt::from(1u8) << self.width;
        let form = self.integer_form(term, 0)?;
        Some(form.iter().any(|(monomial, coefficient)| {
            !monomial.is_empty() && !coefficient.is_zero() && (coefficient % &modulus).is_zero()
        }))
    }

    /// Whether `left = right` is a NONLINEAR identity of the polynomial ring
    /// over Z/(2^width) that Carcara's `poly_simp` replays (module docs).
    ///
    /// Both sides are expanded into Carcara's integer form and each
    /// coefficient is reduced modulo 2^width. Accepted exactly when the two
    /// sides have the same non-constant monomials, every one of them with a
    /// NONZERO residue and the same residue on both sides, and the same
    /// constant residue. That is a ring identity, so it holds for every value
    /// of the factors (a factor is a validated non-arithmetic term, the same
    /// `TermId` on both sides); and it is a subset of what `poly_simp`
    /// accepts, which keeps a monomial whose coefficient wrapped to zero and
    /// so refuses exactly the shapes excluded here.
    ///
    /// Only an identity with a monomial of degree two or more is decided
    /// here: every affine one is the affine lane's, whose verdict (and the
    /// multiplier-circuit certificate a zero product keeps) is unchanged.
    fn ring_identity(&mut self, left: TermId, right: TermId) -> Option<bool> {
        let left = self.integer_form(left, 0)?;
        let right = self.integer_form(right, 0)?;
        if !left
            .keys()
            .chain(right.keys())
            .any(|monomial| monomial.len() >= 2)
        {
            return Some(false);
        }
        let modulus = BigInt::from(1u8) << self.width;
        let residue = |coefficient: &BigInt| coefficient.mod_floor(&modulus);
        let constant =
            |form: &IntegerForm| form.get(&Vec::new()).map_or_else(BigInt::zero, residue);
        if constant(&left) != constant(&right) {
            return Some(false);
        }
        let monomials = |form: &IntegerForm| form.keys().filter(|m| !m.is_empty()).count();
        if monomials(&left) != monomials(&right) {
            return Some(false);
        }
        for (monomial, coefficient) in left.iter().filter(|(m, _)| !m.is_empty()) {
            let reduced = residue(coefficient);
            if reduced.is_zero() || right.get(monomial).map(residue) != Some(reduced) {
                return Some(false);
            }
        }
        Some(true)
    }

    /// Carcara's `poly_simp` normalization of an already validated term over
    /// the integers: `bvadd`/`bvsub`/`bvneg` add, every `bvmul` multiplies its
    /// operands' polynomials, any other term is a factor, and nothing is
    /// reduced. An elaborated shift the native lane admitted is a factor here.
    fn integer_form(&mut self, term: TermId, depth: usize) -> Option<IntegerForm> {
        self.work = self.work.checked_add(1)?;
        if self.work > MAX_MERGES || depth > MAX_DEPTH {
            return None;
        }
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, .. }) => Some(if value.is_zero() {
                IntegerForm::new()
            } else {
                IntegerForm::from([(Vec::new(), value.clone())])
            }),
            TermData::App(Symbol::Named(op), args)
                if matches!(op.as_str(), "bvadd" | "bvsub" | "bvneg") =>
            {
                let mut result = if op == "bvneg" {
                    IntegerForm::new()
                } else {
                    self.integer_form(args[0], depth + 1)?
                };
                let right = self.integer_form(args[usize::from(op != "bvneg")], depth + 1)?;
                for (monomial, coefficient) in right {
                    let coefficient = if op == "bvadd" {
                        coefficient
                    } else {
                        -coefficient
                    };
                    self.accumulate(&mut result, monomial, coefficient)?;
                }
                Some(result)
            }
            TermData::App(Symbol::Named(op), args) if op == "bvmul" => {
                let left = self.integer_form(args[0], depth + 1)?;
                let right = self.integer_form(args[1], depth + 1)?;
                let mut result = IntegerForm::new();
                for (left_monomial, left_coefficient) in &left {
                    for (right_monomial, right_coefficient) in &right {
                        let mut monomial = left_monomial.clone();
                        monomial.extend_from_slice(right_monomial);
                        monomial.sort_unstable();
                        self.accumulate(
                            &mut result,
                            monomial,
                            left_coefficient * right_coefficient,
                        )?;
                    }
                }
                Some(result)
            }
            _ => Some(IntegerForm::from([(vec![term], BigInt::from(1u8))])),
        }
    }

    /// Add `coefficient * monomial` to `form`, dropping an exact zero.
    fn accumulate(
        &mut self,
        form: &mut IntegerForm,
        monomial: Vec<TermId>,
        coefficient: BigInt,
    ) -> Option<()> {
        self.work = self.work.checked_add(monomial.len().checked_add(1)?)?;
        if self.work > MAX_MERGES {
            return None;
        }
        let next = form.remove(&monomial).unwrap_or_default() + coefficient;
        if !next.is_zero() {
            form.insert(monomial, next);
        }
        Some(())
    }

    /// The value of a validated literal bit-vector constant.
    fn literal(&self, term: TermId) -> Option<u128> {
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, .. }) => value.to_u128(),
            _ => None,
        }
    }
}

/// Only positive unit equalities enter the modular lane. Charge the complete
/// bounded attempt before traversal, including failed candidates; callers may
/// cancel before any allocation. No producer-supplied coefficients are used.
///
/// Only identities Carcara's `poly_simp` also replays.
pub(super) fn check(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<bool, ProofCheckError> {
    check_identity(terms, clause, progress, false)
}

/// [`check`], also reading elaboration's power-of-two shifts (module docs).
/// For the native strict checker only; never a wire (`poly_simp`) authority.
pub(super) fn check_native(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<bool, ProofCheckError> {
    check_identity(terms, clause, progress, true)
}

// No heap allocation before reservation: at most32 recursive source frames.
// All forms are degree<=1 with<=32 monomials. Integer coefficients need at
// most128+ceil(log2(32))=133 bits. Even two forms per frame plus four outer
// forms hold <=2*(32+4)*32 entries. A conservative1024 bytes per entry,
// including tree/key/coefficient allocation, plus stack/control is <4MiB.
// Products, indexed/opaque applications, malformed literals and longer syntax
// retain the general8MiB reserve. This selects a price, never proof authority.
fn small_linear_source(terms: &TermStore, term: TermId, width: u32, remaining: &mut usize) -> bool {
    let Some(next) = remaining.checked_sub(1) else {
        return false;
    };
    *remaining = next;
    if terms.entry_stamp(term).is_none() || terms.sort(term) != &Sort::bitvec(width) {
        return false;
    }
    match terms.get(term) {
        TermData::Var(..) => true,
        TermData::Const(Constant::BitVec {
            value,
            width: literal_width,
        }) => {
            *literal_width == width
                && value.sign() != num_bigint::Sign::Minus
                && value.bits() <= u64::from(width)
        }
        TermData::App(Symbol::Named(op), args)
            if (matches!(op.as_str(), "bvadd" | "bvsub") && args.len() == 2)
                || (op == "bvneg" && args.len() == 1) =>
        {
            args.iter()
                .all(|&arg| small_linear_source(terms, arg, width, remaining))
        }
        _ => false,
    }
}

/// Direct wire decision for the completely inspected small linear grammar.
/// This uses the existing wire checker (including its wrap-to-zero refusal),
/// rather than probing the general arithmetic/bit-blast recognizers. Every
/// recursive pass sees at most32 occurrences and degree-one forms with at
/// most32 entries; no products, opaque atoms or large DAG expansion enter.
pub(crate) fn small_linear_wire_identity(terms: &TermStore, clause: &[TermId]) -> bool {
    let Some((left, right, width)) = equality(terms, clause) else {
        return false;
    };
    let mut remaining = SMALL_LINEAR_SOURCE_NODES;
    small_linear_source(terms, left, width, &mut remaining)
        && small_linear_source(terms, right, width, &mut remaining)
        && check(terms, clause, &mut |_, _| true).unwrap_or(false)
}

fn check_identity(
    terms: &TermStore,
    clause: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
    accept_elaborated_shifts: bool,
) -> Result<bool, ProofCheckError> {
    let Some((left, right, width)) = equality(terms, clause) else {
        return Ok(false);
    };
    // Pay before the bounded price inspection, and preserve exactly the
    // original aggregate WORK debit. A refused stage never retries a lane.
    if !progress(PRICE_SCAN_WORK, 0) {
        return Err(ProofCheckError::ResourceLimit);
    }
    let mut remaining = SMALL_LINEAR_SOURCE_NODES;
    let allocation = if small_linear_source(terms, left, width, &mut remaining)
        && small_linear_source(terms, right, width, &mut remaining)
    {
        SMALL_LINEAR_ALLOCATION
    } else {
        MAX_ALLOCATION
    };
    if !progress(MAX_WORK - PRICE_SCAN_WORK, allocation) {
        return Err(ProofCheckError::ResourceLimit);
    }
    let mask = if width == 128 {
        u128::MAX
    } else {
        (1u128 << width) - 1
    };
    let mut normalizer = Normalizer {
        terms,
        width,
        mask,
        nodes: 0,
        work: 0,
        scale_constant_products: true,
        accept_elaborated_shifts,
    };
    let result = (|| {
        normalizer.validate(left, 0)?;
        normalizer.validate(right, 0)?;
        if normalizer.normalize(left, 0)? != normalizer.normalize(right, 0)? {
            // The affine form keeps a product of two non-literals as one
            // atom, so `(bvmul a b)` and `(bvmul b a)` differ there. A
            // nonlinear identity is decided by the ring lane instead.
            return normalizer.ring_identity(left, right);
        }
        // The native lane decides the modular identity itself; the wire lane
        // must also be one `poly_simp` replays (module docs).
        Some(
            accept_elaborated_shifts
                || !(normalizer.wraps_to_zero(left)? || normalizer.wraps_to_zero(right)?),
        )
    })();
    Ok(result.unwrap_or(false))
}

fn equality(terms: &TermStore, clause: &[TermId]) -> Option<(TermId, TermId, u32)> {
    let [root] = clause else { return None };
    terms.entry_stamp(*root)?;
    let TermData::App(Symbol::Named(op), args) = terms.get(*root) else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    terms.entry_stamp(*left)?;
    terms.entry_stamp(*right)?;
    let Sort::BitVec(sort) = terms.sort(*left) else {
        return None;
    };
    (op == "="
        && terms.sort(*root) == &Sort::Bool
        && terms.sort(*left) == terms.sort(*right)
        && (1..=128).contains(&sort.width))
    .then_some((*left, *right, sort.width))
}

#[cfg(test)]
mod tests;
