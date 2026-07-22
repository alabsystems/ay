// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BV arithmetic normalization preprocessing pass
//!
//! Canonicalizes commutative and associative BV operations (`bvadd`, `bvmul`,
//! `bvand`, `bvor`, `bvxor`) to improve term sharing and reduce CNF size
//! after bit-blasting. At BV equality boundaries it also compares bounded
//! modular polynomial fingerprints (multiset-of-monomials normal form over
//! `Z / 2^w`), closing ring identities — including nonlinear ones such as
//! `(x+y)^2 = x^2 + 2xy + y^2` — before bit-blasting.
//!
//! # Normalization
//!
//! For commutative+associative BV ops (`bvadd`, `bvmul`, `bvand`, `bvor`, `bvxor`):
//! 1. Flatten nested same-op trees into operand list
//! 2. Sort operands by TermId (deterministic ordering)
//! 3. Rebuild as left-associated binary tree (preserves binary arity)
//!
//! This ensures that syntactically different but semantically equivalent
//! expressions (e.g., `(bvadd a b)` vs `(bvadd b a)`) normalize to the
//! same canonical form.
//!
//! Note: Non-commutative ops are not globally reordered. `bvsub` and `bvneg`
//! are interpreted only by the equality-local modular polynomial fingerprint.
//!
//! # Reference
//!
//! Modeled after Bitwuzla's `PassNormalize` with AY extensions for bitwise ops:
//! - `reference/bitwuzla/src/preprocess/pass/normalize.cpp`
//! - Design: the development design notes

use super::PreprocessingPass;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::BTreeMap;

/// Red zone size for `stacker::maybe_grow` in BV arith normalization recursion (#8414).
const BV_NORM_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for BV arith normalization recursion.
const BV_NORM_STACK_SIZE: usize = 1024 * 1024;

/// Hard work bound for one modular polynomial equality comparison. Exceeding
/// it declines the optimization; it never changes the formula's meaning.
const BV_LINEAR_MAX_NODES: usize = 4096;

/// Hard bound on distinct monomials retained in one fingerprint. Product
/// expansion is exponential in nesting degree; over the cap the fold declines.
const BV_POLY_MAX_MONOMIALS: usize = 512;

/// Hard bound on one monomial's total degree (sum of exponents). Over the cap
/// the fold declines — a sound no-op, never a wrong answer.
const BV_POLY_MAX_DEGREE: u32 = 8;

/// Hard bound on modular coefficient operations. A node bound alone is not a
/// work bound: repeatedly scaling a large coefficient map is quadratic.
const BV_LINEAR_MAX_COEFFICIENT_OPS: usize = 65_536;

/// Avoid allocating and repeatedly operating on attacker-sized coefficients.
/// Wider words still take the ordinary, semantics-preserving solver path.
const BV_LINEAR_MAX_WIDTH: u32 = 4096;

#[derive(Clone, Copy, Debug)]
struct BvLinearBudget {
    nodes: usize,
    coefficient_ops: usize,
}

impl BvLinearBudget {
    fn new() -> Self {
        Self {
            nodes: BV_LINEAR_MAX_NODES,
            coefficient_ops: BV_LINEAR_MAX_COEFFICIENT_OPS,
        }
    }

    fn spend_node(&mut self) -> Option<()> {
        self.nodes = self.nodes.checked_sub(1)?;
        Some(())
    }

    fn spend_coefficient_ops(&mut self, count: usize) -> Option<()> {
        self.coefficient_ops = self.coefficient_ops.checked_sub(count)?;
        Some(())
    }
}

/// One monomial: `(atom, exponent)` pairs, strictly ascending by `TermId`,
/// every exponent `>= 1`. The empty vector is the constant-term monomial.
/// The derived lexicographic `Ord` on the sorted representation gives a
/// canonical `BTreeMap` key: equal multisets of atoms iff equal keys.
type BvMonomial = Vec<(TermId, u32)>;

/// A canonical polynomial in the modular ring `Z / 2^width` (`width` is the
/// RING width; see [`NormalizeBvArith::poly_fingerprint`] — atoms may be
/// wider terms whose values are taken mod `2^width`).
///
/// Recognized ring operators (`bvadd`, `bvsub`, `bvneg`, `bvmul`, literal
/// `bvshl`, zero-padded `concat`, low `extract`) are expanded into a
/// multiset-of-monomials normal form with coefficients canonical in
/// `[0, 2^width)`; every other term — division, symbolic shifts, bitwise
/// ops, non-low extracts, uninterpreted applications — is one indivisible
/// atom. A matching fingerprint therefore proves equality under every
/// assignment without assuming algebraic independence or assigning semantics
/// to unsupported ops. Zero-coefficient entries are deleted immediately after
/// every modular reduction so map equality IS formal-polynomial equality.
#[derive(Clone, Debug, PartialEq, Eq)]
struct BvPolyFingerprint {
    width: u32,
    coeffs: BTreeMap<BvMonomial, BigInt>,
}

impl BvPolyFingerprint {
    fn zero(width: u32) -> Self {
        Self {
            width,
            coeffs: BTreeMap::new(),
        }
    }

    fn reduced(value: BigInt, modulus: &BigInt) -> BigInt {
        let remainder = value % modulus;
        if remainder.is_negative() {
            remainder + modulus
        } else {
            remainder
        }
    }

    fn constant(width: u32, value: BigInt, modulus: &BigInt) -> Self {
        let mut result = Self::zero(width);
        let reduced = Self::reduced(value, modulus);
        if !reduced.is_zero() {
            result.coeffs.insert(BvMonomial::new(), reduced);
        }
        result
    }

    fn atom(width: u32, term: TermId) -> Self {
        let mut result = Self::zero(width);
        result.coeffs.insert(vec![(term, 1)], BigInt::one());
        result
    }

    fn add_assign(
        &mut self,
        other: Self,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<()> {
        if self.width != other.width {
            return None;
        }
        budget.spend_coefficient_ops(1 + other.coeffs.len())?;
        for (monomial, coefficient) in other.coeffs {
            let previous = self.coeffs.remove(&monomial).unwrap_or_else(BigInt::zero);
            let combined = Self::reduced(previous + coefficient, modulus);
            if !combined.is_zero() {
                self.coeffs.insert(monomial, combined);
                if self.coeffs.len() > BV_POLY_MAX_MONOMIALS {
                    return None;
                }
            }
        }
        Some(())
    }

    fn scale(
        mut self,
        coefficient: &BigInt,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<Self> {
        budget.spend_coefficient_ops(1 + self.coeffs.len())?;
        let monomials: Vec<BvMonomial> = self.coeffs.keys().cloned().collect();
        for monomial in monomials {
            let value = self.coeffs.remove(&monomial).unwrap_or_else(BigInt::zero);
            let scaled = Self::reduced(value * coefficient, modulus);
            if !scaled.is_zero() {
                self.coeffs.insert(monomial, scaled);
            }
        }
        Some(self)
    }

    fn negate(self, modulus: &BigInt, budget: &mut BvLinearBudget) -> Option<Self> {
        self.scale(&-BigInt::one(), modulus, budget)
    }

    /// Reinterpret a `Z / 2^self.width` polynomial as `2^shift * self` in the
    /// wider ring `Z / 2^new_width` where `new_width == self.width + shift`.
    ///
    /// Soundness: multiplication by `2^shift` is a ring homomorphism from
    /// `Z / 2^(w-shift)` onto the subgroup `2^shift * Z / 2^w`: for any
    /// integers `c, m`, `2^shift * (c + m * 2^(w-shift)) ≡ 2^shift * c
    /// (mod 2^w)`, so coefficients already reduced in the narrow ring rescale
    /// to exactly the right residues in the wide ring. A nonzero narrow
    /// coefficient `c < 2^(w-shift)` gives `2^shift * c < 2^w`, never zero,
    /// but zero entries are still dropped defensively to keep canonicity
    /// unconditional.
    fn embed_shifted(
        mut self,
        shift: u32,
        new_width: u32,
        new_modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<Self> {
        debug_assert_eq!(
            self.width.checked_add(shift),
            Some(new_width),
            "BUG: embed_shifted requires new_width == width + shift"
        );
        budget.spend_coefficient_ops(1 + self.coeffs.len())?;
        let factor = BigInt::one() << shift;
        let monomials: Vec<BvMonomial> = self.coeffs.keys().cloned().collect();
        for monomial in monomials {
            let value = self.coeffs.remove(&monomial).unwrap_or_else(BigInt::zero);
            let scaled = Self::reduced(value * &factor, new_modulus);
            if !scaled.is_zero() {
                self.coeffs.insert(monomial, scaled);
            }
        }
        self.width = new_width;
        Some(self)
    }

    /// Full polynomial product. The entire `|P| * |Q|` cross-product cost is
    /// pre-charged (checked) against the coefficient-op budget BEFORE any
    /// work, so work stays bounded regardless of term shape. Declines when a
    /// product monomial's total degree exceeds [`BV_POLY_MAX_DEGREE`] or the
    /// result exceeds [`BV_POLY_MAX_MONOMIALS`].
    fn multiply(
        &self,
        other: &Self,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<Self> {
        if self.width != other.width {
            return None;
        }
        let cross_terms = self.coeffs.len().checked_mul(other.coeffs.len())?;
        budget.spend_coefficient_ops(1 + cross_terms)?;
        let mut result = Self::zero(self.width);
        for (left_monomial, left_coefficient) in &self.coeffs {
            for (right_monomial, right_coefficient) in &other.coeffs {
                let monomial = Self::merge_monomials(left_monomial, right_monomial)?;
                let product = Self::reduced(left_coefficient * right_coefficient, modulus);
                if product.is_zero() {
                    continue;
                }
                let previous = result.coeffs.remove(&monomial).unwrap_or_else(BigInt::zero);
                let combined = Self::reduced(previous + product, modulus);
                if !combined.is_zero() {
                    result.coeffs.insert(monomial, combined);
                    if result.coeffs.len() > BV_POLY_MAX_MONOMIALS {
                        return None;
                    }
                }
            }
        }
        Some(result)
    }

    /// Merge two sorted exponent multisets, adding exponents of shared atoms.
    /// Every addition is checked and the running total degree is capped BEFORE
    /// the entry is committed; `None` declines the whole fingerprint.
    fn merge_monomials(left: &BvMonomial, right: &BvMonomial) -> Option<BvMonomial> {
        let mut merged = BvMonomial::with_capacity(left.len() + right.len());
        let mut total_degree: u32 = 0;
        let (mut i, mut j) = (0usize, 0usize);
        let mut push = |entry: (TermId, u32), total: &mut u32| -> Option<()> {
            *total = total.checked_add(entry.1)?;
            if *total > BV_POLY_MAX_DEGREE {
                return None;
            }
            merged.push(entry);
            Some(())
        };
        while i < left.len() && j < right.len() {
            let entry = match left[i].0.cmp(&right[j].0) {
                std::cmp::Ordering::Less => {
                    let entry = left[i];
                    i += 1;
                    entry
                }
                std::cmp::Ordering::Greater => {
                    let entry = right[j];
                    j += 1;
                    entry
                }
                std::cmp::Ordering::Equal => {
                    let exponent = left[i].1.checked_add(right[j].1)?;
                    let entry = (left[i].0, exponent);
                    i += 1;
                    j += 1;
                    entry
                }
            };
            push(entry, &mut total_degree)?;
        }
        for &entry in &left[i..] {
            push(entry, &mut total_degree)?;
        }
        for &entry in &right[j..] {
            push(entry, &mut total_degree)?;
        }
        Some(merged)
    }
}

/// Check if a BV operation is commutative and associative (normalizable).
fn is_commutative_bv_op(name: &str) -> bool {
    matches!(name, "bvadd" | "bvmul" | "bvand" | "bvor" | "bvxor")
}

fn has_canonical_constructor(symbol: &Symbol) -> bool {
    match symbol {
        Symbol::Named(name) => matches!(
            name.as_str(),
            "=" | "eq"
                | "and"
                | "or"
                | "ite"
                | "bvadd"
                | "bvsub"
                | "bvmul"
                | "bvand"
                | "bvor"
                | "bvxor"
                | "bvnot"
                | "bvneg"
                | "bvshl"
                | "bvlshr"
                | "bvashr"
                | "bvudiv"
                | "bvurem"
                | "bvsdiv"
                | "bvsrem"
                | "bvsmod"
                | "bvult"
                | "bvule"
                | "bvugt"
                | "bvuge"
                | "bvslt"
                | "bvsle"
                | "bvsgt"
                | "bvsge"
                | "bvcomp"
                | "concat"
                | "select"
                | "store"
        ),
        Symbol::Indexed(name, _) => {
            matches!(name.as_str(), "extract" | "zero_extend" | "sign_extend")
        }
        _ => false,
    }
}

fn has_ite_arg(terms: &TermStore, args: &[TermId]) -> bool {
    args.iter()
        .any(|&arg| matches!(terms.get(arg), TermData::Ite(_, _, _)))
}

/// Normalizes BV arithmetic expressions for canonical form.
pub(crate) struct NormalizeBvArith {
    /// Cache: original term -> normalized term
    cache: HashMap<TermId, TermId>,
}

impl NormalizeBvArith {
    /// Create a new BV arithmetic normalization pass.
    pub(crate) fn new() -> Self {
        Self {
            cache: HashMap::default(),
        }
    }

    /// Normalize a term recursively, returning the normalized TermId.
    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    fn normalize(&mut self, terms: &mut TermStore, id: TermId) -> TermId {
        stacker::maybe_grow(BV_NORM_STACK_RED_ZONE, BV_NORM_STACK_SIZE, || {
            // Check cache first
            if let Some(&cached) = self.cache.get(&id) {
                return cached;
            }

            let result = match terms.get(id).clone() {
                TermData::App(sym, args) => {
                    let name = sym.name();

                    // Recursively normalize children first
                    let normalized_args: Vec<TermId> =
                        args.iter().map(|&a| self.normalize(terms, a)).collect();

                    // Canonicalize only an exact, well-formed named builtin.
                    // Raw/native replay terms can contain indexed lookalikes,
                    // zero-arity apps, or inconsistent child sorts; those must
                    // remain opaque instead of being reinterpreted or panicking.
                    let commutative_width = if matches!(&sym, Symbol::Named(_))
                        && is_commutative_bv_op(name)
                        && normalized_args.len() == 2
                    {
                        match terms.sort(id) {
                            Sort::BitVec(result_bv)
                                if normalized_args.iter().all(|&arg| {
                                    matches!(terms.sort(arg), Sort::BitVec(arg_bv) if arg_bv.width == result_bv.width)
                                }) => Some(result_bv.width),
                            _ => None,
                        }
                    } else {
                        None
                    };

                    if let Some(width) = commutative_width {
                        // Flatten and canonicalize
                        let mut operands = Vec::new();
                        Self::flatten_op(terms, name, width, &normalized_args, &mut operands);

                        // Sort by TermId for canonical ordering
                        operands.sort_by_key(|t| t.index());

                        // Rebuild as left-associated binary tree
                        self.rebuild_binary_tree(terms, name, operands, width)
                    } else if is_commutative_bv_op(name) {
                        // Preserve malformed or indexed builtin-lookalikes.
                        if normalized_args == args {
                            id
                        } else {
                            let sort = terms.sort(id).clone();
                            terms.mk_app(sym, normalized_args, sort)
                        }
                    } else if normalized_args != args || has_canonical_constructor(&sym) {
                        // Rebuild known operations through canonical constructors even when
                        // children are unchanged. Parsed terms may not have gone through the
                        // specialized builders, and QF_ABV relies on folding constant BV
                        // guards before read-over-write simplification.
                        self.rebuild_app(terms, id, sym, normalized_args)
                    } else {
                        id
                    }
                }
                TermData::Not(inner) => {
                    let normalized_inner = self.normalize(terms, inner);
                    if normalized_inner == inner {
                        id
                    } else {
                        terms.mk_not(normalized_inner)
                    }
                }
                TermData::Ite(cond, then_term, else_term) => {
                    let normalized_cond = self.normalize(terms, cond);
                    let normalized_then = self.normalize(terms, then_term);
                    let normalized_else = self.normalize(terms, else_term);
                    if normalized_cond == cond
                        && normalized_then == then_term
                        && normalized_else == else_term
                    {
                        id
                    } else {
                        terms.mk_ite(normalized_cond, normalized_then, normalized_else)
                    }
                }
                // Other non-application terms: no normalization needed
                _ => id,
            };

            self.cache.insert(id, result);
            result
        }) // stacker::maybe_grow
    }

    /// Flatten nested operations of the same kind into a flat operand list.
    fn flatten_op(
        terms: &TermStore,
        op_name: &str,
        width: u32,
        args: &[TermId],
        operands: &mut Vec<TermId>,
    ) {
        let mut stack: Vec<TermId> = args.iter().rev().copied().collect();

        while let Some(arg) = stack.pop() {
            // Check if arg is the same operation
            if let TermData::App(Symbol::Named(child_name), child_args) = terms.get(arg) {
                if child_name == op_name
                    && child_args.len() == 2
                    && child_args.iter().all(
                        |&child| matches!(terms.sort(child), Sort::BitVec(bv) if bv.width == width),
                    )
                {
                    // Push in reverse so the explicit stack preserves the recursive order.
                    stack.extend(child_args.iter().rev().copied());
                    continue;
                }
            }
            // Not same op: add as operand
            operands.push(arg);
        }
    }

    /// Rebuild a flat operand list as a left-associated binary tree.
    fn rebuild_binary_tree(
        &self,
        terms: &mut TermStore,
        op_name: &str,
        operands: Vec<TermId>,
        width: u32,
    ) -> TermId {
        debug_assert!(
            !operands.is_empty(),
            "BUG: empty operands in rebuild_binary_tree"
        );

        if operands.len() == 1 {
            return operands[0];
        }

        // Build left-associated: ((a + b) + c) + d
        let mut result = operands[0];
        for &operand in &operands[1..] {
            result = match op_name {
                "bvadd" => terms.mk_bvadd(vec![result, operand]),
                "bvmul" => terms.mk_bvmul(vec![result, operand]),
                "bvand" => terms.mk_bvand(vec![result, operand]),
                "bvor" => terms.mk_bvor(vec![result, operand]),
                "bvxor" => terms.mk_bvxor(vec![result, operand]),
                _ => unreachable!("BUG: unknown commutative BV op: {}", op_name),
            };

            // Verify width is preserved
            debug_assert!(
                matches!(terms.sort(result), Sort::BitVec(bv) if bv.width == width),
                "BUG: width changed during rebuild"
            );
        }

        result
    }

    /// Prove two same-width BV terms equal by comparing canonical polynomials
    /// in `Z / 2^width`. Failure to recognize or stay within budget simply
    /// declines the fold.
    ///
    /// The conclusion is strictly one-sided: equal fingerprints prove equality
    /// under every assignment (folding `=` to true is verdict-preserving), but
    /// a mismatch concludes NOTHING and falls through to bit-blasting —
    /// formally distinct polynomials can still be semantically equal (at
    /// width 1, `x*x` and `x` agree everywhere yet differ formally).
    fn modular_poly_equal(terms: &TermStore, lhs: TermId, rhs: TermId, width: u32) -> bool {
        if width == 0 || width > BV_LINEAR_MAX_WIDTH {
            return false;
        }
        // Construct the potentially width-sized modulus once per comparison;
        // every recursive reduction borrows it.
        let modulus = BigInt::one() << width;
        let mut budget = BvLinearBudget::new();
        let Some(lhs) = Self::poly_fingerprint(terms, lhs, width, &modulus, &mut budget) else {
            return false;
        };
        let Some(rhs) = Self::poly_fingerprint(terms, rhs, width, &modulus, &mut budget) else {
            return false;
        };
        lhs == rhs
    }

    /// Collect a modular polynomial fingerprint of `term` in the ring
    /// `Z / 2^ring_width`. Unsupported terms are opaque atoms; only operators
    /// whose ring meaning is exact are expanded.
    ///
    /// `ring_width` may be SMALLER than the term's own bit width (never
    /// larger): reduction mod `2^ring_width` is a ring homomorphism from
    /// `Z / 2^term_width` whenever `ring_width <= term_width`, so a term
    /// well-formed at its own width denotes, in the smaller ring, exactly its
    /// formal polynomial evaluated at the atoms' values mod `2^ring_width`.
    /// This is what lets the collector see through the constructor lowerings
    /// of constant multiplication: `mk_bvmul(2^k, t)` is stored as
    /// `concat(extract(t, w-k-1, 0), 0_k)` — and `mk_bvextract` further
    /// rewrites `extract(w-k-1, 0, bvmul(X, Y))` into
    /// `bvmul(extract(X), extract(Y))` — both of which are exact ring
    /// operations under the two rules below (zero-padded concat = scale by
    /// `2^k` from the narrower ring; low-extract = the mod-`2^(hi+1)`
    /// homomorphism).
    ///
    /// Every arm verifies operand sorts against the term's OWN stored width
    /// before assigning ring semantics, so malformed raw applications (mixed
    /// widths, forged sorts, indexed builtin-lookalikes) stay opaque atoms or
    /// decline — never a wrong interpretation.
    fn poly_fingerprint(
        terms: &TermStore,
        term: TermId,
        ring_width: u32,
        modulus: &BigInt,
        budget: &mut BvLinearBudget,
    ) -> Option<BvPolyFingerprint> {
        stacker::maybe_grow(BV_NORM_STACK_RED_ZONE, BV_NORM_STACK_SIZE, || {
            let term_width = match terms.sort(term) {
                Sort::BitVec(bv) if bv.width >= ring_width => bv.width,
                _ => return None,
            };
            budget.spend_node()?;

            if let Some(value) = Self::bitvec_constant(terms, term, term_width) {
                budget.spend_coefficient_ops(1)?;
                return Some(BvPolyFingerprint::constant(ring_width, value, modulus));
            }

            let TermData::App(sym, args) = terms.get(term) else {
                return Some(BvPolyFingerprint::atom(ring_width, term));
            };
            // Indexed symbols with a builtin-looking base name are not the
            // corresponding SMT-LIB builtin — except the genuine indexed
            // `extract`, whose low slice is interpreted below. Only exact
            // symbols may be interpreted algebraically by this trusted fold.
            let name = match sym {
                Symbol::Named(name) => name,
                Symbol::Indexed(name, indices)
                    if name == "extract" && indices.len() == 2 && args.len() == 1 =>
                {
                    // extract(hi, 0, t) denotes t mod 2^(hi+1). With
                    // ring_width <= hi+1 (implied by term_width >= ring_width
                    // and the sort check below), the ring value is t mod
                    // 2^ring_width: recurse into t in the SAME ring. Require
                    // the stored sort to match the indices exactly and the
                    // source to be wide enough — anything else is malformed
                    // and stays an opaque atom.
                    let source = args[0];
                    let well_formed = indices[1] == 0
                        && indices[0].checked_add(1) == Some(term_width)
                        && matches!(terms.sort(source), Sort::BitVec(bv) if bv.width > indices[0]);
                    return if well_formed {
                        Self::poly_fingerprint(terms, source, ring_width, modulus, budget)
                    } else {
                        Some(BvPolyFingerprint::atom(ring_width, term))
                    };
                }
                _ => return Some(BvPolyFingerprint::atom(ring_width, term)),
            };

            // Ring semantics require the application to be well-formed at its
            // own stored width: every operand's sort must be exactly
            // BitVec(term_width) (concat is the exception, handled in-arm).
            let operands_well_formed = |arg_ids: &[TermId]| {
                arg_ids.iter().all(
                    |&arg| matches!(terms.sort(arg), Sort::BitVec(bv) if bv.width == term_width),
                )
            };

            match name.as_str() {
                "bvadd" if !args.is_empty() && operands_well_formed(args) => {
                    let mut sum = BvPolyFingerprint::zero(ring_width);
                    for &arg in args {
                        let part = Self::poly_fingerprint(terms, arg, ring_width, modulus, budget)?;
                        sum.add_assign(part, modulus, budget)?;
                    }
                    Some(sum)
                }
                "bvsub" if args.len() == 2 && operands_well_formed(args) => {
                    let mut lhs =
                        Self::poly_fingerprint(terms, args[0], ring_width, modulus, budget)?;
                    let rhs = Self::poly_fingerprint(terms, args[1], ring_width, modulus, budget)?
                        .negate(modulus, budget)?;
                    lhs.add_assign(rhs, modulus, budget)?;
                    Some(lhs)
                }
                "bvneg" if args.len() == 1 && operands_well_formed(args) => Some(
                    Self::poly_fingerprint(terms, args[0], ring_width, modulus, budget)?
                        .negate(modulus, budget)?,
                ),
                "bvmul" if args.len() >= 2 && operands_well_formed(args) => {
                    // Full polynomial product over all operands. A literal
                    // operand is just a constant polynomial; variable-by-
                    // variable products expand into higher-degree monomials,
                    // capped by degree/monomial-count bounds.
                    let mut product =
                        Self::poly_fingerprint(terms, args[0], ring_width, modulus, budget)?;
                    for &arg in &args[1..] {
                        let factor =
                            Self::poly_fingerprint(terms, arg, ring_width, modulus, budget)?;
                        product = product.multiply(&factor, modulus, budget)?;
                    }
                    Some(product)
                }
                "bvshl" if args.len() == 2 && operands_well_formed(args) => {
                    let Some(shift) = Self::bitvec_constant(terms, args[1], term_width) else {
                        return Some(BvPolyFingerprint::atom(ring_width, term));
                    };
                    // A shift amount too large for u32 is necessarily >= the
                    // u32-sized ring width, hence the ring value is zero
                    // (2^shift ≡ 0 mod 2^ring_width; for shift >= term_width
                    // SMT-LIB also defines the whole word to be zero).
                    let Some(shift) = shift.to_u32() else {
                        return Some(BvPolyFingerprint::zero(ring_width));
                    };
                    if shift >= ring_width {
                        return Some(BvPolyFingerprint::zero(ring_width));
                    }
                    let coefficient = BigInt::one() << shift;
                    Some(
                        Self::poly_fingerprint(terms, args[0], ring_width, modulus, budget)?
                            .scale(&coefficient, modulus, budget)?,
                    )
                }
                "concat" if args.len() == 2 => {
                    // concat(high, 0_k) denotes 2^k * val(high) with
                    // val(high) < 2^(term_width - k): collect `high` in the
                    // NARROWER ring Z/2^(ring_width - k) and rescale via
                    // `embed_shifted` (the 2^k homomorphism). Requires the
                    // concat to be well-formed: the zero low part's constant
                    // width matches its sort, and child widths sum to the
                    // stored width. k >= ring_width makes the ring value zero.
                    let (high, low) = (args[0], args[1]);
                    let shift = match terms.get(low) {
                        TermData::Const(Constant::BitVec {
                            value,
                            width: low_width,
                        }) if value.is_zero() => *low_width,
                        _ => return Some(BvPolyFingerprint::atom(ring_width, term)),
                    };
                    let widths_consistent = shift > 0
                        && matches!(terms.sort(low), Sort::BitVec(bv) if bv.width == shift)
                        && matches!(
                            terms.sort(high),
                            Sort::BitVec(bv)
                                if bv.width.checked_add(shift) == Some(term_width)
                        );
                    if !widths_consistent {
                        return Some(BvPolyFingerprint::atom(ring_width, term));
                    }
                    if shift >= ring_width {
                        return Some(BvPolyFingerprint::zero(ring_width));
                    }
                    let narrow_width = ring_width - shift;
                    let narrow_modulus = BigInt::one() << narrow_width;
                    Some(
                        Self::poly_fingerprint(terms, high, narrow_width, &narrow_modulus, budget)?
                            .embed_shifted(shift, ring_width, modulus, budget)?,
                    )
                }
                _ => Some(BvPolyFingerprint::atom(ring_width, term)),
            }
        })
    }

    fn bitvec_constant(terms: &TermStore, term: TermId, width: u32) -> Option<BigInt> {
        match terms.get(term) {
            TermData::Const(Constant::BitVec {
                value,
                width: constant_width,
            }) if *constant_width == width
                && !value.is_negative()
                && value.bits() <= u64::from(width) =>
            {
                Some(value.clone())
            }
            _ => None,
        }
    }

    /// Rebuild an application term with new arguments.
    fn rebuild_app(
        &self,
        terms: &mut TermStore,
        original: TermId,
        sym: Symbol,
        args: Vec<TermId>,
    ) -> TermId {
        // Only extract/extension operators are genuinely indexed builtins in
        // this pass. Preserve every other indexed name exactly; matching on
        // `Symbol::name()` below would otherwise reinterpret a lookalike as a
        // named builtin.
        if matches!(&sym, Symbol::Indexed(name, _) if !matches!(name.as_str(), "extract" | "zero_extend" | "sign_extend"))
        {
            let sort = terms.sort(original).clone();
            return terms.mk_app(sym, args, sort);
        }
        // Use TermStore's existing mk_* methods when available for simplification
        let name = sym.name();
        match name {
            // Binary BV ops
            "bvadd" => terms.mk_bvadd(args),
            "bvsub" if args.len() == 2 => terms.mk_bvsub(args),
            "bvmul" => terms.mk_bvmul(args),
            "bvand" => terms.mk_bvand(args),
            "bvor" => terms.mk_bvor(args),
            "bvxor" => terms.mk_bvxor(args),
            // Unary BV ops
            "bvneg" if args.len() == 1 => terms.mk_bvneg(args[0]),
            "bvnot" if args.len() == 1 => terms.mk_bvnot(args[0]),
            // BV shifts
            "bvshl" if args.len() == 2 => terms.mk_bvshl(args),
            "bvlshr" if args.len() == 2 => terms.mk_bvlshr(args),
            "bvashr" if args.len() == 2 => terms.mk_bvashr(args),
            // BV division/remainder
            "bvudiv" if args.len() == 2 => terms.mk_bvudiv(args),
            "bvurem" if args.len() == 2 => terms.mk_bvurem(args),
            "bvsdiv" if args.len() == 2 => terms.mk_bvsdiv(args),
            "bvsrem" if args.len() == 2 => terms.mk_bvsrem(args),
            "bvsmod" if args.len() == 2 => terms.mk_bvsmod(args),
            // BV comparisons
            "bvult" if args.len() == 2 => terms.mk_bvult(args[0], args[1]),
            "bvule" if args.len() == 2 => terms.mk_bvule(args[0], args[1]),
            "bvugt" if args.len() == 2 => terms.mk_bvugt(args[0], args[1]),
            "bvuge" if args.len() == 2 => terms.mk_bvuge(args[0], args[1]),
            "bvslt" if args.len() == 2 => terms.mk_bvslt(args[0], args[1]),
            "bvsle" if args.len() == 2 => terms.mk_bvsle(args[0], args[1]),
            "bvsgt" if args.len() == 2 => terms.mk_bvsgt(args[0], args[1]),
            "bvsge" if args.len() == 2 => terms.mk_bvsge(args[0], args[1]),
            "bvcomp" if args.len() == 2 => terms.mk_bvcomp(args[0], args[1]),
            "concat" if args.len() >= 2 => terms.mk_bvconcat(args),
            // Boolean ops
            "and" => terms.mk_and(args),
            "or" => terms.mk_or(args),
            "not" if args.len() == 1 => terms.mk_not(args[0]),
            "ite" if args.len() == 3 => terms.mk_ite(args[0], args[1], args[2]),
            "eq" | "=" if args.len() == 2 => {
                let same_sort = terms.sort(args[0]) == terms.sort(args[1]);
                let ring_identity = match (terms.sort(args[0]), terms.sort(args[1])) {
                    (Sort::BitVec(lhs), Sort::BitVec(rhs)) if lhs.width == rhs.width => {
                        Self::modular_poly_equal(terms, args[0], args[1], lhs.width)
                    }
                    _ => false,
                };
                if ring_identity {
                    terms.mk_bool(true)
                } else if same_sort && has_ite_arg(terms, &args) {
                    terms.mk_app(Symbol::named("="), args, Sort::Bool)
                } else {
                    terms.mk_eq_coerce_no_ite_expand(args[0], args[1])
                }
            }
            // Array ops
            "select" if args.len() == 2 => terms.mk_select(args[0], args[1]),
            "store" if args.len() == 3 => terms.mk_store(args[0], args[1], args[2]),
            // Indexed BV ops
            "extract" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 2 {
                        return terms.mk_bvextract(indices[0], indices[1], args[0]);
                    }
                }
                terms.mk_app(sym, args, terms.sort(original).clone())
            }
            "zero_extend" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 1 {
                        return terms.mk_bvzero_extend(indices[0], args[0]);
                    }
                }
                terms.mk_app(sym, args, terms.sort(original).clone())
            }
            "sign_extend" if args.len() == 1 => {
                if let Symbol::Indexed(_, indices) = &sym {
                    if indices.len() == 1 {
                        return terms.mk_bvsign_extend(indices[0], args[0]);
                    }
                }
                terms.mk_app(sym, args, terms.sort(original).clone())
            }
            _ => {
                // Generic rebuild using public mk_app
                terms.mk_app(sym, args, terms.sort(original).clone())
            }
        }
    }
}

impl Default for NormalizeBvArith {
    fn default() -> Self {
        Self::new()
    }
}

impl PreprocessingPass for NormalizeBvArith {
    fn apply(&mut self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        let mut modified = false;

        for assertion in assertions.iter_mut() {
            let normalized = self.normalize(terms, *assertion);
            if normalized != *assertion {
                *assertion = normalized;
                modified = true;
            }
        }

        modified
    }

    fn reset(&mut self) {
        self.cache.clear();
    }
}

#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
