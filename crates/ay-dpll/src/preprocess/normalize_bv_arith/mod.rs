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
mod fingerprint;
mod sign_extension;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use fingerprint::PolyRelation;
#[cfg(test)]
use {
    ay_core::term::Constant,
    fingerprint::{BvLinearBudget, BV_LINEAR_MAX_WIDTH},
    num_traits::{One, Zero},
};

/// Red zone size for `stacker::maybe_grow` in BV arith normalization recursion (#8414).
const BV_NORM_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for BV arith normalization recursion.
const BV_NORM_STACK_SIZE: usize = 1024 * 1024;

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
            "concat" if args.len() >= 2 => sign_extension::rebuild_concat(terms, args),
            // Boolean ops
            "and" => terms.mk_and(args),
            "or" => terms.mk_or(args),
            "not" if args.len() == 1 => terms.mk_not(args[0]),
            "ite" if args.len() == 3 => terms.mk_ite(args[0], args[1], args[2]),
            "eq" | "=" if args.len() == 2 => {
                let same_sort = terms.sort(args[0]) == terms.sort(args[1]);
                let ring_relation = match (terms.sort(args[0]), terms.sort(args[1])) {
                    (Sort::BitVec(lhs), Sort::BitVec(rhs)) if lhs.width == rhs.width => {
                        Self::modular_poly_compare(terms, args[0], args[1], lhs.width)
                    }
                    _ => PolyRelation::Unknown,
                };
                match ring_relation {
                    PolyRelation::Equal => terms.mk_bool(true),
                    // Identical non-constant polynomial parts, different
                    // constants: false under every assignment (e.g. the
                    // `x = x + 3` location tests left by substitution on
                    // instruction-selection dumps — folding them is what
                    // collapses the surrounding ite trees pre-blast).
                    PolyRelation::NotEqual => terms.mk_bool(false),
                    PolyRelation::Unknown => {
                        if same_sort && has_ite_arg(terms, &args) {
                            terms.mk_app(Symbol::named("="), args, Sort::Bool)
                        } else {
                            terms.mk_eq_coerce_no_ite_expand(args[0], args[1])
                        }
                    }
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
