// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Canonical-constructor fold dispatch shared by value-propagation consumers.

use super::*;

impl PropagateValues {
    /// Canonical-constructor fold dispatch shared by [`Self::rewrite`] and the
    /// proof-side propagation replayer (#ppp-provenance).
    ///
    /// Rebuild `term`'s application head over `new_args` through the FOLDING
    /// constructors, so a substitution that turns arguments constant collapses
    /// exactly as the solve-pipeline pass collapsed it. Behaviour-preserving
    /// extraction of the former inline dispatch in `rewrite`; the `value_map`
    /// post-lookup stays in `rewrite` (the replayer mirrors it separately).
    ///
    /// Rebuild using canonical constructors for constant folding. BV and array
    /// constructors fold all-constant arguments, which is critical for QF_ABV
    /// benchmarks where propagation substitutes concrete array-select values.
    pub(crate) fn fold_rebuild(
        terms: &mut TermStore,
        sym: Symbol,
        term: TermId,
        new_args: Vec<TermId>,
    ) -> TermId {
        if let Some(rebuilt) = Self::fold_scalar_app(terms, &sym, &new_args) {
            return rebuilt;
        }
        if let Some(rebuilt) = Self::fold_bv_or_array_app(terms, &sym, &new_args) {
            return rebuilt;
        }
        if let Some(rebuilt) = Self::fold_indexed_app(terms, &sym, &new_args) {
            return rebuilt;
        }
        let sort = terms.sort(term).clone();
        terms.mk_app(sym, new_args, sort)
    }

    fn fold_scalar_app(terms: &mut TermStore, sym: &Symbol, new_args: &[TermId]) -> Option<TermId> {
        Some(match sym.name() {
            "=" if new_args.len() == 2 => terms.mk_eq_coerce(new_args[0], new_args[1]),
            "+" => terms.mk_add(new_args.to_vec()),
            "-" => terms.mk_sub(new_args.to_vec()),
            "*" => terms.mk_mul(new_args.to_vec()),
            "<" if new_args.len() == 2 => terms.mk_lt(new_args[0], new_args[1]),
            "<=" if new_args.len() == 2 => terms.mk_le(new_args[0], new_args[1]),
            ">" if new_args.len() == 2 => terms.mk_gt(new_args[0], new_args[1]),
            ">=" if new_args.len() == 2 => terms.mk_ge(new_args[0], new_args[1]),
            "div" if new_args.len() == 2 => terms.mk_intdiv(new_args[0], new_args[1]),
            "mod" if new_args.len() == 2 => terms.mk_mod(new_args[0], new_args[1]),
            "abs" if new_args.len() == 1 => terms.mk_abs(new_args[0]),
            "or" => terms.mk_or(new_args.to_vec()),
            "and" => terms.mk_and(new_args.to_vec()),
            "=>" if new_args.len() == 2 => terms.mk_implies(new_args[0], new_args[1]),
            "xor" if new_args.len() == 2 => terms.mk_xor(new_args[0], new_args[1]),
            _ => return None,
        })
    }

    fn fold_bv_or_array_app(
        terms: &mut TermStore,
        sym: &Symbol,
        new_args: &[TermId],
    ) -> Option<TermId> {
        Some(match sym.name() {
            "bvadd" if new_args.len() == 2 => terms.mk_bvadd(new_args.to_vec()),
            "bvsub" if new_args.len() == 2 => terms.mk_bvsub(new_args.to_vec()),
            "bvmul" if new_args.len() == 2 => terms.mk_bvmul(new_args.to_vec()),
            "bvand" if new_args.len() == 2 => terms.mk_bvand(new_args.to_vec()),
            "bvor" if new_args.len() == 2 => terms.mk_bvor(new_args.to_vec()),
            "bvxor" if new_args.len() == 2 => terms.mk_bvxor(new_args.to_vec()),
            "bvnot" if new_args.len() == 1 => terms.mk_bvnot(new_args[0]),
            "bvneg" if new_args.len() == 1 => terms.mk_bvneg(new_args[0]),
            "bvnand" if new_args.len() == 2 => terms.mk_bvnand(new_args.to_vec()),
            "bvnor" if new_args.len() == 2 => terms.mk_bvnor(new_args.to_vec()),
            "bvxnor" if new_args.len() == 2 => terms.mk_bvxnor(new_args.to_vec()),
            "bvshl" if new_args.len() == 2 => terms.mk_bvshl(new_args.to_vec()),
            "bvlshr" if new_args.len() == 2 => terms.mk_bvlshr(new_args.to_vec()),
            "bvashr" if new_args.len() == 2 => terms.mk_bvashr(new_args.to_vec()),
            "bvudiv" if new_args.len() == 2 => terms.mk_bvudiv(new_args.to_vec()),
            "bvurem" if new_args.len() == 2 => terms.mk_bvurem(new_args.to_vec()),
            "bvsdiv" if new_args.len() == 2 => terms.mk_bvsdiv(new_args.to_vec()),
            "bvsrem" if new_args.len() == 2 => terms.mk_bvsrem(new_args.to_vec()),
            "bvsmod" if new_args.len() == 2 => terms.mk_bvsmod(new_args.to_vec()),
            "bvult" if new_args.len() == 2 => terms.mk_bvult(new_args[0], new_args[1]),
            "bvule" if new_args.len() == 2 => terms.mk_bvule(new_args[0], new_args[1]),
            "bvugt" if new_args.len() == 2 => terms.mk_bvugt(new_args[0], new_args[1]),
            "bvuge" if new_args.len() == 2 => terms.mk_bvuge(new_args[0], new_args[1]),
            "bvslt" if new_args.len() == 2 => terms.mk_bvslt(new_args[0], new_args[1]),
            "bvsle" if new_args.len() == 2 => terms.mk_bvsle(new_args[0], new_args[1]),
            "bvsgt" if new_args.len() == 2 => terms.mk_bvsgt(new_args[0], new_args[1]),
            "bvsge" if new_args.len() == 2 => terms.mk_bvsge(new_args[0], new_args[1]),
            "bvcomp" if new_args.len() == 2 => terms.mk_bvcomp(new_args[0], new_args[1]),
            "concat" if new_args.len() == 2 => terms.mk_bvconcat(new_args.to_vec()),
            "bv2nat" if new_args.len() == 1 => terms.mk_bv2nat(new_args[0]),
            "select" if new_args.len() == 2 => terms.mk_select(new_args[0], new_args[1]),
            "store" if new_args.len() == 3 => terms.mk_store(new_args[0], new_args[1], new_args[2]),
            _ => return None,
        })
    }

    fn fold_indexed_app(
        terms: &mut TermStore,
        sym: &Symbol,
        new_args: &[TermId],
    ) -> Option<TermId> {
        let Symbol::Indexed(_, indices) = sym else {
            return None;
        };
        let [arg] = new_args else {
            return None;
        };
        Some(match (sym.name(), indices.as_slice()) {
            ("int2bv", [width]) => terms.mk_int2bv(*width, *arg),
            ("extract", [high, low]) => terms.mk_bvextract(*high, *low, *arg),
            ("zero_extend", [width]) => terms.mk_bvzero_extend(*width, *arg),
            ("sign_extend", [width]) => terms.mk_bvsign_extend(*width, *arg),
            ("repeat", [count]) => terms.mk_bvrepeat(*count, *arg),
            ("rotate_left", [amount]) => terms.mk_bvrotate_left(*amount, *arg),
            ("rotate_right", [amount]) => terms.mk_bvrotate_right(*amount, *arg),
            _ => return None,
        })
    }
}
