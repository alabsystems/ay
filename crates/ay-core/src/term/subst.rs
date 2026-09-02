// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Simultaneous, capture-respecting subterm substitution over the
//! hash-consed term DAG.
//!
//! This backs the Z3-compat `Z3_substitute` FFI entry point. Unlike
//! [`TermStore::substitute_var`] (which replaces a single `Var` by name and is
//! used for lambda beta-reduction), this performs *simultaneous* replacement of
//! arbitrary subterms matched by hash-consed [`TermId`] identity. The common
//! consumer use (KLEE/SeaHorn/angr-style symbolic execution) is replacing
//! uninterpreted constants with concrete terms.
//!
//! Rebuilt nodes go through the simplifying `mk_*` constructors so the result
//! stays interned and benefits from eager simplification: substituting `x -> 5`
//! in `(+ x 1)` yields the *same* `TermId` as building `(+ 5 1)` directly, which
//! folds to `6`.

use super::*;

/// Arity guards as slice patterns, so every element access in the rebuild
/// dispatchers below is structurally in bounds.
fn unary(args: &[TermId]) -> Option<TermId> {
    match args {
        &[a] => Some(a),
        _ => None,
    }
}

fn binary(args: &[TermId]) -> Option<(TermId, TermId)> {
    match args {
        &[a, b] => Some((a, b)),
        _ => None,
    }
}

fn ternary(args: &[TermId]) -> Option<(TermId, TermId, TermId)> {
    match args {
        &[a, b, c] => Some((a, b, c)),
        _ => None,
    }
}

impl TermStore {
    /// Simultaneously replace each `from[i]` subterm of `term` with `to[i]`.
    ///
    /// Matching is by hash-consed [`TermId`] identity (structural equality, since
    /// terms are interned). Substitution is *simultaneous*: when a node equals
    /// some `from[i]`, it is replaced by `to[i]` without recursing into `to[i]`
    /// (so an `x -> y`, `y -> x` swap genuinely swaps rather than collapsing).
    ///
    /// `from` and `to` must have equal length; only the common prefix is honored
    /// if they differ. The walk is memoized post-order over the DAG and rebuilds
    /// changed nodes via the simplifying constructors, so the result is interned.
    ///
    /// This does *not* descend through quantifier/let binders in a
    /// capture-avoiding way for `from`/`to` containing the bound variables; the
    /// intended use is replacing ground constants, which has no capture concern.
    /// Binders are still traversed structurally (their bodies are rewritten).
    pub fn substitute(&mut self, term: TermId, from: &[TermId], to: &[TermId]) -> TermId {
        if from.is_empty() || to.is_empty() {
            return term;
        }
        let mut cache = crate::kani_compat::det_hash_map_new();
        self.substitute_inner(term, from, to, &mut cache)
    }

    /// Rebuild `term` bottom-up through the simplifying `mk_*` constructors,
    /// re-applying AY's eager constant-folding and identity simplification to
    /// every node.
    ///
    /// Backs the Z3-compat `Z3_simplify` FFI entry point. AY already simplifies
    /// eagerly at construction, so a term built entirely through `mk_*` is a
    /// fixpoint of this rewrite (every reconstructed node hash-conses back to the
    /// same [`TermId`], so the result is identical). The value-add is for terms
    /// whose constant/identity subexpressions were *not* folded at build time —
    /// e.g. terms produced by a raw parser path or assembled by a consumer that
    /// did not route through the folding builders. For those, this folds the
    /// obvious cases Z3 folds: closed arithmetic to a numeral (`(+ 2 3)` -> `5`),
    /// `And`/`Or` with `true`/`false`, `x + 0`, `x * 1`, `ite(true, a, b)`,
    /// `(select (store a i v) i)`, etc.
    ///
    /// The result is **logically equivalent** to the input: each `mk_*` only
    /// performs semantics-preserving simplifications, so the rebuilt DAG denotes
    /// the same value/relation as the original.
    ///
    /// The walk is memoized post-order over the hash-consed DAG, so each distinct
    /// subterm is rebuilt once; the result is interned.
    pub fn simplify(&mut self, term: TermId) -> TermId {
        let mut cache = crate::kani_compat::det_hash_map_new();
        self.simplify_inner(term, &mut cache)
    }

    fn simplify_inner(
        &mut self,
        term: TermId,
        cache: &mut crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }

        let result = match self.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(sym, args) => {
                // Rebuild children first, then re-apply the folding constructor for
                // this operator. Even if no child changed, run it through
                // `rebuild_app` so a constant application that escaped eager
                // folding (e.g. a raw parser-built `(+ 2 3)`) collapses.
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| self.simplify_inner(arg, cache))
                    .collect();
                self.rebuild_app(&sym, new_args, term)
            }
            TermData::Not(inner) => {
                let new_inner = self.simplify_inner(inner, cache);
                self.mk_not(new_inner)
            }
            TermData::Ite(c, t, e) => {
                let nc = self.simplify_inner(c, cache);
                let nt = self.simplify_inner(t, cache);
                let ne = self.simplify_inner(e, cache);
                self.mk_ite(nc, nt, ne)
            }
            TermData::Let(bindings, body) => {
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(name, val)| (name.clone(), self.simplify_inner(*val, cache)))
                    .collect();
                let new_body = self.simplify_inner(body, cache);
                if new_bindings == bindings && new_body == body {
                    term
                } else {
                    let sort = self.sort(term).clone();
                    self.intern(TermData::Let(new_bindings, new_body), sort)
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let new_body = self.simplify_inner(body, cache);
                if new_body == body {
                    term
                } else {
                    let sort = self.sort(term).clone();
                    let rebuilt = self.intern(TermData::Forall(vars, new_body, triggers), sort);
                    self.copy_quantifier_metadata(term, rebuilt);
                    rebuilt
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let new_body = self.simplify_inner(body, cache);
                if new_body == body {
                    term
                } else {
                    let sort = self.sort(term).clone();
                    let rebuilt = self.intern(TermData::Exists(vars, new_body, triggers), sort);
                    self.copy_quantifier_metadata(term, rebuilt);
                    rebuilt
                }
            }
        };

        cache.insert(term, result);
        result
    }

    fn substitute_inner(
        &mut self,
        term: TermId,
        from: &[TermId],
        to: &[TermId],
        cache: &mut crate::kani_compat::DetHashMap<TermId, TermId>,
    ) -> TermId {
        // Direct hit: replace WITHOUT recursing into the replacement
        // (simultaneous semantics). Checked first so a top-level match wins.
        // `zip` honors only the common prefix, so unequal `from`/`to` lengths
        // need no pre-truncation.
        for (&f, &t) in from.iter().zip(to.iter()) {
            if term == f {
                return t;
            }
        }
        if let Some(&cached) = cache.get(&term) {
            return cached;
        }

        let result = match self.get(term).clone() {
            TermData::Const(_) | TermData::Var(_, _) => term,
            TermData::App(sym, args) => {
                let mut changed = false;
                let new_args: Vec<TermId> = args
                    .iter()
                    .map(|&arg| {
                        let new_arg = self.substitute_inner(arg, from, to, cache);
                        changed |= new_arg != arg;
                        new_arg
                    })
                    .collect();
                if changed {
                    self.rebuild_app(&sym, new_args, term)
                } else {
                    term
                }
            }
            TermData::Not(inner) => {
                let new_inner = self.substitute_inner(inner, from, to, cache);
                if new_inner != inner {
                    self.mk_not(new_inner)
                } else {
                    term
                }
            }
            TermData::Ite(c, t, e) => {
                let nc = self.substitute_inner(c, from, to, cache);
                let nt = self.substitute_inner(t, from, to, cache);
                let ne = self.substitute_inner(e, from, to, cache);
                if nc != c || nt != t || ne != e {
                    self.mk_ite(nc, nt, ne)
                } else {
                    term
                }
            }
            TermData::Let(bindings, body) => {
                let mut changed = false;
                let new_bindings: Vec<(String, TermId)> = bindings
                    .iter()
                    .map(|(name, val)| {
                        let new_val = self.substitute_inner(*val, from, to, cache);
                        changed |= new_val != *val;
                        (name.clone(), new_val)
                    })
                    .collect();
                let new_body = self.substitute_inner(body, from, to, cache);
                changed |= new_body != body;
                if changed {
                    let sort = self.sort(term).clone();
                    self.intern(TermData::Let(new_bindings, new_body), sort)
                } else {
                    term
                }
            }
            TermData::Forall(vars, body, triggers) => {
                let new_body = self.substitute_inner(body, from, to, cache);
                if new_body != body {
                    let sort = self.sort(term).clone();
                    let rebuilt = self.intern(TermData::Forall(vars, new_body, triggers), sort);
                    self.copy_quantifier_metadata(term, rebuilt);
                    rebuilt
                } else {
                    term
                }
            }
            TermData::Exists(vars, body, triggers) => {
                let new_body = self.substitute_inner(body, from, to, cache);
                if new_body != body {
                    let sort = self.sort(term).clone();
                    let rebuilt = self.intern(TermData::Exists(vars, new_body, triggers), sort);
                    self.copy_quantifier_metadata(term, rebuilt);
                    rebuilt
                } else {
                    term
                }
            }
        };

        cache.insert(term, result);
        result
    }

    /// Rebuild an `App(sym, args)` node using simplifying constructors where one
    /// exists for the operator, so substitution results are eagerly folded and
    /// canonicalized (e.g. `(+ 5 1)` becomes `6`). Falls back to a raw `mk_app`
    /// carrying the original node's sort for operators without a folding builder.
    ///
    /// Mirrors the dispatch used by quantifier-instantiation substitution so the
    /// two paths produce identical interned terms.
    pub fn rebuild_app(&mut self, sym: &Symbol, args: Vec<TermId>, original: TermId) -> TermId {
        // Dispatch is split by operator family: one flat match over every
        // operator exceeds Trust's per-function VC-generation budget.
        let name = sym.name();
        match name {
            "and" | "or" | "=>" | "implies" | "xor" | "=" | "distinct" => {
                self.rebuild_bool_app(name, sym, args, original)
            }
            "+" | "-" | "*" | "/" | "div" | "mod" | "rem" | "abs" | "to_int" | "to_real"
            | "is_int" | "<" | "<=" | ">" | ">=" => {
                self.rebuild_arith_app(name, sym, args, original)
            }
            "select" | "store" => self.rebuild_array_app(name, sym, args, original),
            "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor" | "bvnand" | "bvnor"
            | "bvxnor" | "bvshl" | "bvlshr" | "bvashr" | "bvudiv" | "bvurem" | "bvsdiv"
            | "bvsrem" | "bvsmod" | "bvcomp" | "bvconcat" | "concat" => {
                self.rebuild_bv_binary_app(name, sym, args, original)
            }
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
            | "bvnot" | "bvneg" => self.rebuild_bv_cmp_unary_app(name, sym, args, original),
            "extract" | "repeat" | "rotate_left" | "rotate_right" | "zero_extend"
            | "sign_extend" => self.rebuild_bv_indexed_app(name, sym, args, original),
            // Fallback: uninterpreted / other operators keep the original sort.
            _ => self.rebuild_other_app(sym, args, original),
        }
    }

    /// Shared fallback for operators without a folding builder (and for arity
    /// guard misses inside the family dispatchers): raw `mk_app` carrying the
    /// original node's sort.
    fn rebuild_other_app(&mut self, sym: &Symbol, args: Vec<TermId>, original: TermId) -> TermId {
        let sort = self.sort(original).clone();
        self.mk_app(sym.clone(), args, sort)
    }

    fn rebuild_bool_app(
        &mut self,
        name: &str,
        sym: &Symbol,
        args: Vec<TermId>,
        original: TermId,
    ) -> TermId {
        match (name, binary(&args)) {
            ("and", _) => self.mk_and(args),
            ("or", _) => self.mk_or(args),
            ("=>" | "implies", Some((a, b))) => self.mk_implies(a, b),
            ("xor", Some((a, b))) => self.mk_xor(a, b),
            ("=", Some((a, b))) => self.mk_eq_coerce(a, b),
            ("distinct", _) => self.mk_distinct(args),
            _ => self.rebuild_other_app(sym, args, original),
        }
    }

    fn rebuild_arith_app(
        &mut self,
        name: &str,
        sym: &Symbol,
        args: Vec<TermId>,
        original: TermId,
    ) -> TermId {
        match (name, unary(&args), binary(&args)) {
            ("+", ..) => self.mk_add(args),
            ("-", Some(a), _) => self.mk_neg(a),
            ("-", ..) => self.mk_sub(args),
            ("*", ..) => self.mk_mul(args),
            ("/", _, Some((a, b))) => self.mk_div(a, b),
            ("div", _, Some((a, b))) => self.mk_intdiv(a, b),
            ("mod", _, Some((a, b))) => self.mk_mod(a, b),
            ("rem", _, Some((a, b))) => self.mk_rem(a, b),
            ("abs", Some(a), _) => self.mk_abs(a),
            ("to_int", Some(a), _) => self.mk_to_int(a),
            ("to_real", Some(a), _) => self.mk_to_real(a),
            ("is_int", Some(a), _) => self.mk_is_int(a),
            ("<", _, Some((a, b))) => self.mk_lt(a, b),
            ("<=", _, Some((a, b))) => self.mk_le(a, b),
            (">", _, Some((a, b))) => self.mk_gt(a, b),
            (">=", _, Some((a, b))) => self.mk_ge(a, b),
            _ => self.rebuild_other_app(sym, args, original),
        }
    }

    fn rebuild_array_app(
        &mut self,
        name: &str,
        sym: &Symbol,
        args: Vec<TermId>,
        original: TermId,
    ) -> TermId {
        match (name, binary(&args), ternary(&args)) {
            ("select", Some((a, i)), _) => self.mk_select(a, i),
            ("store", _, Some((a, i, v))) => self.mk_store(a, i, v),
            _ => self.rebuild_other_app(sym, args, original),
        }
    }

    fn rebuild_bv_binary_app(
        &mut self,
        name: &str,
        sym: &Symbol,
        args: Vec<TermId>,
        original: TermId,
    ) -> TermId {
        let Some((a, b)) = binary(&args) else {
            return self.rebuild_other_app(sym, args, original);
        };
        match name {
            "bvadd" => self.mk_bvadd(args),
            "bvsub" => self.mk_bvsub(args),
            "bvmul" => self.mk_bvmul(args),
            "bvand" => self.mk_bvand(args),
            "bvor" => self.mk_bvor(args),
            "bvxor" => self.mk_bvxor(args),
            "bvnand" => self.mk_bvnand(args),
            "bvnor" => self.mk_bvnor(args),
            "bvxnor" => self.mk_bvxnor(args),
            "bvshl" => self.mk_bvshl(args),
            "bvlshr" => self.mk_bvlshr(args),
            "bvashr" => self.mk_bvashr(args),
            "bvudiv" => self.mk_bvudiv(args),
            "bvurem" => self.mk_bvurem(args),
            "bvsdiv" => self.mk_bvsdiv(args),
            "bvsrem" => self.mk_bvsrem(args),
            "bvsmod" => self.mk_bvsmod(args),
            "bvcomp" => self.mk_bvcomp(a, b),
            "bvconcat" | "concat" => self.mk_bvconcat(args),
            _ => self.rebuild_other_app(sym, args, original),
        }
    }

    fn rebuild_bv_cmp_unary_app(
        &mut self,
        name: &str,
        sym: &Symbol,
        args: Vec<TermId>,
        original: TermId,
    ) -> TermId {
        match (name, unary(&args), binary(&args)) {
            ("bvult", _, Some((a, b))) => self.mk_bvult(a, b),
            ("bvule", _, Some((a, b))) => self.mk_bvule(a, b),
            ("bvugt", _, Some((a, b))) => self.mk_bvugt(a, b),
            ("bvuge", _, Some((a, b))) => self.mk_bvuge(a, b),
            ("bvslt", _, Some((a, b))) => self.mk_bvslt(a, b),
            ("bvsle", _, Some((a, b))) => self.mk_bvsle(a, b),
            ("bvsgt", _, Some((a, b))) => self.mk_bvsgt(a, b),
            ("bvsge", _, Some((a, b))) => self.mk_bvsge(a, b),
            ("bvnot", Some(a), _) => self.mk_bvnot(a),
            ("bvneg", Some(a), _) => self.mk_bvneg(a),
            _ => self.rebuild_other_app(sym, args, original),
        }
    }

    fn rebuild_bv_indexed_app(
        &mut self,
        name: &str,
        sym: &Symbol,
        args: Vec<TermId>,
        original: TermId,
    ) -> TermId {
        let Some(arg) = unary(&args) else {
            return self.rebuild_other_app(sym, args, original);
        };
        match sym {
            Symbol::Indexed(_, indices) => match (name, indices.as_slice()) {
                ("extract", &[high, low, ..]) => self.mk_bvextract(high, low, arg),
                ("repeat", &[i, ..]) => self.mk_bvrepeat(i, arg),
                ("rotate_left", &[i, ..]) => self.mk_bvrotate_left(i, arg),
                ("rotate_right", &[i, ..]) => self.mk_bvrotate_right(i, arg),
                ("zero_extend", &[i, ..]) => self.mk_bvzero_extend(i, arg),
                ("sign_extend", &[i, ..]) => self.mk_bvsign_extend(i, arg),
                _ => self.rebuild_other_app(sym, args, original),
            },
            _ => self.rebuild_other_app(sym, args, original),
        }
    }
}

#[cfg(test)]
mod tests {
    use crate::sort::Sort;
    use crate::term::TermStore;

    fn store() -> TermStore {
        TermStore::new()
    }

    #[test]
    fn substitute_const_to_numeral_folds_and_interns() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        let one = s.mk_int(1.into());
        let expr = s.mk_add(vec![x, one]); // (+ x 1)

        let five = s.mk_int(5.into());
        let got = s.substitute(expr, &[x], &[five]);

        // Directly building (+ 5 1) eager-folds to 6; substitution must match.
        let direct = s.mk_add(vec![five, one]);
        let six = s.mk_int(6.into());
        assert_eq!(
            got, direct,
            "substitute result must equal directly-built term"
        );
        assert_eq!(got, six, "(+ x 1)[x:=5] must fold to 6");
    }

    #[test]
    fn substitute_swap_is_simultaneous() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        let y = s.mk_var("y", Sort::Int);
        let expr = s.mk_sub(vec![x, y]); // (- x y)

        // Swap x<->y simultaneously: (- x y) -> (- y x), NOT (- x x).
        let got = s.substitute(expr, &[x, y], &[y, x]);
        let expected = s.mk_sub(vec![y, x]);
        assert_eq!(got, expected);
        assert_ne!(got, expr);
    }

    #[test]
    fn substitute_no_match_is_noop() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        let one = s.mk_int(1.into());
        let expr = s.mk_add(vec![x, one]);

        let z = s.mk_var("z", Sort::Int);
        let five = s.mk_int(5.into());
        let got = s.substitute(expr, &[z], &[five]);
        assert_eq!(got, expr, "substituting an absent term is a no-op");
    }

    #[test]
    fn substitute_top_level_match_no_recurse_into_replacement() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        // Replacement mentions x; since the whole term IS x, we must return the
        // replacement verbatim without re-substituting x inside it.
        let one = s.mk_int(1.into());
        let repl = s.mk_add(vec![x, one]); // (+ x 1)
        let got = s.substitute(x, &[x], &[repl]);
        assert_eq!(got, repl);
    }

    #[test]
    fn substitute_empty_is_noop() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        let got = s.substitute(x, &[], &[]);
        assert_eq!(got, x);
    }

    // ---- simplify ----
    //
    // AY folds eagerly at construction, so to exercise simplify's value-add we
    // build *un-folded* terms via the raw `intern`/`mk_app` path (bypassing the
    // folding constructors), then assert simplify collapses them to the same
    // interned term the folding constructor would produce directly.

    use crate::term::{Symbol, TermData};

    /// Raw, NON-folding `(op a b)` application — bypasses the simplifying `mk_*`.
    fn raw_app(
        s: &mut TermStore,
        op: &str,
        args: Vec<crate::term::TermId>,
        sort: Sort,
    ) -> crate::term::TermId {
        s.intern(TermData::App(Symbol::named(op), args), sort)
    }

    fn attach_quantifier_metadata(
        s: &mut TermStore,
        quantifier: crate::term::TermId,
        no_pattern: crate::term::TermId,
        no_mbqi: bool,
    ) {
        if no_mbqi {
            s.mark_no_mbqi(quantifier);
        }
        s.set_quantifier_id(quantifier, "metadata-qid".to_string());
        s.set_skolem_id(quantifier, "metadata-skid".to_string());
        s.set_quantifier_weight(quantifier, 17);
        s.set_quantifier_no_patterns(quantifier, vec![no_pattern]);
    }

    fn assert_quantifier_metadata(
        s: &TermStore,
        quantifier: crate::term::TermId,
        no_pattern: crate::term::TermId,
        no_mbqi: bool,
    ) {
        assert_eq!(s.is_no_mbqi(quantifier), no_mbqi);
        assert_eq!(s.quantifier_id(quantifier), Some("metadata-qid"));
        assert_eq!(s.skolem_id(quantifier), Some("metadata-skid"));
        assert_eq!(s.explicit_quantifier_weight(quantifier), Some(17));
        assert_eq!(s.quantifier_no_patterns(quantifier), &[no_pattern]);
    }

    #[test]
    fn simplify_preserves_rebuilt_forall_metadata() {
        let mut s = store();
        let p = s.mk_var("simplify_metadata_p", Sort::Bool);
        let t = s.mk_bool(true);
        let raw_body = raw_app(&mut s, "and", vec![t, p], Sort::Bool);
        let quantifier = s.mk_forall(vec![("x".to_string(), Sort::Bool)], raw_body);
        attach_quantifier_metadata(&mut s, quantifier, p, true);

        let rebuilt = s.simplify(quantifier);

        assert_ne!(
            rebuilt, quantifier,
            "simplification must rebuild the forall"
        );
        assert!(matches!(s.get(rebuilt), TermData::Forall(_, body, _) if *body == p));
        assert_quantifier_metadata(&s, rebuilt, p, true);
    }

    #[test]
    fn substitute_preserves_rebuilt_exists_metadata() {
        let mut s = store();
        let p = s.mk_var("substitute_metadata_p", Sort::Bool);
        let replacement = s.mk_var("substitute_metadata_replacement", Sort::Bool);
        let quantifier = s.mk_exists(vec![("x".to_string(), Sort::Bool)], p);
        attach_quantifier_metadata(&mut s, quantifier, p, false);

        let rebuilt = s.substitute(quantifier, &[p], &[replacement]);

        assert_ne!(rebuilt, quantifier, "substitution must rebuild the exists");
        assert!(matches!(s.get(rebuilt), TermData::Exists(_, body, _) if *body == replacement));
        assert_quantifier_metadata(&s, rebuilt, p, false);
    }

    #[test]
    fn substitute_var_preserves_rebuilt_forall_metadata() {
        let mut s = store();
        let outer = s.mk_var("substitute_var_metadata_outer", Sort::Bool);
        let replacement = s.mk_var("substitute_var_metadata_replacement", Sort::Bool);
        let quantifier = s.mk_forall(vec![("bound".to_string(), Sort::Bool)], outer);
        attach_quantifier_metadata(&mut s, quantifier, outer, true);

        let rebuilt = s.substitute_var(quantifier, outer, replacement);

        assert_ne!(rebuilt, quantifier, "substitution must rebuild the forall");
        assert!(matches!(s.get(rebuilt), TermData::Forall(_, body, _) if *body == replacement));
        assert_quantifier_metadata(&s, rebuilt, outer, true);
    }

    #[test]
    fn substitute_terms_preserves_rebuilt_exists_metadata() {
        let mut s = store();
        let from = s.mk_var("substitute_terms_metadata_from", Sort::Bool);
        let replacement = s.mk_var("substitute_terms_metadata_replacement", Sort::Bool);
        let quantifier = s.mk_exists(vec![("bound".to_string(), Sort::Bool)], from);
        attach_quantifier_metadata(&mut s, quantifier, from, false);
        let mut substitutions = crate::kani_compat::det_hash_map_new();
        substitutions.insert(from, replacement);

        let rebuilt = s.substitute_terms(quantifier, &substitutions);

        assert_ne!(rebuilt, quantifier, "substitution must rebuild the exists");
        assert!(matches!(s.get(rebuilt), TermData::Exists(_, body, _) if *body == replacement));
        assert_quantifier_metadata(&s, rebuilt, from, false);
    }

    #[test]
    fn simplify_closed_arithmetic_folds_to_numeral() {
        let mut s = store();
        let two = s.mk_int(2.into());
        let three = s.mk_int(3.into());
        // Raw (+ 2 3): un-folded application.
        let raw = raw_app(&mut s, "+", vec![two, three], Sort::Int);
        // Sanity: the raw node is genuinely un-folded (not already the numeral 5).
        assert!(
            matches!(s.get(raw), TermData::App(_, _)),
            "raw (+ 2 3) must not be pre-folded"
        );
        let got = s.simplify(raw);
        let five = s.mk_int(5.into());
        assert_eq!(got, five, "simplify((+ 2 3)) must fold to 5");
    }

    #[test]
    fn simplify_add_zero_identity() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        let zero = s.mk_int(0.into());
        let raw = raw_app(&mut s, "+", vec![x, zero], Sort::Int);
        let got = s.simplify(raw);
        assert_eq!(got, x, "simplify((+ x 0)) must fold to x");
    }

    #[test]
    fn simplify_mul_one_identity() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        let one = s.mk_int(1.into());
        let raw = raw_app(&mut s, "*", vec![x, one], Sort::Int);
        let got = s.simplify(raw);
        assert_eq!(got, x, "simplify((* x 1)) must fold to x");
    }

    #[test]
    fn simplify_and_true_collapses() {
        let mut s = store();
        let p = s.mk_var("p", Sort::Bool);
        let t = s.mk_bool(true);
        let raw = raw_app(&mut s, "and", vec![t, p], Sort::Bool);
        let got = s.simplify(raw);
        assert_eq!(got, p, "simplify((and true p)) must fold to p");
    }

    #[test]
    fn simplify_or_false_collapses() {
        let mut s = store();
        let p = s.mk_var("p", Sort::Bool);
        let f = s.mk_bool(false);
        let raw = raw_app(&mut s, "or", vec![f, p], Sort::Bool);
        let got = s.simplify(raw);
        assert_eq!(got, p, "simplify((or false p)) must fold to p");
    }

    #[test]
    fn simplify_ite_true_picks_then() {
        let mut s = store();
        let a = s.mk_var("a", Sort::Int);
        let b = s.mk_var("b", Sort::Int);
        let t = s.mk_bool(true);
        // Raw Ite node with a constant condition.
        let raw = s.intern(TermData::Ite(t, a, b), Sort::Int);
        let got = s.simplify(raw);
        assert_eq!(got, a, "simplify((ite true a b)) must fold to a");
    }

    #[test]
    fn simplify_nested_subterm_folds() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        let two = s.mk_int(2.into());
        let three = s.mk_int(3.into());
        // Inner (+ 2 3) un-folded, wrapped in an un-folded (+ x <inner>).
        let inner = raw_app(&mut s, "+", vec![two, three], Sort::Int);
        let outer = raw_app(&mut s, "+", vec![x, inner], Sort::Int);
        let got = s.simplify(outer);
        // Direct build (+ x 5) folds nothing more, so equals (+ x 5).
        let five = s.mk_int(5.into());
        let expected = s.mk_add(vec![x, five]);
        assert_eq!(got, expected, "nested constant subterm must fold");
    }

    #[test]
    fn simplify_store_select_same_index() {
        let mut s = store();
        let arr = s.mk_var("a", Sort::array(Sort::Int, Sort::Int));
        let i = s.mk_var("i", Sort::Int);
        let v = s.mk_var("v", Sort::Int);
        // Build store via folding constructor, then a raw select on it.
        let stored = s.mk_store(arr, i, v);
        let raw_sel = raw_app(&mut s, "select", vec![stored, i], Sort::Int);
        let got = s.simplify(raw_sel);
        assert_eq!(got, v, "simplify((select (store a i v) i)) must fold to v");
    }

    #[test]
    fn simplify_already_simplified_is_fixpoint() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        let one = s.mk_int(1.into());
        // Built through folding constructors: already a fixpoint.
        let expr = s.mk_add(vec![x, one]); // (+ x 1)
        let got = s.simplify(expr);
        assert_eq!(
            got, expr,
            "simplify of an already-simplified term is identity"
        );
        // Idempotence: simplify(simplify(t)) == simplify(t).
        let got2 = s.simplify(got);
        assert_eq!(got2, got, "simplify must be idempotent");
    }

    #[test]
    fn simplify_const_and_var_are_identity() {
        let mut s = store();
        let x = s.mk_var("x", Sort::Int);
        let five = s.mk_int(5.into());
        assert_eq!(s.simplify(x), x);
        assert_eq!(s.simplify(five), five);
    }

    #[test]
    fn simplify_bitvector_constant_folds() {
        let mut s = store();
        let a = s.mk_bitvec(1.into(), 8);
        let b = s.mk_bitvec(2.into(), 8);
        let raw = raw_app(&mut s, "bvadd", vec![a, b], Sort::bitvec(8));
        let got = s.simplify(raw);
        let three = s.mk_bitvec(3.into(), 8);
        assert_eq!(got, three, "simplify((bvadd #x01 #x02)) must fold to #x03");
    }
}
