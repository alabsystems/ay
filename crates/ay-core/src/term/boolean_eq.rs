// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality, ITE, and distinct term constructors.
//!
//! Boolean/logical connectives (not, and, or, implies, xor) are in `boolean`.

use super::*;

impl TermStore {
    /// Create if-then-else
    /// Create a raw `ite` term WITHOUT simplification — preserves an explicit
    /// `Ite` even when the branches are equal (or the condition is constant),
    /// which the folding [`mk_ite`](Self::mk_ite) would collapse. Required when
    /// reconstructing the `(ite c x x) = x` axiom instance as a proof lemma: the
    /// `ite` must survive so the strict checker can recognize the schema.
    pub fn mk_ite_raw(&mut self, cond: TermId, then_term: TermId, else_term: TermId) -> TermId {
        debug_assert!(
            self.sort(cond) == &Sort::Bool,
            "BUG: mk_ite_raw condition must be Bool, got {:?}",
            self.sort(cond)
        );
        debug_assert!(
            self.sort(then_term) == self.sort(else_term),
            "BUG: mk_ite_raw branches must have same sort, got {:?} vs {:?}",
            self.sort(then_term),
            self.sort(else_term)
        );
        let sort = self.sort(then_term).clone();
        self.intern(TermData::Ite(cond, then_term, else_term), sort)
    }

    /// Build `(ite cond then_term else_term)`, applying local simplifications
    /// (constant/equal-branch folding, Boolean-sorted rewrites) before interning.
    pub fn mk_ite(&mut self, cond: TermId, then_term: TermId, else_term: TermId) -> TermId {
        debug_assert!(
            self.sort(cond) == &Sort::Bool,
            "BUG: mk_ite condition must be Bool, got {:?}",
            self.sort(cond)
        );
        debug_assert!(
            self.sort(then_term) == self.sort(else_term),
            "BUG: mk_ite branches must have same sort, got {:?} vs {:?}",
            self.sort(then_term),
            self.sort(else_term)
        );
        // Constant condition simplification
        match self.get(cond) {
            TermData::Const(Constant::Bool(true)) => return then_term,
            TermData::Const(Constant::Bool(false)) => return else_term,
            _ => {}
        }

        // Negated condition normalization: (ite (not c) a b) -> (ite c b a)
        // This normalizes to positive conditions, reducing structural variations
        // and potentially enabling further simplifications after the swap.
        if let Some(inner_cond) = self.get_not_inner(cond) {
            return self.mk_ite(inner_cond, else_term, then_term);
        }

        // Same branches: (ite c x x) = x
        if then_term == else_term {
            return then_term;
        }

        // Boolean branch simplifications
        let true_term = self.true_term();
        let false_term = self.false_term();

        // (ite c true false) = c
        if then_term == true_term && else_term == false_term {
            return cond;
        }

        // (ite c false true) = (not c)
        if then_term == false_term && else_term == true_term {
            return self.mk_not(cond);
        }

        // Get the result sort to check if it's Bool
        let result_sort = self.sort(then_term).clone();

        // Boolean-specific simplifications (only when result is Bool)
        if result_sort == Sort::Bool {
            // (ite c c false) = c
            if then_term == cond && else_term == false_term {
                return cond;
            }
            // (ite c true c) = c
            if then_term == true_term && else_term == cond {
                return cond;
            }
            // (ite c x false) = (and c x)
            if else_term == false_term {
                return self.mk_and(vec![cond, then_term]);
            }
            // (ite c true x) = (or c x)
            if then_term == true_term {
                return self.mk_or(vec![cond, else_term]);
            }
            // (ite c false x) = (and (not c) x)
            if then_term == false_term {
                let not_cond = self.mk_not(cond);
                return self.mk_and(vec![not_cond, else_term]);
            }
            // (ite c x true) = (or (not c) x)
            if else_term == true_term {
                let not_cond = self.mk_not(cond);
                return self.mk_or(vec![not_cond, then_term]);
            }

            // Nested ite simplifications with same condition
            // (ite c (ite c x y) z) = (ite c x z)
            if let TermData::Ite(nested_cond, nested_then, _) = self.get(then_term).clone() {
                if nested_cond == cond {
                    return self.mk_ite(cond, nested_then, else_term);
                }
            }
            // (ite c x (ite c y z)) = (ite c x z)
            if let TermData::Ite(nested_cond, _, nested_else) = self.get(else_term).clone() {
                if nested_cond == cond {
                    return self.mk_ite(cond, then_term, nested_else);
                }
            }
        }

        // Distribute `ite` through a SHARED head symbol when it COLLAPSES
        // structure: `(ite c (s a0..an) (s b0..bn)) -> (s (ite c a0 b0) ..)`.
        // SOUND by congruence for any same-symbol/same-arity application. Applied
        // ONLY when at least one argument pair is already identical, so the
        // matching `(ite c x x) = x` fields collapse and the rewrite is a NET
        // reduction (never a blow-up). This collapses a symbolic datatype
        // RECONSTRUCTION `ite`-tree — a state-machine post-state struct rebuilt
        // per branch with most fields unchanged (e.g. aterm's 14-field `Parser`,
        // where one transition touches ≤2 fields) — into a SINGLE constructor
        // with a couple of field-`ite`s, instead of materialising the whole
        // struct value once per branch. The dual of the existing selector-over-
        // `ite` fold (which already handles the READ side). (#ite-over-app)
        // Restrict to DATATYPE-sorted applications (constructors): distributing
        // through `store`/`select` (Array) or arithmetic/bv (`App`) ops can break
        // theory-specific term-shape guards (e.g. array store-commute) and is not
        // the reconstruction case we target.
        let ctor_distribute = if matches!(result_sort, Sort::Datatype(_)) {
            match (self.get(then_term), self.get(else_term)) {
                (TermData::App(s1, a1), TermData::App(s2, a2))
                    if s1 == s2
                        && a1.len() == a2.len()
                        && a1.len() >= 2
                        && a1.iter().zip(a2.iter()).any(|(x, y)| x == y) =>
                {
                    Some((s1.clone(), a1.clone(), a2.clone()))
                }
                _ => None,
            }
        } else {
            None
        };
        if let Some((sym, a1, a2)) = ctor_distribute {
            let field_ites: Vec<TermId> = a1
                .into_iter()
                .zip(a2)
                .map(|(x, y)| self.mk_ite(cond, x, y))
                .collect();
            return self.intern(TermData::App(sym, field_ites), result_sort);
        }

        self.intern(TermData::Ite(cond, then_term, else_term), result_sort)
    }

    /// Maximum depth for recursive ITE expansion inside `mk_eq`.
    ///
    /// The general rule `(= (ite c a b) val) -> (ite c (= a val) (= b val))`
    /// recurses into `mk_eq(a, val)` and `mk_eq(b, val)`. If `a` or `b` are
    /// themselves ITEs, each level doubles the number of leaf equalities. With
    /// store chains of depth N, expand_select_store creates ITE chains of depth
    /// up to `SYMBOLIC_ITE_BUDGET` (4), and variable substitution can compose
    /// multiple such chains. Unbounded expansion produces O(2^N) terms.
    ///
    /// Depth 3 allows one level of ITE decomposition (sufficient for BV/array
    /// theory reasoning) while preventing exponential blowup on deep chains.
    /// The Tseitin encoder handles deeper ITE equalities structurally.
    const EQ_ITE_EXPAND_DEPTH: u32 = 3;

    /// Create equality with constant folding and bounded ITE expansion.
    pub fn mk_eq(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        self.mk_eq_depth(lhs, rhs, Self::EQ_ITE_EXPAND_DEPTH)
    }

    /// Create equality with automatic Int/Real sort coercion.
    ///
    /// When `lhs` and `rhs` have different sorts, this method coerces
    /// Int-sorted operands to Real via `to_real` (SMT-LIB implicit
    /// coercion). This is needed at term reconstruction sites
    /// (variable substitution, value propagation, SOM normalization,
    /// E-matching) where a substitution can change the sort of a
    /// sub-term, producing `(= Int Real)` which violates `mk_eq`'s
    /// same-sort precondition.
    ///
    /// For same-sort arguments, delegates directly to `mk_eq`.
    pub fn mk_eq_coerce(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let lhs_sort = self.sort(lhs).clone();
        let rhs_sort = self.sort(rhs).clone();
        if lhs_sort == rhs_sort {
            return self.mk_eq(lhs, rhs);
        }
        // Int/Real coercion: wrap the Int side in to_real
        match (&lhs_sort, &rhs_sort) {
            (Sort::Int, Sort::Real) => {
                let lhs_real = self.mk_to_real(lhs);
                self.mk_eq(lhs_real, rhs)
            }
            (Sort::Real, Sort::Int) => {
                let rhs_real = self.mk_to_real(rhs);
                self.mk_eq(lhs, rhs_real)
            }
            _ => {
                // Non-arithmetic sort mismatch: this is a genuine bug in
                // the caller. Fire the same debug_assert as mk_eq.
                debug_assert!(
                    false,
                    "BUG: mk_eq_coerce cannot coerce {lhs_sort:?} = {rhs_sort:?}"
                );
                // In release mode, fall through to mk_eq which will
                // intern the malformed equality rather than panicking.
                self.mk_eq(lhs, rhs)
            }
        }
    }

    /// Create equality with automatic Int/Real coercion, but without the
    /// general `(= (ite ...) value)` expansion.
    ///
    /// This is intended for rebuild-only preprocessing passes where expanding
    /// every substituted equality can duplicate deep ITE chains before the
    /// bit-blaster has a chance to encode them structurally.
    pub fn mk_eq_coerce_no_ite_expand(&mut self, lhs: TermId, rhs: TermId) -> TermId {
        let lhs_sort = self.sort(lhs).clone();
        let rhs_sort = self.sort(rhs).clone();
        if lhs_sort == rhs_sort {
            return self.mk_eq_depth_mode(lhs, rhs, 0, false);
        }
        match (&lhs_sort, &rhs_sort) {
            (Sort::Int, Sort::Real) => {
                let lhs_real = self.mk_to_real(lhs);
                self.mk_eq_depth_mode(lhs_real, rhs, 0, false)
            }
            (Sort::Real, Sort::Int) => {
                let rhs_real = self.mk_to_real(rhs);
                self.mk_eq_depth_mode(lhs, rhs_real, 0, false)
            }
            _ => {
                debug_assert!(
                    false,
                    "BUG: mk_eq_coerce_no_ite_expand cannot coerce {lhs_sort:?} = {rhs_sort:?}"
                );
                self.mk_eq_depth_mode(lhs, rhs, 0, false)
            }
        }
    }

    /// Depth-limited equality constructor (#8140). When `ite_depth` reaches 0,
    /// the general ITE expansion rule is skipped. All other simplifications
    /// are always applied regardless of depth.
    fn mk_eq_depth(&mut self, lhs: TermId, rhs: TermId, ite_depth: u32) -> TermId {
        self.mk_eq_depth_mode(lhs, rhs, ite_depth, true)
    }

    fn mk_eq_depth_mode(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ite_depth: u32,
        expand_ite_equalities: bool,
    ) -> TermId {
        debug_assert!(
            self.sort(lhs) == self.sort(rhs),
            "BUG: mk_eq expects same sort, got {:?} = {:?}",
            self.sort(lhs),
            self.sort(rhs)
        );
        // Reflexive: x = x is true
        if lhs == rhs {
            return self.true_term();
        }

        // Constant folding: different constants are not equal
        // (Note: since we intern constants, if lhs != rhs and both are constants,
        // they must be different values)
        let lhs_is_const = matches!(self.get(lhs), TermData::Const(_));
        let rhs_is_const = matches!(self.get(rhs), TermData::Const(_));
        if lhs_is_const && rhs_is_const {
            return self.false_term();
        }

        // to_real-integrality rewrites for Real equality (#to-real-bridge).
        // EQUIVALENCES (safe under any polarity):
        //   to_real(a) = to_real(b)  <=>  a = b     (to_real is injective)
        //   to_real(n) = c           <=>  n = c if c integral, else FALSE
        // Termination: each recursion strips a to_real (or reaches an
        // Int-const equality). Builtin-only + Int-arg-only via get_to_real_arg.
        if *self.sort(lhs) == Sort::Real {
            if let (Some(a), Some(b)) = (self.get_to_real_arg(lhs), self.get_to_real_arg(rhs)) {
                return self.mk_eq_depth_mode(a, b, ite_depth, expand_ite_equalities);
            }
            if let Some(n) = self.get_to_real_arg(lhs) {
                if let Some(c) = self.get_rational(rhs).cloned() {
                    if c.is_integer() {
                        let ci = self.mk_int(c.to_integer());
                        return self.mk_eq_depth_mode(n, ci, ite_depth, expand_ite_equalities);
                    }
                    return self.false_term();
                }
            }
            if let Some(n) = self.get_to_real_arg(rhs) {
                if let Some(c) = self.get_rational(lhs).cloned() {
                    if c.is_integer() {
                        let ci = self.mk_int(c.to_integer());
                        return self.mk_eq_depth_mode(ci, n, ite_depth, expand_ite_equalities);
                    }
                    return self.false_term();
                }
            }
        }

        // Boolean equality simplifications (iff-style)
        // (= x true) -> x
        // (= x false) -> (not x)
        let true_term = self.true_term();
        let false_term = self.false_term();

        if rhs == true_term && *self.sort(lhs) == Sort::Bool {
            return lhs;
        }
        if lhs == true_term && *self.sort(rhs) == Sort::Bool {
            return rhs;
        }
        if rhs == false_term && *self.sort(lhs) == Sort::Bool {
            return self.mk_not(lhs);
        }
        if lhs == false_term && *self.sort(rhs) == Sort::Bool {
            return self.mk_not(rhs);
        }

        // Boolean complement detection: (= x (not x)) -> false
        // Check if lhs is (not rhs) or rhs is (not lhs)
        if *self.sort(lhs) == Sort::Bool {
            if let Some(inner) = self.get_not_inner(lhs) {
                if inner == rhs {
                    return self.false_term();
                }
            }
            if let Some(inner) = self.get_not_inner(rhs) {
                if inner == lhs {
                    return self.false_term();
                }
            }

            // Negation lifting: (= (not x) (not y)) -> (= x y)
            if let (Some(lhs_inner), Some(rhs_inner)) =
                (self.get_not_inner(lhs), self.get_not_inner(rhs))
            {
                return self.mk_eq_depth_mode(
                    lhs_inner,
                    rhs_inner,
                    ite_depth,
                    expand_ite_equalities,
                );
            }
        }

        // ITE-equality simplifications
        // (= (ite c a b) a) -> (or c (= b a))
        // (= (ite c a b) b) -> (or (not c) (= a b))
        // (= (ite c a b) (ite c x y)) -> (ite c (= a x) (= b y))

        if expand_ite_equalities {
            // Check if lhs is an ITE
            if let TermData::Ite(c, a, b) = self.get(lhs).clone() {
                // (= (ite c a b) a) -> (or c (= b a))
                if rhs == a {
                    let eq_ba = self.mk_eq_depth_mode(b, a, ite_depth, expand_ite_equalities);
                    return self.mk_or(vec![c, eq_ba]);
                }
                // (= (ite c a b) b) -> (or (not c) (= a b))
                if rhs == b {
                    let not_c = self.mk_not(c);
                    let eq_ab = self.mk_eq_depth_mode(a, b, ite_depth, expand_ite_equalities);
                    return self.mk_or(vec![not_c, eq_ab]);
                }
                // (= (ite c a b) (ite c x y)) -> (ite c (= a x) (= b y))
                if let TermData::Ite(c2, x, y) = self.get(rhs).clone() {
                    if c == c2 {
                        let eq_ax = self.mk_eq_depth_mode(a, x, ite_depth, expand_ite_equalities);
                        let eq_by = self.mk_eq_depth_mode(b, y, ite_depth, expand_ite_equalities);
                        return self.mk_ite(c, eq_ax, eq_by);
                    }
                }
            }

            // Check if rhs is an ITE (symmetric cases)
            if let TermData::Ite(c, a, b) = self.get(rhs).clone() {
                // (= a (ite c a b)) -> (or c (= b a))
                if lhs == a {
                    let eq_ba = self.mk_eq_depth_mode(b, a, ite_depth, expand_ite_equalities);
                    return self.mk_or(vec![c, eq_ba]);
                }
                // (= b (ite c a b)) -> (or (not c) (= a b))
                if lhs == b {
                    let not_c = self.mk_not(c);
                    let eq_ab = self.mk_eq_depth_mode(a, b, ite_depth, expand_ite_equalities);
                    return self.mk_or(vec![not_c, eq_ab]);
                }
            }
        }

        // General ITE expansion: (= (ite c a b) val) -> (ite c (= a val) (= b val))
        // This ensures theories can reason about each branch separately.
        // Only expand for non-Bool sorts since Bool ITE has its own simplifications.
        //
        // Depth-gated (#8140): each expansion level doubles the leaf count.
        // Deep ITE chains from expand_select_store (store chains of depth N)
        // cause O(2^N) blowup without a depth limit. When budget is exhausted,
        // the equality is left structural for the Tseitin encoder to handle.
        if expand_ite_equalities && ite_depth > 0 {
            if let TermData::Ite(c, a, b) = self.get(lhs).clone() {
                if *self.sort(a) != Sort::Bool {
                    let eq_a = self.mk_eq_depth_mode(a, rhs, ite_depth - 1, expand_ite_equalities);
                    let eq_b = self.mk_eq_depth_mode(b, rhs, ite_depth - 1, expand_ite_equalities);
                    return self.mk_ite(c, eq_a, eq_b);
                }
            }
            if let TermData::Ite(c, a, b) = self.get(rhs).clone() {
                if *self.sort(a) != Sort::Bool {
                    let eq_a = self.mk_eq_depth_mode(lhs, a, ite_depth - 1, expand_ite_equalities);
                    let eq_b = self.mk_eq_depth_mode(lhs, b, ite_depth - 1, expand_ite_equalities);
                    return self.mk_ite(c, eq_a, eq_b);
                }
            }
        }

        // Array store equality simplifications (#920, #4479)
        if let Some(result) = self.try_simplify_store_eq(lhs, rhs, ite_depth, expand_ite_equalities)
        {
            return result;
        }

        // #3421 previously normalized Bool-Bool equality to ite(a, b, not(b)).
        // Removed (#6869): the ITE decomposition destroys the equality term,
        // preventing EUF from seeing alias chains like (= b (= x y)) where
        // congruence closure needs the explicit equality. The Tseitin encoder
        // already handles Bool-Bool equalities with biconditional clauses
        // (tseitin.rs:encode_eq), so propositional semantics are preserved.

        // Canonical order
        let (a, b) = if lhs < rhs { (lhs, rhs) } else { (rhs, lhs) };
        self.intern(TermData::App(Symbol::named("="), vec![a, b]), Sort::Bool)
    }

    /// Array store equality simplifications for `mk_eq`.
    ///
    /// Handles two patterns:
    /// - Self-store (#920): `(= (store a i v) a)` -> `(= (select a i) v)`
    /// - Store-store (#4479): `(= (store a i v1) (store a i v2))` -> `(= v1 v2)`
    ///   when base and index are syntactically identical (ROW1+ROW2 soundness).
    fn try_simplify_store_eq(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        ite_depth: u32,
        expand_ite_equalities: bool,
    ) -> Option<TermId> {
        // Extract store components from lhs
        let lhs_store = match self.get(lhs).clone() {
            TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
                Some((args[0], args[1], args[2]))
            }
            _ => None,
        };
        // Extract store components from rhs
        let rhs_store = match self.get(rhs).clone() {
            TermData::App(Symbol::Named(name), args) if name == "store" && args.len() == 3 => {
                Some((args[0], args[1], args[2]))
            }
            _ => None,
        };

        // Self-store: (= (store a i v) a) -> (= (select a i) v)
        if let Some((base, idx, val)) = lhs_store {
            if rhs == base {
                let sel = self.mk_select(base, idx);
                return Some(self.mk_eq_depth_mode(sel, val, ite_depth, expand_ite_equalities));
            }
        }
        if let Some((base, idx, val)) = rhs_store {
            if lhs == base {
                let sel = self.mk_select(base, idx);
                return Some(self.mk_eq_depth_mode(sel, val, ite_depth, expand_ite_equalities));
            }
        }

        // Store-store: (= (store a i v1) (store a i v2)) -> (= v1 v2)
        if let (Some((base1, idx1, val1)), Some((base2, idx2, val2))) = (lhs_store, rhs_store) {
            if base1 == base2 && idx1 == idx2 {
                return Some(self.mk_eq_depth_mode(val1, val2, ite_depth, expand_ite_equalities));
            }
        }

        None
    }

    /// Create distinct with duplicate detection and constant folding
    ///
    /// N-ary distinct (>=3 args) is expanded to a conjunction of pairwise inequalities.
    /// This ensures all theory solvers (LIA, LRA, etc.) can reason about distinctness
    /// without needing special distinct handling. Fixes #301.
    #[allow(clippy::needless_pass_by_value)]
    pub fn mk_distinct(&mut self, args: Vec<TermId>) -> TermId {
        if args.len() <= 1 {
            return self.true_term();
        }

        debug_assert!(
            args.windows(2).all(|w| self.sort(w[0]) == self.sort(w[1])),
            "BUG: mk_distinct expects same sort args"
        );

        // Duplicate detection: if any two terms are identical, result is false
        let mut sorted_args = args.clone();
        sorted_args.sort();
        for i in 1..sorted_args.len() {
            if sorted_args[i - 1] == sorted_args[i] {
                return self.false_term();
            }
        }

        // Binary distinct: normalize to NOT(eq) so Tseitin encoding assigns
        // related CNF variables, enabling contradiction detection
        if args.len() == 2 {
            let eq = self.mk_eq(args[0], args[1]);
            return self.mk_not(eq);
        }

        // N-ary distinct (>=3 args): expand to conjunction of pairwise inequalities
        // (distinct a b c d) => (and (not (= a b)) (not (= a c)) (not (= a d))
        //                            (not (= b c)) (not (= b d)) (not (= c d)))
        // This fixes #301: LIA/LRA solvers don't handle n-ary distinct directly
        let mut pairwise_neqs = Vec::new();
        for i in 0..args.len() {
            for j in (i + 1)..args.len() {
                let eq = self.mk_eq(args[i], args[j]);
                let neq = self.mk_not(eq);
                pairwise_neqs.push(neq);
            }
        }

        // Constant folding: if all args are distinct constants, result is true
        // (Since duplicates are detected above, if all args are constants, result is true)
        let all_consts = args
            .iter()
            .all(|&id| matches!(self.get(id), TermData::Const(_)));
        if all_consts {
            return self.true_term();
        }

        self.mk_and(pairwise_neqs)
    }
}
