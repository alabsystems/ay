// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Expression conversion: CHC expressions to ay-core terms.

use super::context::{SmtContext, MAX_CONVERSION_NODES};
use crate::term_bridge::sort::chc_sort_to_core;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::term::Symbol;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;
use num_rational::BigRational;
use std::fmt::Write;

impl SmtContext {
    pub fn preprocess(expr: &ChcExpr) -> ChcExpr {
        // #6360: Single-pass feature scan replaces 6 individual `contains_*` walks.
        let initial_features = expr.scan_features();

        // Simplify select-store chains FIRST (#6047/#8664): reduces
        // select(store(a, i, v), i) → v via ROW axioms at the expression level,
        // and expands short symbolic store chains into ITEs before SMT feature
        // routing decides whether Array theory support is still needed.
        let array_simplified = if initial_features.has_array_ops {
            expr.simplify_array_ops().expand_select_store_symbolic()
        } else {
            expr.clone()
        };
        let features = array_simplified.scan_features();
        let simplified = array_simplified.propagate_constants();
        // #6360: shared core normalization chain (mixed-sort eq → ITE → mod →
        // negation → strict comparison).
        features.core_normalize(simplified)
    }

    /// Convert a CHC sort to a ay-core sort
    pub fn convert_sort(sort: &ChcSort) -> Sort {
        chc_sort_to_core(sort)
    }

    /// Get or create a term for a CHC variable.
    ///
    /// #6100: Always uses sort-qualified names (`{name}_{sort}`) as var_map keys
    /// to ensure deterministic TermId assignment regardless of variable encounter
    /// order. This eliminates warm/fresh context divergence where accumulated
    /// var_map entries from prior PDR iterations changed which sort got the
    /// unqualified name.
    ///
    /// The original CHC variable name is stored in `var_original_names` so that
    /// model extraction can emit original names for downstream lookups.
    fn get_or_create_var(&mut self, var: &ChcVar) -> TermId {
        // #6363: Build the sort-qualified key in a reusable scratch buffer
        // instead of allocating a fresh String on every lookup. On cache hits
        // (the common case), zero allocations occur.
        self.qualified_name_buf.clear();
        let _ = write!(self.qualified_name_buf, "{}_{}", var.name, var.sort);

        if let Some(&term) = self.var_map.get(self.qualified_name_buf.as_str()) {
            return term;
        }

        // Cache miss: allocate the key string for map insertion.
        let qualified_name: String = self.qualified_name_buf.clone();
        let sort = Self::convert_sort(&var.sort);
        let term = self.terms.mk_var(&qualified_name, sort);
        self.var_original_names
            .insert(qualified_name.clone(), var.name.clone());
        self.var_map.insert(qualified_name, term);
        term
    }

    /// Convert a CHC expression to a ay-core term
    pub fn convert_expr(&mut self, expr: &ChcExpr) -> TermId {
        // Guard against stack overflow on deep expression trees (e.g., from PDKind
        // iterations building deep conjunctions). Uses stacker to grow onto heap
        // when the thread stack runs low — matching the protection in expr.rs
        // traversals (#2759).
        crate::expr::maybe_grow_expr_stack(|| self.convert_expr_inner(expr))
    }

    /// Reset the conversion budget for a new conversion session.
    pub(crate) fn reset_conversion_budget(&mut self) {
        self.conversion_node_count = 0;
        self.conversion_budget_exceeded = false;
        self.ill_typed_bv_count = 0;
    }

    /// Return whether the conversion budget was exceeded in the current session.
    pub(crate) fn conversion_budget_exceeded(&self) -> bool {
        self.conversion_budget_exceeded
    }

    /// Return whether the conversion budget has been exhausted across multiple
    /// consecutive `check_sat` calls (#2472).
    ///
    /// Once this returns `true`, all future `check_sat` calls on this context
    /// will short-circuit to `Unknown`. Engines should check this in their main
    /// loops to terminate early rather than retrying doomed queries.
    pub(crate) fn is_budget_exhausted(&self) -> bool {
        self.conversion_budget_strikes >= super::context::MAX_CONVERSION_STRIKES
    }

    /// Check if all terms in the slice have BitVec sort.
    ///
    /// #6047: Array-sorted variables can appear in BV operations due to
    /// `translate_to_canonical_names` followed by `propagate_var_equalities`
    /// in `propagate_constants`. This defensive check prevents panics in
    /// ay-core's BV constructors (mk_bvult, mk_bvadd, etc.).
    fn all_bv_sorted(&self, terms: &[TermId]) -> bool {
        terms
            .iter()
            .all(|t| matches!(self.terms.sort(*t), Sort::BitVec(_)))
    }

    /// Check that a binary BV core builder can accept these operands.
    ///
    /// Core BV arithmetic/comparison constructors require exactly two BitVec
    /// operands with identical widths. CHC preprocessing can expose ill-typed
    /// BV atoms after sort-changing substitutions; guard here so the caller
    /// receives `Unknown` instead of tripping ay-core debug assertions.
    fn well_sorted_binary_bv_args(&self, terms: &[TermId]) -> bool {
        terms.len() == 2
            && self.all_bv_sorted(terms)
            && self.terms.sort(terms[0]) == self.terms.sort(terms[1])
    }

    /// Record an ill-typed BV operation and return the budget-exceeded sentinel.
    ///
    /// #6047 soundness fix: Previously returned `mk_bool(false)` which injects
    /// `false` into the formula. This is unsound in predecessor/inductiveness
    /// queries where false makes the query artificially UNSAT (same pattern as
    /// #5508 Bool ordering bug). Instead, set `conversion_budget_exceeded` so
    /// the caller returns `SmtResult::Unknown`, letting PDR handle the uncertainty
    /// conservatively at each call site.
    fn ill_typed_bv_sentinel(&mut self) -> TermId {
        self.ill_typed_bv_count += 1;
        self.conversion_budget_exceeded = true;
        self.terms.mk_bool(true)
    }

    /// Coerce a pair of comparison operands to compatible sorts (#7126).
    ///
    /// BV-to-Int abstraction can produce mixed-sort comparisons (e.g., Int <= Bool
    /// or Bool >= BV). This coerces both operands to the same sort:
    /// - If sorts already match, no-op.
    /// - BV vs Int: use `coerce_int_bv_pair` (existing logic).
    /// - Bool vs Int/BV: coerce Bool to Int via ITE(b, 1, 0), then retry.
    /// - Otherwise: coerce both to Int.
    fn coerce_comparison_pair(&mut self, a: TermId, b: TermId) -> (TermId, TermId) {
        let sort_a = self.terms.sort(a).clone();
        let sort_b = self.terms.sort(b).clone();
        if sort_a == sort_b {
            return (a, b);
        }
        if matches!(
            (&sort_a, &sort_b),
            (Sort::Int, Sort::Real) | (Sort::Real, Sort::Int)
        ) {
            return self.coerce_int_bv_pair(a, b);
        }
        // First try BV/Int coercion.
        match (&sort_a, &sort_b) {
            (Sort::BitVec(_), Sort::Int) | (Sort::Int, Sort::BitVec(_)) => {
                return self.coerce_int_bv_pair(a, b);
            }
            _ => {}
        }
        // Coerce non-Int/non-Real operands to Int, then retry matching.
        let a_int = self.coerce_to_int(a);
        let b_int = self.coerce_to_int(b);
        self.coerce_int_bv_pair(a_int, b_int)
    }

    /// Coerce a single term to Int sort if it is BitVec (#7126).
    ///
    /// BV-to-Int abstraction may produce BV-sorted subexpressions that end up
    /// as arguments to LIA arithmetic operators (Add, Sub, Mul, Div, Mod, Neg).
    /// The ay-core `mk_add`/`mk_mul`/etc. require Int or Real arguments and
    /// fire debug_asserts otherwise. This inserts `bv2nat` as needed.
    fn coerce_to_int(&mut self, t: TermId) -> TermId {
        match self.terms.sort(t).clone() {
            Sort::Int | Sort::Real => t,
            Sort::BitVec(_) => self.terms.mk_bv2nat(t),
            Sort::Bool => {
                // Bool in arithmetic context: encode as ITE(b, 1, 0).
                let one = self.terms.mk_int(BigInt::from(1));
                let zero = self.terms.mk_int(BigInt::from(0));
                self.terms.mk_ite(t, one, zero)
            }
            _ => {
                // Unsupported sort in arithmetic context → weaken.
                self.conversion_budget_exceeded = true;
                self.terms.mk_int(BigInt::from(0))
            }
        }
    }

    /// Coerce arithmetic operands to a single numeric sort.
    ///
    /// Existing BV/Bool abstraction repair first maps non-arithmetic operands to
    /// Int. If any operand is Real after that repair, Int operands are promoted
    /// with SMT-LIB `to_real` so ay-core arithmetic constructors stay well
    /// sorted for legal mixed Int/Real CHC inputs.
    fn coerce_numeric_args(&mut self, args: Vec<TermId>) -> Vec<TermId> {
        let coerced: Vec<TermId> = args.into_iter().map(|t| self.coerce_to_int(t)).collect();
        if coerced.iter().any(|t| self.terms.sort(*t) == &Sort::Real) {
            coerced
                .into_iter()
                .map(|t| {
                    if self.terms.sort(t) == &Sort::Int {
                        self.terms.mk_to_real(t)
                    } else {
                        t
                    }
                })
                .collect()
        } else {
            coerced
        }
    }

    fn numeric_literal_is_nonzero(expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Int(value) => *value != 0,
            ChcExpr::Real(numer, _) => *numer != 0,
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                Self::numeric_literal_is_nonzero(args[0].as_ref())
            }
            _ => false,
        }
    }

    /// Coerce a pair of terms to matching sorts (#6084).
    ///
    /// When scalarization or CHC preprocessing introduces sort mismatches
    /// (e.g., `(= bv_var int_literal)` or `(= Array(BV,Bool) Array(Int,Bool))`),
    /// the ay-core layer requires both sides to have identical sorts. This inserts
    /// `int2bv` or `bv2nat` conversions as needed. For array sort mismatches, we
    /// accept `a` as the canonical sort (keeping `a` unchanged).
    fn coerce_int_bv_pair(&mut self, a: TermId, b: TermId) -> (TermId, TermId) {
        let sort_a = self.terms.sort(a).clone();
        let sort_b = self.terms.sort(b).clone();
        if sort_a == sort_b {
            return (a, b);
        }
        match (&sort_a, &sort_b) {
            (Sort::Int, Sort::Real) => (self.terms.mk_to_real(a), b),
            (Sort::Real, Sort::Int) => (a, self.terms.mk_to_real(b)),
            (Sort::BitVec(bv), Sort::Int) => {
                let b_coerced = self.terms.mk_int2bv(bv.width, b);
                (a, b_coerced)
            }
            (Sort::Int, Sort::BitVec(bv)) => {
                let a_coerced = self.terms.mk_int2bv(bv.width, a);
                (a_coerced, b)
            }
            // Array sort mismatches: key sort differs (e.g., Array(BV32,Bool) vs
            // Array(Int,Bool)) from ConstArray conversion defaulting to Int key.
            // Recreate the const array with the correct key sort (#6084).
            (Sort::Array(arr_a), Sort::Array(arr_b))
                if arr_a.element_sort == arr_b.element_sort
                    && arr_a.index_sort != arr_b.index_sort =>
            {
                // Prefer `a`'s sort — recreate `b` as const array with `a`'s key sort.
                if let Some(default_val) = self.terms.get_const_array(b) {
                    let b_fixed = self
                        .terms
                        .mk_const_array(arr_a.index_sort.clone(), default_val);
                    (a, b_fixed)
                } else if let Some(default_val) = self.terms.get_const_array(a) {
                    let a_fixed = self
                        .terms
                        .mk_const_array(arr_b.index_sort.clone(), default_val);
                    (a_fixed, b)
                } else {
                    (a, b)
                }
            }
            _ => (a, b),
        }
    }

    fn convert_expr_inner(&mut self, expr: &ChcExpr) -> TermId {
        // Budget check: prevent unbounded expression tree growth (#2771).
        self.conversion_node_count += 1;
        if self.conversion_node_count > MAX_CONVERSION_NODES {
            self.conversion_budget_exceeded = true;
            return self.terms.mk_bool(true);
        }
        // Per-engine term memory budget check (#8600): every 1024 nodes,
        // verify we haven't exceeded the per-engine memory budget. Checking
        // every node would add overhead; 1024-node intervals amortize the
        // cost while catching runaway growth before it causes OOM. The
        // `term_memory_exceeded()` call itself is cheap (uses a cached
        // `true_memory_bytes()` with 64 KiB refresh delta).
        if self.conversion_node_count & 0x3FF == 0 && self.term_memory_exceeded() {
            self.conversion_budget_exceeded = true;
            return self.terms.mk_bool(true);
        }

        match expr {
            ChcExpr::Bool(b) => self.terms.mk_bool(*b),

            ChcExpr::Int(n) => self.terms.mk_int(BigInt::from(*n)),

            ChcExpr::BitVec(val, width) => self.terms.mk_bitvec(BigInt::from(*val), *width),

            ChcExpr::Real(num, denom) => {
                use num_rational::BigRational;
                let r = BigRational::new(BigInt::from(*num), BigInt::from(*denom));
                self.terms.mk_rational(r)
            }

            ChcExpr::Var(v) => self.get_or_create_var(v),

            ChcExpr::PredicateApp(name, id, args) => {
                // Serialize arguments for uniqueness key
                let arg_strs: Vec<String> = args.iter().map(|a| format!("{a}")).collect();
                let key = (*id, arg_strs);

                if let Some(&term) = self.pred_app_map.get(&key) {
                    return term;
                }

                // Create a fresh boolean variable for this predicate application
                let var_name = format!("{}_{}", name, self.pred_app_counter);
                self.pred_app_counter += 1;
                let term = self.terms.mk_var(&var_name, Sort::Bool);
                self.pred_app_map.insert(key, term);
                term
            }

            ChcExpr::FuncApp(name, sort, args) => {
                if name == "to_real" && args.len() == 1 {
                    let arg = self.convert_expr(&args[0]);
                    if self.conversion_budget_exceeded {
                        return self.terms.mk_bool(true);
                    }
                    if self.terms.sort(arg) == &Sort::Int {
                        return self.terms.mk_to_real(arg);
                    }
                    if self.terms.sort(arg) == &Sort::Real {
                        return arg;
                    }
                    self.conversion_budget_exceeded = true;
                    return self
                        .terms
                        .mk_rational(BigRational::from_integer(BigInt::from(0)));
                }
                if name == "to_int" && args.len() == 1 {
                    let arg = self.convert_expr(&args[0]);
                    if self.conversion_budget_exceeded {
                        return self.terms.mk_bool(true);
                    }
                    if self.terms.sort(arg) == &Sort::Real {
                        return self.terms.mk_to_int(arg);
                    }
                    if self.terms.sort(arg) == &Sort::Int {
                        return arg;
                    }
                    self.conversion_budget_exceeded = true;
                    return self.terms.mk_int(BigInt::from(0));
                }
                if name == "is_int" && args.len() == 1 {
                    let arg = self.convert_expr(&args[0]);
                    if self.conversion_budget_exceeded {
                        return self.terms.mk_bool(true);
                    }
                    if self.terms.sort(arg) == &Sort::Real {
                        return self.terms.mk_is_int(arg);
                    }
                    if self.terms.sort(arg) == &Sort::Int {
                        return self.terms.mk_bool(true);
                    }
                    self.conversion_budget_exceeded = true;
                    return self.terms.mk_bool(true);
                }

                let term_args: Vec<TermId> = args.iter().map(|a| self.convert_expr(a)).collect();
                // Budget may have been exceeded during child conversion (#2771).
                if self.conversion_budget_exceeded {
                    return self.terms.mk_bool(true);
                }
                let term_sort = Self::convert_sort(sort);
                self.terms
                    .mk_app(Symbol::named(name.clone()), term_args, term_sort)
            }

            ChcExpr::Op(op, args) => {
                let term_args: Vec<TermId> = args.iter().map(|a| self.convert_expr(a)).collect();
                // Budget may have been exceeded during child conversion (#2771).
                // Return sentinel before passing mixed-sort children to term constructors
                // that would panic (e.g., mk_gt(int, bool)).
                if self.conversion_budget_exceeded {
                    return self.terms.mk_bool(true);
                }

                match op {
                    ChcOp::Not => {
                        assert_eq!(term_args.len(), 1);
                        // Guard: mk_not requires Bool-sorted argument. Array/BV
                        // expressions can reach here during CHC cube negation
                        // for problems with array predicate parameters. (#6047)
                        let arg = term_args[0];
                        if self.terms.sort(arg) == &Sort::Bool {
                            self.terms.mk_not(arg)
                        } else {
                            // Non-Bool under Not: treat as unsupported, return
                            // true (which makes the containing formula weaker,
                            // preserving soundness).
                            self.terms.mk_bool(true)
                        }
                    }
                    ChcOp::And => {
                        // #6047: Guard against non-Bool args in And (same pattern as Not).
                        // Array/BV-sorted variables can reach here through CHC cube
                        // negation or ill-typed formulas from PDR interpolation.
                        if term_args.iter().any(|t| self.terms.sort(*t) != &Sort::Bool) {
                            return self.ill_typed_bv_sentinel();
                        }
                        self.terms.mk_and(term_args)
                    }
                    ChcOp::Or => {
                        // #6047: Guard against non-Bool args in Or.
                        if term_args.iter().any(|t| self.terms.sort(*t) != &Sort::Bool) {
                            return self.ill_typed_bv_sentinel();
                        }
                        self.terms.mk_or(term_args)
                    }
                    ChcOp::Implies => {
                        assert_eq!(term_args.len(), 2);
                        // #6047: Guard against non-Bool args in Implies.
                        if term_args.iter().any(|t| self.terms.sort(*t) != &Sort::Bool) {
                            return self.ill_typed_bv_sentinel();
                        }
                        self.terms.mk_implies(term_args[0], term_args[1])
                    }
                    ChcOp::Iff => {
                        assert_eq!(term_args.len(), 2);
                        // #6047: Guard against non-Bool args in Iff.
                        if term_args.iter().any(|t| self.terms.sort(*t) != &Sort::Bool) {
                            return self.ill_typed_bv_sentinel();
                        }
                        // a <-> b is (a => b) /\ (b => a)
                        let ab = self.terms.mk_implies(term_args[0], term_args[1]);
                        let ba = self.terms.mk_implies(term_args[1], term_args[0]);
                        self.terms.mk_and(vec![ab, ba])
                    }
                    ChcOp::Add => {
                        // #7126/#Real: repair BV/Bool abstraction and promote
                        // mixed Int/Real arithmetic to Real.
                        let coerced = self.coerce_numeric_args(term_args);
                        self.terms.mk_add(coerced)
                    }
                    ChcOp::Sub => {
                        let coerced = self.coerce_numeric_args(term_args);
                        self.terms.mk_sub(coerced)
                    }
                    ChcOp::Mul => {
                        let coerced = self.coerce_numeric_args(term_args);
                        self.terms.mk_mul(coerced)
                    }
                    ChcOp::Div => {
                        assert_eq!(term_args.len(), 2);
                        let coerced = self.coerce_numeric_args(term_args);
                        if coerced.iter().any(|t| self.terms.sort(*t) == &Sort::Real) {
                            if Self::numeric_literal_is_nonzero(args[1].as_ref()) {
                                self.terms.mk_div(coerced[0], coerced[1])
                            } else {
                                // SMT-LIB leaves division by zero underspecified. ay-core
                                // may simplify identities such as 0/x or x/x, which is
                                // unsound when x can be zero, so symbolic Real division
                                // fails closed to Unknown.
                                self.conversion_budget_exceeded = true;
                                self.terms
                                    .mk_rational(BigRational::from_integer(BigInt::from(0)))
                            }
                        } else {
                            self.terms.mk_intdiv(coerced[0], coerced[1])
                        }
                    }
                    ChcOp::Mod => {
                        assert_eq!(term_args.len(), 2);
                        let a = self.coerce_to_int(term_args[0]);
                        let b = self.coerce_to_int(term_args[1]);
                        if self.terms.sort(a) != &Sort::Int || self.terms.sort(b) != &Sort::Int {
                            self.conversion_budget_exceeded = true;
                            self.terms.mk_int(BigInt::from(0))
                        } else {
                            self.terms.mk_mod(a, b)
                        }
                    }
                    ChcOp::Neg => {
                        assert_eq!(term_args.len(), 1);
                        let a = self.coerce_to_int(term_args[0]);
                        self.terms.mk_neg(a)
                    }
                    ChcOp::Eq => {
                        assert_eq!(term_args.len(), 2);
                        let (a, b) = self.coerce_int_bv_pair(term_args[0], term_args[1]);
                        // #6047: After coercion, sorts may still differ (e.g., Array vs BV
                        // from ill-typed formulas in PDR interpolation). Propagate Unknown
                        // via budget mechanism to avoid unsound false injection (#5508 pattern).
                        if self.terms.sort(a) != self.terms.sort(b) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_eq(a, b)
                        }
                    }
                    ChcOp::Ne => {
                        assert_eq!(term_args.len(), 2);
                        // Encode `a != b` as `not (a = b)` rather than `distinct(a, b)`.
                        //
                        // `distinct` is a theory atom and requires explicit disequality support in
                        // theory solvers. Encoding as `not (= ...)` allows DPLL(T) to treat it as a
                        // Boolean negation of an equality atom, which is more robust for AY's CHC
                        // auxiliary queries (e.g., invariant preservation checks).
                        let (a, b) = self.coerce_int_bv_pair(term_args[0], term_args[1]);
                        // #6047: Sort mismatch after coercion → trivially not-equal (true).
                        if self.terms.sort(a) != self.terms.sort(b) {
                            self.terms.mk_bool(true)
                        } else {
                            let eq = self.terms.mk_eq(a, b);
                            self.terms.mk_not(eq)
                        }
                    }
                    ChcOp::Lt => {
                        assert_eq!(term_args.len(), 2);
                        // #7126: Coerce operands to matching sorts before comparison.
                        let (a, b) = self.coerce_comparison_pair(term_args[0], term_args[1]);
                        match self.terms.sort(a).clone() {
                            Sort::Int | Sort::Real => self.terms.mk_lt(a, b),
                            Sort::BitVec(_) => self.terms.mk_bvult(a, b),
                            Sort::Bool if *self.terms.sort(b) == Sort::Bool => {
                                // SOUNDNESS FIX #5508: Bool ordering semantics.
                                // For Bool (false=0, true=1): a < b ≡ ¬a ∧ b
                                let not_a = self.terms.mk_not(a);
                                self.terms.mk_and(vec![not_a, b])
                            }
                            _ => self.terms.mk_bool(true),
                        }
                    }
                    ChcOp::Le => {
                        assert_eq!(term_args.len(), 2);
                        let (a, b) = self.coerce_comparison_pair(term_args[0], term_args[1]);
                        match self.terms.sort(a).clone() {
                            Sort::Int | Sort::Real => self.terms.mk_le(a, b),
                            Sort::BitVec(_) => self.terms.mk_bvule(a, b),
                            Sort::Bool if *self.terms.sort(b) == Sort::Bool => {
                                // SOUNDNESS FIX #5508: Bool Le semantics.
                                // a <= b ≡ a ⟹ b ≡ ¬a ∨ b
                                let not_a = self.terms.mk_not(a);
                                self.terms.mk_or(vec![not_a, b])
                            }
                            _ => self.terms.mk_bool(true),
                        }
                    }
                    ChcOp::Gt => {
                        assert_eq!(term_args.len(), 2);
                        let (a, b) = self.coerce_comparison_pair(term_args[0], term_args[1]);
                        match self.terms.sort(a).clone() {
                            Sort::Int | Sort::Real => self.terms.mk_gt(a, b),
                            Sort::BitVec(_) => self.terms.mk_bvugt(a, b),
                            Sort::Bool if *self.terms.sort(b) == Sort::Bool => {
                                // SOUNDNESS FIX #5508: Bool Gt semantics.
                                // a > b ≡ a ∧ ¬b
                                let not_b = self.terms.mk_not(b);
                                self.terms.mk_and(vec![a, not_b])
                            }
                            _ => self.terms.mk_bool(true),
                        }
                    }
                    ChcOp::Ge => {
                        assert_eq!(term_args.len(), 2);
                        let (a, b) = self.coerce_comparison_pair(term_args[0], term_args[1]);
                        match self.terms.sort(a).clone() {
                            Sort::Int | Sort::Real => self.terms.mk_ge(a, b),
                            Sort::BitVec(_) => self.terms.mk_bvuge(a, b),
                            Sort::Bool if *self.terms.sort(b) == Sort::Bool => {
                                // SOUNDNESS FIX #5508: Bool Ge semantics.
                                // a >= b ≡ b ⟹ a ≡ ¬b ∨ a
                                let not_b = self.terms.mk_not(b);
                                self.terms.mk_or(vec![not_b, a])
                            }
                            _ => self.terms.mk_bool(true),
                        }
                    }
                    ChcOp::Ite => {
                        assert_eq!(term_args.len(), 3);
                        // Coerce ITE branches to same sort (#6084).
                        let (then_br, else_br) =
                            self.coerce_int_bv_pair(term_args[1], term_args[2]);
                        self.terms.mk_ite(term_args[0], then_br, else_br)
                    }
                    ChcOp::Select => {
                        assert_eq!(term_args.len(), 2);
                        let array = term_args[0];
                        let mut index = term_args[1];
                        // Coerce index sort to match array's key sort (#6084).
                        // CHC expressions may mix Int/BitVec sorts across
                        // preprocessing; the ay-core layer requires exact match.
                        let Sort::Array(arr) = self.terms.sort(array).clone() else {
                            self.conversion_budget_exceeded = true;
                            return self.terms.mk_bool(true);
                        };
                        let idx_sort = self.terms.sort(index).clone();
                        match (&arr.index_sort, &idx_sort) {
                            (Sort::BitVec(bv), Sort::Int) => {
                                index = self.terms.mk_int2bv(bv.width, index);
                            }
                            (Sort::Int, Sort::BitVec(_)) => {
                                index = self.terms.mk_bv2nat(index);
                            }
                            _ => {}
                        }
                        if self.terms.sort(index) != &arr.index_sort {
                            self.conversion_budget_exceeded = true;
                            return self.terms.mk_bool(true);
                        }
                        self.terms.mk_select(array, index)
                    }
                    ChcOp::Store => {
                        assert_eq!(term_args.len(), 3);
                        let array = term_args[0];
                        let mut index = term_args[1];
                        let mut value = term_args[2];
                        // Coerce index and value sorts to match array sort (#6084).
                        let Sort::Array(arr) = self.terms.sort(array).clone() else {
                            self.conversion_budget_exceeded = true;
                            return self.terms.mk_bool(true);
                        };
                        let idx_sort = self.terms.sort(index).clone();
                        match (&arr.index_sort, &idx_sort) {
                            (Sort::BitVec(bv), Sort::Int) => {
                                index = self.terms.mk_int2bv(bv.width, index);
                            }
                            (Sort::Int, Sort::BitVec(_)) => {
                                index = self.terms.mk_bv2nat(index);
                            }
                            _ => {}
                        }
                        let val_sort = self.terms.sort(value).clone();
                        match (&arr.element_sort, &val_sort) {
                            (Sort::BitVec(bv), Sort::Int) => {
                                value = self.terms.mk_int2bv(bv.width, value);
                            }
                            (Sort::Int, Sort::BitVec(_)) => {
                                value = self.terms.mk_bv2nat(value);
                            }
                            _ => {}
                        }
                        if self.terms.sort(index) != &arr.index_sort
                            || self.terms.sort(value) != &arr.element_sort
                        {
                            self.conversion_budget_exceeded = true;
                            return self.terms.mk_bool(true);
                        }
                        self.terms.mk_store(array, index, value)
                    }
                    // Bitvector operations
                    //
                    // #6047: All BV operations have defensive sort guards. When
                    // Array-sorted canonical variables end up in BV expressions (due
                    // to name-based variable translation in PDR interpolation), the
                    // ay-core BV constructors would panic. Propagate Unknown via
                    // budget mechanism rather than injecting false (unsound in
                    // predecessor/inductiveness queries — #5508 pattern).
                    ChcOp::BvAdd
                    | ChcOp::BvSub
                    | ChcOp::BvMul
                    | ChcOp::BvUDiv
                    | ChcOp::BvURem
                    | ChcOp::BvSDiv
                    | ChcOp::BvSRem
                    | ChcOp::BvSMod
                    | ChcOp::BvAnd
                    | ChcOp::BvOr
                    | ChcOp::BvXor
                    | ChcOp::BvNand
                    | ChcOp::BvNor
                    | ChcOp::BvXnor
                    | ChcOp::BvShl
                    | ChcOp::BvLShr
                    | ChcOp::BvAShr
                        if !self.well_sorted_binary_bv_args(&term_args) =>
                    {
                        self.ill_typed_bv_sentinel()
                    }
                    ChcOp::BvConcat if !self.all_bv_sorted(&term_args) => {
                        self.ill_typed_bv_sentinel()
                    }
                    ChcOp::BvAdd => self.terms.mk_bvadd(term_args),
                    ChcOp::BvSub => self.terms.mk_bvsub(term_args),
                    ChcOp::BvMul => self.terms.mk_bvmul(term_args),
                    ChcOp::BvUDiv => self.terms.mk_bvudiv(term_args),
                    ChcOp::BvURem => self.terms.mk_bvurem(term_args),
                    ChcOp::BvSDiv => self.terms.mk_bvsdiv(term_args),
                    ChcOp::BvSRem => self.terms.mk_bvsrem(term_args),
                    ChcOp::BvSMod => self.terms.mk_bvsmod(term_args),
                    ChcOp::BvAnd => self.terms.mk_bvand(term_args),
                    ChcOp::BvOr => self.terms.mk_bvor(term_args),
                    ChcOp::BvXor => self.terms.mk_bvxor(term_args),
                    ChcOp::BvNand => self.terms.mk_bvnand(term_args),
                    ChcOp::BvNor => self.terms.mk_bvnor(term_args),
                    ChcOp::BvXnor => self.terms.mk_bvxnor(term_args),
                    ChcOp::BvShl => self.terms.mk_bvshl(term_args),
                    ChcOp::BvLShr => self.terms.mk_bvlshr(term_args),
                    ChcOp::BvAShr => self.terms.mk_bvashr(term_args),
                    ChcOp::BvConcat => self.terms.mk_bvconcat(term_args),
                    ChcOp::BvNot => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvnot(term_args[0])
                        }
                    }
                    ChcOp::BvNeg => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvneg(term_args[0])
                        }
                    }
                    ChcOp::BvULt => {
                        if !self.well_sorted_binary_bv_args(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvult(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvULe => {
                        if !self.well_sorted_binary_bv_args(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvule(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvUGt => {
                        if !self.well_sorted_binary_bv_args(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvugt(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvUGe => {
                        if !self.well_sorted_binary_bv_args(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvuge(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvSLt => {
                        if !self.well_sorted_binary_bv_args(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvslt(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvSLe => {
                        if !self.well_sorted_binary_bv_args(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvsle(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvSGt => {
                        if !self.well_sorted_binary_bv_args(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvsgt(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvSGe => {
                        if !self.well_sorted_binary_bv_args(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvsge(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::BvComp => {
                        if !self.well_sorted_binary_bv_args(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvcomp(term_args[0], term_args[1])
                        }
                    }
                    ChcOp::Bv2Nat => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bv2nat(term_args[0])
                        }
                    }
                    ChcOp::BvExtract(hi, lo) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvextract(*hi, *lo, term_args[0])
                        }
                    }
                    ChcOp::BvZeroExtend(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvzero_extend(*n, term_args[0])
                        }
                    }
                    ChcOp::BvSignExtend(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvsign_extend(*n, term_args[0])
                        }
                    }
                    ChcOp::BvRotateLeft(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvrotate_left(*n, term_args[0])
                        }
                    }
                    ChcOp::BvRotateRight(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvrotate_right(*n, term_args[0])
                        }
                    }
                    ChcOp::BvRepeat(n) => {
                        assert_eq!(term_args.len(), 1);
                        if !self.all_bv_sorted(&term_args) {
                            self.ill_typed_bv_sentinel()
                        } else {
                            self.terms.mk_bvrepeat(*n, term_args[0])
                        }
                    }
                    ChcOp::Int2Bv(w) => {
                        assert_eq!(term_args.len(), 1);
                        // Int2Bv legitimately takes Int arg, no BV sort check
                        self.terms.mk_int2bv(*w, term_args[0])
                    }
                }
            }

            ChcExpr::ConstArrayMarker(_) => {
                // Marker shouldn't appear in real expressions - return a placeholder
                self.terms.mk_bool(true)
            }

            ChcExpr::IsTesterMarker(_) => {
                // Marker shouldn't appear in real expressions - return a placeholder
                self.terms.mk_bool(true)
            }

            ChcExpr::ConstArray(key_sort, val) => {
                // Create a constant array with the parsed key sort (#6084).
                let val_term = self.convert_expr(val);
                let core_key_sort = chc_sort_to_core(key_sort);
                self.terms.mk_const_array(core_key_sort, val_term)
            }
        }
    }
}
