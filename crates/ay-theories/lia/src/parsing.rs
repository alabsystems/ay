// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Linear and Diophantine parsing helpers for LIA.

use super::*;
use crate::linear_collect;

impl LiaSolver<'_> {
    /// Exact linear form of `lhs - rhs` as `(var → coeff, constant)`.
    ///
    /// Served from the atom-indexed parse cache (#C2): the term DAG is
    /// walked once per `(lhs, rhs)` pair per solver lifetime; subsequent
    /// calls reconstruct the map from the cached sorted coefficient list.
    pub(super) fn parse_linear_expr_with_vars(
        &self,
        lhs: TermId,
        rhs: TermId,
    ) -> (HashMap<TermId, BigInt>, BigInt) {
        let cached = self.cached_linear(lhs, rhs);
        let mut var_coeffs: HashMap<TermId, BigInt> = HashMap::default();
        for (term, coeff) in &cached.coeffs {
            var_coeffs.insert(*term, coeff.clone());
        }
        (var_coeffs, cached.constant.clone())
    }

    /// Uncached term-DAG walk behind [`Self::parse_linear_expr_with_vars`];
    /// called once per `(lhs, rhs)` by the #C2 cache builder.
    ///
    /// The row is EXACT: it has the same solution set as `lhs = rhs`. A
    /// non-integral constant (`(+ (to_real c) 1/2)`) is collected as a
    /// rational and the whole row is then multiplied by the least common
    /// denominator, so `to_real c = to_real d + 1/2` becomes
    /// `2·c' - 2·d' = 1`. The walk used to admit only integral constants and
    /// SILENTLY DROPPED any other one, which turned that equality into
    /// `c' - d' = 0`; on the unpreprocessed atom
    /// `(= (to_real c) (+ (to_real c) 1/2))` the row became `0 = 0`, so its
    /// (valid) negation was refuted as the self-contradictory disequality
    /// `t != t` — a 1-literal conflict that turned a satisfiable query UNSAT.
    /// Scaling by a positive constant changes no solution, over the integers
    /// or the reals, so every consumer of the row stays exactly as justified
    /// as it was for integral rows.
    pub(super) fn parse_linear_expr_with_vars_uncached(
        &self,
        lhs: TermId,
        rhs: TermId,
    ) -> (HashMap<TermId, BigInt>, BigInt) {
        let mut var_coeffs: HashMap<TermId, BigRational> = HashMap::default();
        let mut constant = BigRational::zero();

        let resolve_var = |t: TermId| Some(t);
        let convert_const = |c: &Constant| -> Option<BigRational> {
            match c {
                Constant::Int(n) => Some(BigRational::from_integer(n.clone())),
                Constant::Rational(r) => Some(r.0.clone()),
                // Not a numeric constant: the atom is ill-sorted for
                // arithmetic and no linear row can denote it. The callers
                // sort-guard their atoms, so this arm is unreachable for
                // them; keep it total without inventing a value.
                _ => None,
            }
        };
        let terms = self.terms();
        // Multiplication keeps its historical shape: only an INTEGER factor
        // scales a coefficient, so `(* 1/2 x)` stays one opaque column (a
        // consistent abstraction, never a dropped constant).
        let extract_mul_const = |t: TermId| {
            terms
                .extract_integer_constant(t)
                .map(BigRational::from_integer)
        };

        // Parse lhs with positive sign
        linear_collect::collect_linear_terms(
            self.terms(),
            lhs,
            &BigRational::one(),
            &mut var_coeffs,
            &mut constant,
            &resolve_var,
            &convert_const,
            &extract_mul_const,
            false,
            true,
        );

        // Parse rhs with negative sign
        linear_collect::collect_linear_terms(
            self.terms(),
            rhs,
            &-BigRational::one(),
            &mut var_coeffs,
            &mut constant,
            &resolve_var,
            &convert_const,
            &extract_mul_const,
            false,
            true,
        );

        // Negate constant (we're solving for Σ(coeff * var) = constant)
        constant = -constant;

        // Clear denominators: multiply the row by the lcm of every
        // denominator (a positive integer), which preserves its solutions.
        let scale = var_coeffs
            .values()
            .chain(std::iter::once(&constant))
            .fold(BigInt::one(), |acc, value| acc.lcm(value.denom()));
        let scale_value = |value: &BigRational| -> BigInt {
            let scaled = value * BigRational::from_integer(scale.clone());
            debug_assert!(scaled.is_integer(), "BUG: row scaling left a fraction");
            scaled.to_integer()
        };
        let coeffs = var_coeffs
            .iter()
            .map(|(&term, coeff)| (term, scale_value(coeff)))
            .collect();
        (coeffs, scale_value(&constant))
    }

    /// Whether `term`, a column of a parsed row, takes only integer values:
    /// an Int-sorted term, or `to_real` of one (the `to_real` coercion of an
    /// unpreprocessed mixed atom). Integer-only reasoning (GCD divisibility,
    /// residues) over a row is valid only when every column is one of these;
    /// a Real-sorted column (a Real variable, an opaque `(/ x 2)`) may take a
    /// fractional value, and `2·r = 1` is then satisfiable.
    pub(super) fn is_integer_valued_column(&self, term: TermId) -> bool {
        match self.terms().sort(term) {
            Sort::Int => true,
            Sort::Real => matches!(
                self.terms().get(term),
                TermData::App(Symbol::Named(name), args)
                    if name == "to_real"
                        && args.len() == 1
                        && matches!(self.terms().sort(args[0]), Sort::Int)
            ),
            _ => false,
        }
    }

    // parse_linear_expr_for_gcd was removed in #C2: `gcd_test` now reads the
    // per-equality `gcd_divides` flag precomputed in the linear cache.

    pub(super) fn ceil_bigint(val: &BigRational) -> BigInt {
        Self::ceil_rational(val)
    }

    /// Floor of a BigRational as BigInt (delegates to `floor_rational`).
    pub(super) fn floor_bigint(val: &BigRational) -> BigInt {
        Self::floor_rational(val)
    }

    /// Parse equality for Diophantine solver: lhs = rhs -> (coeffs, constant)
    ///
    /// Returns `None` if the equation contains terms not in `term_to_idx` that
    /// cannot be decomposed into known arithmetic operators or constants. This
    /// prevents the Diophantine solver from working with an incomplete equation
    /// that silently dropped terms, which can cause false UNSAT (#4786).
    pub(super) fn parse_equality_for_dioph(
        &self,
        lhs: TermId,
        rhs: TermId,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<(Vec<(usize, BigInt)>, BigInt)> {
        // #C2: cache the parsed row keyed by `(lhs, rhs)`, guarded by the
        // var-index epoch. All callers build `term_to_idx` via
        // `build_var_index()` (the deterministic full-integer_vars bijection),
        // so an unchanged epoch implies an identical index mapping.
        let key = (lhs, rhs);
        if let Some((epoch, cached)) = self.dioph_parse_cache.borrow().get(&key) {
            if *epoch == self.var_index_epoch {
                return cached.as_ref().map(|row| (**row).clone());
            }
        }
        let parsed = self.parse_equality_for_dioph_uncached(lhs, rhs, term_to_idx);
        self.dioph_parse_cache.borrow_mut().insert(
            key,
            (
                self.var_index_epoch,
                parsed.clone().map(std::sync::Arc::new),
            ),
        );
        parsed
    }

    /// Uncached term-DAG walk behind [`Self::parse_equality_for_dioph`].
    fn parse_equality_for_dioph_uncached(
        &self,
        lhs: TermId,
        rhs: TermId,
        term_to_idx: &HashMap<TermId, usize>,
    ) -> Option<(Vec<(usize, BigInt)>, BigInt)> {
        let mut coeffs: HashMap<usize, BigInt> = HashMap::default();
        let mut constant = BigInt::zero();
        let mut complete = true;

        // Parse lhs with positive sign
        self.collect_dioph_terms(
            lhs,
            &BigInt::one(),
            &mut coeffs,
            &mut constant,
            term_to_idx,
            &mut complete,
        );

        // Parse rhs with negative sign (move to LHS)
        self.collect_dioph_terms(
            rhs,
            &-BigInt::one(),
            &mut coeffs,
            &mut constant,
            term_to_idx,
            &mut complete,
        );

        if !complete {
            return None;
        }

        // The equation is: Σ(coeff * var) - constant = 0
        // So: Σ(coeff * var) = constant
        constant = -constant;

        // Remove zero coefficients
        coeffs.retain(|_, v| !v.is_zero());

        // Sort by variable index for deterministic ordering across check_sat calls.
        // HashMap iteration order is non-deterministic, which caused #938 where
        // variables were interned in different orders on subsequent ALL-SAT calls.
        let mut coeffs_vec: Vec<_> = coeffs.into_iter().collect();
        coeffs_vec.sort_by_key(|(idx, _)| *idx);
        Some((coeffs_vec, constant))
    }

    /// Fold fixed variables (lower bound == upper bound) into the constant term.
    ///
    /// Given equation `Σ(coeff_i * var_i) = constant`, for each variable whose
    /// LRA bounds determine it to a single integer value `v`, replace the term
    /// `coeff_i * var_i` with `coeff_i * v` added to the constant. The variable
    /// is removed from the coefficient list.
    ///
    /// This is Z3's fixed-variable folding from `dioph_eq.cpp`: when a variable
    /// is determined (possibly from a prior tightening round), folding it
    /// simplifies the equation system and enables the Dioph solver to find
    /// substitutions it would otherwise miss.
    ///
    /// Returns `(folded_coefficients, folded_constant, bound_reasons)`. The
    /// `bound_reasons` contain the `TheoryLit`s that justified every tight bound
    /// used for folding. Callers MUST include these in any conflict derived from
    /// the folded equation — omitting them produces overly-strong blocking
    /// clauses that can eliminate valid SAT assignments (#8012).
    pub(super) fn fold_fixed_vars_in_equation(
        &self,
        var_coeffs: &[(usize, BigInt)],
        mut constant: BigInt,
        idx_to_term: &[TermId],
    ) -> (Vec<(usize, BigInt)>, BigInt, Vec<TheoryLit>) {
        let mut folded_coeffs = Vec::with_capacity(var_coeffs.len());
        let mut bound_reasons = Vec::new();

        for (idx, coeff) in var_coeffs {
            if let Some(&term_id) = idx_to_term.get(*idx) {
                // ATOM-JUSTIFIED bounds only (#nia-sign-cut-soundness): a
                // variable pinned by an NIA rounding pin (`x = round(model(x))`,
                // reason = the variable term) has `lb == ub` too, and folding
                // it turned a satisfiable Diophantine system infeasible
                // (attack corpus gen2/h0536, h0986). The pin is not a
                // consequence of the asserted atoms, so it is not a constant.
                // Sentinel-only HYPOTHESIS pins (factor-split branches, the
                // NIA's tentative-patch verification) are excluded too: the
                // folded system is cached across pops keyed on the equality
                // set alone, so a hypothesis folded here would outlive its
                // scope and could carry a later refutation.
                if let Some((Some(lb), Some(ub))) = self.justified_bounds(term_id) {
                    if lb.value == ub.value
                        && lb.value.denom().is_one()
                        && Self::bound_has_atom_reason(&lb)
                        && Self::bound_has_atom_reason(&ub)
                    {
                        // A derived bound can have transitive provenance not
                        // present in its direct reason pairs. Fold only when
                        // both sides have complete, nameable justifications;
                        // these become premises of every cached substitution.
                        if let (Some(lower_reasons), Some(upper_reasons)) = (
                            self.justified_lra_bound_reasons(&lb),
                            self.justified_lra_bound_reasons(&ub),
                        ) {
                            constant -= coeff * lb.value.numer();
                            bound_reasons.extend(lower_reasons);
                            bound_reasons.extend(upper_reasons);
                            continue;
                        }
                    }
                }
            }
            folded_coeffs.push((*idx, coeff.clone()));
        }

        // Deduplicate bound reasons (tight bounds from both lb/ub often overlap).
        bound_reasons.sort_unstable();
        bound_reasons.dedup();

        (folded_coeffs, constant, bound_reasons)
    }

    /// Recursively collect linear terms for Diophantine solver.
    ///
    /// Sets `*complete = false` if any term is encountered that cannot be
    /// decomposed and is not in `term_to_idx`. This signals to the caller
    /// that the parsed equation is missing terms and must not be used (#4786).
    fn collect_dioph_terms(
        &self,
        term: TermId,
        scale: &BigInt,
        coeffs: &mut HashMap<usize, BigInt>,
        constant: &mut BigInt,
        term_to_idx: &HashMap<TermId, usize>,
        complete: &mut bool,
    ) {
        // Treat any mapped term as a variable, regardless of TermData kind.
        //
        // This is required for AUFLIA, where Int-sorted UF apps (e.g., (f x)) are
        // represented as atomic variables in the linearization.
        if let Some(&idx) = term_to_idx.get(&term) {
            *coeffs.entry(idx).or_insert_with(BigInt::zero) += scale;
            return;
        }

        match self.terms().get(term) {
            TermData::Const(Constant::Int(n)) => {
                *constant += scale * n;
            }
            TermData::Const(Constant::Rational(r)) => {
                if r.0.denom().is_one() {
                    *constant += scale * r.0.numer();
                } else {
                    // Non-integer rational not in variable index — incomplete parse.
                    *complete = false;
                }
            }
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    "+" => {
                        for &arg in args {
                            self.collect_dioph_terms(
                                arg,
                                scale,
                                coeffs,
                                constant,
                                term_to_idx,
                                complete,
                            );
                        }
                    }
                    "-" if args.len() == 1 => {
                        self.collect_dioph_terms(
                            args[0],
                            &-scale.clone(),
                            coeffs,
                            constant,
                            term_to_idx,
                            complete,
                        );
                    }
                    "-" if args.len() >= 2 => {
                        self.collect_dioph_terms(
                            args[0],
                            scale,
                            coeffs,
                            constant,
                            term_to_idx,
                            complete,
                        );
                        for &arg in &args[1..] {
                            self.collect_dioph_terms(
                                arg,
                                &-scale.clone(),
                                coeffs,
                                constant,
                                term_to_idx,
                                complete,
                            );
                        }
                    }
                    "*" => {
                        let mut const_factor = BigInt::one();
                        let mut var_args = Vec::new();

                        for &arg in args {
                            if let Some(c) = self.terms().extract_integer_constant(arg) {
                                const_factor *= c;
                            } else {
                                var_args.push(arg);
                            }
                        }

                        let new_scale = scale * &const_factor;

                        if var_args.is_empty() {
                            *constant += &new_scale;
                        } else if var_args.len() == 1 {
                            self.collect_dioph_terms(
                                var_args[0],
                                &new_scale,
                                coeffs,
                                constant,
                                term_to_idx,
                                complete,
                            );
                        } else {
                            // Non-linear term not in variable index — incomplete parse.
                            *complete = false;
                        }
                    }
                    _ => {
                        // Unknown function not in variable index — incomplete parse.
                        *complete = false;
                    }
                }
            }
            _ => {
                // Unknown term (Var, ITE, etc.) not in variable index — incomplete
                // parse. Without this, the Dioph solver silently drops terms, causing
                // false UNSAT on equations with un-lifted ITEs or unindexed vars (#4786).
                *complete = false;
            }
        }
    }

    /// Add an integer bound as an equality constraint to LRA.
    /// This is used when Diophantine solving determines a variable's value.
    /// The reasons parameter contains (term_id, value) pairs for the constraints
    /// that determined this bound - used for conflict clause generation.
    pub(crate) fn add_integer_bound(
        &mut self,
        term_id: TermId,
        value: &BigInt,
        reasons: &[(TermId, bool)],
    ) {
        let debug = self.debug_dioph;

        // Ensure the variable is registered with LRA (may not be if it only
        // appeared in pure integer equalities handled by Diophantine solver)
        let lra_var = self.lra.ensure_var_registered(term_id);

        let rat_value = BigRational::from(value.clone());

        if debug {
            safe_eprintln!(
                "[DIOPH] Adding bound: var {} (lra {}) = {} with {} reasons",
                term_id.0,
                lra_var,
                rat_value,
                reasons.len()
            );
        }

        // Add as both lower and upper bound (equality) with the reasons
        self.lra
            .add_direct_bound_with_reasons(lra_var, rat_value.clone(), true, reasons); // lower
        self.lra
            .add_direct_bound_with_reasons(lra_var, rat_value, false, reasons); // upper

        // Track which term IDs got dioph-derived bounds for targeted augmentation.
        self.dioph_bound_term_ids.insert(term_id);
        // Dioph-derived tightening → rescan this var (#C4).
        self.mark_int_bound_dirty(term_id);
    }
}

// Additional methods for incremental solving (not part of TheorySolver trait)
impl LiaSolver<'_> {
    /// Clear assertions but preserve learned cuts.
    ///
    /// Use this between SAT model iterations in DPLL(T) to retain HNF cuts
    /// that are globally valid (derived from the original constraint matrix).
    pub(crate) fn clear_assertions(&mut self) {
        self.clear_assertions_impl(false);
    }

    /// Warm variant for the persistent-theory arm: identical LIA-side
    /// clearing, but the inner LRA relaxation keeps its simplex
    /// values/basis (`soft_reset_warm`) so re-asserted atoms warm-start
    /// instead of re-pivoting from scratch. The bound-revision bump
    /// inside LRA's warm reset covers the stale-memo hazard, and the
    /// Diophantine caches are revalidated exactly as in the cold path
    /// (`dioph_needs_revalidation` below).
    pub(crate) fn clear_assertions_warm(&mut self) {
        self.clear_assertions_impl(true);
    }

    fn clear_assertions_impl(&mut self, warm: bool) {
        if warm {
            self.lra.soft_reset_warm();
        } else {
            self.lra.reset();
        }
        self.integer_vars.clear();
        self.sorted_integer_vars.clear();
        // Fresh bound state → conservative full rescan (#C4).
        self.mark_int_bounds_all_dirty();
        // Variable index changed → dioph parse cache rows are stale (#C2).
        self.var_index_epoch += 1;
        self.int_constant_terms.clear();
        self.asserted.clear();
        self.const_bool_conflicts.clear();
        // Fully clear the incremental view (scope marks and the bounds undo
        // trail included) since `asserted` and `scopes` are both cleared (#C1).
        self.assertion_view_cache.clear();
        self.scopes.clear();
        self.tentative_scope_marks.clear();
        self.cut_scopes.clear();
        self.cut_state_scopes.clear();
        // #C7: all scopes are gone; preserved seen_hnf_cuts keys are now base
        // (permanent), so the per-scope undo trail must be empty too.
        self.seen_hnf_cuts_trail.clear();
        self.direct_enum_witness = None;
        self.gomory_iterations = 0;
        self.hnf_iterations = 0;
        // Clear Nelson-Oppen state - equalities may change
        self.pending_equalities.clear();
        self.propagated_equality_pairs.clear();
        self.propagated_disequality_pairs.clear();
        self.shared_equalities.clear();
        // INTERFACE-DIET: interface cleared ⇒ no longer under-represented.
        self.hidden_interface = false;
        // #shared-eq-idempotent: the membership index mirrors the trail.
        self.shared_eq_seen.clear();
        self.shared_eq_revision += 1;
        self.detect_algebraic_cache = None;
        self.shared_disequalities.clear();
        self.pending_shared_eq_conflict = None;
        // IMPORTANT: Preserve dioph_equality_key, dioph_safe_dependent_vars,
        // dioph_cached_substitutions, and dioph_cached_reasons. These are derived
        // from the equality structure
        // which typically doesn't change across soft resets (only inequality bounds
        // change during branch-and-bound). If the equality structure changes, the
        // equality_key comparison in check() will naturally invalidate the cache.
        //
        // Preserving these allows:
        // 1. Skipping redundant Diophantine solving
        // 2. Using cached branching hints (safe_dependent_vars)
        // 3. Propagating bounds through cached substitutions
        //
        // Also preserve seen_hnf_cuts and learned_cuts - they're globally valid
        //
        // Clear transient Dioph bound tracking - bounds are reset with LRA.
        self.dioph_modified_bounds = false;
        self.dioph_bound_term_ids.clear();
        // #C8: the equality-derived caches survive the reset (see above); force
        // the next check() to re-validate the equality key before reusing them.
        self.dioph_needs_revalidation = true;
    }

    /// Linear expression coefficients: Σ(coeff * var) + constant
    ///
    /// Cached per term (#C2): the affine form of a term is immutable
    /// (`TermStore` is append-only), and the shared-equality/Nelson-Oppen
    /// paths re-parse the same interface terms on every EUF propagation.
    pub(super) fn term_to_linear_coeffs(&self, term: TermId) -> LinearCoeffs {
        if let Some(hit) = self.affine_cache.borrow().get(&term) {
            let (cached_vars, cached_constant) = hit.as_ref();
            let mut vars: HashMap<TermId, BigRational> = HashMap::default();
            for (var, coeff) in cached_vars {
                vars.insert(*var, coeff.clone());
            }
            return LinearCoeffs {
                vars,
                constant: cached_constant.clone(),
            };
        }

        let mut vars: HashMap<TermId, BigRational> = HashMap::default();
        let mut constant = BigRational::zero();
        self.collect_linear_coeffs(term, &BigRational::one(), &mut vars, &mut constant);

        let mut sorted: Vec<(TermId, BigRational)> =
            vars.iter().map(|(t, c)| (*t, c.clone())).collect();
        sorted.sort_by_key(|(t, _)| t.0);
        self.affine_cache
            .borrow_mut()
            .insert(term, std::sync::Arc::new((sorted, constant.clone())));

        LinearCoeffs { vars, constant }
    }

    /// Recursively collect linear coefficients from a term.
    fn collect_linear_coeffs(
        &self,
        term: TermId,
        scale: &BigRational,
        vars: &mut HashMap<TermId, BigRational>,
        constant: &mut BigRational,
    ) {
        match self.terms().get(term) {
            TermData::Const(Constant::Int(n)) => {
                *constant += scale * BigRational::from(n.clone());
            }
            TermData::Const(Constant::Rational(r)) => {
                *constant += scale * &r.0;
            }
            TermData::Var(_, _) => {
                *vars.entry(term).or_insert_with(BigRational::zero) += scale;
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    for &arg in args {
                        self.collect_linear_coeffs(arg, scale, vars, constant);
                    }
                }
                "-" if args.len() == 1 => {
                    self.collect_linear_coeffs(args[0], &-scale.clone(), vars, constant);
                }
                "-" if args.len() >= 2 => {
                    self.collect_linear_coeffs(args[0], scale, vars, constant);
                    for &arg in &args[1..] {
                        self.collect_linear_coeffs(arg, &-scale.clone(), vars, constant);
                    }
                }
                "*" => {
                    // Try to extract constant factor
                    let mut const_factor = BigRational::one();
                    let mut var_args = Vec::new();

                    for &arg in args {
                        match self.terms().get(arg) {
                            TermData::Const(Constant::Int(n)) => {
                                const_factor *= BigRational::from(n.clone());
                            }
                            TermData::Const(Constant::Rational(r)) => {
                                const_factor *= &r.0;
                            }
                            _ => var_args.push(arg),
                        }
                    }

                    let new_scale = scale * &const_factor;

                    if var_args.is_empty() {
                        *constant += &new_scale;
                    } else if var_args.len() == 1 {
                        self.collect_linear_coeffs(var_args[0], &new_scale, vars, constant);
                    } else {
                        // Non-linear: treat entire term as opaque variable
                        *vars.entry(term).or_insert_with(BigRational::zero) += scale;
                    }
                }
                _ => {
                    // Unknown function - treat as opaque variable
                    *vars.entry(term).or_insert_with(BigRational::zero) += scale;
                }
            },
            _ => {
                // Unknown term - treat as variable
                *vars.entry(term).or_insert_with(BigRational::zero) += scale;
            }
        }
    }
}
