// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Move out model-equality/disequality proposal deduplication state.
    ///
    /// LIA recreates its embedded LRA relaxation across lazy DPLL(T)
    /// refinement rounds. Preserving these sets keeps Z3-style `assume_eqs`
    /// from re-proposing the same zero-reason model equalities every round
    /// before expression splits get a chance to make progress.
    pub fn take_model_equality_proposal_state(
        &mut self,
    ) -> (HashSet<(TermId, TermId)>, HashSet<(TermId, TermId)>) {
        (
            std::mem::take(&mut self.propagated_equality_pairs),
            std::mem::take(&mut self.propagated_disequality_pairs),
        )
    }

    /// Restore model-equality/disequality proposal deduplication state.
    pub fn import_model_equality_proposal_state(
        &mut self,
        equality_pairs: HashSet<(TermId, TermId)>,
        disequality_pairs: HashSet<(TermId, TermId)>,
    ) {
        self.propagated_equality_pairs = equality_pairs;
        self.propagated_disequality_pairs = disequality_pairs;
    }

    /// Offset equality discovery for nf==2 rows (Z3's `cheap_eq_on_nbase`).
    ///
    /// For each touched row with exactly 2 non-fixed columns (base `x` and non-base `y`
    /// with coefficient +1 or -1), compute the "offset" — the value `x` would have
    /// if `y` were zero (i.e., `row.constant - sum_of_fixed_contributions`).
    ///
    /// When two rows share the same `(y, y_sign)` and have the same offset, we can
    /// deduce `x1 = x2` since both equal `-y_sign * y + offset`.
    ///
    /// Reference: `reference/z3/src/math/lp/lp_bound_propagator.h:357-418`
    pub(crate) fn discover_offset_equalities(&mut self, rows_to_scan: &DenseIdxSet) {
        // Temporary table: (y_var, y_sign) → HashMap<offset → (row_idx, base_var)>
        // We use a HashMap keyed by (y_var, i8_sign) → Vec<(offset, row_idx, base_var)>
        // and do pairwise matching within each bucket.
        struct RowInfo {
            offset: Rational,
            base_var: u32,
            row_idx: usize,
        }

        // Map: (y_var, y_sign: i8) → list of (offset, base_var, row_idx)
        let mut buckets: HashMap<(u32, i8), Vec<RowInfo>> = HashMap::default();
        let num_vars = self.vars.len();

        for &row_idx in rows_to_scan {
            if row_idx >= self.rows.len() {
                continue;
            }
            let row = &self.rows[row_idx];
            let base_var = row.basic_var;
            let bv = base_var as usize;
            if bv >= num_vars {
                continue;
            }

            // Check if base var is fixed — if so, skip (nf would be 0 or handled by nf==1 path)
            if self.is_var_fixed_for_offset_eq(base_var) {
                continue;
            }

            // Skip rows with Big coefficients (same guard as compute_implied_bounds)
            if row
                .coeffs
                .iter()
                .any(|(_, c)| matches!(c, Rational::Big(_)))
            {
                continue;
            }

            // Count non-fixed non-basic columns, identify the single non-fixed one
            let mut nf = 1u32; // base var is non-fixed (checked above), counts as 1
            let mut y_var: Option<u32> = None;
            let mut y_sign: i8 = 0;
            let mut offset = row.constant.clone();
            let mut too_many = false;

            for &(var, ref coeff) in &row.coeffs {
                let vi = var as usize;
                if vi >= num_vars {
                    too_many = true;
                    break;
                }
                if self.is_var_fixed_for_offset_eq(var) {
                    // Fixed column: subtract its contribution from the offset.
                    // Row equation: base_var = Σ(coeff_j * x_j) + constant
                    // For a fixed variable with value `v`, contribution = coeff * v
                    if let Some(fixed_val) = self.get_fixed_value(var) {
                        offset = &offset - &(&fixed_val * coeff);
                    } else {
                        // Shouldn't happen if is_var_fixed returned true, but be safe
                        too_many = true;
                        break;
                    }
                } else {
                    nf += 1;
                    if nf > 2 {
                        too_many = true;
                        break;
                    }
                    y_var = Some(var);
                    // Check if coefficient is +1 or -1
                    if coeff.is_one() {
                        y_sign = 1;
                    } else if *coeff == Rational::Small(-1, 1) {
                        y_sign = -1;
                    } else {
                        // Coefficient not +/-1, can't do offset equality
                        too_many = true;
                        break;
                    }
                }
            }

            if too_many || nf != 2 || y_var.is_none() || y_sign == 0 {
                continue;
            }

            let y = y_var.unwrap();
            let bucket_key = (y, y_sign);
            buckets.entry(bucket_key).or_default().push(RowInfo {
                offset,
                base_var,
                row_idx,
            });
        }

        // Match within each bucket: rows with the same offset → equality
        for (_key, entries) in &buckets {
            if entries.len() < 2 {
                continue;
            }
            // Build an index from offset → first entry
            let mut offset_map: HashMap<Rational, usize> = HashMap::default(); // offset → index in entries
            for (idx, entry) in entries.iter().enumerate() {
                match offset_map.get(&entry.offset) {
                    None => {
                        offset_map.insert(entry.offset.clone(), idx);
                    }
                    Some(&prev_idx) => {
                        let prev = &entries[prev_idx];
                        // Check sort compatibility (both int or both real)
                        let sort_a = self.fixed_term_sort_key(entry.base_var);
                        let sort_b = self.fixed_term_sort_key(prev.base_var);
                        if sort_a != sort_b || sort_a.is_none() {
                            continue;
                        }
                        // Enqueue offset equality with row indices for reason construction.
                        // Unlike fixed-term equalities, the base vars are NOT fixed — the
                        // equality comes from row structure (shared non-fixed column y).
                        if entry.base_var != prev.base_var {
                            self.pending_offset_equalities.push((
                                entry.base_var,
                                prev.base_var,
                                entry.row_idx,
                                prev.row_idx,
                            ));
                        }
                    }
                }
            }
        }
    }

    /// Check if a variable is "fixed" for offset equality purposes.
    /// A variable is fixed if it has non-strict lower == upper bounds
    /// (from either direct bounds or implied bounds).
    #[inline]
    pub(crate) fn is_var_fixed_for_offset_eq(&self, var: u32) -> bool {
        let vi = var as usize;
        // Check implied bounds first (they may be tighter)
        if let Some((Some(lb), Some(ub))) = self.implied_bounds.get(vi) {
            if !lb.strict && !ub.strict && lb.value == ub.value {
                return true;
            }
        }
        // Check direct bounds
        if let Some(info) = self.vars.get(vi) {
            if let (Some(lower), Some(upper)) = (&info.lower, &info.upper) {
                if !lower.strict && !upper.strict && lower.value == upper.value {
                    return true;
                }
            }
        }
        false
    }

    /// Get the fixed value of a variable (for offset computation).
    /// Returns the non-strict bound value when lower == upper.
    #[inline]
    pub(crate) fn get_fixed_value(&self, var: u32) -> Option<Rational> {
        let vi = var as usize;
        // Check implied bounds first
        if let Some((Some(lb), Some(ub))) = self.implied_bounds.get(vi) {
            if !lb.strict && !ub.strict && lb.value == ub.value {
                return Some(lb.value.clone());
            }
        }
        // Check direct bounds
        if let Some(info) = self.vars.get(vi) {
            if let (Some(lower), Some(upper)) = (&info.lower, &info.upper) {
                if !lower.strict && !upper.strict && lower.value == upper.value {
                    return Some(lower.value.clone());
                }
            }
        }
        None
    }

    pub(crate) fn collect_fixed_term_var_reasons(&self, var_id: u32) -> Vec<TheoryLit> {
        let mut reasons = Vec::new();
        let mut seen_direct = HashSet::default();
        let vi = var_id as usize;

        if let Some(info) = self.vars.get(vi) {
            if let (Some(lower), Some(upper)) = (&info.lower, &info.upper) {
                if !lower.strict && !upper.strict && lower.value == upper.value {
                    for (term, value) in lower.reason_pairs().chain(upper.reason_pairs()) {
                        if term.is_sentinel() {
                            continue;
                        }
                        let lit = TheoryLit::new(term, value);
                        if seen_direct.insert(lit) {
                            reasons.push(lit);
                        }
                    }
                }
            }
        }

        if !reasons.is_empty() {
            return reasons;
        }

        if let Some((Some(lower), Some(upper))) = self.implied_bounds.get(vi) {
            if !lower.strict && !upper.strict && lower.value == upper.value {
                let mut seen_row = HashSet::default();
                // #qfuflia-a5-fixed-eqs: the collector's bool reports whether
                // the justification is COMPLETE. Ignoring it exported
                // equalities with single-atom reasons for two-var fixings,
                // and those under-justified reasons poison conflict analysis
                // into false refutations (measured: false UNSAT on
                // xs-06-07-4-5-4-2, :status sat). Complete-or-empty.
                let ok_lower =
                    self.collect_row_reasons_dedup(var_id, false, &mut reasons, &mut seen_row);
                let ok_upper =
                    self.collect_row_reasons_dedup(var_id, true, &mut reasons, &mut seen_row);
                if !(ok_lower && ok_upper) {
                    reasons.clear();
                }
            }
        }

        reasons
    }

    /// Drain the pending fixed-term equality pairs into model-equality
    /// requests for the combiner, dropping pairs whose terms are unmapped.
    pub fn take_pending_fixed_term_model_equalities(&mut self) -> Vec<ModelEqualityRequest> {
        let pending = std::mem::take(&mut self.pending_fixed_term_equalities);
        let mut requests = Vec::new();

        for (lhs_var, rhs_var) in pending {
            let (Some(&lhs_term), Some(&rhs_term)) = (
                self.var_to_term.get(&lhs_var),
                self.var_to_term.get(&rhs_var),
            ) else {
                continue;
            };
            if lhs_term == rhs_term || self.terms().sort(lhs_term) != self.terms().sort(rhs_term) {
                continue;
            }

            let pair = if lhs_term.0 < rhs_term.0 {
                (lhs_term, rhs_term)
            } else {
                (rhs_term, lhs_term)
            };
            if !self.propagated_equality_pairs.insert(pair) {
                continue;
            }

            let mut reasons = self.collect_fixed_term_var_reasons(lhs_var);
            let mut seen = reasons.iter().copied().collect::<HashSet<_>>();
            for lit in self.collect_fixed_term_var_reasons(rhs_var) {
                if seen.insert(lit) {
                    reasons.push(lit);
                }
            }

            if reasons.is_empty() {
                self.propagated_equality_pairs.remove(&pair);
                continue;
            }

            requests.push(ModelEqualityRequest {
                lhs: pair.0,
                rhs: pair.1,
                reason: reasons,
                implied: false,
            });
        }

        requests.sort_by_key(|req| (req.lhs.0, req.rhs.0));
        requests
    }

    /// Materialize pending offset equalities into `ModelEqualityRequest`s.
    ///
    /// Offset equalities are derived from nf==2 rows sharing a non-fixed column.
    /// The reason is the union of all fixed-column bounds in both derivation rows.
    pub(crate) fn take_pending_offset_equalities(&mut self) -> Vec<ModelEqualityRequest> {
        let pending = std::mem::take(&mut self.pending_offset_equalities);
        let mut requests = Vec::new();
        let num_vars = self.vars.len();

        for (var1, var2, row_idx1, row_idx2) in pending {
            let (Some(&term1), Some(&term2)) =
                (self.var_to_term.get(&var1), self.var_to_term.get(&var2))
            else {
                continue;
            };
            if term1 == term2 || self.terms().sort(term1) != self.terms().sort(term2) {
                continue;
            }

            let pair = if term1.0 < term2.0 {
                (term1, term2)
            } else {
                (term2, term1)
            };
            if !self.propagated_equality_pairs.insert(pair) {
                continue;
            }

            // Construct reason: all fixed-column bounds in both rows.
            // Use collect_fixed_term_var_reasons per fixed column — it handles
            // both direct bounds AND implied-bounds-only variables correctly
            // (falls back to collect_row_reasons_dedup for implied bounds).
            let mut reasons = Vec::new();
            let mut seen = HashSet::default();
            for &ri in &[row_idx1, row_idx2] {
                if ri >= self.rows.len() {
                    continue;
                }
                let row = &self.rows[ri];
                for &(var, _) in &row.coeffs {
                    let vi = var as usize;
                    if vi >= num_vars {
                        continue;
                    }
                    if !self.is_var_fixed_for_offset_eq(var) {
                        continue;
                    }
                    let var_reasons = self.collect_fixed_term_var_reasons(var);
                    for lit in var_reasons {
                        if seen.insert(lit) {
                            reasons.push(lit);
                        }
                    }
                }
            }

            if reasons.is_empty() {
                self.propagated_equality_pairs.remove(&pair);
                continue;
            }

            requests.push(ModelEqualityRequest {
                lhs: pair.0,
                rhs: pair.1,
                reason: reasons,
                implied: false,
            });
        }

        requests.sort_by_key(|req| (req.lhs.0, req.rhs.0));
        requests
    }

    fn model_value_equality_is_asserted_false(&self, lhs: TermId, rhs: TermId) -> bool {
        self.terms().find_eq(lhs, rhs).is_some_and(|eq_atom| {
            self.asserted.get(&eq_atom) == Some(&false)
                || self.cross_theory_asserted.get(&eq_atom) == Some(&false)
        })
    }

    /// Model-value-based equality detection (Z3's `assume_eqs`).
    ///
    /// After simplex finds a feasible model, group all shared (non-slack)
    /// variables by their current model value. For pairs with the same value,
    /// generate `ModelEqualityRequest`s so the SAT solver can try setting the
    /// corresponding equality atoms to true. This is a model-based *guess*,
    /// not a deduction — reasons are empty.
    ///
    /// This is critical for benchmarks with many real-variable equality
    /// comparisons (simple_startup, sc, uart families) where the SAT solver
    /// would otherwise blindly explore equality branches.
    ///
    /// Reference: Z3 `theory_lra.cpp` assume_eqs / random_update.
    /// Fix A: classify a single term as a *native* arithmetic leaf (one whose
    /// LP value is a faithful arithmetic quantity) versus an *opaque* leaf such
    /// as an uninterpreted-function application that LRA only sees through an
    /// interned interface variable.
    ///
    /// Native = `Var`, an Int/Real `Const`, or an arithmetic-operator `App`
    /// (`+ - * /` and the unary/abs variants), plus array `select` of Int/Real
    /// sort (the AUFLIA index-equality case). Everything else — most importantly
    /// `App(Named f, ..)` where `f` is a user function symbol — is opaque.
    ///
    /// Only Int/Real-sorted terms qualify; non-arith sorts can never be a native
    /// arithmetic leaf (mirrors the #7451 sort guard in `assert_shared_equality`).
    fn term_is_native_arith(&self, term: TermId) -> bool {
        let terms = self.terms();
        if !matches!(terms.sort(term), Sort::Int | Sort::Real) {
            return false;
        }
        match terms.get(term) {
            TermData::Var(_, _) => true,
            TermData::Const(Constant::Int(_) | Constant::Rational(_)) => true,
            TermData::App(Symbol::Named(name), _) => matches!(
                name.as_str(),
                "+" | "-" | "*" | "/" | "div" | "mod" | "abs" | "to_int" | "to_real" | "select"
            ),
            _ => false,
        }
    }

    /// Fix A: a discovered model-value-equality pair is "preferable over a
    /// disequality split" only when it is *justified* (carries a non-empty
    /// reason — a genuine theory proof) or both sides are native arithmetic
    /// leaves. Empty-reason guesses over opaque UF-application interface
    /// variables (the EUF+LIA incompleteness root cause) are NOT preferred;
    /// the caller falls through to the already-sound disequality split.
    pub(crate) fn model_eq_pair_prefer_over_split(&self, req: &ModelEqualityRequest) -> bool {
        if !req.reason.is_empty() {
            return true;
        }
        self.term_is_native_arith(req.lhs) && self.term_is_native_arith(req.rhs)
    }

    /// Extract the two operand terms of an `(= a b)` or `(distinct a b)` atom.
    /// Returns `None` for n-ary distinct (n>2) or non-(in)equality atoms.
    fn binary_eq_operands(&self, atom: TermId) -> Option<(TermId, TermId)> {
        match self.terms().get(atom) {
            TermData::App(Symbol::Named(name), args)
                if (name == "=" || name == "distinct") && args.len() == 2 =>
            {
                Some((args[0], args[1]))
            }
            _ => None,
        }
    }

    /// SOUNDNESS GATE (false-UNSAT on QF_LRA diseq + eq-alias-under-push).
    ///
    /// A proof-less model-value-equality *guess* (Z3 `assume_eqs`) groups
    /// shared variables by their coincidental LP value. When such a guess is
    /// PREFERRED over a disequality expression split, the encoded equality is
    /// fed to CDCL and merged into the asserted-equality closure. If the guess
    /// connects (transitively, through the asserted-equality closure) into the
    /// equivalence class of an endpoint of an ACTIVE disequality, it can make
    /// the disequality refutable by facts that are NOT entailed — the free
    /// variables only coincided in a spurious model. In the simplest case the
    /// guess directly closes the disequality (e.g. guess `v0 = v2`, asserted
    /// `v1 = v0`, disequality `v2 != v1`). In a multi-round case the guess
    /// merely *grows* a class that contains a disequality endpoint, and a later
    /// (now-blocked) guess would close it; either way the result is a false
    /// UNSAT or a diverging split loop.
    ///
    /// This returns `true` when merging `(a, b)` into the asserted-true-equality
    /// closure would place EITHER side of the guess in the same class as ANY
    /// endpoint of an active disequality. Such guesses must NOT be
    /// preferred/emitted; the caller falls through to the sound disequality
    /// expression split (which explores `a < b ∨ a > b` and yields SAT, or
    /// fails closed to Unknown). This is intentionally conservative: it may
    /// suppress some legitimate `assume_eqs` progress, but the fallback is
    /// always sound.
    ///
    /// Genuinely-unsat cases are unaffected: when a disequality expression is
    /// FORCED to 0 by real equality/bound constraints, `check_disequalities`
    /// returns `Unsat` directly and never reaches the model-eq preference
    /// branch (see `disequality_check.rs` forced-to-0 / all-vars-pinned paths).
    /// Apply the disequality-closure soundness gate to a freshly-discovered set
    /// of model-value-equality guesses, in place: drop every proof-less guess
    /// that would touch an active disequality's equivalence class (see
    /// `DiseqClosureGate::guess_touches`). Justified guesses (non-empty
    /// reason) are always kept. The gate is UNCONDITIONAL: the former
    /// `AY_NO_DISEQ_CLOSURE_GUARD` kill-switch (which restored the pre-fix,
    /// false-UNSAT-prone behaviour) is removed — no environment variable may
    /// turn off a soundness gate.
    pub(crate) fn filter_unsound_model_eq_guesses(&self, guesses: &mut Vec<ModelEqualityRequest>) {
        // PERF (verification-consumer ghost-collection timeouts): the disequality trails,
        // the multi-variable groups, and the asserted-equality closure are all
        // independent of the individual guess, so build them ONCE per filter
        // call instead of once per guess. The per-guess test then reduces to
        // two union-find lookups (see `DiseqClosureGate::guess_touches`).
        // The previous per-guess rebuild was O(guesses × asserted-equalities)
        // and dominated solve time on N-O-heavy instances with hundreds of
        // same-model-value shared variables (e.g. Creusot ghost/FSet tests).
        let mut gate = self.build_diseq_closure_gate();
        guesses.retain(|req| {
            // Justified guesses carry a genuine theory proof — keep them.
            if !req.reason.is_empty() {
                return true;
            }
            !gate.guess_touches(req.lhs, req.rhs)
        });
    }

    /// Build the guess-independent half of the disequality-closure soundness
    /// gate: the asserted-true-equality union-find plus the set of union-find
    /// roots that a proof-less guess must not touch (binary-disequality
    /// endpoints and #9604 multi-variable expression co-variables).
    fn build_diseq_closure_gate(&self) -> DiseqClosureGate {
        // Collect the endpoints of every active (binary) disequality. These are
        // the terms that must remain in DISTINCT equivalence classes, so the
        // assume_eqs guesser must not merge fresh variables into their classes.
        let mut diseq_endpoints: Vec<TermId> = Vec::new();
        for (term, _expr, _value) in &self.disequality_trail {
            if let Some((p, q)) = self.binary_eq_operands(*term) {
                diseq_endpoints.push(p);
                diseq_endpoints.push(q);
            }
        }
        for (p, q, _expr, _reasons, _eq) in &self.shared_disequality_trail {
            diseq_endpoints.push(*p);
            diseq_endpoints.push(*q);
        }

        // #9604: Multi-variable / multi-arg `distinct` disequalities (e.g.
        // `(distinct (+ v4 v4) v3 (- v1 v3))`) do NOT have binary `=`/`distinct`
        // operand terms that `binary_eq_operands` can extract — their trail entry
        // is an arithmetic *expression* `E ≠ 0` over several LRA variables. The
        // binary-endpoint guard above therefore never fires for them, so a
        // proof-less model-value-equality guess that equates two of the
        // expression's variables (because they coincided in a spurious LP model)
        // is wrongly PREFERRED over the sound expression split, and the assume_eqs
        // loop drives the search to a false UNSAT (C1/C2 in the diseq+distinct
        // fuzz; `AY_NO_DISEQ_CLOSURE_GUARD` had no effect precisely because the
        // binary guard could not see these endpoints).
        //
        // For each active disequality whose expression mentions ≥2 distinct LRA
        // variables, collect the corresponding *variable terms* (via var_to_term)
        // as a group. A proof-less guess that, through the asserted-equality
        // closure, lands BOTH its endpoints inside the SAME such group is
        // equating two co-variables of a multi-variable disequality — a
        // non-entailed merge that can refute the disequality. Such guesses are
        // dropped (caller falls through to the sound expression split → SAT or
        // Unknown). Single-variable disequalities keep the precise binary
        // handling above and are unaffected (their expr has <2 variables).
        let mut multivar_groups: Vec<Vec<TermId>> = Vec::new();
        let collect_group = |expr: &LinearExpr, groups: &mut Vec<Vec<TermId>>| {
            let group: Vec<TermId> = expr
                .coeffs
                .iter()
                .filter(|(_, c)| !c.is_zero())
                .filter_map(|(v, _)| self.var_to_term.get(v).copied())
                .collect();
            // Need ≥2 distinct variable terms for the merge-within-group test to
            // be meaningful (a single-variable disequality is handled precisely
            // by the binary-endpoint path; an expr with <2 mapped vars cannot be
            // closed by a single equality guess).
            if group.len() >= 2 {
                groups.push(group);
            }
        };
        for (_term, expr, _value) in &self.disequality_trail {
            collect_group(expr, &mut multivar_groups);
        }
        for (_p, _q, expr, _reasons, _eq) in &self.shared_disequality_trail {
            collect_group(expr, &mut multivar_groups);
        }

        if diseq_endpoints.is_empty() && multivar_groups.is_empty() {
            // Nothing to protect: the gate is trivially open, skip the
            // closure build entirely.
            return DiseqClosureGate::default();
        }

        // Build a union-find over every term mentioned in an asserted-true
        // equality plus every disequality endpoint / group member.
        let mut uf = EqClosureUf::default();

        // Union all asserted-true equality atoms (per-theory and cross-theory).
        for (&atom, &value) in self
            .asserted
            .iter()
            .chain(self.cross_theory_asserted.iter())
        {
            // Asserted-true `=` (or asserted-false `distinct`) is an equality.
            let is_eq_true = value
                && matches!(
                    self.terms().get(atom),
                    TermData::App(Symbol::Named(name), _) if name == "="
                );
            let is_distinct_false = !value
                && matches!(
                    self.terms().get(atom),
                    TermData::App(Symbol::Named(name), _) if name == "distinct"
                );
            if is_eq_true || is_distinct_false {
                if let Some((a, b)) = self.binary_eq_operands(atom) {
                    uf.union(a, b);
                }
            }
        }

        // Precompute the set of union-find roots a proof-less guess must not
        // touch. This is EXACTLY equivalent to the previous per-guess test,
        // which merged the guess pair into a fresh copy of the closure and
        // asked:
        //
        //   (a) does any binary-disequality endpoint `ep` satisfy
        //       `same_class(lhs, ep) || same_class(rhs, ep)` post-merge, or
        //   (b) (#9604) does any multi-variable group contain a term in the
        //       class of `lhs` AND a term in the class of `rhs` post-merge?
        //
        // Post-merge, `lhs` and `rhs` share ONE class C = class(lhs) ∪
        // class(rhs), so (a) holds iff some endpoint's base root equals
        // root(lhs) or root(rhs), and in (b) "in the class of lhs" and "in the
        // class of rhs" are the same predicate (membership in C), so (b) holds
        // iff some group member's base root equals root(lhs) or root(rhs).
        // Both reduce to: root(lhs) or root(rhs) is in the blocked-root set
        // below — no per-guess union (and hence no per-guess closure copy) is
        // needed. We deliberately do NOT exempt "already-entailed" guesses
        // (where `lhs`/`rhs` are pre-merged): even a redundant guess, once
        // emitted into the disequality split loop, re-routes it down the buggy
        // assume_eqs path and yields a false UNSAT (validated: keeping
        // entailed guesses reintroduced 3 false-unsats in the diseq+eq-alias
        // fuzz). Soundness over completeness — the caller falls through to the
        // sound expression split (SAT, or Unknown).
        let mut blocked_roots: HashSet<usize> = HashSet::default();
        for ep in diseq_endpoints {
            let i = uf.intern(ep);
            let root = uf.find(i);
            blocked_roots.insert(root);
        }
        for group in multivar_groups {
            for t in group {
                let i = uf.intern(t);
                let root = uf.find(i);
                blocked_roots.insert(root);
            }
        }

        DiseqClosureGate { uf, blocked_roots }
    }

    pub(crate) fn discover_model_value_equalities(&mut self) -> Vec<ModelEqualityRequest> {
        // #8187: Only run model-based equality discovery (Z3's assume_eqs) when
        // the solver is part of a combined theory context (Nelson-Oppen) OR when
        // we have active disequality constraints in pure LIA/LRA (#8707).
        //
        // In pure QF_LRA with only inequalities, model-based equality guesses
        // are not needed and produce spurious NeedModelEquality results for
        // variables that happen to share the same default model value (0).
        //
        // However, in pure QF_LIA with pairwise `distinct` constraints (e.g.,
        // 8-queens, SEND+MORE=MONEY), the LP repeatedly assigns equal integer
        // values to variables that must be distinct, and the disequality-split
        // loop diverges (#8707). Z3's `assume_eqs` (theory_arith_aux.h:2199-2251)
        // runs in pure LIA final-check too, letting CDCL learn blocking clauses
        // that escape the diseq trap. Mirror that behaviour: when at least one
        // disequality is active (from the per-theory trail or N-O), run
        // `assume_eqs` even outside combined mode.
        let has_active_disequalities =
            !self.disequality_trail.is_empty() || !self.shared_disequality_trail.is_empty();
        if !self.combined_theory_mode && !has_active_disequalities {
            return Vec::new();
        }

        // Collect (value, var_id, term_id) for shared variables.
        let mut entries: Vec<(&InfRational, u32, TermId)> = Vec::new();
        for (&var_id, &term_id) in &self.var_to_term {
            if self.slack_var_set.contains(&var_id) {
                continue;
            }
            let vi = var_id as usize;
            if vi >= self.vars.len() {
                continue;
            }
            entries.push((&self.vars[vi].value, var_id, term_id));
        }

        if entries.len() < 2 {
            return Vec::new();
        }

        // Sort by value, then by term_id for determinism.
        entries.sort_by(|a, b| a.0.cmp(b.0).then(a.2 .0.cmp(&b.2 .0)));

        let mut requests = Vec::new();
        let mut i = 0;
        while i < entries.len() {
            // Find the run of entries with the same value.
            let mut j = i + 1;
            while j < entries.len() && entries[j].0 == entries[i].0 {
                j += 1;
            }
            // entries[i..j] all have the same model value.
            if j - i >= 2 {
                // Anchor pattern: pair the first entry with each subsequent one.
                let anchor_term = entries[i].2;
                let anchor_sort = self.terms().sort(anchor_term);
                for entry in entries.iter().take(j).skip(i + 1) {
                    let other_term = entry.2;
                    if anchor_term == other_term {
                        continue;
                    }
                    // Only pair same-sort variables.
                    if self.terms().sort(other_term) != anchor_sort {
                        continue;
                    }
                    let pair = if anchor_term.0 < other_term.0 {
                        (anchor_term, other_term)
                    } else {
                        (other_term, anchor_term)
                    };
                    if self.model_value_equality_is_asserted_false(pair.0, pair.1) {
                        continue;
                    }
                    if !self.propagated_equality_pairs.insert(pair) {
                        continue;
                    }
                    requests.push(ModelEqualityRequest {
                        lhs: pair.0,
                        rhs: pair.1,
                        reason: Vec::new(),
                        implied: false,
                    });
                }
            }
            i = j;
        }

        requests
    }
}

/// Guess-independent half of the disequality-closure soundness gate: the
/// asserted-true-equality closure plus the union-find roots of every protected
/// term (binary-disequality endpoints and #9604 multi-variable expression
/// co-variables). Built once per `filter_unsound_model_eq_guesses` call;
/// each guess then costs two union-find lookups. See the equivalence proof in
/// `build_diseq_closure_gate`.
#[derive(Default)]
struct DiseqClosureGate {
    uf: EqClosureUf,
    blocked_roots: HashSet<usize>,
}

impl DiseqClosureGate {
    /// Would merging the proof-less guess `(lhs, rhs)` into the asserted
    /// equality closure place either side in the class of a protected term?
    fn guess_touches(&mut self, lhs: TermId, rhs: TermId) -> bool {
        if self.blocked_roots.is_empty() {
            return false;
        }
        let il = self.uf.intern(lhs);
        let rl = self.uf.find(il);
        if self.blocked_roots.contains(&rl) {
            return true;
        }
        let ir = self.uf.intern(rhs);
        let rr = self.uf.find(ir);
        self.blocked_roots.contains(&rr)
    }
}

/// Small union-find over `TermId`s, used by the model-equality soundness gate
/// (`DiseqClosureGate`) to compute the asserted-equality closure and detect
/// whether a proof-less guess would merge the two endpoints of an active
/// disequality.
#[derive(Default)]
struct EqClosureUf {
    index: HashMap<TermId, usize>,
    parent: Vec<usize>,
}

impl EqClosureUf {
    fn intern(&mut self, t: TermId) -> usize {
        if let Some(&i) = self.index.get(&t) {
            return i;
        }
        let i = self.parent.len();
        self.index.insert(t, i);
        self.parent.push(i);
        i
    }

    fn find(&mut self, x: usize) -> usize {
        let mut x = x;
        while self.parent[x] != x {
            self.parent[x] = self.parent[self.parent[x]];
            x = self.parent[x];
        }
        x
    }

    fn union(&mut self, a: TermId, b: TermId) {
        let ia = self.intern(a);
        let ib = self.intern(b);
        let ra = self.find(ia);
        let rb = self.find(ib);
        if ra != rb {
            self.parent[ra] = rb;
        }
    }
}
