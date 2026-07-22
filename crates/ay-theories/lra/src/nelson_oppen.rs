// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    pub(crate) fn propagate_equalities_inner(&mut self) -> EqualityPropagationResult {
        let debug = self.debug_lra_nelson_oppen;

        // Collect variables with tight bounds (lower == upper, both non-strict)
        // These are variables whose value is uniquely determined.
        // #8406: Use Rational instead of BigRational to avoid heap allocation per
        // tight-bound variable. Most bound values fit in i64, so the inline Small(n,d)
        // path avoids all allocation during Nelson-Oppen equality propagation.
        let mut tight_bound_vars: Vec<(TermId, Rational, Vec<TheoryLit>)> = Vec::new();

        // Sort term_to_var entries by TermId for deterministic iteration (#2681).
        let mut sorted_term_vars: Vec<_> = self.term_to_var.iter().collect();
        sorted_term_vars.sort_by_key(|(&term, _)| term.0);

        for (&var_term, &var_id) in sorted_term_vars {
            if let Some(info) = self.vars.get(var_id as usize) {
                if let (Some(ref lower), Some(ref upper)) = (&info.lower, &info.upper) {
                    // Check if bounds are equal and non-strict (tight).
                    if lower.value == upper.value && !lower.strict && !upper.strict {
                        // Collect reasons from both bounds.
                        let mut reasons = Vec::new();
                        for (term, val) in lower.reason_pairs() {
                            if !term.is_sentinel() {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }
                        for (term, val) in upper.reason_pairs() {
                            if !term.is_sentinel() && !reasons.iter().any(|r| r.term == term) {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }

                        if debug {
                            safe_eprintln!(
                                "[LRA N-O] Tight bound: term {} = {} (reasons: {:?})",
                                var_term.0,
                                lower.value,
                                reasons
                            );
                        }

                        // Skip zero-reason tight bounds (#6282): these are variables
                        // whose value is only determined by simplex initialization
                        // (default model), not by asserted constraints. Propagating
                        // them as N-O equalities floods EUF with "all variables = 0"
                        // equalities that create spurious conflicts, preventing the
                        // N-O fixpoint from converging. Model-based equalities should
                        // go through discover_model_equality / NeedModelEquality
                        // instead, which lets the SAT solver explore both branches.
                        if reasons.is_empty() {
                            if self.debug_lra_nelson_oppen {
                                safe_eprintln!(
                                    "[LRA N-O] Skipping zero-reason tight bound: term {} = {}",
                                    var_term.0,
                                    lower.value,
                                );
                            }
                            continue;
                        }
                        if self.debug_lra_nelson_oppen {
                            safe_eprintln!(
                                "[LRA N-O] KEEPING tight bound: term {} = {} ({} reasons)",
                                var_term.0,
                                lower.value,
                                reasons.len(),
                            );
                        }
                        tight_bound_vars.push((var_term, lower.value.clone(), reasons));
                    }
                }
            }
        }

        // Group variables by their value.
        let mut vars_by_value: HashMap<Rational, Vec<(TermId, Vec<TheoryLit>)>> =
            HashMap::default();
        for (term, value, reasons) in tight_bound_vars {
            vars_by_value
                .entry(value)
                .or_default()
                .push((term, reasons));
        }

        // Sort groups by value for deterministic iteration (#2681).
        let mut sorted_groups: Vec<_> = vars_by_value.iter().collect();
        sorted_groups.sort_by_key(|(a, _)| *a);

        // For each group of variables with the same value, propagate equalities.
        for (_value, vars) in sorted_groups {
            if vars.len() < 2 {
                continue;
            }

            // Propagate pairwise equalities between all variables with same value.
            for i in 0..vars.len() {
                for j in (i + 1)..vars.len() {
                    let (lhs, lhs_reasons) = &vars[i];
                    let (rhs, rhs_reasons) = &vars[j];

                    // SOUNDNESS (#cross-sort-alias wrong-UNSAT, AUFLIRA
                    // 2026-07): value-based grouping is sort-blind, and mixed
                    // Int/Real solving tracks terms of BOTH sorts here (an Int
                    // term asserted to the Real side, a Real UF value shared
                    // with LIA). Equating an Int term with a Real term because
                    // their numeric values coincide is ill-sorted: EUF then
                    // merges e.g. Int(5) and Rational(5) into one class and its
                    // constant-conflict check "refutes" the innocent ground
                    // fact that pinned the value — a false conflict / wrong
                    // UNSAT. Same guard family as the Bool rejection (#8786).
                    if self.terms().sort(*lhs) != self.terms().sort(*rhs) {
                        continue;
                    }

                    // Canonicalize the pair to avoid duplicate propagations.
                    let pair = if lhs.0 < rhs.0 {
                        (*lhs, *rhs)
                    } else {
                        (*rhs, *lhs)
                    };

                    if !self.propagated_equality_pairs.contains(&pair) {
                        self.propagated_equality_pairs.insert(pair);

                        // Combine reasons from both variables.
                        // Use HashSet for O(1) dedup instead of Vec::contains().
                        let mut reason_seen: HashSet<TheoryLit> =
                            lhs_reasons.iter().copied().collect();
                        let mut combined_reasons = lhs_reasons.clone();
                        for r in rhs_reasons {
                            if reason_seen.insert(*r) {
                                combined_reasons.push(*r);
                            }
                        }

                        if debug {
                            safe_eprintln!(
                                "[LRA N-O] Propagating equality: term {} = term {} (reasons: {:?})",
                                lhs.0,
                                rhs.0,
                                combined_reasons
                            );
                        }

                        self.pending_equalities.push(DiscoveredEquality::new(
                            *lhs,
                            *rhs,
                            combined_reasons,
                        ));
                    }
                }
            }
        }

        // #8469: Discover disequalities from tight bounds.
        // When two terms have tight bounds at DIFFERENT values, and both have
        // non-empty reasons (i.e., the value is provably forced, not just a
        // model default), they are provably unequal.
        // This enables arith->EUF disequality propagation, completing the
        // bidirectional Nelson-Oppen requirement.
        let mut new_disequalities = Vec::new();
        let mut sorted_groups_for_diseq: Vec<_> = vars_by_value.iter().collect();
        sorted_groups_for_diseq.sort_by_key(|(a, _)| *a);

        for i in 0..sorted_groups_for_diseq.len() {
            for j in (i + 1)..sorted_groups_for_diseq.len() {
                let (_, group_a) = &sorted_groups_for_diseq[i];
                let (_, group_b) = &sorted_groups_for_diseq[j];

                // For each pair of groups with different values, propagate
                // disequalities between their members. Use anchor approach:
                // pick the first term from each group to avoid O(n*m) blow-up.
                // This is sufficient because equality transitivity means if
                // the anchor is unequal, all group members are unequal.
                for (term_a, reasons_a) in group_a.iter().take(1) {
                    if reasons_a.is_empty() {
                        continue;
                    }
                    for (term_b, reasons_b) in group_b.iter().take(1) {
                        if reasons_b.is_empty() {
                            continue;
                        }
                        // SOUNDNESS (#cross-sort-alias): never emit an
                        // ill-sorted disequality between terms of different
                        // sorts (mirrors the equality guard above).
                        if self.terms().sort(*term_a) != self.terms().sort(*term_b) {
                            continue;
                        }
                        let pair = if term_a.0 < term_b.0 {
                            (*term_a, *term_b)
                        } else {
                            (*term_b, *term_a)
                        };
                        if self.propagated_disequality_pairs.contains(&pair) {
                            continue;
                        }
                        self.propagated_disequality_pairs.insert(pair);

                        // Combine reasons from both tight bounds.
                        let mut reason_seen: HashSet<TheoryLit> =
                            reasons_a.iter().copied().collect();
                        let mut combined_reasons = reasons_a.clone();
                        for r in reasons_b {
                            if reason_seen.insert(*r) {
                                combined_reasons.push(*r);
                            }
                        }

                        if debug {
                            safe_eprintln!(
                                "[LRA N-O] Propagating disequality: term {} != term {} ({} reasons)",
                                term_a.0,
                                term_b.0,
                                combined_reasons.len()
                            );
                        }

                        new_disequalities.push(DiscoveredDisequality::new(
                            *term_a,
                            *term_b,
                            combined_reasons,
                        ));
                    }
                }
            }
        }

        // Return and clear pending equalities.
        let new_equalities = std::mem::take(&mut self.pending_equalities);
        if !new_equalities.is_empty() {
            info!(
                target: "ay::lra",
                propagated = new_equalities.len(),
                "Nelson-Oppen equality propagation"
            );
        }
        if !new_disequalities.is_empty() {
            info!(
                target: "ay::lra",
                propagated = new_disequalities.len(),
                "Nelson-Oppen disequality propagation"
            );
        }
        EqualityPropagationResult {
            equalities: new_equalities,
            disequalities: new_disequalities,
            ..Default::default()
        }
    }

    pub(crate) fn assert_shared_equality_inner(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) {
        // Receive equality from another theory (EUF→LRA direction in Nelson-Oppen).
        // Add the equality constraint: lhs = rhs, which means lhs - rhs = 0.
        //
        // This allows LRA to use EUF-discovered equalities in its arithmetic reasoning.
        // For example, if EUF tells us f(x) = y, we add the constraint f(x) - y = 0,
        // which affects bounds on both f(x) and y in the simplex tableau.

        let debug = self.debug_lra_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LRA N-O] Receiving shared equality: term {} = term {} (reason: {} lits)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // #8786: Soundness guard — reject Bool-sorted shared equalities.
        //
        // LRA only reasons about Real/Int terms. When EUF's congruence closure
        // discovers that two boolean atoms have equal values under the current
        // model (e.g. `(> a 0) = (> b 0)` both true), it queues the pair as a
        // shared equality. Forwarding it to LRA is unsound: parse_linear_expr
        // cannot interpret boolean atoms as arithmetic and silently creates
        // fresh theory vars aliased to both booleans, corrupting the simplex
        // tableau and producing wrong models. Bool-sorted equalities belong to
        // EUF / DPLL(T) Boolean propagation, not arithmetic.
        let lhs_sort = self.terms().sort(lhs);
        let rhs_sort = self.terms().sort(rhs);
        if *lhs_sort == Sort::Bool || *rhs_sort == Sort::Bool {
            if debug {
                safe_eprintln!(
                    "[LRA N-O]   Rejecting Bool-sorted shared equality (#8786 soundness guard): \
                     lhs sort {:?}, rhs sort {:?}",
                    lhs_sort,
                    rhs_sort,
                );
            }
            return;
        }

        // P1b: Soundness guard — reject shared equalities where either side is an
        // ITE term. An `(ite c t e)`'s value is condition-dependent (the condition
        // is a SAT-layer choice), so it is NOT a stable Nelson-Oppen shared
        // variable / UF-application term. EUF's congruence closure forwards
        // `ite_term = v` for EACH branch value it observes across case-splits
        // (e.g. `(ite p -3 -2) = -3` AND `= -2`); LRA would assert BOTH into the
        // simplex tableau simultaneously, deriving `-3 = -2` and a spurious
        // infeasibility => false-UNSAT (e.g. `(= (ga z) 5) ∧ (= z (ite p -3 -2))`,
        // QF_UFLRA). The ite is decided soundly by its lifted branch atoms; the
        // arithmetic relation between the ite and a constant must NOT be imposed
        // as an unconditional shared equality. Same class of guard as #8786.
        // The guard is UNCONDITIONAL: the former `AY_LRA_NO_ITE_SHARED_EQ=0`
        // kill-switch (which restored the unsound pre-fix path) is removed —
        // no environment variable may re-enable an unsound path.
        if matches!(self.terms().get(lhs), TermData::Ite(..))
            || matches!(self.terms().get(rhs), TermData::Ite(..))
        {
            if debug {
                safe_eprintln!(
                    "[LRA N-O]   Rejecting ITE-term shared equality (P1b soundness guard): \
                     lhs {:?}, rhs {:?}",
                    self.terms().get(lhs),
                    self.terms().get(rhs),
                );
            }
            return;
        }

        // Parse both terms into linear expressions.
        // current_parsing_atom is None here, so parse_linear_expr won't mark
        // any atom as unsupported — shared equalities are cross-theory terms
        // handled by the other theory's semantics (#6167, #5511).
        debug_assert!(self.current_parsing_atom.is_none());
        let lhs_expr = self.parse_linear_expr(lhs);
        let rhs_expr = self.parse_linear_expr(rhs);

        // Build linear expression: lhs - rhs = 0.
        let mut diff_expr = lhs_expr;
        for &(var, ref coeff) in &rhs_expr.coeffs {
            diff_expr.add_term_rat(var, -coeff.clone());
        }
        diff_expr.constant = &diff_expr.constant - &rhs_expr.constant;

        // If expression is just a constant, check if it's zero.
        if diff_expr.is_constant() {
            if diff_expr.constant.is_zero() {
                if debug {
                    safe_eprintln!("[LRA N-O]   Equality is trivially true (constant 0)");
                }
            } else {
                // Constant is non-zero: lhs - rhs = c where c != 0, so lhs = rhs
                // is impossible. Record a trivial conflict using the reason literal
                // so DPLL(T) can backtrack. (#6157)
                if debug {
                    safe_eprintln!(
                        "[LRA N-O]   Equality is impossible! Constant {} != 0 — recording conflict",
                        diff_expr.constant
                    );
                }
                if self.trivial_conflict.is_none() {
                    // #8012: Store ALL reason literals so the blocking clause is
                    // complete. Previously only reason.first() was kept, producing
                    // overly-strong single-literal blocking clauses that eliminated
                    // valid SAT assignments when EUF propagated multi-literal
                    // equalities (e.g., f(a)=f(b) because a=b).
                    let conflict_lits: Vec<TheoryLit> = if reason.is_empty() {
                        vec![TheoryLit::new(lhs, true)]
                    } else {
                        reason.to_vec()
                    };
                    self.trivial_conflict = Some(conflict_lits);
                }
                self.dirty = true;
            }
            return;
        }

        // Assert the equality: diff_expr = 0, i.e., diff_expr <= 0 AND diff_expr >= 0.
        //
        // Pass ALL reason literals so conflict explanations are complete.
        // Previously only the first reason was tracked, causing false UNSAT
        // when cross-disequality split atoms were dropped (#4891).
        let reasons: Vec<(TermId, bool)> = if reason.is_empty() {
            vec![(lhs, true)]
        } else {
            reason.iter().map(|r| (r.term, r.value)).collect()
        };
        self.record_cross_theory_reasons(&reasons);

        // #8406: Rational::zero() avoids BigRational heap allocation.
        let zero = Rational::zero();

        self.assert_bound_with_reasons(
            diff_expr.clone(),
            zero.clone(),
            BoundType::Upper,
            false,
            &reasons,
            None,
        );
        self.assert_bound_with_reasons(diff_expr, zero, BoundType::Lower, false, &reasons, None);

        // Mark as dirty to trigger re-check.
        self.dirty = true;
    }

    pub(crate) fn assert_shared_disequality_inner(
        &mut self,
        lhs: TermId,
        rhs: TermId,
        reason: &[TheoryLit],
    ) {
        // Receive disequality from another theory (EUF→LRA direction in Nelson-Oppen).
        // When EUF asserts (not (= (f x) y)), LRA needs to know lhs != rhs so it can
        // detect violations: if the LRA model satisfies lhs = rhs, a split or conflict
        // is generated (#5228).

        let debug = self.debug_lra_nelson_oppen;
        if debug {
            safe_eprintln!(
                "[LRA N-O] Receiving shared disequality: term {} != term {} (reason: {} lits)",
                lhs.0,
                rhs.0,
                reason.len()
            );
        }

        // Parse both terms into linear expressions (same as assert_shared_equality).
        // current_parsing_atom is None here (#6167).
        debug_assert!(self.current_parsing_atom.is_none());
        let lhs_expr = self.parse_linear_expr(lhs);
        let rhs_expr = self.parse_linear_expr(rhs);

        // Build linear expression: lhs - rhs.
        let mut diff_expr = lhs_expr;
        for &(var, ref coeff) in &rhs_expr.coeffs {
            diff_expr.add_term_rat(var, -coeff.clone());
        }
        diff_expr.constant = &diff_expr.constant - &rhs_expr.constant;

        // If expression is just a constant, check if it's zero.
        if diff_expr.is_constant() {
            if diff_expr.constant.is_zero() {
                // lhs = rhs is forced but we have lhs != rhs — immediate conflict.
                // Record the conflict so DPLL(T) can backtrack. (#6157)
                if debug {
                    safe_eprintln!(
                        "[LRA N-O]   Shared disequality is trivially violated (constant 0 != 0) — recording conflict"
                    );
                }
                if self.trivial_conflict.is_none() {
                    // #8012: Store ALL reason literals (same fix as equality path).
                    let conflict_lits: Vec<TheoryLit> = if reason.is_empty() {
                        vec![TheoryLit::new(lhs, true)]
                    } else {
                        reason.to_vec()
                    };
                    self.trivial_conflict = Some(conflict_lits);
                }
                self.dirty = true;
            }
            // Non-zero constant: disequality is trivially satisfied, nothing to do.
            return;
        }

        // #6131: Extract the original equality term from the reason literals.
        // The first reason literal with value=false is the negated equality atom
        // (e.g., TheoryLit { term: (= a b), value: false }). This term is passed
        // to DisequalitySplitRequest so split clauses become conditional:
        // `(= a b) OR (x < c) OR (x > c)` instead of the unconditional
        // `(x < c) OR (x > c)` which survives backtracking and can cause false UNSAT.
        let eq_term = reason
            .iter()
            .find(|lit| !lit.value)
            .map(|lit| lit.term)
            .or_else(|| self.terms().find_eq(lhs, rhs));

        // (#6131) Shared disequalities from the combiner (direct EUF→LRA path)
        // always have a negated equality in their reason. However, disequalities
        // from the Nelson-Oppen fixpoint loop (tight-bound propagation via
        // check_loops.rs) may have reasons containing only positive bound literals
        // with no negated equality atom. This is legitimate for congruence-derived
        // disequalities on mixed ReLU/AUFLIRA encodings (#8516).
        //
        // When eq_term is None, the disequality split will be unconditional
        // (fallback at check_shared_disequalities returns Unknown), which is
        // sound but less efficient. The fallback re-evaluates on the next check().
        if eq_term.is_none() && debug {
            safe_eprintln!(
                "[LRA N-O] WARNING: shared disequality has no negated equality in reason ({} lits, all true)",
                reason.len()
            );
        }

        // Store in the shared disequality trail for post-simplex checking.
        self.shared_disequality_trail
            .push((lhs, rhs, diff_expr, reason.to_vec(), eq_term));
        self.record_cross_theory_reasons_from_lits(reason);

        // Mark as dirty to trigger re-check.
        self.dirty = true;
    }
}
