// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl LraSolver {
    /// Check regular disequalities against the current model.
    pub(crate) fn check_disequalities(
        &mut self,
        disequalities: &[(TermId, LinearExpr, bool)],
        debug: bool,
    ) -> Option<TheoryResult> {
        // Reset violation flag at start of disequality check. Will be set
        // to true if any violation triggers a split request.
        self.last_diseq_check_had_violation = false;
        // Clear stale batch splits from previous check() invocations (#6269).
        // Without this, splits buffered before a NeedExpressionSplit early
        // return survive into the next check() call, causing duplicates.
        self.pending_diseq_splits.clear();
        // #8707: Also reset buffered expression splits between check() calls.
        self.pending_expr_splits.clear();
        if debug {
            safe_eprintln!("[LRA] Before disequality check, var bounds:");
            for (i, info) in self.vars.iter().enumerate() {
                safe_eprintln!(
                    "  var {}: lb={:?}, ub={:?}, value={}",
                    i,
                    info.lower.as_ref().map(|b| &b.value),
                    info.upper.as_ref().map(|b| &b.value),
                    info.value
                );
            }
        }
        // Evaluate each disequality in the current model
        // A disequality (term, expr, asserted_value) with expr = LHS - RHS is violated if expr == 0
        let mut free_var_pair_repairs: Vec<(TermId, u32, u32)> = Vec::new();
        for (term, expr, asserted_value) in disequalities {
            // Evaluate the expression in the current model using InfRational
            // to account for epsilon components from strict bounds (#6020).
            // Using only the rational part (BigRational) discards ε, causing
            // values like x = 0+ε, y = 0 to evaluate as x - y = 0 instead
            // of x - y = ε ≠ 0, leading to spurious NeedExpressionSplit.
            let mut eval_inf = InfRational::from_rat(expr.constant.clone());
            for &(var, ref coeff) in &expr.coeffs {
                if let Some(info) = self.vars.get(var as usize) {
                    let scaled = info.value.mul_rat(coeff);
                    eval_inf += &scaled;
                }
            }
            let eval_value = eval_inf.rational();

            if debug {
                safe_eprintln!(
                    "[LRA] Checking disequality {:?}: expr value = {} (inf: {:?})",
                    term,
                    eval_value,
                    eval_inf
                );
            }

            // If expr == 0 (including epsilon), the disequality is violated.
            // A non-zero epsilon means the values differ infinitesimally,
            // which satisfies the disequality in the real-valued model.
            if eval_inf.is_zero() {
                // First check if the expression is forced to 0 by equality constraints.
                // This handles cases like `A = B` making `A - B` identically 0, even if
                // the individual variables A and B have slack.
                if let Some((equality_reasons, is_forced)) =
                    self.is_expression_forced_to_value(expr, &BigRational::zero())
                {
                    if is_forced {
                        debug!(
                            target: "ay::lra",
                            reason = "forced_equality",
                            "Disequality violated — UNSAT"
                        );
                        if debug {
                            safe_eprintln!(
                                "[LRA] Disequality {:?} is VIOLATED (expression forced to 0 by equality constraint) - returning Unsat",
                                term
                            );
                        }
                        let mut conflict = vec![TheoryLit {
                            term: *term,
                            value: *asserted_value,
                        }];
                        conflict.extend(equality_reasons);
                        self.stats.conflict_count += 1;
                        // #8762: Mark disequality violation so the next check()
                        // re-runs this evaluation even when bounds haven't
                        // tightened. Without this, the model_may_have_changed
                        // guard skips disequality re-check on the next LRA
                        // check() call and returns false Sat with S=Y=8
                        // (SEND+MORE=MONEY, n-queens, Sudoku).
                        self.last_diseq_check_had_violation = true;
                        self.dirty = true;
                        return Some(TheoryResult::Unsat(conflict));
                    }
                }

                // Fallback: Check if all individual variables in the expression are pinned.
                // This handles cases where the expression doesn't match a tableau row.
                let all_vars_pinned = expr.coeffs.iter().all(|&(var, _)| {
                    if let Some(info) = self.vars.get(var as usize) {
                        // Variable is pinned if lower == upper == value
                        let pinned = info
                            .lower
                            .as_ref()
                            .is_some_and(|lb| lb.value == info.value.rational())
                            && info
                                .upper
                                .as_ref()
                                .is_some_and(|ub| ub.value == info.value.rational());
                        if debug && !pinned {
                            safe_eprintln!(
                                "[LRA] Var {} has slack: value={}, lb={:?}, ub={:?}",
                                var,
                                info.value,
                                info.lower.as_ref().map(|b| &b.value),
                                info.upper.as_ref().map(|b| &b.value)
                            );
                        }
                        pinned
                    } else {
                        false // Unknown variable - conservative: assume not pinned
                    }
                });

                if all_vars_pinned || expr.coeffs.is_empty() {
                    debug!(
                        target: "ay::lra",
                        reason = "pinned_vars",
                        "Disequality violated — UNSAT"
                    );
                    if debug {
                        safe_eprintln!(
                            "[LRA] Disequality {:?} is VIOLATED with forced model - returning Unsat",
                            term
                        );
                    }
                    // All variables are pinned, so the model is forced and violates disequality
                    // Build conflict clause: disequality + all bound reasons that pinned the variables
                    let seed_lit = TheoryLit {
                        term: *term,
                        value: *asserted_value,
                    };
                    let mut conflict = vec![seed_lit];
                    let mut seen: HashSet<TheoryLit> = HashSet::default();
                    seen.insert(seed_lit);
                    // Add all bound reasons that contributed to pinning the variables.
                    // Use HashSet for O(1) dedup instead of Vec::contains() (#938).
                    for &(var, _) in &expr.coeffs {
                        if let Some(info) = self.vars.get(var as usize) {
                            if let Some(ref lb) = info.lower {
                                for (term, val) in lb.reason_pairs() {
                                    if !term.is_sentinel() {
                                        let lit = TheoryLit::new(term, val);
                                        if seen.insert(lit) {
                                            conflict.push(lit);
                                        }
                                    }
                                }
                            }
                            if let Some(ref ub) = info.upper {
                                for (term, val) in ub.reason_pairs() {
                                    if !term.is_sentinel() {
                                        let lit = TheoryLit::new(term, val);
                                        if seen.insert(lit) {
                                            conflict.push(lit);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    self.stats.conflict_count += 1;
                    // #8762: See comment above — mark the violation so the
                    // next LRA check() re-evaluates this disequality even
                    // when no bounds tightened.
                    self.last_diseq_check_had_violation = true;
                    self.dirty = true;
                    return Some(TheoryResult::Unsat(conflict));
                } else {
                    // Some variables have slack, so other solutions might exist.
                    // Request a split on (expr < 0) OR (expr > 0) to explore both regions.
                    // For a simple disequality like x != 0, this becomes (x < 0) OR (x > 0).

                    // Find a variable to split on.
                    // For single-variable disequalities (x != c), we split on x.
                    // For multi-variable disequalities (x - y != 0), we pick any variable with slack.
                    if expr.coeffs.len() == 1 {
                        let (var, coeff) = &expr.coeffs[0];
                        if let Some(&var_term) = self.var_to_term.get(var) {
                            // For expr = coeff*x + const = 0, the excluded value is -const/coeff.
                            // Previously this incorrectly used -const (ignoring coeff), which
                            // caused wrong split clauses for scaled disequalities like
                            // (distinct (* 2 x) 6) → should exclude x=3, not x=6 (#6155).
                            let excluded = (-expr.constant.clone() / coeff.clone()).to_big();
                            if debug {
                                safe_eprintln!(
                                    "[LRA] Disequality {:?} violated with slack - buffering split on var {:?} != {}",
                                    term,
                                    var_term,
                                    excluded
                                );
                            }
                            // Batch collect all single-var disequality splits (#6259).
                            // Instead of returning immediately on the first violation,
                            // collect all violated disequalities so the DPLL(T) split
                            // loop can process them in a single iteration. This avoids
                            // O(N) solver restarts for N violated disequalities.
                            self.pending_diseq_splits.push(DisequalitySplitRequest {
                                variable: var_term,
                                excluded_value: excluded,
                                disequality_term: Some(*term),
                                is_distinct: *asserted_value,
                            });
                            // Continue to check remaining disequalities
                            continue;
                        }
                    } else if let Some((lhs_var, rhs_var)) =
                        self.free_int_var_pair_disequality_candidate(expr)
                    {
                        free_var_pair_repairs.push((*term, lhs_var, rhs_var));
                        self.dirty = true;
                        self.last_diseq_check_had_violation = true;
                        continue;
                    } else {
                        // Multi-variable disequality (e.g., E - F != 0, i.e., E != F).
                        //
                        // Always use expression splits for multi-variable disequalities.
                        // Single-variable enumeration is UNSOUND here (#5671): the clause
                        // `~distinct(E,F) OR var <= c-1 OR var >= c+1` doesn't capture
                        // constraints on the other variables, so it over-constrains the
                        // search space and can cause false UNSAT. The correct split is
                        // on the full expression: `E < F OR E > F`.
                        //
                        // #8707: Batch collect multi-var expression splits rather than
                        // returning immediately. For problems like 8-queens with
                        // `(distinct (+ q0 0) (+ q1 1) ...)` that expand to 28 pairwise
                        // multi-var disequalities, returning after the first violation
                        // causes 28 solver restarts — one per split. Batching lets the
                        // DPLL(T) split loop encode all violated splits in a single
                        // iteration.
                        if debug {
                            safe_eprintln!(
                                "[LRA] Multi-var disequality {:?} violated - buffering expression split",
                                term
                            );
                        }
                        // Keep dirty so next check() re-evaluates disequalities (#5511).
                        self.dirty = true;
                        self.last_diseq_check_had_violation = true;
                        self.pending_expr_splits.push(ExpressionSplitRequest {
                            disequality_term: *term,
                        });
                        // Continue to check remaining disequalities (#8707).
                        continue;
                    }

                    // Fallback for complex expressions where no variable has slack: return Unknown
                    if debug {
                        safe_eprintln!(
                            "[LRA] Disequality {:?} is VIOLATED but no splittable var found - returning Unknown",
                            term
                        );
                    }
                    // Keep dirty so next check() re-evaluates disequalities (#5511).
                    self.dirty = true;
                    return Some(TheoryResult::Unknown);
                }
            }
        }
        if self.pending_diseq_splits.is_empty()
            && self.pending_expr_splits.is_empty()
            && !free_var_pair_repairs.is_empty()
            && self.try_repair_free_var_pair_disequalities(&free_var_pair_repairs, disequalities)
        {
            if debug {
                safe_eprintln!(
                        "[LRA] Repaired {} free integer pair disequalities by assigning distinct model values",
                        free_var_pair_repairs.len()
                    );
            }
            self.last_diseq_check_had_violation = false;
            return None;
        }
        for (term, _, _) in free_var_pair_repairs {
            self.pending_expr_splits.push(ExpressionSplitRequest {
                disequality_term: term,
            });
        }
        // After scanning all disequalities, return the first batched split (#6259).
        // Remaining splits are available via drain_pending_diseq_splits().
        if !self.pending_diseq_splits.is_empty() {
            let first = self.pending_diseq_splits.remove(0);
            if debug {
                safe_eprintln!(
                    "[LRA] Returning first of {} batched diseq splits (var {:?} != {})",
                    self.pending_diseq_splits.len() + 1,
                    first.variable,
                    first.excluded_value,
                );
            }
            self.dirty = true;
            self.last_diseq_check_had_violation = true;
            return Some(TheoryResult::NeedDisequalitySplit(first));
        }
        // #8707: Return batched expression splits, if any. If there are
        // multiple violated multi-var disequalities, return them as
        // `NeedExpressionSplits` so the DPLL(T) split loop can encode all of
        // them in a single iteration (avoids O(N) SAT restarts for the
        // 28 pairwise disequalities produced by a single `(distinct ...)`).
        if !self.pending_expr_splits.is_empty() {
            let splits = std::mem::take(&mut self.pending_expr_splits);
            if debug {
                safe_eprintln!("[LRA] Returning {} batched expr splits", splits.len(),);
            }
            self.dirty = true;
            self.last_diseq_check_had_violation = true;
            if splits.len() == 1 {
                let mut iter = splits.into_iter();
                return Some(TheoryResult::NeedExpressionSplit(iter.next().unwrap()));
            }
            return Some(TheoryResult::NeedExpressionSplits(splits));
        }
        if debug {
            safe_eprintln!("[LRA] All disequalities satisfied");
        }
        None
    }

    fn free_int_var_pair_disequality_candidate(&self, expr: &LinearExpr) -> Option<(u32, u32)> {
        if !expr.constant.is_zero() || expr.coeffs.len() != 2 {
            return None;
        }
        let (lhs_var, lhs_coeff) = &expr.coeffs[0];
        let (rhs_var, rhs_coeff) = &expr.coeffs[1];
        let is_unit_difference = (lhs_coeff.is_one() && rhs_coeff.is_neg_one())
            || (lhs_coeff.is_neg_one() && rhs_coeff.is_one());
        if !is_unit_difference {
            return None;
        }
        if !self.is_free_integer_model_repair_var(*lhs_var)
            || !self.is_free_integer_model_repair_var(*rhs_var)
        {
            return None;
        }
        Some(if lhs_var < rhs_var {
            (*lhs_var, *rhs_var)
        } else {
            (*rhs_var, *lhs_var)
        })
    }

    fn is_free_integer_model_repair_var(&self, var: u32) -> bool {
        if !self.integer_mode {
            return false;
        }
        let Some(info) = self.vars.get(var as usize) else {
            return false;
        };
        if info.lower.is_some() || info.upper.is_some() {
            return false;
        }
        if matches!(info.status, Some(VarStatus::Basic(_))) {
            return false;
        }
        if self.var_occurs_in_tableau_row(var) {
            return false;
        }
        let Some(&term) = self.var_to_term.get(&var) else {
            return false;
        };
        self.terms().sort(term) == &Sort::Int
    }

    fn var_occurs_in_tableau_row(&self, var: u32) -> bool {
        self.rows
            .iter()
            .any(|row| row.basic_var == var || row.coeffs.iter().any(|&(v, _)| v == var))
    }

    fn try_repair_free_var_pair_disequalities(
        &mut self,
        repairs: &[(TermId, u32, u32)],
        disequalities: &[(TermId, LinearExpr, bool)],
    ) -> bool {
        let mut vars: Vec<u32> = Vec::with_capacity(repairs.len() * 2);
        for &(_, lhs, rhs) in repairs {
            vars.push(lhs);
            vars.push(rhs);
        }
        vars.sort_unstable();
        vars.dedup();

        let mut old_values = Vec::with_capacity(vars.len());
        for &var in &vars {
            let Some(info) = self.vars.get(var as usize) else {
                return false;
            };
            old_values.push((var, info.value.clone()));
        }

        // #inc-guard-memo: value perturbation (and its rollback below) mutates
        // variable values — memo invalid and tracked-only chain broken
        // (#inc-guard-chain).
        self.guard_clean_valid = false;
        self.guard_tracked_only = false;
        // #warm-simplex: untracked value writes (and rollback below).
        self.warm_invalidate();
        for (idx, &var) in vars.iter().enumerate() {
            if let Some(info) = self.vars.get_mut(var as usize) {
                info.value = InfRational::from_rat(Rational::from(idx as i64));
            }
        }

        if self.all_disequalities_satisfied_by_current_model(disequalities) {
            true
        } else {
            for (var, value) in old_values {
                if let Some(info) = self.vars.get_mut(var as usize) {
                    info.value = value;
                }
            }
            false
        }
    }

    fn all_disequalities_satisfied_by_current_model(
        &self,
        disequalities: &[(TermId, LinearExpr, bool)],
    ) -> bool {
        disequalities.iter().all(|(_, expr, _)| {
            let mut eval_inf = InfRational::from_rat(expr.constant.clone());
            for &(var, ref coeff) in &expr.coeffs {
                let Some(info) = self.vars.get(var as usize) else {
                    return false;
                };
                eval_inf += &info.value.mul_rat(coeff);
            }
            !eval_inf.is_zero()
        })
    }

    /// Check shared disequalities from Nelson-Oppen.
    pub(crate) fn check_shared_disequalities(&mut self, debug: bool) -> Option<TheoryResult> {
        for (lhs, rhs, expr, reasons, eq_term) in &self.shared_disequality_trail {
            let mut eval_inf = InfRational::from_rat(expr.constant.clone());
            for &(var, ref coeff) in &expr.coeffs {
                if let Some(info) = self.vars.get(var as usize) {
                    let scaled = info.value.mul_rat(coeff);
                    eval_inf += &scaled;
                }
            }

            if debug {
                safe_eprintln!(
                    "[LRA] Checking shared disequality: expr value = {} (inf: {:?}, {} reasons)",
                    eval_inf.rational(),
                    eval_inf,
                    reasons.len()
                );
            }

            if eval_inf.is_zero() {
                // Shared disequality violated: model satisfies lhs = rhs but
                // the other theory asserted lhs != rhs.

                // Check if expression is forced to zero.
                if let Some((equality_reasons, is_forced)) =
                    self.is_expression_forced_to_value(expr, &BigRational::zero())
                {
                    if is_forced {
                        if debug {
                            safe_eprintln!(
                                "[LRA] Shared disequality VIOLATED (forced to 0) - returning Unsat"
                            );
                        }
                        let mut conflict: Vec<TheoryLit> = reasons.clone();
                        conflict.extend(equality_reasons);
                        self.stats.conflict_count += 1;
                        // #8762: Mirror the fix in check_disequalities —
                        // mark violation so the next LRA check() re-evaluates
                        // shared disequalities even when bounds haven't
                        // tightened.
                        self.last_diseq_check_had_violation = true;
                        self.dirty = true;
                        return Some(TheoryResult::Unsat(conflict));
                    }
                }

                // Check if all variables are pinned.
                let all_vars_pinned = expr.coeffs.iter().all(|&(var, _)| {
                    self.vars.get(var as usize).is_some_and(|info| {
                        info.lower
                            .as_ref()
                            .is_some_and(|lb| lb.value == info.value.rational())
                            && info
                                .upper
                                .as_ref()
                                .is_some_and(|ub| ub.value == info.value.rational())
                    })
                });

                if all_vars_pinned || expr.coeffs.is_empty() {
                    if debug {
                        safe_eprintln!(
                            "[LRA] Shared disequality VIOLATED with pinned vars - returning Unsat"
                        );
                    }
                    let mut conflict: Vec<TheoryLit> = reasons.clone();
                    let mut seen: HashSet<TheoryLit> = conflict.iter().copied().collect();
                    // Use HashSet for O(1) dedup instead of Vec::contains() (#938).
                    for &(var, _) in &expr.coeffs {
                        if let Some(info) = self.vars.get(var as usize) {
                            if let Some(ref lb) = info.lower {
                                for (term, val) in lb.reason_pairs() {
                                    if !term.is_sentinel() {
                                        let lit = TheoryLit::new(term, val);
                                        if seen.insert(lit) {
                                            conflict.push(lit);
                                        }
                                    }
                                }
                            }
                            if let Some(ref ub) = info.upper {
                                for (term, val) in ub.reason_pairs() {
                                    if !term.is_sentinel() {
                                        let lit = TheoryLit::new(term, val);
                                        if seen.insert(lit) {
                                            conflict.push(lit);
                                        }
                                    }
                                }
                            }
                        }
                    }
                    self.stats.conflict_count += 1;
                    // #8762: Mirror the fix above — mark violation so the next
                    // LRA check() re-evaluates shared disequalities even when
                    // bounds haven't tightened.
                    self.last_diseq_check_had_violation = true;
                    self.dirty = true;
                    return Some(TheoryResult::Unsat(conflict));
                }

                // Variables have slack — request a split.
                if expr.coeffs.len() == 1 && eq_term.is_some() {
                    let (var, coeff) = &expr.coeffs[0];
                    if let Some(&var_term) = self.var_to_term.get(var) {
                        // For expr = coeff*x + const = 0, excluded value is -const/coeff.
                        // Previously used -const (ignoring coeff), same bug as #6155.
                        let excluded = (-expr.constant.clone() / coeff.clone()).to_big();
                        if debug {
                            safe_eprintln!(
                                "[LRA] Shared disequality violated with slack - split on {:?} != {}",
                                var_term,
                                excluded
                            );
                        }
                        self.dirty = true;
                        self.last_diseq_check_had_violation = true;
                        // #6131: Pass the original equality term so the DPLL(T)
                        // layer creates a conditional split clause:
                        //   `term OR (x < c) OR (x > c)`
                        // Without this, the split is unconditional and survives
                        // backtracking, potentially causing false UNSAT.
                        return Some(TheoryResult::NeedDisequalitySplit(
                            DisequalitySplitRequest {
                                variable: var_term,
                                excluded_value: excluded,
                                disequality_term: *eq_term,
                                is_distinct: false,
                            },
                        ));
                    }
                }
                // Multi-variable shared disequality: use expression split
                // (same as regular disequality handler).
                // Without this, multi-var shared disequalities like f(x) - f(y) != 0
                // fall through to Unknown, causing completeness failures (#6148).
                if let Some(diseq_term) = eq_term {
                    if debug {
                        safe_eprintln!(
                            "[LRA] Multi-var shared disequality violated - requesting expression split"
                        );
                    }
                    self.dirty = true;
                    self.last_diseq_check_had_violation = true;
                    return Some(TheoryResult::NeedExpressionSplit(ExpressionSplitRequest {
                        disequality_term: *diseq_term,
                    }));
                }
                // #8747: No eq_term and multi-variable expression. If all but
                // one variable is pinned, we can reduce to the single-var case:
                // solve for the unpinned variable's excluded value and request
                // an unconditional disequality split. Without this, multi-var
                // shared disequalities propagated through Nelson-Oppen with
                // only positive bound-literal reasons (e.g. to_real in QF_LIRA
                // Big-M ReLU encodings) return Unknown, causing false
                // `unknown (:reason-unknown incomplete)` on satisfiable
                // instances. The split is unconditional (no guard literal)
                // because no equality atom justifies the disequality, but
                // this matches the legacy single-var eq_term=None behavior.
                let mut unpinned: Option<(u32, BigRational)> = None;
                let mut pinned_contrib: BigRational = expr.constant.to_big();
                let mut all_but_one_pinned = true;
                if debug {
                    safe_eprintln!(
                        "[LRA] shared diseq expr: constant={}, coeffs={:?}",
                        expr.constant,
                        expr.coeffs
                    );
                }
                for &(var, ref coeff) in &expr.coeffs {
                    let info = match self.vars.get(var as usize) {
                        Some(info) => info,
                        None => {
                            all_but_one_pinned = false;
                            break;
                        }
                    };
                    let is_pinned = info
                        .lower
                        .as_ref()
                        .is_some_and(|lb| lb.value == info.value.rational() && !lb.strict)
                        && info
                            .upper
                            .as_ref()
                            .is_some_and(|ub| ub.value == info.value.rational() && !ub.strict);
                    if debug {
                        safe_eprintln!(
                            "[LRA]   var={} coeff={} value={} pinned={} lb={:?} ub={:?}",
                            var,
                            coeff,
                            info.value.rational(),
                            is_pinned,
                            info.lower.as_ref().map(|b| (b.value.clone(), b.strict)),
                            info.upper.as_ref().map(|b| (b.value.clone(), b.strict)),
                        );
                    }
                    if is_pinned {
                        pinned_contrib += info.value.rational() * coeff.to_big();
                    } else if unpinned.is_none() {
                        unpinned = Some((var, coeff.to_big()));
                    } else {
                        all_but_one_pinned = false;
                        break;
                    }
                }
                if all_but_one_pinned && expr.coeffs.len() > 1 && eq_term.is_some() {
                    if let Some((var, coeff)) = unpinned {
                        if let Some(&var_term) = self.var_to_term.get(&var) {
                            if !Zero::is_zero(&coeff) {
                                // coeff * var + pinned_contrib = 0  =>  var = -pinned_contrib / coeff
                                let excluded: BigRational = -pinned_contrib / coeff;
                                if debug {
                                    safe_eprintln!(
                                        "[LRA] Shared disequality violated (all-but-one pinned) - split on {:?} != {}",
                                        var_term,
                                        excluded
                                    );
                                }
                                self.dirty = true;
                                self.last_diseq_check_had_violation = true;
                                return Some(TheoryResult::NeedDisequalitySplit(
                                    DisequalitySplitRequest {
                                        variable: var_term,
                                        excluded_value: excluded,
                                        disequality_term: None,
                                        is_distinct: false,
                                    },
                                ));
                            }
                        }
                    }
                }
                // No equality atom is available to guard an expression split.
                // Fall back to requesting a model equality so the DPLL(T) layer
                // can create `(= lhs rhs)` and branch on it explicitly.
                if debug {
                    safe_eprintln!(
                        "[LRA] Shared disequality violated - no eq_term for split, requesting model equality"
                    );
                }
                self.dirty = true;
                self.last_diseq_check_had_violation = true;
                return Some(TheoryResult::NeedModelEquality(ModelEqualityRequest {
                    lhs: *lhs,
                    rhs: *rhs,
                    reason: reasons.clone(),
                    implied: false,
                }));
            }
        }
        if debug {
            safe_eprintln!("[LRA] All shared disequalities satisfied");
        }
        None
    }
}

impl LraSolver {
    /// A5 core: materialize every deferred equality whose expression is
    /// VIOLATED (nonzero) under the current simplex assignment, returning how
    /// many were materialized. The caller re-runs the simplex and loops to a
    /// fixpoint. Satisfied deferrals stay row-free (the demand principle:
    /// z3's lar_solver materializes only rows the solve actually needs).
    pub(crate) fn materialize_violated_deferred_eqs(&mut self) -> usize {
        if !self.a5_core || self.deferred_eq_atoms.is_empty() {
            return 0;
        }
        let deferred = std::mem::take(&mut self.deferred_eq_atoms);
        use num_traits::Zero;
        let mut materialized = 0usize;
        let zero = Rational::zero();
        for (term, expr, value) in deferred {
            // Still asserted with the same polarity?
            if self.asserted.get(&term) != Some(&value) {
                continue; // popped/flipped: drop
            }
            let mut eval_inf = InfRational::from_rat(expr.constant.clone());
            for &(var, ref coeff) in &expr.coeffs {
                if let Some(info) = self.vars.get(var as usize) {
                    let scaled = info.value.mul_rat(coeff);
                    eval_inf += &scaled;
                }
            }
            let val = eval_inf.rational();
            if val.is_zero() {
                // Satisfied without a row: keep deferred.
                self.deferred_eq_atoms.push((term, expr, value));
                continue;
            }
            self.assert_bound_for_atom(
                expr.clone(),
                zero.clone(),
                BoundType::Upper,
                false,
                term,
                value,
                (term, value),
            );
            self.assert_bound_for_atom(
                expr,
                zero.clone(),
                BoundType::Lower,
                false,
                term,
                value,
                (term, value),
            );
            materialized += 1;
        }
        materialized
    }
}
