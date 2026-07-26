// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bound assertion, slack variable management, and compound atom propagation.
//!
//! Complements `atom_parsing` (variable interning and expression parsing) with:
//! - Bound assertion with atom-level slack caching
//! - Slack variable creation and tableau row setup
//! - Compound atom propagation via direct bounds, implied bounds, and intervals

use super::*;

impl LraSolver {
    /// Assert a bound on a linear expression
    /// For expr <= c: create slack variable s, add row s = expr, then s <= c
    ///
    /// #8406: Takes `Rational` instead of `BigRational` to avoid heap allocation
    /// in the common case where bounds are small integers (0, 1, -1).
    pub(crate) fn assert_bound(
        &mut self,
        expr: LinearExpr,
        bound: Rational,
        bound_type: BoundType,
        strict: bool,
        reason: TermId,
        reason_value: bool,
    ) {
        let single_reason = [(reason, reason_value)];
        self.assert_bound_with_reasons(expr, bound, bound_type, strict, &single_reason, None);
    }

    /// Assert a bound with atom-level slack variable caching.
    ///
    /// When an atom is re-asserted after push/pop, the slack variable from the
    /// previous assertion is reused. This prevents the tableau from growing
    /// unboundedly across DPLL(T) backtracking cycles (#4919).
    ///
    /// #8406: Takes `Rational` instead of `BigRational`.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn assert_bound_for_atom(
        &mut self,
        expr: LinearExpr,
        bound: Rational,
        bound_type: BoundType,
        strict: bool,
        reason: TermId,
        reason_value: bool,
        atom_key: (TermId, bool),
    ) {
        let single_reason = [(reason, reason_value)];
        self.assert_bound_with_reasons(
            expr,
            bound,
            bound_type,
            strict,
            &single_reason,
            Some(atom_key),
        );
    }

    /// Get or create a slack variable for a multi-variable linear expression.
    ///
    /// If a slack already exists for this expression (via `expr_to_slack`), returns it.
    /// Otherwise creates a new slack variable, adds a tableau row `slack = expr`,
    /// sets the initial value, and registers the row for implied-bound analysis.
    ///
    /// This is the core mechanism for atom normalization (#4919): by creating slack
    /// variables at registration time, compound atoms like `x + y - z <= 5` become
    /// single-variable atoms `s <= 5` that participate in same-variable chain
    /// propagation via `atom_index`.
    /// Returns (slack_var, original_constant) — the original constant is needed so callers
    /// can adjust bounds when the reused slack was created with a different constant offset (#6193).
    pub(crate) fn get_or_create_slack(&mut self, expr: &LinearExpr) -> (u32, Rational) {
        // Normalize key: sorted coefficients (without constant — the constant is
        // part of the slack definition, not the key).
        let mut key: Vec<(u32, Rational)> =
            expr.coeffs.iter().map(|(v, c)| (*v, c.clone())).collect();
        key.sort_by_key(|(v, _)| *v);

        if let Some(&(existing, ref orig_constant)) = self.expr_to_slack.get(&key) {
            return (existing, orig_constant.clone());
        }

        let new_slack = self.next_var;
        self.next_var += 1;
        while self.vars.len() <= new_slack as usize {
            self.vars.push(VarInfo::default());
        }

        let row_idx = self.rows.len();
        self.vars[new_slack as usize].status = Some(VarStatus::Basic(row_idx));

        // Substitute any basic variables with their row equations so that
        // row coefficients only reference non-basic variables (#4842).
        let mut new_coeffs: Vec<(u32, Rational)> = Vec::new();
        let mut new_constant = expr.constant.clone();
        for &(v, ref c) in &expr.coeffs {
            if let Some(VarStatus::Basic(basic_row_idx)) =
                self.vars.get(v as usize).and_then(|info| info.status)
            {
                let basic_row = &self.rows[basic_row_idx];
                for &(rv, ref rc) in &basic_row.coeffs {
                    types::add_sparse_term_rat(&mut new_coeffs, rv, c * rc);
                }
                new_constant = &new_constant + &(c * &basic_row.constant);
            } else {
                types::add_sparse_term_rat(&mut new_coeffs, v, c.clone());
            }
        }

        let row = TableauRow::new_rat(new_slack, new_coeffs, new_constant);
        // #8003: Track max row width for dense LP detection.
        let row_width = row.coeffs.len();
        self.rows.push(row);
        if row_width > self.max_row_width {
            self.max_row_width = row_width;
        }
        self.heap_stale = true; // #8782: new row → full heap rebuild needed
                                // #warm-simplex: a new row creates a basic var (and may flip
                                // status-None vars to NonBasic) outside the tracked chokepoints, and
                                // breaks the last-feasible delta's row-consistency (the anchor
                                // assignment predates this row). Invalidate all warm tracking; the
                                // next full simplex scan re-arms it.
        self.warm_invalidate();

        let new_row_ref = &self.rows[row_idx];
        for (pos, &(v, _)) in new_row_ref.coeffs.iter().enumerate() {
            let vi = v as usize;
            if vi >= self.col_index.len() {
                self.col_index.resize(vi + 1, Vec::new());
            }
            self.col_index[vi].push(ColEntry::new(row_idx, pos));
        }
        self.basic_var_to_row.insert(new_slack, row_idx);
        self.touched_rows.insert(row_idx);

        // Set initial value for slack based on current variable values.
        let mut slack_val = InfRational::from_rat(expr.constant.clone());
        for &(v, ref c) in &expr.coeffs {
            if let Some(info) = self.vars.get(v as usize) {
                slack_val += &info.value.mul_rat(c);
            }
        }
        self.vars[new_slack as usize].value = slack_val;

        // Mark non-basic variables used in this row.
        let row_ref = &self.rows[row_idx];
        let row_vars: Vec<u32> = row_ref.coeffs.iter().map(|(v, _)| *v).collect();
        for v in row_vars {
            if let Some(info) = self.vars.get_mut(v as usize) {
                if info.status.is_none() {
                    info.status = Some(VarStatus::NonBasic);
                }
            }
        }

        self.slack_var_set.insert(new_slack);
        let orig_constant = expr.constant.clone();
        self.expr_to_slack
            .insert(key, (new_slack, Rational::from(&orig_constant)));
        (new_slack, orig_constant)
    }

    /// Z3-style sub-expression term row internalization (#8008).
    ///
    /// For a comparison atom `(op lhs rhs)`, Z3 creates theory variables for
    /// sub-expressions via `internalize_def` (theory_lra.cpp:937-949) and
    /// recursive `linearize` (theory_lra.cpp:355-553). Each compound sub-expression
    /// in the term tree gets its own simplex row `v = linearize(sub_expr)`.
    ///
    /// AY's default approach flattens the entire `lhs - rhs` into a single
    /// coefficient vector, losing intermediate sub-expression variables. This method
    /// restores the Z3 behavior by recursively walking the term tree and creating
    /// term rows for every compound arithmetic sub-expression.
    ///
    /// This increases the number of simplex rows (Z3: 526, AY before: 193 on
    /// simple_startup_6nodes) and creates more implied-bound propagation targets.
    pub(crate) fn internalize_atom_sub_terms(&mut self, atom: TermId) {
        // Extract the LHS and RHS from the original term structure.
        let (lhs, rhs) = {
            let td = self.terms().get(atom);
            match td {
                TermData::App(Symbol::Named(_), args) if args.len() == 2 => (args[0], args[1]),
                _ => return,
            }
        };

        // Recursively internalize sub-expression terms for both sides.
        if self.debug_lra {
            safe_eprintln!(
                "[LRA] internalize_atom_sub_terms: atom={:?}, lhs={:?}, rhs={:?}",
                atom,
                lhs,
                rhs
            );
        }
        self.internalize_term_recursive(lhs);
        self.internalize_term_recursive(rhs);
    }

    /// Recursively walk an arithmetic term tree and create simplex rows for
    /// every compound sub-expression (Z3's `internalize_term` + `linearize`).
    ///
    /// For `(+ (+ a b) (* 2 c))`, this creates term rows for:
    /// - `(+ a b)` => `s1 = a + b`
    /// - The top-level `(+ (+ a b) (* 2 c))` => `s2 = a + b + 2*c`
    ///   (but this is handled by the caller via get_or_create_slack for the atom)
    ///
    /// The recursion stops at leaf variables, constants, and single-variable terms.
    fn internalize_term_recursive(&mut self, term: TermId) {
        // Collect sub-terms to process. We use a worklist to avoid deep recursion
        // on large expression trees.
        let mut worklist: Vec<TermId> = vec![term];
        let mut visited: HashSet<TermId> = HashSet::default();

        while let Some(current) = worklist.pop() {
            if !visited.insert(current) {
                continue;
            }

            // Parse the current term as a linear expression. If compound, create
            // a term row. Then descend into its sub-terms.
            let sub_expr = self.parse_linear_expr(current);
            if sub_expr.coeffs.len() > 1 {
                let (slack, _) = self.get_or_create_slack(&sub_expr);
                if self.debug_lra {
                    safe_eprintln!(
                        "[LRA] internalize_term_recursive: created term row for {:?} -> slack {}, coeffs={}",
                        current, slack, sub_expr.coeffs.len()
                    );
                }
                for &(v, _) in &sub_expr.coeffs {
                    self.propagation_dirty_vars.insert(v);
                }
                self.propagation_dirty_vars.insert(slack);
            }

            // Descend into arithmetic sub-terms. We need to re-read the term
            // since parse_linear_expr consumed the borrow.
            let children: SmallVec<[TermId; 4]> = {
                let td = self.terms().get(current);
                match td {
                    TermData::App(Symbol::Named(name), args) => match name.as_str() {
                        "+" | "-" | "*" => args.iter().copied().collect(),
                        _ => SmallVec::new(),
                    },
                    _ => SmallVec::new(),
                }
            };
            for child in children {
                worklist.push(child);
            }
        }
    }

    pub(crate) fn compound_atom_ref(&self, compound: CompoundAtomRef) -> Option<AtomRef> {
        self.atom_index
            .get(&compound.slack)
            .and_then(|atoms| atoms.iter().find(|atom| atom.term == compound.term))
            .cloned()
    }

    pub(crate) fn queue_compound_propagations_for_dirty_vars(&mut self, dirty: &[u32]) -> usize {
        if dirty.is_empty() || self.compound_use_index.is_empty() {
            self.last_compound_propagations_queued = 0;
            self.last_compound_wake_dirty_hits = 0;
            self.last_compound_wake_candidates = 0;
            return 0;
        }

        let mut seen = HashSet::default();
        let mut queued = 0usize;
        let mut dirty_hits = 0usize;
        let mut candidates = 0usize;
        for &var in dirty {
            let Some(compounds) = self.compound_use_index.get(&var).cloned() else {
                continue;
            };
            dirty_hits += 1;
            for compound in compounds {
                if !seen.insert(compound.term) {
                    continue;
                }
                candidates += 1;
                if self.try_queue_compound_propagation(compound) {
                    queued += 1;
                }
            }
        }
        self.last_compound_propagations_queued = queued;
        self.last_compound_wake_dirty_hits = dirty_hits;
        self.last_compound_wake_candidates = candidates;
        queued
    }

    pub(crate) fn try_queue_compound_propagation(&mut self, compound: CompoundAtomRef) -> bool {
        if self.asserted.contains_key(&compound.term) {
            return false;
        }

        let Some(atom) = self.compound_atom_ref(compound) else {
            return false;
        };
        let slack_vi = compound.slack as usize;
        // Same-expression compound atoms share one slack variable. A stronger
        // asserted slack bound is therefore a sound direct witness for a weaker
        // atom over that same slack, and it must stay available when source-var
        // interval reconstruction comes back empty.

        // #8064: Extract (value, strict, reasons) from direct bounds eagerly.
        // Reasons are collected now to avoid losing propagations when bounds
        // are backtracked between check() and propagate().
        let direct_upper = self
            .vars
            .get(slack_vi)
            .and_then(|info| info.upper.as_ref())
            .map(|bound| {
                let reasons: Vec<TheoryLit> = bound
                    .reason_pairs()
                    .filter(|(term, _)| !term.is_sentinel())
                    .map(|(term, val)| TheoryLit::new(term, val))
                    .collect();
                (bound.value.clone(), bound.strict, reasons)
            });
        let direct_lower = self
            .vars
            .get(slack_vi)
            .and_then(|info| info.lower.as_ref())
            .map(|bound| {
                let reasons: Vec<TheoryLit> = bound
                    .reason_pairs()
                    .filter(|(term, _)| !term.is_sentinel())
                    .map(|(term, val)| TheoryLit::new(term, val))
                    .collect();
                (bound.value.clone(), bound.strict, reasons)
            });
        // #9031: Re-enabled with stale-reason safety filter in propagate_impl().
        let implied_upper: Option<(Rational, bool, usize)> = if slack_vi < self.implied_bounds.len()
        {
            self.implied_bounds[slack_vi]
                .1
                .as_ref()
                .filter(|b| b.row_idx != usize::MAX)
                .map(|b| (b.value.clone(), b.strict, b.row_idx))
        } else {
            None
        };
        let implied_lower: Option<(Rational, bool, usize)> = if slack_vi < self.implied_bounds.len()
        {
            self.implied_bounds[slack_vi]
                .0
                .as_ref()
                .filter(|b| b.row_idx != usize::MAX)
                .map(|b| (b.value.clone(), b.strict, b.row_idx))
        } else {
            None
        };

        // #8064: Check if direct bound implies truth, with eagerly-collected reasons.
        let direct_true_implied = if atom.is_upper {
            direct_upper.as_ref().is_some_and(|(value, strict, _)| {
                if atom.strict {
                    value < &atom.bound_value || (value == &atom.bound_value && *strict)
                } else {
                    value <= &atom.bound_value
                }
            })
        } else {
            direct_lower.as_ref().is_some_and(|(value, strict, _)| {
                if atom.strict {
                    value > &atom.bound_value || (value == &atom.bound_value && *strict)
                } else {
                    value >= &atom.bound_value
                }
            })
        };
        let implied_true_row = if atom.is_upper {
            implied_upper.as_ref().and_then(|(value, strict, row_idx)| {
                let cmp = value.cmp(&atom.bound_value);
                let implied = if atom.strict {
                    cmp == std::cmp::Ordering::Less || (cmp == std::cmp::Ordering::Equal && *strict)
                } else {
                    cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                };
                implied.then_some(*row_idx)
            })
        } else {
            implied_lower.as_ref().and_then(|(value, strict, row_idx)| {
                let cmp = value.cmp(&atom.bound_value);
                let implied = if atom.strict {
                    cmp == std::cmp::Ordering::Greater
                        || (cmp == std::cmp::Ordering::Equal && *strict)
                } else {
                    cmp == std::cmp::Ordering::Greater || cmp == std::cmp::Ordering::Equal
                };
                implied.then_some(*row_idx)
            })
        };

        if !self.propagated_atoms.contains(&(compound.term, true)) {
            // #8467: Check if interval bounds imply TRUE, but defer reason collection.
            let interval_true_implied = if !direct_true_implied && implied_true_row.is_none() {
                match self.atom_cache.get(&compound.term) {
                    Some(Some(info)) => {
                        let expr = info.expr.clone();
                        let (lb, ub) = self.compute_expr_interval(&expr);
                        if info.is_le {
                            ub.as_ref().is_some_and(|ep| {
                                Self::endpoint_implies_le_zero(ep, compound.strict)
                            })
                        } else {
                            lb.as_ref().is_some_and(|ep| {
                                Self::endpoint_implies_ge_zero(ep, compound.strict)
                            })
                        }
                    }
                    _ => false,
                }
            } else {
                false
            };
            // #8467: Dispatch to type-specific deferred reasons so
            // explain_propagation() can use the most precise reconstruction
            // path. DirectBound reasons read var.upper/lower.reason_pairs(),
            // ImpliedBound reasons read implied_bounds[var].explanation, and
            // Interval reasons call collect_interval_reasons(). Routing all
            // compound propagations through the Interval path (old code) caused
            // failures when interval bounds changed but direct bounds were still
            // valid.
            if direct_true_implied {
                Self::note_propagated(
                    &mut self.propagated_atoms,
                    &mut self.propagated_trail,
                    compound.term,
                    true,
                );
                self.pending_propagations.push(PendingPropagation::deferred(
                    TheoryLit::new(compound.term, true),
                    DeferredReason::DirectBound {
                        var: compound.slack,
                        need_upper: atom.is_upper,
                    },
                ));
                return true;
            }
            if implied_true_row.is_some() {
                Self::note_propagated(
                    &mut self.propagated_atoms,
                    &mut self.propagated_trail,
                    compound.term,
                    true,
                );
                self.pending_propagations.push(PendingPropagation::deferred(
                    TheoryLit::new(compound.term, true),
                    DeferredReason::ImpliedBound {
                        var: compound.slack,
                        need_upper: atom.is_upper,
                    },
                ));
                return true;
            }
            if interval_true_implied {
                Self::note_propagated(
                    &mut self.propagated_atoms,
                    &mut self.propagated_trail,
                    compound.term,
                    true,
                );
                self.pending_propagations.push(PendingPropagation::deferred(
                    TheoryLit::new(compound.term, true),
                    DeferredReason::Interval {
                        atom_term: compound.term,
                        for_upper: atom.is_upper,
                    },
                ));
                return true;
            }
        }

        // #8064: Check if direct bound implies falsity, with eagerly-collected reasons.
        let direct_false_implied = if atom.is_upper {
            direct_lower.as_ref().is_some_and(|(value, strict, _)| {
                if atom.strict {
                    value >= &atom.bound_value
                } else {
                    value > &atom.bound_value || (value == &atom.bound_value && *strict)
                }
            })
        } else {
            direct_upper.as_ref().is_some_and(|(value, strict, _)| {
                if atom.strict {
                    value <= &atom.bound_value
                } else {
                    value < &atom.bound_value || (value == &atom.bound_value && *strict)
                }
            })
        };
        let implied_false_row = if atom.is_upper {
            implied_lower.as_ref().and_then(|(value, strict, row_idx)| {
                let cmp = value.cmp(&atom.bound_value);
                let implied = if atom.strict {
                    cmp == std::cmp::Ordering::Greater || cmp == std::cmp::Ordering::Equal
                } else {
                    cmp == std::cmp::Ordering::Greater
                        || (cmp == std::cmp::Ordering::Equal && *strict)
                };
                implied.then_some(*row_idx)
            })
        } else {
            implied_upper.as_ref().and_then(|(value, strict, row_idx)| {
                let cmp = value.cmp(&atom.bound_value);
                let implied = if atom.strict {
                    cmp == std::cmp::Ordering::Less || cmp == std::cmp::Ordering::Equal
                } else {
                    cmp == std::cmp::Ordering::Less || (cmp == std::cmp::Ordering::Equal && *strict)
                };
                implied.then_some(*row_idx)
            })
        };

        if !self.propagated_atoms.contains(&(compound.term, false)) {
            // #8467: Check if interval bounds imply FALSE, but defer reason collection.
            let interval_false_implied = if !direct_false_implied && implied_false_row.is_none() {
                match self.atom_cache.get(&compound.term) {
                    Some(Some(info)) => {
                        let expr = info.expr.clone();
                        let (lb, ub) = self.compute_expr_interval(&expr);
                        if info.is_le {
                            lb.as_ref().is_some_and(|ep| {
                                Self::endpoint_implies_not_le_zero(ep, compound.strict)
                            })
                        } else {
                            ub.as_ref().is_some_and(|ep| {
                                Self::endpoint_implies_not_ge_zero(ep, compound.strict)
                            })
                        }
                    }
                    _ => false,
                }
            } else {
                false
            };
            // #8467: Same type-specific dispatch as the true case above.
            if direct_false_implied {
                Self::note_propagated(
                    &mut self.propagated_atoms,
                    &mut self.propagated_trail,
                    compound.term,
                    false,
                );
                self.pending_propagations.push(PendingPropagation::deferred(
                    TheoryLit::new(compound.term, false),
                    DeferredReason::DirectBound {
                        var: compound.slack,
                        need_upper: !atom.is_upper,
                    },
                ));
                return true;
            }
            if implied_false_row.is_some() {
                Self::note_propagated(
                    &mut self.propagated_atoms,
                    &mut self.propagated_trail,
                    compound.term,
                    false,
                );
                self.pending_propagations.push(PendingPropagation::deferred(
                    TheoryLit::new(compound.term, false),
                    DeferredReason::ImpliedBound {
                        var: compound.slack,
                        need_upper: !atom.is_upper,
                    },
                ));
                return true;
            }
            if interval_false_implied {
                Self::note_propagated(
                    &mut self.propagated_atoms,
                    &mut self.propagated_trail,
                    compound.term,
                    false,
                );
                self.pending_propagations.push(PendingPropagation::deferred(
                    TheoryLit::new(compound.term, false),
                    DeferredReason::Interval {
                        atom_term: compound.term,
                        for_upper: !atom.is_upper,
                    },
                ));
                return true;
            }
        }

        false
    }
}
