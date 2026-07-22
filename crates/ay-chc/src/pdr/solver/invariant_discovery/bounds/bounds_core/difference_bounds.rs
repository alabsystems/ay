// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Difference-bound template synthesis from transition step constants.
//!
//! For self-loop transitions with a "stepped" variable (a' = a + c) and an
//! "unchanged" variable (b' = b), this generates candidate invariants of the
//! form `a < b + c` (and the symmetric `b < a + c`).
//!
//! Motivation: benchmarks like s_multipl_11 have LOOPY with A'=A+1000, B'=B.
//! The needed invariant `A < B + 1000` is a difference bound derived from the
//! step constant. It is both entry-inductive and self-inductive, but PDR does
//! not discover it through its standard bound/equality/sum passes.
//!
//! Reference: Miné 2001 (ESOP), difference-bound domain in abstract interp.
//! Also related to Z3 Spacer's `propagate_clause_guided()`.

use super::*;

impl PdrSolver {
    /// Discover difference-bound invariants from self-loop transition step constants.
    ///
    /// For each predicate P with a self-loop clause of the form:
    ///   P(x0, x1, ...) ∧ constraint => P(x0', x1', ...)
    /// where x_i' = x_i + c_i (stepped) and x_j' = x_j (unchanged),
    /// generate candidates:
    ///   canonical[i] < canonical[j] + c_i
    ///   canonical[j] < canonical[i] + c_i  (symmetric)
    ///
    /// These are tested for entry-inductiveness and self-inductiveness via
    /// `add_discovered_invariant`.
    pub(in crate::pdr::solver) fn discover_step_difference_bound_invariants(&mut self) {
        let pred_ids: Vec<PredicateId> = self.problem.predicates().iter().map(|p| p.id).collect();

        if self.config.verbose {
            safe_eprintln!(
                "PDR: discover_step_difference_bounds: starting for {} predicates",
                pred_ids.len()
            );
        }

        for pred_id in pred_ids {
            let canonical_vars = match self.canonical_vars(pred_id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Only process Int-sorted variables.
            let int_indices: Vec<usize> = canonical_vars
                .iter()
                .enumerate()
                .filter(|(_, v)| matches!(v.sort, ChcSort::Int))
                .map(|(i, _)| i)
                .collect();
            if int_indices.len() < 2 {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: discover_step_difference_bounds: pred {} has {} int vars (need >=2), skipping",
                        pred_id.index(), int_indices.len()
                    );
                }
                continue;
            }

            // Collect self-loop clause data to avoid borrow conflicts.
            // For each self-loop: (step_info, constraint)
            // step_info[var_idx] = Some(step_constant) for stepped, None for non-stepped
            // unchanged[var_idx] = true if variable is preserved
            let clause_data: Vec<(Vec<Option<i128>>, Vec<bool>)> = self
                .problem
                .clauses_defining(pred_id)
                .filter_map(|clause| {
                    // Must be a self-loop: exactly one body predicate == pred_id
                    if clause.body.predicates.len() != 1 {
                        return None;
                    }
                    let (body_pred, body_args) = &clause.body.predicates[0];
                    if *body_pred != pred_id {
                        return None;
                    }
                    let head_args = match &clause.head {
                        crate::ClauseHead::Predicate(_, a) => a,
                        crate::ClauseHead::False => return None,
                    };
                    if body_args.len() != canonical_vars.len()
                        || head_args.len() != canonical_vars.len()
                    {
                        return None;
                    }

                    let constraint = clause.body.constraint.as_ref();

                    let mut steps = vec![None; canonical_vars.len()];
                    let mut unchanged = vec![false; canonical_vars.len()];

                    for &idx in &int_indices {
                        let body_expr = &body_args[idx];
                        let head_expr = &head_args[idx];

                        // Try direct pattern: head = body + c
                        if let Some(c) = Self::extract_simple_offset(body_expr, head_expr) {
                            if c != 0 {
                                steps[idx] = Some(c);
                            } else {
                                unchanged[idx] = true;
                            }
                            continue;
                        }

                        // Try indirect: body = Var(bv), head = Var(hv),
                        // constraint has hv = bv + c
                        if let (ChcExpr::Var(bv), ChcExpr::Var(hv)) = (body_expr, head_expr) {
                            if bv.name == hv.name {
                                // Same variable name => unchanged
                                unchanged[idx] = true;
                                continue;
                            }
                            if let Some(constraint_expr) = constraint {
                                // Look for hv = bv + c in constraint
                                if let Some(rhs) =
                                    Self::find_equality_rhs(constraint_expr, &hv.name)
                                {
                                    if let Some(c) = Self::extract_addition_offset(&rhs, &bv.name) {
                                        if c != 0 {
                                            steps[idx] = Some(c);
                                        } else {
                                            unchanged[idx] = true;
                                        }
                                        continue;
                                    }
                                    // Check if rhs is just the body var (unchanged via equality)
                                    if Self::is_var_expr(&rhs, &bv.name) {
                                        unchanged[idx] = true;
                                        continue;
                                    }
                                }
                                // Try the other direction: bv = hv + c (i.e., hv = bv - c)
                                if let Some(rhs) =
                                    Self::find_equality_rhs(constraint_expr, &bv.name)
                                {
                                    if let Some(c) = Self::extract_addition_offset(&rhs, &hv.name) {
                                        // bv = hv + c => hv = bv - c => step = -c
                                        if c != 0 {
                                            steps[idx] = Some(-c);
                                        } else {
                                            unchanged[idx] = true;
                                        }
                                        continue;
                                    }
                                    if Self::is_var_expr(&rhs, &hv.name) {
                                        unchanged[idx] = true;
                                        continue;
                                    }
                                }
                            }
                        }
                    }

                    Some((steps, unchanged))
                })
                .collect();

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_step_difference_bounds: pred {} has {} self-loop clause(s)",
                    pred_id.index(),
                    clause_data.len()
                );
                for (i, (steps, unchanged)) in clause_data.iter().enumerate() {
                    safe_eprintln!(
                        "PDR:   clause {}: steps={:?}, unchanged={:?}",
                        i,
                        steps,
                        unchanged
                    );
                }
            }

            if clause_data.is_empty() {
                continue;
            }

            // Generate difference-bound candidates from each self-loop clause.
            let mut candidates: Vec<ChcExpr> = Vec::new();

            for (steps, unchanged) in &clause_data {
                for &i in &int_indices {
                    let Some(c) = steps[i] else { continue };
                    // i is a stepped variable with step c
                    let abs_c_u128 = c.unsigned_abs();
                    if abs_c_u128 > 1_000_000 {
                        // Skip unreasonably large steps
                        continue;
                    }
                    let abs_c = abs_c_u128 as i128; // safe: checked <= 1_000_000

                    for &j in &int_indices {
                        if j == i {
                            continue;
                        }
                        if !unchanged[j] {
                            continue;
                        }
                        // j is unchanged. Generate both directions and let
                        // add_discovered_invariant check entry-inductiveness and
                        // self-inductiveness via SMT. Invalid candidates are rejected.

                        // Candidate 1: canonical[i] < canonical[j] + |c|
                        let cand1 = ChcExpr::lt(
                            ChcExpr::var(canonical_vars[i].clone()),
                            ChcExpr::add(
                                ChcExpr::var(canonical_vars[j].clone()),
                                ChcExpr::Int(abs_c),
                            ),
                        );
                        if !candidates.contains(&cand1) {
                            candidates.push(cand1);
                        }

                        // Candidate 2: canonical[j] < canonical[i] + |c|
                        let cand2 = ChcExpr::lt(
                            ChcExpr::var(canonical_vars[j].clone()),
                            ChcExpr::add(
                                ChcExpr::var(canonical_vars[i].clone()),
                                ChcExpr::Int(abs_c),
                            ),
                        );
                        if !candidates.contains(&cand2) {
                            candidates.push(cand2);
                        }

                        // Also try <= variants (sometimes tighter)
                        // canonical[i] <= canonical[j] + |c| - 1
                        if abs_c > 1 {
                            let cand3 = ChcExpr::le(
                                ChcExpr::var(canonical_vars[i].clone()),
                                ChcExpr::add(
                                    ChcExpr::var(canonical_vars[j].clone()),
                                    ChcExpr::Int(abs_c - 1),
                                ),
                            );
                            if !candidates.contains(&cand3) {
                                candidates.push(cand3);
                            }
                        }

                        // Guard-bounded slack (#4751): loops guarded by a
                        // NON-strict comparison (i <= j) that step i by c can
                        // overshoot j by up to |c|, so the inductive bound is
                        // `i <= j + |c|` — one looser than cand1/cand3 which
                        // only cover strict guards. dillig12_m's SAD predicate
                        // (guard A <= B, step +2) needs exactly A <= B + 2.
                        // Admission still SMT-checks entry- and
                        // self-inductiveness, so the extra candidate is sound.
                        let cand4 = ChcExpr::le(
                            ChcExpr::var(canonical_vars[i].clone()),
                            ChcExpr::add(
                                ChcExpr::var(canonical_vars[j].clone()),
                                ChcExpr::Int(abs_c),
                            ),
                        );
                        if !candidates.contains(&cand4) {
                            candidates.push(cand4);
                        }
                    }
                }
            }

            if candidates.is_empty() {
                continue;
            }

            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_step_difference_bounds: pred {} generated {} candidates",
                    pred_id.index(),
                    candidates.len()
                );
            }

            let mut added = 0;
            for candidate in candidates {
                if self.add_discovered_invariant(pred_id, candidate, 1) {
                    added += 1;
                }
            }

            if self.config.verbose && added > 0 {
                safe_eprintln!(
                    "PDR: discover_step_difference_bounds: pred {} added {} invariants",
                    pred_id.index(),
                    added
                );
            }
        }
    }
}
