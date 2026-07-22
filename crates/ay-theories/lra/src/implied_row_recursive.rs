// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Depth-limited recursive row reason collection for implied bounds.
//!
//! Contains `collect_row_reasons_recursive` (the core recursive walk) and
//! `collect_reasons_from_row_for_basic` (its per-row helper). Called from
//! `collect_row_reasons_dedup` in `implied_row_reasons.rs`.
//!
//! Extracted from implied_row_reasons.rs as part of #5970 code-health splits.
//!
//! #8013: Eliminated HashMap clone/clone_from rollback pattern that consumed
//! ~84% of solve time on Motzkin-style termination template benchmarks.
//! Replaced with stack-based rollback via `visited_added: Vec<(u32, bool)>`.
//! Added total-calls budget (`MAX_RECURSIVE_CALLS = 256`) to cap exponential
//! re-exploration on dense LP instances.

use super::*;

impl LraSolver {
    /// Maximum total recursive calls across the entire reason collection tree.
    /// Prevents exponential blowup on dense LP instances where depth-limiting
    /// alone is insufficient (many rows × many nonbasic vars per row).
    /// 256 is generous for typical instances while capping pathological cases.
    const MAX_RECURSIVE_CALLS: u32 = 256;

    /// Depth-limited recursive row reason collection.
    /// `depth` limits transitive reasoning to avoid worst-case blowup.
    ///
    /// When `var` is the basic variable of a row, collects reasons from the
    /// nonbasic variables' bounds (the standard case).
    ///
    /// When `var` is NOT basic, uses the derivation row stored in `implied_bounds`
    /// (if available) to go directly to the row that derived the bound. Falls back
    /// to searching `col_index` if no stored row exists (#4919).
    ///
    /// Reference: Z3 stores a lazy explanation closure capturing the derivation row
    /// (`reference/z3/src/math/lp/bound_analyzer_on_row.h:298-319`).
    pub(crate) fn collect_row_reasons_recursive(
        &self,
        var: u32,
        need_upper: bool,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
        depth: u32,
    ) -> bool {
        // #8013: Delegate to budgeted version with stack-based visited rollback.
        let mut call_count: u32 = 0;
        let mut visited_added: Vec<(u32, bool)> = Vec::new();
        let mut on_stack: HashSet<(u32, bool)> = HashSet::default();
        self.collect_row_reasons_recursive_inner(
            var,
            need_upper,
            reasons,
            seen,
            visited_vars,
            &mut visited_added,
            &mut on_stack,
            depth,
            &mut call_count,
        )
    }

    /// Inner implementation with stack-based visited_vars rollback and call budget.
    ///
    /// #8013: The original code used `visited_vars.clone()` before the row loop
    /// and `visited_vars.clone_from(&snapshot)` on each row failure. On Motzkin-
    /// style termination template benchmarks (_gj2007, _standard_allDiff2, etc.)
    /// with many narrow rows (width ~5-10), this HashMap clone consumed ~84% of
    /// total solve time. The stack-based rollback records which entries were added
    /// and removes only those on failure, reducing rollback from O(n) clone to
    /// O(added) removal.
    #[allow(clippy::too_many_arguments)]
    fn collect_row_reasons_recursive_inner(
        &self,
        var: u32,
        need_upper: bool,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
        visited_added: &mut Vec<(u32, bool)>,
        on_stack: &mut HashSet<(u32, bool)>,
        depth: u32,
        call_count: &mut u32,
    ) -> bool {
        // #8013: Total-calls budget. Even with depth limiting, the branching
        // factor across many rows can produce exponential work. This caps the
        // total number of recursive invocations across the entire call tree.
        *call_count += 1;
        if *call_count > Self::MAX_RECURSIVE_CALLS {
            return false;
        }
        // #6590: Reduced from 12 to 8. Depth 12 causes exponential blowup on
        // sc-* benchmarks (32s → should be <1s). Z3 does not do recursive
        // reason collection at all — it stores lazy explanations. Depth 8
        // allows moderate transitive reasoning while capping the cost.
        // (Depth 6 caused clocksynchro_9clocks regression from unsat to unknown.)
        const MAX_DEPTH: u32 = 8;
        if depth > MAX_DEPTH {
            return false;
        }
        // Soundness (#cyclic-explanation false-UNSAT): a (var, direction)
        // pair whose derivation is CURRENTLY being explored on this DFS path
        // (gray node) means the justification is circular — the bound would
        // support itself through a row cycle. Previously this fell into the
        // `visited_vars` skip below and returned `true`, silently DROPPING
        // the antecedent and producing an over-strong reason clause (false
        // UNSAT). Fail closed instead; the caller rolls back and tries
        // another row or abandons the chain.
        if on_stack.contains(&(var, need_upper)) {
            return false;
        }
        // Prevent exponential re-exploration of the same (var, direction) pair
        // via different paths (#6364). Once we've FULLY explored a variable's
        // derivation chain (black node — kept in visited_vars only on
        // success, see #7654 rollback), don't re-enter it from another
        // branch: its reasons are already in the `reasons` vector.
        if !visited_vars.insert((var, need_upper)) {
            return true;
        }
        visited_added.push((var, need_upper));
        on_stack.insert((var, need_upper));
        let ok = self.collect_row_reasons_recursive_body(
            var,
            need_upper,
            reasons,
            seen,
            visited_vars,
            visited_added,
            on_stack,
            depth,
            call_count,
        );
        on_stack.remove(&(var, need_upper));
        ok
    }

    /// Body of `collect_row_reasons_recursive_inner` after the budget /
    /// cycle / visited checks; the caller owns the `on_stack` gray marker
    /// for (var, need_upper) and the `visited_added` push.
    #[allow(clippy::too_many_arguments)]
    fn collect_row_reasons_recursive_body(
        &self,
        var: u32,
        need_upper: bool,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
        visited_added: &mut Vec<(u32, bool)>,
        on_stack: &mut HashSet<(u32, bool)>,
        depth: u32,
        call_count: &mut u32,
    ) -> bool {
        // Case 1: var is basic — collect from nonbasic vars in its row.
        if let Some(&row_idx) = self.basic_var_to_row.get(&var) {
            let ok = self.collect_reasons_from_row_for_basic_inner(
                row_idx,
                need_upper,
                reasons,
                seen,
                visited_vars,
                visited_added,
                on_stack,
                depth,
                call_count,
            );
            // #7654: Only cache successful visits. If the basic row failed,
            // remove our entry so a future request (from a different row
            // context) can retry this variable instead of assuming its
            // reasons are already in the vector.
            if !ok {
                visited_vars.remove(&(var, need_upper));
                visited_added.pop();
            }
            return ok;
        }
        // Case 2: var is nonbasic — use the derivation row from implied_bounds
        // if available, then fall back to col_index search.
        let vi = var as usize;

        // Get stored derivation row index from implied_bounds (usize::MAX = direct bound).
        let stored_row = if vi < self.implied_bounds.len() {
            let ib = if need_upper {
                &self.implied_bounds[vi].1
            } else {
                &self.implied_bounds[vi].0
            };
            ib.as_ref()
                .filter(|b| b.row_idx != usize::MAX)
                .map(|b| b.row_idx)
        } else {
            None
        };

        if vi >= self.col_index.len() && stored_row.is_none() {
            visited_vars.remove(&(var, need_upper));
            visited_added.pop();
            return false;
        }

        // Try stored derivation row first (likely to succeed since it was the
        // row used to derive the bound), then fall back to col_index search.
        let col_rows: Vec<usize> = if vi < self.col_index.len() {
            self.col_index[vi].iter().map(|e| e.row_idx).collect()
        } else {
            Vec::new()
        };
        // #7654 / #8013: Record visited_added mark before the row loop.
        // When a row attempt fails, we rollback visited_vars by removing
        // entries added after this mark (stack-based rollback instead of
        // HashMap clone). This is O(added) per rollback instead of O(n) clone.
        let visited_mark = visited_added.len();
        for row_idx in stored_row.into_iter().chain(
            col_rows
                .iter()
                .copied()
                .filter(|ri| Some(*ri) != stored_row),
        ) {
            if row_idx >= self.rows.len() {
                continue;
            }
            let row = &self.rows[row_idx];
            // Row: basic_var = constant + Σ(coeff_j * nonbasic_j)
            // To derive a bound on `var` (a nonbasic variable with coefficient c_var):
            //   c_var * var = basic_var - constant - Σ(c_j * other_j)
            //
            // We need bounds on the basic variable AND all other nonbasic variables.
            // Try collecting reasons from them. If any is missing, skip this row.
            //
            // Rollback approach (#4919): instead of cloning `seen` for each candidate
            // row, record the insertion point and rollback on failure. This eliminates
            // O(seen × candidate_rows) allocation overhead.
            // Every new entry in `reasons` after `reasons_mark` corresponds to a
            // freshly-inserted `seen` key (including from recursive calls), so
            // truncating reasons + removing those keys from `seen` is correct.
            let reasons_mark = reasons.len();
            let mut all_found = true;

            // Find coefficient of var in this row (binary search on sorted vec)
            let var_coeff = match row.coeffs.binary_search_by_key(&var, |(v, _)| *v) {
                Ok(idx) => &row.coeffs[idx].1,
                Err(_) => continue,
            };
            // Determine what bound direction we need for the "sum" side.
            let sum_need_upper = var_coeff.is_positive() == need_upper;

            // Basic variable: need bound in `sum_need_upper` direction
            let bv = row.basic_var as usize;
            if bv >= self.vars.len() {
                continue;
            }

            // Check if implied bound is tighter than direct bound (#6202)
            let bv_implied_derived = if bv < self.implied_bounds.len() {
                let ib = if sum_need_upper {
                    &self.implied_bounds[bv].1
                } else {
                    &self.implied_bounds[bv].0
                };
                ib.as_ref()
                    .as_ref()
                    .is_some_and(|b| b.row_idx != usize::MAX)
            } else {
                false
            };

            if bv_implied_derived {
                if !self.collect_row_reasons_recursive_inner(
                    row.basic_var,
                    sum_need_upper,
                    reasons,
                    seen,
                    visited_vars,
                    visited_added,
                    on_stack,
                    depth + 1,
                    call_count,
                ) {
                    for lit in reasons.drain(reasons_mark..) {
                        seen.remove(&(lit.term, lit.value));
                    }
                    Self::rollback_visited(visited_vars, visited_added, visited_mark);
                    continue;
                }
            } else {
                let bv_info = &self.vars[bv];
                let bv_bound = if sum_need_upper {
                    &bv_info.upper
                } else {
                    &bv_info.lower
                };
                if let Some(b) = bv_bound {
                    for (term, val) in b.reason_pairs() {
                        if seen.insert((term, val)) {
                            reasons.push(TheoryLit::new(term, val));
                        }
                    }
                } else if !self.collect_row_reasons_recursive_inner(
                    row.basic_var,
                    sum_need_upper,
                    reasons,
                    seen,
                    visited_vars,
                    visited_added,
                    on_stack,
                    depth + 1,
                    call_count,
                ) {
                    for lit in reasons.drain(reasons_mark..) {
                        seen.remove(&(lit.term, lit.value));
                    }
                    Self::rollback_visited(visited_vars, visited_added, visited_mark);
                    continue; // Try next row
                }
            }

            // Other nonbasic variables (not `var` itself)
            for &(nv, ref coeff) in &row.coeffs {
                if nv == var {
                    continue;
                }
                let nvi = nv as usize;
                if nvi >= self.vars.len() {
                    all_found = false;
                    break;
                }
                let nv_need_upper = coeff.is_positive() != sum_need_upper;

                // Check if implied bound is tighter than direct bound (#6202)
                let nv_implied_derived = if nvi < self.implied_bounds.len() {
                    let ib = if nv_need_upper {
                        &self.implied_bounds[nvi].1
                    } else {
                        &self.implied_bounds[nvi].0
                    };
                    ib.as_ref().is_some_and(|b| b.row_idx != usize::MAX)
                } else {
                    false
                };

                if nv_implied_derived {
                    if !self.collect_row_reasons_recursive_inner(
                        nv,
                        nv_need_upper,
                        reasons,
                        seen,
                        visited_vars,
                        visited_added,
                        on_stack,
                        depth + 1,
                        call_count,
                    ) {
                        all_found = false;
                        break;
                    }
                } else {
                    let nv_info = &self.vars[nvi];
                    let nv_bound = if nv_need_upper {
                        &nv_info.upper
                    } else {
                        &nv_info.lower
                    };
                    if let Some(b) = nv_bound {
                        for (term, val) in b.reason_pairs() {
                            if seen.insert((term, val)) {
                                reasons.push(TheoryLit::new(term, val));
                            }
                        }
                    } else if !self.collect_row_reasons_recursive_inner(
                        nv,
                        nv_need_upper,
                        reasons,
                        seen,
                        visited_vars,
                        visited_added,
                        on_stack,
                        depth + 1,
                        call_count,
                    ) {
                        all_found = false;
                        break;
                    }
                }
            }

            if all_found {
                // Successfully collected all reasons from this row.
                return true;
            }
            // Rollback: undo all insertions into `seen`, `reasons`, and
            // `visited_vars` for this row (#7654 / #8013).
            for lit in reasons.drain(reasons_mark..) {
                seen.remove(&(lit.term, lit.value));
            }
            Self::rollback_visited(visited_vars, visited_added, visited_mark);
        }
        // All rows failed — remove our own entry so a future request
        // (from a different row context) can retry this variable.
        visited_vars.remove(&(var, need_upper));
        // Our entry was pushed at visited_mark - 1. Each row failure's
        // rollback_visited truncates to visited_mark, preserving our entry.
        // Now that all rows failed, pop our own entry too.
        debug_assert!(
            visited_mark > 0 && visited_added.get(visited_mark - 1) == Some(&(var, need_upper)),
            "visited_added stack invariant violated"
        );
        if visited_mark > 0 {
            visited_added.truncate(visited_mark - 1);
        }
        false
    }

    /// Rollback visited_vars entries added after `mark` in the visited_added stack.
    /// Removes each entry from the HashSet and truncates the stack to `mark`.
    fn rollback_visited(
        visited_vars: &mut HashSet<(u32, bool)>,
        visited_added: &mut Vec<(u32, bool)>,
        mark: usize,
    ) {
        for &entry in &visited_added[mark..] {
            visited_vars.remove(&entry);
        }
        visited_added.truncate(mark);
    }

    /// Collect reasons from a row where `var` is the basic variable.
    /// Helper for `collect_row_reasons_recursive` — the original Case 1 logic.
    #[allow(dead_code)]
    pub(crate) fn collect_reasons_from_row_for_basic(
        &self,
        row_idx: usize,
        need_upper: bool,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
        depth: u32,
    ) -> bool {
        let mut call_count: u32 = 0;
        let mut visited_added: Vec<(u32, bool)> = Vec::new();
        let mut on_stack: HashSet<(u32, bool)> = HashSet::default();
        self.collect_reasons_from_row_for_basic_inner(
            row_idx,
            need_upper,
            reasons,
            seen,
            visited_vars,
            &mut visited_added,
            &mut on_stack,
            depth,
            &mut call_count,
        )
    }

    /// Inner implementation of collect_reasons_from_row_for_basic with
    /// stack-based visited rollback and call budget.
    #[allow(clippy::too_many_arguments)]
    fn collect_reasons_from_row_for_basic_inner(
        &self,
        row_idx: usize,
        need_upper: bool,
        reasons: &mut Vec<TheoryLit>,
        seen: &mut HashSet<(TermId, bool)>,
        visited_vars: &mut HashSet<(u32, bool)>,
        visited_added: &mut Vec<(u32, bool)>,
        on_stack: &mut HashSet<(u32, bool)>,
        depth: u32,
        call_count: &mut u32,
    ) -> bool {
        let row = &self.rows[row_idx];
        let mark = reasons.len();
        for &(nv, ref coeff) in &row.coeffs {
            let nvi = nv as usize;
            if nvi >= self.vars.len() {
                // Rollback partial additions from earlier nonbasic vars
                for lit in reasons.drain(mark..) {
                    seen.remove(&(lit.term, lit.value));
                }
                return false;
            }
            let nv_need_upper = coeff.is_positive() == need_upper;

            // Check if implied bound is tighter than direct bound (#6202).
            // compute_implied_bounds() may derive a tighter bound from another
            // tableau row. If that happened (row_idx != usize::MAX), the direct
            // bound's reasons are insufficient — we must trace through the
            // derivation row that produced the tighter bound.
            let implied_derived = if nvi < self.implied_bounds.len() {
                let ib = if nv_need_upper {
                    &self.implied_bounds[nvi].1
                } else {
                    &self.implied_bounds[nvi].0
                };
                ib.as_ref()
                    .as_ref()
                    .is_some_and(|b| b.row_idx != usize::MAX)
            } else {
                false
            };

            if implied_derived {
                // Implied bound was derived from a tableau row and is tighter
                // than the direct bound. Recursively collect from the derivation
                // chain to get the true set of reason literals.
                if !self.collect_row_reasons_recursive_inner(
                    nv,
                    nv_need_upper,
                    reasons,
                    seen,
                    visited_vars,
                    visited_added,
                    on_stack,
                    depth + 1,
                    call_count,
                ) {
                    // Rollback partial additions from earlier nonbasic vars
                    for lit in reasons.drain(mark..) {
                        seen.remove(&(lit.term, lit.value));
                    }
                    return false;
                }
            } else {
                let info = &self.vars[nvi];
                let bound = if nv_need_upper {
                    &info.upper
                } else {
                    &info.lower
                };
                if let Some(b) = bound {
                    for (term, val) in b.reason_pairs() {
                        if seen.insert((term, val)) {
                            reasons.push(TheoryLit::new(term, val));
                        }
                    }
                } else if !self.collect_row_reasons_recursive_inner(
                    nv,
                    nv_need_upper,
                    reasons,
                    seen,
                    visited_vars,
                    visited_added,
                    on_stack,
                    depth + 1,
                    call_count,
                ) {
                    // Rollback partial additions from earlier nonbasic vars
                    for lit in reasons.drain(mark..) {
                        seen.remove(&(lit.term, lit.value));
                    }
                    return false;
                }
            }
        }
        true
    }
}
