// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Phase 0b: Implication-based generalization for blocking formulas.
//!
//! For state formula (v1 = c1 AND v2 = c2), tries to learn implicative lemmas:
//! If (v1 = c1) => (v2 != c2) is inductive, produces NOT(v1 = c1) OR (v2 != c2).
//! Discovers invariants like (pc = 2) => (lock = 1) for mutex protocols.
//!
//! Also includes range implications: (v1 = c1) => (v2 < c2) and init-guarded
//! strengthening for init-only antecedent values.

use super::super::*;

impl PdrSolver {
    /// Phase 0b: Implication generalization.
    ///
    /// Returns `Some(blocking_formula)` if generalization succeeded, `None` to continue.
    pub(super) fn generalize_phase_implication(
        &mut self,
        current_conjuncts: &[ChcExpr],
        predicate: PredicateId,
        level: usize,
    ) -> Option<ChcExpr> {
        if current_conjuncts.len() < 2 {
            return None;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: Phase 0b implication generalization with {} conjuncts",
                current_conjuncts.len()
            );
        }
        let mut small_range_implication_blocking: Vec<ChcExpr> = Vec::new();
        let mut point_implication_blocking: Option<ChcExpr> = None;

        // Extract all equality conjuncts
        let equalities: Vec<(usize, ChcVar, i128)> = current_conjuncts
            .iter()
            .enumerate()
            .filter_map(|(i, c)| Self::extract_equality(c).map(|(v, val)| (i, v, val)))
            .collect();

        // Get init bounds for range-based implications
        let init_values = self.get_init_values(predicate);

        // Try each pair of equalities for implication pattern
        for i in 0..equalities.len() {
            for j in 0..equalities.len() {
                if i == j {
                    continue;
                }

                let (_, var_antecedent, val_antecedent) = &equalities[i];
                let (_, var_consequent, val_consequent) = &equalities[j];

                // First, try range consequent: (v1 = c1) => (v2 < c2) or (v1 = c1) => (v2 > c2)
                // This handles cases like (pc = 1) => (i < 10) for B3
                if let Some(init_bounds) = init_values.get(&var_consequent.name) {
                    // IMPORTANT: Only use range implications when the gap from init bounds is
                    // "large enough" that multi-step reachability is unlikely to be an issue.
                    // For small-domain variables (like pc with values 0,1,2), the level-1
                    // inductiveness check is too weak because states can be reached in
                    // 2+ transitions. We require a gap of at least 3 to use range implications.
                    // This prevents overgeneralization like (pc1=2) => (pc2<2) for mutex protocols.
                    // (Mutex has pc values 0,1,2 - a gap of 2 from init, so MIN_RANGE_GAP=3 blocks it)
                    const MIN_RANGE_GAP: i128 = 3;

                    // Try: (v1 = c1) => (v2 < c2) - when c2 is significantly above init max
                    // Use saturating_add to avoid overflow when init_bounds.max is near i64::MAX
                    if *val_consequent > init_bounds.max.saturating_add(MIN_RANGE_GAP) {
                        // Blocking formula is (v1 = c1 AND v2 >= c2)
                        let mut blocking_formula = ChcExpr::and(
                            ChcExpr::eq(
                                ChcExpr::var(var_antecedent.clone()),
                                ChcExpr::Int(*val_antecedent),
                            ),
                            ChcExpr::ge(
                                ChcExpr::var(var_consequent.clone()),
                                ChcExpr::Int(*val_consequent),
                            ),
                        );
                        // Prefer dropping the antecedent when the range bound alone is inductive.
                        // This avoids learning disjunctive implications like:
                        //   (y = 0) => (x > -12)
                        // when we can learn the stronger unconditional bound:
                        //   x > -12
                        let bound_only = ChcExpr::ge(
                            ChcExpr::var(var_consequent.clone()),
                            ChcExpr::Int(*val_consequent),
                        );
                        if self.is_inductive_blocking(&bound_only, predicate, 1)
                            && self.is_inductive_blocking(&bound_only, predicate, level)
                        {
                            blocking_formula = bound_only;
                        }
                        // BUG FIX #685: Check BOTH 1-step inductiveness from init AND self-inductiveness.
                        // The original code only checked is_inductive_blocking at level 1, which verifies:
                        //   init /\ T => L' (lemma holds after one step from init)
                        // But for counter variables, this is insufficient. We also need:
                        //   L /\ T => L' (lemma is preserved by ALL transitions, not just from init)
                        // Without this, we could learn (pc=0) => (x<6) when x increments each step.
                        let is_inductive_at_level1 =
                            self.is_inductive_blocking(&blocking_formula, predicate, 1);
                        let is_inductive_at_current =
                            self.is_inductive_blocking(&blocking_formula, predicate, level);
                        let is_self_inductive = if level == 1 {
                            self.is_self_inductive_blocking(&blocking_formula, predicate)
                        } else {
                            true
                        };
                        if is_inductive_at_level1 && is_inductive_at_current && is_self_inductive {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Range implication: ({} = {}) => ({} < {}): level1={}, current={}, self_ind={} (at level {})",
                                    var_antecedent.name,
                                    val_antecedent,
                                    var_consequent.name,
                                    val_consequent,
                                    if is_inductive_at_level1 { "yes" } else { "no" },
                                    if is_inductive_at_current { "yes" } else { "no" },
                                    if is_self_inductive { "yes" } else { "no" }
                                    ,
                                    level
                                );
                            }
                            // Prefer learning large-bound implications immediately (typical loop bounds),
                            // but avoid short-circuiting on small-domain vars (e.g., pc) so we can
                            // still discover better lock/auxiliary implications.
                            if (*val_consequent).unsigned_abs() >= 5 {
                                // NOT((v1 = c1) => (v2 < c2))  <==>  (v1 = c1) AND (v2 >= c2)
                                return Some(blocking_formula);
                            }
                            small_range_implication_blocking.push(blocking_formula);
                        }
                    }

                    // Try: (v1 = c1) => (v2 > c2) - when c2 is significantly below init min
                    // Use saturating_sub to avoid overflow when init_bounds.min is near i64::MIN
                    if *val_consequent < init_bounds.min.saturating_sub(MIN_RANGE_GAP) {
                        // Blocking formula is (v1 = c1 AND v2 <= c2)
                        let mut blocking_formula = ChcExpr::and(
                            ChcExpr::eq(
                                ChcExpr::var(var_antecedent.clone()),
                                ChcExpr::Int(*val_antecedent),
                            ),
                            ChcExpr::le(
                                ChcExpr::var(var_consequent.clone()),
                                ChcExpr::Int(*val_consequent),
                            ),
                        );
                        // Prefer dropping the antecedent when the bound alone is inductive.
                        let bound_only = ChcExpr::le(
                            ChcExpr::var(var_consequent.clone()),
                            ChcExpr::Int(*val_consequent),
                        );
                        if self.is_inductive_blocking(&bound_only, predicate, 1)
                            && self.is_inductive_blocking(&bound_only, predicate, level)
                        {
                            blocking_formula = bound_only;
                        }
                        let is_inductive_at_level1 =
                            self.is_inductive_blocking(&blocking_formula, predicate, 1);
                        let is_inductive_at_current =
                            self.is_inductive_blocking(&blocking_formula, predicate, level);
                        let is_self_inductive = if level == 1 {
                            self.is_self_inductive_blocking(&blocking_formula, predicate)
                        } else {
                            true
                        };
                        if is_inductive_at_level1 && is_inductive_at_current && is_self_inductive {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Range implication: ({} = {}) => ({} > {}): level1={}, current={}, self_ind={} (at level {})",
                                    var_antecedent.name,
                                    val_antecedent,
                                    var_consequent.name,
                                    val_consequent,
                                    if is_inductive_at_level1 { "yes" } else { "no" },
                                    if is_inductive_at_current { "yes" } else { "no" },
                                    if is_self_inductive { "yes" } else { "no" }
                                    ,
                                    level
                                );
                            }
                            if (*val_consequent).unsigned_abs() >= 5 {
                                // NOT((v1 = c1) => (v2 > c2))  <==>  (v1 = c1) AND (v2 <= c2)
                                return Some(blocking_formula);
                            }
                            small_range_implication_blocking.push(blocking_formula);
                        }
                    }
                }

                // Try: (var_antecedent = val_antecedent) => (var_consequent != val_consequent)
                // This is equivalent to: NOT(var_antecedent = val_antecedent) OR (var_consequent != val_consequent)

                // blocking_formula = (v1 = c1) AND (v2 = c2)
                let blocking_formula = ChcExpr::and(
                    ChcExpr::eq(
                        ChcExpr::var(var_antecedent.clone()),
                        ChcExpr::Int(*val_antecedent),
                    ),
                    ChcExpr::eq(
                        ChcExpr::var(var_consequent.clone()),
                        ChcExpr::Int(*val_consequent),
                    ),
                );

                // Check if blocking (v1 = c1 AND v2 = c2) is inductive
                let is_inductive_at_current =
                    self.is_inductive_blocking(&blocking_formula, predicate, level);
                // BUG FIX #685: At level 1, also verify self-inductiveness.
                // Level 1 checks only verify 1-step from init, missing multi-step reachability.
                // Point blocking lemmas like (pc=0 AND x=6) can block reachable states.
                let is_self_inductive = if level == 1 {
                    self.is_self_inductive_blocking(&blocking_formula, predicate)
                } else {
                    true // Higher levels don't need extra check - frame constraints are stronger
                };
                if self.config.verbose {
                    let is_inductive_at_level1 = if level <= 1 {
                        is_inductive_at_current
                    } else {
                        self.is_inductive_blocking(&blocking_formula, predicate, 1)
                    };
                    safe_eprintln!(
                        "PDR: Trying implication ({} = {}) => ({} != {}): {} (level1={}, current={}, self_ind={})",
                        var_antecedent.name, val_antecedent,
                        var_consequent.name, val_consequent,
                        if is_inductive_at_current && is_self_inductive { "INDUCTIVE" } else { "not inductive" },
                        if is_inductive_at_level1 { "yes" } else { "no" },
                        level,
                        if is_self_inductive { "yes" } else { "no" }
                    );
                }
                if is_inductive_at_current
                    && is_self_inductive
                    && point_implication_blocking.is_none()
                {
                    // Fix #967: Init-guarded strengthening
                    //
                    // Before accepting a point implication like (a0 = 0 AND a2 = k), check if
                    // the antecedent (a0 = 0) is "init-only" (value that can only hold at init).
                    // If so, learn a stronger blocking formula: (a0 = 0) AND (a2 != init_a2)
                    // instead of the point-specific (a0 = 0) AND (a2 = k).
                    //
                    // This prevents per-value enumeration under init-guarded antecedents.
                    if let Some(antecedent_init_bounds) = init_values.get(&var_antecedent.name) {
                        // Check if antecedent value matches an exact init value (min == max == val)
                        if antecedent_init_bounds.min == antecedent_init_bounds.max
                            && antecedent_init_bounds.min == *val_antecedent
                        {
                            // Check if this init value is "init-only" (cannot reoccur)
                            if self.is_init_only_value(
                                predicate,
                                &var_antecedent.name,
                                *val_antecedent,
                            ) {
                                // Try init-guarded strengthening: block (a0 = init) AND (a2 != init)
                                if let Some(consequent_init_bounds) =
                                    init_values.get(&var_consequent.name)
                                {
                                    // Only apply when consequent has an exact init value (min == max)
                                    if consequent_init_bounds.min == consequent_init_bounds.max {
                                        let consequent_init = consequent_init_bounds.min;
                                        // blocking_formula = (a0 = init_a0) AND (a2 != init_a2)
                                        // expressed as disjunction for blocking convention:
                                        // = (a0 = 0) AND ((a2 < 0) OR (a2 > 0)) since init_a2 = 0
                                        // But for SMT, use: (a0 = 0) AND (NOT (a2 = 0))
                                        let init_guard_blocking = ChcExpr::and(
                                            ChcExpr::eq(
                                                ChcExpr::var(var_antecedent.clone()),
                                                ChcExpr::Int(*val_antecedent),
                                            ),
                                            ChcExpr::not(ChcExpr::eq(
                                                ChcExpr::var(var_consequent.clone()),
                                                ChcExpr::Int(consequent_init),
                                            )),
                                        );

                                        // Check if this stronger blocking formula is inductive
                                        let is_init_guard_inductive = self.is_inductive_blocking(
                                            &init_guard_blocking,
                                            predicate,
                                            level,
                                        );
                                        let is_init_guard_self_inductive = if level == 1 {
                                            self.is_self_inductive_blocking(
                                                &init_guard_blocking,
                                                predicate,
                                            )
                                        } else {
                                            true
                                        };

                                        if is_init_guard_inductive && is_init_guard_self_inductive {
                                            if self.config.verbose {
                                                safe_eprintln!(
                                                    "PDR: Init-guarded strengthening: ({} = {}) AND ({} != {}) blocks region (vs point {} = {})",
                                                    var_antecedent.name, val_antecedent,
                                                    var_consequent.name, consequent_init,
                                                    var_consequent.name, val_consequent
                                                );
                                            }
                                            // Use the init-guarded formula instead of point implication
                                            return Some(init_guard_blocking);
                                        }
                                    }
                                }
                            }
                        }
                    }

                    // Fall back to point implication if init-guarded strengthening didn't apply
                    // Fix for #302: Preserve the conditional antecedent when selecting
                    // a point implication. We keep the first inductive implication's
                    // blocking cube: (A=c AND B=v), not an unrelated pair (B=v AND C=w).
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Found inductive implication blocking cube: ({} = {}) AND ({} = {})",
                            var_antecedent.name,
                            val_antecedent,
                            var_consequent.name,
                            val_consequent
                        );
                    }
                    point_implication_blocking = Some(blocking_formula);
                }
            }
        }

        // PRIORITY: If we found range implications (e.g., (A=0) => (B<2)), use them first.
        // Range implications are more general than point-blocking and prevent enumeration.
        // This is critical for benchmarks like const_mod_3 where B toggles 0<->1.
        if !small_range_implication_blocking.is_empty() {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Using range implication blocking (priority over point-blocking)"
                );
            }
            return Some(small_range_implication_blocking[0].clone());
        }

        if let Some(blocking) = point_implication_blocking {
            return Some(blocking);
        }
        None
    }
}
