// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Blocking formula generalization orchestrator.
//!
//! Contains `try_strengthen_point_blocking` and the main `generalize_blocking_formula`
//! orchestrator. The heavy lifting is delegated to sibling modules:
//! - `generalization_implication`: Phase 0b implication-based generalization
//! - `generalization_weakening`: Phases 1a-2 weakening and generalizer pipeline
//! - `generalization_iuc`: IUC (Inductive UNSAT Core) shrinking

use super::super::*;

impl PdrSolver {
    fn build_scaled_var_expr(var: &ChcVar, coeff: i128) -> ChcExpr {
        match coeff {
            1 => ChcExpr::var(var.clone()),
            -1 => ChcExpr::neg(ChcExpr::var(var.clone())),
            _ => ChcExpr::mul(ChcExpr::int(coeff), ChcExpr::var(var.clone())),
        }
    }

    fn build_point_affine_equality(
        var_i: &ChcVar,
        val_i: i128,
        coeff_i: i128,
        var_j: &ChcVar,
        val_j: i128,
        coeff_j: i128,
    ) -> Option<ChcExpr> {
        let lhs = Self::build_scaled_var_expr(var_i, coeff_i);
        let rhs = Self::build_scaled_var_expr(var_j, coeff_j);
        let offset = coeff_i
            .checked_mul(val_i)?
            .checked_sub(coeff_j.checked_mul(val_j)?)?;
        let shifted_rhs = if offset == 0 {
            rhs
        } else {
            ChcExpr::add(rhs, ChcExpr::int(offset))
        };
        Some(ChcExpr::eq(lhs, shifted_rhs).simplify_constants())
    }

    fn normalized_affine_signature(
        &self,
        predicate: PredicateId,
        expr: &ChcExpr,
    ) -> Option<(ChcExpr, i128)> {
        let normalized = self.normalize_affine_equality_for_target(predicate, expr)?;
        match normalized {
            ChcExpr::Op(ChcOp::Eq, ref args) if args.len() == 2 => {
                match (args[0].as_ref(), args[1].as_ref()) {
                    (lhs, ChcExpr::Int(constant)) => Some((lhs.clone(), *constant)),
                    (ChcExpr::Int(constant), rhs) => Some((rhs.clone(), *constant)),
                    _ => None,
                }
            }
            _ => None,
        }
    }

    fn collect_affine_anchor_signatures(
        &self,
        predicate: PredicateId,
        level: usize,
    ) -> Vec<(ChcExpr, i128)> {
        let mut anchors = Vec::new();
        let mut seen: FxHashSet<(u64, i128)> = FxHashSet::default();

        for frame in self.frames.iter().take(level.saturating_add(1)).skip(1) {
            for lemma in frame
                .lemmas
                .iter()
                .filter(|lemma| lemma.predicate == predicate)
            {
                let Some((lhs, constant)) =
                    self.normalized_affine_signature(predicate, &lemma.formula)
                else {
                    continue;
                };
                let key = (lhs.structural_hash(), constant);
                if seen.insert(key) {
                    anchors.push((lhs, constant));
                }
            }
        }

        anchors.sort_by_key(|(lhs, constant)| (lhs.structural_hash(), *constant));
        anchors
    }

    fn try_disjunctive_affine_generalization(
        &mut self,
        current_conjuncts: &[ChcExpr],
        predicate: PredicateId,
        level: usize,
    ) -> Option<ChcExpr> {
        if level == 0 {
            return None;
        }

        let anchors = self.collect_affine_anchor_signatures(predicate, level);
        if anchors.is_empty() {
            return None;
        }

        let var_values: Vec<(ChcVar, i128)> = current_conjuncts
            .iter()
            .filter_map(Self::extract_equality)
            .collect();
        if var_values.len() < 2 {
            return None;
        }

        const COEFF_PAIRS: &[(i128, i128)] = &[(1, 1), (2, 1), (1, 2), (-1, 1), (1, -1)];
        let mut seen_blocking: FxHashSet<u64> = FxHashSet::default();

        for i in 0..var_values.len() {
            for j in 0..var_values.len() {
                if i == j {
                    continue;
                }
                let (var_i, val_i) = &var_values[i];
                let (var_j, val_j) = &var_values[j];
                if var_i.name == var_j.name {
                    continue;
                }

                for &(coeff_i, coeff_j) in COEFF_PAIRS {
                    let Some(point_eq) = Self::build_point_affine_equality(
                        var_i, *val_i, coeff_i, var_j, *val_j, coeff_j,
                    ) else {
                        continue;
                    };
                    let Some((lhs, point_constant)) =
                        self.normalized_affine_signature(predicate, &point_eq)
                    else {
                        continue;
                    };

                    for (anchor_lhs, anchor_constant) in &anchors {
                        if *anchor_lhs != lhs {
                            continue;
                        }

                        let neighbors = [
                            anchor_constant.checked_sub(1),
                            anchor_constant.checked_add(1),
                        ];
                        for neighbor in neighbors.into_iter().flatten() {
                            if point_constant == *anchor_constant || point_constant == neighbor {
                                continue;
                            }

                            let (lo, hi) = if neighbor < *anchor_constant {
                                (neighbor, *anchor_constant)
                            } else {
                                (*anchor_constant, neighbor)
                            };
                            let disj_lo = ChcExpr::eq(lhs.clone(), ChcExpr::int(lo));
                            let disj_hi = ChcExpr::eq(lhs.clone(), ChcExpr::int(hi));
                            let blocking = ChcExpr::and(
                                ChcExpr::not(disj_lo.clone()),
                                ChcExpr::not(disj_hi.clone()),
                            );
                            let blocking_hash = blocking.structural_hash();
                            if !seen_blocking.insert(blocking_hash) {
                                continue;
                            }

                            if self.is_inductive_blocking(&blocking, predicate, level) {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Disjunctive affine generalization: {} OR {}",
                                        disj_lo,
                                        disj_hi
                                    );
                                }
                                return Some(blocking);
                            }
                        }
                    }
                }
            }
        }

        None
    }

    fn build_modular_residue_blocking(var: &ChcVar, modulus: i128, residue: i128) -> ChcExpr {
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(var.clone()), ChcExpr::int(modulus)),
            ChcExpr::int(residue),
        )
        .simplify_constants()
    }

    fn recent_blocked_numeric_values(
        &self,
        predicate: PredicateId,
        var_name: &str,
        limit: usize,
    ) -> Vec<i128> {
        self.caches
            .blocked_states_for_convex
            .get(&predicate)
            .map(|entries| {
                entries
                    .iter()
                    .rev()
                    .filter_map(|entry| entry.get(var_name).copied().map(i128::from))
                    .take(limit)
                    .collect()
            })
            .unwrap_or_default()
    }

    fn try_modular_history_generalization(
        &mut self,
        state: &ChcExpr,
        predicate: PredicateId,
        level: usize,
    ) -> Option<ChcExpr> {
        const MODULI: &[i128] = &[2, 3];
        const HISTORY_WINDOW: usize = 3;
        const MIN_BLOCKED_CUBES: usize = 2;

        let init_values = self.get_init_values(predicate);
        let mut seen_candidates: FxHashSet<(String, i128, i128)> = FxHashSet::default();

        for conjunct in state.collect_conjuncts() {
            let Some((var, val)) = Self::extract_equality(&conjunct) else {
                continue;
            };
            if !matches!(var.sort, ChcSort::Int) {
                continue;
            }

            let Some(init_bounds) = init_values.get(&var.name) else {
                continue;
            };
            if init_bounds.min != init_bounds.max {
                continue;
            }

            let recent_values =
                self.recent_blocked_numeric_values(predicate, &var.name, HISTORY_WINDOW);
            if recent_values.len() + 1 < MIN_BLOCKED_CUBES {
                continue;
            }

            for &modulus in MODULI {
                let blocked_residue = val.rem_euclid(modulus);
                let init_residue = init_bounds.min.rem_euclid(modulus);
                if blocked_residue == init_residue {
                    continue;
                }
                if !recent_values
                    .iter()
                    .all(|prev| prev.rem_euclid(modulus) == blocked_residue)
                {
                    continue;
                }
                if !seen_candidates.insert((var.name.clone(), modulus, blocked_residue)) {
                    continue;
                }

                let blocking_formula =
                    Self::build_modular_residue_blocking(&var, modulus, blocked_residue);
                if self.is_inductive_blocking(&blocking_formula, predicate, level) {
                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Phase 0c modular history: {} mod {} = {} from {} blocked cubes (init mod {} = {})",
                            var.name,
                            modulus,
                            blocked_residue,
                            recent_values.len() + 1,
                            modulus,
                            init_residue
                        );
                    }
                    return Some(blocking_formula);
                }
            }
        }

        None
    }

    /// Fix #967: Strengthen weak point-blocking from interpolation to avoid enumeration.
    ///
    /// When interpolation produces a single-variable equality like `(= var k)`, this blocks
    /// only one point value. If var has an init-only value (appears at init and never again
    /// in the self-loop), we can strengthen to `(= var init_val)` to block ALL non-init states.
    pub(in crate::pdr::solver) fn try_strengthen_point_blocking(
        &mut self,
        blocking_formula: &ChcExpr,
        predicate: PredicateId,
        level: usize,
        pob_state: &ChcExpr,
    ) -> ChcExpr {
        if self.config.verbose {
            safe_eprintln!(
                "PDR: #967 try_strengthen_point_blocking input: {}",
                blocking_formula
            );
        }
        // Extract equality from various forms:
        // - (= var const)
        // - (not (distinct var const)) - this comes from NOT(interpolant) when interpolant is (distinct ...)
        if let Some((var, val)) = Self::extract_equality_or_not_distinct(blocking_formula) {
            let init_values = self.get_init_values(predicate);
            if let Some(init_bounds) = init_values.get(&var.name) {
                // Only strengthen if init has exact value (min == max) and val != init
                if init_bounds.min == init_bounds.max && val != init_bounds.min {
                    let init_val = init_bounds.min;
                    // Check if this value is init-only (cannot reoccur in self-loop)
                    if self.is_init_only_value(predicate, &var.name, init_val) {
                        // Try strengthening: (= var val) -> (= var init_val)
                        let strengthened =
                            ChcExpr::eq(ChcExpr::var(var.clone()), ChcExpr::Int(init_val));
                        if self.is_inductive_blocking(&strengthened, predicate, level) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: #967 strengthened ({} = {}) to ({} = {}) [init-only]",
                                    var.name,
                                    val,
                                    var.name,
                                    init_val
                                );
                            }
                            return strengthened;
                        }
                    }

                    // #1155: If init-only strengthening failed, try range generalization.
                    // When val < init_min, generalize to (var < init_min).
                    // This avoids infinite per-value enumeration in bounded systems.
                    //
                    // Try at the current level first, then at level 1 (relative to init).
                    // The lemma (var >= init_min) may not be self-inductive at higher levels
                    // but IS inductive relative to init.
                    if val < init_bounds.min {
                        let range_blocking =
                            ChcExpr::lt(ChcExpr::var(var.clone()), ChcExpr::Int(init_bounds.min));
                        // Try current level first
                        if self.is_inductive_blocking(&range_blocking, predicate, level) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: #1155 strengthened ({} = {}) to ({} < {}) [range-below-init] at level {}",
                                    var.name, val, var.name, init_bounds.min, level
                                );
                            }
                            return range_blocking;
                        }
                        // Try level 1 (relative to init) if current level failed
                        if level > 1 && self.is_inductive_blocking(&range_blocking, predicate, 1) {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: #1155 strengthened ({} = {}) to ({} < {}) [range-below-init] at level 1",
                                    var.name, val, var.name, init_bounds.min
                                );
                            }
                            return range_blocking;
                        }
                    }
                }
            }
        }

        // Check for conjunctions containing equalities that can be strengthened
        let conjuncts = blocking_formula.collect_conjuncts();
        if conjuncts.len() >= 2 {
            let init_values = self.get_init_values(predicate);
            let mut new_conjuncts = Vec::with_capacity(conjuncts.len());
            let mut strengthened = false;

            for conjunct in &conjuncts {
                if let Some((var, val)) = Self::extract_equality_or_not_distinct(conjunct) {
                    if let Some(init_bounds) = init_values.get(&var.name) {
                        if init_bounds.min == init_bounds.max && val != init_bounds.min {
                            let init_val = init_bounds.min;
                            if self.is_init_only_value(predicate, &var.name, init_val) {
                                let strengthened_eq =
                                    ChcExpr::eq(ChcExpr::var(var.clone()), ChcExpr::Int(init_val));
                                // Check if strengthened conjunction is still inductive
                                let mut test_conjuncts = new_conjuncts.clone();
                                test_conjuncts.push(strengthened_eq.clone());
                                let test_formula = ChcExpr::and_all(test_conjuncts);
                                if self.is_inductive_blocking(&test_formula, predicate, level) {
                                    // #1236: CRITICAL - verify the strengthened formula still blocks
                                    // the POB state. Strengthening (var = val) to (var = init_val)
                                    // changes WHICH state is blocked, so we must check that POB
                                    // still implies the strengthened formula.
                                    //
                                    // The blocking lemma will be NOT(test_formula), and for it to
                                    // block pob_state, we need: pob_state => test_formula
                                    // (so that NOT(test_formula) is false for pob_state)
                                    //
                                    // Quick check: if pob_state conjuncts contain (var = val) but
                                    // we're proposing (var = init_val) where init_val != val,
                                    // then pob_state does NOT imply test_formula.
                                    let pob_conjuncts = pob_state.collect_conjuncts();
                                    let pob_has_different_value = pob_conjuncts.iter().any(|pc| {
                                        if let Some((pob_var, pob_val)) =
                                            Self::extract_equality_or_not_distinct(pc)
                                        {
                                            pob_var.name == var.name && pob_val != init_val
                                        } else {
                                            false
                                        }
                                    });
                                    if pob_has_different_value {
                                        // Cannot strengthen: POB state would not be blocked
                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: #1236 skipping strengthening ({} = {}) to ({} = {}) - would not block POB state",
                                                var.name, val, var.name, init_val
                                            );
                                        }
                                        new_conjuncts.push(conjunct.clone());
                                        continue;
                                    }
                                    if self.config.verbose {
                                        safe_eprintln!(
                                            "PDR: #967 strengthened ({} = {}) to ({} = {}) in conjunction",
                                            var.name, val, var.name, init_val
                                        );
                                    }
                                    new_conjuncts.push(strengthened_eq);
                                    strengthened = true;
                                    continue;
                                }
                            }
                        }
                    }
                }
                new_conjuncts.push(conjunct.clone());
            }

            if strengthened {
                return ChcExpr::and_all(new_conjuncts);
            }
        }

        blocking_formula.clone()
    }

    /// Generalize a blocking formula by dropping conjuncts and weakening equalities
    ///
    /// Given a state formula s to block, we try to find a more general formula s'
    /// such that:
    /// 1. s' implies s (s' is more general)
    /// 2. s' is inductive relative to the current frame (frame[level-1] /\ T => s')
    /// 3. s' doesn't block initial states (init /\ s' is satisfiable or we don't care)
    ///
    /// Uses two techniques:
    /// 1. Drop-literal: try removing conjuncts one at a time
    /// 2. Inequality weakening: weaken equalities (v = c) to inequalities against init bounds
    pub(in crate::pdr::solver) fn generalize_blocking_formula(
        &mut self,
        state: &ChcExpr,
        predicate: PredicateId,
        level: usize,
    ) -> ChcExpr {
        self.telemetry.generalization_attempts =
            self.telemetry.generalization_attempts.saturating_add(1);

        // Deadline early-out. Generalization is OPTIONAL widening of an already
        // sound blocking formula; if the solve deadline is already spent, return
        // the un-generalized state unchanged (sound — it still blocks the
        // obligation) rather than entering the multi-phase enumeration. Combined
        // with the `is_inductive_blocking` cancel short-circuit, this guarantees
        // generalization cannot spin past the timeout on a non-synthesizable
        // invariant.
        if self.is_cancelled() {
            return state.clone();
        }

        // Extract conjuncts from the state formula
        let conjuncts = state.collect_conjuncts();

        if conjuncts.is_empty() {
            return state.clone();
        }

        // Phase -1: UNSAT core shrinking (before domain-specific heuristics)
        //
        // When blocking cubes are large (e.g., from multi-reason bound conflicts after the #294
        // fix), shrink using UNSAT cores BEFORE expensive heuristic phases. This is a port of
        // Z3 Spacer's pattern where inductiveness checks opportunistically shrink cubes using
        // the UNSAT core (reference/z3/src/muz/spacer/spacer_context.cpp:1540-1564).
        //
        // Gate: Only run if cube has multiple conjuncts (conjuncts.len() >= 2). The previous
        // threshold of >= 6 was too conservative - benchmarks like s_multipl_12 have 3-argument
        // predicates producing cubes of 2-5 conjuncts that never triggered shrinking.
        // Z3's check_inductive extracts cores unconditionally on UNSAT (#302 gap analysis).
        let mut current_conjuncts = conjuncts;
        if level >= 2 && current_conjuncts.len() >= 2 {
            if let Some(shrunk) =
                self.try_shrink_blocking_conjuncts_with_iuc(&current_conjuncts, predicate, level)
            {
                if shrunk.len() < current_conjuncts.len() {
                    let candidate = Self::build_conjunction(&shrunk);
                    if self.is_inductive_blocking(&candidate, predicate, level) {
                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Phase -1 IUC shrunk {} -> {} conjuncts",
                                current_conjuncts.len(),
                                shrunk.len()
                            );
                        }
                        current_conjuncts = shrunk;
                    }
                }
            }
        }

        // Phase 0 (pre): Constant sum detection (try BEFORE relational equality)
        //
        // For states like (x=0, y=1) where init has (x=0, y=100), check if
        // the state violates a preserved sum invariant like x + y = 100.
        // This is critical for loop invariants that transfer quantities.
        // Must run BEFORE relational equality which would find x = y + offset patterns.
        if current_conjuncts.len() >= 2 {
            let var_vals: Vec<(ChcVar, i128)> = current_conjuncts
                .iter()
                .filter_map(Self::extract_equality)
                .collect();

            if var_vals.len() >= 2 {
                let init_values = self.get_init_values(predicate);

                for i in 0..var_vals.len() {
                    for j in (i + 1)..var_vals.len() {
                        let (var_i, val_i) = &var_vals[i];
                        let (var_j, val_j) = &var_vals[j];

                        if let (Some(init_i), Some(init_j)) =
                            (init_values.get(&var_i.name), init_values.get(&var_j.name))
                        {
                            if init_i.min == init_i.max && init_j.min == init_j.max {
                                let init_sum = init_i.min + init_j.min;
                                let state_sum = *val_i + *val_j;

                                if state_sum != init_sum {
                                    // State violates sum invariant - but is the sum actually preserved?
                                    // Verify ALGEBRAICALLY that sum is preserved by all transitions.
                                    // For B6: x_next = x+1, y_next = y-1 => x_next + y_next = x + y (preserved)
                                    // For B7: a_next = b, b_next = a+b => sum changes (NOT preserved)
                                    if !self
                                        .is_sum_preserved_by_transitions(predicate, var_i, var_j)
                                    {
                                        continue;
                                    }

                                    let sum_expr = ChcExpr::add(
                                        ChcExpr::var(var_i.clone()),
                                        ChcExpr::var(var_j.clone()),
                                    );
                                    let blocking_formula =
                                        ChcExpr::ne(sum_expr.clone(), ChcExpr::Int(init_sum));

                                    // Check basic inductiveness at level 1 (from init)
                                    if self.is_inductive_blocking(&blocking_formula, predicate, 1) {
                                        if self.config.verbose {
                                            safe_eprintln!(
                                                "PDR: Constant sum generalization: ({} + {}) != {} (algebraically verified)",
                                                var_i.name, var_j.name, init_sum
                                            );
                                        }
                                        return blocking_formula;
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }

        // Phase 0: Relational equality/disequality generalization (try FIRST)
        //
        // This should happen BEFORE other weakening phases because:
        // 1. Relational patterns (D=E or D!=E) are more powerful than point constraints
        // 2. Other phases weaken point constraints (D=1 -> D>0), losing the pattern info
        // 3. If D!=E is inductive, it blocks infinite states vs. just one
        // NOTE: Do NOT re-initialize from conjuncts - use current_conjuncts from Phase -1
        if self.config.use_relational_equality && current_conjuncts.len() >= 2 {
            if let Some(relational) =
                self.try_relational_equality_generalization(&current_conjuncts, predicate, level)
            {
                // Don't short-circuit: later phases (especially init-bound weakening) can turn
                // remaining point constraints into range lemmas and avoid point enumeration.
                current_conjuncts = relational.collect_conjuncts();
                if current_conjuncts.is_empty() {
                    return state.clone();
                }
            }
        }

        // Phase 0aa: anchored disjunctive affine equality generalization (#431)
        //
        // If we already know an affine equality such as `2*A - B = 0`, and the blocked
        // state suggests the same linear form with a nearby different constant, try a
        // two-branch lemma like `(2*A - B = -1) OR (2*A - B = 0)`. This keeps the
        // implementation narrow while covering the `B = 2*A OR B = 2*A+1` pattern.
        if current_conjuncts.len() >= 2 {
            if let Some(disjunctive) =
                self.try_disjunctive_affine_generalization(&current_conjuncts, predicate, level)
            {
                return disjunctive;
            }
        }

        // Phase 0a: Single-variable range generalization (try BEFORE implication)
        //
        // For each equality (var = val) where val is outside init bounds, try to
        // generalize to a range constraint. This is stronger than two-variable
        // implication because it blocks an infinite set of states with one lemma.
        // Example: For B7 fibonacci, if fib_n=0 and init has fib_n=1, block (fib_n < 1)
        // which gives invariant (fib_n >= 1).
        {
            let init_values = self.get_init_values(predicate);

            for conjunct in &current_conjuncts {
                if let Some((var, val)) = Self::extract_equality(conjunct) {
                    if let Some(init_bounds) = init_values.get(&var.name) {
                        // Try range blocking if value is outside init bounds
                        //
                        // IMPORTANT: Only generalize LOWER bounds based on init. Many benchmarks
                        // initialize loop counters at 0 and then monotonically increase them.
                        // Generalizing an observed value `val > init_max` to `(var > init_max)`
                        // would learn invariants like `var <= 0`, which is typically false.
                        let range_formula = if val < init_bounds.min {
                            // val is below init min: try blocking (var < init_min)
                            // Invariant: var >= init_min
                            Some(ChcExpr::lt(
                                ChcExpr::var(var.clone()),
                                ChcExpr::Int(init_bounds.min),
                            ))
                        } else {
                            None
                        };

                        if let Some(range_blocking) = range_formula {
                            if self.is_inductive_blocking(&range_blocking, predicate, level) {
                                if self.config.verbose {
                                    safe_eprintln!(
                                        "PDR: Phase 0a single-var range generalization: {} (val={}, init=[{},{}])",
                                        range_blocking, val, init_bounds.min, init_bounds.max
                                    );
                                }
                                // Found a strong single-variable range invariant - use it!
                                return range_blocking;
                            }
                        }
                    }
                }
            }
        }

        // Phase 0b: Implication generalization (delegated to generalization_implication.rs)
        if let Some(result) =
            self.generalize_phase_implication(&current_conjuncts, predicate, level)
        {
            return result;
        }

        // Phase 0c: Blocked-cube modular residue strengthening (#1362)
        //
        // Use the current blocked cube plus recent blocked cubes for the same
        // predicate as a signal for modular structure. When an integer variable
        // repeatedly appears with the same residue modulo 2 or 3, try the
        // corresponding modular blocking cube.
        if let Some(blocking_formula) =
            self.try_modular_history_generalization(state, predicate, level)
        {
            return blocking_formula;
        }

        // Phase 0d: Inequality-pair disjunctive blocking
        //
        // For each pair of equalities (vi = ki, vj = kj), try blocking with
        // inequality pairs: (vi <= ki AND vj >= kj), producing invariant lemma
        // NOT(vi <= ki AND vj >= kj) = (vi > ki OR vj < kj).
        //
        // This is the exact pattern Z3 Spacer produces via MBP/Farkas interpolation
        // for per-constant blocking lemmas. When Farkas interpolation fails (e.g.,
        // no UNSAT cores available), this heuristic approximates the same result.
        //
        // Example: s_multipl_24 needs invariant (A > 3 OR B < 3).
        // Given blocking cube {A=3, B=3}, this phase tries (A <= 3 AND B >= 3)
        // as blocking formula, producing the invariant (A > 3 OR B < 3).
        if current_conjuncts.len() >= 2 {
            let equalities: Vec<(ChcVar, i128)> = current_conjuncts
                .iter()
                .filter_map(Self::extract_equality)
                .collect();

            if equalities.len() >= 2 {
                for i in 0..equalities.len() {
                    for j in 0..equalities.len() {
                        if i == j {
                            continue;
                        }
                        let (var_i, val_i) = &equalities[i];
                        let (var_j, val_j) = &equalities[j];

                        // Try: (vi <= ki AND vj >= kj)
                        // Invariant lemma: (vi > ki OR vj < kj)
                        let blocking = ChcExpr::and(
                            ChcExpr::le(ChcExpr::var(var_i.clone()), ChcExpr::Int(*val_i)),
                            ChcExpr::ge(ChcExpr::var(var_j.clone()), ChcExpr::Int(*val_j)),
                        );

                        let inductive_at_level =
                            self.is_inductive_blocking(&blocking, predicate, level);
                        if !inductive_at_level {
                            continue;
                        }
                        let inductive_at_1 =
                            level == 1 || self.is_inductive_blocking(&blocking, predicate, 1);
                        if !inductive_at_1 {
                            continue;
                        }
                        let self_inductive = if level == 1 {
                            self.is_self_inductive_blocking(&blocking, predicate)
                        } else {
                            true
                        };
                        if self_inductive {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Phase 0d inequality-pair: ({} <= {} AND {} >= {}) blocks region, invariant: ({} > {} OR {} < {})",
                                    var_i.name, val_i, var_j.name, val_j,
                                    var_i.name, val_i, var_j.name, val_j
                                );
                            }
                            return blocking;
                        }
                    }
                }
            }
        }

        // Phases 1a through pipeline (delegated to generalization_weakening.rs)
        self.generalize_weakening_and_pipeline(current_conjuncts, predicate, level)
    }
}
