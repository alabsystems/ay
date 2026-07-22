// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Discover bound invariants proactively before the PDR loop starts.
    ///
    /// For each predicate with fact clauses, finds integer variables where:
    /// 1. The variable has a constant initial value
    /// 2. The variable is monotonically non-decreasing (never goes below init)
    ///    OR monotonically non-increasing (never goes above init)
    ///
    /// Such bound invariants are added as lemmas at level 1.
    /// Example: For s_disj_ite_05, B starts at 50 and only increases, so B >= 50.
    pub(in crate::pdr::solver) fn discover_bound_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        for pred in &predicates {
            // Skip predicates without fact clauses (no initial state)
            if !self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Get initial values for this predicate
            let init_values = self.get_init_values(pred.id);

            // Check each integer variable for monotonicity
            for var in &canonical_vars {
                if self.is_cancelled() {
                    return;
                }
                // Only check integer variables
                if !matches!(var.sort, ChcSort::Int) {
                    continue;
                }

                // Get the initial bounds (constant or range)
                let init_bounds = match init_values.get(&var.name) {
                    Some(bounds) if bounds.is_valid() => bounds,
                    _ => continue,
                };

                // Case 1: Constant initial value (min == max)
                if init_bounds.min == init_bounds.max {
                    let init_val = init_bounds.min;

                    // Check if variable is monotonically non-decreasing (var >= init_val)
                    if self.is_var_non_decreasing(pred.id, var, init_val) {
                        let bound_invariant =
                            ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(init_val));

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Discovered lower bound invariant for pred {}: {} >= {}",
                                pred.id.index(),
                                var.name,
                                init_val
                            );
                        }

                        // Add to frame 1
                        self.add_discovered_invariant(pred.id, bound_invariant, 1);
                    }

                    // Check if variable is monotonically non-increasing (var <= init_val)
                    if self.is_var_non_increasing(pred.id, var, init_val) {
                        let bound_invariant =
                            ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(init_val));

                        if self.config.verbose {
                            safe_eprintln!(
                                "PDR: Discovered upper bound invariant for pred {}: {} <= {}",
                                pred.id.index(),
                                var.name,
                                init_val
                            );
                        }

                        // Add to frame 1
                        self.add_discovered_invariant(pred.id, bound_invariant, 1);
                    }
                }
                // Case 2: Range initial value (min != max but finite bounds)
                else {
                    // For range bounds, check if the bounds are preserved as invariants
                    // Check lower bound if finite: var >= min is preserved if non-decreasing from min
                    if init_bounds.min > i128::MIN
                        && self.is_var_non_decreasing(pred.id, var, init_bounds.min)
                    {
                        let bound_invariant =
                            ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(init_bounds.min));

                        if self.config.verbose {
                            safe_eprintln!(
                                    "PDR: Discovered range lower bound invariant for pred {}: {} >= {} (init range [{}, {}])",
                                    pred.id.index(),
                                    var.name,
                                    init_bounds.min,
                                    init_bounds.min,
                                    init_bounds.max
                                );
                        }

                        self.add_discovered_invariant(pred.id, bound_invariant, 1);
                    }

                    // Check upper bound if finite: var <= max is preserved if non-increasing from max
                    if init_bounds.max < i128::MAX
                        && self.is_var_non_increasing(pred.id, var, init_bounds.max)
                    {
                        let bound_invariant =
                            ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(init_bounds.max));

                        if self.config.verbose {
                            safe_eprintln!(
                                    "PDR: Discovered range upper bound invariant for pred {}: {} <= {} (init range [{}, {}])",
                                    pred.id.index(),
                                    var.name,
                                    init_bounds.max,
                                    init_bounds.min,
                                    init_bounds.max
                                );
                        }

                        self.add_discovered_invariant(pred.id, bound_invariant, 1);
                    }
                }
            }
        }

        // Phase 2: Propagate bound invariants to predicates without facts
        // Similar to how relational invariants are propagated
        self.propagate_bound_invariants();

        // Phase 3: Discover ITE toggle bounds (var ∈ {0, 1} from ite patterns)
        self.discover_ite_toggle_bounds();

        // Phases 4-7 (scaled difference bounds, sum bounds, loop exit bounds,
        // entry guard bounds) are expensive O(n^2) passes that do not depend on
        // other frame lemmas. They are run once after the fixpoint loop converges
        // via discover_bound_invariants_post_fixpoint() to avoid redundant work.
    }

    /// Expensive O(n^2) bound discovery passes that do not depend on other frame lemmas.
    /// Run once after the startup fixpoint loop converges, not per-iteration.
    ///
    /// This includes: scaled difference bounds, sum bounds, loop exit bounds,
    /// scaled loop exit bounds, and entry guard bounds.
    pub(in crate::pdr::solver) fn discover_bound_invariants_post_fixpoint(&mut self) {
        // Phase 4: Discover scaled difference bounds (B - k*A >= c)
        if self.config.use_scaled_difference_bounds {
            let _tb = ay_core::time::Instant::now();
            self.discover_scaled_difference_bounds();
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: discover_scaled_difference_bounds took {:?}",
                    _tb.elapsed()
                );
            }
        }

        // Phase 5: Discover sum bounds (A + B >= c)
        let _tb = ay_core::time::Instant::now();
        self.discover_sum_bounds();
        if self.config.verbose {
            safe_eprintln!("PDR: discover_sum_bounds took {:?}", _tb.elapsed());
        }

        // Phase 5.5: Discover sum upper bounds (A + B <= c)
        // Together with Phase 5, this enables discovering sum equalities
        // (e.g., A + B = 0) which are critical for benchmarks like s_mutants_21
        // where opposite-direction transitions preserve the sum.
        let _tb = ay_core::time::Instant::now();
        self.discover_sum_upper_bounds();
        if self.config.verbose {
            safe_eprintln!("PDR: discover_sum_upper_bounds took {:?}", _tb.elapsed());
        }

        // Phase 6: Discover loop exit bounds from self-loop guards
        let _tb = ay_core::time::Instant::now();
        self.discover_loop_exit_bounds();
        if self.config.verbose {
            safe_eprintln!("PDR: discover_loop_exit_bounds took {:?}", _tb.elapsed());
        }

        // Phase 6.5: Discover scaled loop exit bounds
        let _tb = ay_core::time::Instant::now();
        self.discover_scaled_loop_exit_bounds();
        if self.config.verbose {
            safe_eprintln!(
                "PDR: discover_scaled_loop_exit_bounds took {:?}",
                _tb.elapsed()
            );
        }

        // Phase 7: Discover entry guard bounds from cross-predicate transitions
        let _tb = ay_core::time::Instant::now();
        self.discover_entry_guard_bounds();
        if self.config.verbose {
            safe_eprintln!("PDR: discover_entry_guard_bounds took {:?}", _tb.elapsed());
        }
    }

    /// Discover upper bounds from entry guards on cross-predicate transitions.
    ///
    /// For a transition P(A) -> Q(A, ...) with guard A < N, if A flows unchanged
    /// to Q's first argument and is preserved in Q's self-loop, then Q's first arg
    /// has upper bound N-1.
    ///
    /// This handles patterns like:
    /// - itp1(A) -> itp2(A, v) when A < 256: itp2.arg0 <= 255
    pub(in crate::pdr::solver) fn discover_entry_guard_bounds(&mut self) {
        if self.frames.len() <= 1 {
            return;
        }

        let predicates: Vec<_> = self.problem.predicates().to_vec();
        let mut entry_bounds: Vec<(PredicateId, ChcVar, i128)> = Vec::new();

        for target_pred in &predicates {
            // Skip predicates with fact clauses (they have direct init bounds)
            if self.predicate_has_facts(target_pred.id) {
                continue;
            }

            let target_canonical = match self.canonical_vars(target_pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Look at incoming cross-predicate transitions
            for clause in self.problem.clauses_defining(target_pred.id) {
                // Skip fact clauses
                if clause.body.predicates.is_empty() {
                    continue;
                }

                // Only handle simple transitions (single body predicate)
                if clause.body.predicates.len() != 1 {
                    continue;
                }

                let (source_pred, source_args) = &clause.body.predicates[0];

                // Only consider cross-predicate transitions
                if *source_pred == target_pred.id {
                    continue;
                }

                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };

                if head_args.len() != target_canonical.len() {
                    continue;
                }

                // Extract upper bounds from the transition constraint
                let constraint = clause
                    .body
                    .constraint
                    .clone()
                    .unwrap_or(ChcExpr::Bool(true));

                // Collect source/body variable names used in this transition.
                // #2492: Also extract constituent vars from expression body args
                let source_var_names: Vec<String> = source_args
                    .iter()
                    .flat_map(|arg| match arg {
                        ChcExpr::Var(v) => vec![v.name.clone()],
                        expr => expr.vars().into_iter().map(|v| v.name).collect(),
                    })
                    .collect();

                // For each head arg, try to derive an upper bound from guard constraints.
                // Supports direct variables and simple shifted expressions (e.g., x + 1).
                for (head_idx, head_arg) in head_args.iter().enumerate() {
                    let Some(target_var) = target_canonical.get(head_idx) else {
                        continue;
                    };
                    if !matches!(target_var.sort, ChcSort::Int) {
                        continue;
                    }

                    // Verify the variable is preserved in target's self-loop
                    // (i.e., doesn't increase in self-transitions).
                    if !self.is_var_preserved_in_self_loop(target_pred.id, head_idx) {
                        continue;
                    }

                    let mut derived_upper: Option<i128> = None;
                    for source_var in &source_var_names {
                        let Some(source_upper) =
                            Self::extract_upper_bound_for_var(&constraint, source_var)
                        else {
                            continue;
                        };
                        let Some(offset) =
                            Self::get_offset_from_head_arg(head_arg, source_var, &constraint)
                        else {
                            continue;
                        };

                        let candidate = source_upper.saturating_add(offset);
                        derived_upper = Some(match derived_upper {
                            Some(existing) => existing.min(candidate),
                            None => candidate,
                        });
                    }

                    if let Some(upper_bound) = derived_upper {
                        entry_bounds.push((target_pred.id, target_var.clone(), upper_bound));
                    }
                }
            }
        }

        // Add entry bounds as lemmas
        for (pred_id, var, bound) in entry_bounds {
            let bound_invariant = ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(bound));

            // Check if already known
            let already_known = self.frames[1]
                .lemmas
                .iter()
                .any(|l| l.predicate == pred_id && l.formula == bound_invariant);

            if !already_known {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: Discovered entry guard upper bound for pred {}: {} <= {}",
                        pred_id.index(),
                        var.name,
                        bound
                    );
                }

                self.add_discovered_invariant(pred_id, bound_invariant, 1);
            }
        }
    }
}
