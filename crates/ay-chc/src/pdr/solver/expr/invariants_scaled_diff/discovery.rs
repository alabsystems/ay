// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::solver::PdrSolver;
use crate::{ChcExpr, ChcSort, ChcVar, Predicate, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl PdrSolver {
    /// Discover scaled difference invariants proactively.
    ///
    /// For each predicate with fact clauses, finds triples of integer variables
    /// `(vi, vj, vk)` where:
    /// 1. `vi - vj = k * vk` for some constant `k` in the initial state
    /// 2. The relationship is preserved by all self-transitions
    pub(in crate::pdr::solver) fn discover_scaled_difference_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Track discovered invariants: (pred_id, var_i_idx, var_j_idx, var_k_idx, coeff)
        let mut discovered_scaled_diffs: Vec<(PredicateId, usize, usize, usize, i128)> = Vec::new();

        // Phase 1: Discover scaled difference invariants from predicates with fact clauses
        for pred in &predicates {
            if !self.predicate_has_facts(pred.id) {
                continue;
            }
            if self.has_unrestricted_incoming_inter_predicate_transitions(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            let init_values = self.get_init_values(pred.id);
            let mult_relations = self.extract_init_multiplicative_relations(pred.id);

            self.discover_direct_multiplicative_scaled_diffs(
                pred.id,
                &canonical_vars,
                &init_values,
                &mult_relations,
                &mut discovered_scaled_diffs,
            );
            self.discover_unit_scaled_diffs(
                pred.id,
                &canonical_vars,
                &init_values,
                &mut discovered_scaled_diffs,
            );
            self.discover_constant_ratio_scaled_diffs(
                pred.id,
                &canonical_vars,
                &init_values,
                &mut discovered_scaled_diffs,
            );
            self.discover_zero_init_coeff_invariants(
                pred.id,
                &canonical_vars,
                &init_values,
                &mut discovered_scaled_diffs,
            );
        }

        self.propagate_scaled_difference_invariants(&predicates, &discovered_scaled_diffs);
    }

    fn discover_direct_multiplicative_scaled_diffs(
        &mut self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
        init_values: &FxHashMap<String, crate::pdr::config::InitIntBounds>,
        mult_relations: &[(String, i128, String)],
        discovered_scaled_diffs: &mut Vec<(PredicateId, usize, usize, usize, i128)>,
    ) {
        for (var_i_name, coeff, var_k_name) in mult_relations {
            if self.is_cancelled() {
                return;
            }
            let var_i_idx = canonical_vars.iter().position(|v| &v.name == var_i_name);
            let var_k_idx = canonical_vars.iter().position(|v| &v.name == var_k_name);

            let (var_i_idx, var_k_idx) = match (var_i_idx, var_k_idx) {
                (Some(i), Some(k)) => (i, k),
                _ => continue,
            };
            let var_i = &canonical_vars[var_i_idx];
            let var_k = &canonical_vars[var_k_idx];

            for (var_j_idx, var_j) in canonical_vars.iter().enumerate() {
                if var_j.name == var_i.name || var_j.name == var_k.name {
                    continue;
                }
                let _init_j = match init_values.get(&var_j.name) {
                    Some(bounds) if bounds.min == 0 && bounds.max == 0 => bounds,
                    _ => continue,
                };
                if !matches!(var_j.sort, ChcSort::Int) {
                    continue;
                }
                if !self.is_scaled_diff_preserved(predicate, var_i, var_j, var_k, *coeff) {
                    continue;
                }

                discovered_scaled_diffs.push((predicate, var_i_idx, var_j_idx, var_k_idx, *coeff));
                let scaled_diff_invariant =
                    build_scaled_diff_invariant(var_i, var_j, var_k, *coeff);
                self.log_discovered_scaled_diff(
                    predicate,
                    "Discovered scaled difference invariant",
                    var_i,
                    var_j,
                    var_k,
                    *coeff,
                );
                self.add_discovered_invariant(predicate, scaled_diff_invariant, 1);
            }
        }
    }

    fn discover_unit_scaled_diffs(
        &mut self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
        init_values: &FxHashMap<String, crate::pdr::config::InitIntBounds>,
        discovered_scaled_diffs: &mut Vec<(PredicateId, usize, usize, usize, i128)>,
    ) {
        if canonical_vars.len() > 8 {
            return;
        }

        const MAX_UNIT_DIFF_CANDIDATES: usize = 64;
        let mut checked = 0usize;

        'unit_diff: for i in 0..canonical_vars.len() {
            let var_i = &canonical_vars[i];
            if !matches!(var_i.sort, ChcSort::Int) {
                continue;
            }
            let init_i = match init_values.get(&var_i.name) {
                Some(b) if b.min == b.max => b.min,
                _ => continue,
            };

            for j in 0..canonical_vars.len() {
                if i == j {
                    continue;
                }
                let var_j = &canonical_vars[j];
                if !matches!(var_j.sort, ChcSort::Int) {
                    continue;
                }
                let init_j = match init_values.get(&var_j.name) {
                    Some(b) if b.min == b.max => b.min,
                    _ => continue,
                };

                for (k_idx, var_k) in canonical_vars.iter().enumerate() {
                    if k_idx == i || k_idx == j {
                        continue;
                    }
                    if checked >= MAX_UNIT_DIFF_CANDIDATES {
                        break 'unit_diff;
                    }
                    checked += 1;
                    if !matches!(var_k.sort, ChcSort::Int) {
                        continue;
                    }
                    let init_k = match init_values.get(&var_k.name) {
                        Some(b) if b.min == b.max => b.min,
                        _ => continue,
                    };

                    let init_lhs = match init_i.checked_sub(init_j) {
                        Some(d) => d,
                        None => continue,
                    };
                    if init_lhs == 0 && init_k == 0 {
                        continue;
                    }
                    let coeff = if init_lhs == init_k {
                        1
                    } else if init_k != 0 && init_k != i128::MIN && init_lhs == -init_k {
                        -1
                    } else {
                        continue;
                    };

                    if discovered_scaled_diffs.iter().any(|&(p, ii, jj, kk, c)| {
                        p == predicate && ii == i && jj == j && kk == k_idx && c == coeff
                    }) {
                        continue;
                    }

                    if !self.is_scaled_diff_preserved(predicate, var_i, var_j, var_k, coeff) {
                        continue;
                    }

                    discovered_scaled_diffs.push((predicate, i, j, k_idx, coeff));
                    let scaled_diff_invariant =
                        build_scaled_diff_invariant(var_i, var_j, var_k, coeff);
                    self.log_discovered_scaled_diff(
                        predicate,
                        "Discovered unit scaled diff invariant",
                        var_i,
                        var_j,
                        var_k,
                        coeff,
                    );
                    self.add_discovered_invariant(predicate, scaled_diff_invariant, 1);
                }
            }
        }
    }

    fn discover_constant_ratio_scaled_diffs(
        &mut self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
        init_values: &FxHashMap<String, crate::pdr::config::InitIntBounds>,
        discovered_scaled_diffs: &mut Vec<(PredicateId, usize, usize, usize, i128)>,
    ) {
        for i in 0..canonical_vars.len() {
            for j in 0..canonical_vars.len() {
                if i == j {
                    continue;
                }

                let var_i = &canonical_vars[i];
                let var_j = &canonical_vars[j];
                if !matches!(var_i.sort, ChcSort::Int) || !matches!(var_j.sort, ChcSort::Int) {
                    continue;
                }

                let init_i = init_values.get(&var_i.name);
                let init_j = init_values.get(&var_j.name);
                let init_diff = match (init_i, init_j) {
                    (Some(bounds_i), Some(bounds_j))
                        if bounds_i.min == bounds_i.max && bounds_j.min == bounds_j.max =>
                    {
                        match bounds_i.min.checked_sub(bounds_j.min) {
                            Some(d) => d,
                            None => continue,
                        }
                    }
                    _ => continue,
                };
                if init_diff == 0 {
                    continue;
                }

                for (k_idx, var_k) in canonical_vars.iter().enumerate() {
                    if k_idx == i || k_idx == j {
                        continue;
                    }
                    if !matches!(var_k.sort, ChcSort::Int) {
                        continue;
                    }
                    let init_k = match init_values.get(&var_k.name) {
                        Some(bounds) if bounds.min == bounds.max && bounds.min != 0 => bounds,
                        _ => continue,
                    };
                    if init_k.min == -1 && init_diff == i128::MIN {
                        continue;
                    }
                    if init_diff % init_k.min != 0 {
                        continue;
                    }

                    let coeff = init_diff / init_k.min;
                    if coeff.unsigned_abs() < 2 || coeff.unsigned_abs() > 10 {
                        continue;
                    }
                    if !self.is_scaled_diff_preserved(predicate, var_i, var_j, var_k, coeff) {
                        continue;
                    }

                    discovered_scaled_diffs.push((predicate, i, j, k_idx, coeff));
                    let scaled_diff_invariant =
                        build_scaled_diff_invariant(var_i, var_j, var_k, coeff);
                    self.log_discovered_scaled_diff(
                        predicate,
                        "Discovered scaled difference invariant",
                        var_i,
                        var_j,
                        var_k,
                        coeff,
                    );
                    self.add_discovered_invariant(predicate, scaled_diff_invariant, 1);
                }
            }
        }
    }

    fn discover_zero_init_coeff_invariants(
        &mut self,
        predicate: PredicateId,
        canonical_vars: &[ChcVar],
        init_values: &FxHashMap<String, crate::pdr::config::InitIntBounds>,
        discovered_scaled_diffs: &mut Vec<(PredicateId, usize, usize, usize, i128)>,
    ) {
        if canonical_vars.len() > 8 {
            return;
        }

        let int_vars: Vec<(usize, &ChcVar)> = canonical_vars
            .iter()
            .enumerate()
            .filter(|(_, v)| matches!(v.sort, ChcSort::Int))
            .collect();

        if self.config.verbose {
            safe_eprintln!(
                "PDR: Method 3 zero-init scan for pred {}: {} int vars, init_values keys: {:?}",
                predicate.index(),
                int_vars.len(),
                init_values.keys().collect::<Vec<_>>()
            );
            for &(idx, v) in &int_vars {
                if let Some(b) = init_values.get(&v.name) {
                    safe_eprintln!("PDR:   var[{idx}] {} init=[{}, {}]", v.name, b.min, b.max);
                } else {
                    safe_eprintln!("PDR:   var[{idx}] {} init=NONE", v.name);
                }
            }
        }

        for &(i, var_i) in &int_vars {
            if self.is_cancelled() {
                return;
            }
            match init_values.get(&var_i.name) {
                Some(b) if b.min == b.max && b.min == 0 => {}
                _ => continue,
            }

            for &(k_idx, var_k) in &int_vars {
                if k_idx == i {
                    continue;
                }
                match init_values.get(&var_k.name) {
                    Some(b) if b.min == b.max && b.min == 0 => {}
                    _ => continue,
                }

                for coeff in [2i128, -2, 3, -3, 4, -4, 5, -5] {
                    if discovered_scaled_diffs.iter().any(|&(p, ii, _, kk, c)| {
                        p == predicate && ii == i && kk == k_idx && c == coeff
                    }) {
                        continue;
                    }
                    if !self.is_zero_init_coeff_preserved(predicate, var_i, var_k, coeff) {
                        continue;
                    }

                    discovered_scaled_diffs.push((predicate, i, i, k_idx, coeff));
                    let invariant = ChcExpr::eq(
                        ChcExpr::var(var_i.clone()),
                        ChcExpr::mul(ChcExpr::Int(coeff), ChcExpr::var(var_k.clone())),
                    );

                    if self.config.verbose {
                        safe_eprintln!(
                            "PDR: Discovered zero-init coefficient invariant for pred {}: {} = {} * {}",
                            predicate.index(),
                            var_i.name,
                            coeff,
                            var_k.name
                        );
                    }

                    self.add_discovered_invariant(predicate, invariant, 1);
                }
            }
        }
    }

    fn propagate_scaled_difference_invariants(
        &mut self,
        predicates: &[Predicate],
        discovered_scaled_diffs: &[(PredicateId, usize, usize, usize, i128)],
    ) {
        let mut propagation_candidates: Vec<(PredicateId, usize, usize, usize, i128, PredicateId)> =
            Vec::new();

        for pred in predicates {
            if self.predicate_has_facts(pred.id) {
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            for clause in self.problem.clauses_defining(pred.id) {
                if clause.body.predicates.len() != 1 {
                    continue;
                }

                let (body_pred, body_args) = &clause.body.predicates[0];
                if pred.id == *body_pred {
                    continue;
                }

                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, a) => a.as_slice(),
                    crate::ClauseHead::False => continue,
                };

                let mut body_to_head: FxHashMap<usize, usize> = FxHashMap::default();
                for (h_idx, head_arg) in head_args.iter().enumerate() {
                    for (b_idx, body_arg) in body_args.iter().enumerate() {
                        let is_match = match (head_arg, body_arg) {
                            (ChcExpr::Var(hv), ChcExpr::Var(bv)) => hv.name == bv.name,
                            (h, b) => h == b,
                        };
                        if is_match {
                            body_to_head.insert(b_idx, h_idx);
                        }
                    }
                }

                for &(src_pred, src_i, src_j, src_k, coeff) in discovered_scaled_diffs {
                    if src_pred != *body_pred {
                        continue;
                    }

                    let head_i = body_to_head.get(&src_i);
                    let head_j = body_to_head.get(&src_j);
                    let head_k = body_to_head.get(&src_k);
                    let (h_i, h_j, h_k) = match (head_i, head_j, head_k) {
                        (Some(&i), Some(&j), Some(&k)) => (i, j, k),
                        _ => continue,
                    };
                    if h_i >= canonical_vars.len()
                        || h_j >= canonical_vars.len()
                        || h_k >= canonical_vars.len()
                    {
                        continue;
                    }

                    propagation_candidates.push((pred.id, h_i, h_j, h_k, coeff, *body_pred));
                }
            }
        }

        for (target_pred, h_i, h_j, h_k, coeff, source_pred) in propagation_candidates {
            let canonical_vars = match self.canonical_vars(target_pred) {
                Some(v) => v.to_vec(),
                None => continue,
            };
            if h_i >= canonical_vars.len()
                || h_j >= canonical_vars.len()
                || h_k >= canonical_vars.len()
            {
                continue;
            }

            let var_i = &canonical_vars[h_i];
            let var_j = &canonical_vars[h_j];
            let var_k = &canonical_vars[h_k];
            if !self.is_scaled_diff_preserved(target_pred, var_i, var_j, var_k, coeff) {
                continue;
            }

            let scaled_diff_invariant = build_scaled_diff_invariant(var_i, var_j, var_k, coeff);
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: Propagated scaled diff invariant from pred {} to pred {}: {} - {} = {} * {}",
                    source_pred.index(),
                    target_pred.index(),
                    var_i.name,
                    var_j.name,
                    coeff,
                    var_k.name
                );
            }
            self.add_discovered_invariant(target_pred, scaled_diff_invariant, 1);
        }
    }

    fn log_discovered_scaled_diff(
        &self,
        predicate: PredicateId,
        label: &str,
        var_i: &ChcVar,
        var_j: &ChcVar,
        var_k: &ChcVar,
        coeff: i128,
    ) {
        if self.config.verbose {
            safe_eprintln!(
                "PDR: {label} for pred {}: {} - {} = {} * {}",
                predicate.index(),
                var_i.name,
                var_j.name,
                coeff,
                var_k.name
            );
        }
    }
}

fn build_scaled_diff_invariant(
    var_i: &ChcVar,
    var_j: &ChcVar,
    var_k: &ChcVar,
    coeff: i128,
) -> ChcExpr {
    let lhs = ChcExpr::sub(ChcExpr::var(var_i.clone()), ChcExpr::var(var_j.clone()));
    let rhs = ChcExpr::mul(ChcExpr::Int(coeff), ChcExpr::var(var_k.clone()));
    ChcExpr::eq(lhs, rhs)
}
