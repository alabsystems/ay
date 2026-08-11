// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// Detect disjunctive (unary resource) scheduling patterns from FlatZinc
// int_lin_le_reif pairs and emit Constraint::Disjunctive for each machine.
//
// Pattern in jobshop FlatZinc:
//   int_lin_le_reif([1,-1], [s_i, s_j], -d_i, b_ij)  // s_i + d_i ≤ s_j when b_ij
//   int_lin_le_reif([1,-1], [s_j, s_i], -d_j, b_ji)  // s_j + d_j ≤ s_i when b_ji
//   bool_clause([b_ij, b_ji], [])                       // exactly one ordering
//
// Detection algorithm:
//   1. Collect all int_lin_le_reif with coeffs [1,-1] — these encode "s_a + d ≤ s_b"
//   2. Group by task-variable pairs: (s_a, s_b) and (s_b, s_a) form a disjunctive pair
//   3. Build disjunctive-pair graph: tasks connected by disjunctive pairs
//   4. Find cliques in the graph — each clique is a machine
//   5. Add Constraint::Disjunctive for each machine
//
// The int_lin_le_reif constraints are STILL translated normally (Big-M encoding
// provides the SAT-level OR choice). The Disjunctive propagator adds stronger
// bounds propagation via O(n log n) edge-finding.

use std::collections::{BTreeMap as HashMap, BTreeSet as HashSet};

use ay_cp::propagator::Constraint;
use ay_cp::variable::IntVarId;
use ay_flatzinc_parser::ast::{ConstraintItem, Expr, FznModel};

use super::CpContext;

#[derive(Debug, Clone, Copy)]
struct DisjunctiveHalf {
    constraint_idx: usize,
    var_a: IntVarId,
    var_b: IntVarId,
    dur: i64,
    indicator: IntVarId,
}

/// A disjunctive pair: tasks (s_a, d_a) and (s_b, d_b) cannot overlap.
#[derive(Debug)]
struct DisjunctivePair {
    var_a: IntVarId,
    var_b: IntVarId,
    dur_a: i64,
    dur_b: i64,
    half_a_idx: usize,
    half_b_idx: usize,
    clause_idx: usize,
}

impl CpContext {
    /// Pre-scan FlatZinc constraints for disjunctive scheduling patterns.
    /// Adds Constraint::Disjunctive for each detected machine (clique of
    /// pairwise-disjunctive tasks).
    ///
    /// Must be called AFTER variables are created but BEFORE constraint
    /// translation, since we need IntVarIds for the FlatZinc variable names.
    pub(super) fn detect_disjunctive(&mut self, model: &FznModel) -> HashSet<usize> {
        // Step 1: Collect int_lin_le_reif([1,-1], [s_a, s_b], -d_a, _)
        // These encode s_a - s_b ≤ -d_a, i.e., s_a + d_a ≤ s_b.
        let mut half_pairs: Vec<DisjunctiveHalf> = Vec::new();

        for (idx, c) in model.constraints.iter().enumerate() {
            if c.id != "int_lin_le_reif" {
                continue;
            }
            if let Some((var_a, var_b, dur, indicator)) = self.try_parse_disjunctive_half(c) {
                half_pairs.push(DisjunctiveHalf {
                    constraint_idx: idx,
                    var_a,
                    var_b,
                    dur,
                    indicator,
                });
            }
        }

        if half_pairs.is_empty() {
            return HashSet::new();
        }

        // Step 2: Find matching pairs.
        // For each (s_a, s_b, d_a), look for (s_b, s_a, d_b).
        let mut pair_map: HashMap<(IntVarId, IntVarId), DisjunctiveHalf> = HashMap::new();
        for half in &half_pairs {
            pair_map.insert((half.var_a, half.var_b), *half);
        }

        let mut pairs: Vec<DisjunctivePair> = Vec::new();
        let mut used_halves: HashSet<(IntVarId, IntVarId)> = HashSet::new();
        let bool_clauses = self.collect_disjunctive_bool_clauses(model);
        let var_use_counts = self.constraint_var_use_counts(model);
        let output_vars: HashSet<IntVarId> = self.output_var_ids().into_iter().collect();

        for half_a in &half_pairs {
            if used_halves.contains(&(half_a.var_a, half_a.var_b)) {
                continue;
            }
            if let Some(half_b) = pair_map.get(&(half_a.var_b, half_a.var_a)) {
                let clause_key = normalized_pair_key(half_a.indicator, half_b.indicator);
                let Some(&clause_idx) = bool_clauses.get(&clause_key) else {
                    continue;
                };
                if output_vars.contains(&half_a.indicator)
                    || output_vars.contains(&half_b.indicator)
                {
                    continue;
                }
                if var_use_counts.get(&half_a.indicator).copied().unwrap_or(0) != 2
                    || var_use_counts.get(&half_b.indicator).copied().unwrap_or(0) != 2
                {
                    continue;
                }

                used_halves.insert((half_a.var_a, half_a.var_b));
                used_halves.insert((half_b.var_a, half_b.var_b));
                pairs.push(DisjunctivePair {
                    var_a: half_a.var_a,
                    var_b: half_a.var_b,
                    dur_a: half_a.dur,
                    dur_b: half_b.dur,
                    half_a_idx: half_a.constraint_idx,
                    half_b_idx: half_b.constraint_idx,
                    clause_idx,
                });
            }
        }

        if pairs.is_empty() {
            return HashSet::new();
        }

        // Step 3: Build disjunctive-pair graph and find machines (cliques).
        // Each task variable has a duration that may vary by pair. For jobshop,
        // each task has a SINGLE consistent duration across all pairs on the
        // same machine. We verify this and extract it.
        let mut task_durations: HashMap<IntVarId, i64> = HashMap::new();
        let mut inconsistent_tasks: HashSet<IntVarId> = HashSet::new();
        let mut adj: HashMap<IntVarId, HashSet<IntVarId>> = HashMap::new();

        for p in &pairs {
            // A native disjunctive constraint has one processing time per
            // task. If generated pair constraints disagree, substituting a
            // first-seen duration would weaken or strengthen the model while
            // deleting its exact reified constraints. Mark the whole task
            // ineligible for reconstruction instead.
            for (var, duration) in [(p.var_a, p.dur_a), (p.var_b, p.dur_b)] {
                if duration < 0
                    || task_durations
                        .get(&var)
                        .is_some_and(|existing| *existing != duration)
                {
                    inconsistent_tasks.insert(var);
                } else {
                    task_durations.entry(var).or_insert(duration);
                }
            }

            adj.entry(p.var_a).or_default().insert(p.var_b);
            adj.entry(p.var_b).or_default().insert(p.var_a);
        }

        // Step 4: Greedy clique detection (same algorithm as detect_alldifferent).
        // For jobshop, each machine is a complete graph of n tasks.
        let mut vars_by_degree: Vec<(IntVarId, usize)> =
            adj.iter().map(|(&v, nbrs)| (v, nbrs.len())).collect();
        vars_by_degree.sort_by_key(|b| std::cmp::Reverse(b.1));

        let mut used: HashSet<IntVarId> = HashSet::new();
        let mut machines: Vec<Vec<IntVarId>> = Vec::new();

        for &(seed, _) in &vars_by_degree {
            if used.contains(&seed) {
                continue;
            }
            let seed_nbrs = match adj.get(&seed) {
                Some(n) => n,
                None => continue,
            };

            let mut clique = vec![seed];
            let mut candidates: Vec<IntVarId> = seed_nbrs
                .iter()
                .filter(|v| !used.contains(v))
                .copied()
                .collect();
            // Sort by degree descending for better cliques
            candidates.sort_by(|a, b| {
                adj.get(b)
                    .map_or(0, HashSet::len)
                    .cmp(&adj.get(a).map_or(0, HashSet::len))
            });

            for cand in candidates {
                let cand_nbrs = match adj.get(&cand) {
                    Some(n) => n,
                    None => continue,
                };
                if clique.iter().all(|m| cand_nbrs.contains(m)) {
                    clique.push(cand);
                }
            }

            if clique.len() >= 2 {
                if clique.iter().all(|v| !inconsistent_tasks.contains(v)) {
                    for &v in &clique {
                        used.insert(v);
                    }
                    machines.push(clique);
                }
            }
        }

        // Step 5: Add Constraint::Disjunctive for each machine.
        let mut skip_constraints = HashSet::new();
        for machine in &machines {
            let starts = machine.clone();
            let durations: Vec<i64> = machine
                .iter()
                .map(|v| *task_durations.get(v).expect("task must have duration"))
                .collect();
            self.engine
                .add_constraint(Constraint::Disjunctive { starts, durations });
        }

        for p in &pairs {
            let covered = machines
                .iter()
                .any(|machine| machine.contains(&p.var_a) && machine.contains(&p.var_b));
            if covered {
                skip_constraints.insert(p.half_a_idx);
                skip_constraints.insert(p.half_b_idx);
                skip_constraints.insert(p.clause_idx);
            }
        }

        if !machines.is_empty() {
            eprintln!(
                "detect_disjunctive: {} machines from {} disjunctive pairs ({} tasks total, skipped {} generated constraints)",
                machines.len(),
                pairs.len(),
                machines.iter().map(Vec::len).sum::<usize>(),
                skip_constraints.len()
            );
        }

        skip_constraints
    }

    /// Try to parse a single int_lin_le_reif as a disjunctive half-pair.
    ///
    /// Pattern: int_lin_le_reif([1,-1], [s_a, s_b], rhs, _)
    /// where rhs < 0, meaning s_a - s_b ≤ rhs, i.e., s_a + |rhs| ≤ s_b.
    /// Duration = -rhs.
    fn try_parse_disjunctive_half(
        &self,
        c: &ConstraintItem,
    ) -> Option<(IntVarId, IntVarId, i64, IntVarId)> {
        // Must have 4 args: coeffs, vars, rhs, indicator
        if c.args.len() != 4 {
            return None;
        }

        // Parse coefficients — must be [1, -1]
        let coeffs = self.resolve_const_int_array_opt(&c.args[0])?;
        if coeffs.len() != 2 || coeffs[0] != 1 || coeffs[1] != -1 {
            return None;
        }

        // Parse rhs — must be negative (encodes -duration)
        let rhs = self.eval_const_int(&c.args[2])?;
        if rhs >= 0 {
            return None;
        }

        // Parse variables
        let vars = self.resolve_var_array_opt(&c.args[1])?;
        if vars.len() != 2 {
            return None;
        }

        let dur = rhs.checked_neg()?;
        let indicator = self.resolve_var_opt(&c.args[3])?;
        Some((vars[0], vars[1], dur, indicator))
    }

    fn collect_disjunctive_bool_clauses(
        &self,
        model: &FznModel,
    ) -> HashMap<(IntVarId, IntVarId), usize> {
        let mut clauses = HashMap::new();
        for (idx, c) in model.constraints.iter().enumerate() {
            let Some((a, b)) = self.try_parse_disjunctive_bool_clause(c) else {
                continue;
            };
            clauses.insert(normalized_pair_key(a, b), idx);
        }
        clauses
    }

    fn try_parse_disjunctive_bool_clause(
        &self,
        c: &ConstraintItem,
    ) -> Option<(IntVarId, IntVarId)> {
        match c.id.as_str() {
            "bool_clause" => {
                if c.args.len() != 2 {
                    return None;
                }
                let pos = self.resolve_var_array_opt(&c.args[0])?;
                let neg = self.resolve_var_array_opt(&c.args[1])?;
                if pos.len() == 2 && neg.is_empty() {
                    Some((pos[0], pos[1]))
                } else {
                    None
                }
            }
            "bool_or" => {
                if c.args.len() != 3 || self.eval_const_int(&c.args[2])? != 1 {
                    return None;
                }
                Some((
                    self.resolve_var_opt(&c.args[0])?,
                    self.resolve_var_opt(&c.args[1])?,
                ))
            }
            _ => None,
        }
    }

    fn constraint_var_use_counts(&self, model: &FznModel) -> HashMap<IntVarId, usize> {
        let mut counts = HashMap::new();
        for c in &model.constraints {
            let mut vars = HashSet::new();
            for arg in &c.args {
                self.collect_expr_vars(arg, &mut vars);
            }
            for var in vars {
                *counts.entry(var).or_insert(0) += 1;
            }
        }
        counts
    }

    fn collect_expr_vars(&self, expr: &Expr, vars: &mut HashSet<IntVarId>) {
        match expr {
            Expr::Ident(name) => {
                if let Some(&var) = self.var_map.get(name) {
                    vars.insert(var);
                } else if let Some(array) = self.array_var_map.get(name) {
                    vars.extend(array.iter().copied());
                }
            }
            Expr::ArrayLit(elems) | Expr::SetLit(elems) => {
                for elem in elems {
                    self.collect_expr_vars(elem, vars);
                }
            }
            Expr::ArrayAccess(name, index) => {
                if let Some(array) = self.array_var_map.get(name) {
                    vars.extend(array.iter().copied());
                }
                self.collect_expr_vars(index, vars);
            }
            Expr::Annotation(annotation) => {
                if let ay_flatzinc_parser::ast::Annotation::Call(_, args) = annotation.as_ref() {
                    for arg in args {
                        self.collect_expr_vars(arg, vars);
                    }
                }
            }
            Expr::Bool(_)
            | Expr::Int(_)
            | Expr::Float(_)
            | Expr::Str(_)
            | Expr::IntRange(_, _)
            | Expr::EmptySet => {}
        }
    }

    /// Non-failing version of resolve_const_int_array.
    fn resolve_const_int_array_opt(&self, expr: &Expr) -> Option<Vec<i64>> {
        match expr {
            Expr::ArrayLit(elems) => {
                let mut result = Vec::with_capacity(elems.len());
                for e in elems {
                    result.push(self.eval_const_int(e)?);
                }
                Some(result)
            }
            Expr::Ident(name) => self.par_int_arrays.get(name).cloned(),
            _ => None,
        }
    }

    fn resolve_var_opt(&self, expr: &Expr) -> Option<IntVarId> {
        match expr {
            Expr::Ident(name) => self.var_map.get(name).copied(),
            _ => None,
        }
    }

    /// Non-failing version of resolve_var_array.
    fn resolve_var_array_opt(&self, expr: &Expr) -> Option<Vec<IntVarId>> {
        match expr {
            Expr::ArrayLit(elems) => {
                let mut result = Vec::with_capacity(elems.len());
                for e in elems {
                    if let Expr::Ident(name) = e {
                        result.push(*self.var_map.get(name)?);
                    } else {
                        return None;
                    }
                }
                Some(result)
            }
            Expr::Ident(name) => self.array_var_map.get(name).cloned(),
            _ => None,
        }
    }
}

fn normalized_pair_key(a: IntVarId, b: IntVarId) -> (IntVarId, IntVarId) {
    if a <= b {
        (a, b)
    } else {
        (b, a)
    }
}
