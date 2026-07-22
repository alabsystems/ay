// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Constraint compilation: pending Constraint → SAT clauses + propagators.
//!
//! Extracted from engine/mod.rs to keep file sizes manageable.

use std::collections::{BTreeMap as HashMap, BTreeSet as HashSet};

use crate::propagator::Constraint;
use crate::propagators::alldifferent::AllDifferentBounds;
use crate::propagators::alldifferent_ac::{AllDifferentAc, ALLDIFF_AC_DOMAIN_LIMIT};
use crate::propagators::cumulative::Cumulative;
use crate::propagators::disjunctive::Disjunctive;
use crate::propagators::element::Element;
use crate::propagators::linear::LinearLe;
use crate::propagators::linear_ne::LinearNotEqual;
use crate::propagators::shifted_alldifferent::ShiftedAllDifferentBounds;
use crate::propagators::table::Table;
use crate::variable::IntVarId;

use super::{CpSatEngine, LazyNeq, LAZY_NEQ_DOMAIN_THRESHOLD};

/// Threshold: skip pairwise SAT encoding for AllDifferent with >= this many vars.
/// Bounds propagation alone is sufficient; pairwise encoding is O(n²d).
const ALLDIFF_PAIRWISE_THRESHOLD: usize = 20;

impl CpSatEngine {
    /// Compile pending constraints into SAT clauses and propagators.
    ///
    /// AllDifferent: pairwise SAT clauses (eager) + bounds propagator (LCG).
    /// LinearLe: propagator only (bounds propagation with explanations).
    /// LinearEq: split into LeLinear + GeLinear propagators.
    pub(super) fn compile_constraints(&mut self) {
        for constraint in std::mem::take(&mut self.constraints) {
            match &constraint {
                Constraint::AllDifferent(vars) => {
                    // Check if AC propagator is applicable.
                    let use_ac = vars.len() >= 3
                        && vars
                            .iter()
                            .all(|&v| self.trail.domain_size(v) <= ALLDIFF_AC_DOMAIN_LIMIT as u64)
                        && vars.iter().any(|&v| {
                            let lb = self.trail.lb(v);
                            let ub = self.trail.ub(v);
                            let span = ub.saturating_sub(lb).saturating_add(1) as u64;
                            self.trail.domain_size(v) < span
                        });

                    if vars.len() < ALLDIFF_PAIRWISE_THRESHOLD {
                        self.encode_alldiff_pairwise(vars);
                    }
                    if vars.len() >= 2 {
                        let prop = AllDifferentBounds::new(vars.clone());
                        self.dirty.push(true);
                        self.propagators.push(Box::new(prop));
                    }
                    // Pigeon-hole clauses for n-over-n AllDifferent (Chuffed
                    // alldiff_cheat, alldiff.cpp:41-53). When n variables
                    // cover exactly n values, each value must be taken.
                    // In order encoding, we add two families of clauses:
                    //   OR_i [x_i >= v]       — at least one var >= v
                    //   OR_i NOT [x_i >= v+1] — at least one var <= v
                    // These give the SAT solver structural pigeon-hole
                    // knowledge that pure != decomposition lacks, enabling
                    // CDCL learning of Hall-set implications.
                    self.encode_alldiff_pigeon_hole(vars);

                    // Add AC propagator as a complement when all variable
                    // domains are small enough for matching-based reasoning.
                    // The cutoff uses sparse cardinality (`domain_size`)
                    // rather than interval width, so wide sparse domains
                    // like {1, 200} still enroll in AC. Dense domains stay
                    // on bounds propagation to avoid the matching overhead on
                    // large permutation-style models.
                    if use_ac {
                        let mut all_values = Vec::new();
                        for &v in vars {
                            all_values.extend(self.trail.values(v));
                        }
                        all_values.sort_unstable();
                        all_values.dedup();
                        let ac_prop = AllDifferentAc::new(vars.clone(), all_values);
                        self.dirty.push(true);
                        self.propagators.push(Box::new(ac_prop));
                    }
                }
                Constraint::LinearLe { coeffs, vars, rhs } => {
                    let prop = LinearLe::new(coeffs.clone(), vars.clone(), *rhs);
                    self.dirty.push(true);
                    self.propagators.push(Box::new(prop));
                }
                Constraint::LinearEq { coeffs, vars, rhs } => {
                    let prop_le = LinearLe::new(coeffs.clone(), vars.clone(), *rhs);
                    self.dirty.push(true);
                    self.propagators.push(Box::new(prop_le));
                    let neg_coeffs: Vec<i64> = coeffs.iter().map(|c| -c).collect();
                    let prop_ge = LinearLe::new(neg_coeffs, vars.clone(), -*rhs);
                    self.dirty.push(true);
                    self.propagators.push(Box::new(prop_ge));
                }
                Constraint::LinearGe { coeffs, vars, rhs } => {
                    let neg_coeffs: Vec<i64> = coeffs.iter().map(|c| -c).collect();
                    let prop = LinearLe::new(neg_coeffs, vars.clone(), -*rhs);
                    self.dirty.push(true);
                    self.propagators.push(Box::new(prop));
                }
                Constraint::Table { vars, tuples } => {
                    let prop = Table::new(vars.clone(), tuples.clone());
                    self.dirty.push(true);
                    self.propagators.push(Box::new(prop));
                }
                Constraint::Element {
                    index,
                    array,
                    result,
                } => {
                    let prop = Element::new(*index, array.clone(), *result);
                    self.dirty.push(true);
                    self.propagators.push(Box::new(prop));
                }
                Constraint::Cumulative {
                    starts,
                    durations,
                    demands,
                    capacity,
                } => {
                    let prop = Cumulative::new(
                        starts.clone(),
                        durations.clone(),
                        demands.clone(),
                        *capacity,
                    );
                    self.dirty.push(true);
                    self.propagators.push(Box::new(prop));
                }
                Constraint::PairwiseNeq { x, y, offset } => {
                    let (lb_x, ub_x) = self.encoder.var_bounds(*x);
                    let (lb_y, ub_y) = self.encoder.var_bounds(*y);
                    let overlap = (ub_x - offset).min(ub_y) - (lb_x - offset).max(lb_y) + 1;
                    if overlap > LAZY_NEQ_DOMAIN_THRESHOLD {
                        self.lazy_neqs.push(LazyNeq {
                            x: *x,
                            y: *y,
                            offset: *offset,
                        });
                    } else {
                        self.encode_pairwise_neq(*x, *y, *offset);
                    }
                }
                Constraint::Circuit(vars) => self.encode_circuit(vars),
                Constraint::Inverse { x, y } => self.encode_inverse(x, y),
                Constraint::BoolClause { pos, neg } => self.encode_bool_clause(pos, neg),
                Constraint::Abs { result, arg } => self.encode_abs(*result, *arg),
                Constraint::Maximum { result, args } => self.encode_maximum(*result, args),
                Constraint::Minimum { result, args } => self.encode_minimum(*result, args),
                Constraint::Diffn { x, y, dx, dy } => self.encode_diffn(x, y, dx, dy),
                Constraint::LinearNotEqual { coeffs, vars, rhs } => {
                    let prop = LinearNotEqual::new(coeffs.clone(), vars.clone(), *rhs);
                    self.dirty.push(true);
                    self.propagators.push(Box::new(prop));
                }
                Constraint::Disjunctive { starts, durations } => {
                    let prop = Disjunctive::new(starts.clone(), durations.clone());
                    self.dirty.push(true);
                    self.propagators.push(Box::new(prop));
                }
            }
        }
    }

    /// Detect AllDifferent patterns from PairwiseNeq decompositions.
    ///
    /// FlatZinc decomposes `alldifferent(xs)` into O(n²) `int_ne(x_i, x_j)`
    /// constraints (offset=0). We reconstruct the original AllDifferent by
    /// finding cliques in the neq graph: if n variables are pairwise distinct,
    /// that's an AllDifferent constraint.
    ///
    /// Uses greedy clique detection: sort by degree, greedily extend cliques.
    /// Replaces pairwise neqs with a single AllDifferent constraint that
    /// enables O(n log n) bounds propagation via Hall intervals.
    pub(super) fn detect_alldifferent(&mut self) {
        // Build adjacency for offset-0 PairwiseNeq edges
        let mut neq_edges: HashMap<IntVarId, HashSet<IntVarId>> = HashMap::new();

        for c in &self.constraints {
            if let Constraint::PairwiseNeq { x, y, offset } = c {
                if *offset == 0 {
                    neq_edges.entry(*x).or_default().insert(*y);
                    neq_edges.entry(*y).or_default().insert(*x);
                }
            }
        }

        if neq_edges.is_empty() {
            return;
        }

        // Sort variables by degree (descending) for greedy clique detection
        let mut vars_by_degree: Vec<(IntVarId, usize)> = neq_edges
            .iter()
            .map(|(&v, neighbors)| (v, neighbors.len()))
            .collect();
        vars_by_degree.sort_by_key(|b| std::cmp::Reverse(b.1));

        let mut used: HashSet<IntVarId> = HashSet::new();
        let mut cliques: Vec<Vec<IntVarId>> = Vec::new();

        for &(seed, _) in &vars_by_degree {
            if used.contains(&seed) {
                continue;
            }
            let seed_neighbors = match neq_edges.get(&seed) {
                Some(n) => n,
                None => continue,
            };

            // Build clique greedily: add variables connected to all current members
            let mut clique = vec![seed];
            let mut candidates: Vec<IntVarId> = seed_neighbors
                .iter()
                .filter(|v| !used.contains(v))
                .copied()
                .collect();
            // Sort candidates by degree (descending) for better cliques
            candidates.sort_by(|a, b| {
                neq_edges
                    .get(b)
                    .map_or(0, HashSet::len)
                    .cmp(&neq_edges.get(a).map_or(0, HashSet::len))
            });

            for cand in candidates {
                let cand_neighbors = match neq_edges.get(&cand) {
                    Some(n) => n,
                    None => continue,
                };
                // Check if cand is connected to all current clique members
                if clique.iter().all(|m| cand_neighbors.contains(m)) {
                    clique.push(cand);
                }
            }

            if clique.len() >= 3 {
                for &v in &clique {
                    used.insert(v);
                }
                cliques.push(clique);
            }
        }

        if cliques.is_empty() {
            return;
        }

        // Remove consumed PairwiseNeq constraints and add AllDifferent
        let mut remove_set: HashSet<usize> = HashSet::new();
        for (i, c) in self.constraints.iter().enumerate() {
            if let Constraint::PairwiseNeq { x, y, offset } = c {
                if *offset == 0 && used.contains(x) && used.contains(y) {
                    for clique in &cliques {
                        if clique.contains(x) && clique.contains(y) {
                            remove_set.insert(i);
                            break;
                        }
                    }
                }
            }
        }

        // Remove in reverse order to preserve indices
        let mut indices: Vec<usize> = remove_set.into_iter().collect();
        indices.sort_unstable();
        for &i in indices.iter().rev() {
            self.constraints.swap_remove(i);
        }

        // Add reconstructed AllDifferent constraints
        for clique in cliques {
            self.constraints.push(Constraint::AllDifferent(clique));
        }
    }

    /// Detect shifted AllDifferent patterns from non-zero-offset PairwiseNeq.
    ///
    /// Queens diagonal constraints decompose as `int_lin_ne([1,-1], [q_i, q_j], i-j)`
    /// producing PairwiseNeq with offset = i-j. If n variables form a complete
    /// clique under a consistent shift assignment, that's `alldiff(q[k] + shift[k])`.
    pub(super) fn detect_shifted_alldifferent(&mut self) {
        let mut edge_set: HashMap<(IntVarId, IntVarId), HashSet<i64>> = HashMap::new();
        let mut var_edges: HashMap<IntVarId, Vec<(IntVarId, i64)>> = HashMap::new();

        for c in &self.constraints {
            if let Constraint::PairwiseNeq { x, y, offset } = c {
                if *offset == 0 {
                    continue;
                }
                var_edges.entry(*x).or_default().push((*y, *offset));
                var_edges.entry(*y).or_default().push((*x, -*offset));
                let (lo, hi, canon) = if *x < *y {
                    (*x, *y, *offset)
                } else {
                    (*y, *x, -*offset)
                };
                edge_set.entry((lo, hi)).or_default().insert(canon);
            }
        }

        if var_edges.is_empty() {
            return;
        }

        let has_edge = |a: IntVarId, b: IntVarId, offset: i64| -> bool {
            let (lo, hi, canon) = if a < b {
                (a, b, offset)
            } else {
                (b, a, -offset)
            };
            edge_set
                .get(&(lo, hi))
                .map_or(false, |s| s.contains(&canon))
        };

        let mut shifted_groups: Vec<(Vec<IntVarId>, Vec<i64>)> = Vec::new();
        let mut consumed: HashSet<(IntVarId, IntVarId, i64)> = HashSet::new();

        let all_vars: Vec<IntVarId> = var_edges.keys().copied().collect();
        for &seed in &all_vars {
            let seed_neighbors = match var_edges.get(&seed) {
                Some(e) => e.clone(),
                None => continue,
            };
            for &(first_nbr, first_offset) in &seed_neighbors {
                if consumed.contains(&(seed, first_nbr, first_offset)) {
                    continue;
                }
                let mut group: HashMap<IntVarId, i64> = HashMap::new();
                group.insert(seed, 0);
                group.insert(first_nbr, -first_offset);

                for &(nbr, offset) in &seed_neighbors {
                    if group.contains_key(&nbr) {
                        continue;
                    }
                    let candidate_shift = -offset;
                    let ok = group
                        .iter()
                        .all(|(&m, &ms)| m == seed || has_edge(m, nbr, ms - candidate_shift));
                    if ok {
                        group.insert(nbr, candidate_shift);
                    }
                }

                if group.len() < 3 {
                    continue;
                }

                let members: Vec<(IntVarId, i64)> = group.iter().map(|(&v, &s)| (v, s)).collect();
                let mut is_clique = true;
                'verify: for i in 0..members.len() {
                    for j in (i + 1)..members.len() {
                        if !has_edge(members[i].0, members[j].0, members[i].1 - members[j].1) {
                            is_clique = false;
                            break 'verify;
                        }
                    }
                }
                if !is_clique {
                    continue;
                }

                for i in 0..members.len() {
                    for j in (i + 1)..members.len() {
                        let (vi, si) = members[i];
                        let (vj, sj) = members[j];
                        consumed.insert((vi, vj, si - sj));
                        consumed.insert((vj, vi, sj - si));
                    }
                }

                let vars: Vec<IntVarId> = members.iter().map(|&(v, _)| v).collect();
                // Negate shifts: the group assigns shift[v] such that the
                // PairwiseNeq offset between vi and vj equals si - sj, i.e.,
                // vi - vj != si - sj. The propagator enforces
                // alldiff(v[k] + s'[k]), meaning vi + s'i != vj + s'j, i.e.,
                // vi - vj != s'j - s'i = -(s'i - s'j). Setting s' = -s gives
                // vi - vj != si - sj, matching the original constraints.
                let shifts: Vec<i64> = members.iter().map(|&(_, s)| -s).collect();
                shifted_groups.push((vars, shifts));
            }
        }

        if shifted_groups.is_empty() {
            return;
        }

        let mut remove_set: HashSet<usize> = HashSet::new();
        for (i, c) in self.constraints.iter().enumerate() {
            if let Constraint::PairwiseNeq { x, y, offset } = c {
                if *offset != 0 && consumed.contains(&(*x, *y, *offset)) {
                    remove_set.insert(i);
                }
            }
        }
        let mut indices: Vec<usize> = remove_set.into_iter().collect();
        indices.sort_unstable();
        for &i in indices.iter().rev() {
            self.constraints.swap_remove(i);
        }

        for (vars, shifts) in shifted_groups {
            // Bounds-consistency propagator on original vars — no auxiliary
            // variables needed, O(n log n) propagation via Lopez-Ortiz
            // union-find in shifted space.
            //
            // AC via aux-var lifting is disabled: LinearLe linking only
            // propagates bounds, not domain holes. AllDifferentAc's
            // build_adjacency sees the full interval [lb, ub] for aux vars,
            // including phantom values not reachable from the original var.
            // This causes incorrect matching/SCC computations → false UNSAT.
            // Re-enabling requires either domain channeling or a native
            // shifted-AllDifferentAc propagator.
            let prop = ShiftedAllDifferentBounds::new(vars, shifts);
            self.dirty.push(true);
            self.propagators.push(Box::new(prop));
        }
    }

    /// Pairwise exclusion encoding for `x - y != offset`.
    ///
    /// For each value `vx` in dom(x) where `vx - offset` is in dom(y),
    /// add clause: ¬(x=vx ∧ y=vx-offset).
    /// In order encoding: ¬[x≥vx] ∨ [x≥vx+1] ∨ ¬[y≥vy] ∨ [y≥vy+1]
    ///
    /// This avoids auxiliary variables and propagators, producing O(d) clauses
    /// instead of 2 LinearLe propagators + 1 boolean indicator per constraint.
    fn encode_pairwise_neq(&mut self, x: IntVarId, y: IntVarId, offset: i64) {
        let (lb_x, ub_x) = self.encoder.var_bounds(x);
        let (lb_y, ub_y) = self.encoder.var_bounds(y);

        for vx in lb_x..=ub_x {
            let vy = vx - offset;
            if vy >= lb_y && vy <= ub_y {
                // ¬(x=vx ∧ y=vy) = ¬[x≥vx] ∨ [x≥vx+1] ∨ ¬[y≥vy] ∨ [y≥vy+1]
                let mut clause = Vec::with_capacity(4);
                clause.push(
                    self.encoder
                        .get_or_create_ge(&mut self.sat, x, vx)
                        .negated(),
                );
                if let Some(next_vx) = vx.checked_add(1) {
                    clause.push(self.encoder.get_or_create_ge(&mut self.sat, x, next_vx));
                }
                clause.push(
                    self.encoder
                        .get_or_create_ge(&mut self.sat, y, vy)
                        .negated(),
                );
                if let Some(next_vy) = vy.checked_add(1) {
                    clause.push(self.encoder.get_or_create_ge(&mut self.sat, y, next_vy));
                }
                self.sat.add_clause(clause);
            }
        }
    }

    /// Add pigeon-hole clauses for n-over-n AllDifferent constraints.
    ///
    /// When `|vars| == |union_of_domains|` (every value must be taken),
    /// adds two families of clauses per value v:
    ///   `OR_i [x_i >= v]`       — at least one variable is >= v
    ///   `OR_i NOT [x_i >= v+1]` — at least one variable is <= v
    ///
    /// Ported from Chuffed alldiff.cpp:41-53 (alldiff_cheat), adapted
    /// for order encoding. Chuffed uses direct equality literals; we use
    /// the weaker >= / <= formulation which still enables CDCL to derive
    /// Hall-set implications via unit propagation.
    fn encode_alldiff_pigeon_hole(&mut self, vars: &[IntVarId]) {
        if vars.len() < 3 {
            return;
        }

        // Compute union of all variable domains.
        let mut all_values: Vec<i64> = Vec::new();
        for &v in vars {
            all_values.extend(self.trail.values(v));
        }
        all_values.sort_unstable();
        all_values.dedup();

        // Only add pigeon-hole clauses for n-over-n (exact cover).
        if all_values.len() != vars.len() {
            return;
        }

        // For each value v: OR_i [x_i >= v] (at least one var >= v).
        // Skip v = all_values[0] (the minimum) since [x >= lb] is always
        // true for all variables — the clause is a tautology.
        for &v in &all_values[1..] {
            let mut clause = Vec::with_capacity(vars.len());
            for &var in vars {
                let (lb, ub) = self.encoder.var_bounds(var);
                if v > ub + 1 {
                    // Variable can never be >= v; skip.
                    continue;
                }
                if v <= lb {
                    // [x >= v] is always true when lb >= v → clause is tautology.
                    clause.clear();
                    break;
                }
                let lit = self.encoder.get_or_create_ge(&mut self.sat, var, v);
                clause.push(lit);
            }
            if !clause.is_empty() {
                self.sat.add_clause(clause);
            }
        }

        // For each value v: OR_i NOT [x_i >= v+1] = OR_i [x_i <= v]
        // (at least one var <= v). Skip v = last value (the maximum)
        // since [x <= ub] is always true — the clause is a tautology.
        let last_idx = all_values.len() - 1;
        for &v in &all_values[..last_idx] {
            let mut clause = Vec::with_capacity(vars.len());
            for &var in vars {
                let (lb, ub) = self.encoder.var_bounds(var);
                if v < lb - 1 {
                    // Variable is always > v; skip.
                    continue;
                }
                if v >= ub {
                    // [x <= v] is always true when ub <= v → clause is tautology.
                    clause.clear();
                    break;
                }
                let lit = self.encoder.get_or_create_ge(&mut self.sat, var, v + 1);
                clause.push(lit.negated());
            }
            if !clause.is_empty() {
                self.sat.add_clause(clause);
            }
        }
    }
}
