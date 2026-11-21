// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager SAT encoding for CP constraints.
//!
//! These methods encode constraints directly into SAT clauses using the
//! order encoding ([x >= v] literals). Used for constraints that don't
//! have dedicated propagator implementations: AllDifferent (pairwise),
//! BoolClause, Abs, Maximum, Minimum, Circuit (MTZ), and Inverse (channeling).

use crate::propagators::linear::LinearLe;
use crate::variable::IntVarId;

use super::CpSatEngine;

impl CpSatEngine {
    fn extend_not_equal_terms(
        &mut self,
        clause: &mut Vec<ay_sat::Literal>,
        var: IntVarId,
        value: i64,
    ) {
        let ge_value = self.encoder.get_or_create_ge(&mut self.sat, var, value);
        clause.push(ge_value.negated());
        if let Some(next_value) = value.checked_add(1) {
            clause.push(
                self.encoder
                    .get_or_create_ge(&mut self.sat, var, next_value),
            );
        }
    }

    /// Node numbering of a successor or inverse array: the nodes are
    /// `base..base + n`, and every value outside that range is forbidden
    /// here.
    ///
    /// Until 2026-11-19 the constraint carried no base: it was the smallest
    /// value in any of the variables' root domains (before 2026-11-18 the
    /// first variable's lower bound alone, which shifted every node number
    /// when that variable could not take the base: wrong UNSAT), so the
    /// meaning of the constraint depended on its domains. Values above the
    /// range had no clause before 2026-11-18, so a variable could take one
    /// freely.
    ///
    /// `false` when the nodes `base..base + n` are not all i64 values: no
    /// assignment can then be a permutation of them, and the model is
    /// unsatisfiable (an empty clause is added). Before 2026-11-19 that case
    /// panicked ("node range fits i64"), e.g. two successors over
    /// `[i64::MAX, i64::MAX]`.
    fn node_numbering(&mut self, vars: &[IntVarId], base: i64) -> bool {
        let Some(top) = i64::try_from(vars.len())
            .ok()
            .and_then(|n| base.checked_add(n.saturating_sub(1)))
        else {
            self.add_model_clause("node_numbering", Vec::new());
            return false;
        };
        for &var in vars {
            let (lb, ub) = self.encoder.var_bounds(var);
            if lb < base {
                let at_least_base = self.encoder.get_or_create_ge(&mut self.sat, var, base);
                self.add_model_clause("node_numbering", vec![at_least_base]);
            }
            if ub > top {
                // `top < ub <= i64::MAX`, so `top + 1` is an i64.
                let above = self.encoder.get_or_create_ge(&mut self.sat, var, top + 1);
                self.add_model_clause("node_numbering", vec![above.negated()]);
            }
        }
        true
    }

    /// Node `index` of an array numbered from `base`: an i64 whenever
    /// [`Self::node_numbering`] accepted the numbering.
    fn node(base: i64, index: usize) -> i64 {
        i64::try_from(index)
            .ok()
            .and_then(|i| base.checked_add(i))
            .expect("node_numbering checked that every node is an i64")
    }

    /// Pairwise encoding of alldifferent: for each pair (xi, xj),
    /// for each value v in intersection of domains: ¬(xi=v ∧ xj=v).
    pub(super) fn encode_alldiff_pairwise(&mut self, vars: &[IntVarId]) {
        for i in 0..vars.len() {
            for j in (i + 1)..vars.len() {
                let (lb_i, ub_i) = self.encoder.var_bounds(vars[i]);
                let (lb_j, ub_j) = self.encoder.var_bounds(vars[j]);
                let lb = lb_i.max(lb_j);
                let ub = ub_i.min(ub_j);

                for v in lb..=ub {
                    // ¬(xi=v ∧ xj=v) =
                    // ¬[xi >= v] ∨ [xi >= v+1] ∨ ¬[xj >= v] ∨ [xj >= v+1]
                    let mut clause = Vec::with_capacity(4);
                    self.extend_not_equal_terms(&mut clause, vars[i], v);
                    self.extend_not_equal_terms(&mut clause, vars[j], v);
                    self.add_model_clause("encode_alldiff_pairwise", clause);
                }
            }
        }
    }

    /// Encode BoolClause: at least one pos var ≥ 1 or one neg var ≤ 0.
    ///
    /// In order encoding: [x ≥ 1] for each positive, ¬[x ≥ 1] for each negative.
    pub(super) fn encode_bool_clause(&mut self, pos: &[IntVarId], neg: &[IntVarId]) {
        let mut clause = Vec::with_capacity(pos.len() + neg.len());
        for &var in pos {
            let lit = self.encoder.get_or_create_ge(&mut self.sat, var, 1);
            clause.push(lit);
        }
        for &var in neg {
            let lit = self.encoder.get_or_create_ge(&mut self.sat, var, 1);
            clause.push(lit.negated());
        }
        debug_assert!(
            !clause.is_empty(),
            "BUG: encode_bool_clause produced empty clause (empty pos + neg)"
        );
        if !clause.is_empty() {
            self.add_model_clause("encode_bool_clause", clause);
        }
    }

    /// Encode Abs: result = |arg|.
    ///
    /// Decomposed into: result >= arg, result >= -arg (via LinearLe propagators),
    /// and result <= |arg| via order encoding clauses.
    pub(super) fn encode_abs(&mut self, result: IntVarId, arg: IntVarId) {
        // result >= arg  ↔  -result + arg <= 0
        let prop1 = LinearLe::new(vec![-1, 1], vec![result, arg], 0);
        self.dirty.push(true);
        self.propagators.push(Box::new(prop1));
        // result >= -arg  ↔  -result - arg <= 0
        let prop2 = LinearLe::new(vec![-1, -1], vec![result, arg], 0);
        self.dirty.push(true);
        self.propagators.push(Box::new(prop2));
        // result <= |arg|: for each v > 0, [result >= v] → [arg >= v] ∨ [arg <= -v]
        // i.e. ¬[result >= v] ∨ [arg >= v] ∨ ¬[arg >= -v + 1]
        // For v <= lb(result) the clause at v = lb(result) implies the
        // others, so the thresholds start there: before 2026-11-19 they
        // started at 1, and a result domain against i64::MAX made the loop
        // run about 2^63 times.
        let (lb_r, ub_r) = self.encoder.var_bounds(result);
        for v in lb_r.max(1)..=ub_r {
            let r_ge_v = self.encoder.get_or_create_ge(&mut self.sat, result, v);
            let a_ge_v = self.encoder.get_or_create_ge(&mut self.sat, arg, v);
            let a_ge_neg_v_plus_1 = self.encoder.get_or_create_ge(&mut self.sat, arg, -v + 1);
            self.add_model_clause(
                "encode_abs",
                vec![r_ge_v.negated(), a_ge_v, a_ge_neg_v_plus_1.negated()],
            );
        }
    }

    /// Encode Maximum: result = max(args).
    ///
    /// Decomposed into: result >= each arg (propagators), and
    /// for each value v, [result >= v] → ∨_i [arg_i >= v] (SAT clauses).
    pub(super) fn encode_maximum(&mut self, result: IntVarId, args: &[IntVarId]) {
        for &arg in args {
            let prop = LinearLe::new(vec![-1, 1], vec![result, arg], 0);
            self.dirty.push(true);
            self.propagators.push(Box::new(prop));
        }
        // From v = lb(result) on: `result >= lb(result)` always holds, so
        // some argument must reach it. (Before 2026-11-18 the clauses started
        // at lb + 1, and none was added for a fixed result: `2 = max([1])`
        // was accepted.)
        let (lb_r, ub_r) = self.encoder.var_bounds(result);
        for v in lb_r..=ub_r {
            let r_ge_v = self.encoder.get_or_create_ge(&mut self.sat, result, v);
            let mut clause = vec![r_ge_v.negated()];
            for &arg in args {
                let a_ge_v = self.encoder.get_or_create_ge(&mut self.sat, arg, v);
                clause.push(a_ge_v);
            }
            self.add_model_clause("encode_maximum", clause);
        }
    }

    /// Encode Circuit: Hamiltonian cycle on n nodes.
    ///
    /// vars[i] = successor of node i (FlatZinc uses 1-based indexing).
    /// Encoding:
    /// 1. AllDifferent(vars) — each node has a unique successor
    /// 2. No self-loops: vars[i] != i+base
    /// 3. Subtour elimination via Table constraint on (vars[i], pos[i], pos[succ])
    ///    triples, where pos tracks position in the cycle.
    pub(super) fn encode_circuit(&mut self, vars: &[IntVarId], base: i64) {
        use crate::propagators::alldifferent::AllDifferentBounds;

        let n = vars.len();
        // 1. Node numbering (typically base 1 for FlatZinc). A single node
        // is its own successor: the numbering leaves it `base` alone.
        // (Before 2026-11-19 a single successor was not constrained.)
        if !self.node_numbering(vars, base) || n <= 1 {
            return;
        }

        // 2. AllDifferent on successor variables
        self.encode_alldiff_pairwise(vars);
        self.add_propagator(AllDifferentBounds::new(vars.to_vec()));

        // 3. No self-loops: vars[i] != i+base
        // Encoded as: ¬[vars[i] >= i+base] ∨ [vars[i] >= i+base+1]
        for (i, &var_i) in vars.iter().enumerate() {
            let self_val = Self::node(base, i);
            let (lb_i, ub_i) = self.encoder.var_bounds(var_i);
            if self_val < lb_i || self_val > ub_i {
                continue; // self-loop value not in domain anyway
            }
            let ge_self = self
                .encoder
                .get_or_create_ge(&mut self.sat, var_i, self_val);
            // ¬(vars[i] = self_val) = ¬[ge_self] ∨ [ge_self+1]
            let mut clause = vec![ge_self.negated()];
            if let Some(next_value) = self_val.checked_add(1) {
                clause.push(
                    self.encoder
                        .get_or_create_ge(&mut self.sat, var_i, next_value),
                );
            }
            self.add_model_clause("encode_circuit", clause);
        }

        // 4. Subtour elimination via position variables (MTZ encoding)
        // pos[i] ∈ [0, n-1], pos[0] = 0
        // For each non-root edge (vars[i] -> j where j != node 0):
        //   pos[j-base] = pos[i] + 1
        let pos: Vec<IntVarId> = (0..n)
            .map(|_| {
                let trail_id = self.trail.register(0, (n - 1) as i64);
                let enc_id = self.encoder.register_var(0, (n - 1) as i64);
                debug_assert_eq!(trail_id, enc_id);
                self.var_names.push(None);
                trail_id
            })
            .collect();

        // Witness values: the position of each node on the cycle from node
        // 0, when the witness successors form one.
        if self.witness.is_some() {
            let succ: Option<Vec<i64>> = vars.iter().map(|&v| self.witness_value(v)).collect();
            let mut positions = vec![None; n];
            if let Some(succ) = succ {
                let mut node = 0usize;
                for step in 0..n {
                    if positions[node].is_some() {
                        break;
                    }
                    positions[node] = Some(step as i64);
                    match usize::try_from(i128::from(succ[node]) - i128::from(base)) {
                        Ok(next) if next < n => node = next,
                        _ => break,
                    }
                }
                if positions.iter().any(Option::is_none) {
                    positions = vec![None; n];
                }
            }
            for (k, (&p, value)) in pos.iter().zip(positions).enumerate() {
                self.witness_define(p, value, &format!("circuit_pos[{k}]"));
            }
        }

        // Fix pos[0] = 0
        self.add_propagator(LinearLe::new(vec![1], vec![pos[0]], 0));
        self.add_propagator(LinearLe::new(vec![-1], vec![pos[0]], 0));

        // For each node i, for each possible successor j (j_idx != 0):
        //   vars[i] = j_val → pos[j_idx] = pos[i] + 1
        //
        // Encoded via implication table: for each (i, j_idx) with j_idx != 0,
        // for each possible position value p of pos[i]:
        //   [vars[i]=j_val] ∧ [pos[i]=p] → [pos[j_idx]=p+1]
        //
        // In CNF (6 clauses per (i, j_idx, p)):
        //   not_vi_eq_j ∨ not_pi_eq_p ∨ pj_eq_p1
        // Where not_vi_eq_j = {¬[vi>=j], [vi>=j+1]}
        //   not_pi_eq_p = {¬[pi>=p], [pi>=p+1]}  (for p>lb) or {[pi>=p+1]} (for p=lb)
        //   pj_eq_p1 = {[pj>=p+1]} ∧ {¬[pj>=p+2]}
        //
        // Simplified: use two clauses per (i, j_idx, p):
        //   ¬[vi>=j] ∨ [vi>=j+1] ∨ ¬[pi>=p] ∨ [pi>=p+1] ∨ [pj>=p+1]
        //   ¬[vi>=j] ∨ [vi>=j+1] ∨ ¬[pi>=p] ∨ [pi>=p+1] ∨ ¬[pj>=p+2]
        for (i, &var_i) in vars.iter().enumerate() {
            for j_idx in 1..n {
                let j_val = Self::node(base, j_idx);
                let (lb_i, ub_i) = self.encoder.var_bounds(var_i);
                if j_val < lb_i || j_val > ub_i {
                    continue;
                }
                if i == j_idx {
                    continue; // self-loop already forbidden
                }

                let vi_ge_j = self.encoder.get_or_create_ge(&mut self.sat, var_i, j_val);
                let vi_ge_j1 = j_val.checked_add(1).map(|next_value| {
                    self.encoder
                        .get_or_create_ge(&mut self.sat, var_i, next_value)
                });

                // For each possible position value p of pos[i], including
                // the last one, n - 1: there `pos[j_idx] >= n` is the
                // constant-false literal, so the clause forbids the edge.
                // Without p = n - 1 (before 2026-11-18) a node in last
                // position could point to any node, which let two subtours
                // pass as a circuit (successors [1, 0, 3, 2]).
                for p in 0..(n as i64) {
                    // If vars[i]=j_val and pos[i]=p, then pos[j_idx]=p+1
                    // Clause 1 (pos[j_idx] >= p+1):
                    //   ¬[vi>=j] ∨ [vi>=j+1] ∨ ¬[pi>=p] ∨ [pi>=p+1] ∨ [pj>=p+1]
                    let pj_ge_p1 = self
                        .encoder
                        .get_or_create_ge(&mut self.sat, pos[j_idx], p + 1);

                    if p == 0 {
                        // pos[i] = 0 means ¬[pi >= 1], so "not_pi_eq_0" = [pi >= 1]
                        let pi_ge_1 = self.encoder.get_or_create_ge(&mut self.sat, pos[i], 1);
                        let mut clause = vec![vi_ge_j.negated()];
                        if let Some(lit) = vi_ge_j1 {
                            clause.push(lit);
                        }
                        clause.push(pi_ge_1);
                        clause.push(pj_ge_p1);
                        self.add_model_clause("encode_circuit", clause);
                        // Clause 2 (pos[j_idx] <= p+1 = 1):
                        if p + 2 <= (n - 1) as i64 {
                            let pj_ge_p2 =
                                self.encoder
                                    .get_or_create_ge(&mut self.sat, pos[j_idx], p + 2);
                            let mut clause = vec![vi_ge_j.negated()];
                            if let Some(lit) = vi_ge_j1 {
                                clause.push(lit);
                            }
                            clause.push(pi_ge_1);
                            clause.push(pj_ge_p2.negated());
                            self.add_model_clause("encode_circuit", clause);
                        }
                    } else {
                        let pi_ge_p = self.encoder.get_or_create_ge(&mut self.sat, pos[i], p);
                        let pi_ge_p1 = self.encoder.get_or_create_ge(&mut self.sat, pos[i], p + 1);
                        // Clause 1: pos[j_idx] >= p+1
                        let mut clause = vec![vi_ge_j.negated()];
                        if let Some(lit) = vi_ge_j1 {
                            clause.push(lit);
                        }
                        clause.push(pi_ge_p.negated());
                        clause.push(pi_ge_p1);
                        clause.push(pj_ge_p1);
                        self.add_model_clause("encode_circuit", clause);
                        // Clause 2: pos[j_idx] <= p+1
                        if p + 2 <= (n - 1) as i64 {
                            let pj_ge_p2 =
                                self.encoder
                                    .get_or_create_ge(&mut self.sat, pos[j_idx], p + 2);
                            let mut clause = vec![vi_ge_j.negated()];
                            if let Some(lit) = vi_ge_j1 {
                                clause.push(lit);
                            }
                            clause.push(pi_ge_p.negated());
                            clause.push(pi_ge_p1);
                            clause.push(pj_ge_p2.negated());
                            self.add_model_clause("encode_circuit", clause);
                        }
                    }
                }
            }
        }
    }

    /// Encode Inverse: x[y[i]] = i and y[x[i]] = i for all i.
    ///
    /// Decomposed into:
    /// 1. AllDifferent on x and y separately
    /// 2. Channeling: for each i, j: x[i] = j+base ↔ y[j] = i+base
    ///    Encoded as: [x[i] = j+base] → [y[j] = i+base] (and vice versa)
    pub(super) fn encode_inverse(
        &mut self,
        x: &[IntVarId],
        y: &[IntVarId],
        base_x: i64,
        base_y: i64,
    ) {
        let n = x.len();
        if n != y.len() {
            // No bijection between index sets of different sizes. (Before
            // 2026-11-19 a debug assertion; release builds channelled the
            // common prefix only.)
            self.add_model_clause("encode_inverse", Vec::new());
            return;
        }

        // AllDifferent on both arrays
        self.encode_alldiff_pairwise(x);
        self.encode_alldiff_pairwise(y);
        if n >= 2 {
            use crate::propagators::alldifferent::AllDifferentBounds;
            self.add_propagator(AllDifferentBounds::new(x.to_vec()));
            self.add_propagator(AllDifferentBounds::new(y.to_vec()));
        }

        // Node numbering of each array (see `node_numbering`).
        if !self.node_numbering(x, base_x) || !self.node_numbering(y, base_y) {
            return;
        }

        // Channeling constraints: x[i] = j+base_x → y[j] = i+base_y
        for (i, &xi) in x.iter().enumerate() {
            for (j, &yj) in y.iter().enumerate() {
                let j_val_in_x = Self::node(base_x, j);
                let i_val_in_y = Self::node(base_y, i);

                let (lb_xi, ub_xi) = self.encoder.var_bounds(xi);

                if j_val_in_x < lb_xi || j_val_in_x > ub_xi {
                    continue;
                }
                // When y[j] cannot take i, the clauses below forbid
                // x[i] = j (their y literals are then constant false).
                // Before 2026-11-18 this pair was skipped, which let x[i]
                // take j with no constraint on y[j].

                // x[i] = j_val_in_x → y[j] = i_val_in_y
                // In CNF:
                // ¬[x[i]>=j_val] ∨ [x[i]>=j_val+1] ∨ [y[j]>=i_val]
                // ¬[x[i]>=j_val] ∨ [x[i]>=j_val+1] ∨ ¬[y[j]>=i_val+1]
                let xi_ge_j = self.encoder.get_or_create_ge(&mut self.sat, xi, j_val_in_x);
                let xi_ge_j1 = j_val_in_x
                    .checked_add(1)
                    .map(|next_value| self.encoder.get_or_create_ge(&mut self.sat, xi, next_value));
                let yj_ge_i = self.encoder.get_or_create_ge(&mut self.sat, yj, i_val_in_y);

                // x[i]=j → y[j]>=i
                let mut clause = vec![xi_ge_j.negated()];
                if let Some(lit) = xi_ge_j1 {
                    clause.push(lit);
                }
                clause.push(yj_ge_i);
                self.add_model_clause("encode_inverse", clause);
                // x[i]=j → y[j]<=i  (i.e. y[j] < i+1)
                if let Some(next_value) = i_val_in_y.checked_add(1) {
                    let yj_ge_i1 = self.encoder.get_or_create_ge(&mut self.sat, yj, next_value);
                    let mut clause = vec![xi_ge_j.negated()];
                    if let Some(lit) = xi_ge_j1 {
                        clause.push(lit);
                    }
                    clause.push(yj_ge_i1.negated());
                    self.add_model_clause("encode_inverse", clause);
                }
            }
        }
    }

    /// Encode Minimum: result = min(args).
    ///
    /// Decomposed into: result <= each arg (propagators), and
    /// for each value v, (∧_i [arg_i >= v]) → [result >= v] (SAT clauses).
    pub(super) fn encode_minimum(&mut self, result: IntVarId, args: &[IntVarId]) {
        for &arg in args {
            let prop = LinearLe::new(vec![1, -1], vec![result, arg], 0);
            self.dirty.push(true);
            self.propagators.push(Box::new(prop));
        }
        // CNF: [result >= v] ∨ ¬[arg_1 >= v] ∨ ... ∨ ¬[arg_n >= v]
        // Up to v = ub(result) + 1, where `[result >= v]` is constant false:
        // some argument must be at most ub(result). (Before 2026-11-18 the
        // clauses stopped at ub, and none was added for a fixed result:
        // `2 = min([4])` was accepted.)
        // From lb + 1 on (`[result >= lb]` is true). With `result` fixed to
        // `i64::MAX` there is no such threshold, and none is needed:
        // `result <= arg` (above) already forces every argument to
        // `i64::MAX`. (Before 2026-11-19 `lb + 1` overflowed there.)
        let (lb_r, ub_r) = self.encoder.var_bounds(result);
        let top = ub_r.checked_add(1).unwrap_or(ub_r);
        let Some(first) = lb_r.checked_add(1) else {
            return;
        };
        for v in first..=top {
            let r_ge_v = self.encoder.get_or_create_ge(&mut self.sat, result, v);
            let mut clause = vec![r_ge_v];
            for &arg in args {
                let a_ge_v = self.encoder.get_or_create_ge(&mut self.sat, arg, v);
                clause.push(a_ge_v.negated());
            }
            self.add_model_clause("encode_minimum", clause);
        }
    }

    /// Encode Diffn: non-overlapping rectangles.
    ///
    /// For each pair of rectangles (i, j), at least one separation must hold:
    ///   x[i] + dx[i] <= x[j]  OR  x[j] + dx[j] <= x[i]
    ///   OR  y[i] + dy[i] <= y[j]  OR  y[j] + dy[j] <= y[i]
    ///
    /// Encoded using 4 Boolean indicator variables per pair with Big-M
    /// disjunctive constraints. At least one indicator must be true
    /// (boolean clause), and each indicator implies its separation constraint.
    ///
    /// Reference: Beldiceanu & Contejean, "Introducing Global Constraints in
    /// CHIP" (1994). The Big-M encoding is standard for CP-SAT solvers; see
    /// OR-Tools `AddNoOverlap2D` and Chuffed `diffn`.
    pub(super) fn encode_diffn(
        &mut self,
        x: &[IntVarId],
        y: &[IntVarId],
        dx: &[IntVarId],
        dy: &[IntVarId],
    ) {
        let n = x.len();
        debug_assert_eq!(n, y.len());
        debug_assert_eq!(n, dx.len());
        debug_assert_eq!(n, dy.len());

        for i in 0..n {
            for j in (i + 1)..n {
                // Create 4 Boolean indicator variables for separation directions.
                let b1 = self.new_bool_var(None);
                let b2 = self.new_bool_var(None);
                let b3 = self.new_bool_var(None);
                let b4 = self.new_bool_var(None);
                // Witness values: an indicator is 1 exactly when its
                // separation holds under the witness.
                if self.witness.is_some() {
                    let separated = |s: &Self, a: IntVarId, da: IntVarId, b: IntVarId| {
                        Some(i64::from(
                            s.witness_value(a)? + s.witness_value(da)? <= s.witness_value(b)?,
                        ))
                    };
                    let values = [
                        separated(self, x[i], dx[i], x[j]),
                        separated(self, x[j], dx[j], x[i]),
                        separated(self, y[i], dy[i], y[j]),
                        separated(self, y[j], dy[j], y[i]),
                    ];
                    for (k, (b, value)) in [b1, b2, b3, b4].into_iter().zip(values).enumerate() {
                        self.witness_define(b, value, &format!("diffn_sep{}[{i},{j}]", k + 1));
                    }
                }

                // At least one separation must hold: b1 ∨ b2 ∨ b3 ∨ b4
                // Encoded directly as SAT clause on order-encoding literals.
                self.encode_bool_clause(&[b1, b2, b3, b4], &[]);

                // Compute Big-M values from variable domains.
                let (lb_xi, ub_xi) = self.encoder.var_bounds(x[i]);
                let (_, ub_dxi) = self.encoder.var_bounds(dx[i]);
                let (lb_xj, ub_xj) = self.encoder.var_bounds(x[j]);
                let (_, ub_dxj) = self.encoder.var_bounds(dx[j]);

                let (lb_yi, ub_yi) = self.encoder.var_bounds(y[i]);
                let (_, ub_dyi) = self.encoder.var_bounds(dy[i]);
                let (lb_yj, ub_yj) = self.encoder.var_bounds(y[j]);
                let (_, ub_dyj) = self.encoder.var_bounds(dy[j]);

                // b1=1 → x[i] + dx[i] <= x[j]  (i left of j)
                // Big-M: x[i] + dx[i] - x[j] + M*b1 <= M
                // b1=1: x[i]+dx[i]-x[j] <= 0  (enforced)
                // b1=0: x[i]+dx[i]-x[j] <= M   (relaxed)
                let m1 = (i128::from(ub_xi) + i128::from(ub_dxi) - i128::from(lb_xj)).max(0) + 1;
                self.add_propagator(LinearLe::new_wide(
                    vec![1, 1, -1, m1],
                    vec![x[i], dx[i], x[j], b1],
                    m1,
                ));

                // b2=1 → x[j] + dx[j] <= x[i]  (j left of i)
                let m2 = (i128::from(ub_xj) + i128::from(ub_dxj) - i128::from(lb_xi)).max(0) + 1;
                self.add_propagator(LinearLe::new_wide(
                    vec![1, 1, -1, m2],
                    vec![x[j], dx[j], x[i], b2],
                    m2,
                ));

                // b3=1 → y[i] + dy[i] <= y[j]  (i below j)
                let m3 = (i128::from(ub_yi) + i128::from(ub_dyi) - i128::from(lb_yj)).max(0) + 1;
                self.add_propagator(LinearLe::new_wide(
                    vec![1, 1, -1, m3],
                    vec![y[i], dy[i], y[j], b3],
                    m3,
                ));

                // b4=1 → y[j] + dy[j] <= y[i]  (j below i)
                let m4 = (i128::from(ub_yj) + i128::from(ub_dyj) - i128::from(lb_yi)).max(0) + 1;
                self.add_propagator(LinearLe::new_wide(
                    vec![1, 1, -1, m4],
                    vec![y[j], dy[j], y[i], b4],
                    m4,
                ));
            }
        }
    }
}
