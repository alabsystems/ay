// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::PdrSolver;
use super::bounds_bv_seed_helpers::{
    bitvec_bits_from_seed_value, collect_bv_constants, push_bv_lower_bound_candidate,
    MAX_BLOCKED_STATE_BV_CONSTANTS_PER_VAR,
};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, HornClause, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;

/// Per-transition-clause seed bundle for native-BV Bool/comparison combinatorics.
///
/// Groups the Bool canonical vars and BV comparison atoms that co-occur in a
/// single transition clause. This scopes candidate generation to clause-local
/// relationships instead of the global O(n^2 + n*m) search that was disabled
/// for native BV (#5877).
pub(in crate::pdr::solver) struct BvClauseSeed {
    pub bool_vars: Vec<ChcVar>,
    pub comparison_atoms: Vec<ChcExpr>,
}

impl PdrSolver {
    /// Extract candidate BV comparison invariants from transition clauses.
    ///
    /// Scans the constraint formulas of transition clauses that define `pred`,
    /// looking for BV comparison atoms that involve canonical predicate variables.
    pub(in crate::pdr::solver) fn extract_bv_candidate_invariants(
        &self,
        pred: PredicateId,
        canonical_vars: &[ChcVar],
    ) -> Vec<ChcExpr> {
        let blocked_state_seed_values = self.blocked_state_bv_seed_values(
            pred,
            canonical_vars,
            MAX_BLOCKED_STATE_BV_CONSTANTS_PER_VAR,
        );
        let mut candidates = Vec::new();
        let mut seen = FxHashSet::default();

        for clause in self.problem.clauses() {
            if clause.head.predicate_id() != Some(pred) || clause.is_fact() {
                continue;
            }

            let var_map = self.build_body_var_map(clause, pred, canonical_vars);
            if var_map.is_empty() {
                continue;
            }

            let Some(constraint) = &clause.body.constraint else {
                continue;
            };
            self.collect_bv_comparison_atoms(constraint, &var_map, &mut candidates, &mut seen);
        }

        let mut bv_constants = FxHashSet::default();
        for candidate in &candidates {
            collect_bv_constants(candidate, &mut bv_constants);
        }

        let bv_vars: Vec<_> = canonical_vars
            .iter()
            .filter(|var| matches!(var.sort, ChcSort::BitVec(_)))
            .collect();
        for var in &bv_vars {
            if let ChcSort::BitVec(width) = var.sort {
                bv_constants.insert((1, width));
            }
        }

        for var in &bv_vars {
            let width = match var.sort {
                ChcSort::BitVec(width) => width,
                _ => continue,
            };
            for &(value, candidate_width) in &bv_constants {
                if candidate_width != width {
                    continue;
                }
                push_bv_lower_bound_candidate(&mut candidates, &mut seen, var, value);
            }

            if let Some(extra_constants) = blocked_state_seed_values.get(&var.name) {
                for &value in extra_constants {
                    push_bv_lower_bound_candidate(
                        &mut candidates,
                        &mut seen,
                        var,
                        bitvec_bits_from_seed_value(i128::from(value), width),
                    );
                }
            }
        }

        candidates
    }

    /// Extract per-transition-clause seed bundles for native-BV problems.
    ///
    /// For each transition clause defining `pred`, collects the Bool canonical
    /// vars and BV comparison atoms that co-occur in that clause. These bundles
    /// scope Bool/BV combinatorics to clause-local relationships, avoiding the
    /// global O(n^2 + n*m) explosion while generating the exact shapes needed
    /// (e.g., `(A ∨ ¬B)`, `(¬C ∨ bvsle(1, H))`).
    pub(in crate::pdr::solver) fn extract_bv_clause_seeds(
        &self,
        pred: PredicateId,
        canonical_vars: &[ChcVar],
    ) -> Vec<BvClauseSeed> {
        let blocked_state_seed_values = self.blocked_state_bv_seed_values(
            pred,
            canonical_vars,
            MAX_BLOCKED_STATE_BV_CONSTANTS_PER_VAR,
        );
        let mut seeds = Vec::new();

        for clause in self.problem.clauses() {
            if clause.head.predicate_id() != Some(pred) || clause.is_fact() {
                continue;
            }

            let var_map = self.build_body_var_map(clause, pred, canonical_vars);
            if var_map.is_empty() {
                continue;
            }

            // Collect Bool canonical vars that appear in this clause's body predicates
            let mut clause_bool_vars: Vec<ChcVar> = var_map
                .values()
                .filter(|v| matches!(v.sort, ChcSort::Bool))
                .cloned()
                .collect();
            // Dedup by name for stable ordering
            clause_bool_vars.sort_by(|a, b| a.name.cmp(&b.name));
            clause_bool_vars.dedup_by(|a, b| a.name == b.name);

            // Collect BV comparison atoms from this clause's constraint
            let mut clause_comparisons = Vec::new();
            let mut seen = FxHashSet::default();
            if let Some(constraint) = &clause.body.constraint {
                self.collect_bv_comparison_atoms(
                    constraint,
                    &var_map,
                    &mut clause_comparisons,
                    &mut seen,
                );
            }

            // Also add bvsle(1, var) for each BV variable in this clause
            let bv_vars_in_clause: Vec<_> = var_map
                .values()
                .filter(|v| matches!(v.sort, ChcSort::BitVec(_)))
                .cloned()
                .collect();
            for var in &bv_vars_in_clause {
                if let ChcSort::BitVec(width) = var.sort {
                    push_bv_lower_bound_candidate(&mut clause_comparisons, &mut seen, var, 1);
                    if let Some(extra_constants) = blocked_state_seed_values.get(&var.name) {
                        for &value in extra_constants {
                            push_bv_lower_bound_candidate(
                                &mut clause_comparisons,
                                &mut seen,
                                var,
                                bitvec_bits_from_seed_value(i128::from(value), width),
                            );
                        }
                    }
                }
            }

            if !clause_bool_vars.is_empty() || !clause_comparisons.is_empty() {
                seeds.push(BvClauseSeed {
                    bool_vars: clause_bool_vars,
                    comparison_atoms: clause_comparisons,
                });
            }
        }

        seeds
    }

    fn build_body_var_map(
        &self,
        clause: &HornClause,
        pred: PredicateId,
        canonical_vars: &[ChcVar],
    ) -> FxHashMap<String, ChcVar> {
        let mut var_map = FxHashMap::default();
        for (body_pred_id, body_args) in &clause.body.predicates {
            if *body_pred_id != pred || body_args.len() != canonical_vars.len() {
                continue;
            }
            for (arg, canonical_var) in body_args.iter().zip(canonical_vars.iter()) {
                if let ChcExpr::Var(var) = arg {
                    var_map.insert(var.name.clone(), canonical_var.clone());
                }
            }
        }
        var_map
    }

    fn collect_bv_comparison_atoms(
        &self,
        expr: &ChcExpr,
        var_map: &FxHashMap<String, ChcVar>,
        candidates: &mut Vec<ChcExpr>,
        seen: &mut FxHashSet<String>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) | ChcExpr::Op(ChcOp::Or, args) => {
                for arg in args {
                    self.collect_bv_comparison_atoms(arg, var_map, candidates, seen);
                }
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                if let Some(inner_candidate) = self.try_extract_bv_comparison(&args[0], var_map) {
                    let negated = ChcExpr::not(inner_candidate);
                    let key = format!("{negated}");
                    if seen.insert(key) {
                        candidates.push(negated);
                    }
                }
                self.collect_bv_comparison_atoms(&args[0], var_map, candidates, seen);
            }
            ChcExpr::Op(ChcOp::BvSLe | ChcOp::BvSGe | ChcOp::BvULe | ChcOp::BvUGe, _) => {
                if let Some(candidate) = self.try_extract_bv_comparison(expr, var_map) {
                    let key = format!("{candidate}");
                    if seen.insert(key) {
                        candidates.push(candidate.clone());
                    }
                    let negated = ChcExpr::not(candidate);
                    let neg_key = format!("{negated}");
                    if seen.insert(neg_key) {
                        candidates.push(negated);
                    }
                }
            }
            _ => {}
        }
    }

    /// Extract Int bound candidates for BvToInt-relaxed problems (#5877).
    ///
    /// For predicates with Bool+Int variables (typical of BvToInt-relaxed
    /// transforms), generates Int comparison atoms:
    /// - `V >= c` for each Int variable V and candidate constant c
    /// - `V <= c` for each Int variable V and candidate constant c
    /// - Int comparison atoms extracted from transition clause constraints
    ///
    /// These serve the same role as BV comparison atoms in `extract_bv_candidate_invariants`
    /// but for the integer domain.
    pub(in crate::pdr::solver) fn extract_int_bound_candidates(
        &self,
        pred: PredicateId,
        canonical_vars: &[ChcVar],
    ) -> Vec<ChcExpr> {
        let mut candidates = Vec::new();
        let mut seen = FxHashSet::default();

        let int_vars: Vec<_> = canonical_vars
            .iter()
            .filter(|var| matches!(var.sort, ChcSort::Int))
            .collect();

        if int_vars.is_empty() {
            return candidates;
        }

        // Collect Int constants from transition constraints.
        let mut int_constants = FxHashSet::default();
        int_constants.insert(0i128);
        int_constants.insert(1);

        for clause in self.problem.clauses() {
            if clause.head.predicate_id() != Some(pred) || clause.is_fact() {
                continue;
            }
            let var_map = self.build_body_var_map(clause, pred, canonical_vars);
            if var_map.is_empty() {
                continue;
            }
            if let Some(constraint) = &clause.body.constraint {
                self.collect_int_comparison_atoms(constraint, &var_map, &mut candidates, &mut seen);
                Self::collect_int_constants(constraint, &mut int_constants);
            }
        }

        // Also collect constants from fact constraints.
        for clause in self.problem.clauses() {
            if clause.head.predicate_id() != Some(pred) || !clause.is_fact() {
                continue;
            }
            if let Some(constraint) = &clause.body.constraint {
                Self::collect_int_constants(constraint, &mut int_constants);
            }
        }

        // Generate V >= c and V <= c for each Int variable and constant.
        // Limit to small constants to avoid combinatorial explosion.
        let small_constants: Vec<i128> = int_constants
            .into_iter()
            .filter(|c| *c >= -10 && *c <= 10)
            .collect();

        for var in &int_vars {
            for &c in &small_constants {
                let ge = ChcExpr::ge(ChcExpr::var((*var).clone()), ChcExpr::Int(c));
                let key = format!("{ge}");
                if seen.insert(key) {
                    candidates.push(ge);
                }
                let le = ChcExpr::le(ChcExpr::var((*var).clone()), ChcExpr::Int(c));
                let key = format!("{le}");
                if seen.insert(key) {
                    candidates.push(le);
                }
            }
        }

        candidates
    }

    fn collect_int_constants(expr: &ChcExpr, constants: &mut FxHashSet<i128>) {
        match expr {
            ChcExpr::Int(value) => {
                constants.insert(*value);
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    Self::collect_int_constants(arg, constants);
                }
            }
            _ => {}
        }
    }

    fn collect_int_comparison_atoms(
        &self,
        expr: &ChcExpr,
        var_map: &FxHashMap<String, ChcVar>,
        candidates: &mut Vec<ChcExpr>,
        seen: &mut FxHashSet<String>,
    ) {
        match expr {
            ChcExpr::Op(ChcOp::And, args) | ChcExpr::Op(ChcOp::Or, args) => {
                for arg in args {
                    self.collect_int_comparison_atoms(arg, var_map, candidates, seen);
                }
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                self.collect_int_comparison_atoms(&args[0], var_map, candidates, seen);
            }
            ChcExpr::Op(ChcOp::Le | ChcOp::Ge | ChcOp::Lt | ChcOp::Gt, args) if args.len() == 2 => {
                if let Some(candidate) = self.try_extract_int_comparison(expr, var_map) {
                    let key = format!("{candidate}");
                    if seen.insert(key) {
                        candidates.push(candidate);
                    }
                }
            }
            _ => {}
        }
    }

    fn try_extract_int_comparison(
        &self,
        expr: &ChcExpr,
        var_map: &FxHashMap<String, ChcVar>,
    ) -> Option<ChcExpr> {
        let ChcExpr::Op(op @ (ChcOp::Le | ChcOp::Ge | ChcOp::Lt | ChcOp::Gt), args) = expr else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        let lhs = &args[0];
        let rhs = &args[1];

        // Pattern: const OP var or var OP const
        if let (ChcExpr::Int(value), ChcExpr::Var(var)) = (lhs.as_ref(), rhs.as_ref()) {
            let canonical = var_map.get(&var.name)?;
            if !matches!(canonical.sort, ChcSort::Int) {
                return None;
            }
            return Some(ChcExpr::Op(
                *op,
                vec![
                    Arc::new(ChcExpr::Int(*value)),
                    Arc::new(ChcExpr::var(canonical.clone())),
                ],
            ));
        }

        if let (ChcExpr::Var(var), ChcExpr::Int(value)) = (lhs.as_ref(), rhs.as_ref()) {
            let canonical = var_map.get(&var.name)?;
            if !matches!(canonical.sort, ChcSort::Int) {
                return None;
            }
            return Some(ChcExpr::Op(
                *op,
                vec![
                    Arc::new(ChcExpr::var(canonical.clone())),
                    Arc::new(ChcExpr::Int(*value)),
                ],
            ));
        }

        // Pattern: var OP var
        if let (ChcExpr::Var(lhs_var), ChcExpr::Var(rhs_var)) = (lhs.as_ref(), rhs.as_ref()) {
            let lhs_canonical = var_map.get(&lhs_var.name)?;
            let rhs_canonical = var_map.get(&rhs_var.name)?;
            if !matches!(lhs_canonical.sort, ChcSort::Int)
                || !matches!(rhs_canonical.sort, ChcSort::Int)
            {
                return None;
            }
            return Some(ChcExpr::Op(
                *op,
                vec![
                    Arc::new(ChcExpr::var(lhs_canonical.clone())),
                    Arc::new(ChcExpr::var(rhs_canonical.clone())),
                ],
            ));
        }

        None
    }

    fn try_extract_bv_comparison(
        &self,
        expr: &ChcExpr,
        var_map: &FxHashMap<String, ChcVar>,
    ) -> Option<ChcExpr> {
        let ChcExpr::Op(op @ (ChcOp::BvSLe | ChcOp::BvSGe | ChcOp::BvULe | ChcOp::BvUGe), args) =
            expr
        else {
            return None;
        };
        if args.len() != 2 {
            return None;
        }

        let lhs = &args[0];
        let rhs = &args[1];

        if let (ChcExpr::BitVec(value, width), ChcExpr::Var(var)) = (lhs.as_ref(), rhs.as_ref()) {
            let canonical = var_map.get(&var.name)?;
            return Some(ChcExpr::Op(
                *op,
                vec![
                    Arc::new(ChcExpr::BitVec(*value, *width)),
                    Arc::new(ChcExpr::var(canonical.clone())),
                ],
            ));
        }

        if let (ChcExpr::Var(var), ChcExpr::BitVec(value, width)) = (lhs.as_ref(), rhs.as_ref()) {
            let canonical = var_map.get(&var.name)?;
            return Some(ChcExpr::Op(
                *op,
                vec![
                    Arc::new(ChcExpr::var(canonical.clone())),
                    Arc::new(ChcExpr::BitVec(*value, *width)),
                ],
            ));
        }

        if let (ChcExpr::Var(lhs_var), ChcExpr::Var(rhs_var)) = (lhs.as_ref(), rhs.as_ref()) {
            let lhs_canonical = var_map.get(&lhs_var.name)?;
            let rhs_canonical = var_map.get(&rhs_var.name)?;
            return Some(ChcExpr::Op(
                *op,
                vec![
                    Arc::new(ChcExpr::var(lhs_canonical.clone())),
                    Arc::new(ChcExpr::var(rhs_canonical.clone())),
                ],
            ));
        }

        None
    }
}
