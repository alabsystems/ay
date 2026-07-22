// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Interpolation helpers: IUC-Farkas fallback, N1 per-clause interpolation,
//! and variable name translation between clause-local and canonical forms.

use super::super::PdrSolver;
use crate::proof_interpolation::{
    compute_interpolant_candidate_from_smt_farkas_history, InterpolantCandidate,
};
use crate::{ChcExpr, ChcVar, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

impl PdrSolver {
    /// Try IUC-Farkas fallback when standard interpolation fails (#816).
    ///
    /// When `transition_constraints` contains disjunctions (ITE, Or), the standard
    /// `compute_interpolant_from_lia_farkas` fails because it requires pure linear atoms.
    ///
    /// This fallback runs full DPLL(T) on `A ∧ B` by treating B as SAT assumptions, then:
    /// - extracts an UNSAT core over B (IUC-style shrinking), and
    /// - collects the arithmetic Farkas conflicts produced during solving.
    ///
    /// It then attempts to extract a proof-based interpolant from the collected conflicts.
    ///
    /// Reference: Z3 Spacer's `iuc_solver` uses proxy literals + proof processing
    /// (`reference/z3/src/muz/spacer/spacer_iuc_solver.cpp:253`).
    pub(in crate::pdr::solver) fn try_iuc_farkas_fallback_candidate(
        &mut self,
        transition_constraints: &[ChcExpr],
        bad_state_constraints: &[ChcExpr],
        shared_vars: &FxHashSet<String>,
    ) -> Option<InterpolantCandidate> {
        compute_interpolant_candidate_from_smt_farkas_history(
            &mut self.smt,
            transition_constraints,
            bad_state_constraints,
            shared_vars,
            self.config.verbose,
        )
    }

    /// Try N1 per-clause interpolation (#917).
    ///
    /// When combined interpolation fails (e.g., due to variable naming mismatches between
    /// clause-local names and canonical names), this approach tries each clause separately:
    ///
    /// 1. For each clause that contributed to UNSAT:
    ///    a. Translate B (bad state) from canonical names to clause-local names
    ///    b. Use clause head argument variable names as shared_vars
    ///    c. Try interpolation on (clause_constraint, B_local, shared_vars_local)
    ///    d. If successful, translate the interpolant back to canonical names
    ///
    /// This ensures proper variable alignment: A and B use the same naming scheme within
    /// each interpolation attempt, so Farkas combinations produce valid interpolants.
    ///
    /// Reference: the development design notes, Option N1.
    pub(in crate::pdr::solver) fn try_n1_per_clause_interpolation(
        &mut self,
        clause_data: &[(Vec<ChcExpr>, ChcExpr)],
        bad_state: &ChcExpr,
        predicate: PredicateId,
    ) -> Option<InterpolantCandidate> {
        // Clone canonical vars to avoid borrow conflict with self.smt
        let canonical_vars: Vec<ChcVar> = self.canonical_vars(predicate)?.to_vec();
        if canonical_vars.is_empty() {
            return None;
        }
        let verbose = self.config.verbose;

        for (head_args, clause_constraint) in clause_data {
            // Skip if head_args arity doesn't match canonical vars
            if head_args.len() != canonical_vars.len() {
                continue;
            }

            // Build mapping: canonical_var_name -> head_arg_var_name
            // This translates B from canonical names to clause-local names.
            let mut canon_to_local: FxHashMap<String, ChcVar> = FxHashMap::default();
            let mut shared_vars_local: FxHashSet<String> = FxHashSet::default();

            // #2492: Also extract constituent vars from expression head args
            for (canon_var, head_arg) in canonical_vars.iter().zip(head_args.iter()) {
                match head_arg {
                    ChcExpr::Var(local_var) => {
                        canon_to_local.insert(canon_var.name.clone(), local_var.clone());
                        shared_vars_local.insert(local_var.name.clone());
                    }
                    expr => {
                        for v in expr.vars_of_sort(&canon_var.sort) {
                            canon_to_local
                                .entry(canon_var.name.clone())
                                .or_insert_with(|| v.clone());
                            shared_vars_local.insert(v.name.clone());
                        }
                    }
                }
            }

            if canon_to_local.is_empty() {
                continue;
            }

            // Translate B to clause-local names
            let b_local = Self::translate_expr_vars(bad_state, &canon_to_local);
            let b_local_constraints = b_local.collect_conjuncts();

            // Try interpolation with clause-local A and B
            let a_constraints = clause_constraint.collect_conjuncts();

            if self.config.is_lia_farkas_profile() {
                self.telemetry.lia_farkas_templates.record_farkas_check();
            }
            if let Some(candidate_local) = compute_interpolant_candidate_from_smt_farkas_history(
                &mut self.smt,
                &a_constraints,
                &b_local_constraints,
                &shared_vars_local,
                verbose,
            ) {
                let interpolant_local = candidate_local.expr;
                // Translate interpolant back to canonical names
                // #2492: Also extract constituent vars from expression head args
                let mut local_to_canon: FxHashMap<String, ChcVar> = FxHashMap::default();
                for (canon_var, head_arg) in canonical_vars.iter().zip(head_args.iter()) {
                    match head_arg {
                        ChcExpr::Var(local_var) => {
                            local_to_canon.insert(local_var.name.clone(), canon_var.clone());
                        }
                        expr => {
                            for v in expr.vars_of_sort(&canon_var.sort) {
                                local_to_canon
                                    .entry(v.name.clone())
                                    .or_insert_with(|| canon_var.clone());
                            }
                        }
                    }
                }
                let interpolant = Self::translate_expr_vars(&interpolant_local, &local_to_canon);

                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: N1 per-clause interpolation succeeded: {} (from local: {}, kind={:?}, has_farkas_conflicts={})",
                        interpolant,
                        interpolant_local,
                        candidate_local.kind,
                        candidate_local.has_farkas_conflicts,
                    );
                }
                return Some(InterpolantCandidate {
                    expr: interpolant,
                    kind: candidate_local.kind,
                    has_farkas_conflicts: candidate_local.has_farkas_conflicts,
                });
            }
        }

        None
    }

    /// Translate a clause constraint from clause-local variable names to canonical names.
    ///
    /// This is used for interpolation: transition constraints (A) need to use the same
    /// naming scheme as bad state constraints (B) for interpolation to work correctly.
    ///
    /// # Arguments
    /// - `constraint`: The clause constraint using clause-local variable names
    /// - `head_args`: The clause head arguments (expressions, may include non-Var exprs)
    /// - `canonical_vars`: The canonical variable names for the predicate
    ///
    /// # Returns
    /// The constraint with clause-local head arg names replaced by canonical names.
    pub(in crate::pdr::solver) fn translate_to_canonical_names(
        constraint: &ChcExpr,
        head_args: &[ChcExpr],
        canonical_vars: &[ChcVar],
    ) -> ChcExpr {
        if head_args.len() != canonical_vars.len() {
            return constraint.clone();
        }

        // Build mapping: clause-local name -> canonical var
        // #2492: Also extract constituent vars from expression head args
        // #6047: Only map variables whose sort matches the canonical var's sort.
        // Expression head args (e.g., (store ov cnt true)) contain variables of
        // mixed sorts; mapping all to the position's canonical sort causes BV
        // variables to acquire Array sorts, triggering panics in BV operations.
        let mut local_to_canon: FxHashMap<String, ChcVar> = FxHashMap::default();
        for (head_arg, canon_var) in head_args.iter().zip(canonical_vars.iter()) {
            match head_arg {
                ChcExpr::Var(local_var) => {
                    local_to_canon.insert(local_var.name.clone(), canon_var.clone());
                }
                expr => {
                    for v in expr.vars() {
                        // Only map variables with matching sort to avoid cross-sort
                        // contamination (#6047).
                        if v.sort == canon_var.sort {
                            local_to_canon
                                .entry(v.name.clone())
                                .or_insert_with(|| canon_var.clone());
                        }
                    }
                }
            }
        }

        if local_to_canon.is_empty() {
            return constraint.clone();
        }

        Self::translate_expr_vars(constraint, &local_to_canon)
    }

    /// Translate variable names in an expression using a mapping.
    /// Variables not in the mapping are left unchanged.
    pub(in crate::pdr::solver) fn translate_expr_vars(
        expr: &ChcExpr,
        mapping: &FxHashMap<String, ChcVar>,
    ) -> ChcExpr {
        let name_map: FxHashMap<String, ChcExpr> = mapping
            .iter()
            .map(|(name, var)| (name.clone(), ChcExpr::var(var.clone())))
            .collect();
        expr.substitute_name_map(&name_map)
    }
}
