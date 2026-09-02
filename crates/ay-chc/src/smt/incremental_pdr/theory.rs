// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Theory integration for the incremental PDR DPLL(T) loop (#6358).
//!
//! This module contains the LIA theory check that runs after the SAT solver
//! finds a propositional model. It either confirms the model is theory-consistent
//! (returning a concrete model) or generates a theory conflict clause that is
//! added to the SAT solver for re-solving.

use super::IncrementalPdrContext;
use crate::smt::context::SmtContext;
use crate::smt::model_verify::{
    is_theory_atom, verify_sat_model_conjunction_strict_with_mod_retry,
};
use crate::smt::types::{ModelVerifyResult, SmtValue};
use crate::ChcExpr;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId};
use num_traits::One;
use std::collections::BTreeMap;

/// Internal result type for the theory check loop.
pub(super) enum TheoryLoopResult {
    Sat(FxHashMap<String, SmtValue>),
    Unsat,
    ConflictAdded,
    Unknown,
}

impl IncrementalPdrContext {
    /// Run theory check on a propositional SAT model and either extract a model
    /// or add a theory conflict clause to the SAT solver.
    pub(super) fn check_theory_and_extract_model(
        &mut self,
        sat_model: &[bool],
        term_to_var: &BTreeMap<TermId, u32>,
        var_to_term: &BTreeMap<u32, TermId>,
        propagated_equalities: &FxHashMap<String, i128>,
        propagated_bv_equalities: &FxHashMap<String, (u128, u32)>,
        assumptions: &[ChcExpr],
        remaining_timeout: Option<std::time::Duration>,
    ) -> TheoryLoopResult {
        use ay_core::{TheoryResult, TheorySolver};
        use ay_lia::LiaSolver;

        let mut lia = LiaSolver::new(&self.own_smt.terms);
        if let Some(t) = remaining_timeout {
            let start = ay_core::time::Instant::now();
            lia.set_timeout_callback(move || start.elapsed() >= t);
        }

        // Feed theory atoms from SAT model to LIA solver.
        for (&var_idx, &term_id) in var_to_term {
            if !is_theory_atom(&self.own_smt.terms, term_id) {
                continue;
            }
            if SmtContext::is_bv_theory_atom(&self.own_smt.terms, term_id) {
                continue;
            }
            if SmtContext::is_array_theory_atom(&self.own_smt.terms, term_id) {
                continue;
            }
            let sat_var = ay_sat::Variable::new(var_idx - 1);
            if let Some(value) = sat_model.get(sat_var.index()) {
                lia.assert_literal(term_id, *value);
            }
        }

        match lia.check() {
            TheoryResult::Sat => self.extract_theory_model(
                &lia,
                sat_model,
                term_to_var,
                propagated_equalities,
                propagated_bv_equalities,
                assumptions,
            ),
            TheoryResult::Unsat(conflict) => {
                self.add_theory_conflict_clause(&conflict, term_to_var)
            }
            TheoryResult::UnsatWithFarkas(conflict) => {
                self.add_theory_conflict_clause(&conflict.literals, term_to_var)
            }
            TheoryResult::NeedSplit(split) => self.handle_need_split(split, term_to_var),
            TheoryResult::NeedDisequalitySplit(split) => {
                self.handle_need_disequality_split(split, term_to_var)
            }
            TheoryResult::NeedExpressionSplit(split) => {
                self.handle_need_expression_split(split, term_to_var)
            }
            TheoryResult::NeedStringLemma(_) => TheoryLoopResult::Unknown,
            TheoryResult::NeedModelEquality(_) => TheoryLoopResult::Unknown,
            TheoryResult::Unknown => TheoryLoopResult::Unknown,
            #[allow(unreachable_patterns)]
            _ => TheoryLoopResult::Unknown,
        }
    }

    /// Extract a theory-consistent model from LIA solver + SAT assignments.
    fn extract_theory_model(
        &self,
        lia: &ay_lia::LiaSolver<'_>,
        sat_model: &[bool],
        term_to_var: &BTreeMap<TermId, u32>,
        propagated_equalities: &FxHashMap<String, i128>,
        propagated_bv_equalities: &FxHashMap<String, (u128, u32)>,
        assumptions: &[ChcExpr],
    ) -> TheoryLoopResult {
        let mut values: FxHashMap<String, SmtValue> = FxHashMap::default();
        for (name, value) in propagated_equalities {
            values.insert(name.clone(), SmtValue::Int(*value));
        }
        // #5877: Insert BV var=const equalities with their exact BV type.
        for (name, (value, width)) in propagated_bv_equalities {
            values.insert(name.clone(), SmtValue::bitvec_from_u128(*value, *width));
        }

        let lia_model = lia.extract_model();
        let var_entries: Vec<(String, TermId)> = self
            .own_smt
            .var_map()
            .iter()
            .map(|(k, &v)| (k.clone(), v))
            .collect();

        for (qualified_name, term_id) in &var_entries {
            let name = self.own_smt.original_var_name(qualified_name);
            if values.contains_key(name) {
                continue;
            }
            match self.own_smt.terms.sort(*term_id) {
                Sort::Bool => {
                    if let Some(&cnf_var) = term_to_var.get(term_id) {
                        let sat_var = ay_sat::Variable::new(cnf_var - 1);
                        if let Some(value) = sat_model.get(sat_var.index()) {
                            values.insert(name.to_owned(), SmtValue::Bool(*value));
                        }
                    }
                }
                Sort::Int => {
                    if let Some(m) = &lia_model {
                        if let Some(v) = m.values.get(term_id) {
                            // Phase-2 BigInt escape: carry beyond-i128 witnesses
                            // as canonical SmtValue::BigInt (in-range values stay
                            // SmtValue::Int) instead of skipping them fail-closed.
                            values.insert(name.to_owned(), SmtValue::int_from_bigint(v.clone()));
                            continue;
                        }
                    }
                    if let Some(v) = lia.lra_solver().get_value(*term_id) {
                        if v.denom().is_one() {
                            values.insert(
                                name.to_owned(),
                                SmtValue::int_from_bigint(v.numer().clone()),
                            );
                        }
                    }
                }
                Sort::Real => {
                    // #LRA-Lin: mirror check_sat/theory_model.rs Real arm. This
                    // match previously fell through to `_ => {}`, silently
                    // dropping every Real var from the incremental-PDR model so
                    // that the downstream strict re-verify saw a missing
                    // assignment and demoted an otherwise-Sat query to Unknown.
                    if let Some(v) = lia.lra_solver().get_value(*term_id) {
                        values.insert(name.to_owned(), SmtValue::Real(v.clone()));
                    }
                }
                _ => {}
            }
        }

        // #7380: Reverse-map namespaced model entries to un-namespaced base names.
        // PDR assumptions are preprocessed with namespace renaming (e.g., _mod_r_1 -> _mod_r_1__q0).
        // The original assumptions reference un-namespaced names that the evaluator needs.
        use crate::smt::incremental::strip_namespace_suffix;
        let mut extra_entries = Vec::new();
        for (name, value) in &values {
            if let Some(base) = strip_namespace_suffix(name) {
                if !values.contains_key(base) {
                    extra_entries.push((base.to_owned(), value.clone()));
                }
            }
        }
        for (name, value) in extra_entries {
            values.insert(name, value);
        }

        // Verify the model against the original assumptions.
        let verify_result =
            verify_sat_model_conjunction_strict_with_mod_retry(assumptions.iter(), &values);
        match verify_result {
            ModelVerifyResult::Invalid => {
                tracing::warn!(
                    "incremental_pdr: SAT model violates assumptions; returning Unknown"
                );
                TheoryLoopResult::Unknown
            }
            ModelVerifyResult::Indeterminate => {
                let has_array_ops = assumptions.iter().any(ChcExpr::contains_array_ops);
                let has_dt = assumptions.iter().any(ChcExpr::contains_dt_ops);
                let has_mod_aux = assumptions.iter().any(ChcExpr::has_mod_aux_vars);
                if has_array_ops || has_dt || has_mod_aux {
                    tracing::debug!(
                        "incremental_pdr: SAT model indeterminate with array/DT/mod ops; degrading to Unknown"
                    );
                    TheoryLoopResult::Unknown
                } else {
                    TheoryLoopResult::Sat(values)
                }
            }
            ModelVerifyResult::Valid => TheoryLoopResult::Sat(values),
        }
    }

    /// Add a theory conflict clause (negation of conflict literals) to the SAT solver.
    fn add_theory_conflict_clause(
        &mut self,
        conflict: &[ay_core::TheoryLit],
        term_to_var: &BTreeMap<TermId, u32>,
    ) -> TheoryLoopResult {
        if conflict.is_empty() {
            return TheoryLoopResult::Unsat;
        }
        let clause: Vec<ay_sat::Literal> = conflict
            .iter()
            .filter_map(|lit| {
                term_to_var.get(&lit.term).map(|&cnf_var| {
                    let sat_var = ay_sat::Variable::new(cnf_var - 1);
                    if lit.value {
                        ay_sat::Literal::negative(sat_var)
                    } else {
                        ay_sat::Literal::positive(sat_var)
                    }
                })
            })
            .collect();
        if clause.is_empty() {
            return TheoryLoopResult::Unsat;
        }
        self.sat.add_clause_global(clause);
        TheoryLoopResult::ConflictAdded
    }

    /// Handle NeedSplit from the theory solver.
    fn handle_need_split(
        &mut self,
        split: ay_core::SplitRequest,
        term_to_var: &BTreeMap<TermId, u32>,
    ) -> TheoryLoopResult {
        let var_sort = self.own_smt.terms.sort(split.variable).clone();
        if !matches!(var_sort, Sort::Int | Sort::Real) {
            return TheoryLoopResult::Unknown;
        }

        let floor_term = self.own_smt.terms.mk_int(split.floor.clone());
        let ceil_term = self.own_smt.terms.mk_int(split.ceil.clone());
        let le_atom = self.own_smt.terms.mk_le(split.variable, floor_term);
        let ge_atom = self.own_smt.terms.mk_ge(split.variable, ceil_term);

        let le_var = self.get_or_alloc_theory_var(le_atom, term_to_var);
        let ge_var = self.get_or_alloc_theory_var(ge_atom, term_to_var);
        self.sat.ensure_num_vars(self.num_vars as usize);

        let le_sat = ay_sat::Variable::new(le_var - 1);
        let ge_sat = ay_sat::Variable::new(ge_var - 1);

        // #6358 phase-hint parity: bias split polarity from seed model.
        self.own_smt
            .apply_integer_split_phase_hint(&mut self.sat, le_sat, ge_sat, &split);

        self.sat.add_clause_global(vec![
            ay_sat::Literal::positive(le_sat),
            ay_sat::Literal::positive(ge_sat),
        ]);
        TheoryLoopResult::ConflictAdded
    }

    /// Handle NeedDisequalitySplit from the theory solver.
    fn handle_need_disequality_split(
        &mut self,
        split: ay_core::DisequalitySplitRequest,
        term_to_var: &BTreeMap<TermId, u32>,
    ) -> TheoryLoopResult {
        let var_sort = self.own_smt.terms.sort(split.variable).clone();
        let (left_atom, right_atom) = if var_sort == Sort::Int && split.excluded_value.is_integer()
        {
            let excluded = split.excluded_value.numer().clone();
            let le_bound = self
                .own_smt
                .terms
                .mk_int(&excluded - num_bigint::BigInt::from(1));
            let ge_bound = self
                .own_smt
                .terms
                .mk_int(&excluded + num_bigint::BigInt::from(1));
            (
                self.own_smt.terms.mk_le(split.variable, le_bound),
                self.own_smt.terms.mk_ge(split.variable, ge_bound),
            )
        } else if var_sort == Sort::Int {
            let floor_val = split.excluded_value.floor().to_integer();
            let ceil_val = split.excluded_value.ceil().to_integer();
            let le_bound = self.own_smt.terms.mk_int(floor_val);
            let ge_bound = self.own_smt.terms.mk_int(ceil_val);
            (
                self.own_smt.terms.mk_le(split.variable, le_bound),
                self.own_smt.terms.mk_ge(split.variable, ge_bound),
            )
        } else {
            let excluded_term = self.own_smt.terms.mk_rational(split.excluded_value.clone());
            (
                self.own_smt.terms.mk_lt(split.variable, excluded_term),
                self.own_smt.terms.mk_gt(split.variable, excluded_term),
            )
        };

        let lt_var = self.get_or_alloc_theory_var(left_atom, term_to_var);
        let gt_var = self.get_or_alloc_theory_var(right_atom, term_to_var);
        self.sat.ensure_num_vars(self.num_vars as usize);

        let lt_sat = ay_sat::Variable::new(lt_var - 1);
        let gt_sat = ay_sat::Variable::new(gt_var - 1);

        // #6358 phase-hint parity: bias split polarity from seed model.
        self.own_smt
            .apply_disequality_split_phase_hint(&mut self.sat, lt_sat, gt_sat, &split);

        self.sat.add_clause_global(vec![
            ay_sat::Literal::positive(lt_sat),
            ay_sat::Literal::positive(gt_sat),
        ]);
        TheoryLoopResult::ConflictAdded
    }

    /// Handle NeedExpressionSplit from the theory solver.
    fn handle_need_expression_split(
        &mut self,
        split: ay_core::ExpressionSplitRequest,
        term_to_var: &BTreeMap<TermId, u32>,
    ) -> TheoryLoopResult {
        let pair = match self.own_smt.terms.get(split.disequality_term) {
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2 && (name == "=" || name == "distinct") =>
            {
                Some((args[0], args[1]))
            }
            TermData::Not(inner) => match self.own_smt.terms.get(*inner) {
                TermData::App(Symbol::Named(name), args)
                    if args.len() == 2 && (name == "=" || name == "distinct") =>
                {
                    Some((args[0], args[1]))
                }
                _ => None,
            },
            _ => None,
        };

        let Some((lhs, rhs)) = pair else {
            return TheoryLoopResult::Unknown;
        };

        if !matches!(self.own_smt.terms.sort(lhs), Sort::Int | Sort::Real)
            || self.own_smt.terms.sort(lhs) != self.own_smt.terms.sort(rhs)
        {
            return TheoryLoopResult::Unknown;
        }

        let left_atom = self.own_smt.terms.mk_lt(lhs, rhs);
        let right_atom = self.own_smt.terms.mk_gt(lhs, rhs);

        let lt_var = self.get_or_alloc_theory_var(left_atom, term_to_var);
        let gt_var = self.get_or_alloc_theory_var(right_atom, term_to_var);
        self.sat.ensure_num_vars(self.num_vars as usize);

        let lt_sat = ay_sat::Variable::new(lt_var - 1);
        let gt_sat = ay_sat::Variable::new(gt_var - 1);
        self.sat.add_clause_global(vec![
            ay_sat::Literal::positive(lt_sat),
            ay_sat::Literal::positive(gt_sat),
        ]);
        TheoryLoopResult::ConflictAdded
    }

    /// Allocate or reuse a SAT variable for a theory-generated atom.
    pub(super) fn get_or_alloc_theory_var(
        &mut self,
        atom: TermId,
        term_to_var: &BTreeMap<TermId, u32>,
    ) -> u32 {
        if let Some(&var) = term_to_var.get(&atom) {
            return var;
        }
        if let Some(state) = &self.tseitin_state {
            if let Some(&var) = state.term_to_var.get(&atom) {
                return var;
            }
        }
        self.num_vars += 1;
        let var = self.num_vars;
        if let Some(state) = &mut self.tseitin_state {
            state.term_to_var.insert(atom, var);
            state.var_to_term.insert(var, atom);
            if state.next_var <= var {
                state.next_var = var + 1;
            }
        }
        var
    }
}
