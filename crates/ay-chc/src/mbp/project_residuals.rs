// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Residual-tracking projection for MBP.
//!
//! `project_with_residuals` returns unprojectable variables as residuals
//! instead of substituting them with model values. Used for PDR blocking
//! where the caller needs to know which variables survived projection.

use crate::{ChcExpr, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::{Mbp, MbpResult};

impl Mbp {
    /// Project with residual variable tracking (allow-residual mode).
    ///
    /// Like `project()`, but instead of substituting unprojectable variables
    /// with model values, returns them as residual_vars. The caller can then
    /// skolemize these (Z3 Spacer pattern) or substitute them as needed.
    ///
    /// This matches Z3's `qe_project(..., dont_sub=true)` mode used in
    /// `create_next_child` (spacer_context.cpp:281-333).
    ///
    /// REQUIRES: `model` satisfies `formula`
    /// ENSURES: `result.formula` does not contain any projected vars except residual_vars
    pub fn project_with_residuals(
        &self,
        formula: &ChcExpr,
        vars_to_eliminate: &[ChcVar],
        model: &FxHashMap<String, SmtValue>,
    ) -> MbpResult {
        if vars_to_eliminate.is_empty() {
            return MbpResult {
                formula: formula.clone(),
                residual_vars: vec![],
            };
        }

        // Partition variables by sort category (same as project()).
        let mut subst_vars: Vec<&ChcVar> = Vec::new();
        let mut project_vars: Vec<&ChcVar> = Vec::new();
        for v in vars_to_eliminate {
            match &v.sort {
                ChcSort::Bool => subst_vars.push(v),
                ChcSort::BitVec(_) => project_vars.push(v),
                _ => project_vars.push(v),
            }
        }

        let mut current = formula.clone();
        let mut subst_residuals: Vec<ChcVar> = Vec::new();
        for var in &subst_vars {
            let value = Self::model_value_expr(var, model);
            if let Some(expr) = value {
                current = current.substitute(&[((*var).clone(), expr)]);
            } else {
                subst_residuals.push((*var).clone());
            }
        }

        // 3-way sort partition (same as project()).
        let mut array_vars: Vec<&ChcVar> = Vec::new();
        let mut dt_vars: Vec<&ChcVar> = Vec::new();
        let mut arith_vars: Vec<&ChcVar> = Vec::new();
        for v in project_vars {
            match &v.sort {
                ChcSort::Array(_, _) => array_vars.push(v),
                ChcSort::Datatype { .. } => dt_vars.push(v),
                _ => arith_vars.push(v),
            }
        }

        if array_vars.is_empty() && dt_vars.is_empty() && arith_vars.is_empty() {
            return MbpResult {
                formula: current.simplify_constants(),
                residual_vars: subst_residuals,
            };
        }

        // Extract implicant
        let implicant = self.get_implicant(&current, model);

        // Pre-compute per-literal variable name sets (one tree walk each, #2956).
        let lit_var_sets: Vec<FxHashSet<String>> = implicant
            .iter()
            .map(|lit| lit.atom.vars().into_iter().map(|v| v.name).collect())
            .collect();

        // Partition vars into projectable vs fallback
        let mut projectable_vars: Vec<&ChcVar> = Vec::new();
        let mut fallback_vars: Vec<&ChcVar> = Vec::new();

        for var in &arith_vars {
            // BV vars go through project_bitvec_var, but only if the model has a value.
            // Without a model value, BV projection can silently eliminate variables
            // (via equality substitution) without producing correct residuals (#7217).
            if matches!(&var.sort, ChcSort::BitVec(_)) {
                if model.contains_key(&var.name) {
                    projectable_vars.push(var);
                } else {
                    fallback_vars.push(var);
                }
                continue;
            }
            let has_unprojectable = implicant
                .iter()
                .zip(lit_var_sets.iter())
                .any(|(lit, vars)| {
                    vars.contains(&var.name) && !self.is_projectable_literal(lit, var)
                });
            if has_unprojectable {
                fallback_vars.push(var);
            } else {
                projectable_vars.push(var);
            }
        }

        // For fallback vars, try MBQI-style term substitution first.
        // Unlike project(), we do NOT fall back to model values — unprojectable vars
        // become residuals that the caller can skolemize.
        let (implicant, mbqi_residuals) = if fallback_vars.is_empty() {
            (implicant, vec![])
        } else {
            let candidate_terms = Self::collect_candidate_terms(&current);
            let mut residual = Vec::new();
            let mut subst: Vec<(ChcVar, ChcExpr)> = Vec::new();

            for var in &fallback_vars {
                let mbqi_term = self.find_equivalent_term(var, &candidate_terms, model);
                if let Some(term) = mbqi_term {
                    subst.push(((*var).clone(), term));
                } else {
                    residual.push((*var).clone());
                }
            }

            if !subst.is_empty() {
                let substituted = current.substitute(&subst);
                (self.get_implicant(&substituted, model), residual)
            } else {
                (implicant, residual)
            }
        };

        // Expand DT constructor equalities (same as project()).
        let mut projected = implicant;
        if !dt_vars.is_empty() {
            Self::expand_dt_literals(&mut projected);
        }

        // Saturate array extensionality (same as project()).
        if !array_vars.is_empty() {
            self.saturate_array_disequalities(&mut projected, model);
        }

        // Augmented model for fresh variable tracking (same as project()).
        let mut augmented_model = model.clone();

        // Project array variables first via model-based Ackermannization (#6047).
        for var in &array_vars {
            let (with_var, without_var): (Vec<_>, Vec<_>) = projected
                .into_iter()
                .partition(|lit| lit.atom.contains_var_name(&var.name));
            if with_var.is_empty() {
                projected = without_var;
                continue;
            }
            let (result, fresh) =
                self.project_array_var_with_fresh(var, with_var, without_var, &augmented_model);
            projected = result;
            for (fv, fval) in fresh {
                augmented_model.insert(fv.name.clone(), fval);
            }
        }

        // Iterative loop for fresh variables (same as project()).
        projected = self.project_fresh_mbp_vars(projected, &augmented_model);
        let mut extra_arith_vars: Vec<ChcVar> = Vec::new();
        for var in &dt_vars {
            let (with_var, without_var): (Vec<_>, Vec<_>) = projected
                .into_iter()
                .partition(|lit| lit.atom.contains_var_name(&var.name));
            if with_var.is_empty() {
                projected = without_var;
                continue;
            }
            let (result, fresh) =
                self.project_datatype_var_with_fresh(var, with_var, without_var, model);
            projected = result;
            for (fv, fval) in fresh {
                augmented_model.insert(fv.name.clone(), fval);
                match &fv.sort {
                    ChcSort::Bool => {
                        if let Some(val) = Self::model_value_expr(&fv, &augmented_model) {
                            projected = projected
                                .into_iter()
                                .map(|lit| {
                                    let new_atom =
                                        lit.atom.substitute(&[(fv.clone(), val.clone())]);
                                    super::Literal::new(new_atom.simplify_constants(), lit.positive)
                                })
                                .filter(|lit| lit.atom != ChcExpr::Bool(true))
                                .collect();
                        }
                    }
                    _ => extra_arith_vars.push(fv),
                }
            }
        }

        let proj_model = if extra_arith_vars.is_empty() {
            model
        } else {
            &augmented_model
        };

        // Project out each projectable arithmetic/BV variable.
        for var in &projectable_vars {
            projected = self.project_single_var(var, projected, proj_model);
        }

        // Project fresh vars introduced by DT projection (arith + BV)
        for var in &extra_arith_vars {
            projected = self.project_single_var(var, projected, &augmented_model);
        }

        let result = self.implicant_to_formula(&projected);

        // Collect all residuals: MBQI failures + projection failures.
        // Pre-compute result var names once to avoid O(V*T) repeated tree walks (#2956).
        let result_var_names: FxHashSet<String> =
            result.vars().into_iter().map(|v| v.name).collect();
        let mut all_residuals = subst_residuals;
        for var in mbqi_residuals {
            if !all_residuals.iter().any(|r| r == &var) {
                all_residuals.push(var);
            }
        }
        let all_project_vars: Vec<&ChcVar> = array_vars
            .iter()
            .chain(dt_vars.iter())
            .chain(arith_vars.iter())
            .copied()
            .collect();
        for var in &all_project_vars {
            if result_var_names.contains(&var.name) && !all_residuals.iter().any(|r| r == *var) {
                all_residuals.push((*var).clone());
            }
        }

        MbpResult {
            formula: result,
            residual_vars: all_residuals,
        }
    }

    /// Re-project fresh scalar variables introduced by array MBP.
    ///
    /// Array projection creates `__mbp_sel_*` and `__mbp_arr_*` variables as
    /// placeholders for `select(arr, idx)` terms. These fresh variables are
    /// scalar-sorted (Int, Real, BV) and may appear in bounds that the
    /// Fourier-Motzkin or BV projector can eliminate.
    ///
    /// Without this loop, fresh variables survive to the final fallback which
    /// substitutes them with model values — losing precision. The loop
    /// iterates because projecting one fresh var may expose another.
    ///
    /// Bounded to 5 iterations (convergent in practice; Z3 does not bound
    /// this but always converges because each iteration eliminates at least
    /// one variable or leaves the set unchanged).
    ///
    /// Ref: Z3 `spacer_util.cpp:191-250` (iterative QE loop).
    pub(super) fn project_fresh_mbp_vars(
        &self,
        mut projected: Vec<super::Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<super::Literal> {
        let mut seen_fresh: FxHashSet<String> = FxHashSet::default();
        for _ in 0..5 {
            let mut fresh_vars: Vec<ChcVar> = Vec::new();
            let mut fresh_names: FxHashSet<String> = FxHashSet::default();
            for lit in &projected {
                for v in lit.atom.vars() {
                    if v.name.starts_with("__mbp_")
                        && !seen_fresh.contains(&v.name)
                        && fresh_names.insert(v.name.clone())
                    {
                        fresh_vars.push(v);
                    }
                }
            }
            if fresh_vars.is_empty() {
                break;
            }
            // Only project fresh vars that are projectable in ALL their
            // mentioning literals. Fresh vars inside store/select terms
            // (e.g., __mbp_arr_* inside store(b, idx, fresh)) are not
            // FM-projectable and would cause the projector to drop
            // constraints. Skip them — the final fallback substitution
            // handles these.
            let projectable: Vec<ChcVar> = fresh_vars
                .into_iter()
                .filter(|v| {
                    projected.iter().all(|lit| {
                        if lit.atom.contains_var_name(&v.name) {
                            self.is_projectable_literal(lit, v)
                        } else {
                            true
                        }
                    })
                })
                .collect();
            if projectable.is_empty() {
                break;
            }
            for v in &projectable {
                seen_fresh.insert(v.name.clone());
            }
            for var in &projectable {
                projected = self.project_single_var(var, projected, model);
            }
        }
        projected
    }
}
