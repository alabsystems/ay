// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core projection orchestration.
//!
//! Implements the main `project` and `project_with_residuals` entry points
//! that coordinate implicant extraction, bound-based variable elimination,
//! and MBQI fallback substitution.

use crate::{ChcExpr, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

use super::Mbp;

impl Mbp {
    /// Project away variables from a formula under a model
    ///
    /// Given a formula `phi`, variables to eliminate `vars`, and a model `M`,
    /// returns a formula `psi` such that:
    /// 1. M |= psi
    /// 2. psi implies (exists vars. phi)
    /// 3. psi does not contain any variable from `vars`
    ///
    /// REQUIRES: `model` satisfies `formula` (evaluating `formula` under `model` yields true).
    /// REQUIRES: `model` contains values for all free variables in `formula` that affect the
    ///   truth value (partial models are acceptable if they determine the relevant branches).
    ///
    /// ENSURES: The returned formula `psi` satisfies:
    ///   - `model |= psi` (the model satisfies the result)
    ///   - `psi` logically implies `exists vars_to_eliminate. formula` (soundness: weakening)
    ///   - For all `v` in `vars_to_eliminate`: `v` does not appear free in `psi` (completeness)
    ///   - If `vars_to_eliminate` is empty, returns `formula.clone()` unchanged.
    ///
    /// Note: The result may be more specific than the optimal existential projection
    ///   (i.e., `psi` may imply but not be equivalent to `exists vars. phi`). This is sound
    ///   for PDR/IC3 where we need under-approximations of predecessor states.
    pub fn project(
        &self,
        formula: &ChcExpr,
        vars_to_eliminate: &[ChcVar],
        model: &FxHashMap<String, SmtValue>,
    ) -> ChcExpr {
        if vars_to_eliminate.is_empty() {
            return formula.clone();
        }

        // Partition variables by sort category:
        // - Bool: substitute with model values
        // - BV: project via unsigned interval elimination (BV MBP)
        // - Array: project via model-based Ackermannization (#6047)
        // - Int/Real: project via Fourier-Motzkin / Loos-Weispfenning
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
        for var in &subst_vars {
            let value = Self::model_value_expr(var, model);
            if let Some(expr) = value {
                current = current.substitute(&[((*var).clone(), expr)]);
            }
        }

        if project_vars.is_empty() {
            return current.simplify_constants();
        }

        // 3-way sort partition: Array > DT > Arithmetic.
        // DT projection may introduce fresh scalar variables (selector fields)
        // that arithmetic projection can handle.
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

        // Extract implicant (the literals that are true under model)
        let implicant = self.get_implicant(&current, model);

        // Pre-compute per-literal variable name sets (O(L*T) total, one tree walk each).
        // This avoids O(V*L*T) repeated tree walks in the partitioning loop below (#2956).
        let lit_var_sets: Vec<FxHashSet<String>> = implicant
            .iter()
            .map(|lit| lit.atom.vars().into_iter().map(|v| v.name).collect())
            .collect();

        // Partition vars into projectable vs fallback.
        // See #759: Instead of bailing out entirely when any var is unprojectable,
        // we substitute fallback vars with model values and project only the rest.
        // This produces a more general result than the old all-or-nothing approach.
        let mut projectable_vars: Vec<&ChcVar> = Vec::new();
        let mut fallback_vars: Vec<&ChcVar> = Vec::new();

        for var in &arith_vars {
            // BV vars always go through project_bitvec_var which handles mixed
            // projectable/unhandled literals internally (model-value fallback
            // for unhandled, interval resolution for BV bounds).
            if matches!(&var.sort, ChcSort::BitVec(_)) {
                projectable_vars.push(var);
                continue;
            }
            // Check if this var is projectable in ALL literals that mention it.
            // Uses pre-computed var sets for O(1) contains check instead of tree walk (#2956).
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

        // If there are fallback vars, try MBQI-style term substitution first (#892).
        // This finds equivalent terms in the formula (more general than model values).
        // Falls back to model values if no equivalent term is found.
        let implicant = if fallback_vars.is_empty() {
            implicant
        } else {
            // Collect candidate terms from the current formula for MBQI substitution
            let candidate_terms = Self::collect_candidate_terms(&current);

            // Build substitution: try MBQI term substitution, fall back to model value
            let subst: Vec<(ChcVar, ChcExpr)> = fallback_vars
                .iter()
                .map(|var| {
                    // Try MBQI: find a term that evaluates to the same value and doesn't contain var
                    let mbqi_term = self.find_equivalent_term(var, &candidate_terms, model);
                    let value =
                        mbqi_term.unwrap_or_else(|| Self::model_value_expr_or_default(var, model));
                    ((*var).clone(), value)
                })
                .collect();

            let substituted = current.substitute(&subst);
            self.get_implicant(&substituted, model)
        };

        // Expand DT constructor equalities into per-field constraints (Spacer-style).
        // Must run before DT projection so the projector sees atomic constraints.
        // Ref: Z3 spacer_util.cpp:344-355 (expand_literals).
        let mut projected = implicant;
        if !dt_vars.is_empty() {
            Self::expand_dt_literals(&mut projected);
        }

        // Saturate array extensionality: for `a != b` where both are arrays
        // with known model values, add witnessing `select(a,k) != select(b,k)`.
        // Ref: Z3 mbp_arrays.cpp:1228-1272.
        if !array_vars.is_empty() {
            self.saturate_array_disequalities(&mut projected, model);
        }

        // Augmented model: array projection creates fresh variables (__mbp_sel_*,
        // __mbp_arr_*) whose model values must be tracked so downstream phases
        // (FM projection, Ackermannization, DT projection) can evaluate
        // expressions containing them. Matches Z3 mbp_arrays.cpp:194-195, :922-923.
        let mut augmented_model = model.clone();

        // Project array variables first via model-based Ackermannization (#6047).
        // Array projection may introduce fresh scalar variables (which the
        // subsequent arithmetic projection can handle).
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

        // Iterative loop: re-project fresh scalar variables from array projection.
        // Array MBP creates __mbp_sel_* and __mbp_arr_* variables that need
        // arithmetic (FM) or BV projection. Ref: Z3 spacer_util.cpp:191-250.
        projected = self.project_fresh_mbp_vars(projected, &augmented_model);

        // Project DT variables second. DT projection creates fresh selector
        // variables that get projected by arithmetic/BV projectors below.
        // Ref: Z3 mbp_datatypes.cpp project_nonrec.
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
                        // Substitute Bool fresh vars with model values immediately
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
                    // BV fresh vars: use BV MBP (same as Int/Real fresh vars)
                    _ => extra_arith_vars.push(fv),
                }
            }
        }

        // Use augmented model (with DT fresh var values) for projection.
        let proj_model = if extra_arith_vars.is_empty() {
            model
        } else {
            &augmented_model
        };

        // Project out each projectable arithmetic/BV variable
        for var in &projectable_vars {
            projected = self.project_single_var(var, projected, proj_model);
        }

        // Project fresh vars introduced by DT projection (arith + BV)
        for var in &extra_arith_vars {
            projected = self.project_single_var(var, projected, &augmented_model);
        }

        // Verify that all vars_to_eliminate are actually eliminated.
        // If any remain (due to bugs in projection logic), substitute them.
        // Pre-compute result var names once to avoid O(V*T) repeated tree walks (#2956).
        let result = self.implicant_to_formula(&projected);
        let result_var_names: FxHashSet<String> =
            result.vars().into_iter().map(|v| v.name).collect();
        let all_vars: Vec<&ChcVar> = array_vars
            .iter()
            .chain(dt_vars.iter())
            .chain(arith_vars.iter())
            .copied()
            .collect();
        let remaining_vars: Vec<&ChcVar> = all_vars
            .iter()
            .filter(|v| result_var_names.contains(&v.name))
            .copied()
            .collect();

        if remaining_vars.is_empty() {
            return result;
        }

        // Fallback: try MBQI term substitution first, then model values (#892).
        // This ensures we ALWAYS return a formula without vars_to_eliminate.
        // Per Z3's spacer_util.cpp:279-287 and :854-907, substitution fallback is standard practice.
        let candidate_terms = Self::collect_candidate_terms(&result);
        let final_subst: Vec<(ChcVar, ChcExpr)> = remaining_vars
            .iter()
            .map(|var| {
                // Try MBQI: find equivalent term that doesn't contain var
                let mbqi_term = self.find_equivalent_term(var, &candidate_terms, model);
                let value =
                    mbqi_term.unwrap_or_else(|| Self::model_value_expr_or_default(var, model));
                ((*var).clone(), value)
            })
            .collect();

        // Substitute in the projected result (not working_formula) to preserve projection work.
        result.substitute(&final_subst).simplify_constants()
    }

    /// Convert a model value for `var` to a `ChcExpr` literal, if available.
    ///
    /// Used by projection routines to substitute variables with their concrete
    /// model values. Returns `None` if the model has no entry for this variable
    /// or the entry's sort doesn't match.
    pub(super) fn model_value_expr(
        var: &ChcVar,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        match (&var.sort, model.get(&var.name)) {
            (ChcSort::Bool, Some(SmtValue::Bool(b))) => Some(ChcExpr::Bool(*b)),
            (ChcSort::Int, Some(SmtValue::Int(n))) => Some(ChcExpr::Int(*n)),
            (ChcSort::Int, Some(SmtValue::BigInt(n))) => {
                Some(ChcExpr::from_bigint(n.as_ref().clone()))
            }
            (ChcSort::Real, Some(SmtValue::Real(r))) => {
                use num_traits::ToPrimitive;
                let n = r.numer().to_i64()?;
                let d = r.denom().to_i64()?;
                Some(ChcExpr::Real(n, d))
            }
            (
                ChcSort::BitVec(expected_width),
                Some(
                    value @ (SmtValue::BitVec(_, actual_width)
                    | SmtValue::BigBitVec(_, actual_width)),
                ),
            ) if expected_width == actual_width => value.bitvec_to_chc_expr(),
            // DT constructor application from model pipeline.
            (ChcSort::Datatype { .. }, Some(SmtValue::Datatype(ctor, fields))) => {
                let field_exprs: Vec<std::sync::Arc<ChcExpr>> = fields
                    .iter()
                    .map(|f| Self::smt_value_to_expr(f).map(std::sync::Arc::new))
                    .collect::<Option<_>>()?;
                Some(ChcExpr::FuncApp(
                    ctor.clone(),
                    var.sort.clone(),
                    field_exprs,
                ))
            }
            // Nullary DT constructors may come as Opaque strings.
            (ChcSort::Datatype { constructors, .. }, Some(SmtValue::Opaque(s))) => constructors
                .iter()
                .find(|c| c.selectors.is_empty() && c.name == *s)
                .map(|c| ChcExpr::FuncApp(c.name.clone(), var.sort.clone(), vec![])),
            _ => None,
        }
    }

    /// Like `model_value_expr`, but returns a sort-appropriate default on missing values.
    ///
    /// Used in MBQI fallback paths where a concrete value is required (force mode).
    pub(super) fn model_value_expr_or_default(
        var: &ChcVar,
        model: &FxHashMap<String, SmtValue>,
    ) -> ChcExpr {
        Self::model_value_expr(var, model).unwrap_or(match &var.sort {
            ChcSort::Bool => ChcExpr::Bool(false),
            ChcSort::Int => ChcExpr::Int(0),
            ChcSort::Real => ChcExpr::Real(0, 1),
            ChcSort::BitVec(w) => ChcExpr::BitVec(0, *w),
            ChcSort::Datatype { constructors, .. } => {
                // Sound default: first nullary constructor, or first constructor
                // with recursively-defaulted arguments.
                if let Some(ctor) = constructors.iter().find(|c| c.selectors.is_empty()) {
                    ChcExpr::FuncApp(ctor.name.clone(), var.sort.clone(), vec![])
                } else if let Some(ctor) = constructors.first() {
                    let default_args: Vec<std::sync::Arc<ChcExpr>> = ctor
                        .selectors
                        .iter()
                        .map(|sel| {
                            std::sync::Arc::new(Self::model_value_expr_or_default(
                                &ChcVar {
                                    name: String::new(),
                                    sort: sel.sort.clone(),
                                },
                                model,
                            ))
                        })
                        .collect();
                    ChcExpr::FuncApp(ctor.name.clone(), var.sort.clone(), default_args)
                } else {
                    ChcExpr::Int(0)
                }
            }
            _ => ChcExpr::Int(0),
        })
    }

    /// Convert an SmtValue to a ChcExpr (for DT field values in model_value_expr).
    fn smt_value_to_expr(val: &SmtValue) -> Option<ChcExpr> {
        Some(match val {
            SmtValue::Bool(b) => ChcExpr::Bool(*b),
            SmtValue::Int(n) => ChcExpr::Int(*n),
            SmtValue::BigInt(n) => ChcExpr::from_bigint(n.as_ref().clone()),
            SmtValue::Real(r) => {
                use num_traits::ToPrimitive;
                let n = r.numer().to_i64()?;
                let d = r.denom().to_i64()?;
                ChcExpr::Real(n, d)
            }
            SmtValue::BitVec(..) | SmtValue::BigBitVec(..) => val.bitvec_to_chc_expr()?,
            SmtValue::Datatype(ctor, fields) => {
                let field_exprs: Vec<std::sync::Arc<ChcExpr>> = fields
                    .iter()
                    .map(|f| Self::smt_value_to_expr(f).map(std::sync::Arc::new))
                    .collect::<Option<_>>()?;
                // Best-effort sort: no sort info available in SmtValue, so use
                // Uninterpreted as a placeholder. Callers with sort info
                // (model_value_expr) use the correct DT sort for the top level.
                ChcExpr::FuncApp(
                    ctor.clone(),
                    ChcSort::Uninterpreted(ctor.clone()),
                    field_exprs,
                )
            }
            SmtValue::Opaque(_) | SmtValue::ConstArray(_) | SmtValue::ArrayMap { .. } => {
                return None;
            }
        })
    }
}
