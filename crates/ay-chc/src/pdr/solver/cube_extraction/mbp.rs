// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-based projection (MBP) cube extraction.
//!
//! Given a satisfiable formula and model, uses MBP to project out auxiliary
//! variables and produce generalized predecessor cubes. Includes residual
//! variable handling and augmentation for unconstrained canonical vars.

use super::super::{
    ChcExpr, ChcSort, ChcVar, FxHashMap, FxHashSet, PdrSolver, PredicateId, SmtValue,
};

pub(super) struct CubeMbpInputs {
    pub(super) canonical_vars: Vec<ChcVar>,
    pub(super) renamed_formula: ChcExpr,
    pub(super) renamed_model: FxHashMap<String, SmtValue>,
    pub(super) vars_to_eliminate: Vec<ChcVar>,
}

impl PdrSolver {
    #[cfg_attr(not(test), allow(dead_code))]
    pub(in crate::pdr::solver) fn cube_from_model_mbp(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        formula: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<ChcExpr> {
        let inputs = self.prepare_cube_mbp_inputs(pred, args, formula, model)?;
        self.cube_from_model_mbp_with_inputs(pred, args, formula, model, inputs)
    }

    pub(super) fn prepare_cube_mbp_inputs(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        formula: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
    ) -> Option<CubeMbpInputs> {
        let canonical_vars = self.canonical_vars(pred)?.to_vec();
        if canonical_vars.len() != args.len() {
            return None;
        }

        let mut arg_var_names: FxHashSet<String> = FxHashSet::default();
        let mut substitutions: Vec<(ChcVar, ChcExpr)> = Vec::new();
        let mut proxy_equalities: Vec<ChcExpr> = Vec::new();
        let mut proxy_expr_map: FxHashMap<String, ChcExpr> = FxHashMap::default();
        let mut used_names: FxHashSet<String> = FxHashSet::default();
        for var in formula.vars() {
            used_names.insert(var.name);
        }
        for arg in args {
            for var in arg.vars() {
                used_names.insert(var.name);
            }
        }
        for canonical_var in &canonical_vars {
            used_names.insert(canonical_var.name.clone());
        }
        for model_name in model.keys() {
            used_names.insert(model_name.clone());
        }
        let mut proxy_counter = 0usize;

        for (arg, canon) in args.iter().zip(canonical_vars.iter()) {
            match arg {
                ChcExpr::Var(v) => {
                    arg_var_names.insert(v.name.clone());
                    if v != canon {
                        substitutions.push((v.clone(), ChcExpr::var(canon.clone())));
                    }
                }
                expr => {
                    for v in expr.vars() {
                        arg_var_names.insert(v.name.clone());
                    }
                    let proxy = loop {
                        let candidate = format!("__mbp_head_{proxy_counter}");
                        proxy_counter += 1;
                        if used_names.insert(candidate.clone()) {
                            break ChcVar::new(candidate, canon.sort.clone());
                        }
                    };
                    arg_var_names.insert(proxy.name.clone());
                    proxy_equalities.push(ChcExpr::eq(ChcExpr::var(proxy.clone()), expr.clone()));
                    proxy_expr_map.insert(canon.name.clone(), expr.clone());
                    substitutions.push((proxy, ChcExpr::var(canon.clone())));
                }
            }
        }

        let augmented_formula = if proxy_equalities.is_empty() {
            formula.clone()
        } else {
            let mut conjuncts = proxy_equalities;
            conjuncts.push(formula.clone());
            ChcExpr::and_all(conjuncts)
        };

        let all_vars = augmented_formula.vars();
        let vars_to_eliminate: Vec<ChcVar> = all_vars
            .into_iter()
            .filter(|v| !arg_var_names.contains(&v.name))
            .collect();

        let renamed_formula = if substitutions.is_empty() {
            augmented_formula
        } else {
            augmented_formula.substitute(&substitutions)
        };

        let renamed_model = if substitutions.is_empty() {
            model.clone()
        } else {
            let mut rm = model.clone();
            for (original_var, canonical_expr) in &substitutions {
                if let ChcExpr::Var(canonical_var) = canonical_expr {
                    if let Some(val) = model.get(&original_var.name) {
                        rm.insert(canonical_var.name.clone(), val.clone());
                    } else if let Some(expr_arg) = proxy_expr_map.get(&canonical_var.name) {
                        if let Some(val) = crate::expr::evaluate_expr(expr_arg, model) {
                            rm.insert(canonical_var.name.clone(), val.clone());
                            rm.insert(original_var.name.clone(), val);
                        }
                    }
                }
            }
            rm
        };

        Some(CubeMbpInputs {
            canonical_vars,
            renamed_formula,
            renamed_model,
            vars_to_eliminate,
        })
    }

    pub(super) fn should_attempt_cube_mbp(inputs: &CubeMbpInputs) -> bool {
        let pred_has_bv = inputs
            .canonical_vars
            .iter()
            .any(|var| matches!(var.sort, ChcSort::BitVec(_)));
        !pred_has_bv
            || inputs
                .vars_to_eliminate
                .iter()
                .all(|var| matches!(var.sort, ChcSort::Bool | ChcSort::BitVec(_)))
    }

    pub(super) fn cube_from_model_mbp_with_inputs(
        &self,
        pred: PredicateId,
        args: &[ChcExpr],
        formula: &ChcExpr,
        model: &FxHashMap<String, SmtValue>,
        inputs: CubeMbpInputs,
    ) -> Option<ChcExpr> {
        let CubeMbpInputs {
            canonical_vars,
            renamed_formula,
            renamed_model,
            vars_to_eliminate,
        } = inputs;

        if vars_to_eliminate.is_empty() {
            let implicant = self.mbp.implicant_cube(&renamed_formula, &renamed_model);
            let result = self.filter_to_canonical_vars(&implicant, &canonical_vars);

            if result == ChcExpr::Bool(true) {
                return self.cube_from_model_or_constraints(pred, args, formula, model);
            }

            let result_vars = result.vars();
            let all_constrained = canonical_vars
                .iter()
                .all(|cv| result_vars.iter().any(|rv| rv.name == cv.name));
            if all_constrained {
                return Some(result);
            }

            return self.cube_from_model_or_constraints(pred, args, formula, model);
        }

        let mbp_result = self.mbp.project_with_mode(
            &renamed_formula,
            &vars_to_eliminate,
            &renamed_model,
            crate::mbp::MbpMode::AllowResidual,
        );

        let result = if mbp_result.residual_vars.is_empty() {
            mbp_result.formula
        } else {
            let mut subst: Vec<(ChcVar, ChcExpr)> =
                Vec::with_capacity(mbp_result.residual_vars.len());
            let mut array_residual_conjuncts: Vec<ChcExpr> = Vec::new();
            for var in &mbp_result.residual_vars {
                if matches!(var.sort, ChcSort::Array(_, _)) {
                    if let Some(select_conjuncts) =
                        Self::array_select_constraints_from_model(var, renamed_model.get(&var.name))
                    {
                        array_residual_conjuncts.extend(select_conjuncts);
                    }
                    continue;
                }
                if matches!(var.sort, ChcSort::Datatype { .. }) {
                    if let Some(dt_conjuncts) =
                        Self::dt_constraints_from_model(var, renamed_model.get(&var.name))
                    {
                        array_residual_conjuncts.extend(dt_conjuncts);
                    }
                    continue;
                }
                let value = match (var.sort.clone(), renamed_model.get(&var.name)) {
                    (ChcSort::Int, Some(SmtValue::Int(n))) => Some(ChcExpr::Int(*n)),
                    (ChcSort::Bool, Some(SmtValue::Bool(b))) => Some(ChcExpr::Bool(*b)),
                    (ChcSort::BitVec(_), Some(SmtValue::BitVec(v, w))) => {
                        Some(ChcExpr::BitVec(*v, *w))
                    }
                    _ => None,
                };
                let Some(value) = value else {
                    return self.cube_from_model_or_constraints(pred, args, formula, model);
                };
                subst.push((var.clone(), value));
            }
            let mut projected = mbp_result.formula.substitute(&subst);
            if !array_residual_conjuncts.is_empty() {
                array_residual_conjuncts.insert(0, projected);
                projected = ChcExpr::and_all(array_residual_conjuncts);
            }
            projected
        };

        let projected_vars = result.vars();
        let has_non_canonical = projected_vars
            .iter()
            .filter(|v| !matches!(v.sort, ChcSort::Array(_, _) | ChcSort::Datatype { .. }))
            .any(|v| !canonical_vars.iter().any(|cv| cv.name == v.name));

        if has_non_canonical {
            return self.cube_from_model_or_constraints(pred, args, formula, model);
        }

        if result == ChcExpr::Bool(true) {
            self.cube_from_model_or_constraints(pred, args, formula, model)
        } else {
            let result_vars = result.vars();
            let unconstrained: Vec<&ChcVar> = canonical_vars
                .iter()
                .filter(|cv| !result_vars.iter().any(|rv| rv.name == cv.name))
                .collect();
            if unconstrained.is_empty() {
                Some(result)
            } else {
                let mut augment = Vec::with_capacity(unconstrained.len() + 1);
                augment.push(result);
                for var in &unconstrained {
                    if matches!(var.sort, ChcSort::Array(_, _)) {
                        if let Some(select_conjuncts) = Self::array_select_constraints_from_model(
                            var,
                            renamed_model.get(&var.name),
                        ) {
                            augment.extend(select_conjuncts);
                        }
                        continue;
                    }
                    if matches!(var.sort, ChcSort::Datatype { .. }) {
                        if let Some(dt_conjuncts) =
                            Self::dt_constraints_from_model(var, renamed_model.get(&var.name))
                        {
                            augment.extend(dt_conjuncts);
                        }
                        continue;
                    }
                    let val = match (var.sort.clone(), renamed_model.get(&var.name)) {
                        (ChcSort::Int, Some(SmtValue::Int(n))) => {
                            Some(ChcExpr::eq(ChcExpr::var((*var).clone()), ChcExpr::int(*n)))
                        }
                        (ChcSort::Bool, Some(SmtValue::Bool(b))) => {
                            Some(ChcExpr::eq(ChcExpr::var((*var).clone()), ChcExpr::Bool(*b)))
                        }
                        (ChcSort::BitVec(_), Some(SmtValue::BitVec(v, w))) => Some(ChcExpr::eq(
                            ChcExpr::var((*var).clone()),
                            ChcExpr::BitVec(*v, *w),
                        )),
                        _ => None,
                    };
                    match val {
                        Some(eq) => augment.push(eq),
                        None => {
                            return self.cube_from_model_or_constraints(pred, args, formula, model);
                        }
                    }
                }
                let augmented = ChcExpr::and_all(augment);
                if self.mbp.eval_bool(&augmented, &renamed_model) == Some(false) {
                    safe_eprintln!("BUG: augmented MBP cube is not satisfied by renamed model — falling back to point cube (#3095)");
                    return self.cube_from_model_or_constraints(pred, args, formula, model);
                }
                Some(augmented)
            }
        }
    }
}
