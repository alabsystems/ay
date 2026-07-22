// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Datatype projection for MBP.
//!
//! Eliminates DT-sorted variables by constructor unfolding: given a model
//! value `var = C(v0, ..., vn)`, creates fresh selector variables and
//! substitutes `var → C(fresh_0, ..., fresh_n)`.
//!
//! Algorithm: Z3 `project_nonrec` (`reference/z3/src/qe/mbp/mbp_datatypes.cpp:68`).
//! Scope: non-recursive datatypes only (covers flat structs, enums, tuples).

use crate::{ChcExpr, ChcSort, ChcVar, SmtValue};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::sync::Arc;

use super::{Literal, Mbp};

impl Mbp {
    /// Project out a single datatype variable by constructor unfolding.
    ///
    /// Returns the projected literals AND the fresh variables with their model
    /// values. The caller must add the fresh variables to the model and project
    /// them via their respective theory projectors.
    ///
    /// Algorithm (Z3 `project_nonrec`, mbp_datatypes.cpp:68):
    /// 1. Evaluate `var` in model → get constructor C and field values.
    /// 2. Create fresh variable for each selector of C.
    /// 3. Substitute var → C(fresh_0, ..., fresh_n) in all literals.
    /// 4. If sort has >1 constructor, add recognizer literal.
    /// 5. Return modified literals + fresh vars for further projection.
    pub(super) fn project_datatype_var(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        without_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        let (result, _fresh) =
            self.project_datatype_var_with_fresh(var, with_var, without_var, model);
        result
    }

    /// Project a DT variable and return fresh selector variables for further projection.
    pub(super) fn project_datatype_var_with_fresh(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        mut without_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> (Vec<Literal>, Vec<(ChcVar, SmtValue)>) {
        // Step 1: Get constructor metadata from the sort.
        let constructors = match &var.sort {
            ChcSort::Datatype { constructors, .. } => constructors.clone(),
            _ => return (without_var, vec![]),
        };

        // Step 2: Get constructor from model value.
        let (ctor_name, field_values) = match model.get(&var.name) {
            Some(SmtValue::Opaque(name))
                // Nullary constructor: match by name
                if constructors.iter().any(|c| c.name == *name) => {
                    (name.clone(), vec![])
                }
            Some(SmtValue::Datatype(name, fields))
                // Non-nullary (or nullary) constructor with field values.
                if constructors.iter().any(|c| c.name == *name) => {
                    (name.clone(), fields.clone())
                }
            _ => {
                // No recognized DT model value. Fall back to model-value substitution.
                return (
                    self.dt_fallback_substitute(var, with_var, without_var, model),
                    vec![],
                );
            }
        };

        let ctor_meta = match constructors.iter().find(|c| c.name == ctor_name) {
            Some(c) => c,
            None => {
                return (
                    self.dt_fallback_substitute(var, with_var, without_var, model),
                    vec![],
                )
            }
        };

        // Step 3: Create fresh variables for each selector field.
        let fresh_vars: Vec<(ChcVar, SmtValue)> = ctor_meta
            .selectors
            .iter()
            .enumerate()
            .map(|(i, sel)| {
                let fresh_name = format!("{}__{}", var.name, sel.name);
                let fresh_var = ChcVar {
                    name: fresh_name,
                    sort: sel.sort.clone(),
                };
                let fresh_val = field_values.get(i).cloned().unwrap_or(SmtValue::Int(0));
                (fresh_var, fresh_val)
            })
            .collect();

        // Step 4: Build substitution term: C(fresh_0, ..., fresh_n)
        let fresh_args: Vec<Arc<ChcExpr>> = fresh_vars
            .iter()
            .map(|(fv, _)| Arc::new(ChcExpr::Var(fv.clone())))
            .collect();
        let ctor_app = ChcExpr::FuncApp(ctor_name.clone(), var.sort.clone(), fresh_args);

        // Step 5: Substitute var → C(fresh_0, ..., fresh_n) in with_var literals.
        for lit in &with_var {
            let new_atom = lit.atom.substitute(&[(var.clone(), ctor_app.clone())]);
            let simplified = new_atom.simplify_constants();
            if simplified != ChcExpr::Bool(true) {
                without_var.push(Literal::new(simplified, lit.positive));
            }
        }

        // Step 6: If sort has >1 constructor, add recognizer literal.
        // For non-recursive DTs, the substitution eliminates var completely,
        // so the recognizer is on the constructor application (always true by
        // construction). However, if with_var contains equalities like
        // `var = other_dt_var`, the recognizer on `other_dt_var` is needed.
        // For now, skip — the substitution handles the common case.
        // Recognizers become essential for recursive DTs (deferred).

        (without_var, fresh_vars)
    }

    /// Expand DT constructor equalities into atomic constraints (Spacer-style).
    ///
    /// `(= x (Ctor a b))` → `(is-Ctor x) ∧ (= (sel_0 x) a) ∧ (= (sel_1 x) b)`
    ///
    /// This expansion is sound (the conjunction is equivalent) and enables
    /// per-field generalization in the lemma generalizer.
    /// Ref: Z3 `spacer_util.cpp:344-355` (`expand_literals`).
    pub(super) fn expand_dt_literals(literals: &mut Vec<Literal>) {
        let mut expanded = Vec::new();
        let mut to_remove = Vec::new();

        for (i, lit) in literals.iter().enumerate() {
            if !lit.positive {
                continue;
            }
            if let ChcExpr::Op(crate::ChcOp::Eq, args) = &lit.atom {
                if args.len() != 2 {
                    continue;
                }
                // Check if one side is a Var with DT sort, other is a FuncApp (constructor)
                let (var_side, ctor_side) = if matches!(args[0].as_ref(), ChcExpr::Var(_)) {
                    (args[0].as_ref(), args[1].as_ref())
                } else if matches!(args[1].as_ref(), ChcExpr::Var(_)) {
                    (args[1].as_ref(), args[0].as_ref())
                } else {
                    continue;
                };

                if let (ChcExpr::Var(v), ChcExpr::FuncApp(ctor_name, _, ctor_args)) =
                    (var_side, ctor_side)
                {
                    let constructors = match &v.sort {
                        ChcSort::Datatype { constructors, .. } => constructors,
                        _ => continue,
                    };

                    let ctor_meta = match constructors.iter().find(|c| &c.name == ctor_name) {
                        Some(c) => c,
                        None => continue,
                    };

                    to_remove.push(i);

                    // Add recognizer if >1 constructor
                    if constructors.len() > 1 {
                        let tester = ChcExpr::FuncApp(
                            format!("is-{ctor_name}"),
                            ChcSort::Bool,
                            vec![Arc::new(ChcExpr::Var(v.clone()))],
                        );
                        expanded.push(Literal::new(tester, true));
                    }

                    // Add per-field selector equalities
                    for (j, sel) in ctor_meta.selectors.iter().enumerate() {
                        if let Some(arg) = ctor_args.get(j) {
                            let selector_app = ChcExpr::FuncApp(
                                sel.name.clone(),
                                sel.sort.clone(),
                                vec![Arc::new(ChcExpr::Var(v.clone()))],
                            );
                            let field_eq = ChcExpr::eq(selector_app, arg.as_ref().clone());
                            expanded.push(Literal::new(field_eq, true));
                        }
                    }
                }
            }
        }

        // Remove original literals (in reverse to preserve indices)
        for i in to_remove.into_iter().rev() {
            literals.remove(i);
        }
        literals.extend(expanded);
    }

    /// Fallback: substitute DT var with model value expression.
    fn dt_fallback_substitute(
        &self,
        var: &ChcVar,
        with_var: Vec<Literal>,
        mut without_var: Vec<Literal>,
        model: &FxHashMap<String, SmtValue>,
    ) -> Vec<Literal> {
        let value = Self::model_value_expr_or_default(var, model);
        for lit in &with_var {
            let new_atom = lit.atom.substitute(&[(var.clone(), value.clone())]);
            let simplified = new_atom.simplify_constants();
            if simplified != ChcExpr::Bool(true) {
                without_var.push(Literal::new(simplified, lit.positive));
            }
        }
        without_var
    }
}
