// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::super::PdrSolver;
use crate::expr::maybe_grow_expr_stack;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;

impl PdrSolver {
    fn try_eval_int_expr_in_model(
        model: &FxHashMap<String, SmtValue>,
        expr: &ChcExpr,
    ) -> Option<i128> {
        maybe_grow_expr_stack(|| match expr {
            ChcExpr::Int(n) => Some(*n),
            ChcExpr::Var(v) => match model.get(&v.name) {
                Some(SmtValue::Int(v)) => Some(*v),
                _ => None,
            },
            ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
                let v = Self::try_eval_int_expr_in_model(model, args[0].as_ref())?;
                v.checked_neg()
            }
            ChcExpr::Op(ChcOp::Add, args) => {
                let mut acc: i128 = 0;
                for a in args {
                    let v = Self::try_eval_int_expr_in_model(model, a.as_ref())?;
                    acc = acc.checked_add(v)?;
                }
                Some(acc)
            }
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
                let a = Self::try_eval_int_expr_in_model(model, args[0].as_ref())?;
                let b = Self::try_eval_int_expr_in_model(model, args[1].as_ref())?;
                a.checked_sub(b)
            }
            ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
                let a = Self::try_eval_int_expr_in_model(model, args[0].as_ref())?;
                let b = Self::try_eval_int_expr_in_model(model, args[1].as_ref())?;
                a.checked_mul(b)
            }
            _ => None,
        })
    }

    /// Evaluate a boolean constraint algebraically given resolved variable values.
    ///
    /// Returns `Some(true)` if the constraint is satisfied, `Some(false)` if violated,
    /// or `None` if evaluation is incomplete (unresolved variables or unsupported ops).
    fn try_eval_bool_constraint(
        model: &FxHashMap<String, SmtValue>,
        expr: &ChcExpr,
    ) -> Option<bool> {
        maybe_grow_expr_stack(|| match expr {
            ChcExpr::Bool(b) => Some(*b),
            ChcExpr::Op(ChcOp::And, args) => {
                let mut any_none = false;
                for a in args {
                    match Self::try_eval_bool_constraint(model, a) {
                        Some(false) => return Some(false),
                        Some(true) => {}
                        None => any_none = true,
                    }
                }
                if any_none {
                    None
                } else {
                    Some(true)
                }
            }
            ChcExpr::Op(ChcOp::Or, args) => {
                let mut any_none = false;
                for a in args {
                    match Self::try_eval_bool_constraint(model, a) {
                        Some(true) => return Some(true),
                        Some(false) => {}
                        None => any_none = true,
                    }
                }
                if any_none {
                    None
                } else {
                    Some(false)
                }
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                Self::try_eval_bool_constraint(model, &args[0]).map(|b| !b)
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let a = Self::try_eval_int_expr_in_model(model, &args[0])?;
                let b = Self::try_eval_int_expr_in_model(model, &args[1])?;
                Some(a == b)
            }
            ChcExpr::Op(ChcOp::Lt, args) if args.len() == 2 => {
                let a = Self::try_eval_int_expr_in_model(model, &args[0])?;
                let b = Self::try_eval_int_expr_in_model(model, &args[1])?;
                Some(a < b)
            }
            ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
                let a = Self::try_eval_int_expr_in_model(model, &args[0])?;
                let b = Self::try_eval_int_expr_in_model(model, &args[1])?;
                Some(a <= b)
            }
            ChcExpr::Op(ChcOp::Gt, args) if args.len() == 2 => {
                let a = Self::try_eval_int_expr_in_model(model, &args[0])?;
                let b = Self::try_eval_int_expr_in_model(model, &args[1])?;
                Some(a > b)
            }
            ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
                let a = Self::try_eval_int_expr_in_model(model, &args[0])?;
                let b = Self::try_eval_int_expr_in_model(model, &args[1])?;
                Some(a >= b)
            }
            ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
                let a = Self::try_eval_int_expr_in_model(model, &args[0])?;
                let b = Self::try_eval_int_expr_in_model(model, &args[1])?;
                Some(a != b)
            }
            ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                let a = Self::try_eval_bool_constraint(model, &args[0])?;
                let b = Self::try_eval_bool_constraint(model, &args[1])?;
                Some(!a || b)
            }
            _ => None,
        })
    }

    /// Try to compute forward simulation result algebraically without SMT.
    ///
    /// Extracts `var = const` equalities from the substituted constraint, builds a
    /// variable→value map, then evaluates each head arg expression to a constant.
    /// For constraints with OR branches, tries each branch to find one that makes all
    /// head args evaluable.
    pub(super) fn try_algebraic_forward_eval(
        subst_constraint: &ChcExpr,
        head_var_info: &[(String, String, ChcExpr)],
        int_vars: &[ChcVar],
    ) -> Option<FxHashMap<String, i128>> {
        // Collect branches: either a single branch (no OR) or multiple branches
        let branches = Self::collect_and_branches(subst_constraint);

        for branch_equalities in &branches {
            // Build a var→value map from the equalities, with fixed-point resolution
            let mut var_values: FxHashMap<String, i128> = FxHashMap::default();

            // First pass: collect direct constant equalities
            for eq in branch_equalities {
                if let ChcExpr::Op(ChcOp::Eq, args) = eq {
                    if args.len() == 2 {
                        match (args[0].as_ref(), args[1].as_ref()) {
                            (ChcExpr::Var(v), ChcExpr::Int(c))
                            | (ChcExpr::Int(c), ChcExpr::Var(v)) => {
                                var_values.insert(v.name.clone(), *c);
                            }
                            _ => {}
                        }
                    }
                }
            }

            // Fixed-point: resolve equalities transitively (e.g., F = D + E, D=1, E=-1 → F=0)
            for _round in 0..5 {
                let mut progress = false;
                for eq in branch_equalities {
                    if let ChcExpr::Op(ChcOp::Eq, args) = eq {
                        if args.len() == 2 {
                            // Try var = expr direction
                            if let ChcExpr::Var(v) = args[0].as_ref() {
                                if !var_values.contains_key(&v.name) {
                                    let model: FxHashMap<String, SmtValue> = var_values
                                        .iter()
                                        .map(|(k, &v)| (k.clone(), SmtValue::Int(v)))
                                        .collect();
                                    if let Some(val) =
                                        Self::try_eval_int_expr_in_model(&model, args[1].as_ref())
                                    {
                                        var_values.insert(v.name.clone(), val);
                                        progress = true;
                                    }
                                }
                            }
                            // Try expr = var direction
                            if let ChcExpr::Var(v) = args[1].as_ref() {
                                if !var_values.contains_key(&v.name) {
                                    let model: FxHashMap<String, SmtValue> = var_values
                                        .iter()
                                        .map(|(k, &v)| (k.clone(), SmtValue::Int(v)))
                                        .collect();
                                    if let Some(val) =
                                        Self::try_eval_int_expr_in_model(&model, args[0].as_ref())
                                    {
                                        var_values.insert(v.name.clone(), val);
                                        progress = true;
                                    }
                                }
                            }
                        }
                    }
                }
                if !progress {
                    break;
                }
            }

            // Try to evaluate all head args using the resolved values
            let model: FxHashMap<String, SmtValue> = var_values
                .iter()
                .map(|(k, &v)| (k.clone(), SmtValue::Int(v)))
                .collect();

            let mut result: FxHashMap<String, i128> = FxHashMap::default();
            let mut all_resolved = true;
            for (canonical_name, _, head_arg_expr) in head_var_info {
                if let Some(val) = Self::try_eval_int_expr_in_model(&model, head_arg_expr) {
                    result.insert(canonical_name.clone(), val);
                } else {
                    all_resolved = false;
                    break;
                }
            }

            if all_resolved && result.len() == int_vars.len() {
                // Verify the constraint is actually satisfiable under the resolved values.
                // Without this check, unsatisfiable branches (e.g., NOT(x < 0) with x=-1)
                // would produce phantom next-states. (#2921)
                match Self::try_eval_bool_constraint(&model, subst_constraint) {
                    Some(false) => continue, // constraint violated, try next branch
                    Some(true) => return Some(result),
                    None => return Some(result), // can't determine, optimistically return
                }
            }
        }

        None
    }

    /// Collect equality conjuncts from a constraint, handling AND/OR structure.
    ///
    /// For `(and eq1 eq2 ... (or branch1 branch2))`, returns one set of equalities
    /// per OR branch, each including the top-level equalities.
    /// For `(and eq1 eq2)` without OR, returns a single set.
    fn collect_and_branches(expr: &ChcExpr) -> Vec<Vec<&ChcExpr>> {
        let mut top_level_eqs: Vec<&ChcExpr> = Vec::new();
        let mut or_branches: Vec<Vec<&ChcExpr>> = Vec::new();

        fn walk_and<'a>(
            expr: &'a ChcExpr,
            top: &mut Vec<&'a ChcExpr>,
            branches: &mut Vec<Vec<&'a ChcExpr>>,
        ) {
            match expr {
                ChcExpr::Op(ChcOp::And, args) => {
                    for a in args {
                        walk_and(a.as_ref(), top, branches);
                    }
                }
                ChcExpr::Op(ChcOp::Or, args) => {
                    // Each OR arg is a branch. Recursively collect equalities within each.
                    for a in args {
                        let mut branch_eqs: Vec<&ChcExpr> = Vec::new();
                        fn collect_eqs_from_and<'b>(e: &'b ChcExpr, out: &mut Vec<&'b ChcExpr>) {
                            match e {
                                ChcExpr::Op(ChcOp::And, args) => {
                                    for a in args {
                                        collect_eqs_from_and(a.as_ref(), out);
                                    }
                                }
                                ChcExpr::Op(ChcOp::Eq, _) => out.push(e),
                                _ => {}
                            }
                        }
                        collect_eqs_from_and(a.as_ref(), &mut branch_eqs);
                        branches.push(branch_eqs);
                    }
                }
                ChcExpr::Op(ChcOp::Eq, _) => top.push(expr),
                _ => {}
            }
        }

        walk_and(expr, &mut top_level_eqs, &mut or_branches);

        if or_branches.is_empty() {
            // No OR: single branch with all top-level equalities
            vec![top_level_eqs]
        } else {
            // Combine top-level equalities with each OR branch
            or_branches
                .into_iter()
                .map(|mut branch| {
                    branch.extend(top_level_eqs.iter().copied());
                    branch
                })
                .collect()
        }
    }

    /// Static version of try_eval_head_arg_in_model that doesn't require &self.
    pub(super) fn try_eval_head_arg_in_model_static(
        model: &FxHashMap<String, SmtValue>,
        head_arg: &ChcExpr,
    ) -> Option<SmtValue> {
        let v = Self::try_eval_int_expr_in_model(model, head_arg)?;
        Some(SmtValue::Int(v))
    }

    /// Augment an SMT model by resolving equality constraints from the query.
    ///
    /// When the SMT solver eliminates variables via constant propagation, those variables
    /// are missing from the model. This function walks equality conjuncts (e.g., `D = 1`)
    /// and adds resolved values to the model. Uses fixed-point iteration to handle
    /// transitive definitions (e.g., `F = C + D + E` where C, D, E resolve first).
    ///
    /// Returns true if any new variables were added to the model.
    pub(super) fn augment_model_from_equalities(
        model: &mut FxHashMap<String, SmtValue>,
        conjuncts: &[ChcExpr],
    ) -> bool {
        // Collect equalities of the form (= var expr) or (= expr var)
        let equalities: Vec<(&ChcVar, &ChcExpr)> = conjuncts
            .iter()
            .filter_map(|conj| {
                if let ChcExpr::Op(ChcOp::Eq, args) = conj {
                    if args.len() == 2 {
                        match (args[0].as_ref(), args[1].as_ref()) {
                            (ChcExpr::Var(v), rhs) => Some((v, rhs)),
                            (lhs, ChcExpr::Var(v)) => Some((v, lhs)),
                            _ => None,
                        }
                    } else {
                        None
                    }
                } else {
                    None
                }
            })
            .collect();

        if equalities.is_empty() {
            return false;
        }

        // Also collect equalities from within AND conjuncts (handles nested structures
        // like `(and (= D 1) (= E -1))` that appear inside OR branches).
        // We walk shallow AND nesting to find all equalities.
        let mut nested_equalities: Vec<(String, ChcExpr)> = Vec::new();
        fn collect_nested_eqs(expr: &ChcExpr, out: &mut Vec<(String, ChcExpr)>) {
            match expr {
                ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                    match (args[0].as_ref(), args[1].as_ref()) {
                        (ChcExpr::Var(v), rhs) => {
                            out.push((v.name.clone(), rhs.clone()));
                        }
                        (lhs, ChcExpr::Var(v)) => {
                            out.push((v.name.clone(), lhs.clone()));
                        }
                        _ => {}
                    }
                }
                ChcExpr::Op(ChcOp::And, args) => {
                    for a in args {
                        collect_nested_eqs(a.as_ref(), out);
                    }
                }
                _ => {}
            }
        }
        for conj in conjuncts {
            collect_nested_eqs(conj, &mut nested_equalities);
        }

        // Fixed-point iteration: resolve equalities until no new values are added.
        // Limit iterations to prevent pathological cases.
        let initial_size = model.len();
        for _round in 0..10 {
            let mut progress = false;

            // Try top-level equalities
            for &(var, rhs) in &equalities {
                if model.contains_key(&var.name) {
                    continue;
                }
                if let Some(v) = Self::try_eval_int_expr_in_model(model, rhs) {
                    model.insert(var.name.clone(), SmtValue::Int(v));
                    progress = true;
                }
            }

            // Try nested equalities
            for (var_name, rhs) in &nested_equalities {
                if model.contains_key(var_name) {
                    continue;
                }
                if let Some(v) = Self::try_eval_int_expr_in_model(model, rhs) {
                    model.insert(var_name.clone(), SmtValue::Int(v));
                    progress = true;
                }
            }

            if !progress {
                break;
            }
        }

        model.len() > initial_size
    }

    pub(super) fn extract_head_int_assignment_from_model(
        model: &FxHashMap<String, SmtValue>,
        canonical_vars: &[ChcVar],
        head_args: &[ChcExpr],
    ) -> Option<FxHashMap<String, i128>> {
        if canonical_vars.len() != head_args.len() {
            return None;
        }

        let mut values: FxHashMap<String, i128> = FxHashMap::default();
        for (i, canon) in canonical_vars.iter().enumerate() {
            if !matches!(canon.sort, ChcSort::Int) {
                continue;
            }
            if let Some(SmtValue::Int(v)) = model.get(&canon.name) {
                values.insert(canon.name.clone(), *v);
                continue;
            }

            // Fallback: evaluate the head argument in the returned model. This handles cases where
            // constant propagation eliminates the canonical head variable from the SMT term store,
            // but the query still includes `canon_i = head_arg_i` and body args were fixed to a
            // concrete sample.
            let v = Self::try_eval_int_expr_in_model(model, &head_args[i])?;
            values.insert(canon.name.clone(), v);
        }

        let needed = canonical_vars
            .iter()
            .filter(|v| matches!(v.sort, ChcSort::Int))
            .count();
        if values.len() == needed {
            Some(values)
        } else {
            None
        }
    }

    /// Try to evaluate a head argument in an SMT model.
    ///
    /// This is used when the SMT solver returns a model but the "_next" variable wasn't assigned
    /// directly (e.g., because it was constrained by an equality to another intermediate variable).
    pub(super) fn try_eval_head_arg_in_model(
        &self,
        model: &FxHashMap<String, SmtValue>,
        head_arg: &ChcExpr,
    ) -> Option<SmtValue> {
        let v = Self::try_eval_int_expr_in_model(model, head_arg)?;
        Some(SmtValue::Int(v))
    }
}
