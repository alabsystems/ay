// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Modular arithmetic hint providers (ModResidue, ModSum).

use super::recurrence_conserved::RecurrenceConservedEqualityProvider;
use super::*;

pub(crate) struct ModResidueHintProvider;

impl ModResidueHintProvider {
    const SOURCE: &'static str = "mod-residue-v1";
    const PREDECESSOR_SOURCE: &'static str = "mod-residue-pred-v1";
    const PRIORITY: u16 = 250;
    const PREDECESSOR_PRIORITY: u16 = 255;
    const MAX_ENUM_STARTUP: i128 = 4;
    const MAX_ENUM_STUCK: i128 = 8;
    const MAX_HINTS_PER_PRED: usize = 64;

    pub(super) fn extract_mod_terms(expr: &ChcExpr) -> Vec<(ChcExpr, i128)> {
        let mut terms = Vec::new();
        Self::extract_mod_terms_recursive(expr, &mut terms);
        terms
    }

    pub(super) fn extract_divisibility_terms(expr: &ChcExpr) -> Vec<(ChcExpr, i128)> {
        let mut terms = Vec::new();
        Self::extract_divisibility_terms_recursive(expr, &mut terms);
        terms
    }

    fn extract_mod_terms_recursive(expr: &ChcExpr, out: &mut Vec<(ChcExpr, i128)>) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Mod, args) if args.len() == 2 => {
                if let ChcExpr::Int(k) = args[1].as_ref() {
                    if *k > 1 && !Self::contains_next_var(&args[0]) {
                        out.push(((*args[0]).clone(), *k));
                        Self::extract_vars_from_dividend(&args[0], *k, out);
                    }
                }
                Self::extract_mod_terms_recursive(&args[0], out);
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    Self::extract_mod_terms_recursive(arg, out);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    Self::extract_mod_terms_recursive(arg, out);
                }
            }
            _ => {}
        });
    }

    fn extract_divisibility_terms_recursive(expr: &ChcExpr, out: &mut Vec<(ChcExpr, i128)>) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::Mul, args) => {
                if let Some((coeff, scaled_expr)) = Self::const_coeff_times_expr(args) {
                    Self::extract_divisibility_from_scaled_expr(&scaled_expr, coeff, out);
                }
                for arg in args {
                    Self::extract_divisibility_terms_recursive(arg, out);
                }
            }
            ChcExpr::Op(_, args) => {
                for arg in args {
                    Self::extract_divisibility_terms_recursive(arg, out);
                }
            }
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                for arg in args {
                    Self::extract_divisibility_terms_recursive(arg, out);
                }
            }
            _ => {}
        });
    }

    fn const_coeff_times_expr(args: &[Arc<ChcExpr>]) -> Option<(i128, ChcExpr)> {
        let mut coeff = 1i128;
        let mut scaled_expr: Option<ChcExpr> = None;

        for arg in args {
            match arg.as_ref() {
                ChcExpr::Int(k) => {
                    coeff = coeff.checked_mul(*k)?;
                }
                expr => {
                    if scaled_expr.is_some() {
                        return None;
                    }
                    scaled_expr = Some(expr.clone());
                }
            }
        }

        let scaled_expr = scaled_expr?;
        let coeff = coeff.abs();
        if coeff <= 1 || Self::contains_next_var(&scaled_expr) {
            return None;
        }

        Some((coeff, scaled_expr))
    }

    fn extract_divisibility_from_scaled_expr(
        expr: &ChcExpr,
        modulus: i128,
        out: &mut Vec<(ChcExpr, i128)>,
    ) {
        match expr {
            ChcExpr::Var(v) if !v.name.ends_with("_next") => {
                out.push((ChcExpr::var(v.clone()), modulus));
            }
            _ => Self::extract_vars_from_dividend(expr, modulus, out),
        }
    }

    pub(super) fn extract_vars_from_dividend(
        expr: &ChcExpr,
        modulus: i128,
        out: &mut Vec<(ChcExpr, i128)>,
    ) {
        if let ChcExpr::Op(ChcOp::Add, args) = expr {
            for arg in args {
                if let ChcExpr::Var(v) = arg.as_ref() {
                    if !v.name.ends_with("_next") {
                        out.push((ChcExpr::var(v.clone()), modulus));
                    }
                }
            }
        }
    }

    pub(super) fn contains_next_var(expr: &ChcExpr) -> bool {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Var(v) => v.name.ends_with("_next"),
            ChcExpr::Op(_, args) => args.iter().any(|a| Self::contains_next_var(a)),
            ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
                args.iter().any(|a| Self::contains_next_var(a))
            }
            _ => false,
        })
    }

    fn divisibility_moduli(divisor: i128, max_enum: i128) -> Vec<i128> {
        let mut moduli = Vec::new();
        for modulus in 2..=divisor.min(max_enum) {
            if divisor % modulus == 0 {
                moduli.push(modulus);
            }
        }
        moduli
    }

    fn canonicalize_clause_from_body(
        clause: &crate::HornClause,
        canonical_body_vars: &[ChcVar],
    ) -> Option<(ChcExpr, Vec<ChcExpr>)> {
        if clause.body.predicates.len() != 1 {
            return None;
        }
        let (_, body_args) = &clause.body.predicates[0];
        let crate::ClauseHead::Predicate(_, head_args) = &clause.head else {
            return None;
        };
        if body_args.len() != canonical_body_vars.len() {
            return None;
        }

        let mut body_subst = Vec::new();
        for (i, arg) in body_args.iter().enumerate() {
            match arg {
                ChcExpr::Var(v) => {
                    body_subst.push((v.clone(), ChcExpr::var(canonical_body_vars[i].clone())));
                }
                expr => {
                    for v in expr.vars() {
                        if !body_subst.iter().any(|(sv, _)| sv.name == v.name) {
                            body_subst.push((v.clone(), ChcExpr::var(v.clone())));
                        }
                    }
                }
            }
        }

        let mut constraint = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true));
        for (old_var, new_expr) in &body_subst {
            constraint = constraint.substitute(&[(old_var.clone(), new_expr.clone())]);
        }

        let canonical_var_names: ay_core::kani_compat::DetHashSet<&str> = canonical_body_vars
            .iter()
            .map(|v| v.name.as_str())
            .collect();
        let aux_var_defs = RecurrenceConservedEqualityProvider::extract_aux_var_definitions(
            &constraint,
            &canonical_var_names,
            &ay_core::kani_compat::DetHashSet::default(),
        );
        let inlined_constraint =
            RecurrenceConservedEqualityProvider::inline_aux_vars(&constraint, &aux_var_defs)
                .simplify_constants();
        let mut inlined_head_args = Vec::new();
        for head_arg in head_args {
            let mut arg = head_arg.clone();
            for (old_var, new_expr) in &body_subst {
                arg = arg.substitute(&[(old_var.clone(), new_expr.clone())]);
            }
            arg = RecurrenceConservedEqualityProvider::inline_aux_vars(&arg, &aux_var_defs)
                .simplify_constants();
            inlined_head_args.push(arg);
        }

        Some((inlined_constraint, inlined_head_args))
    }

    fn canonicalize_self_loop(
        clause: &crate::HornClause,
        canonical_vars: &[ChcVar],
    ) -> Option<(ChcExpr, Vec<ChcExpr>)> {
        RecurrenceConservedEqualityProvider::is_self_loop(clause)?;
        Self::canonicalize_clause_from_body(clause, canonical_vars)
    }

    fn referenced_positions(
        formula: &ChcExpr,
        canonical_vars: &[ChcVar],
    ) -> ay_core::kani_compat::DetHashSet<usize> {
        let formula_var_names: ay_core::kani_compat::DetHashSet<String> =
            formula.vars().into_iter().map(|v| v.name).collect();
        canonical_vars
            .iter()
            .enumerate()
            .filter_map(|(idx, v)| formula_var_names.contains(&v.name).then_some(idx))
            .collect()
    }

    fn propagate_hints_to_predecessors(
        req: &HintRequest<'_>,
        seeds: &[LemmaHint],
        priority: u16,
        source: &'static str,
        max_hints_per_pred: usize,
    ) -> Vec<LemmaHint> {
        use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

        if req.problem.predicates().len() < 2 || seeds.is_empty() {
            return Vec::new();
        }

        let mut predecessors: FxHashMap<PredicateId, Vec<(PredicateId, Vec<ChcExpr>)>> =
            FxHashMap::default();
        for clause in req.problem.clauses() {
            let crate::ClauseHead::Predicate(head_pred, _) = &clause.head else {
                continue;
            };
            if clause.body.predicates.len() != 1 {
                continue;
            }
            let (body_pred, _) = &clause.body.predicates[0];
            if body_pred == head_pred {
                continue;
            }
            let Some(body_canonical_vars) = req.canonical_vars(*body_pred) else {
                continue;
            };
            let Some((_, canonicalized_head_args)) =
                Self::canonicalize_clause_from_body(clause, body_canonical_vars)
            else {
                continue;
            };
            if canonicalized_head_args.is_empty() {
                continue;
            }
            predecessors
                .entry(*head_pred)
                .or_default()
                .push((*body_pred, canonicalized_head_args));
        }

        if predecessors.is_empty() {
            return Vec::new();
        }

        let mut worklist: Vec<(PredicateId, ChcExpr)> = seeds
            .iter()
            .map(|hint| (hint.predicate, hint.formula.clone()))
            .collect();
        let mut visited: FxHashSet<(PredicateId, ChcExpr)> = worklist.iter().cloned().collect();
        let mut propagated_per_pred: FxHashMap<PredicateId, usize> = FxHashMap::default();
        let mut propagated = Vec::new();

        while let Some((pred_id, formula)) = worklist.pop() {
            let Some(head_canonical_vars) = req.canonical_vars(pred_id) else {
                continue;
            };
            let Some(preds) = predecessors.get(&pred_id) else {
                continue;
            };

            let mut used_positions: Vec<usize> =
                Self::referenced_positions(&formula, head_canonical_vars)
                    .into_iter()
                    .collect();
            used_positions.sort_unstable();
            if used_positions.is_empty() {
                continue;
            }

            for (body_pred, mapping) in preds {
                if propagated_per_pred.get(body_pred).copied().unwrap_or(0) >= max_hints_per_pred {
                    continue;
                }
                let Some(body_canonical_vars) = req.canonical_vars(*body_pred) else {
                    continue;
                };
                if mapping.len() != head_canonical_vars.len() {
                    continue;
                }
                let body_var_names: FxHashSet<&str> = body_canonical_vars
                    .iter()
                    .map(|v| v.name.as_str())
                    .collect();

                let mut substitutions = Vec::with_capacity(used_positions.len());
                let mut applicable = true;
                for &head_idx in &used_positions {
                    let Some(head_var) = head_canonical_vars.get(head_idx) else {
                        applicable = false;
                        break;
                    };
                    let Some(body_expr) = mapping.get(head_idx) else {
                        applicable = false;
                        break;
                    };
                    if body_expr
                        .vars()
                        .into_iter()
                        .any(|v| !body_var_names.contains(v.name.as_str()))
                    {
                        applicable = false;
                        break;
                    }
                    substitutions.push((head_var.clone(), body_expr.clone()));
                }
                if !applicable {
                    continue;
                }

                let propagated_formula = formula.substitute(&substitutions).simplify_constants();
                if !visited.insert((*body_pred, propagated_formula.clone())) {
                    continue;
                }

                propagated.push(LemmaHint::new(
                    *body_pred,
                    propagated_formula.clone(),
                    priority,
                    source,
                ));
                *propagated_per_pred.entry(*body_pred).or_insert(0) += 1;
                worklist.push((*body_pred, propagated_formula));
            }
        }

        propagated
    }
}

impl LemmaHintProvider for ModResidueHintProvider {
    fn collect(&self, req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
        let max_enum = match req.stage {
            HintStage::Startup => Self::MAX_ENUM_STARTUP,
            HintStage::Stuck => Self::MAX_ENUM_STUCK,
        };
        let mut hints = Vec::new();
        for clause in req.problem.clauses() {
            let pred_id = match RecurrenceConservedEqualityProvider::is_self_loop(clause) {
                Some((pid, _, _)) => pid,
                None => continue,
            };
            let canonical_vars = match req.canonical_vars(pred_id) {
                Some(vars) => vars,
                None => continue,
            };
            let (constraint, head_args) = match Self::canonicalize_self_loop(clause, canonical_vars)
            {
                Some(c) => c,
                None => continue,
            };
            let mut divisibility_terms = Self::extract_divisibility_terms(&constraint);
            let mut mod_terms = Self::extract_mod_terms(&constraint);
            for head_arg in &head_args {
                divisibility_terms.extend(Self::extract_divisibility_terms(head_arg));
                mod_terms.extend(Self::extract_mod_terms(head_arg));
            }
            divisibility_terms.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
            divisibility_terms.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1);
            mod_terms.sort_by(|a, b| a.0.cmp(&b.0).then_with(|| a.1.cmp(&b.1)));
            mod_terms.dedup_by(|a, b| a.0 == b.0 && a.1 == b.1);
            let mut hint_count = 0;
            let mut seen_formulas: ay_core::kani_compat::DetHashSet<ChcExpr> =
                ay_core::kani_compat::DetHashSet::default();
            for (dividend, divisor) in divisibility_terms {
                for modulus in Self::divisibility_moduli(divisor, max_enum) {
                    if hint_count >= Self::MAX_HINTS_PER_PRED {
                        break;
                    }
                    let hint_formula = ChcExpr::eq(
                        ChcExpr::mod_op(dividend.clone(), ChcExpr::int(modulus)),
                        ChcExpr::int(0),
                    );
                    if seen_formulas.insert(hint_formula.clone()) {
                        hints.push(LemmaHint::new(
                            pred_id,
                            hint_formula,
                            Self::PRIORITY,
                            Self::SOURCE,
                        ));
                        hint_count += 1;
                    }
                }
            }
            for (dividend, modulus) in mod_terms {
                if modulus > max_enum {
                    continue;
                }
                for r in 0..modulus {
                    if hint_count >= Self::MAX_HINTS_PER_PRED {
                        break;
                    }
                    let mod_expr = ChcExpr::mod_op(dividend.clone(), ChcExpr::int(modulus));
                    let hint_formula = ChcExpr::eq(mod_expr, ChcExpr::int(r));
                    if seen_formulas.insert(hint_formula.clone()) {
                        hints.push(LemmaHint::new(
                            pred_id,
                            hint_formula,
                            Self::PRIORITY,
                            Self::SOURCE,
                        ));
                        hint_count += 1;
                    }
                }
            }
        }
        let propagated = Self::propagate_hints_to_predecessors(
            req,
            &hints,
            Self::PREDECESSOR_PRIORITY,
            Self::PREDECESSOR_SOURCE,
            Self::MAX_HINTS_PER_PRED,
        );
        out.extend(hints);
        out.extend(propagated);
    }
}

pub(crate) struct ModSumHintProvider;

impl ModSumHintProvider {
    const SOURCE: &'static str = "mod-sum-v1";
    const PRIORITY: u16 = 260;
    const MAX_SUM_SIZE: usize = 6;
    const MAX_HINTS_PER_PRED: usize = 32;

    pub(super) fn problem_contains_mod_div(problem: &ChcProblem) -> bool {
        for clause in problem.clauses() {
            if let Some(constraint) = &clause.body.constraint {
                if Self::expr_contains_mod_div(constraint) {
                    return true;
                }
            }
            for (_, args) in &clause.body.predicates {
                for arg in args {
                    if Self::expr_contains_mod_div(arg) {
                        return true;
                    }
                }
            }
            if let crate::ClauseHead::Predicate(_, args) = &clause.head {
                for arg in args {
                    if Self::expr_contains_mod_div(arg) {
                        return true;
                    }
                }
            }
        }
        false
    }

    fn expr_contains_mod_div(expr: &ChcExpr) -> bool {
        expr.contains_mod_or_div()
    }
}

impl LemmaHintProvider for ModSumHintProvider {
    fn collect(&self, req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
        if req.stage != HintStage::Startup {
            return;
        }
        if !Self::problem_contains_mod_div(req.problem) {
            return;
        }
        for pred_info in req.problem.predicates() {
            let pred_id = pred_info.id;
            let canonical_vars = match req.canonical_vars(pred_id) {
                Some(vars) => vars,
                None => continue,
            };
            let int_vars: Vec<&ChcVar> = canonical_vars
                .iter()
                .filter(|v| matches!(v.sort, crate::ChcSort::Int))
                .collect();
            if int_vars.len() < 2 {
                continue;
            }
            let mut hint_count = 0;
            let max_size = int_vars.len().min(Self::MAX_SUM_SIZE);
            for sum_size in 2..=max_size {
                let mut indices: Vec<usize> = (0..sum_size).collect();
                let mut combo_count = 0;
                loop {
                    if hint_count >= Self::MAX_HINTS_PER_PRED || combo_count >= 8 {
                        break;
                    }
                    let sum_expr = indices
                        .iter()
                        .map(|&i| ChcExpr::var(int_vars[i].clone()))
                        .reduce(ChcExpr::add)
                        .unwrap_or_else(|| ChcExpr::int(0));
                    for r in 0..2i64 {
                        let mod_expr = ChcExpr::mod_op(sum_expr.clone(), ChcExpr::int(2));
                        let hint_formula = ChcExpr::eq(mod_expr, ChcExpr::int(r));
                        out.push(LemmaHint::new(
                            pred_id,
                            hint_formula,
                            Self::PRIORITY,
                            Self::SOURCE,
                        ));
                        hint_count += 1;
                    }
                    combo_count += 1;
                    let n = int_vars.len();
                    let mut i = sum_size;
                    while i > 0 {
                        i -= 1;
                        if indices[i] < n - sum_size + i {
                            indices[i] += 1;
                            for j in (i + 1)..sum_size {
                                indices[j] = indices[j - 1] + 1;
                            }
                            break;
                        }
                    }
                    if i == 0 && indices[0] > n - sum_size {
                        break;
                    }
                }
            }
            if int_vars.len() > 2 && hint_count < Self::MAX_HINTS_PER_PRED {
                let full_sum = int_vars
                    .iter()
                    .map(|v| ChcExpr::var((*v).clone()))
                    .reduce(ChcExpr::add)
                    .unwrap_or_else(|| ChcExpr::int(0));
                for r in 0..2i64 {
                    let mod_expr = ChcExpr::mod_op(full_sum.clone(), ChcExpr::int(2));
                    let hint_formula = ChcExpr::eq(mod_expr, ChcExpr::int(r));
                    out.push(LemmaHint::new(
                        pred_id,
                        hint_formula,
                        Self::PRIORITY,
                        Self::SOURCE,
                    ));
                }
            }
        }
    }
}

pub(super) static MOD_RESIDUE_PROVIDER: ModResidueHintProvider = ModResidueHintProvider;
pub(super) static MOD_SUM_PROVIDER: ModSumHintProvider = ModSumHintProvider;
