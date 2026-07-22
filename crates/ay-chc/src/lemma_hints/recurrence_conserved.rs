// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Recurrence conserved equality hint provider: discovers preserved linear equalities.

use super::*;

/// Provider that uses recurrence analysis to find conserved linear equalities.
///
/// For self-loop transitions (P(v) /\ constraint => P(v')), analyzes the transition
/// to find linear combinations of variables that are preserved, e.g., `v0 + v1 = c`.
pub(crate) struct RecurrenceConservedEqualityProvider;

impl RecurrenceConservedEqualityProvider {
    const SOURCE: &'static str = "recurrence-conserved-eq-v1";
    const PRIORITY: u16 = 200;

    pub(crate) fn is_self_loop(
        clause: &crate::HornClause,
    ) -> Option<(PredicateId, &[ChcExpr], &[ChcExpr])> {
        if clause.body.predicates.len() != 1 {
            return None;
        }
        let (body_pred, body_args) = &clause.body.predicates[0];
        match &clause.head {
            crate::ClauseHead::Predicate(head_pred, head_args) if body_pred == head_pred => {
                Some((*body_pred, body_args.as_slice(), head_args.as_slice()))
            }
            _ => None,
        }
    }

    pub(super) fn extract_transition(
        clause: &crate::HornClause,
        canonical_vars: &[ChcVar],
    ) -> Option<(ChcExpr, Vec<String>)> {
        let (_, body_args, head_args) = Self::is_self_loop(clause)?;
        if body_args.len() != canonical_vars.len() || head_args.len() != canonical_vars.len() {
            return None;
        }
        let state_var_names: Vec<String> = canonical_vars.iter().map(|v| v.name.clone()).collect();
        let next_var_names: ay_core::kani_compat::DetHashSet<String> = canonical_vars
            .iter()
            .map(|v| format!("{}_next", v.name))
            .collect();
        let mut body_subst = Vec::new();
        for (i, arg) in body_args.iter().enumerate() {
            match arg {
                ChcExpr::Var(v) => {
                    body_subst.push((v.clone(), ChcExpr::var(canonical_vars[i].clone())));
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
        let canonical_var_names: ay_core::kani_compat::DetHashSet<&str> =
            canonical_vars.iter().map(|v| v.name.as_str()).collect();
        let aux_var_defs =
            Self::extract_aux_var_definitions(&constraint, &canonical_var_names, &next_var_names);
        let mut next_constraint = ChcExpr::Bool(true);
        for (i, head_arg) in head_args.iter().enumerate() {
            let next_var = ChcVar::new(
                format!("{}_next", canonical_vars[i].name),
                canonical_vars[i].sort.clone(),
            );
            let mut substituted_head_arg = head_arg.clone();
            for (old_var, new_expr) in &body_subst {
                substituted_head_arg =
                    substituted_head_arg.substitute(&[(old_var.clone(), new_expr.clone())]);
            }
            substituted_head_arg = Self::inline_aux_vars(&substituted_head_arg, &aux_var_defs);
            substituted_head_arg = substituted_head_arg.simplify_constants();
            let eq = ChcExpr::eq(ChcExpr::var(next_var), substituted_head_arg);
            next_constraint = ChcExpr::and(next_constraint, eq);
        }
        Some((next_constraint, state_var_names))
    }

    pub(crate) fn extract_aux_var_definitions(
        constraint: &ChcExpr,
        exclude_vars: &ay_core::kani_compat::DetHashSet<&str>,
        next_var_names: &ay_core::kani_compat::DetHashSet<String>,
    ) -> ay_core::kani_compat::DetHashMap<ChcVar, ChcExpr> {
        use ay_core::kani_compat::DetHashMap as FxHashMap;
        let mut defs: FxHashMap<ChcVar, ChcExpr> = FxHashMap::default();
        Self::collect_aux_defs_recursive(constraint, &mut defs, exclude_vars, next_var_names);
        Self::remove_cyclic_definitions(&mut defs);
        defs
    }

    fn remove_cyclic_definitions(defs: &mut ay_core::kani_compat::DetHashMap<ChcVar, ChcExpr>) {
        use ay_core::kani_compat::DetHashSet as FxHashSet;
        let var_names: Vec<String> = defs.keys().map(|v| v.name.clone()).collect();
        let name_to_idx: ay_core::kani_compat::DetHashMap<&str, usize> = var_names
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), i))
            .collect();
        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); var_names.len()];
        for (var, def) in defs.iter() {
            if let Some(&from_idx) = name_to_idx.get(var.name.as_str()) {
                for dep_var in def.vars() {
                    if let Some(&to_idx) = name_to_idx.get(dep_var.name.as_str()) {
                        adj[from_idx].push(to_idx);
                    }
                }
            }
        }
        let mut state = vec![0u8; var_names.len()];
        let mut in_cycle: FxHashSet<usize> = FxHashSet::default();

        fn dfs(
            node: usize,
            adj: &[Vec<usize>],
            state: &mut [u8],
            path: &mut Vec<usize>,
            in_cycle: &mut FxHashSet<usize>,
        ) {
            state[node] = 1;
            path.push(node);
            for &next in &adj[node] {
                if state[next] == 1 {
                    let cycle_start = path
                        .iter()
                        .position(|&n| n == next)
                        .expect("DFS back-edge target must be in current path");
                    for &cycle_node in &path[cycle_start..] {
                        in_cycle.insert(cycle_node);
                    }
                } else if state[next] == 0 {
                    dfs(next, adj, state, path, in_cycle);
                }
            }
            path.pop();
            state[node] = 2;
        }

        for start in 0..var_names.len() {
            if state[start] == 0 {
                let mut path = Vec::new();
                dfs(start, &adj, &mut state, &mut path, &mut in_cycle);
            }
        }
        let cyclic_names: FxHashSet<&str> = in_cycle
            .iter()
            .map(|&idx| var_names[idx].as_str())
            .collect();
        defs.retain(|var, _| !cyclic_names.contains(var.name.as_str()));
    }

    fn collect_aux_defs_recursive(
        expr: &ChcExpr,
        defs: &mut ay_core::kani_compat::DetHashMap<ChcVar, ChcExpr>,
        exclude_vars: &ay_core::kani_compat::DetHashSet<&str>,
        next_var_names: &ay_core::kani_compat::DetHashSet<String>,
    ) {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    Self::collect_aux_defs_recursive(arg, defs, exclude_vars, next_var_names);
                }
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
                let mut captured = false;
                if let ChcExpr::Var(v) = args[0].as_ref() {
                    if !next_var_names.contains(v.name.as_str())
                        && !exclude_vars.contains(v.name.as_str())
                    {
                        let rhs = args[1].as_ref();
                        if !rhs.vars().iter().any(|rv| rv.name == v.name) {
                            defs.insert(v.clone(), rhs.clone());
                            captured = true;
                        }
                    }
                }
                if !captured {
                    if let ChcExpr::Var(v) = args[1].as_ref() {
                        if !next_var_names.contains(v.name.as_str())
                            && !exclude_vars.contains(v.name.as_str())
                            && !defs.contains_key(v)
                        {
                            let lhs = args[0].as_ref();
                            if !lhs.vars().iter().any(|rv| rv.name == v.name) {
                                defs.insert(v.clone(), lhs.clone());
                            }
                        }
                    }
                }
            }
            _ => {}
        });
    }

    pub(crate) fn inline_aux_vars(
        expr: &ChcExpr,
        defs: &ay_core::kani_compat::DetHashMap<ChcVar, ChcExpr>,
    ) -> ChcExpr {
        const MAX_ITERATIONS: usize = 10;
        let mut current = expr.clone();
        for _ in 0..MAX_ITERATIONS {
            let mut changed = false;
            for (var, def) in defs {
                let new_expr = current.substitute(&[(var.clone(), def.clone())]);
                if new_expr != current {
                    changed = true;
                    current = new_expr;
                }
            }
            if !changed {
                break;
            }
        }
        current
    }

    fn to_polynomial_coeffs(
        cf: &crate::recurrence::ClosedForm,
    ) -> Option<Vec<ay_core::kani_compat::DetHashMap<String, num_rational::Rational64>>> {
        use crate::recurrence::ClosedForm;
        use ay_core::kani_compat::DetHashMap as FxHashMap;
        use num_rational::Rational64;
        match cf {
            ClosedForm::ConstantDelta { delta, .. } => {
                let mut coeff_1 = FxHashMap::default();
                coeff_1.insert(String::new(), Rational64::from_integer(*delta));
                Some(vec![coeff_1])
            }
            ClosedForm::Polynomial { coeffs, .. } => {
                if coeffs.len() <= 1 {
                    Some(vec![])
                } else {
                    Some(coeffs[1..].to_vec())
                }
            }
        }
    }

    fn coeffs_sum_to_zero(
        coeffs_a: &[ay_core::kani_compat::DetHashMap<String, num_rational::Rational64>],
        coeffs_b: &[ay_core::kani_compat::DetHashMap<String, num_rational::Rational64>],
        negate_b: bool,
    ) -> bool {
        use num_rational::Rational64;
        let max_len = coeffs_a.len().max(coeffs_b.len());
        for i in 0..max_len {
            let mut sum: ay_core::kani_compat::DetHashMap<String, Rational64> =
                ay_core::kani_compat::DetHashMap::default();
            if let Some(coeff_map) = coeffs_a.get(i) {
                for (var, &val) in coeff_map {
                    *sum.entry(var.clone())
                        .or_insert(Rational64::from_integer(0)) += val;
                }
            }
            if let Some(coeff_map) = coeffs_b.get(i) {
                for (var, &val) in coeff_map {
                    let contribution = if negate_b { -val } else { val };
                    *sum.entry(var.clone())
                        .or_insert(Rational64::from_integer(0)) += contribution;
                }
            }
            for &val in sum.values() {
                if val != Rational64::from_integer(0) {
                    return false;
                }
            }
        }
        true
    }

    fn extract_init_constant(
        problem: &ChcProblem,
        pred_id: PredicateId,
        var_idx: usize,
    ) -> Option<i128> {
        let mut values = Vec::new();
        for fact in problem.facts() {
            match &fact.head {
                crate::ClauseHead::Predicate(id, args) if *id == pred_id => {
                    if let Some(arg) = args.get(var_idx) {
                        if let ChcExpr::Int(n) = arg {
                            values.push(*n);
                        } else if let ChcExpr::Var(v) = arg {
                            if let Some(constraint) = &fact.body.constraint {
                                if let Some(c) = Self::find_equality_constant(constraint, &v.name) {
                                    values.push(c);
                                }
                            }
                        }
                    }
                }
                _ => continue,
            }
        }
        if values.is_empty() {
            return None;
        }
        let first = values[0];
        if values.iter().all(|&v| v == first) {
            Some(first)
        } else {
            None
        }
    }

    fn find_equality_constant(expr: &ChcExpr, var_name: &str) -> Option<i128> {
        crate::expr::maybe_grow_expr_stack(|| match expr {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args {
                    if let Some(c) = Self::find_equality_constant(arg, var_name) {
                        return Some(c);
                    }
                }
                None
            }
            ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == var_name => Some(*c),
                (ChcExpr::Int(c), ChcExpr::Var(v)) if v.name == var_name => Some(*c),
                _ => None,
            },
            _ => None,
        })
    }
}

impl LemmaHintProvider for RecurrenceConservedEqualityProvider {
    fn collect(&self, req: &HintRequest<'_>, out: &mut Vec<LemmaHint>) {
        if req.stage != HintStage::Startup {
            return;
        }
        for clause in req.problem.transitions() {
            let (pred_id, _body_args, _) = match Self::is_self_loop(clause) {
                Some(x) => x,
                None => continue,
            };
            let canonical_vars = match req.canonical_vars(pred_id) {
                Some(vars) => vars,
                None => continue,
            };
            if canonical_vars
                .iter()
                .any(|v| !matches!(v.sort, crate::ChcSort::Int))
            {
                continue;
            }
            let (transition, state_var_names) =
                match Self::extract_transition(clause, canonical_vars) {
                    Some(x) => x,
                    None => continue,
                };
            let system = match crate::recurrence::analyze_transition(&transition, &state_var_names)
            {
                Some(s) => s,
                None => continue,
            };
            let mut var_coeffs: Vec<(
                usize,
                Vec<ay_core::kani_compat::DetHashMap<String, num_rational::Rational64>>,
            )> = Vec::new();
            for (i, var_name) in state_var_names.iter().enumerate() {
                if let Some(cf) = system.get_solution(var_name) {
                    if let Some(coeffs) = Self::to_polynomial_coeffs(cf) {
                        var_coeffs.push((i, coeffs));
                    }
                }
            }
            for (idx_a, (i, coeffs_a)) in var_coeffs.iter().enumerate() {
                for (j, coeffs_b) in &var_coeffs[idx_a + 1..] {
                    if Self::coeffs_sum_to_zero(coeffs_a, coeffs_b, false) {
                        let const_i = Self::extract_init_constant(req.problem, pred_id, *i);
                        let const_j = Self::extract_init_constant(req.problem, pred_id, *j);
                        // i128-lockstep: checked add; skip the hint on overflow.
                        if let Some(sum) =
                            const_i.zip(const_j).and_then(|(ci, cj)| ci.checked_add(cj))
                        {
                            let hint_formula = ChcExpr::eq(
                                ChcExpr::add(
                                    ChcExpr::var(canonical_vars[*i].clone()),
                                    ChcExpr::var(canonical_vars[*j].clone()),
                                ),
                                ChcExpr::int(sum),
                            );
                            out.push(LemmaHint::new(
                                pred_id,
                                hint_formula,
                                Self::PRIORITY,
                                Self::SOURCE,
                            ));
                        }
                    }
                    if Self::coeffs_sum_to_zero(coeffs_a, coeffs_b, true) {
                        let const_i = Self::extract_init_constant(req.problem, pred_id, *i);
                        let const_j = Self::extract_init_constant(req.problem, pred_id, *j);
                        // i128-lockstep: checked sub; skip the hint on overflow.
                        if let Some(diff) =
                            const_i.zip(const_j).and_then(|(ci, cj)| ci.checked_sub(cj))
                        {
                            let hint_formula = ChcExpr::eq(
                                ChcExpr::sub(
                                    ChcExpr::var(canonical_vars[*i].clone()),
                                    ChcExpr::var(canonical_vars[*j].clone()),
                                ),
                                ChcExpr::int(diff),
                            );
                            out.push(LemmaHint::new(
                                pred_id,
                                hint_formula,
                                Self::PRIORITY,
                                Self::SOURCE,
                            ));
                        }
                    }
                    for k in [2i64, 3, -2, -3] {
                        let scale_coeffs = |coeffs: &Vec<
                            ay_core::kani_compat::DetHashMap<String, num_rational::Rational64>,
                        >| {
                            coeffs
                                .iter()
                                .map(|term_coeffs| {
                                    term_coeffs
                                        .iter()
                                        .map(|(var, val)| {
                                            (
                                                var.clone(),
                                                *val * num_rational::Rational64::from_integer(k),
                                            )
                                        })
                                        .collect()
                                })
                                .collect::<Vec<_>>()
                        };
                        let scaled_coeffs_a = scale_coeffs(coeffs_a);
                        if Self::coeffs_sum_to_zero(&scaled_coeffs_a, coeffs_b, true) {
                            let const_i = Self::extract_init_constant(req.problem, pred_id, *i);
                            let const_j = Self::extract_init_constant(req.problem, pred_id, *j);
                            // i128-lockstep: checked mul/sub; skip on overflow.
                            if let Some(c) = const_i.zip(const_j).and_then(|(ci, cj)| {
                                i128::from(k)
                                    .checked_mul(ci)
                                    .and_then(|kci| kci.checked_sub(cj))
                            }) {
                                let scaled_vi = ChcExpr::mul(
                                    ChcExpr::int(k),
                                    ChcExpr::var(canonical_vars[*i].clone()),
                                );
                                let rhs = if c == 0 {
                                    ChcExpr::var(canonical_vars[*j].clone())
                                } else {
                                    ChcExpr::add(
                                        ChcExpr::var(canonical_vars[*j].clone()),
                                        ChcExpr::int(c),
                                    )
                                };
                                let hint_formula = ChcExpr::eq(scaled_vi, rhs);
                                out.push(LemmaHint::new(
                                    pred_id,
                                    hint_formula,
                                    Self::PRIORITY,
                                    Self::SOURCE,
                                ));
                            }
                        }
                        let scaled_coeffs_b = scale_coeffs(coeffs_b);
                        if Self::coeffs_sum_to_zero(coeffs_a, &scaled_coeffs_b, true) {
                            let const_i = Self::extract_init_constant(req.problem, pred_id, *i);
                            let const_j = Self::extract_init_constant(req.problem, pred_id, *j);
                            // i128-lockstep: checked mul/sub; skip on overflow.
                            if let Some(c) = const_i.zip(const_j).and_then(|(ci, cj)| {
                                i128::from(k)
                                    .checked_mul(cj)
                                    .and_then(|kcj| ci.checked_sub(kcj))
                            }) {
                                let scaled_vj = ChcExpr::mul(
                                    ChcExpr::int(k),
                                    ChcExpr::var(canonical_vars[*j].clone()),
                                );
                                let rhs = if c == 0 {
                                    scaled_vj
                                } else {
                                    ChcExpr::add(scaled_vj, ChcExpr::int(c))
                                };
                                let hint_formula =
                                    ChcExpr::eq(ChcExpr::var(canonical_vars[*i].clone()), rhs);
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
        }
    }
}

pub(super) static RECURRENCE_CONSERVED_EQ_PROVIDER: RecurrenceConservedEqualityProvider =
    RecurrenceConservedEqualityProvider;
