// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Clause-local variable elimination for CHC problems.
//!
//! Eliminates variables that appear only in constraints, not predicate arguments.
//! Part of #1615 CHC regression fix.
//!
//! Reference: Z3 Spacer qe_project, the development design notes

use crate::{ChcExpr, ChcOp, ChcProblem, ChcVar, ClauseBody, HornClause};
use ay_core::kani_compat::DetHashSet as FxHashSet;
use num_bigint::BigInt;

use super::{
    MemoryBackTranslator, TransformMemoryReport, TransformObligation, TransformationResult,
    Transformer,
};

pub(crate) struct LocalVarEliminator {
    verbose: bool,
}

impl Default for LocalVarEliminator {
    fn default() -> Self {
        Self::new()
    }
}

impl LocalVarEliminator {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    pub(crate) fn eliminate(&self, problem: &ChcProblem) -> ChcProblem {
        self.eliminate_with_index_map(problem).0
    }

    fn eliminate_with_index_map(&self, problem: &ChcProblem) -> (ChcProblem, Vec<usize>) {
        let mut total_eliminated = 0;
        let mut clauses_modified = 0;
        let mut new_clauses = Vec::with_capacity(problem.clauses().len());
        let mut output_to_input = Vec::with_capacity(problem.clauses().len());

        for (input_index, clause) in problem.clauses().iter().enumerate() {
            let (new_clause, eliminated) = self.eliminate_in_clause(clause);
            if eliminated > 0 {
                total_eliminated += eliminated;
                clauses_modified += 1;
            }
            if !is_trivially_false(&new_clause) {
                new_clauses.push(new_clause);
                output_to_input.push(input_index);
            }
        }

        if self.verbose && total_eliminated > 0 {
            safe_eprintln!(
                "CHC: local-var-elim: {} vars across {} clauses",
                total_eliminated,
                clauses_modified
            );
        }

        let mut new_problem = ChcProblem::new();
        for pred in problem.predicates() {
            new_problem.declare_predicate(&pred.name, pred.arg_sorts.clone());
        }
        for clause in new_clauses {
            new_problem.add_clause(clause);
        }
        (new_problem, output_to_input)
    }

    fn eliminate_in_clause(&self, clause: &HornClause) -> (HornClause, usize) {
        let constraint = match &clause.body.constraint {
            Some(c) => c,
            None => return (clause.clone(), 0),
        };

        let shared_vars = collect_shared_vars(clause);
        let constraint_vars: FxHashSet<_> = constraint.vars().into_iter().collect();
        let local_vars: Vec<_> = constraint_vars
            .iter()
            .filter(|v| !shared_vars.contains(*v))
            .cloned()
            .collect();
        if local_vars.is_empty() {
            return (clause.clone(), 0);
        }

        let mut current_constraint = constraint.clone();
        let mut eliminated = 0;
        for var in &local_vars {
            if let Some(simplified) = self.try_eliminate_var(&current_constraint, var) {
                current_constraint = simplified;
                eliminated += 1;
            }
        }
        if eliminated == 0 {
            return (clause.clone(), 0);
        }

        let final_constraint = current_constraint.simplify_array_ops().simplify_constants();
        let new_body = ClauseBody::new(
            clause.body.predicates.clone(),
            Some(final_constraint).filter(|c| !matches!(c, ChcExpr::Bool(true))),
        );
        (HornClause::new(new_body, clause.head.clone()), eliminated)
    }

    fn try_eliminate_var(&self, constraint: &ChcExpr, var: &ChcVar) -> Option<ChcExpr> {
        if let Some(result) = self.try_equality_substitution(constraint, var) {
            return Some(result);
        }
        if let Some(result) = self.try_constant_interval_elimination(constraint, var) {
            return Some(result);
        }
        self.try_one_sided_bound_elimination(constraint, var)
    }

    fn try_equality_substitution(&self, constraint: &ChcExpr, var: &ChcVar) -> Option<ChcExpr> {
        let conjuncts = {
            let mut c = constraint.collect_conjuncts();
            c.retain(|x| !matches!(x, ChcExpr::Bool(true)));
            c
        };
        for (i, conj) in conjuncts.iter().enumerate() {
            if let Some(replacement) = extract_equality_for_var(conj, var) {
                let subst = vec![(var.clone(), replacement)];
                let other: Vec<ChcExpr> = conjuncts
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, c)| c.substitute(&subst))
                    .collect();
                return Some(ChcExpr::and_all(other));
            }
        }
        None
    }

    fn try_constant_interval_elimination(
        &self,
        constraint: &ChcExpr,
        var: &ChcVar,
    ) -> Option<ChcExpr> {
        if !matches!(&var.sort, crate::ChcSort::Int) {
            return None;
        }

        let conjuncts = {
            let mut c = constraint.collect_conjuncts();
            c.retain(|x| !matches!(x, ChcExpr::Bool(true)));
            c
        };
        let mut lower: Option<BigInt> = None;
        let mut upper: Option<BigInt> = None;
        let mut found_bound = false;

        for conj in &conjuncts {
            if !conjunct_mentions_var(conj, var) {
                continue;
            }
            found_bound = true;
            match classify_constant_int_bound(conj, var)? {
                ConstantIntBound::Lower(value) => {
                    lower = Some(match lower.take() {
                        Some(current) => current.max(value),
                        None => value,
                    });
                }
                ConstantIntBound::Upper(value) => {
                    upper = Some(match upper.take() {
                        Some(current) => current.min(value),
                        None => value,
                    });
                }
            }
        }

        if !found_bound {
            return None;
        }
        if matches!((lower, upper), (Some(lower), Some(upper)) if lower > upper) {
            return Some(ChcExpr::Bool(false));
        }

        Some(ChcExpr::and_all(
            conjuncts
                .into_iter()
                .filter(|conj| !conjunct_mentions_var(conj, var)),
        ))
    }

    fn try_one_sided_bound_elimination(
        &self,
        constraint: &ChcExpr,
        var: &ChcVar,
    ) -> Option<ChcExpr> {
        let conjuncts = {
            let mut c = constraint.collect_conjuncts();
            c.retain(|x| !matches!(x, ChcExpr::Bool(true)));
            c
        };
        let mut has_lower = false;
        let mut has_upper = false;
        let mut all_bounds = true;

        for conj in &conjuncts {
            if !conjunct_mentions_var(conj, var) {
                continue;
            }
            match classify_bound(conj, var) {
                BoundType::Lower => has_lower = true,
                BoundType::Upper => has_upper = true,
                BoundType::NotBound => {
                    all_bounds = false;
                    break;
                }
            }
        }
        if !all_bounds || (has_lower && has_upper) {
            return None;
        }
        Some(ChcExpr::and_all(
            conjuncts
                .into_iter()
                .filter(|c| !conjunct_mentions_var(c, var)),
        ))
    }
}

impl Transformer for LocalVarEliminator {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let (transformed, output_to_input) = self.eliminate_with_index_map(&problem);
        TransformationResult {
            problem: transformed,
            back_translator: Box::new(
                MemoryBackTranslator::new(
                    TransformMemoryReport::with_original_validation_obligations(
                        "local_var_elimination",
                        [
                            TransformObligation::named("local-existential-projection"),
                            TransformObligation::named("original-validation-on-safe"),
                            TransformObligation::named("original-replay-on-unsafe"),
                        ],
                    ),
                )
                .with_ground_index_map(
                    "local-var-elimination",
                    &problem,
                    output_to_input,
                ),
            ),
        }
    }
}

fn collect_shared_vars(clause: &HornClause) -> FxHashSet<ChcVar> {
    let mut vars = FxHashSet::default();
    for (_, args) in &clause.body.predicates {
        for arg in args {
            for v in arg.vars() {
                vars.insert(v);
            }
        }
    }
    for v in clause.head.vars() {
        vars.insert(v);
    }
    vars
}

fn extract_equality_for_var(conj: &ChcExpr, var: &ChcVar) -> Option<ChcExpr> {
    if let ChcExpr::Op(ChcOp::Eq, args) = conj {
        if args.len() == 2 {
            if let ChcExpr::Var(v) = &*args[0] {
                if v == var && !args[1].vars().contains(var) {
                    return Some((*args[1]).clone());
                }
            }
            if let ChcExpr::Var(v) = &*args[1] {
                if v == var && !args[0].vars().contains(var) {
                    return Some((*args[0]).clone());
                }
            }
        }
    }
    None
}

fn conjunct_mentions_var(conj: &ChcExpr, var: &ChcVar) -> bool {
    conj.vars().contains(var)
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum ConstantIntBound {
    Lower(BigInt),
    Upper(BigInt),
}

fn classify_constant_int_bound(conj: &ChcExpr, var: &ChcVar) -> Option<ConstantIntBound> {
    let ChcExpr::Op(op @ (ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt), args) = conj else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    let (var_on_lhs, constant_expr) = match (args[0].as_ref(), args[1].as_ref()) {
        (ChcExpr::Var(candidate), constant) if candidate == var => (true, constant),
        (constant, ChcExpr::Var(candidate)) if candidate == var => (false, constant),
        _ => return None,
    };
    let mut constant = eval_ground_int_constant(constant_expr)?;
    let strict = matches!(*op, ChcOp::Gt | ChcOp::Lt);
    let lower = matches!(
        (*op, var_on_lhs),
        (ChcOp::Ge | ChcOp::Gt, true) | (ChcOp::Le | ChcOp::Lt, false)
    );
    if strict {
        if lower {
            constant += 1;
        } else {
            constant -= 1;
        }
    }

    Some(if lower {
        ConstantIntBound::Lower(constant)
    } else {
        ConstantIntBound::Upper(constant)
    })
}

fn eval_ground_int_constant(expr: &ChcExpr) -> Option<BigInt> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Int(value) => Some(BigInt::from(*value)),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            Some(-eval_ground_int_constant(&args[0])?)
        }
        ChcExpr::Op(ChcOp::Add, args) if !args.is_empty() => {
            let mut args = args.iter();
            let mut value = eval_ground_int_constant(args.next()?)?;
            for arg in args {
                value += eval_ground_int_constant(arg)?;
            }
            Some(value)
        }
        ChcExpr::Op(ChcOp::Mul, args) if !args.is_empty() => {
            let mut args = args.iter();
            let mut value = eval_ground_int_constant(args.next()?)?;
            for arg in args {
                value *= eval_ground_int_constant(arg)?;
            }
            Some(value)
        }
        _ => None,
    })
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BoundType {
    Lower,
    Upper,
    NotBound,
}

fn classify_bound(conj: &ChcExpr, var: &ChcVar) -> BoundType {
    match conj {
        ChcExpr::Op(ChcOp::Ge | ChcOp::Gt, args) if args.len() == 2 => {
            if is_var_expr(&args[0], var) && !args[1].vars().contains(var) {
                return BoundType::Lower;
            }
            if is_var_expr(&args[1], var) && !args[0].vars().contains(var) {
                return BoundType::Upper;
            }
        }
        ChcExpr::Op(ChcOp::Le | ChcOp::Lt, args) if args.len() == 2 => {
            if is_var_expr(&args[0], var) && !args[1].vars().contains(var) {
                return BoundType::Upper;
            }
            if is_var_expr(&args[1], var) && !args[0].vars().contains(var) {
                return BoundType::Lower;
            }
        }
        _ => {}
    }
    if let Some(bt) = classify_linear_bound(conj, var) {
        return bt;
    }
    BoundType::NotBound
}

fn is_var_expr(expr: &ChcExpr, var: &ChcVar) -> bool {
    matches!(expr, ChcExpr::Var(v) if v == var)
}

fn classify_linear_bound(conj: &ChcExpr, var: &ChcVar) -> Option<BoundType> {
    match conj {
        ChcExpr::Op(op @ (ChcOp::Ge | ChcOp::Gt | ChcOp::Le | ChcOp::Lt), args)
            if args.len() == 2 =>
        {
            let (lhs, rhs) = (&*args[0], &*args[1]);
            let (lhs_has, rhs_has) = (lhs.vars().contains(var), rhs.vars().contains(var));
            if lhs_has && !rhs_has {
                return Some(determine_bound_type(
                    *op,
                    get_linear_coefficient(lhs, var)?,
                    true,
                ));
            }
            if rhs_has && !lhs_has {
                return Some(determine_bound_type(
                    *op,
                    get_linear_coefficient(rhs, var)?,
                    false,
                ));
            }
            None
        }
        _ => None,
    }
}

fn get_linear_coefficient(expr: &ChcExpr, var: &ChcVar) -> Option<i128> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Var(v) if v == var => Some(1),
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            if let ChcExpr::Int(c) = args[0].as_ref() {
                if is_var_expr(&args[1], var) {
                    return Some(*c);
                }
            }
            if let ChcExpr::Int(c) = args[1].as_ref() {
                if is_var_expr(&args[0], var) {
                    return Some(*c);
                }
            }
            None
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut found = None;
            for arg in args {
                if arg.vars().contains(var) {
                    if found.is_some() {
                        return None;
                    }
                    found = get_linear_coefficient(arg, var);
                }
            }
            found
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let l = if args[0].vars().contains(var) {
                get_linear_coefficient(&args[0], var)
            } else {
                Some(0)
            };
            let r = if args[1].vars().contains(var) {
                get_linear_coefficient(&args[1], var)
            } else {
                Some(0)
            };
            match (l, r) {
                (Some(l), Some(r)) => l.checked_sub(r),
                _ => None,
            }
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            get_linear_coefficient(&args[0], var).and_then(i128::checked_neg)
        }
        _ => {
            if !expr.vars().contains(var) {
                Some(0)
            } else {
                None
            }
        }
    })
}

fn determine_bound_type(op: ChcOp, coeff: i128, var_on_lhs: bool) -> BoundType {
    if coeff == 0 {
        return BoundType::NotBound;
    }
    let is_lower_op = matches!(op, ChcOp::Ge | ChcOp::Gt);
    let effective_lower = if var_on_lhs {
        is_lower_op
    } else {
        !is_lower_op
    };
    if (coeff > 0) == effective_lower {
        BoundType::Lower
    } else {
        BoundType::Upper
    }
}

fn is_trivially_false(clause: &HornClause) -> bool {
    matches!(clause.body.constraint, Some(ChcExpr::Bool(false)))
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "local_var_elimination_tests.rs"]
mod tests;
