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
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use num_bigint::BigInt;
use std::sync::Arc;

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

        let Some((projected, eliminated)) = eliminate_locals(constraint, &local_vars) else {
            return (clause.clone(), 0);
        };

        let final_constraint = projected.simplify_array_ops().simplify_constants();
        let new_body = ClauseBody::new(
            clause.body.predicates.clone(),
            Some(final_constraint).filter(|c| !matches!(c, ChcExpr::Bool(true))),
        );
        (HornClause::new(new_body, clause.head.clone()), eliminated)
    }
}

/// Project `local_vars` out of `constraint`, one variable at a time in the
/// given order, and return the projected conjunction with the number of
/// variables eliminated (`None` when none was).
///
/// Each variable is tried against three exact projection rules, first match
/// wins:
/// 1. equality substitution: the first conjunct (in conjunction order) of the
///    form `var = e` / `e = var` with `var` not in `e` is dropped and `e` is
///    substituted for `var` in every other conjunct;
/// 2. constant interval (Int only): every conjunct mentioning `var` is a bound
///    `var op c` with `c` ground; they are dropped, or the whole conjunction
///    becomes `false` when the interval is empty;
/// 3. one-sided bound: every conjunct mentioning `var` is a linear bound on
///    `var` and they all bound it from the same side; they are dropped. A
///    variable that no longer occurs anywhere is eliminated by this rule.
///
/// After every successful step the conjunction is kept in `and_all` normal
/// form: flattened, without `true`, without repeated conjuncts (the first copy
/// wins), and collapsed to `false` as soon as a conjunct is `false`.
///
/// The work is driven by a [`ConjunctTable`]: each conjunct's variable set is
/// computed once, and an occurrence index restricts every rule to the
/// conjuncts that mention the variable, so a substitution rewrites only those.
fn eliminate_locals(constraint: &ChcExpr, local_vars: &[ChcVar]) -> Option<(ChcExpr, usize)> {
    let mut table = ConjunctTable::new(constraint);
    let mut eliminated = 0;
    for var in local_vars {
        if table.try_eliminate(var) {
            eliminated += 1;
            table.note_success();
        }
    }
    (eliminated > 0).then(|| (table.into_constraint(), eliminated))
}

type SlotId = usize;
type VarId = usize;

struct Conjunct {
    expr: ChcExpr,
    /// Sorted ids of `expr.vars()`.
    vars: Vec<VarId>,
    /// Position in the conjunction: live conjuncts ordered by `key`
    /// (lexicographically) are the conjunction in order. A conjunct that a
    /// substitution splits into `k` conjuncts is replaced by keys `key ++ [j]`,
    /// which sort between it and its successor.
    key: Vec<u32>,
    live: bool,
}

/// The conjuncts of one clause constraint under elimination, with an
/// occurrence index from each variable to the conjuncts that mention it.
struct ConjunctTable {
    conjuncts: Vec<Conjunct>,
    var_ids: FxHashMap<ChcVar, VarId>,
    /// Conjuncts that mentioned each variable when they were added. Entries go
    /// stale when a conjunct dies; [`Self::live_occurrences`] drops them.
    occurrences: Vec<Vec<SlotId>>,
    /// Live conjunct -> its slot. `None` until the first successful step:
    /// like the reference `and_all`, repeated conjuncts of the input are kept
    /// until a step rebuilds the conjunction.
    distinct: Option<FxHashMap<ChcExpr, SlotId>>,
    /// The conjunction is `false`.
    contradiction: bool,
}

impl ConjunctTable {
    fn new(constraint: &ChcExpr) -> Self {
        let mut table = Self {
            conjuncts: Vec::new(),
            var_ids: FxHashMap::default(),
            occurrences: Vec::new(),
            distinct: None,
            contradiction: false,
        };
        let mut position = 0u32;
        for conj in flatten_conjuncts(constraint) {
            table.push(conj, vec![position]);
            position += 1;
        }
        table
    }

    fn push(&mut self, expr: ChcExpr, key: Vec<u32>) -> SlotId {
        let id = self.conjuncts.len();
        let mut vars = Vec::new();
        for var in exact_vars(&expr) {
            let next = self.occurrences.len();
            let var_id = *self.var_ids.entry(var).or_insert(next);
            if var_id == next {
                self.occurrences.push(Vec::new());
            }
            self.occurrences[var_id].push(id);
            vars.push(var_id);
        }
        vars.sort_unstable();
        self.conjuncts.push(Conjunct {
            expr,
            vars,
            key,
            live: true,
        });
        id
    }

    /// The live conjuncts mentioning `var`, in conjunction order.
    fn live_occurrences(&mut self, var: &ChcVar) -> Vec<SlotId> {
        let Some(&var_id) = self.var_ids.get(var) else {
            return Vec::new();
        };
        let mut occurrences = std::mem::take(&mut self.occurrences[var_id]);
        let conjuncts = &self.conjuncts;
        occurrences
            .retain(|&id| conjuncts[id].live && conjuncts[id].vars.binary_search(&var_id).is_ok());
        occurrences.sort_unstable_by(|&a, &b| conjuncts[a].key.cmp(&conjuncts[b].key));
        occurrences.dedup();
        self.occurrences[var_id].clone_from(&occurrences);
        occurrences
    }

    fn try_eliminate(&mut self, var: &ChcVar) -> bool {
        if self.contradiction {
            // `false` mentions no variable: the one-sided rule applies.
            return true;
        }
        let occurrences = self.live_occurrences(var);
        self.try_equality_substitution(var, &occurrences)
            || self.try_constant_interval_elimination(var, &occurrences)
            || self.try_one_sided_bound_elimination(var, &occurrences)
    }

    fn try_equality_substitution(&mut self, var: &ChcVar, occurrences: &[SlotId]) -> bool {
        let Some((defining, replacement)) = occurrences.iter().find_map(|&id| {
            extract_equality_for_var(&self.conjuncts[id].expr, var).map(|e| (id, e))
        }) else {
            return false;
        };
        // `substitute` keeps an original child when it reaches its depth or
        // node limit, so it can return a conjunct that still mentions `var`.
        // Rewrite every occurrence first and commit only if `var` is gone
        // from all of them: dropping the definition while an occurrence
        // survives would leave the variable free and weaken the projection.
        let subst = [(var.clone(), replacement)];
        let mut rewritten = Vec::with_capacity(occurrences.len());
        for &id in occurrences {
            if id == defining || !self.conjuncts[id].live {
                continue;
            }
            let expr = self.conjuncts[id].expr.substitute(&subst);
            if exact_vars(&expr).contains(var) {
                return false;
            }
            rewritten.push((id, expr));
        }
        self.kill(defining);
        for (id, expr) in rewritten {
            if !self.conjuncts[id].live {
                continue;
            }
            self.rewrite(id, &expr);
            if self.contradiction {
                break;
            }
        }
        true
    }

    fn try_constant_interval_elimination(&mut self, var: &ChcVar, occurrences: &[SlotId]) -> bool {
        if !matches!(&var.sort, crate::ChcSort::Int) || occurrences.is_empty() {
            return false;
        }
        let mut lower: Option<BigInt> = None;
        let mut upper: Option<BigInt> = None;
        for &id in occurrences {
            match classify_constant_int_bound(&self.conjuncts[id].expr, var) {
                None => return false,
                Some(ConstantIntBound::Lower(value)) => {
                    lower = Some(match lower.take() {
                        Some(current) => current.max(value),
                        None => value,
                    });
                }
                Some(ConstantIntBound::Upper(value)) => {
                    upper = Some(match upper.take() {
                        Some(current) => current.min(value),
                        None => value,
                    });
                }
            }
        }
        if matches!((lower, upper), (Some(lower), Some(upper)) if lower > upper) {
            self.contradiction = true;
            return true;
        }
        for &id in occurrences {
            self.kill(id);
        }
        true
    }

    fn try_one_sided_bound_elimination(&mut self, var: &ChcVar, occurrences: &[SlotId]) -> bool {
        let mut has_lower = false;
        let mut has_upper = false;
        for &id in occurrences {
            match classify_bound(&self.conjuncts[id].expr, var) {
                BoundType::Lower => has_lower = true,
                BoundType::Upper => has_upper = true,
                BoundType::NotBound => return false,
            }
        }
        if has_lower && has_upper {
            return false;
        }
        for &id in occurrences {
            self.kill(id);
        }
        true
    }

    /// Replace conjunct `id` by the conjuncts of `rewritten`.
    fn rewrite(&mut self, id: SlotId, rewritten: &ChcExpr) {
        let mut pieces = flatten_conjuncts(rewritten);
        if pieces
            .iter()
            .any(|piece| matches!(piece, ChcExpr::Bool(false)))
        {
            self.contradiction = true;
            return;
        }
        let key = self.conjuncts[id].key.clone();
        self.kill(id);
        if pieces.len() == 1 {
            let piece = pieces.pop().unwrap_or(ChcExpr::Bool(true));
            let new_id = self.push(piece, key);
            self.admit(new_id);
            return;
        }
        for (j, piece) in pieces.into_iter().enumerate() {
            let mut piece_key = key.clone();
            piece_key.push(u32::try_from(j).unwrap_or(u32::MAX));
            let new_id = self.push(piece, piece_key);
            self.admit(new_id);
        }
    }

    fn kill(&mut self, id: SlotId) {
        let expr = Self::retire(&mut self.conjuncts[id]);
        if let Some(distinct) = &mut self.distinct {
            if distinct.get(&expr) == Some(&id) {
                distinct.remove(&expr);
            }
        }
    }

    fn retire(conjunct: &mut Conjunct) -> ChcExpr {
        conjunct.live = false;
        conjunct.vars = Vec::new();
        std::mem::replace(&mut conjunct.expr, ChcExpr::Bool(true))
    }

    /// Keep only the first copy of a repeated conjunct.
    fn admit(&mut self, id: SlotId) {
        let Some(distinct) = &mut self.distinct else {
            return;
        };
        let expr = self.conjuncts[id].expr.clone();
        match distinct.get(&expr).copied() {
            None => {
                distinct.insert(expr, id);
            }
            Some(other) if self.conjuncts[other].key < self.conjuncts[id].key => {
                Self::retire(&mut self.conjuncts[id]);
            }
            Some(other) => {
                Self::retire(&mut self.conjuncts[other]);
                distinct.insert(expr, id);
            }
        }
    }

    /// A step succeeded: on the first one, bring the conjunction to `and_all`
    /// normal form (later steps keep it there incrementally).
    fn note_success(&mut self) {
        if self.distinct.is_some() || self.contradiction {
            return;
        }
        let mut order: Vec<SlotId> = (0..self.conjuncts.len())
            .filter(|&id| self.conjuncts[id].live)
            .collect();
        order.sort_unstable_by(|&a, &b| self.conjuncts[a].key.cmp(&self.conjuncts[b].key));
        let mut distinct = FxHashMap::default();
        for id in order {
            let expr = &self.conjuncts[id].expr;
            if matches!(expr, ChcExpr::Bool(false)) {
                self.contradiction = true;
                return;
            }
            if distinct.contains_key(expr) {
                Self::retire(&mut self.conjuncts[id]);
            } else {
                distinct.insert(expr.clone(), id);
            }
        }
        self.distinct = Some(distinct);
    }

    fn into_constraint(self) -> ChcExpr {
        if self.contradiction {
            return ChcExpr::Bool(false);
        }
        let mut live: Vec<Conjunct> = self.conjuncts.into_iter().filter(|c| c.live).collect();
        live.sort_unstable_by(|a, b| a.key.cmp(&b.key));
        ChcExpr::and_all(live.into_iter().map(|c| c.expr))
    }
}

/// The conjuncts of `expr`: nested `and`s flattened at any depth, in order,
/// with `true` dropped. Unlike [`ChcExpr::collect_conjuncts`], which stops at
/// `MAX_EXPR_RECURSION_DEPTH` and keeps the deeper `and` as one conjunct, this
/// matches the flattening of [`ChcExpr::and_all`], so no conjunct hides inside
/// an unflattened `and` remainder. A shared nested `and` is expanded once (a
/// second expansion would only repeat its conjuncts).
fn flatten_conjuncts(expr: &ChcExpr) -> Vec<ChcExpr> {
    let mut out = Vec::new();
    let mut expanded: FxHashSet<*const ChcExpr> = FxHashSet::default();
    let mut stack: Vec<&ChcExpr> = vec![expr];
    while let Some(node) = stack.pop() {
        match node {
            ChcExpr::Op(ChcOp::And, args) => {
                for arg in args.iter().rev() {
                    if matches!(arg.as_ref(), ChcExpr::Op(ChcOp::And, _))
                        && !expanded.insert(Arc::as_ptr(arg))
                    {
                        continue;
                    }
                    stack.push(arg);
                }
            }
            ChcExpr::Bool(true) => {}
            other => out.push(other.clone()),
        }
    }
    out
}

/// Every variable of `expr`, at any depth (unlike [`ChcExpr::vars`], which
/// stops at `MAX_EXPR_RECURSION_DEPTH`): the occurrence index and the
/// shared-variable test must not miss a deep occurrence. Each shared node is
/// visited once.
fn exact_vars(expr: &ChcExpr) -> Vec<ChcVar> {
    let mut seen_vars: FxHashSet<ChcVar> = FxHashSet::default();
    let mut out = Vec::new();
    let mut visited: FxHashSet<*const ChcExpr> = FxHashSet::default();
    let mut stack: Vec<&ChcExpr> = vec![expr];
    while let Some(node) = stack.pop() {
        if let ChcExpr::Var(var) = node {
            if seen_vars.insert(var.clone()) {
                out.push(var.clone());
            }
            continue;
        }
        for child in expr_children(node).iter().rev() {
            if visited.insert(Arc::as_ptr(child)) {
                stack.push(child);
            }
        }
    }
    out
}

fn expr_children(node: &ChcExpr) -> &[Arc<ChcExpr>] {
    match node {
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            args
        }
        ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
        ChcExpr::ArrayLambda(lambda) => lambda.captures(),
        ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::Var(_)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => &[],
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

/// Variables of the clause's predicate arguments, at any depth: a variable
/// missed here would be eliminated as a local although a predicate reads it.
fn collect_shared_vars(clause: &HornClause) -> FxHashSet<ChcVar> {
    let head_args: &[ChcExpr] = match &clause.head {
        crate::ClauseHead::Predicate(_, args) => args,
        crate::ClauseHead::False => &[],
    };
    clause
        .body
        .predicates
        .iter()
        .flat_map(|(_, args)| args.iter())
        .chain(head_args)
        .flat_map(exact_vars)
        .collect()
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
