// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Equality solving ("solve-eqs") for scalar Search-lane queries.
//!
//! The transition-system engines (IMC, BMC-style unrollings, TPA, DAR, PDKind)
//! and PDR ask the executor about formulas of the shape
//! `init(x0) ∧ T(x0,x1) ∧ … ∧ T(x_{k-1},x_k) ∧ bad(x_k)` or
//! `F(x) ∧ T(x,x') ∧ cube(x')`. On the LRA-Lin track (sally, cav12) `T` is a
//! disjunction of guarded cases whose disjuncts are mostly frame equalities
//! (`x' = x`), and `init` / the cube pin many variables to constants. z3's
//! default tactic eliminates those equalities before search (`solve-eqs`):
//! substituting the init constants selects one disjunct of `T@0`, its frame
//! equalities become top-level and are eliminated in turn, and the whole
//! unrolling collapses. The ay-dpll QF_LRA route has no such pass, so it
//! searches the disjunctions: om1_with_relays_agreement's IMC k=4 check takes
//! 2.7 s (191 k decisions) where z3 needs 58 decisions; after z3's `solve-eqs`
//! the same formula takes ay 0.07 s. azadmanesh scenario1's IMC k=1 check goes
//! from `unknown` at 30 s to 0.06 s.
//!
//! [`solve_eqs`] repeats, to a fixed point: extract top-level definitions
//! `x = t` (`x ∉ vars(t)`, `t` small), `b` / `¬b` for Bool `b`; substitute
//! them (DAG-memoised, sharing-preserving); fold constants (exact rationals),
//! Boolean structure and `ite`s; flatten new top-level conjunctions. The
//! residual is equisatisfiable with the input: `F ≡ ∃X. F` for the eliminated
//! `X`, because each eliminated `x` is constrained only by its own definition
//! once it has been substituted everywhere.
//!
//! Model reconstruction: definitions are kept idempotent (a right-hand side
//! mentions no eliminated variable), so every eliminated variable is the value
//! of its definition under the residual's model; variables that vanished from
//! the residual without a definition are unconstrained and get a default.
//! Callers validate the completed model against the ORIGINAL formula, so a
//! reconstruction defect can only turn `sat` into `unknown`.
//!
//! Soundness of `unsat`: the executor refutes the residual; the residual is
//! equisatisfiable with the input by the argument above. Callers use this only
//! on the Search lane, whose `unsat` never publishes a verdict on its own (every
//! Safe is re-validated on the Verification lane, every Unsafe replayed).

use std::sync::Arc;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use num_rational::BigRational;
use num_traits::Zero;

use super::types::SmtValue;
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};

mod fold;
mod shape;
use fold::Simplifier;
use shape::{is_scalar_term, is_substitutable, rejoin_equality_pairs};

/// Passes that may extract definitions (each pass re-simplifies every
/// conjunct); a pass after the last one only substitutes.
const MAX_ROUNDS: usize = 64;
/// Node visits across all passes of one call; past it the call gives up and
/// the caller solves the original formula.
const MAX_VISITS: usize = 4_000_000;
/// A compound right-hand side is substituted only when it has at most this
/// many distinct nodes (variables and constants are always substituted).
/// Mirrors ay-dpll's `VAR_SUBST_SCALAR_REPLACEMENT_NODE_LIMIT` rationale:
/// substituting large terms into many occurrences grows the formula.
const MAX_DEF_RHS_NODES: usize = 32;
/// A variable mentioned by at most this many conjuncts may be replaced by a
/// right-hand side of any size: its own definition plus one use.
const LARGE_DEF_MAX_OCCURRENCES: usize = 2;

/// The outcome of [`solve_eqs`].
#[derive(Debug, Clone)]
pub(crate) struct SolvedEqs {
    /// Equisatisfiable with the input; `Bool(false)` / `Bool(true)` when the
    /// solve decided it.
    pub(crate) residual: ChcExpr,
    /// Eliminated variables with idempotent definitions (no right-hand side
    /// mentions an eliminated variable), in elimination order.
    defs: Vec<(ChcVar, Arc<ChcExpr>)>,
    /// Simplification passes run.
    pub(crate) rounds: usize,
}

impl SolvedEqs {
    /// Number of eliminated variables.
    pub(crate) fn eliminated(&self) -> usize {
        self.defs.len()
    }

    /// Extend `model` (a model of [`Self::residual`]) to every variable of
    /// `original_vars`: residual variables the model lacks and variables that
    /// vanished get the default of their sort, eliminated variables the value
    /// of their definition. Returns `false` when a definition cannot be
    /// evaluated (the caller then treats the check as undecided).
    pub(crate) fn complete_model(
        &self,
        original_vars: &[ChcVar],
        model: &mut FxHashMap<String, SmtValue>,
    ) -> bool {
        let eliminated: FxHashSet<&ChcVar> = self.defs.iter().map(|(v, _)| v).collect();
        let mut free: Vec<ChcVar> = original_vars
            .iter()
            .filter(|v| !eliminated.contains(v))
            .cloned()
            .collect();
        for (_, rhs) in &self.defs {
            free.extend(rhs.vars());
        }
        for v in &free {
            if crate::expr::lookup_model_value(model, v).is_none() {
                let Some(default) = default_value(&v.sort) else {
                    return false;
                };
                model.insert(v.name.clone(), default);
            }
        }
        for (v, rhs) in &self.defs {
            // `evaluate_expr` does Int arithmetic only; a Real definition
            // (`x := y + 1/2`) needs the exact rational evaluator.
            let value = match v.sort {
                ChcSort::Real => {
                    crate::expr::evaluate::eval_real_big(rhs, model).map(SmtValue::Real)
                }
                _ => crate::expr::evaluate_expr(rhs, model),
            };
            let Some(value) = value else {
                return false;
            };
            model.insert(v.name.clone(), value);
        }
        true
    }
}

/// The Search-lane executor pre-pass (`smt::executor_adapter`): `Some` with
/// the solve and the input's variables when `expr` is a pure Bool/Int/Real
/// formula with at least one Real variable, no name at two sorts, and
/// solve-eqs changed it. Integer-only queries are left to the executor's own
/// LIA substitution passes (`--chc-no-search-solve-eqs` disables the pass).
pub(crate) fn for_search_executor(expr: &ChcExpr) -> Option<(SolvedEqs, Vec<ChcVar>)> {
    if !crate::ab_switches::get().search_solve_eqs {
        return None;
    }
    let features = expr.scan_features();
    if features.has_array_ops || features.has_bv || features.has_uf_apps || features.has_dt {
        return None;
    }
    let vars = expr.vars();
    let mut has_real = false;
    {
        let mut names: FxHashSet<&str> = FxHashSet::default();
        for v in &vars {
            match v.sort {
                ChcSort::Real => has_real = true,
                ChcSort::Bool | ChcSort::Int => {}
                _ => return None,
            }
            if !names.insert(v.name.as_str()) {
                return None;
            }
        }
    }
    if !has_real {
        return None;
    }
    let solved = solve_eqs_with(expr, &FxHashSet::default(), Reach::Plain)?;
    Some((solved, vars))
}

/// `x = rhs` as a residual conjunct (`x` / `¬x` for a Bool constant).
fn definition_equality(x: &ChcVar, rhs: &Arc<ChcExpr>) -> Arc<ChcExpr> {
    let var = Arc::new(ChcExpr::Var(x.clone()));
    match rhs.as_ref() {
        ChcExpr::Bool(true) => var,
        ChcExpr::Bool(false) => Arc::new(ChcExpr::Op(ChcOp::Not, vec![var])),
        _ => Arc::new(ChcExpr::Op(ChcOp::Eq, vec![var, Arc::clone(rhs)])),
    }
}

fn default_value(sort: &ChcSort) -> Option<SmtValue> {
    match sort {
        ChcSort::Bool => Some(SmtValue::Bool(false)),
        ChcSort::Int => Some(SmtValue::Int(0)),
        ChcSort::Real => Some(SmtValue::Real(BigRational::zero())),
        _ => None,
    }
}

/// Which definitions [`solve_eqs_with`] extracts.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum Reach {
    /// `x = t` with a small right-hand side only: the Search-lane pre-pass.
    /// A conditional or large right-hand side moves case splits into the
    /// arithmetic terms the executor then has to lift (approx_hybrid.6.c's
    /// k = 1 base check: SAT in 2.4 s plain, undecided after 5 s + 12 s with
    /// them).
    Plain,
    /// Also `ite(c, x = a, x = b)` as `x = ite(c, a, b)`, and right-hand
    /// sides of any size for a variable at most
    /// [`LARGE_DEF_MAX_OCCURRENCES`] conjuncts mention: the interpolation cut
    /// transfer, which wants every local variable gone.
    Full,
}

/// [`solve_eqs_with`] at [`Reach::Full`].
pub(crate) fn solve_eqs(expr: &ChcExpr, protected: &FxHashSet<String>) -> Option<SolvedEqs> {
    solve_eqs_with(expr, protected, Reach::Full)
}

/// Solve the top-level equalities of `expr`. A variable named in `protected`
/// is substituted like any other but not eliminated: its definition stays in
/// the residual as an equality (so the residual keeps every protected
/// variable's constraints — what an interpolation partition needs for its
/// shared variables). `None` when nothing was substituted or folded, or when
/// the visit budget ran out — the caller then solves `expr` as given.
pub(crate) fn solve_eqs_with(
    expr: &ChcExpr,
    protected: &FxHashSet<String>,
    reach: Reach,
) -> Option<SolvedEqs> {
    let full = reach == Reach::Full;
    let mut state = State {
        defs: FxHashMap::default(),
        order: Vec::new(),
        users: FxHashMap::default(),
        visits: 0,
        protected,
    };
    let root = Arc::new(expr.clone());
    let mut conjuncts = Vec::new();
    flatten_into(&root, &mut conjuncts, &mut FxHashSet::default());
    let mut changed = rejoin_equality_pairs(&mut conjuncts) > 0;
    let mut passes = 0;
    // Each pass simplifies every conjunct under the current definitions and
    // extracts definitions from the result right away, so an unrolling listed
    // in order (init, T@0, T@1, …) collapses in one pass: the init units
    // select a disjunct of T@0, whose frame equalities select one of T@1, …
    // A definition found mid-pass may leave earlier (memoised) conjuncts
    // unsubstituted; the loop ends only after a pass that found none, so the
    // residual is fully substituted.
    loop {
        passes += 1;
        let extract = passes <= MAX_ROUNDS;
        let mut simp = Simplifier::default();
        let mut next = Vec::with_capacity(conjuncts.len());
        let mut seen = FxHashSet::default();
        let mut added = 0usize;
        // Conjunct counts per variable, computed on the first large
        // right-hand side of the pass (see `LARGE_DEF_MAX_OCCURRENCES`).
        let mut occurrences: Option<FxHashMap<ChcVar, usize>> = None;
        for c in &conjuncts {
            let s = simp.simp(&state.defs, &mut state.visits, c, 0)?;
            changed |= !Arc::ptr_eq(&s, c);
            let first = next.len();
            flatten_into(&s, &mut next, &mut seen);
            if !extract {
                continue;
            }
            for part in &next[first..] {
                let mut candidates = definition_candidates(part, full);
                // Eliminate a local variable before substituting a protected one.
                candidates.sort_by_key(|(x, _)| state.protected.contains(&x.name));
                for (x, t) in candidates {
                    let rare = |occ: &mut Option<FxHashMap<ChcVar, usize>>| {
                        occ.get_or_insert_with(|| occurrence_counts(&conjuncts))
                            .get(&x)
                            .map_or(true, |&n| n <= LARGE_DEF_MAX_OCCURRENCES)
                    };
                    let large_ok = full
                        && !state.protected.contains(&x.name)
                        && !is_substitutable(&t, &x.sort)
                        && rare(&mut occurrences);
                    if state.try_add_def(x, t, large_ok)? {
                        added += 1;
                    }
                }
            }
        }
        conjuncts = next;
        if contains_false(&conjuncts) {
            return state.finish(ChcExpr::Bool(false), passes);
        }
        if added == 0 {
            break;
        }
    }
    if !changed && state.order.is_empty() {
        return None;
    }
    let residual = match conjuncts.len() {
        0 => ChcExpr::Bool(true),
        1 => conjuncts[0].as_ref().clone(),
        _ => ChcExpr::Op(ChcOp::And, conjuncts),
    };
    state.finish(residual, passes)
}

fn contains_false(conjuncts: &[Arc<ChcExpr>]) -> bool {
    conjuncts
        .iter()
        .any(|c| matches!(c.as_ref(), ChcExpr::Bool(false)))
}

/// Push the conjuncts of `e` (flattening nested `and`, dropping `true` and
/// repeated nodes — a shared `and` is expanded once, not once per path).
/// `seen` holds the nodes already flattened into `out`.
fn flatten_into(
    e: &Arc<ChcExpr>,
    out: &mut Vec<Arc<ChcExpr>>,
    seen: &mut FxHashSet<*const ChcExpr>,
) {
    let mut stack = vec![Arc::clone(e)];
    while let Some(e) = stack.pop() {
        if !seen.insert(Arc::as_ptr(&e)) {
            continue;
        }
        match e.as_ref() {
            ChcExpr::Op(ChcOp::And, args) => {
                for a in args.iter().rev() {
                    stack.push(Arc::clone(a));
                }
            }
            ChcExpr::Bool(true) => {}
            _ => out.push(e),
        }
    }
}

/// For each variable, the number of conjuncts that mention it.
fn occurrence_counts(conjuncts: &[Arc<ChcExpr>]) -> FxHashMap<ChcVar, usize> {
    let mut counts: FxHashMap<ChcVar, usize> = FxHashMap::default();
    for c in conjuncts {
        for v in c.vars() {
            *counts.entry(v).or_default() += 1;
        }
    }
    counts
}

/// `x` and `t` when `e` is `x = t` or `t = x` for a variable `x`.
fn var_equation(e: &ChcExpr) -> Option<(&ChcVar, &Arc<ChcExpr>)> {
    match e {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(x), _) => Some((x, &args[1])),
                (_, ChcExpr::Var(y)) => Some((y, &args[0])),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Definitions a top-level conjunct offers, most preferred first.
/// `conditional`: also read `ite(c, x = a, x = b)` ([`Reach::Full`]).
fn definition_candidates(c: &ChcExpr, conditional: bool) -> Vec<(ChcVar, Arc<ChcExpr>)> {
    match c {
        // `ite(c, x = a, x = b)` is `x = ite(c, a, b)` (a conditional
        // assignment; z3's solve-eqs reads it the same way).
        ChcExpr::Op(ChcOp::Ite, args) if conditional && args.len() == 3 => {
            match (var_equation(&args[1]), var_equation(&args[2])) {
                (Some((x, a)), Some((y, b))) if x == y => vec![(
                    x.clone(),
                    Arc::new(ChcExpr::Op(
                        ChcOp::Ite,
                        vec![Arc::clone(&args[0]), Arc::clone(a), Arc::clone(b)],
                    )),
                )],
                _ => Vec::new(),
            }
        }
        ChcExpr::Var(v) if v.sort == ChcSort::Bool => {
            vec![(v.clone(), Arc::new(ChcExpr::Bool(true)))]
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => match args[0].as_ref() {
            ChcExpr::Var(v) if v.sort == ChcSort::Bool => {
                vec![(v.clone(), Arc::new(ChcExpr::Bool(false)))]
            }
            _ => Vec::new(),
        },
        ChcExpr::Op(ChcOp::Eq | ChcOp::Iff, args) if args.len() == 2 => {
            let mut out = Vec::with_capacity(2);
            if let ChcExpr::Var(x) = args[0].as_ref() {
                out.push((x.clone(), Arc::clone(&args[1])));
            }
            if let ChcExpr::Var(y) = args[1].as_ref() {
                out.push((y.clone(), Arc::clone(&args[0])));
            }
            out
        }
        _ => Vec::new(),
    }
}

struct State<'p> {
    /// Idempotent definitions.
    defs: FxHashMap<ChcVar, Arc<ChcExpr>>,
    order: Vec<ChcVar>,
    /// For each variable, the defined variables whose right-hand side
    /// mentions it (kept so a new definition can be pushed into them).
    users: FxHashMap<ChcVar, Vec<ChcVar>>,
    visits: usize,
    protected: &'p FxHashSet<String>,
}

impl State<'_> {
    /// `Some(true)` when `x := t` was added, `Some(false)` when refused,
    /// `None` when the visit budget ran out.
    ///
    /// `large_ok`: `x` occurs in at most [`LARGE_DEF_MAX_OCCURRENCES`]
    /// conjuncts, so a right-hand side of any size may replace it (the
    /// substitution shares the right-hand side's DAG; a variable only its own
    /// definition mentions just disappears).
    fn try_add_def(&mut self, x: ChcVar, t: Arc<ChcExpr>, large_ok: bool) -> Option<bool> {
        if self.defs.contains_key(&x) {
            return Some(false);
        }
        if !matches!(x.sort, ChcSort::Bool | ChcSort::Int | ChcSort::Real) {
            return Some(false);
        }
        let t = Simplifier::default().simp(&self.defs, &mut self.visits, &t, 0)?;
        if !(is_substitutable(&t, &x.sort) || large_ok && is_scalar_term(&t, &x.sort)) {
            return Some(false);
        }
        let t_vars = t.vars();
        if t_vars.contains(&x) {
            return Some(false);
        }
        // Keep the map idempotent: push `x := t` into every definition that
        // mentions `x`.
        if let Some(users) = self.users.remove(&x) {
            let single: FxHashMap<ChcVar, Arc<ChcExpr>> =
                std::iter::once((x.clone(), Arc::clone(&t))).collect();
            for y in users {
                let Some(old) = self.defs.get(&y).cloned() else {
                    continue;
                };
                let new = Simplifier::default().simp(&single, &mut self.visits, &old, 0)?;
                for v in &t_vars {
                    self.users.entry(v.clone()).or_default().push(y.clone());
                }
                self.defs.insert(y, new);
            }
        }
        for v in &t_vars {
            self.users.entry(v.clone()).or_default().push(x.clone());
        }
        self.defs.insert(x.clone(), t);
        self.order.push(x);
        Some(true)
    }

    fn finish(self, residual: ChcExpr, rounds: usize) -> Option<SolvedEqs> {
        let mut defs = Vec::with_capacity(self.order.len());
        let mut kept: Vec<Arc<ChcExpr>> = Vec::new();
        for v in self.order {
            let Some(rhs) = self.defs.get(&v).cloned() else {
                continue;
            };
            if self.protected.contains(&v.name) {
                kept.push(definition_equality(&v, &rhs));
            } else {
                defs.push((v, rhs));
            }
        }
        let residual = if kept.is_empty() || matches!(residual, ChcExpr::Bool(false)) {
            residual
        } else {
            let mut conjuncts = Vec::with_capacity(kept.len() + 1);
            flatten_into(
                &Arc::new(residual),
                &mut conjuncts,
                &mut FxHashSet::default(),
            );
            conjuncts.extend(kept);
            match conjuncts.len() {
                1 => conjuncts[0].as_ref().clone(),
                _ => ChcExpr::Op(ChcOp::And, conjuncts),
            }
        };
        Some(SolvedEqs {
            residual,
            defs,
            rounds,
        })
    }
}

#[cfg(test)]
mod random_tests;
#[cfg(test)]
mod tests;
