// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Forward+backward interval propagation over integer CHC systems (WORD-BV #8).
//!
//! Port of the idea behind Eldarica's `IntervalPropagator` (and the FMCAD'18
//! "lazy reduction" bounds-first philosophy): after `BvToIntAbstractor`
//! translates a BV system into integer arithmetic with `mod 2^w` wraparound
//! casts, this pass
//!
//! 1. runs a FORWARD interval fixpoint across clauses (per-predicate-argument
//!    `[lo, hi]` bounds, widening after [`WIDENING_THRESHOLD`] unstable joins),
//! 2. verifies the resulting candidate interval invariant INDUCTIVELY with an
//!    SMT check per clause (fail-closed: bounds that do not verify are
//!    dropped),
//! 3. strengthens each clause's constraint with the verified bounds of its
//!    body-predicate arguments (BACKWARD/local direction: bounds flow from the
//!    predicates and the clause constraint to every subterm), and
//! 4. discharges `t mod m` casts: whenever the clause context SMT-implies
//!    `0 <= t < m`, the cast is rewritten to `t` and the implied bound atoms
//!    are conjoined so the rewrite is a per-clause equivalence.
//!
//! # Soundness (G1)
//!
//! Every step is gated by an SMT proof obligation that fails closed:
//!
//! * The interval invariant is only used after passing a per-clause inductive
//!   check (`body constraint ∧ body bounds ⇒ head bounds` must be VALID; a
//!   Sat/Unknown answer drops the offending predicate's bounds entirely and
//!   re-verifies the remainder).
//! * Each `mod` discharge requires a per-occurrence validity proof
//!   (`context ⇒ 0 <= t < m` must be UNSAT-certified on its negation); on
//!   Unknown the cast is kept.
//!
//! Given the verified invariant `I`, each transformed clause is equivalent to
//! its original modulo `I`: strengthening bodies with `I`-atoms and replacing
//! `t mod m` by `t` (with the proven bound atoms conjoined) is implied in both
//! directions. Consequently:
//!
//! * UNSAFE witnesses transfer verbatim (a derivation through a strengthened
//!   clause satisfies the original clause) — `translate_invalidity` is the
//!   identity.
//! * SAFE models are corrected by conjoining the interval atoms onto every
//!   predicate interpretation (`translate_validity`), after which they satisfy
//!   the original clauses. The final `verify_model_per_rule` gate on the
//!   ORIGINAL problem remains in force downstream.
//!
//! Kill-switch: `AY_CHC_DISABLE_WORD_BV=1` (shared with the lazy bitwise
//! bounds in `bv_to_int`).

use std::time::Duration;
// The workspace-wide monotonic clock shim (#wasm port): byte-identical to
// `std::time::Instant` on native targets, host-clock-backed on wasm32 (raw
// `std::time::Instant` panics there and breaks the wasm build).
use ay_core::time::Instant;

use num_bigint::BigInt;
use num_traits::{One, Zero};

use crate::smt::{SmtContext, SmtResult};
use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause,
    InvariantModel, PredicateId, PredicateInterpretation,
};
use ay_core::kani_compat::DetHashMap as FxHashMap;

use super::{
    BackTranslator, IdentityBackTranslator, InvalidityWitness, TransformMemoryReport,
    TransformObligation, TransformationResult, Transformer, ValidityWitness,
};

/// Widening threshold: after this many unstable joins on one bound of one
/// predicate argument, that bound is widened to ±∞ (Eldarica default).
const WIDENING_THRESHOLD: u32 = 5;

/// Cap on forward fixpoint rounds (safety net; widening guarantees fast
/// convergence in practice).
const MAX_FIXPOINT_ROUNDS: usize = 64;

/// Per-SMT-query timeout for invariant verification / mod discharge.
const QUERY_TIMEOUT: Duration = Duration::from_millis(600);

/// Total wall budget for the whole pass (analysis + SMT checks).
const PASS_BUDGET: Duration = Duration::from_secs(8);

/// Skip the pass on systems larger than this (SMT cost scales with clauses).
const MAX_CLAUSES: usize = 300;

/// Iterations of the collect-check-rewrite loop per clause (nested mods
/// become dischargeable only after their inner casts are discharged).
const MAX_REWRITE_ROUNDS: usize = 3;

// ── Interval domain ────────────────────────────────────────────────────────

/// A (possibly half-open) integer interval. `None` = unbounded on that side.
#[derive(Clone, Debug, PartialEq, Eq)]
struct Interval {
    lo: Option<BigInt>,
    hi: Option<BigInt>,
}

impl Interval {
    fn top() -> Self {
        Self { lo: None, hi: None }
    }

    fn constant(v: BigInt) -> Self {
        Self {
            lo: Some(v.clone()),
            hi: Some(v),
        }
    }

    fn is_top(&self) -> bool {
        self.lo.is_none() && self.hi.is_none()
    }

    /// Least upper bound (interval hull).
    fn join(&self, other: &Self) -> Self {
        let lo = match (&self.lo, &other.lo) {
            (Some(a), Some(b)) => Some(a.min(b).clone()),
            _ => None,
        };
        let hi = match (&self.hi, &other.hi) {
            (Some(a), Some(b)) => Some(a.max(b).clone()),
            _ => None,
        };
        Self { lo, hi }
    }

    /// Greatest lower bound (intersection). May produce an empty interval
    /// (lo > hi); callers treat that as "infeasible context" and keep going —
    /// the SMT gate is the source of truth.
    fn meet(&self, other: &Self) -> Self {
        let lo = match (&self.lo, &other.lo) {
            (Some(a), Some(b)) => Some(a.max(b).clone()),
            (Some(a), None) => Some(a.clone()),
            (None, b) => b.clone(),
        };
        let hi = match (&self.hi, &other.hi) {
            (Some(a), Some(b)) => Some(a.min(b).clone()),
            (Some(a), None) => Some(a.clone()),
            (None, b) => b.clone(),
        };
        Self { lo, hi }
    }

    fn add(&self, other: &Self) -> Self {
        Self {
            lo: opt_add(&self.lo, &other.lo),
            hi: opt_add(&self.hi, &other.hi),
        }
    }

    fn sub(&self, other: &Self) -> Self {
        Self {
            lo: opt_sub(&self.lo, &other.hi),
            hi: opt_sub(&self.hi, &other.lo),
        }
    }

    fn neg(&self) -> Self {
        Self {
            lo: self.hi.as_ref().map(|v| -v),
            hi: self.lo.as_ref().map(|v| -v),
        }
    }

    fn mul(&self, other: &Self) -> Self {
        // Only fully bounded products are tracked; anything else is top.
        match (&self.lo, &self.hi, &other.lo, &other.hi) {
            (Some(a), Some(b), Some(c), Some(d)) => {
                let products = [a * c, a * d, b * c, b * d];
                let lo = products.iter().min().cloned();
                let hi = products.iter().max().cloned();
                Self { lo, hi }
            }
            _ => Self::top(),
        }
    }

    /// Euclidean `mod` with a positive constant modulus: result ∈ [0, m-1],
    /// or the operand interval itself when it is already within range.
    fn mod_const(&self, m: &BigInt) -> Self {
        if let (Some(lo), Some(hi)) = (&self.lo, &self.hi) {
            if lo.sign() != num_bigint::Sign::Minus && hi < m {
                return self.clone();
            }
        }
        Self {
            lo: Some(BigInt::zero()),
            hi: Some(m - BigInt::one()),
        }
    }

    /// Division by a positive constant, tracked only for non-negative
    /// operands (where truncating and flooring division agree).
    fn div_const(&self, d: &BigInt) -> Self {
        match (&self.lo, &self.hi) {
            (Some(lo), Some(hi)) if lo.sign() != num_bigint::Sign::Minus => Self {
                lo: Some(lo / d),
                hi: Some(hi / d),
            },
            _ => Self::top(),
        }
    }
}

fn opt_add(a: &Option<BigInt>, b: &Option<BigInt>) -> Option<BigInt> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a + b),
        _ => None,
    }
}

fn opt_sub(a: &Option<BigInt>, b: &Option<BigInt>) -> Option<BigInt> {
    match (a, b) {
        (Some(a), Some(b)) => Some(a - b),
        _ => None,
    }
}

/// Fold a constant integer expression (including the `2^32 * 2^(w-32)` pow2
/// trees that `bv_to_int::ops::int_pow2` emits) into a `BigInt`.
fn const_bigint(expr: &ChcExpr) -> Option<BigInt> {
    match expr {
        ChcExpr::Int(v) => Some(BigInt::from(*v)),
        ChcExpr::Op(ChcOp::Add, args) => args
            .iter()
            .try_fold(BigInt::zero(), |acc, a| Some(acc + const_bigint(a)?)),
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut it = args.iter();
            let first = const_bigint(it.next()?)?;
            it.try_fold(first, |acc, a| Some(acc - const_bigint(a)?))
        }
        ChcExpr::Op(ChcOp::Mul, args) => args
            .iter()
            .try_fold(BigInt::one(), |acc, a| Some(acc * const_bigint(a)?)),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => Some(-const_bigint(&args[0])?),
        _ => None,
    }
}

// ── Per-clause environment ─────────────────────────────────────────────────

type VarEnv = FxHashMap<ChcVar, Interval>;
type PredState = FxHashMap<PredicateId, Vec<Interval>>;

fn env_interval(env: &VarEnv, v: &ChcVar) -> Interval {
    env.get(v).cloned().unwrap_or_else(Interval::top)
}

/// Evaluate an integer expression to an interval under `env`.
fn eval_interval(expr: &ChcExpr, env: &VarEnv) -> Interval {
    if let Some(c) = const_bigint(expr) {
        return Interval::constant(c);
    }
    match expr {
        ChcExpr::Var(v) => env_interval(env, v),
        ChcExpr::Op(op, args) => match op {
            ChcOp::Add => args
                .iter()
                .map(|a| eval_interval(a, env))
                .reduce(|a, b| a.add(&b))
                .unwrap_or_else(Interval::top),
            ChcOp::Sub if !args.is_empty() => {
                let mut it = args.iter().map(|a| eval_interval(a, env));
                let first = it.next().expect("non-empty");
                it.fold(first, |acc, b| acc.sub(&b))
            }
            ChcOp::Neg if args.len() == 1 => eval_interval(&args[0], env).neg(),
            ChcOp::Mul => args
                .iter()
                .map(|a| eval_interval(a, env))
                .reduce(|a, b| a.mul(&b))
                .unwrap_or_else(Interval::top),
            ChcOp::Mod if args.len() == 2 => match const_bigint(&args[1]) {
                Some(m) if m.sign() == num_bigint::Sign::Plus => {
                    eval_interval(&args[0], env).mod_const(&m)
                }
                _ => Interval::top(),
            },
            ChcOp::Div if args.len() == 2 => match const_bigint(&args[1]) {
                Some(d) if d.sign() == num_bigint::Sign::Plus => {
                    eval_interval(&args[0], env).div_const(&d)
                }
                _ => Interval::top(),
            },
            ChcOp::Ite if args.len() == 3 => {
                let t = eval_interval(&args[1], env);
                let e = eval_interval(&args[2], env);
                t.join(&e)
            }
            _ => Interval::top(),
        },
        _ => Interval::top(),
    }
}

/// Meet `v`'s environment interval with `itv` (Int-sorted vars only).
fn bound_var(env: &mut VarEnv, v: &ChcVar, itv: Interval) {
    if v.sort != ChcSort::Int {
        return;
    }
    let cur = env_interval(env, v);
    env.insert(v.clone(), cur.meet(&itv));
}

/// Refine `env` with a single comparison atom `var ⋈ expr` / `expr ⋈ var`
/// (the backward/local direction of the propagation).
fn apply_atom(atom: &ChcExpr, env: &mut VarEnv) {
    let ChcExpr::Op(op, args) = atom else { return };
    if args.len() != 2 {
        return;
    }

    match (args[0].as_ref(), args[1].as_ref()) {
        (ChcExpr::Var(v), rhs) => {
            let r = eval_interval(rhs, env);
            let itv = match op {
                ChcOp::Eq => r,
                ChcOp::Le => Interval { lo: None, hi: r.hi },
                ChcOp::Lt => Interval {
                    lo: None,
                    hi: r.hi.map(|h| h - BigInt::one()),
                },
                ChcOp::Ge => Interval { lo: r.lo, hi: None },
                ChcOp::Gt => Interval {
                    lo: r.lo.map(|l| l + BigInt::one()),
                    hi: None,
                },
                _ => return,
            };
            bound_var(env, v, itv);
        }
        (lhs, ChcExpr::Var(v)) => {
            let l = eval_interval(lhs, env);
            let itv = match op {
                ChcOp::Eq => l,
                // c <= v  ⇒  v >= c
                ChcOp::Le => Interval { lo: l.lo, hi: None },
                ChcOp::Lt => Interval {
                    lo: l.lo.map(|l| l + BigInt::one()),
                    hi: None,
                },
                ChcOp::Ge => Interval { lo: None, hi: l.hi },
                ChcOp::Gt => Interval {
                    lo: None,
                    hi: l.hi.map(|h| h - BigInt::one()),
                },
                _ => return,
            };
            bound_var(env, v, itv);
        }
        _ => {}
    }
}

/// Build the per-clause variable environment: body-predicate argument bounds
/// (forward direction) meet constraint-atom bounds (backward direction).
fn clause_env(clause: &HornClause, state: &PredState) -> VarEnv {
    let mut env = VarEnv::default();
    for (pid, args) in &clause.body.predicates {
        if let Some(intervals) = state.get(pid) {
            for (arg, itv) in args.iter().zip(intervals.iter()) {
                if let ChcExpr::Var(v) = arg {
                    if v.sort == ChcSort::Int && !itv.is_top() {
                        let cur = env_interval(&env, v);
                        env.insert(v.clone(), cur.meet(itv));
                    }
                }
            }
        }
    }
    if let Some(constraint) = &clause.body.constraint {
        // Two passes so bounds derived late feed atoms seen early.
        for _ in 0..2 {
            for atom in constraint.conjuncts() {
                apply_atom(atom, &mut env);
            }
        }
    }
    env
}

// ── The transformer ────────────────────────────────────────────────────────

/// Interval propagation + `mod 2^w` discharge pass (WORD-BV item #8).
///
/// Intended to run directly after [`super::BvToIntAbstractor`] in the
/// BvToInt-only preprocessing lanes. A no-op (identity) when disabled via
/// `AY_CHC_DISABLE_WORD_BV`, when the problem is too large, or when nothing
/// can be proven.
pub(crate) struct IntervalPropagator {
    verbose: bool,
    /// Test-only override for the `AY_CHC_DISABLE_WORD_BV` kill-switch so
    /// behavioral tests stay deterministic under parallel test execution.
    enabled_override: Option<bool>,
}

impl IntervalPropagator {
    pub(crate) fn new() -> Self {
        Self {
            verbose: false,
            enabled_override: None,
        }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    #[cfg(test)]
    pub(crate) fn with_enabled_for_test(mut self, enabled: bool) -> Self {
        self.enabled_override = Some(enabled);
        self
    }
}

impl Transformer for IntervalPropagator {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let enabled = self
            .enabled_override
            .unwrap_or_else(|| !super::word_bv_hardening_disabled());
        if !enabled || problem.clauses().is_empty() || problem.clauses().len() > MAX_CLAUSES {
            return identity(problem);
        }
        let deadline = Instant::now() + PASS_BUDGET;

        // Phase 1: forward interval fixpoint with widening (candidates only —
        // correctness comes from the SMT verification in phase 2).
        let candidates = forward_fixpoint(&problem);

        // Phase 2: verify the candidate invariant inductively; fail-closed.
        let verified = verify_invariant(&problem, candidates, deadline, self.verbose);

        // Phase 3: strengthen clauses with verified body bounds and discharge
        // mod casts whose no-wraparound condition is SMT-implied.
        let (transformed, rewrites, strengthened) =
            strengthen_and_discharge(&problem, &verified, deadline, self.verbose);

        if rewrites == 0 && !strengthened {
            return identity(problem);
        }
        if self.verbose {
            safe_eprintln!(
                "IntervalPropagator: {} mod cast(s) discharged, {} predicate(s) with verified bounds",
                rewrites,
                verified.len()
            );
        }
        TransformationResult {
            problem: transformed,
            back_translator: Box::new(IntervalBackTranslator {
                invariants: verified,
                rewrites,
            }),
        }
    }
}

fn identity(problem: ChcProblem) -> TransformationResult {
    TransformationResult {
        problem,
        back_translator: Box::new(IdentityBackTranslator),
    }
}

/// Forward interval analysis: per-predicate-argument `[lo, hi]` candidates.
fn forward_fixpoint(problem: &ChcProblem) -> PredState {
    let mut state = PredState::default();
    // Per (pred, arg): how often each bound moved (for widening).
    let mut lo_moves: FxHashMap<(PredicateId, usize), u32> = FxHashMap::default();
    let mut hi_moves: FxHashMap<(PredicateId, usize), u32> = FxHashMap::default();

    for _round in 0..MAX_FIXPOINT_ROUNDS {
        let mut changed = false;
        for clause in problem.clauses() {
            let ClauseHead::Predicate(pid, head_args) = &clause.head else {
                continue;
            };
            // Bottom semantics: a clause only fires once all its body
            // predicates have been reached.
            if clause
                .body
                .predicates
                .iter()
                .any(|(bpid, _)| !state.contains_key(bpid))
            {
                continue;
            }
            let env = clause_env(clause, &state);
            let new_intervals: Vec<Interval> = head_args
                .iter()
                .map(|arg| {
                    if arg.sort() == ChcSort::Int {
                        eval_interval(arg, &env)
                    } else {
                        Interval::top()
                    }
                })
                .collect();

            match state.get_mut(pid) {
                None => {
                    state.insert(*pid, new_intervals);
                    changed = true;
                }
                Some(current) => {
                    for (i, (cur, new)) in current.iter_mut().zip(new_intervals.iter()).enumerate()
                    {
                        let joined = cur.join(new);
                        if joined != *cur {
                            // Widen the moving side past the threshold.
                            let mut widened = joined;
                            if widened.lo != cur.lo {
                                let n = lo_moves.entry((*pid, i)).or_insert(0);
                                *n += 1;
                                if *n >= WIDENING_THRESHOLD {
                                    widened.lo = None;
                                }
                            }
                            if widened.hi != cur.hi {
                                let n = hi_moves.entry((*pid, i)).or_insert(0);
                                *n += 1;
                                if *n >= WIDENING_THRESHOLD {
                                    widened.hi = None;
                                }
                            }
                            if widened != *cur {
                                *cur = widened;
                                changed = true;
                            }
                        }
                    }
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Keep only informative entries.
    state.retain(|_, intervals| intervals.iter().any(|i| !i.is_top()));
    state
}

/// Bound atoms `lo <= e ∧ e <= hi` for one expression.
fn interval_atoms(expr: &ChcExpr, itv: &Interval) -> Vec<ChcExpr> {
    let mut atoms = Vec::new();
    if let Some(lo) = &itv.lo {
        atoms.push(ChcExpr::ge(expr.clone(), ChcExpr::from_bigint(lo.clone())));
    }
    if let Some(hi) = &itv.hi {
        atoms.push(ChcExpr::le(expr.clone(), ChcExpr::from_bigint(hi.clone())));
    }
    atoms
}

/// All bound atoms for one predicate application under `state`.
fn pred_app_atoms(pid: &PredicateId, args: &[ChcExpr], state: &PredState) -> Vec<ChcExpr> {
    let Some(intervals) = state.get(pid) else {
        return Vec::new();
    };
    args.iter()
        .zip(intervals.iter())
        .filter(|(arg, itv)| !itv.is_top() && arg.sort() == ChcSort::Int)
        .flat_map(|(arg, itv)| interval_atoms(arg, itv))
        .collect()
}

/// SMT-verify the candidate invariant inductively, per clause. Any predicate
/// whose bounds fail (or time out) is dropped entirely and verification
/// restarts, because its atoms may have justified other clauses. Fail-closed:
/// deadline exhaustion drops everything.
fn verify_invariant(
    problem: &ChcProblem,
    mut candidates: PredState,
    deadline: Instant,
    verbose: bool,
) -> PredState {
    let mut smt = SmtContext::new();
    'restart: while !candidates.is_empty() {
        for clause in problem.clauses() {
            let ClauseHead::Predicate(pid, head_args) = &clause.head else {
                continue;
            };
            let head_atoms = pred_app_atoms(pid, head_args, &candidates);
            if head_atoms.is_empty() {
                continue;
            }
            if Instant::now() >= deadline {
                // Fail-closed: partially verified bounds are not trusted.
                if verbose {
                    safe_eprintln!("IntervalPropagator: verification budget exhausted — dropping all interval candidates");
                }
                return PredState::default();
            }
            let mut premise: Vec<ChcExpr> = Vec::new();
            if let Some(c) = &clause.body.constraint {
                premise.push(c.clone());
            }
            for (bpid, bargs) in &clause.body.predicates {
                premise.extend(pred_app_atoms(bpid, bargs, &candidates));
            }
            premise.push(ChcExpr::not(ChcExpr::and_all(head_atoms)));
            let query = ChcExpr::and_all(premise).simplify_constants();
            match smt.check_sat_with_executor_fallback_timeout(&query, QUERY_TIMEOUT) {
                SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
                _ => {
                    if verbose {
                        safe_eprintln!(
                            "IntervalPropagator: bounds for predicate {} failed inductive check — dropped",
                            pid.index()
                        );
                    }
                    candidates.remove(pid);
                    continue 'restart;
                }
            }
        }
        // All clauses verified against the current candidate set.
        return candidates;
    }
    candidates
}

/// Collect all distinct `Mod(t, m)` subterms with a positive constant modulus.
fn collect_mod_terms(expr: &ChcExpr, out: &mut Vec<(ChcExpr, ChcExpr, BigInt)>) {
    crate::expr::maybe_grow_expr_stack(|| {
        if let ChcExpr::Op(op, args) = expr {
            if *op == ChcOp::Mod && args.len() == 2 {
                if let Some(m) = const_bigint(&args[1]) {
                    if m.sign() == num_bigint::Sign::Plus && !out.iter().any(|(t, _, _)| t == expr)
                    {
                        out.push((expr.clone(), args[0].as_ref().clone(), m));
                    }
                }
            }
            for a in args {
                collect_mod_terms(a, out);
            }
        } else if let ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) = expr {
            for a in args {
                collect_mod_terms(a, out);
            }
        } else if let ChcExpr::ConstArray(_, val) = expr {
            collect_mod_terms(val, out);
        }
    })
}

/// Replace every occurrence of `target` (an exact subterm) with `replacement`.
fn replace_subterm(expr: &ChcExpr, target: &ChcExpr, replacement: &ChcExpr) -> ChcExpr {
    crate::expr::maybe_grow_expr_stack(|| {
        if expr == target {
            return replacement.clone();
        }
        match expr {
            ChcExpr::Op(op, args) => ChcExpr::Op(
                *op,
                args.iter()
                    .map(|a| std::sync::Arc::new(replace_subterm(a, target, replacement)))
                    .collect(),
            ),
            ChcExpr::PredicateApp(name, pid, args) => ChcExpr::PredicateApp(
                name.clone(),
                *pid,
                args.iter()
                    .map(|a| std::sync::Arc::new(replace_subterm(a, target, replacement)))
                    .collect(),
            ),
            ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
                name.clone(),
                sort.clone(),
                args.iter()
                    .map(|a| std::sync::Arc::new(replace_subterm(a, target, replacement)))
                    .collect(),
            ),
            ChcExpr::ConstArray(sort, val) => ChcExpr::ConstArray(
                sort.clone(),
                std::sync::Arc::new(replace_subterm(val, target, replacement)),
            ),
            _ => expr.clone(),
        }
    })
}

/// Strengthen clauses with verified body bounds and discharge provably
/// in-range `mod` casts. Returns the transformed problem, the number of
/// discharged casts, and whether any clause was strengthened.
fn strengthen_and_discharge(
    problem: &ChcProblem,
    verified: &PredState,
    deadline: Instant,
    verbose: bool,
) -> (ChcProblem, usize, bool) {
    let mut smt = SmtContext::new();
    let mut result = ChcProblem::new();
    for pred in problem.predicates() {
        result.declare_predicate(&pred.name, pred.arg_sorts.clone());
    }

    let mut total_rewrites = 0usize;
    let mut strengthened = false;

    for clause in problem.clauses() {
        // Verified bounds of body-predicate arguments (Eldarica-style clause
        // strengthening; sound because the invariant is conjoined onto every
        // model at back-translation).
        let mut body_atoms: Vec<ChcExpr> = Vec::new();
        for (bpid, bargs) in &clause.body.predicates {
            body_atoms.extend(pred_app_atoms(bpid, bargs, verified));
        }

        let mut constraint = clause.body.constraint.clone();
        let mut head = clause.head.clone();
        let env = clause_env(clause, verified);

        // Discharge loop: proven bound atoms accumulate into the context so
        // nested casts can be discharged in later rounds.
        let mut proven_bounds: Vec<ChcExpr> = Vec::new();
        for _round in 0..MAX_REWRITE_ROUNDS {
            let mut mods: Vec<(ChcExpr, ChcExpr, BigInt)> = Vec::new();
            if let Some(c) = &constraint {
                collect_mod_terms(c, &mut mods);
            }
            if let ClauseHead::Predicate(_, head_args) = &head {
                for arg in head_args {
                    collect_mod_terms(arg, &mut mods);
                }
            }
            let mut round_rewrites = 0usize;
            for (mod_term, operand, modulus) in mods {
                if Instant::now() >= deadline {
                    break;
                }
                // Cheap interval pre-filter: only pay for SMT when the
                // abstract interpretation already suggests no wraparound.
                let itv = eval_interval(&operand, &env);
                let in_range_hint = matches!(
                    (&itv.lo, &itv.hi),
                    (Some(lo), Some(hi))
                        if lo.sign() != num_bigint::Sign::Minus && *hi < modulus
                );
                if !in_range_hint {
                    continue;
                }
                // SMT gate (fail-closed): context must IMPLY 0 <= t < m.
                let lo_atom = ChcExpr::ge(operand.clone(), ChcExpr::int(0));
                let hi_atom = ChcExpr::lt(operand.clone(), ChcExpr::from_bigint(modulus.clone()));
                let mut ctx: Vec<ChcExpr> = Vec::new();
                if let Some(c) = &constraint {
                    ctx.push(c.clone());
                }
                ctx.extend(body_atoms.iter().cloned());
                ctx.extend(proven_bounds.iter().cloned());
                ctx.push(ChcExpr::not(ChcExpr::and(lo_atom.clone(), hi_atom.clone())));
                let query = ChcExpr::and_all(ctx).simplify_constants();
                match smt.check_sat_with_executor_fallback_timeout(&query, QUERY_TIMEOUT) {
                    SmtResult::Unsat
                    | SmtResult::UnsatWithCore(_)
                    | SmtResult::UnsatWithFarkas(_) => {
                        if verbose {
                            safe_eprintln!(
                                "IntervalPropagator: discharged cast {} (no wraparound SMT-proven)",
                                mod_term
                            );
                        }
                        // Rewrite everywhere in the clause and keep the proven
                        // bounds so the rewrite is an equivalence.
                        constraint = constraint.map(|c| replace_subterm(&c, &mod_term, &operand));
                        if let ClauseHead::Predicate(pid, head_args) = &head {
                            let new_args = head_args
                                .iter()
                                .map(|a| replace_subterm(a, &mod_term, &operand))
                                .collect();
                            head = ClauseHead::Predicate(*pid, new_args);
                        }
                        proven_bounds.push(lo_atom);
                        proven_bounds.push(hi_atom);
                        round_rewrites += 1;
                    }
                    // Sat or Unknown: wraparound not disproven — keep the cast.
                    _ => {}
                }
            }
            total_rewrites += round_rewrites;
            if round_rewrites == 0 {
                break;
            }
        }

        let extra: Vec<ChcExpr> = body_atoms.iter().cloned().chain(proven_bounds).collect();
        if !extra.is_empty() {
            strengthened = true;
            let side = ChcExpr::and_all(extra);
            constraint = Some(match constraint {
                Some(c) => ChcExpr::and(c, side),
                None => side,
            });
        }
        result.add_clause(HornClause::new(
            ClauseBody::new(clause.body.predicates.clone(), constraint),
            head,
        ));
    }

    (result, total_rewrites, strengthened)
}

// ── Back-translation ───────────────────────────────────────────────────────

/// Conjoins the verified interval invariant onto every predicate
/// interpretation of a SAFE model (models of the strengthened system are
/// models of the original system only after this correction); UNSAFE
/// witnesses transfer verbatim.
struct IntervalBackTranslator {
    invariants: PredState,
    rewrites: usize,
}

impl BackTranslator for IntervalBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        let mut result = InvariantModel::new();
        for (pid, interp) in witness.iter() {
            let mut formula = interp.formula.clone();
            if let Some(intervals) = self.invariants.get(pid) {
                let atoms: Vec<ChcExpr> = interp
                    .vars
                    .iter()
                    .zip(intervals.iter())
                    .filter(|(v, itv)| v.sort == ChcSort::Int && !itv.is_top())
                    .flat_map(|(v, itv)| interval_atoms(&ChcExpr::var(v.clone()), itv))
                    .collect();
                if !atoms.is_empty() {
                    formula = ChcExpr::and(formula, ChcExpr::and_all(atoms));
                }
            }
            result.set(
                *pid,
                PredicateInterpretation::new(interp.vars.clone(), formula),
            );
        }
        result.verification_method = witness.verification_method;
        result
    }

    fn translate_invalidity(&self, witness: InvalidityWitness) -> InvalidityWitness {
        // Strengthened clause bodies imply the original bodies, so any
        // derivation in the transformed system replays on the original
        // clauses unchanged.
        witness
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        TransformMemoryReport::with_original_validation_obligations(
            "interval_prop",
            vec![
                TransformObligation::named("interval-invariant-model-conjunction"),
                TransformObligation::named("original-validation-on-safe"),
            ],
        )
        .with_fact("interval-mod-rewrites", self.rewrites.to_string())
        .with_fact(
            "interval-bounded-predicates",
            self.invariants.len().to_string(),
        )
    }
}

#[cfg(test)]
#[path = "interval_propagation_tests.rs"]
mod tests;
