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
//!    `[lo, hi]` bounds, widening after [`WIDENING_THRESHOLD`] unstable joins;
//!    each clause is read with Boolean guard propagation so the guarded-CNF
//!    encodings that compiler front ends emit are not opaque — see
//!    [`MAX_GUARD_ROUNDS`]),
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
/// predicate argument, that bound is widened (Eldarica default) — up the
/// landmark ladder of [`widen_up`] first, and to ±∞ once it is exhausted.
const WIDENING_THRESHOLD: u32 = 5;

/// Cap on forward fixpoint rounds (safety net; widening guarantees fast
/// convergence in practice).
const MAX_FIXPOINT_ROUNDS: usize = 64;

/// Standard post-widening narrowing rounds.
///
/// Widening deliberately forgets a moving bound after a few iterations. A
/// guarded bounded loop can therefore lose its final finite upper bound just
/// before convergence (for example `x = 0; x < 6; x++`). Narrowing intersects
/// the widened post-fixpoint with its abstract one-step image and recovers
/// bounds implied by stable guards. Every recovered candidate still passes
/// the existing per-clause inductiveness check before it is used.
const MAX_NARROWING_ROUNDS: usize = 8;

/// Per-SMT-query timeout for invariant verification / mod discharge.
const QUERY_TIMEOUT: Duration = Duration::from_millis(600);

/// Total wall budget for the whole pass (analysis + SMT checks).
const PASS_BUDGET: Duration = Duration::from_secs(8);

/// Wall budget for the `#[cfg(test)]` fixpoint helpers.
///
/// Matches [`PASS_BUDGET`] rather than being a tighter figure of its own: these
/// helpers run inside a ~4000-test parallel suite, so a budget sized for an idle
/// machine makes the tests that use them fail under load rather than report a
/// real regression. The deterministic [`PASS_WORK_BUDGET`] fuel cap is what
/// actually bounds them.
#[cfg(test)]
const TEST_HELPER_BUDGET: Duration = PASS_BUDGET;

/// Deterministic work cap in addition to the wall-clock deadline.
///
/// Deadline checks happen at every abstract-expression, atom, argument, and
/// clause step. The fuel cap is a second fail-closed guard for clocks with
/// coarse resolution and makes exhaustion behavior deterministic in tests.
const PASS_WORK_BUDGET: usize = 1_000_000;

/// Skip the pass on systems larger than this (SMT cost scales with clauses).
const MAX_CLAUSES: usize = 300;

/// Iterations of the collect-check-rewrite loop per clause (nested mods
/// become dischargeable only after their inner casts are discharged).
const MAX_REWRITE_ROUNDS: usize = 3;

/// Rounds of Boolean guard propagation over one clause constraint.
///
/// Compiler front ends (SeaHorn, and CHC-COMP's `svcomp` families generally)
/// emit guarded CNF: every arithmetic fact sits under guard literals, as in
/// `(or (not g) (= x 0))`, and loop conditions are reified
/// (`(not (= (<= 6 h) g))`). A literal decided in one round unlocks unit
/// propagation in the next — `(or (not d) (and e d))` decides `e` only once
/// `d` is known — so several rounds are needed. A fixed constant (rather than
/// a fixpoint) keeps the pass a bounded analysis.
const MAX_GUARD_ROUNDS: usize = 6;

/// Cap on the widening landmark ladder (see [`widen_up`]); above this the pass
/// falls back to widening straight to ±∞.
const MAX_WIDENING_LANDMARKS: usize = 32;

/// Shared, monotonically decreasing budget for every phase of one pass.
struct PassBudget {
    deadline: Instant,
    work_remaining: usize,
}

impl PassBudget {
    fn new(deadline: Instant, work_remaining: usize) -> Self {
        Self {
            deadline,
            work_remaining,
        }
    }

    /// Charge one bounded unit and reject work once either limit is spent.
    fn checkpoint(&mut self) -> Option<()> {
        if self.work_remaining == 0 || Instant::now() >= self.deadline {
            return None;
        }
        self.work_remaining -= 1;
        Some(())
    }

    /// Remaining timeout for one external solver call.
    fn timeout(&mut self, cap: Duration) -> Option<Duration> {
        self.checkpoint()?;
        let remaining = self.deadline.saturating_duration_since(Instant::now());
        (!remaining.is_zero()).then_some(cap.min(remaining))
    }
}

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
///
/// The outer `Option` is budget exhaustion; the inner one is "not constant".
fn const_bigint_budgeted(expr: &ChcExpr, budget: &mut PassBudget) -> Option<Option<BigInt>> {
    budget.checkpoint()?;
    let value = match expr {
        ChcExpr::Int(v) => Some(BigInt::from(*v)),
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut result = BigInt::zero();
            for arg in args {
                let Some(value) = const_bigint_budgeted(arg, budget)? else {
                    return Some(None);
                };
                result += value;
            }
            Some(result)
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut it = args.iter();
            let Some(mut result) = const_bigint_budgeted(it.next()?, budget)? else {
                return Some(None);
            };
            for arg in it {
                let Some(value) = const_bigint_budgeted(arg, budget)? else {
                    return Some(None);
                };
                result -= value;
            }
            Some(result)
        }
        ChcExpr::Op(ChcOp::Mul, args) => {
            let mut result = BigInt::one();
            for arg in args {
                let Some(value) = const_bigint_budgeted(arg, budget)? else {
                    return Some(None);
                };
                result *= value;
            }
            Some(result)
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            const_bigint_budgeted(&args[0], budget)?.map(|value| -value)
        }
        _ => None,
    };
    Some(value)
}

#[cfg(test)]
fn const_bigint(expr: &ChcExpr) -> Option<BigInt> {
    let mut budget = PassBudget::new(Instant::now() + TEST_HELPER_BUDGET, PASS_WORK_BUDGET);
    const_bigint_budgeted(expr, &mut budget).flatten()
}

// ── Per-clause environment ─────────────────────────────────────────────────

type VarEnv = FxHashMap<ChcVar, Interval>;
type PredState = FxHashMap<PredicateId, Vec<Interval>>;

/// Boolean guard literals decided while reading one clause constraint.
type BoolAssign = FxHashMap<ChcVar, bool>;

fn env_interval(env: &VarEnv, v: &ChcVar) -> Interval {
    env.get(v).cloned().unwrap_or_else(Interval::top)
}

/// Evaluate an integer expression to an interval under `env`.
fn eval_interval(expr: &ChcExpr, env: &VarEnv, budget: &mut PassBudget) -> Option<Interval> {
    budget.checkpoint()?;
    if let Some(c) = const_bigint_budgeted(expr, budget)? {
        return Some(Interval::constant(c));
    }
    let interval = match expr {
        ChcExpr::Var(v) => env_interval(env, v),
        ChcExpr::Op(op, args) => match op {
            ChcOp::Add => {
                let mut result: Option<Interval> = None;
                for arg in args {
                    let incoming = eval_interval(arg, env, budget)?;
                    result = Some(match result {
                        Some(current) => current.add(&incoming),
                        None => incoming,
                    });
                }
                result.unwrap_or_else(Interval::top)
            }
            ChcOp::Sub if !args.is_empty() => {
                let mut it = args.iter();
                let mut result = eval_interval(it.next().expect("non-empty"), env, budget)?;
                for arg in it {
                    result = result.sub(&eval_interval(arg, env, budget)?);
                }
                result
            }
            ChcOp::Neg if args.len() == 1 => eval_interval(&args[0], env, budget)?.neg(),
            ChcOp::Mul => {
                let mut result: Option<Interval> = None;
                for arg in args {
                    let incoming = eval_interval(arg, env, budget)?;
                    result = Some(match result {
                        Some(current) => current.mul(&incoming),
                        None => incoming,
                    });
                }
                result.unwrap_or_else(Interval::top)
            }
            ChcOp::Mod if args.len() == 2 => match const_bigint_budgeted(&args[1], budget)? {
                Some(m) if m.sign() == num_bigint::Sign::Plus => {
                    eval_interval(&args[0], env, budget)?.mod_const(&m)
                }
                _ => Interval::top(),
            },
            ChcOp::Div if args.len() == 2 => match const_bigint_budgeted(&args[1], budget)? {
                Some(d) if d.sign() == num_bigint::Sign::Plus => {
                    eval_interval(&args[0], env, budget)?.div_const(&d)
                }
                _ => Interval::top(),
            },
            ChcOp::Ite if args.len() == 3 => {
                let t = eval_interval(&args[1], env, budget)?;
                let e = eval_interval(&args[2], env, budget)?;
                t.join(&e)
            }
            _ => Interval::top(),
        },
        _ => Interval::top(),
    };
    Some(interval)
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
fn apply_atom(atom: &ChcExpr, env: &mut VarEnv, budget: &mut PassBudget) -> Option<()> {
    budget.checkpoint()?;
    let ChcExpr::Op(op, args) = atom else {
        return Some(());
    };
    if args.len() != 2 {
        return Some(());
    }

    match (args[0].as_ref(), args[1].as_ref()) {
        (ChcExpr::Var(v), rhs) => {
            let r = eval_interval(rhs, env, budget)?;
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
                _ => return Some(()),
            };
            bound_var(env, v, itv);
        }
        (lhs, ChcExpr::Var(v)) => {
            let l = eval_interval(lhs, env, budget)?;
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
                _ => return Some(()),
            };
            bound_var(env, v, itv);
        }
        _ => {}
    }
    Some(())
}

/// Feed a comparison atom to [`apply_atom`] at the requested polarity.
///
/// Under a negative polarity the operator is negated first. `Eq` negates to
/// `Ne`, which is deliberately dropped: `x != c` bounds nothing, so there is
/// no interval fact to record. BV comparisons are dropped for the same reason
/// ([`apply_atom`] only understands the LIA order relations).
fn apply_polar_atom(
    atom: &ChcExpr,
    polarity: bool,
    env: &mut VarEnv,
    budget: &mut PassBudget,
) -> Option<()> {
    budget.checkpoint()?;
    if polarity {
        return apply_atom(atom, env, budget);
    }
    let ChcExpr::Op(op, args) = atom else {
        return Some(());
    };
    let negated = match op.negate_comparison() {
        Some(negated @ (ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge)) => negated,
        _ => return Some(()),
    };
    apply_atom(&ChcExpr::Op(negated, args.clone()), env, budget)
}

/// Three-valued truth of a Boolean formula under the decided guard literals.
///
/// The inner `Option` is `None` for "not determined", which is the answer for
/// EVERY node that is not a Boolean connective or a decided Boolean variable.
/// This must stay conservative: a guessed truth value would let
/// [`assert_unit`] enter a disjunct the clause does not imply, and the derived
/// bound would then be merely plausible rather than valid.
fn truth(expr: &ChcExpr, assign: &BoolAssign, budget: &mut PassBudget) -> Option<Option<bool>> {
    budget.checkpoint()?;
    crate::expr::maybe_grow_expr_stack(|| {
        let value = match expr {
            ChcExpr::Bool(b) => Some(*b),
            ChcExpr::Var(v) if v.sort == ChcSort::Bool => assign.get(v).copied(),
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                truth(&args[0], assign, budget)?.map(|b| !b)
            }
            ChcExpr::Op(ChcOp::And, args) => {
                let mut all_true = true;
                for arg in args {
                    match truth(arg, assign, budget)? {
                        Some(false) => return Some(Some(false)),
                        Some(true) => {}
                        None => all_true = false,
                    }
                }
                all_true.then_some(true)
            }
            ChcExpr::Op(ChcOp::Or, args) => {
                let mut all_false = true;
                for arg in args {
                    match truth(arg, assign, budget)? {
                        Some(true) => return Some(Some(true)),
                        Some(false) => {}
                        None => all_false = false,
                    }
                }
                all_false.then_some(false)
            }
            _ => None,
        };
        Some(value)
    })
}

/// Unit propagation over the arguments of a disjunction (or of a negated
/// conjunction): when every argument but one is `falsifying`, the remaining
/// one is implied at `!falsifying`.
///
/// Bails without asserting anything as soon as the clause is discharged (some
/// argument already satisfies it) or more than one argument is undetermined.
fn assert_unit(
    args: &[std::sync::Arc<ChcExpr>],
    falsifying: bool,
    assign: &mut BoolAssign,
    env: &mut VarEnv,
    budget: &mut PassBudget,
) -> Option<()> {
    let mut undetermined: Option<&std::sync::Arc<ChcExpr>> = None;
    for arg in args {
        budget.checkpoint()?;
        match truth(arg, assign, budget)? {
            // Already satisfied: nothing is implied about the other args.
            Some(value) if value != falsifying => return Some(()),
            Some(_) => {}
            None if undetermined.is_some() => return Some(()),
            None => undetermined = Some(arg),
        }
    }
    match undetermined {
        Some(unit) => assert_formula(unit, !falsifying, assign, env, budget),
        // Every argument falsified: the clause context is contradictory. The
        // SMT gate is the source of truth for that, so record nothing.
        None => Some(()),
    }
}

/// Assert that `expr` holds at `polarity` in the clause context: record
/// decided Boolean guard literals in `assign` and refine `env` with every
/// comparison atom the context implies.
///
/// Only implied facts are recorded. Disjunctions are entered exclusively when
/// unit, reified comparisons exclusively when their Boolean side is decided,
/// and `ite` exclusively when its condition is decided — so nothing here
/// weakens what [`verify_invariant`] must later prove.
fn assert_formula(
    expr: &ChcExpr,
    polarity: bool,
    assign: &mut BoolAssign,
    env: &mut VarEnv,
    budget: &mut PassBudget,
) -> Option<()> {
    budget.checkpoint()?;
    crate::expr::maybe_grow_expr_stack(|| {
        match expr {
            ChcExpr::Var(v) if v.sort == ChcSort::Bool => {
                assign.insert(v.clone(), polarity);
            }
            ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
                assert_formula(&args[0], !polarity, assign, env, budget)?;
            }
            // `and` under a positive polarity / `or` under a negative one:
            // every argument is implied.
            ChcExpr::Op(ChcOp::And, args) if polarity => {
                for arg in args {
                    assert_formula(arg, true, assign, env, budget)?;
                }
            }
            ChcExpr::Op(ChcOp::Or, args) if !polarity => {
                for arg in args {
                    assert_formula(arg, false, assign, env, budget)?;
                }
            }
            // The dual cases are clauses: unit-propagate them.
            ChcExpr::Op(ChcOp::Or, args) => assert_unit(args, false, assign, env, budget)?,
            ChcExpr::Op(ChcOp::And, args) => assert_unit(args, true, assign, env, budget)?,
            // Reified comparison, e.g. the SeaHorn shape
            // `(not (= (<= 6 h) g))` with `g` a decided guard literal: with
            // one side determined the other is forced. Restricted to
            // Boolean-sorted operands so `(= i j)` over Ints stays an
            // interval atom.
            ChcExpr::Op(ChcOp::Eq, args)
                if args.len() == 2
                    && args[0].sort() == ChcSort::Bool
                    && args[1].sort() == ChcSort::Bool =>
            {
                if let Some(known) = truth(&args[0], assign, budget)? {
                    assert_formula(&args[1], known == polarity, assign, env, budget)?;
                } else if let Some(known) = truth(&args[1], assign, budget)? {
                    assert_formula(&args[0], known == polarity, assign, env, budget)?;
                }
            }
            ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
                if let Some(condition) = truth(&args[0], assign, budget)? {
                    let taken = if condition { &args[1] } else { &args[2] };
                    assert_formula(taken, polarity, assign, env, budget)?;
                }
            }
            _ => apply_polar_atom(expr, polarity, env, budget)?,
        }
        Some(())
    })
}

/// Build the per-clause variable environment: body-predicate argument bounds
/// (forward direction) meet constraint-atom bounds (backward direction).
fn clause_env(clause: &HornClause, state: &PredState, budget: &mut PassBudget) -> Option<VarEnv> {
    budget.checkpoint()?;
    let mut env = VarEnv::default();
    for (pid, args) in &clause.body.predicates {
        budget.checkpoint()?;
        if let Some(intervals) = state.get(pid) {
            for (arg, itv) in args.iter().zip(intervals.iter()) {
                budget.checkpoint()?;
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
        // Repeated rounds so guard literals and bounds derived late feed
        // atoms seen early; stops as soon as a round adds nothing.
        let mut assign = BoolAssign::default();
        for _ in 0..MAX_GUARD_ROUNDS {
            budget.checkpoint()?;
            let previous_env = env.clone();
            let previous_assign = assign.clone();
            assert_formula(constraint, true, &mut assign, &mut env, budget)?;
            if env == previous_env && assign == previous_assign {
                break;
            }
        }
    }
    Some(env)
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
    pass_budget: Duration,
    work_budget: usize,
    /// Test-only override for the `AY_CHC_DISABLE_WORD_BV` kill-switch so
    /// behavioral tests stay deterministic under parallel test execution.
    enabled_override: Option<bool>,
}

impl IntervalPropagator {
    pub(crate) fn new() -> Self {
        Self {
            verbose: false,
            pass_budget: PASS_BUDGET,
            work_budget: PASS_WORK_BUDGET,
            enabled_override: None,
        }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }

    /// Bound this pass by the caller's local route budget.
    ///
    /// The global default remains [`PASS_BUDGET`]; specialized candidate
    /// routes can only reduce it. A zero budget makes the transform a no-op.
    pub(crate) fn with_pass_budget(mut self, budget: Duration) -> Self {
        self.pass_budget = budget.min(PASS_BUDGET);
        self
    }

    #[cfg(test)]
    pub(crate) fn with_enabled_for_test(mut self, enabled: bool) -> Self {
        self.enabled_override = Some(enabled);
        self
    }

    #[cfg(test)]
    pub(crate) fn with_work_budget_for_test(mut self, work_budget: usize) -> Self {
        self.work_budget = work_budget;
        self
    }
}

impl Transformer for IntervalPropagator {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let enabled = self
            .enabled_override
            .unwrap_or_else(|| !super::word_bv_hardening_disabled());
        if !enabled
            || self.pass_budget.is_zero()
            || problem.clauses().is_empty()
            || problem.clauses().len() > MAX_CLAUSES
        {
            return identity(problem);
        }
        let deadline = Instant::now() + self.pass_budget;
        let mut budget = PassBudget::new(deadline, self.work_budget);
        if budget.checkpoint().is_none() {
            return identity(problem);
        }

        // Phase 1: forward interval fixpoint with widening (candidates only —
        // correctness comes from the SMT verification in phase 2).
        let Some(mut candidates) = forward_fixpoint_budgeted(&problem, &mut budget) else {
            return identity(problem);
        };
        if narrow_fixpoint(&problem, &mut candidates, &mut budget).is_none() {
            return identity(problem);
        }
        // Only now drop the predicates that carry no information. Narrowing
        // treats "absent from the state" as "not reached" (bottom semantics
        // inherited from the forward pass), so filtering earlier would hide
        // every clause whose body mentions an all-top predicate and turn the
        // abstract image into an under-approximation.
        if retain_informative(&mut candidates, &mut budget).is_none() {
            return identity(problem);
        }

        // Phase 2: verify the candidate invariant inductively; fail-closed.
        let Some(verified) = verify_invariant(&problem, candidates, &mut budget, self.verbose)
        else {
            return identity(problem);
        };

        // Phase 3: strengthen clauses with verified body bounds and discharge
        // mod casts whose no-wraparound condition is SMT-implied.
        let Some((transformed, rewrites, strengthened)) =
            strengthen_and_discharge(&problem, &verified, &mut budget, self.verbose)
        else {
            return identity(problem);
        };
        if budget.checkpoint().is_none() {
            return identity(problem);
        }

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

/// A sorted, deduped ladder of the integer constants occurring in a problem,
/// abandoned wholesale once it would exceed [`MAX_WIDENING_LANDMARKS`].
#[derive(Default)]
struct Landmarks {
    values: Vec<BigInt>,
    overflowed: bool,
}

impl Landmarks {
    fn insert(&mut self, value: BigInt) {
        if self.overflowed {
            return;
        }
        if let Err(at) = self.values.binary_search(&value) {
            if self.values.len() >= MAX_WIDENING_LANDMARKS {
                // Too many distinct constants for this to stay a cheap,
                // bounded ladder: fall back to widening straight to ±∞.
                self.overflowed = true;
                self.values.clear();
                return;
            }
            self.values.insert(at, value);
        }
    }
}

/// Collect the integer constants occurring in `problem` into a widening
/// landmark ladder (see [`widen_up`]).
fn widening_landmarks(problem: &ChcProblem, budget: &mut PassBudget) -> Option<Vec<BigInt>> {
    fn collect(expr: &ChcExpr, out: &mut Landmarks, budget: &mut PassBudget) -> Option<()> {
        budget.checkpoint()?;
        crate::expr::maybe_grow_expr_stack(|| {
            match expr {
                ChcExpr::Int(v) => out.insert(BigInt::from(*v)),
                ChcExpr::Op(_, args)
                | ChcExpr::PredicateApp(_, _, args)
                | ChcExpr::FuncApp(_, _, args) => {
                    for arg in args {
                        collect(arg, out, budget)?;
                    }
                }
                ChcExpr::ConstArray(_, val) => collect(val, out, budget)?,
                _ => {}
            }
            Some(())
        })
    }

    let mut landmarks = Landmarks::default();
    for clause in problem.clauses() {
        budget.checkpoint()?;
        if let Some(constraint) = &clause.body.constraint {
            collect(constraint, &mut landmarks, budget)?;
        }
        for (_, args) in &clause.body.predicates {
            for arg in args {
                collect(arg, &mut landmarks, budget)?;
            }
        }
        if let ClauseHead::Predicate(_, head_args) = &clause.head {
            for arg in head_args {
                collect(arg, &mut landmarks, budget)?;
            }
        }
    }
    Some(landmarks.values)
}

/// Widen an upper bound to the next landmark at or above it.
///
/// Widening to ±∞ on the [`WIDENING_THRESHOLD`]th move forgets the bound of
/// every guarded counting loop just before it converges (`for (i = 0; i < 6;
/// i++)` needs six moves). Climbing the ladder of constants that actually
/// occur in the problem keeps such bounds.
///
/// Termination is unaffected. A bound is only widened when it strictly moved,
/// so the result is strictly above the previous bound and therefore a strictly
/// higher rung; the ladder holds at most [`MAX_WIDENING_LANDMARKS`] rungs, and
/// past its top the bound goes to +∞ exactly as before. Worst case that is
/// [`WIDENING_THRESHOLD`] + [`MAX_WIDENING_LANDMARKS`] + 1 moves per bound,
/// well inside [`MAX_FIXPOINT_ROUNDS`].
fn widen_up(hi: Option<BigInt>, landmarks: &[BigInt]) -> Option<BigInt> {
    let hi = hi?;
    landmarks.iter().find(|landmark| **landmark >= hi).cloned()
}

/// Mirror of [`widen_up`] for a lower bound: the greatest landmark at or below.
fn widen_down(lo: Option<BigInt>, landmarks: &[BigInt]) -> Option<BigInt> {
    let lo = lo?;
    landmarks
        .iter()
        .rev()
        .find(|landmark| **landmark <= lo)
        .cloned()
}

/// Forward interval analysis: per-predicate-argument `[lo, hi]` candidates.
fn forward_fixpoint_budgeted(problem: &ChcProblem, budget: &mut PassBudget) -> Option<PredState> {
    budget.checkpoint()?;
    let mut state = PredState::default();
    // Per (pred, arg): how often each bound moved (for widening).
    let mut lo_moves: FxHashMap<(PredicateId, usize), u32> = FxHashMap::default();
    let mut hi_moves: FxHashMap<(PredicateId, usize), u32> = FxHashMap::default();
    let landmarks = widening_landmarks(problem, budget)?;

    for _round in 0..MAX_FIXPOINT_ROUNDS {
        budget.checkpoint()?;
        let mut changed = false;
        for clause in problem.clauses() {
            budget.checkpoint()?;
            let ClauseHead::Predicate(pid, head_args) = &clause.head else {
                continue;
            };
            // Bottom semantics: a clause only fires once all its body
            // predicates have been reached.
            let mut body_reached = true;
            for (body_pid, _) in &clause.body.predicates {
                budget.checkpoint()?;
                if !state.contains_key(body_pid) {
                    body_reached = false;
                    break;
                }
            }
            if !body_reached {
                continue;
            }
            let env = clause_env(clause, &state, budget)?;
            let mut new_intervals = Vec::with_capacity(head_args.len());
            for arg in head_args {
                budget.checkpoint()?;
                new_intervals.push(if arg.sort() == ChcSort::Int {
                    eval_interval(arg, &env, budget)?
                } else {
                    Interval::top()
                });
            }

            match state.get_mut(pid) {
                None => {
                    state.insert(*pid, new_intervals);
                    changed = true;
                }
                Some(current) => {
                    for (i, (cur, new)) in current.iter_mut().zip(new_intervals.iter()).enumerate()
                    {
                        budget.checkpoint()?;
                        let joined = cur.join(new);
                        if joined != *cur {
                            // Widen the moving side past the threshold.
                            let mut widened = joined;
                            if widened.lo != cur.lo {
                                let n = lo_moves.entry((*pid, i)).or_insert(0);
                                *n += 1;
                                if *n >= WIDENING_THRESHOLD {
                                    widened.lo = widen_down(widened.lo, &landmarks);
                                }
                            }
                            if widened.hi != cur.hi {
                                let n = hi_moves.entry((*pid, i)).or_insert(0);
                                *n += 1;
                                if *n >= WIDENING_THRESHOLD {
                                    widened.hi = widen_up(widened.hi, &landmarks);
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

    Some(state)
}

/// Drop the predicates whose every argument is `top`.
///
/// Run only once the abstract analysis is finished: while the fixpoint and the
/// narrowing are running, membership in the state means "reached", so removing
/// an entry would silently disable every clause whose body mentions it.
fn retain_informative(state: &mut PredState, budget: &mut PassBudget) -> Option<()> {
    budget.checkpoint()?;
    let mut uninformative = Vec::new();
    for (pid, intervals) in state.iter() {
        budget.checkpoint()?;
        let mut keep = false;
        for interval in intervals {
            budget.checkpoint()?;
            keep |= !interval.is_top();
        }
        if !keep {
            uninformative.push(*pid);
        }
    }
    for pid in uninformative {
        budget.checkpoint()?;
        state.remove(&pid);
    }
    Some(())
}

#[cfg(test)]
fn forward_fixpoint(problem: &ChcProblem) -> PredState {
    let mut budget = PassBudget::new(Instant::now() + TEST_HELPER_BUDGET, PASS_WORK_BUDGET);
    forward_fixpoint_budgeted(problem, &mut budget).unwrap_or_default()
}

/// The complete abstract analysis (forward fixpoint + narrowing), exactly as
/// [`IntervalPropagator::transform`] runs it before the informative filter.
#[cfg(test)]
fn narrowed_fixpoint(problem: &ChcProblem) -> PredState {
    let mut budget = PassBudget::new(Instant::now() + TEST_HELPER_BUDGET, PASS_WORK_BUDGET);
    let mut state = forward_fixpoint_budgeted(problem, &mut budget).unwrap_or_default();
    narrow_fixpoint(problem, &mut state, &mut budget).expect("narrowing fits the test budget");
    state
}

/// Refine a widened interval post-fixpoint by standard abstract narrowing.
///
/// `state` is the post-fixpoint produced by [`forward_fixpoint_budgeted`]. For each
/// round we compute the abstract image `F(state)` from a stable snapshot and
/// intersect it with `state`. This can recover a finite bound lost to
/// widening, while never being trusted directly: [`verify_invariant`] checks
/// the complete narrowed candidate against every defining clause and drops a
/// predicate on SAT, Unknown, or timeout.
fn narrow_fixpoint(
    problem: &ChcProblem,
    state: &mut PredState,
    budget: &mut PassBudget,
) -> Option<()> {
    for _round in 0..MAX_NARROWING_ROUNDS {
        budget.checkpoint()?;
        let mut image = PredState::default();
        for clause in problem.clauses() {
            budget.checkpoint()?;
            let ClauseHead::Predicate(pid, head_args) = &clause.head else {
                continue;
            };
            let mut body_reached = true;
            for (body_pid, _) in &clause.body.predicates {
                budget.checkpoint()?;
                if !state.contains_key(body_pid) {
                    body_reached = false;
                    break;
                }
            }
            if !body_reached {
                continue;
            }
            let env = clause_env(clause, state, budget)?;
            let mut head_intervals = Vec::with_capacity(head_args.len());
            for arg in head_args {
                budget.checkpoint()?;
                head_intervals.push(if arg.sort() == ChcSort::Int {
                    eval_interval(arg, &env, budget)?
                } else {
                    Interval::top()
                });
            }
            match image.get_mut(pid) {
                None => {
                    image.insert(*pid, head_intervals);
                }
                Some(current) => {
                    for (slot, incoming) in current.iter_mut().zip(head_intervals) {
                        budget.checkpoint()?;
                        *slot = slot.join(&incoming);
                    }
                }
            }
        }

        let mut changed = false;
        for (pid, current) in state.iter_mut() {
            budget.checkpoint()?;
            let Some(incoming) = image.get(pid) else {
                continue;
            };
            for (slot, next) in current.iter_mut().zip(incoming) {
                budget.checkpoint()?;
                let narrowed = slot.meet(next);
                if narrowed != *slot {
                    *slot = narrowed;
                    changed = true;
                }
            }
        }
        if !changed {
            break;
        }
    }
    Some(())
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
fn pred_app_atoms(
    pid: &PredicateId,
    args: &[ChcExpr],
    state: &PredState,
    budget: &mut PassBudget,
) -> Option<Vec<ChcExpr>> {
    budget.checkpoint()?;
    let Some(intervals) = state.get(pid) else {
        return Some(Vec::new());
    };
    let mut atoms = Vec::new();
    for (arg, interval) in args.iter().zip(intervals) {
        budget.checkpoint()?;
        if !interval.is_top() && arg.sort() == ChcSort::Int {
            atoms.extend(interval_atoms(arg, interval));
        }
    }
    Some(atoms)
}

/// SMT-verify the candidate invariant inductively, per clause. Any predicate
/// whose bounds fail (or time out) is dropped entirely and verification
/// restarts, because its atoms may have justified other clauses. Fail-closed:
/// deadline exhaustion drops everything.
fn verify_invariant(
    problem: &ChcProblem,
    mut candidates: PredState,
    budget: &mut PassBudget,
    verbose: bool,
) -> Option<PredState> {
    budget.checkpoint()?;
    let mut smt = SmtContext::new();
    'restart: while !candidates.is_empty() {
        budget.checkpoint()?;
        for clause in problem.clauses() {
            budget.checkpoint()?;
            let ClauseHead::Predicate(pid, head_args) = &clause.head else {
                continue;
            };
            let head_atoms = pred_app_atoms(pid, head_args, &candidates, budget)?;
            if head_atoms.is_empty() {
                continue;
            }
            let mut premise: Vec<ChcExpr> = Vec::new();
            if let Some(c) = &clause.body.constraint {
                budget.checkpoint()?;
                premise.push(c.clone());
            }
            for (bpid, bargs) in &clause.body.predicates {
                budget.checkpoint()?;
                premise.extend(pred_app_atoms(bpid, bargs, &candidates, budget)?);
            }
            premise.push(ChcExpr::not(ChcExpr::and_all(head_atoms)));
            let query = ChcExpr::and_all(premise);
            let timeout = budget.timeout(QUERY_TIMEOUT)?;
            match smt.check_sat_with_executor_fallback_timeout(&query, timeout) {
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
        return Some(candidates);
    }
    Some(candidates)
}

/// Collect all distinct `Mod(t, m)` subterms with a positive constant modulus.
fn collect_mod_terms(
    expr: &ChcExpr,
    out: &mut Vec<(ChcExpr, ChcExpr, BigInt)>,
    budget: &mut PassBudget,
) -> Option<()> {
    budget.checkpoint()?;
    crate::expr::maybe_grow_expr_stack(|| {
        if let ChcExpr::Op(op, args) = expr {
            if *op == ChcOp::Mod && args.len() == 2 {
                if let Some(m) = const_bigint_budgeted(&args[1], budget)? {
                    let mut duplicate = false;
                    for (term, _, _) in out.iter() {
                        budget.checkpoint()?;
                        if term == expr {
                            duplicate = true;
                            break;
                        }
                    }
                    if m.sign() == num_bigint::Sign::Plus && !duplicate {
                        out.push((expr.clone(), args[0].as_ref().clone(), m));
                    }
                }
            }
            for a in args {
                collect_mod_terms(a, out, budget)?;
            }
        } else if let ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) = expr {
            for a in args {
                collect_mod_terms(a, out, budget)?;
            }
        } else if let ChcExpr::ConstArray(_, val) = expr {
            collect_mod_terms(val, out, budget)?;
        }
        Some(())
    })
}

/// Replace every occurrence of `target` (an exact subterm) with `replacement`.
fn replace_subterm(
    expr: &ChcExpr,
    target: &ChcExpr,
    replacement: &ChcExpr,
    budget: &mut PassBudget,
) -> Option<ChcExpr> {
    budget.checkpoint()?;
    crate::expr::maybe_grow_expr_stack(|| {
        if expr == target {
            return Some(replacement.clone());
        }
        let rebuilt = match expr {
            ChcExpr::Op(op, args) => {
                let mut rebuilt = Vec::with_capacity(args.len());
                for arg in args {
                    rebuilt.push(std::sync::Arc::new(replace_subterm(
                        arg,
                        target,
                        replacement,
                        budget,
                    )?));
                }
                ChcExpr::Op(*op, rebuilt)
            }
            ChcExpr::PredicateApp(name, pid, args) => {
                let mut rebuilt = Vec::with_capacity(args.len());
                for arg in args {
                    rebuilt.push(std::sync::Arc::new(replace_subterm(
                        arg,
                        target,
                        replacement,
                        budget,
                    )?));
                }
                ChcExpr::PredicateApp(name.clone(), *pid, rebuilt)
            }
            ChcExpr::FuncApp(name, sort, args) => {
                let mut rebuilt = Vec::with_capacity(args.len());
                for arg in args {
                    rebuilt.push(std::sync::Arc::new(replace_subterm(
                        arg,
                        target,
                        replacement,
                        budget,
                    )?));
                }
                ChcExpr::FuncApp(name.clone(), sort.clone(), rebuilt)
            }
            ChcExpr::ConstArray(sort, val) => ChcExpr::ConstArray(
                sort.clone(),
                std::sync::Arc::new(replace_subterm(val, target, replacement, budget)?),
            ),
            _ => expr.clone(),
        };
        Some(rebuilt)
    })
}

/// Strengthen clauses with verified body bounds and discharge provably
/// in-range `mod` casts. Returns the transformed problem, the number of
/// discharged casts, and whether any clause was strengthened.
fn strengthen_and_discharge(
    problem: &ChcProblem,
    verified: &PredState,
    budget: &mut PassBudget,
    verbose: bool,
) -> Option<(ChcProblem, usize, bool)> {
    budget.checkpoint()?;
    let mut smt = SmtContext::new();
    let mut result = ChcProblem::new();
    for pred in problem.predicates() {
        budget.checkpoint()?;
        result.declare_predicate(&pred.name, pred.arg_sorts.clone());
    }

    let mut total_rewrites = 0usize;
    let mut strengthened = false;

    for clause in problem.clauses() {
        budget.checkpoint()?;
        // Verified bounds of body-predicate arguments (Eldarica-style clause
        // strengthening; sound because the invariant is conjoined onto every
        // model at back-translation).
        let mut body_atoms: Vec<ChcExpr> = Vec::new();
        for (bpid, bargs) in &clause.body.predicates {
            budget.checkpoint()?;
            body_atoms.extend(pred_app_atoms(bpid, bargs, verified, budget)?);
        }

        let mut constraint = clause.body.constraint.clone();
        let mut head = clause.head.clone();
        let env = clause_env(clause, verified, budget)?;

        // Discharge loop: proven bound atoms accumulate into the context so
        // nested casts can be discharged in later rounds.
        let mut proven_bounds: Vec<ChcExpr> = Vec::new();
        for _round in 0..MAX_REWRITE_ROUNDS {
            budget.checkpoint()?;
            let mut mods: Vec<(ChcExpr, ChcExpr, BigInt)> = Vec::new();
            if let Some(c) = &constraint {
                collect_mod_terms(c, &mut mods, budget)?;
            }
            if let ClauseHead::Predicate(_, head_args) = &head {
                for arg in head_args {
                    collect_mod_terms(arg, &mut mods, budget)?;
                }
            }
            let mut round_rewrites = 0usize;
            for (mod_term, operand, modulus) in mods {
                budget.checkpoint()?;
                // Cheap interval pre-filter: only pay for SMT when the
                // abstract interpretation already suggests no wraparound.
                let itv = eval_interval(&operand, &env, budget)?;
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
                let query = ChcExpr::and_all(ctx);
                let timeout = budget.timeout(QUERY_TIMEOUT)?;
                match smt.check_sat_with_executor_fallback_timeout(&query, timeout) {
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
                        constraint = match constraint {
                            Some(c) => Some(replace_subterm(&c, &mod_term, &operand, budget)?),
                            None => None,
                        };
                        if let ClauseHead::Predicate(pid, head_args) = &head {
                            let mut new_args = Vec::with_capacity(head_args.len());
                            for arg in head_args {
                                new_args.push(replace_subterm(arg, &mod_term, &operand, budget)?);
                            }
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

    Some((result, total_rewrites, strengthened))
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
