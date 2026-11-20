// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Main check_sat implementation (DPLL(T) loop).

mod array_completion;
mod bitblast;
mod cnf;
#[cfg(test)]
mod completeness_diag;
mod executor_first;
mod horn_session;
#[cfg(test)]
mod masked_residue_tests;
mod model_completion;
mod preprocess;
mod query_datatypes;
mod relevancy;
mod scalar_route;
mod support;
mod term_growth;
mod theory_loop;
mod theory_model;

pub(in crate::smt) use model_completion::complete_model_from_bindings;
use model_completion::evaluable_free_vars_missing_from_model;

#[cfg(test)]
pub(in crate::smt) use executor_first::{
    record_executor_session_for_tests, take_executor_session_budgets_for_tests,
};
#[cfg(test)]
pub(crate) use scalar_route::ill_typed_engine_queries;

use super::context::{SmtContext, SmtLane};
use super::lane;
use super::model_verify::verify_sat_model_strict_with_mod_retry;
use super::types::{ModelVerifyResult, SmtResult, SmtValue};
use crate::ChcExpr;
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashMap as HbHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::TermId;
#[cfg(test)]
use std::sync::atomic::{AtomicUsize, Ordering};

enum TermGrowthAction {
    Split {
        split: ay_core::SplitRequest,
    },
    DisequalitySplit {
        model: Vec<bool>,
        split: ay_core::DisequalitySplitRequest,
    },
    ExpressionSplit {
        split: ay_core::ExpressionSplitRequest,
    },
    /// Speculative model-equality atoms requested by the theory
    /// (Phase 3 Fix 4; see `apply_model_equalities`).
    ModelEqualities {
        eqs: Vec<ay_core::ModelEqualityRequest>,
    },
}

/// Preprocessed query state produced by `prepare_check_sat_query`.
///
/// Bundles the results of feature scanning, constant propagation,
/// normalization, bound promotion, and conjunction flattening so that
/// later pipeline stages (CNF, bitblast, theory loop) receive a
/// single coherent input instead of many loose locals.
pub(super) struct PreparedQuery {
    pub(super) features: crate::expr::ExprFeatures,
    pub(super) normalized: ChcExpr,
    pub(super) propagated_model: FxHashMap<String, SmtValue>,
    pub(super) top_conjuncts: Vec<ChcExpr>,
    pub(super) needs_euf: bool,
    // Retained in the bundle so future executor routing can reuse preprocess output.
    pub(super) _needs_executor: bool,
}

/// CNF encoding state produced by `build_check_sat_cnf`.
///
/// Bundles the SAT solver, Tseitin variable mappings, and optional
/// assumption tracking. BV fields are populated by `attach_bv_bitblasting`.
pub(super) struct CnfState {
    pub(super) term_to_var: std::collections::BTreeMap<TermId, u32>,
    pub(super) var_to_term: std::collections::BTreeMap<u32, TermId>,
    pub(super) num_vars: u32,
    pub(super) sat: ay_sat::Solver,
    pub(super) assumptions: Option<Vec<ay_sat::Literal>>,
    pub(super) assumption_map: Option<FxHashMap<ay_sat::Literal, ChcExpr>>,
    pub(super) bv_var_offset: i32,
    pub(super) bv_term_to_bits: HbHashMap<TermId, Vec<i32>>,
    /// Asserted root terms (conjuncts or the single legacy root), used by
    /// don't-care relevancy filtering (Phase 3 Fix 1; relevancy.rs).
    pub(super) roots: Vec<TermId>,
}

/// Trace level for per-check_sat phase diagnostics (inc-10 overstay
/// attribution): `--chc-checksat-trace=1` logs check entry/exit and stage
/// boundaries; `=2` additionally logs every theory-loop phase transition
/// (see `theory_loop.rs`). Cached after first read; zero overhead when unset.
pub(super) fn checksat_trace_level() -> u8 {
    static LEVEL: std::sync::OnceLock<u8> = std::sync::OnceLock::new();
    *LEVEL.get_or_init(|| ay_core::misc_cli_flags().chc_checksat_trace.unwrap_or(0))
}

/// Process-wide count of `check_sat` calls refused because the thread's SMT
/// deadline had already expired (Rung 0, T3 "post-deadline no-op storm").
static POST_DEADLINE_REFUSALS: std::sync::atomic::AtomicUsize =
    std::sync::atomic::AtomicUsize::new(0);

#[cfg(test)]
thread_local! {
    /// This thread's share of [`POST_DEADLINE_REFUSALS`]. The deadline being
    /// refused is thread-local (`smt::deadline`), and so is what a test can
    /// attribute to itself: the process-wide count also moves with every
    /// concurrent test's refusals, which could satisfy a `>= before + n` read.
    static THREAD_POST_DEADLINE_REFUSALS: std::cell::Cell<usize> =
        const { std::cell::Cell::new(0) };
}

/// Number of `check_sat` calls refused post-deadline on THIS thread (tests).
#[cfg(test)]
pub(crate) fn post_deadline_refusals() -> usize {
    THREAD_POST_DEADLINE_REFUSALS.with(std::cell::Cell::get)
}

/// Record (and, with `--chc-checksat-trace >= 2`, print) a post-deadline
/// refusal. Level 3 additionally prints a backtrace for the first eight so the
/// spinning caller can be identified.
fn note_post_deadline_refusal() {
    let n = POST_DEADLINE_REFUSALS.fetch_add(1, std::sync::atomic::Ordering::Relaxed) + 1;
    #[cfg(test)]
    THREAD_POST_DEADLINE_REFUSALS.with(|c| c.set(c.get() + 1));
    let level = checksat_trace_level();
    if level >= 2 {
        safe_eprintln!(
            "[CKSAT-TRACE {:?}] post-deadline check_sat refused (n={n})",
            std::thread::current().id()
        );
        if level >= 3 && n <= 8 {
            safe_eprintln!("{}", std::backtrace::Backtrace::force_capture());
        }
    }
}

/// Default internal DPLL(T) pre-slice before the executor on Search-lane
/// pure Bool/LIA/LRA queries (Rung 0, measured — RUNG0 report §3.3): the
/// internal loop decides the easy majority in 0–3 ms (p90 1–21 ms) where the
/// executor costs 2–61 ms per decided query, so a short internal first try
/// keeps those wins; the executor then gets the whole remaining budget for
/// the queries the internal loop cannot decide (its Unknowns are what the
/// old capped-fallback schedule turned into 21.7 % Unknown). A/B over six
/// instances (`AY_CHC_SEARCH_EXEC_FIRST` = 1 / slice=10 / slice=50 / 0):
/// slice=50 had the fewest Unknown exits and the same throughput as slice=10,
/// pure executor-first the lowest throughput.
const SEARCH_LANE_INTERNAL_PRESLICE: std::time::Duration = std::time::Duration::from_millis(50);

/// Search-lane scheduling policy for pure Bool/LIA/LRA queries (Rung 0).
///
/// Returns `(executor_first, internal_preslice)`. Default: internal DPLL(T)
/// for at most [`SEARCH_LANE_INTERNAL_PRESLICE`], then the executor with the
/// whole remaining per-check budget. Measurement knob
/// `AY_CHC_SEARCH_EXEC_FIRST`: `0` = the pre-Rung-0 internal-first slice
/// schedule, `1` = executor first with no pre-slice, `slice=<ms>` = an
/// explicit pre-slice. Read once per process.
fn search_lane_scalar_policy() -> (bool, Option<std::time::Duration>) {
    static POLICY: std::sync::OnceLock<(bool, Option<std::time::Duration>)> =
        std::sync::OnceLock::new();
    *POLICY.get_or_init(|| match std::env::var("AY_CHC_SEARCH_EXEC_FIRST") {
        Ok(v) if v == "0" => (false, None),
        Ok(v) if v == "1" => (true, None),
        Ok(v) if v.starts_with("slice=") => (
            true,
            v["slice=".len()..]
                .parse::<u64>()
                .ok()
                .filter(|ms| *ms > 0)
                .map(std::time::Duration::from_millis),
        ),
        _ => (true, Some(SEARCH_LANE_INTERNAL_PRESLICE)),
    })
}

/// Legacy per-context executor-fallback cap (#7109), now applied ONLY to a
/// solve that carries no deadline of any kind (no per-check timeout, no
/// thread SMT/solve deadline, no context global deadline): there nothing
/// else bounds the fallbacks, each of which defaults to 5 s. Every
/// deadline-carrying solve bounds them by the deadline instead (Rung 0).
const DEADLINE_FREE_FALLBACK_CAP: u32 = 10;

/// Eligibility scan for the inc-18 EqDiffVar retry: the inc-14 pass only
/// rewrites Int equality atoms, so a query without Int variables cannot have
/// been hurt by it and the retry reserve would be pure waste.
/// `pub(super)`: shared with the persistent executor context (inc-21 port of
/// the same retry).
pub(super) fn expr_mentions_int_var(expr: &ChcExpr) -> bool {
    expr.vars()
        .iter()
        .any(|v| matches!(v.sort, crate::ChcSort::Int))
}

/// Widest BV bit-width that appears anywhere in `expr` — the width of the widest
/// bitvector that ANY solving path (the internal bit-blast or the ay-dpll
/// executor fallback) would blast to ~one SAT variable per bit. Width-GROWING
/// ops (concat, zero/sign-extend, repeat) are resolved through `ChcExpr::sort()`
/// so their exact result width is counted, not just their operands'; every other
/// width source (BV vars, BV literals, BV-sorted `FuncApp` results, and the
/// wide operands of width-shrinking ops like extract) is caught by the leaf
/// recursion. Returns 0 for a BV-free expression.
///
/// Used by the bit-blast width gate (bitblast-bound): a query whose widest BV
/// exceeds `bitblast_max_width()` is refused with Unknown BEFORE either solving
/// path bit-blasts it, avoiding the `PersistentBvCache` cap-clear thrash /
/// executor blow-up that grinds an arbitrary-precision obligation to a SIGKILL.
pub(super) fn max_bv_width(expr: &ChcExpr) -> u32 {
    use crate::ChcOp;
    fn sort_width(sort: &crate::ChcSort) -> u32 {
        match sort {
            crate::ChcSort::BitVec(w) => *w,
            _ => 0,
        }
    }
    // Max is idempotent, so visiting each distinct node once (WP-F F0b) gives
    // exactly the tree walk's answer.
    let mut max_w = 0u32;
    crate::expr::dag::walk_distinct_preorder(expr, |e| {
        match e {
            ChcExpr::BitVec(_, w) => max_w = max_w.max(*w),
            ChcExpr::Var(v) => max_w = max_w.max(sort_width(&v.sort)),
            ChcExpr::FuncApp(_, sort, _) => max_w = max_w.max(sort_width(sort)),
            ChcExpr::Op(op, _) => {
                // Width-growing ops produce a result WIDER than any operand, so
                // the operand recursion alone would miss it — read the exact
                // result width via sort(). (Rare ops, so the sort() cost is
                // negligible; the common case never calls sort().)
                if matches!(
                    op,
                    ChcOp::BvConcat
                        | ChcOp::BvZeroExtend(_)
                        | ChcOp::BvSignExtend(_)
                        | ChcOp::BvRepeat(_)
                ) {
                    max_w = max_w.max(sort_width(&e.sort()));
                }
            }
            _ => {}
        }
        crate::expr::dag::Step::Descend
    });
    max_w
}

/// CUMULATIVE bit-blast cost estimate: the SUM of BV bit-widths over the
/// DISTINCT sub-terms of `expr`. Whereas `max_bv_width` bounds the single widest
/// term, this bounds the TOTAL number of fresh SAT variables the bit-blast mints
/// across ALL BV terms — the quantity that overflows `PersistentBvCache` when
/// MANY moderate-width terms accumulate (no single one wide enough to trip the
/// width gate). Returns 0 for a BV-free expression.
///
/// DEDUP BY POINTER: `ChcExpr` children are `Arc<Self>` (hash-consed; see the
/// `Arc::ptr_eq` fast path on `PartialEq`), so a sub-term shared by many parents
/// would otherwise be summed once per parent — a gross over-count. A visited-set
/// of `Arc`-inner pointers counts each distinct allocation once. (Two separately
/// allocated but structurally-equal sub-terms are counted twice — a bounded
/// OVER-count, which is SOUND: over-abstain → Unknown, never a wrong verdict.)
///
/// Counts the SAME width sources as `max_bv_width` — BV vars, BV literals,
/// BV-sorted `FuncApp` results, and the exact result width of width-GROWING ops
/// (concat / zero-/sign-extend / repeat) via `sort()` — but ADDS instead of
/// taking the max, and never calls the recursive `sort()` on the common ops (so
/// the walk stays O(distinct nodes)). It may UNDER-count intermediate BV-
/// arithmetic result widths; the `attach_bv_bitblasting` backstop
/// (`bitblast_bv_width_and_total`) sums those precisely over the interned term
/// DAG that is actually bit-blasted, so nothing that would thrash slips through.
pub(super) fn total_bv_bits(expr: &ChcExpr) -> u64 {
    use crate::ChcOp;
    fn sort_width(sort: &crate::ChcSort) -> u64 {
        match sort {
            crate::ChcSort::BitVec(w) => u64::from(*w),
            _ => 0,
        }
    }
    let mut total: u64 = 0;
    let mut visited: FxHashSet<*const ChcExpr> = FxHashSet::default();
    let mut stack: Vec<&ChcExpr> = vec![expr];
    while let Some(e) = stack.pop() {
        // Hash-cons dedup: skip a sub-term already summed via another parent.
        if !visited.insert(std::ptr::from_ref::<ChcExpr>(e)) {
            continue;
        }
        match e {
            ChcExpr::BitVec(_, w) => total = total.saturating_add(u64::from(*w)),
            ChcExpr::Var(v) => total = total.saturating_add(sort_width(&v.sort)),
            ChcExpr::FuncApp(_, sort, args) => {
                total = total.saturating_add(sort_width(sort));
                stack.extend(args.iter().map(|a| a.as_ref()));
            }
            ChcExpr::Op(op, args) => {
                if matches!(
                    op,
                    ChcOp::BvConcat
                        | ChcOp::BvZeroExtend(_)
                        | ChcOp::BvSignExtend(_)
                        | ChcOp::BvRepeat(_)
                ) {
                    total = total.saturating_add(sort_width(&e.sort()));
                }
                stack.extend(args.iter().map(|a| a.as_ref()));
            }
            ChcExpr::ConstArray(_, inner) => stack.push(inner.as_ref()),
            ChcExpr::PredicateApp(_, _, args) => {
                stack.extend(args.iter().map(|a| a.as_ref()));
            }
            _ => {}
        }
    }
    total
}

impl SmtContext {
    /// If `expr` would exceed EITHER bit-blast budget — the per-term WIDTH budget
    /// (`max_bv_width` > `bitblast_max_width`) OR the CUMULATIVE total-bits budget
    /// (`total_bv_bits` > `bitblast_max_total_bits`) — log and return `true`: the
    /// caller must refuse the query with Unknown (fail-closed).
    ///
    /// The width bound catches ONE arbitrary-precision term; the total bound
    /// catches MANY moderate-width terms whose bit-blasts accumulate past the
    /// `PersistentBvCache` cap (the observed real mechanism, invisible to the
    /// width bound because no single term is wide).
    ///
    /// SOUNDNESS: abstaining (returning Unknown) is ALWAYS sound — it is never a
    /// false Sat (refutation) nor a false Unsat (proof). It only forfeits
    /// COMPLETENESS on obligations that genuinely need a huge cumulative
    /// bit-blast, which today produce no verdict at all (they grind the whole
    /// verification wave to a watchdog SIGKILL), so Unknown is strictly better.
    /// The budgets (`AY_BITBLAST_MAX_WIDTH` / `AY_BITBLAST_MAX_TOTAL_BITS`, both
    /// defaulting far above any real BV obligation) are chosen so no genuine
    /// small-BV query is ever refused. This gate covers BOTH solving paths
    /// (internal bit-blast and executor fallback); the term-level guard in
    /// `attach_bv_bitblasting` is an additional backstop for callers that reach
    /// the internal loop directly.
    fn bitblast_budget_exceeded(&self, expr: &ChcExpr) -> bool {
        let max_w = max_bv_width(expr);
        let width_budget = bitblast::bitblast_max_width();
        if max_w > width_budget {
            tracing::warn!(
                width = max_w,
                budget = width_budget,
                "check_sat: BV width exceeds bit-blast budget; returning Unknown (fail-closed)"
            );
            if self.verbose || crate::debug_chc_smt_enabled() {
                safe_eprintln!(
                    "[CHC-SMT] check_sat refused: BV width {max_w} exceeds budget {width_budget}; returning Unknown (fail-closed)"
                );
            }
            return true;
        }
        // High-threshold early-out only (model-checker-consumer #43/#46): static bit counts
        // cannot separate legitimate BMC-unrolled CHC queries from thrash
        // accumulations (both count ~1M under pointer dedup; structural dedup
        // fails too — per-depth variable renaming makes unrolled clones
        // genuinely content-distinct, yet they mint far fewer cache entries
        // than a flat accumulation of the same counted size). The DYNAMIC
        // mid-blast abort in `attach_bv_bitblasting` now enforces the true
        // entry cap, so this pre-gate only screens out astronomically-large
        // queries cheaply; everything else is decided by the blast itself.
        // (The former two-stage structural recount was removed as redundant.)
        let total = total_bv_bits(expr);
        let total_budget = bitblast::bitblast_pregate_max_total_bits();
        if total > total_budget {
            tracing::warn!(
                total_bits = total,
                budget = total_budget,
                "check_sat: cumulative BV bit-blast total exceeds budget; returning Unknown (fail-closed)"
            );
            if self.verbose || crate::debug_chc_smt_enabled() {
                safe_eprintln!(
                    "[CHC-SMT] check_sat refused: cumulative BV bits {total} exceed total budget {total_budget}; returning Unknown (fail-closed)"
                );
            }
            return true;
        }
        false
    }
}

#[cfg(test)]
static THEORY_SOLVER_BUILD_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static SAT_MODEL_ITERATION_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static BV_BITBLAST_BUILD_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
static BV_NEW_CLAUSE_COUNT: AtomicUsize = AtomicUsize::new(0);
#[cfg(test)]
thread_local! {
    /// Per THREAD: the looping_id test reads only the demotions of its own
    /// solve. A process-global count also saw the fail-safe demotions of
    /// concurrently running tests (session differential suites), so the
    /// test failed only in the full parallel lib run.
    static INVALID_SAT_MODEL_DEMOTION_COUNT: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
/// #5384 UNSAT replays attempted (SAT-level UNSAT with learned clauses present).
#[cfg(test)]
static UNSAT_REPLAY_COUNT: AtomicUsize = AtomicUsize::new(0);
/// #5384 recoveries taken (the replay came back SAT and replaced the solver).
#[cfg(test)]
static UNSAT_RECOVERY_COUNT: AtomicUsize = AtomicUsize::new(0);

#[cfg(test)]
fn record_theory_solver_build_for_tests() {
    THEORY_SOLVER_BUILD_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[cfg(test)]
fn record_unsat_replay_for_tests() {
    UNSAT_REPLAY_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[cfg(test)]
fn record_unsat_recovery_for_tests() {
    UNSAT_RECOVERY_COUNT.fetch_add(1, Ordering::Relaxed);
}

/// `(replays attempted, recoveries taken)` by the #5384 UNSAT defense since
/// the last `reset_reuse_counters_for_tests`.
#[cfg(test)]
pub(super) fn unsat_replay_counters_for_tests() -> (usize, usize) {
    (
        UNSAT_REPLAY_COUNT.load(Ordering::Relaxed),
        UNSAT_RECOVERY_COUNT.load(Ordering::Relaxed),
    )
}

#[cfg(test)]
fn record_sat_model_iteration_for_tests() {
    SAT_MODEL_ITERATION_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[cfg(test)]
fn record_bv_bitblast_for_tests() {
    BV_BITBLAST_BUILD_COUNT.fetch_add(1, Ordering::Relaxed);
}

#[cfg(test)]
fn record_bv_new_clauses_for_tests(count: usize) {
    BV_NEW_CLAUSE_COUNT.fetch_add(count, Ordering::Relaxed);
}

#[cfg(test)]
pub(super) fn reset_reuse_counters_for_tests() {
    THEORY_SOLVER_BUILD_COUNT.store(0, Ordering::Relaxed);
    SAT_MODEL_ITERATION_COUNT.store(0, Ordering::Relaxed);
    BV_BITBLAST_BUILD_COUNT.store(0, Ordering::Relaxed);
    BV_NEW_CLAUSE_COUNT.store(0, Ordering::Relaxed);
    INVALID_SAT_MODEL_DEMOTION_COUNT.with(|c| c.set(0));
    UNSAT_REPLAY_COUNT.store(0, Ordering::Relaxed);
    UNSAT_RECOVERY_COUNT.store(0, Ordering::Relaxed);
}

/// Count of SAT models that FAILED strict re-verification against the
/// original expression and were demoted to Unknown ("SAT model from ...
/// violates original expression"). A healthy solver produces zero: every
/// model the DPLL(T)+bit-blast lane assembles should satisfy the original
/// expression. Nonzero counts indicate a model-construction bug (e.g. the
/// persistent-BV-cache reuse bug where variables were re-blasted into
/// disconnected bit sets).
#[cfg(test)]
pub(super) fn invalid_sat_model_demotion_count_for_tests() -> usize {
    INVALID_SAT_MODEL_DEMOTION_COUNT.with(std::cell::Cell::get)
}

#[cfg(test)]
pub(super) fn reuse_counters_for_tests() -> (usize, usize) {
    (
        THEORY_SOLVER_BUILD_COUNT.load(Ordering::Relaxed),
        SAT_MODEL_ITERATION_COUNT.load(Ordering::Relaxed),
    )
}

#[cfg(test)]
pub(super) fn bv_new_clause_count_for_tests() -> usize {
    BV_NEW_CLAUSE_COUNT.load(Ordering::Relaxed)
}

#[cfg(test)]
pub(super) fn bv_bitblast_count_for_tests() -> usize {
    BV_BITBLAST_BUILD_COUNT.load(Ordering::Relaxed)
}

#[cfg(test)]
pub(super) fn cached_bv_clause_count_for_tests(ctx: &SmtContext) -> usize {
    ctx.persistent_bv_cache.clauses.len()
}

#[cfg(test)]
pub(super) fn unassignable_free_var_set_signature_for_tests(
    missing: &[(String, crate::ChcSort)],
) -> u64 {
    unassignable_free_var_set_signature(missing)
}

/// Type-appropriate default witness value for a scalar sort, used by the
/// fail-closed model completion below: BitVec→0 of the right width, Int→0,
/// Bool→false, Real→0. `None` for non-scalar sorts (never produced by
/// `evaluable_free_vars_missing_from_model`).
fn default_scalar_smt_value(sort: &crate::ChcSort) -> Option<SmtValue> {
    Some(match sort {
        crate::ChcSort::Bool => SmtValue::Bool(false),
        crate::ChcSort::Int => SmtValue::Int(0),
        crate::ChcSort::Real => SmtValue::Real(num_rational::BigRational::from_integer(
            num_bigint::BigInt::from(0),
        )),
        crate::ChcSort::BitVec(w) => {
            SmtValue::bitvec_from_biguint(num_bigint::BigUint::from(0u8), *w)
        }
        crate::ChcSort::Array(..)
        | crate::ChcSort::Uninterpreted(_)
        | crate::ChcSort::Datatype { .. } => return None,
    })
}

/// Model-completion half of the completion-then-strict-reverify path shared by
/// `sat_or_unknown` and its executor twin (`accept_reparsed_sat_model`):
/// clone `model` and fill in a type-appropriate default for EVERY
/// evaluable-position scalar variable of `exprs` that is missing from it.
///
/// Returns `None` when nothing is missing (the caller keeps its existing
/// Indeterminate handling), otherwise `Some((completed_model, missing))`.
///
/// SOUNDNESS: the completed model is a GUESS and carries no evidence by
/// itself. Callers MUST re-run the strict verifier against the ORIGINAL
/// expression(s) and accept the completed model as a Sat witness ONLY on
/// `ModelVerifyResult::Valid` — anything else must remain Unknown. See the
/// invariant comment at the `sat_or_unknown` call site.
pub(in crate::smt) fn complete_model_with_scalar_defaults<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    model: &FxHashMap<String, SmtValue>,
) -> Option<(FxHashMap<String, SmtValue>, Vec<(String, crate::ChcSort)>)> {
    let exprs: Vec<&ChcExpr> = exprs.into_iter().collect();
    let missing = evaluable_free_vars_missing_from_model(exprs.iter().copied(), model);
    if missing.is_empty() {
        return None;
    }
    let mut completed = model.clone();
    // Equality propagation BEFORE defaults: check_sat preprocessing
    // (`propagate_var_equalities`) eliminates `(= v1 v2)` conjuncts by
    // substitution, and only var=CONST eliminations are transported back into
    // the final model — a var eliminated through a var=var (or evaluable
    // var=term) equality reaches this point missing, and a blind sort default
    // then falsifies the surviving equality conjunct so strict re-verification
    // correctly rejects the completion (the model-checker-consumer `bbN_thr_vK` threading
    // wobble). Reconstruct such bindings exactly: to a fixpoint, for every
    // top-level `(= v t)` / `(= t v)` conjunct whose scalar `v` is missing,
    // insert `v := eval(t)` whenever `t` evaluates concretely under the
    // partial model. This only PROPOSES values — the caller's strict verifier
    // over the ORIGINAL expression(s) remains the sole acceptance authority,
    // so a propagation bug can at worst leave Unknown, never a wrong verdict.
    loop {
        let mut progressed = false;
        for expr in &exprs {
            propagate_equality_definitions(expr, &mut completed, &mut progressed, 0);
        }
        if !progressed {
            break;
        }
    }
    // Type-appropriate defaults only for vars still missing after propagation.
    for (name, sort) in &missing {
        if !completed.contains_key(name) {
            if let Some(value) = default_scalar_smt_value(sort) {
                completed.insert(name.clone(), value);
            }
        }
    }
    Some((completed, missing))
}

/// Fixpoint step of the completion path above: walk top-level `And` conjuncts
/// (the same bounded walk as `ChcExpr::collect_var_var_equalities`) and, for
/// each binary `Eq` conjunct with a missing scalar variable on one side and a
/// concretely-evaluable term on the other, bind the variable to the term's
/// value under the current partial model.
fn propagate_equality_definitions(
    expr: &ChcExpr,
    completed: &mut FxHashMap<String, SmtValue>,
    progressed: &mut bool,
    depth: usize,
) {
    if depth >= crate::expr::MAX_EXPR_RECURSION_DEPTH {
        return;
    }
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(crate::ChcOp::And, args) => {
            for arg in args {
                propagate_equality_definitions(arg, completed, progressed, depth + 1);
            }
        }
        ChcExpr::Op(crate::ChcOp::Eq, args) if args.len() == 2 => {
            for (var_side, term_side) in [(&args[0], &args[1]), (&args[1], &args[0])] {
                if let ChcExpr::Var(var) = var_side.as_ref() {
                    if !completed.contains_key(&var.name) {
                        if let Some(value) = crate::expr::evaluate_expr(term_side, completed) {
                            completed.insert(var.name.clone(), value);
                            *progressed = true;
                        }
                    }
                }
            }
        }
        _ => {}
    });
}

/// Strip a single trailing solver-fresh-id suffix (`_<digits>`) from a variable
/// name so structurally-identical unassignable variables that differ ONLY by a
/// per-solve fresh id collapse to the same normalized key.
///
/// The reported ny-cert grind re-issues the SAME under-assigned model shape
/// carrying a variable like `lincon_lean_undef_field2_f2_f1_f1_196`, where the
/// engine mints a fresh trailing id (`_196`, `_197`, …) on each re-derivation.
/// Without normalization every spin iteration produces a DIFFERENT name set, so
/// the same-signature streak never accumulates and the breaker never trips.
/// Removing ONLY the final `_<digits>` run makes those renamings share a
/// signature while preserving structural identity:
///   * the STRUCTURAL field/lane indices earlier in the name (`field2`, `f2`,
///     `f1`) are retained — only the LAST numeric run is a fresh id, so
///     `a_f1_196` and `a_f2_196` stay distinct (`a_f1` vs `a_f2`);
///   * a name with no trailing `_<digits>` (e.g. `x`, `bb1_cell`) is returned
///     unchanged.
/// Collapsing genuinely-distinct SSA temporaries (`t_1` vs `t_2` → `t`) is
/// harmless: the breaker only accumulates across an UNBROKEN run of missing-var
/// Unknowns, and any DECIDED verdict resets the streak (`note_solve_progress`),
/// so a healthy, progressing solve can never false-trip on the coarser key.
fn strip_fresh_id_suffix(name: &str) -> &str {
    let bytes = name.as_bytes();
    let mut end = bytes.len();
    while end > 0 && bytes[end - 1].is_ascii_digit() {
        end -= 1;
    }
    // Require at least one trailing digit AND a preceding `_` to strip, so a
    // name without a fresh-id suffix (or a bare number) is left untouched.
    if end < bytes.len() && end > 0 && bytes[end - 1] == b'_' {
        &name[..end - 1]
    } else {
        name
    }
}

/// Order-independent, deterministic signature of an unassignable
/// evaluable-position free-variable SET, used by the no-progress circuit breaker
/// (see `crate::smt::context`). Hashing the fresh-id-NORMALIZED variable NAMES
/// (sorted, via [`strip_fresh_id_suffix`]) makes re-issues of the same stuck
/// query — including the ny-cert spin that re-mints a fresh trailing id on each
/// re-derivation — collapse to the same signature so the breaker can detect the
/// no-progress spin. Uses a fixed-seed FNV-1a rather than the process-randomized
/// `DefaultHasher` so the value is stable within a run and independent of
/// iteration order.
fn unassignable_free_var_set_signature(missing: &[(String, crate::ChcSort)]) -> u64 {
    let mut names: Vec<&str> = missing
        .iter()
        .map(|(name, _)| strip_fresh_id_suffix(name.as_str()))
        .collect();
    names.sort_unstable();
    names.dedup();
    let mut hash: u64 = 0xcbf2_9ce4_8422_2325; // FNV-1a offset basis
    for name in names {
        for byte in name.as_bytes() {
            hash ^= u64::from(*byte);
            hash = hash.wrapping_mul(0x0000_0100_0000_01b3); // FNV prime
        }
        // Delimiter so {"ab","c"} and {"a","bc"} do not collide.
        hash ^= 0xff;
        hash = hash.wrapping_mul(0x0000_0100_0000_01b3);
    }
    hash
}

impl SmtContext {
    /// Verify a SAT model against the original expression and return
    /// `Sat(model)` or `Unknown` depending on the verification result.
    ///
    /// Shared by `prepare_check_sat_query` (early exits) and the theory
    /// loop (final model assembly).
    pub(super) fn sat_or_unknown(
        expr: &ChcExpr,
        model: FxHashMap<String, SmtValue>,
        source: &'static str,
    ) -> SmtResult {
        let verify_result = verify_sat_model_strict_with_mod_retry(expr, &model);
        if matches!(verify_result, ModelVerifyResult::Invalid) {
            tracing::warn!(
                "SAT model from {source} violates original expression; returning Unknown"
            );
            #[cfg(test)]
            INVALID_SAT_MODEL_DEMOTION_COUNT.with(|c| c.set(c.get() + 1));
            return SmtResult::Unknown;
        }
        if matches!(verify_result, ModelVerifyResult::Indeterminate) {
            // Indeterminate has two very different causes, split fail-closed
            // (2026-07-08, the development design notes rank 1):
            //
            // 1. A free variable occurring in an EVALUABLE THEORY position is ABSENT
            //    from the model. That is the signature of an upstream abstraction
            //    dropping the variable's defining conjunct — the model then says
            //    NOTHING about whether the expression is satisfiable. Accepting it as
            //    Sat was a verified fail-open: in the model-checker-consumer midpoint repro the
            //    quotient `q = bvudiv(d, 2)` was absent from the model and the
            //    accepted Sat surfaced downstream as a spurious CHC refutation.
            //    First try completing the model with sort defaults and STRICTLY
            //    re-verifying (below); if the completed model does not verify
            //    Valid, return Unknown — callers' executor/portfolio fallbacks
            //    already fire on Unknown, and a genuine Sat re-emerges from a
            //    lane that produces a checkable model.
            //
            // 2. Every evaluable-position variable IS assigned, and Indeterminate
            //    comes only from nodes the strict evaluator cannot interpret
            //    (uninterpreted predicate/function applications — including any
            //    variables occurring ONLY inside their argument lists, which cannot
            //    affect evaluation). The DPLL(T) solve itself decided those atoms,
            //    so the model is trustworthy even though evaluation is incomplete —
            //    the long-standing #4712 behavior, kept.
            // PRECISION (FIX 5, aychc-completeness): BEFORE the scalar-defaults
            // attempt, try to COMPLETE the model by deriving the missing
            // evaluable-position variable(s) from their SSA defining equalities
            // already present in `expr` — the head-arg binding `q = bvudiv(d, 2)`
            // that the DPLL(T)/LIA model left implicit because the divisor term is
            // opaque to the linear solver, so `extract_theory_sat_values` never
            // emitted `q`. A DERIVED value is FORCED by the constraint (never a
            // default), so it also covers models a default would falsify.
            //
            // This adds NO new acceptance channel: a value is filled ONLY when its
            // binding RHS is itself fully evaluable under the current model, and
            // acceptance still requires the SAME strict `Valid` verdict over the
            // ORIGINAL expression — a fully evaluated, concrete satisfying
            // assignment, exactly the witness the top-level `Valid` arm already
            // accepts. Every other outcome falls through — WITH THE ORIGINAL,
            // UNMUTATED `model` — to the scalar-defaults attempt below and then
            // the unchanged fail-closed Unknown. The derivation works on a CLONE:
            // leaking derived entries into `model` on a non-Valid outcome would
            // change the arm's missing-variable discrimination below (a derived
            // value that FALSIFIES the expression must not make the model look
            // "fully assigned" to the trusted-Indeterminate acceptance path).
            {
                let mut derived = model.clone();
                if complete_model_from_bindings(expr, &mut derived)
                    && matches!(
                        verify_sat_model_strict_with_mod_retry(expr, &derived),
                        ModelVerifyResult::Valid
                    )
                {
                    tracing::debug!(
                        "SAT model from {source} completed from SSA defining-equality bindings \
                         and strict-verified Valid against the original expression; accepting \
                         as Sat"
                    );
                    return SmtResult::Sat(derived);
                }
            }
            if let Some((completed, missing)) =
                complete_model_with_scalar_defaults(std::iter::once(expr), &model)
            {
                // Model-completion-then-strict-reverify (2026-07): before
                // demoting to Unknown, extend the model with type-appropriate
                // defaults (BitVec→0, Int→0, Bool→false, Real→0) for every
                // missing evaluable-position scalar and re-run the SAME strict
                // verifier used at the acceptance gate above. When the missing
                // variable is genuinely unconstrained (e.g. an abstraction
                // dropped its defining conjunct but the rest of the expression
                // does not restrict it), the default frequently satisfies the
                // ORIGINAL expression and a sound Sat replaces a lost verdict.
                //
                // SOUNDNESS INVARIANT (non-negotiable): this path may only
                // ever emit Sat-with-verified-witness or Unknown, NEVER Unsat.
                // Acceptance is gated EXCLUSIVELY on the strict verifier
                // evaluating the ORIGINAL `expr` to Bool(true) under the
                // completed model (`ModelVerifyResult::Valid`). Accepting a
                // completed model WITHOUT that re-verification would reopen
                // the under-assigned-model fail-open documented above (case 1:
                // spurious CHC refutation, model-checker-consumer midpoint repro). Invalid
                // AND Indeterminate completions both fall through to Unknown.
                if matches!(
                    verify_sat_model_strict_with_mod_retry(expr, &completed),
                    ModelVerifyResult::Valid
                ) {
                    tracing::debug!(
                        "SAT model from {source} was missing {} evaluable-position scalar \
                         assignment(s); default-completed model strictly verifies against \
                         the original expression; accepting as Sat",
                        missing.len()
                    );
                    return SmtResult::Sat(completed);
                }
                let (first_missing, _) = &missing[0];
                tracing::warn!(
                    "SAT model from {source} is missing an assignment for free variable \
                     `{first_missing}` (in an evaluable theory position) and cannot be verified \
                     against the original expression; default-value completion was attempted \
                     but the completed model did not strictly verify; returning Unknown \
                     instead of accepting as Sat"
                );
                // No-progress circuit breaker: an outer CHC/PDR engine loop
                // (obligation queue, predecessor reachability, generalization,
                // invariant discovery, …) can RE-ISSUE the same — or the
                // same-unassignable-variable-set — query hundreds of times, each
                // paying full DPLL(T) cost only to reach this identical
                // fail-closed Unknown, grinding past the model-checker-consumer wall-clock
                // watchdog to a SIGKILL. Record the no-progress event keyed by
                // the unassignable free-variable set; once it recurs without
                // progress the breaker trips and `check_sat` / `is_cancelled`
                // short-circuit the whole solve to Unknown. SOUNDNESS: this is
                // reached ONLY on the already-fail-closed Unknown path — it never
                // accepts the under-assigned model, so it can only return Unknown
                // sooner, never fabricate a Sat/Unsat/proof.
                let signature = unassignable_free_var_set_signature(&missing);
                if crate::smt::note_unassignable_free_var_no_progress(signature) {
                    tracing::warn!(
                        "ay_chc::smt::check_sat no-progress breaker tripped: the same \
                         unassignable evaluable-position free-variable set (e.g. \
                         `{first_missing}`) has recurred with no progress; short-circuiting the \
                         remainder of this solve to Unknown (fail-closed) instead of re-issuing \
                         the identical query until the wall-clock watchdog SIGKILLs the process"
                    );
                }
                return SmtResult::Unknown;
            }
            tracing::debug!("SAT model verification indeterminate in {source}; accepting as Sat");
        }
        SmtResult::Sat(model)
    }

    pub fn check_sat(&mut self, expr: &ChcExpr) -> SmtResult {
        if crate::run_meter::charge(crate::run_meter::Step::SmtEntry).is_err() {
            return SmtResult::Unknown;
        }
        let _census =
            lane::CensusFrame::enter1(lane::SmtEntry::CheckSat, Some(self.census_lane()), expr);
        // No-progress circuit breaker (fail-closed): once the solve has been
        // observed spinning on the same unassignable evaluable-position
        // free-variable set (see `sat_or_unknown`), short-circuit every further
        // check_sat to Unknown rather than paying full DPLL(T) cost to reach the
        // identical fail-closed Unknown. Always sound (Unknown). This is the
        // cheap read half of the breaker; `is_cancelled` carries the same signal
        // into the engine's own loop-termination checks.
        if crate::smt::no_progress_breaker_tripped() {
            return SmtResult::Unknown;
        }
        // Rung 0 (T3): an expired lane deadline can only yield Unknown — refuse
        // before any classification work and count it, so the engine loops
        // (`is_cancelled` now polls the same deadline) stop re-issuing queries.
        if self.deadlines_expired() {
            note_post_deadline_refusal();
            return SmtResult::Unknown;
        }
        // Per-engine term memory budget guard (#8600).
        if self.exact_term_memory_exceeded() {
            return SmtResult::Unknown;
        }
        // Bit-blast budget gate (fail-closed): refuse the WHOLE query — internal
        // AND executor paths — when a single BV term is too WIDE, or the CUMULATIVE
        // BV bit total is too large, to bit-blast without exploding the
        // PersistentBvCache past its cap and thrashing to a watchdog SIGKILL.
        // Always sound (Unknown).
        if self.bitblast_budget_exceeded(expr) {
            return SmtResult::Unknown;
        }
        // #horn-smt-session router gate (Rung 1, design §2.11): a `Search`-lane
        // context with the session enabled hands an eligible pure Bool/LRA
        // conjunction to its persistent `HornSmt` session. Never on the
        // `Verification` lane (INV-S1) and never while a verifier's
        // `ScopedVerificationMode` is alive on this thread (INV-S2) — the
        // in-engine `verify_model*` calls run on THIS search context. `None`
        // = the session did not answer (mode 1 fall-through): the legacy
        // schedule below runs unchanged.
        if self.session_gate_open() {
            if let Some(result) = self.route_to_session(expr) {
                return result;
            }
        }
        // Under an effort (P4a slice 8) the check stays on ay-chc's internal,
        // counted path with its whole per-check budget: no executor attempt,
        // no pre-slice or internal slice sized for one, no fallback. Slice 14
        // nests the executor route under the run's node, after GuardTree S6.
        if crate::run_meter::counting() {
            return self.check_sat_counted(expr);
        }
        // Executor-FIRST policy (inc-12 spacer lane, per-solver opt-in): the
        // spacer-mode PDR engine's wide-Bool transition-system queries punt
        // from the internal slice to the executor ~23% of the time at
        // 0.5-0.7s mean per check; routing the executor first gives it the
        // whole per-check budget directly. The internal loop remains the
        // fallback when the executor returns Unknown (shape unsupported), so
        // completeness is unchanged. Both paths return verified verdicts
        // (the executor's SAT models pass the same strict model check).
        // W1-1B: a preserved wide constant modulus `(mod x 2^w)` (w>=63) MUST be
        // decided by the BigInt executor, which folds `2^32 * 2^32 -> 2^64` and
        // solves it exactly. The native DPLL(T) LIA loop treats the surviving mod
        // as an opaque factor (freeing `x`) and can return a spurious Sat, so we
        // route such queries to the executor first regardless of the per-solver
        // executor_first opt-in. The nonlinear-mul guard still applies: those go
        // to the executor fallback path below (idx<len bounds checks are linear,
        // so this fires for the target class).
        // DT scheduling depends on this query's carried sorts, not unused
        // problem declarations. Embedded metadata needs no registry entry;
        // Array key/value sorts and expression-local constructor returns count.
        // A bounded scan that cannot finish conservatively chooses the same
        // executor-first/short-slice schedule, never a solver verdict.
        // Flattening can erase all DT metadata into scalar ITEs. We have no
        // provenance distinguishing those from ordinary ITE queries, so they
        // now use the normal scalar schedule unless another explicit policy
        // applies. That performance tradeoff needs workload measurement.
        let datatype_use = query_datatypes::classify(expr);
        let dt_executor_first = datatype_use.needs_datatype_schedule();
        // Rung 0 (CHC-COMP 2026): on the SEARCH lane a pure Bool/LIA/LRA query
        // goes to the ay-dpll Executor first with the whole per-check budget.
        // Replaying the engines' real query stream showed the executor decides
        // these queries reliably (0 Unknown / 0 disagreements over 2,484
        // verdicts, the development design notes at 9598c4206) while the
        // internal-first slice + capped fallback produced 28–74 % Unknown.
        // The internal loop stays as the fallback when the executor returns
        // Unknown, so completeness is unchanged; the Verification lane keeps
        // the internal-first schedule.
        let (search_executor_first, search_preslice) = search_lane_scalar_policy();
        let trace_level = checksat_trace_level();
        let nonlinear = expr.contains_nonlinear_mul();
        let scalar =
            scalar_route::scalar_arith_query(expr, self.lane, nonlinear || dt_executor_first);
        let pure_scalar = scalar.is_some();
        let real_executor_first = scalar == Some(scalar_route::ScalarArith::Real);
        let scalar_executor_first = real_executor_first
            || (self.lane == SmtLane::Search && search_executor_first && pure_scalar);
        if trace_level >= 3 {
            // Origin hunt for ill-typed engine-built atoms: dump the first few
            // offending conjuncts with the caller's backtrace.
            static ILL_TYPED_DUMPS: std::sync::atomic::AtomicUsize =
                std::sync::atomic::AtomicUsize::new(0);
            if let Some((offending, reason)) = expr.conjuncts().iter().find_map(|c| {
                super::executor_sort_guard::unsupported_executor_expr_reason(c)
                    .map(|r| ((*c).clone(), r))
            }) {
                if ILL_TYPED_DUMPS.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 6 {
                    let text = crate::pdr::model::InvariantModel::expr_to_smtlib(&offending);
                    safe_eprintln!(
                        "[CKSAT-TRACE {:?}] ILL-TYPED conjunct ({reason}): {} vars={:?}\n{}",
                        std::thread::current().id(),
                        &text[..text.len().min(300)],
                        offending
                            .vars()
                            .iter()
                            .map(|v| format!("{}:{}", v.name, v.sort))
                            .collect::<Vec<_>>(),
                        std::backtrace::Backtrace::force_capture()
                    );
                }
            }
        }
        if trace_level >= 2 {
            safe_eprintln!(
                "[CKSAT-TRACE {:?}] policy lane={:?} nonlinear={nonlinear} pure_scalar={pure_scalar} dt={dt_executor_first} scalar_exec_first={scalar_executor_first} strikes={} conv_budget_exceeded={}",
                std::thread::current().id(),
                self.lane,
                self.conversion_budget_strikes,
                self.conversion_budget_exceeded
            );
        }
        if scalar_executor_first {
            // A Real query goes straight to the executor, whose Search lane
            // solves the query's equalities first (`smt::solve_eqs`): the
            // internal loop can never refute a query with Real atoms (#5925),
            // so on the refutations the engines mostly ask for, the pre-slice
            // only spent its whole 50 ms.
            let real_query = crate::ab_switches::get().search_solve_eqs
                && expr.vars().iter().any(|v| v.sort == crate::ChcSort::Real);
            if let (Some(preslice), false) = (search_preslice, real_query) {
                // Measurement variant: a short internal pre-slice catches the
                // ~10 ms internal wins before paying the executor set-up.
                let slice = match self.clamp_timeout_to_deadlines(Some(
                    self.check_timeout
                        .get()
                        .map_or(preslice, |t| t.min(preslice)),
                )) {
                    Ok(Some(t)) => t,
                    Ok(None) => preslice,
                    Err(()) => return SmtResult::Unknown,
                };
                if !slice.is_zero() {
                    let prev = self.check_timeout.replace(Some(slice));
                    let early = self.check_sat_internal(expr);
                    self.check_timeout.set(prev);
                    if !matches!(early, SmtResult::Unknown) {
                        if self.exact_term_memory_exceeded() {
                            return SmtResult::Unknown;
                        }
                        crate::smt::note_solve_progress();
                        return early;
                    }
                }
            }
        }
        let mut executor_first_unknown = false;
        if (self.executor_first_check_sat
            || dt_executor_first
            || scalar_executor_first
            || expr.contains_wide_const_mod_div())
            && !expr.contains_nonlinear_mul()
        {
            let timeout = self
                .check_timeout
                .get()
                .unwrap_or(std::time::Duration::from_secs(5));
            let timeout = match self.clamp_timeout_to_deadlines(Some(timeout)) {
                Ok(Some(t)) => t,
                Ok(None) => timeout,
                Err(()) => return SmtResult::Unknown,
            };
            if !timeout.is_zero() {
                let propagated_model = FxHashMap::default();
                let t_first = ay_core::time::Instant::now();
                if trace_level >= 1 {
                    safe_eprintln!(
                        "[CKSAT-TRACE {:?}] executor-first start timeout={timeout:?}",
                        std::thread::current().id()
                    );
                }
                let first = self.check_sat_via_executor(expr, &propagated_model, timeout);
                if trace_level >= 1 {
                    safe_eprintln!(
                        "[CKSAT-TRACE {:?}] executor-first done dt={:.3}s unknown={}",
                        std::thread::current().id(),
                        t_first.elapsed().as_secs_f64(),
                        matches!(first, SmtResult::Unknown)
                    );
                }
                if !matches!(first, SmtResult::Unknown) {
                    if self.exact_term_memory_exceeded() {
                        return SmtResult::Unknown;
                    }
                    crate::smt::note_solve_progress();
                    return first;
                }
                executor_first_unknown = true;
            }
            // Executor could not decide: fall through to the internal loop
            // (its executor-fallback tail is bounded by the thread SMT
            // deadline, so the repeat attempt cannot double the budget).
        }
        // Inc-10 overstay-attribution trace (--chc-checksat-trace>=1).
        let trace = checksat_trace_level() >= 1;
        let start = ay_core::time::Instant::now();
        // Internal-first SLICE (#23 Stage 2.5): the internal DPLL(T) gets
        // min(2s, budget/4); on Unknown/expiry the full ay-dpll Executor gets
        // the remaining budget. Measured motivation (FIREFLY-class lustre
        // checks): the internal loop spins the WHOLE 30s per-check budget on
        // an init∧bad formula the executor (with its full preprocessing
        // pipeline) decides in 0.03s — and the old `internal_elapsed < 2s`
        // fallback gate then blocked the executor entirely. The slice
        // preserves fast internal wins (post-Stage-1/2 lustre checks decide
        // internally in ~10ms) while guaranteeing the more complete executor
        // always sees real budget. Ordinary scalar queries have no internal
        // slice when no per-check timeout is set.
        // Share the exact query-local classification with executor-first.
        // Only DT-present/indeterminate queries receive the 25ms cap.
        let rescue = real_executor_first && executor_first_unknown;
        let slice = scalar_route::internal_slice(datatype_use, rescue, self.check_timeout.get())
            .map(crate::smt::executor_work::narrow_internal_slice);
        if trace {
            safe_eprintln!(
                "[CKSAT-TRACE {:?}] enter check_sat lane={:?} budget={:?} slice={:?} expr_nodes~{}",
                std::thread::current().id(),
                self.lane,
                self.check_timeout.get(),
                slice,
                expr.conjuncts().len()
            );
        }
        let result = if let Some(slice) = slice {
            let prev = self.check_timeout.replace(Some(slice));
            let r = self.check_sat_internal(expr);
            self.check_timeout.set(prev);
            r
        } else {
            self.check_sat_internal(expr)
        };
        if trace {
            safe_eprintln!(
                "[CKSAT-TRACE {:?}] internal done dt={:.3}s result_unknown={}",
                std::thread::current().id(),
                start.elapsed().as_secs_f64(),
                matches!(result, SmtResult::Unknown)
            );
        }

        // Executor fallback for UNKNOWN on non-trivial queries.
        // The internal DPLL(T) lacks theory propagation and is incomplete
        // on QF_LIA queries with many disequalities (#2477). Route through
        // the full ay-dpll Executor which has LRA bound propagation + CEGQI.
        // #7027: Only fall back for theory-incomplete Unknown, NOT budget/timeout.
        // Budget-exceeded expressions (>1M AST nodes) should not be re-solved
        // through the executor — that defeats the OOM protection mechanism.
        //
        // Overhead guard (#7109 regression fix): Cap executor fallback to 10
        // attempts (MAX_EXECUTOR_FALLBACKS) to prevent cumulative overhead from
        // hundreds of Unknown results exhausting the 15s budget. Also skip fallback
        // when the internal solver took >=2s (query is genuinely hard, not just
        // theory-incomplete — a fast Unknown signals incomplete theory propagation
        // on disequalities). Default per-attempt timeout is 5s (generous for
        // fallback; the 10-attempt cap provides primary overhead protection).
        // QF_NIA short-circuit: the ay-dpll executor is not a decision
        // procedure for nonlinear integer multiplication, so on such a query it
        // can only exhaust its wall-clock bound and return Unknown. (It now
        // honors that bound — see the `:timeout` set-option wiring in
        // ay-dpll's `executor.rs`; the hang predated that fix.) The native loop
        // has already returned the best sound answer it can (Unsat via the
        // dropped-product linear relaxation, else Unknown), so skip the
        // executor rather than stall the full timeout on an undecidable
        // fragment. The decidable bit-vector path bit-blasts to SAT and
        // contains no `Mul`, so it is unaffected.
        // The slice above bounds how much budget the internal attempt can
        // consume, so the old `internal_elapsed < 2s` skip-gate is gone: it
        // wrongly assumed a slow internal Unknown meant "genuinely hard",
        // but the executor decides FIREFLY-class checks in 30ms that the
        // internal loop cannot decide in 30s. The remaining guards (#7027
        // conversion budget, NIA short-circuit, strike/attempt caps) stay.
        let internal_elapsed = start.elapsed();
        // Duplicate-attempt guard (#chc25-dtbv-lane-perf): when the
        // executor-first dispatch above ALREADY solved this byte-identical
        // `expr` (empty propagated model, same adapter pipeline) and returned
        // Unknown, the plain fallback attempt is a pure re-run and can only
        // return Unknown again. Skip it UNLESS the dv-off retry applies (Int
        // vars present — the retry runs a genuinely different preprocessing
        // configuration that can rescue an executor Unknown). Measured on the
        // chc_dt_bv_* fixtures: each undecided DT query paid three executor
        // sessions (executor-first + prepare dispatch + fallback); this
        // removes the redundant third.
        // Search lane: the executor-first attempt already ran EqDiffVar-off,
        // so no dv-off retry can rescue it — a fallback would be a pure re-run.
        let fallback_is_duplicate = executor_first_unknown
            && !(self.lane != SmtLane::Search
                && super::executor_adapter::dv_unknown_retry_enabled()
                && expr_mentions_int_var(expr));
        // Rung 0: the #7109 per-context cap (10 fallbacks) is gone on BOTH
        // lanes — every fallback is bounded by the per-check timeout and the
        // thread SMT deadline below, and a capped fallback was a spurious
        // Unknown (T4 "fallback exhaustion": 44–95 % Unknown on some lustre
        // instances; on the Verification lane a lost solve).
        if trace_level >= 2 && matches!(result, SmtResult::Unknown) {
            safe_eprintln!(
                "[CKSAT-TRACE {:?}] fallback gate dup={fallback_is_duplicate} nonlinear={nonlinear} conv_budget_exceeded={} strikes={} deadline_left={:?}",
                std::thread::current().id(),
                self.conversion_budget_exceeded,
                self.conversion_budget_strikes,
                crate::smt::deadline::smt_deadline_remaining()
            );
        }
        // Rung 0: the #7109 cap is replaced by the deadline bound; only a
        // deadline-free solve keeps the legacy cap (see DEADLINE_FREE_FALLBACK_CAP).
        let fallback_bounded_by_deadline = self.check_timeout.get().is_some()
            || crate::smt::deadline::effective_thread_deadline().is_some()
            || self.current_global_deadline().is_some();
        let fallback_count_ok = fallback_bounded_by_deadline
            || self.executor_fallback_count < DEADLINE_FREE_FALLBACK_CAP;
        if matches!(result, SmtResult::Unknown)
            && !fallback_is_duplicate
            && !nonlinear
            && !self.conversion_budget_exceeded
            && self.conversion_budget_strikes < super::context::MAX_CONVERSION_STRIKES
            && fallback_count_ok
        {
            let check_timeout = self.check_timeout.get();
            let timeout = match check_timeout {
                Some(t) => t
                    .checked_sub(internal_elapsed)
                    .unwrap_or(std::time::Duration::ZERO),
                None => std::time::Duration::from_secs(5),
            };
            // Respect the thread-local SMT deadline for the fallback too.
            let timeout = match self.clamp_timeout_to_deadlines(Some(timeout)) {
                Ok(Some(t)) => t,
                Ok(None) => timeout,
                Err(()) => std::time::Duration::ZERO,
            };
            if !timeout.is_zero() {
                self.executor_fallback_count += 1;
                let propagated_model = FxHashMap::default();
                if trace {
                    safe_eprintln!(
                        "[CKSAT-TRACE {:?}] executor fallback start timeout={timeout:?}",
                        std::thread::current().id()
                    );
                }
                let fallback =
                    self.executor_fallback_with_dv_retry(expr, &propagated_model, timeout, trace);
                if trace {
                    safe_eprintln!(
                        "[CKSAT-TRACE {:?}] executor fallback done total_dt={:.3}s unknown={}",
                        std::thread::current().id(),
                        start.elapsed().as_secs_f64(),
                        matches!(fallback, SmtResult::Unknown)
                    );
                }
                if !matches!(fallback, SmtResult::Unknown) {
                    if self.exact_term_memory_exceeded() {
                        return SmtResult::Unknown;
                    }
                    crate::smt::note_solve_progress();
                    return fallback;
                }
            }
        }
        if trace {
            safe_eprintln!(
                "[CKSAT-TRACE {:?}] exit check_sat total_dt={:.3}s",
                std::thread::current().id(),
                start.elapsed().as_secs_f64()
            );
        }

        // A DECIDED (Sat/Unsat) verdict is genuine progress: reset the
        // no-progress streaks so only an UNBROKEN run of missing-var Unknowns
        // can trip the breaker (see `crate::smt::context`).
        if self.exact_term_memory_exceeded() {
            return SmtResult::Unknown;
        }
        if !matches!(result, SmtResult::Unknown) {
            crate::smt::note_solve_progress();
        }
        result
    }

    /// Executor-fallback check_sat for verification queries (#7109).
    ///
    /// First tries the internal DPLL(T) loop. If it returns Unknown (incomplete
    /// on QF_LIA queries with many disequalities, #2477), falls back to the
    /// full ay-dpll Executor which has theory propagation + CEGQI.
    ///
    /// Use this instead of `check_sat` for PDR verification queries where
    /// completeness matters. Regular check_sat callers (equality discovery,
    /// parity discovery, entry value inference) should NOT use this — they
    /// rely on Unknown to signal graceful degradation.
    pub fn check_sat_with_executor_fallback(&mut self, expr: &ChcExpr) -> SmtResult {
        if crate::run_meter::charge(crate::run_meter::Step::SmtEntry).is_err() {
            return SmtResult::Unknown;
        }
        let _census = lane::CensusFrame::enter1(
            lane::SmtEntry::ExecutorFallback,
            Some(self.census_lane()),
            expr,
        );
        // This entry point intentionally bypasses `check_sat`, whose ordinary
        // preflight owns the same check. A verification caller may therefore
        // reach it directly; never let either the native attempt or its
        // executor fallback publish across this context's term-store ceiling.
        if self.exact_term_memory_exceeded() {
            return SmtResult::Unknown;
        }
        // No-progress circuit breaker (fail-closed): short-circuit to Unknown
        // once the solve has been observed spinning on the same unassignable
        // evaluable-position free-variable set (see `check_sat`/`sat_or_unknown`).
        if crate::smt::no_progress_breaker_tripped() {
            return SmtResult::Unknown;
        }
        // Bit-blast budget gate (fail-closed): refuse the WHOLE query — internal
        // AND executor paths — when a single BV term is too WIDE, or the CUMULATIVE
        // BV bit total is too large, to bit-blast without exploding the
        // PersistentBvCache past its cap and thrashing to a watchdog SIGKILL.
        // Always sound (Unknown).
        if self.bitblast_budget_exceeded(expr) {
            return SmtResult::Unknown;
        }
        // Rung 0 (T3): see `check_sat`.
        if self.deadlines_expired() {
            note_post_deadline_refusal();
            return SmtResult::Unknown;
        }
        // Under an effort: the internal path with the whole budget (`check_sat`).
        if crate::run_meter::counting() {
            return self.check_sat_counted(expr);
        }
        let start = ay_core::time::Instant::now();
        let total = self.check_timeout.get();
        let (slice, real_executor_first) =
            executor_first::native_first_slice(expr, self.lane, total);
        // Under a counted allowance the native attempt keeps the width it had
        // under the 1.5 s cap, as `check_sat`'s internal slice does.
        let slice = slice.map(crate::smt::executor_work::narrow_internal_slice);
        // Executor-routed queries: one full-budget Executor session first
        // (see `executor_first_attempt`), then the sliced internal attempt on
        // what it leaves; after an undecided first session the tail below
        // would be a pure re-run.
        let (result, executor_first_unknown) =
            match self.executor_first_then_internal(expr, slice, total, start, real_executor_first)
            {
                Ok(attempt) => attempt,
                Err(decided) => return decided,
            };
        if self.exact_term_memory_exceeded() {
            return SmtResult::Unknown;
        }

        // QF_NIA short-circuit: skip the executor on nonlinear integer
        // multiplication — it cannot decide that fragment and would only burn
        // the full timeout before returning Unknown. See the rationale on
        // `check_sat`. After an executor-first Unknown the tail would re-run
        // that same attempt on less budget, so it is skipped
        // (`fallback_is_duplicate` in `check_sat`).
        if matches!(result, SmtResult::Unknown)
            && !executor_first_unknown
            && !expr.contains_nonlinear_mul()
        {
            let timeout = self.executor_fallback_budget(total, start);
            if !timeout.is_zero() {
                let propagated_model = FxHashMap::default();
                let fallback = self.executor_fallback_with_dv_retry(
                    expr,
                    &propagated_model,
                    timeout,
                    checksat_trace_level() >= 1,
                );
                if !matches!(fallback, SmtResult::Unknown) {
                    if self.exact_term_memory_exceeded() {
                        return SmtResult::Unknown;
                    }
                    crate::smt::note_solve_progress();
                    return fallback;
                }
            }
        }

        if self.exact_term_memory_exceeded() {
            return SmtResult::Unknown;
        }
        if !matches!(result, SmtResult::Unknown) {
            crate::smt::note_solve_progress();
        }
        result
    }

    /// Executor fallback with the inc-18 EqDiffVar SAT-direction retry.
    ///
    /// Attribution (inc-18, SYNAPSE_all_e7_907 iter=1 strengthened check):
    /// the inc-14 EqDiffVar pass — built for the UNSAT direction of
    /// guarded-eq networks — DEFEATS the executor's model search on the
    /// SAT-shaped sibling (itp-init transition checks with a nearly-free
    /// initial state): the plain pipeline decides `sat` in 0.18s where the
    /// reduced form is still unknown at 30s (z3 agrees `sat` instantly).
    /// The pass fires unconditionally inside the executor, so an
    /// executor-unknown may be pass-induced rather than genuine hardness.
    ///
    /// Policy: reserve `min(timeout/3, 1.5s)` of the fallback budget; run
    /// the executor normally (pass ON) on the rest; if THAT attempt returns
    /// Unknown, re-run ONCE with the pass disabled per-run
    /// (`:ay-eq-diffvar false`) on whatever budget remains. The total never
    /// exceeds the caller's `timeout` (inc-10 per-check cap preserved).
    ///
    /// Soundness: both attempts go through the IDENTICAL adapter pipeline —
    /// UNSAT verdicts carry exactly the trust every executor verdict at this
    /// call site already carries, and SAT models pass the same strict model
    /// validation against the ORIGINAL expression. Disabling a preprocessing
    /// pass cannot change the formula's meaning; there is no new answer
    /// construction in this path. Kill switch: `AY_EXEC_DV_RETRY=0` (also
    /// implied by the inc-14 master `AY_EQ_DIFFVAR=0`).
    fn executor_fallback_with_dv_retry(
        &self,
        expr: &ChcExpr,
        propagated_model: &FxHashMap<String, SmtValue>,
        timeout: std::time::Duration,
        trace: bool,
    ) -> SmtResult {
        // Search lane (Rung 0): every executor script is already EqDiffVar-off
        // (`SmtContext::executor_disables_eq_diffvar`), so the retry is
        // redundant — one attempt with the whole budget.
        let dv_retry = self.lane != SmtLane::Search
            && super::executor_adapter::dv_unknown_retry_enabled()
            && expr_mentions_int_var(expr);
        let reserve = if dv_retry {
            (timeout / 3).min(std::time::Duration::from_millis(1500))
        } else {
            std::time::Duration::ZERO
        };
        let attempt_start = ay_core::time::Instant::now();
        let first =
            self.check_sat_via_executor(expr, propagated_model, timeout.saturating_sub(reserve));
        if !matches!(first, SmtResult::Unknown) || reserve.is_zero() {
            return first;
        }
        // Retry budget: the leftover of the caller's window (>= the reserve
        // when the first attempt returned early), clamped to the thread SMT
        // deadline like every executor dispatch.
        let remaining = timeout.saturating_sub(attempt_start.elapsed());
        let retry_timeout = match self.clamp_timeout_to_deadlines(Some(remaining)) {
            Ok(Some(t)) => t,
            Ok(None) => remaining,
            Err(()) => return SmtResult::Unknown,
        };
        if retry_timeout.is_zero() {
            return SmtResult::Unknown;
        }
        if trace {
            safe_eprintln!(
                "[CKSAT-TRACE {:?}] dv-off executor retry start timeout={retry_timeout:?}",
                std::thread::current().id()
            );
        }
        let retry =
            self.check_sat_via_executor_with_opts(expr, propagated_model, retry_timeout, true);
        if trace {
            safe_eprintln!(
                "[CKSAT-TRACE {:?}] dv-off executor retry done unknown={}",
                std::thread::current().id(),
                matches!(retry, SmtResult::Unknown)
            );
        }
        retry
    }

    /// A check under an effort (P4a slice 8): the internal DPLL(T) path with
    /// the whole per-check budget, the executor route closed. A query that
    /// needs the executor answers `unknown`: a preserved wide constant
    /// modulus, whose opaque native `mod` can yield a spurious `sat` (W1-1B).
    /// What the closed route costs (the executor-decided checks the internal
    /// loop cannot decide: Real refutations, array and datatype queries it
    /// leaves open) is measured in guard-tree.md §14.
    fn check_sat_counted(&mut self, expr: &ChcExpr) -> SmtResult {
        if expr.contains_wide_const_mod_div() {
            let _ = crate::run_meter::close_route();
            return SmtResult::Unknown;
        }
        let result = self.check_sat_internal(expr);
        if self.exact_term_memory_exceeded() {
            return SmtResult::Unknown;
        }
        if matches!(result, SmtResult::Unknown) {
            // The executor fallback's gate (`check_sat`): it would have
            // retried, unless the run's count is what stopped the check.
            if !expr.contains_nonlinear_mul()
                && !self.conversion_budget_exceeded
                && !crate::run_meter::run_stopped()
            {
                let _ = crate::run_meter::close_route();
            }
        } else {
            crate::smt::note_solve_progress();
        }
        result
    }

    fn check_sat_internal(&mut self, expr: &ChcExpr) -> SmtResult {
        let trace = checksat_trace_level() >= 1;
        let start = ay_core::time::Instant::now();
        // Clamp to the thread-local SMT deadline (engine budget enforcement).
        // An expired deadline returns Unknown immediately — callers already
        // treat Unknown as a sound "give up" signal.
        let timeout = match self.clamp_timeout_to_deadlines(self.check_timeout.get()) {
            Ok(timeout) => timeout,
            Err(()) => return SmtResult::Unknown,
        };

        let prepared = match self.prepare_check_sat_query(expr, start, timeout) {
            Ok(p) => p,
            Err(result) => {
                if trace {
                    safe_eprintln!(
                        "[CKSAT-TRACE {:?}] prepare early-exit dt={:.3}s",
                        std::thread::current().id(),
                        start.elapsed().as_secs_f64()
                    );
                }
                return result;
            }
        };
        if trace {
            safe_eprintln!(
                "[CKSAT-TRACE {:?}] prepare ok dt={:.3}s",
                std::thread::current().id(),
                start.elapsed().as_secs_f64()
            );
        }

        // Build CNF via Tseitin transformation.
        let mut cnf_state = match self.build_check_sat_cnf(&prepared, start, timeout) {
            Ok(s) => s,
            Err(result) => return result,
        };
        if trace {
            safe_eprintln!(
                "[CKSAT-TRACE {:?}] cnf ok dt={:.3}s entering theory loop (timeout={timeout:?})",
                std::thread::current().id(),
                start.elapsed().as_secs_f64()
            );
        }

        // Attach BV bit-blasting if the formula contains BV operations.
        // Returns false when a BV term exceeds the bit-blast width budget: the
        // SAT instance is then missing its BV constraints, so we must NOT run
        // the theory loop on it (its models could violate the omitted
        // constraints). Abstain with Unknown — always sound (never a false
        // Sat/Unsat). See the soundness note on `attach_bv_bitblasting`.
        if !self.attach_bv_bitblasting(&prepared.features, &mut cnf_state) {
            if trace {
                safe_eprintln!(
                    "[CKSAT-TRACE {:?}] bitblast refused (width budget) → Unknown dt={:.3}s",
                    std::thread::current().id(),
                    start.elapsed().as_secs_f64()
                );
            }
            return SmtResult::Unknown;
        }

        // #5877: Check timeout after BV bit-blasting.
        if let Some(t) = timeout {
            if start.elapsed() >= t {
                return SmtResult::Unknown;
            }
        }

        let mut split_state = term_growth::SplitState::new();
        self.run_check_sat_theory_loop(expr, prepared, cnf_state, &mut split_state, start, timeout)
    }
}
