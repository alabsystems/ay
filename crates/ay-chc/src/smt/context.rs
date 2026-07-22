// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Core SMT context definition and lifecycle methods.

use super::types::{SmtResult, SmtValue};
use crate::expr::maybe_grow_expr_stack;
use crate::{ChcExpr, ChcSort, PredicateId};
// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::{DetHashMap as HbHashMap, DetHashSet as HbHashSet};
use ay_core::term::TermData;
use ay_core::{CnfClause, TermId, TermStore};
#[cfg(test)]
use std::collections::VecDeque;
use std::sync::Arc;

type CachedBvBits = Vec<i32>;
type CachedBvTermMap<T> = HbHashMap<String, T>;

thread_local! {
    /// Absolute wall-clock deadline for the whole enclosing CHC/PDR proof solve
    /// on this thread. Set once at the `solve_pdr_proof` entry point (via
    /// [`ScopedSolveDeadline`]) so it covers EVERY `SmtContext` used during the
    /// solve — the main PDR solver's context, startup-discovery contexts, the
    /// fresh re-validation verifier, and every portfolio engine — even the ones
    /// that never receive a per-context deadline or a per-query timeout. The
    /// DPLL(T) theory loop and interruptible-SAT `should_stop` consult it on
    /// every `check_sat`, so no single query can run past the solve deadline.
    static THREAD_SOLVE_DEADLINE: std::cell::Cell<Option<ay_core::time::Instant>> =
        const { std::cell::Cell::new(None) };
}

/// Return the current thread's solve-wide deadline, if a solve is in progress.
pub(crate) fn current_thread_solve_deadline() -> Option<ay_core::time::Instant> {
    THREAD_SOLVE_DEADLINE.with(std::cell::Cell::get)
}

/// RAII guard that installs a thread-wide solve deadline for the duration of a
/// CHC/PDR proof solve and restores the previous value on drop (so nested or
/// sequential solves on the same thread compose correctly).
pub(crate) struct ScopedSolveDeadline(Option<ay_core::time::Instant>);

impl ScopedSolveDeadline {
    pub(crate) fn new(deadline: Option<ay_core::time::Instant>) -> Self {
        Self(THREAD_SOLVE_DEADLINE.with(|cell| cell.replace(deadline)))
    }
}

impl Drop for ScopedSolveDeadline {
    fn drop(&mut self) {
        THREAD_SOLVE_DEADLINE.with(|cell| cell.set(self.0));
    }
}

// ---------------------------------------------------------------------------
// No-progress circuit breaker for the missing-free-variable Unknown fail-closed
// path (`SmtContext::sat_or_unknown`).
//
// Motivation (ny-cert JSON-serialization grind): the DPLL(T) loop can return a
// SAT model that omits an assignment for a free variable occurring in an
// evaluable theory position (bb-cell memory-cell SSA temporaries and serde
// `*_undef_field*` values). `sat_or_unknown` correctly refuses to accept such an
// under-assigned model — it completes it with sort defaults, re-verifies
// strictly, and on failure returns Unknown (fail-closed). That decision is
// sound. The DEFECT is that the OUTER CHC/PDR engine (the obligation queue in
// `strengthen`, predecessor reachability, generalization, invariant discovery,
// …) keeps RE-ISSUING the same — or the same-unassignable-variable-set —
// query, each time paying full DPLL(T) + model-completion + strict-reverify
// cost, all returning the identical Unknown. With `max_obligations` in the tens
// of thousands and the DEFAULT_SAFETY_DEADLINE at 300s, the loop grinds long
// past the (shorter) model-checker-consumer native-lane wall-clock watchdog, which then
// SIGKILLs the whole process before the cooperative 300s deadline is ever
// reached — so the obligation is never even measured.
//
// This breaker detects that no-progress spin and short-circuits the solve to
// Unknown cooperatively:
//   * `same_sig_streak` counts CONSECUTIVE missing-var Unknowns with the SAME
//     unassignable-free-variable-set signature (the identical-query spin — the
//     documented symptom, e.g. `bb1_cell_v56` ×370). It resets whenever a
//     different signature appears.
//   * `total_streak` counts CONSECUTIVE missing-var Unknowns regardless of
//     signature (a varying-query but still no-progress spin). It resets only on
//     genuine progress (a DECIDED Sat/Unsat result — see `note_solve_progress`).
// Tripping EITHER limit sets `tripped`, after which `no_progress_breaker_tripped`
// returns true: `check_sat` short-circuits to Unknown, and `PdrSolver::is_cancelled`
// treats it as a cooperative cancellation so every engine loop that already polls
// `is_cancelled` bails to Unknown instead of starting another round.
//
// SOUNDNESS: the breaker's ONLY effect is to return `Unknown` earlier. It never
// converts an incomplete/under-assigned model into a Sat/Unsat/proved verdict —
// it never even touches the accept path, only the already-fail-closed Unknown
// path. Unknown is sound (a not-proved obligation stays not-proved).

/// Consecutive identical-signature missing-var Unknowns before the breaker trips.
/// A healthy solve essentially never re-hits the SAME unassignable-free-variable
/// set this many times in a row; the reported grind repeats it hundreds of times.
pub(crate) const NO_PROGRESS_SAME_SIG_LIMIT: u32 = 48;

/// Consecutive missing-var Unknowns (any signature) with NO decided result in
/// between before the breaker trips. Guards the varying-query no-progress spin.
pub(crate) const NO_PROGRESS_TOTAL_LIMIT: u32 = 256;

/// Full `PersistentBvCache` cap-clears within a single solve before the breaker
/// trips. A cap-clear (`PersistentBvCache cap hit; cleared`) means the bit-blast
/// state exceeded `MAX_PERSISTENT_CACHE_ENTRIES` and the WHOLE cache was thrown
/// away — a strong pathology signal (re-bitblasting the same huge nested-serde
/// structure with no reuse). A healthy BV-heavy solve captures its state ONCE
/// and reuses it; the reported ny-cert grind cleared it ~470 times. Beyond this
/// small bound the solve is thrashing, not progressing, so bailing to Unknown is
/// sound and far cheaper than grinding to the wall-clock watchdog SIGKILL.
pub(crate) const NO_PROGRESS_BV_CACHE_CLEAR_LIMIT: u32 = 8;

#[derive(Clone, Copy)]
struct NoProgressBreaker {
    last_signature: u64,
    same_sig_streak: u32,
    total_streak: u32,
    /// Count of full `PersistentBvCache` cap-clears observed in this solve.
    bv_cache_clears: u32,
    tripped: bool,
}

impl NoProgressBreaker {
    const EMPTY: Self = Self {
        last_signature: 0,
        same_sig_streak: 0,
        total_streak: 0,
        bv_cache_clears: 0,
        tripped: false,
    };
}

thread_local! {
    static NO_PROGRESS_BREAKER: std::cell::Cell<NoProgressBreaker> =
        const { std::cell::Cell::new(NoProgressBreaker::EMPTY) };
}

/// Record a fail-closed "SAT model is missing an assignment for a free variable
/// in an evaluable theory position" Unknown, keyed by `signature` (a hash of the
/// unassignable free-variable set). Returns `true` iff this record TRIPPED the
/// breaker (the transition edge, so the caller can log exactly once).
pub(crate) fn note_unassignable_free_var_no_progress(signature: u64) -> bool {
    NO_PROGRESS_BREAKER.with(|cell| {
        let mut st = cell.get();
        if st.tripped {
            return false;
        }
        if st.same_sig_streak != 0 && st.last_signature == signature {
            st.same_sig_streak = st.same_sig_streak.saturating_add(1);
        } else {
            st.last_signature = signature;
            st.same_sig_streak = 1;
        }
        st.total_streak = st.total_streak.saturating_add(1);
        let tripped_now = st.same_sig_streak >= NO_PROGRESS_SAME_SIG_LIMIT
            || st.total_streak >= NO_PROGRESS_TOTAL_LIMIT;
        if tripped_now {
            st.tripped = true;
        }
        cell.set(st);
        tripped_now
    })
}

/// Record a full `PersistentBvCache` cap-clear (bit-blast thrash) for the current
/// solve. Returns `true` iff this record TRIPPED the breaker (the transition
/// edge, so the caller can log exactly once). Once the clear count reaches
/// [`NO_PROGRESS_BV_CACHE_CLEAR_LIMIT`] the breaker trips and every engine loop
/// that polls `is_cancelled` / every `check_sat` bails to Unknown, instead of
/// re-bitblasting the same oversized structure until the wall-clock watchdog
/// SIGKILLs the process. SOUNDNESS: the cache is a PURE optimization and this
/// only ever forces an earlier `Unknown` — it never fabricates a Sat/Unsat.
///
/// Unlike the missing-var streaks, a bv-cache thrash is NOT reset by
/// `note_solve_progress`: a decided sub-query does not undo the fact that the
/// solve is re-blasting an oversized structure, and the count is naturally
/// scoped to one solve by the `ScopedNoProgressBreaker` RAII reset.
pub(crate) fn note_bv_cache_thrash_clear() -> bool {
    NO_PROGRESS_BREAKER.with(|cell| {
        let mut st = cell.get();
        if st.tripped {
            return false;
        }
        st.bv_cache_clears = st.bv_cache_clears.saturating_add(1);
        let tripped_now = st.bv_cache_clears >= NO_PROGRESS_BV_CACHE_CLEAR_LIMIT;
        if tripped_now {
            st.tripped = true;
        }
        cell.set(st);
        tripped_now
    })
}

/// Reset the no-progress streaks after a DECIDED (Sat/Unsat) `check_sat` result:
/// genuine progress means the solve is not spinning on an unassignable wall.
/// Does NOT clear an already-tripped breaker (a spin already confirmed stays
/// confirmed for the remainder of the solve; the RAII guard resets per solve).
/// Also does NOT clear the bv-cache-thrash count (see `note_bv_cache_thrash_clear`).
pub(crate) fn note_solve_progress() {
    NO_PROGRESS_BREAKER.with(|cell| {
        let mut st = cell.get();
        if !st.tripped && (st.same_sig_streak != 0 || st.total_streak != 0) {
            st.same_sig_streak = 0;
            st.total_streak = 0;
            st.last_signature = 0;
            cell.set(st);
        }
    });
}

/// True once the no-progress breaker has tripped for this solve. `check_sat`
/// short-circuits to Unknown and `is_cancelled` treats it as cooperative
/// cancellation, so the enclosing engine loops terminate to Unknown promptly.
pub(crate) fn no_progress_breaker_tripped() -> bool {
    NO_PROGRESS_BREAKER.with(|cell| cell.get().tripped)
}

/// RAII guard that resets the no-progress breaker for the duration of a solve
/// and restores the previous state on drop, so nested and sequential solves on
/// the same thread compose correctly (mirrors [`ScopedSolveDeadline`]). Without
/// the reset a tripped breaker from a prior solve on a reused thread would
/// wrongly cancel a fresh, decidable solve.
pub(crate) struct ScopedNoProgressBreaker(NoProgressBreaker);

impl ScopedNoProgressBreaker {
    pub(crate) fn new() -> Self {
        Self(NO_PROGRESS_BREAKER.with(|cell| cell.replace(NoProgressBreaker::EMPTY)))
    }
}

impl Drop for ScopedNoProgressBreaker {
    fn drop(&mut self) {
        NO_PROGRESS_BREAKER.with(|cell| cell.set(self.0));
    }
}

type CachedBvDivKey = (String, String);

/// Maximum number of total entries across all PersistentBvCache maps.
///
/// The cache is a pure optimization (avoids re-bitblasting). On long-running
/// BV-heavy CHC solves the maps can grow unboundedly, causing OOM (#8571).
/// When this threshold is exceeded the entire cache is cleared.
///
/// 500_000 (2026-07): a SINGLE BV-heavy query's captured bit-blast state was
/// observed at 312,901 entries, above the previous 100_000 cap — so
/// `clear_if_over_capacity` (a FULL clear of all maps) fired on every capture
/// and the cache thrashed instead of ever being reused. The raised cap admits
/// that observed single-query state while remaining bounded against the #8571
/// OOM regime.
pub(super) const MAX_PERSISTENT_CACHE_ENTRIES: usize = 500_000;

#[derive(Default)]
pub(super) struct PersistentBvCache {
    pub(super) signature: Vec<String>,
    pub(super) clauses: Vec<CnfClause>,
    pub(super) next_var: u32,
    pub(super) term_to_bits: CachedBvTermMap<CachedBvBits>,
    pub(super) predicate_to_var: CachedBvTermMap<i32>,
    pub(super) bool_to_var: CachedBvTermMap<i32>,
    pub(super) ite_conditions: HbHashSet<String>,
    pub(super) and_cache: HbHashMap<(i32, i32), i32>,
    pub(super) and_children: HbHashMap<i32, (i32, i32)>,
    pub(super) or_cache: HbHashMap<(i32, i32), i32>,
    pub(super) xor_cache: HbHashMap<(i32, i32), i32>,
    pub(super) mux_cache: HbHashMap<(i32, i32, i32), i32>,
    pub(super) unsigned_div_cache: HbHashMap<CachedBvDivKey, (CachedBvBits, CachedBvBits)>,
    pub(super) signed_div_cache: HbHashMap<CachedBvDivKey, (CachedBvBits, CachedBvBits, i32, i32)>,
}

impl PersistentBvCache {
    /// Total number of entries across all inner maps and collections.
    pub(super) fn total_entries(&self) -> usize {
        self.clauses.len()
            + self.term_to_bits.len()
            + self.predicate_to_var.len()
            + self.bool_to_var.len()
            + self.ite_conditions.len()
            + self.and_cache.len()
            + self.and_children.len()
            + self.or_cache.len()
            + self.xor_cache.len()
            + self.mux_cache.len()
            + self.unsigned_div_cache.len()
            + self.signed_div_cache.len()
    }

    /// Clear all cached state, releasing memory.
    pub(super) fn clear(&mut self) {
        self.signature.clear();
        self.clauses.clear();
        self.next_var = 0;
        self.term_to_bits.clear();
        self.predicate_to_var.clear();
        self.bool_to_var.clear();
        self.ite_conditions.clear();
        self.and_cache.clear();
        self.and_children.clear();
        self.or_cache.clear();
        self.xor_cache.clear();
        self.mux_cache.clear();
        self.unsigned_div_cache.clear();
        self.signed_div_cache.clear();
    }

    fn clear_if_over_capacity(&mut self, cap: usize) -> Option<usize> {
        let total = self.total_entries();
        if total <= cap {
            return None;
        }
        self.clear();
        Some(total)
    }

    pub(super) fn enforce_capacity(&mut self) -> Option<usize> {
        self.clear_if_over_capacity(MAX_PERSISTENT_CACHE_ENTRIES)
    }
}

/// SMT context for CHC solving
///
/// Converts CHC expressions to ay-core terms and provides satisfiability checking.
pub struct SmtContext {
    /// Term store for ay-core terms
    pub(crate) terms: TermStore,
    /// Mapping from sort-qualified variable names to ay-core term IDs.
    ///
    /// Keys are always sort-qualified (`{name}_{sort}`) to ensure deterministic
    /// TermId assignment regardless of variable encounter order (#6100).
    pub(super) var_map: FxHashMap<String, TermId>,
    /// Reverse mapping from sort-qualified var_map keys to original CHC variable
    /// names. Used by model extraction to emit original names that downstream
    /// code (cube extraction, MBP, etc.) can look up via `v.name` (#6100).
    pub(super) var_original_names: FxHashMap<String, String>,
    /// Mapping from predicate applications to boolean term IDs
    /// Key is (predicate_id, serialized args) for uniqueness
    pub(super) pred_app_map: FxHashMap<(PredicateId, Vec<String>), TermId>,
    /// Counter for generating unique predicate application names
    pub(super) pred_app_counter: u32,
    /// Optional wall-clock timeout for a single `check_sat` call.
    ///
    /// This is intended for best-effort, auxiliary queries (e.g. invariant discovery).
    pub(super) check_timeout: std::rc::Rc<std::cell::Cell<Option<std::time::Duration>>>,
    /// Optional ABSOLUTE wall-clock deadline for the whole enclosing solve
    /// (e.g. the PDR `solve_timeout`). Unlike `check_timeout` (a per-`check_sat`
    /// *budget*), this is a hard end-time consulted by the DPLL(T) theory loop
    /// and the interruptible-SAT `should_stop` callback REGARDLESS of whether a
    /// per-query timeout was supplied — so a portfolio query that is handed
    /// `timeout = None` (and is not Real-sorted, so the LRA iteration cap does
    /// not apply) cannot spin past the solve deadline. `None` = unbounded.
    pub(super) global_deadline: std::rc::Rc<std::cell::Cell<Option<ay_core::time::Instant>>>,
    /// Per-check expression conversion node counter (#2771).
    pub(super) conversion_node_count: usize,
    /// Set when `conversion_node_count` exceeds the budget during `convert_expr`.
    pub(super) conversion_budget_exceeded: bool,
    /// Count of consecutive `check_sat` calls that exceeded the conversion budget (#2472).
    pub(super) conversion_budget_strikes: u32,
    /// Count of ill-typed BV operations encountered during conversion (#6047).
    /// When > 0, `conversion_budget_exceeded` is set so check_sat returns Unknown
    /// rather than injecting `false` (which is unsound in predecessor/inductiveness
    /// queries — same pattern as #5508 Bool ordering bug).
    pub(super) ill_typed_bv_count: u32,
    /// Mirrors PDR verbose mode for lower-level SMT helpers that need to emit
    /// rare resource-cap diagnostics.
    pub(super) verbose: bool,
    /// Optional seed model used to bias SAT branch polarity during `check_sat`.
    ///
    /// This is a best-effort steering hint used by PDR predecessor queries to
    /// improve model stability across iterations. The seed never changes solver
    /// soundness: it only affects phase preference for split literals.
    pub(super) phase_seed_model: Option<FxHashMap<String, SmtValue>>,
    /// Reusable scratch buffer for building sort-qualified variable names (#6363).
    ///
    /// `get_or_create_var` needs the key `{name}_{sort}` for `var_map` lookups.
    /// Previously, every lookup allocated a fresh `String` via `format!()`.
    /// This buffer is cleared and reused on each call, eliminating allocation
    /// on cache hits entirely and reducing allocation on cache misses to the
    /// insert path only.
    pub(super) qualified_name_buf: String,
    /// Persistent BV bit-blast state reused across `reset()` boundaries (#5877).
    ///
    /// The cache is keyed by canonical term fingerprints rather than `TermId`
    /// so it remains valid after `reset()` replaces the query-local term graph.
    pub(super) persistent_bv_cache: PersistentBvCache,
    /// Count of executor fallback attempts in the current solve (#7109 regression fix).
    /// Capped at MAX_EXECUTOR_FALLBACKS to prevent timeout exhaustion on benchmarks
    /// where the internal solver returns Unknown hundreds of times.
    pub(super) executor_fallback_count: u32,
    /// Executor-first `check_sat` policy (inc-12 spacer lane).
    ///
    /// When set, `check_sat` routes to the full ay-dpll Executor FIRST with
    /// the whole per-check budget, falling back to the internal DPLL(T) loop
    /// only when the executor returns Unknown. Per-solver opt-in (spacer-mode
    /// portfolio PDR engine); default keeps the internal-first slice.
    /// Preserved across `reset()` — engine-level policy, not query state.
    pub(super) executor_first_check_sat: bool,
    /// Datatype definitions from the CHC problem (#7016).
    /// When non-empty, queries with UF apps are routed through the executor
    /// adapter which emits declare-datatype commands before the formula.
    pub(super) datatype_defs: FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>>,
    /// Per-engine term memory budget in bytes (#8600).
    ///
    /// When set, `term_memory_exceeded()` checks the owning `TermStore`'s
    /// `instance_term_bytes` against this budget. This enables per-engine
    /// memory isolation: each portfolio engine gets `global_limit / engine_count`
    /// bytes, preventing a single runaway engine from consuming all memory.
    pub(crate) term_memory_budget: Option<usize>,
    /// Test-only queue of forced `check_sat_with_timeout` results.
    ///
    /// This survives `reset()` so verification tests can inject a synthetic
    /// solver answer into code paths that internally reset the SMT context
    /// before querying.
    #[cfg(test)]
    pub(crate) forced_check_sat_results: VecDeque<SmtResult>,
}

pub(crate) struct SmtCheckTimeoutGuard {
    pub(super) cell: std::rc::Rc<std::cell::Cell<Option<std::time::Duration>>>,
    pub(super) prev: Option<std::time::Duration>,
}

impl Drop for SmtCheckTimeoutGuard {
    fn drop(&mut self) {
        self.cell.set(self.prev);
    }
}

// --- Per-engine term memory budget thread-local propagation (#8600) ---

thread_local! {
    /// Thread-local per-engine term memory budget.
    ///
    /// Set by `scoped_thread_term_memory_budget()` in portfolio schedule code
    /// before launching an engine. All `SmtContext::new()` calls on this thread
    /// automatically inherit the budget.
    static THREAD_TERM_MEMORY_BUDGET: std::cell::Cell<Option<usize>> =
        const { std::cell::Cell::new(None) };
}

/// RAII guard that restores the previous thread-local term memory budget on drop.
pub(crate) struct SmtTermMemoryBudgetGuard {
    prev: Option<usize>,
}

impl Drop for SmtTermMemoryBudgetGuard {
    fn drop(&mut self) {
        THREAD_TERM_MEMORY_BUDGET.set(self.prev);
    }
}

impl Default for SmtContext {
    fn default() -> Self {
        Self::new()
    }
}

/// Maximum number of expression nodes that `convert_expr` will process per
/// `check_sat` call before returning a budget-exceeded sentinel (#2771).
pub(super) const MAX_CONVERSION_NODES: usize = 1_000_000;

/// Number of consecutive budget-exceeded `check_sat` calls before
/// short-circuiting to `Unknown` permanently (#2472).
pub(super) const MAX_CONVERSION_STRIKES: u32 = 3;

/// Maximum executor fallback attempts per SmtContext lifetime.
/// 10 attempts × ~30ms each = ~300ms max overhead. Enough to resolve
/// the 2-4 high-disequality queries on half_true_modif_m while preventing
/// the 334-attempt overhead on dillig02_m.
pub(super) const MAX_EXECUTOR_FALLBACKS: u32 = 10;

impl SmtContext {
    fn term_is_bv_cacheable(&self, term: TermId, memo: &mut FxHashMap<TermId, bool>) -> bool {
        maybe_grow_expr_stack(|| {
            if let Some(&cached) = memo.get(&term) {
                return cached;
            }

            let cacheable = match self.terms.get(term) {
                TermData::Const(_) => true,
                TermData::Var(name, _) => self.var_original_names.contains_key(name),
                TermData::Not(inner) => self.term_is_bv_cacheable(*inner, memo),
                TermData::Ite(cond, then_term, else_term) => {
                    self.term_is_bv_cacheable(*cond, memo)
                        && self.term_is_bv_cacheable(*then_term, memo)
                        && self.term_is_bv_cacheable(*else_term, memo)
                }
                TermData::Let(_, body) => self.term_is_bv_cacheable(*body, memo),
                TermData::Forall(..) | TermData::Exists(..) => false,
                TermData::App(_, args) => {
                    args.iter().all(|&arg| self.term_is_bv_cacheable(arg, memo))
                }
                _ => false,
            };
            memo.insert(term, cacheable);
            cacheable
        })
    }

    fn is_internal_aux_var_name(name: &str) -> bool {
        name.starts_with("_ite_")
            || name.starts_with("_mod_q_")
            || name.starts_with("_mod_r_")
            || name.starts_with("_div_q_")
            || name.starts_with("_div_r_")
    }

    /// Rename internal auxiliary variables with a namespace suffix.
    ///
    /// Uses a node budget (#2771) to prevent unbounded heap allocation.
    ///
    /// **Soundness note:** On budget exhaustion, returns `None` to signal
    /// that renaming is incomplete. Partial renaming is unsound because
    /// ITE/mod/div elimination uses local counters (starting at 0) — if two
    /// obligations both produce `_ite_0` and only one gets renamed, they
    /// collide in the shared `var_map`, merging distinct mathematical variables.
    /// Callers must treat `None` as an indication that this expression cannot
    /// be safely used in a multi-obligation context.
    fn rename_internal_aux_vars(expr: &ChcExpr, namespace: &str) -> Option<ChcExpr> {
        use std::cell::Cell;

        let budget = Cell::new(crate::expr::MAX_PREPROCESSING_NODES);

        fn rename_inner(expr: &ChcExpr, namespace: &str, budget: &Cell<usize>) -> Option<ChcExpr> {
            maybe_grow_expr_stack(|| {
                crate::expr::ExprDepthGuard::check()?;
                let remaining = budget.get();
                if remaining == 0 {
                    return None;
                }
                budget.set(remaining - 1);

                Some(match expr {
                    ChcExpr::Bool(_)
                    | ChcExpr::Int(_)
                    | ChcExpr::Real(_, _)
                    | ChcExpr::BitVec(_, _)
                    | ChcExpr::ConstArrayMarker(_)
                    | ChcExpr::IsTesterMarker(_) => expr.clone(),
                    ChcExpr::Var(v) => {
                        if !SmtContext::is_internal_aux_var_name(&v.name) {
                            return Some(expr.clone());
                        }
                        let mut renamed = v.clone();
                        renamed.name = format!("{}__{}", renamed.name, namespace);
                        ChcExpr::Var(renamed)
                    }
                    ChcExpr::Op(op, args) => {
                        let mut rewritten = Vec::with_capacity(args.len());
                        for a in args {
                            rewritten.push(Arc::new(rename_inner(a.as_ref(), namespace, budget)?));
                        }
                        ChcExpr::Op(*op, rewritten)
                    }
                    ChcExpr::PredicateApp(name, id, args) => {
                        let mut rewritten = Vec::with_capacity(args.len());
                        for a in args {
                            rewritten.push(Arc::new(rename_inner(a.as_ref(), namespace, budget)?));
                        }
                        ChcExpr::PredicateApp(name.clone(), *id, rewritten)
                    }
                    ChcExpr::FuncApp(name, sort, args) => {
                        let mut rewritten = Vec::with_capacity(args.len());
                        for a in args {
                            rewritten.push(Arc::new(rename_inner(a.as_ref(), namespace, budget)?));
                        }
                        ChcExpr::FuncApp(name.clone(), sort.clone(), rewritten)
                    }
                    ChcExpr::ConstArray(ks, val) => ChcExpr::ConstArray(
                        ks.clone(),
                        Arc::new(rename_inner(val.as_ref(), namespace, budget)?),
                    ),
                })
            })
        }

        rename_inner(expr, namespace, &budget)
    }

    /// Preprocessing for solver assumptions and interpolation atom classification.
    ///
    /// Skips `propagate_constants()` which extracts `var = const` equalities and
    /// substitutes them, potentially eliminating the constraint entirely (e.g.,
    /// `x = 0` becomes `true`). When a background is present, such constraints
    /// must be preserved for the theory solver to detect conflicts.
    ///
    /// Both the solver (check_sat_with_assumption_conjuncts) and the interpolation
    /// classifier (compute_interpolant_from_smt_farkas_history) must use this same
    /// pipeline so that TermIds match for A/B partition classification (#2930).
    pub(crate) fn preprocess_incremental_assumption(expr: &ChcExpr, namespace: &str) -> ChcExpr {
        // #6360: Single-pass feature scan replaces 5 individual `contains_*` walks.
        // #8664: Match the normal SMT query entry by expanding short symbolic
        // read-over-write chains before feature routing and auxiliary renaming.
        let initial_features = expr.scan_features();
        let preprocessed_expr = if initial_features.has_array_ops {
            expr.simplify_array_ops().expand_select_store_symbolic()
        } else {
            expr.clone()
        };
        let features = preprocessed_expr.scan_features();

        // #6358 performance: Skip normalization for pure LIA assumptions (no ITE,
        // mod/div, mixed-sort eq, negation, strict int comparison). The scan_features
        // walk is still needed, but we avoid 3-4 additional tree walks for
        // normalization passes that would be identity functions.
        if !features.needs_normalization() {
            let renamed = Self::rename_internal_aux_vars(&preprocessed_expr, namespace)
                .unwrap_or_else(|| preprocessed_expr.clone());
            return renamed.simplify_constants();
        }

        // #6360: shared core normalization phase 1 (mixed-sort eq → ITE → mod).
        let after_mod = features.core_normalize_pre_rename(preprocessed_expr.clone());
        // If rename budget is exhausted, fall back to original expression.
        // Partial renaming is unsound (see rename_internal_aux_vars doc), but the
        // original expression has no aux vars and is safe to use as-is. The solver
        // will handle ITE/mod natively (possibly returning Unknown).
        let renamed = Self::rename_internal_aux_vars(&after_mod, namespace)
            .unwrap_or_else(|| preprocessed_expr.clone());
        // #6360: shared core normalization phase 2 (negation → strict comparison).
        features
            .core_normalize_post_rename(renamed)
            .simplify_constants()
    }

    /// Create a new SMT context
    pub fn new() -> Self {
        // Auto-inherit per-engine term memory budget from thread-local (#8600).
        let term_memory_budget = THREAD_TERM_MEMORY_BUDGET.get();
        Self {
            terms: TermStore::new(),
            var_map: FxHashMap::default(),
            var_original_names: FxHashMap::default(),
            pred_app_map: FxHashMap::default(),
            pred_app_counter: 0,
            check_timeout: std::rc::Rc::new(std::cell::Cell::new(None)),
            global_deadline: std::rc::Rc::new(std::cell::Cell::new(None)),
            conversion_node_count: 0,
            conversion_budget_exceeded: false,
            conversion_budget_strikes: 0,
            ill_typed_bv_count: 0,
            verbose: false,
            phase_seed_model: None,
            qualified_name_buf: String::with_capacity(64),
            persistent_bv_cache: PersistentBvCache::default(),
            executor_fallback_count: 0,
            executor_first_check_sat: false,
            datatype_defs: FxHashMap::default(),
            term_memory_budget,
            #[cfg(test)]
            forced_check_sat_results: VecDeque::new(),
        }
    }

    /// Reset the context
    pub fn reset(&mut self) {
        self.terms = TermStore::new();
        self.var_map.clear();
        self.var_original_names.clear();
        self.pred_app_map.clear();
        self.pred_app_counter = 0;
        self.conversion_node_count = 0;
        self.conversion_budget_exceeded = false;
        self.conversion_budget_strikes = 0;
        self.ill_typed_bv_count = 0;
        self.phase_seed_model = None;
        self.executor_fallback_count = 0;
        // Preserve `check_timeout` across reset so callers can enforce per-check timeouts
        // even when helper routines (e.g., ITE case-splitting) reset the context.
        // Preserve `datatype_defs` across reset — they're problem-level metadata (#7016).
        // Preserve `term_memory_budget` across reset — it's engine-level config (#8600).
        // Preserve `verbose` across reset so cap diagnostics remain visible for
        // the owning solver.
        // Preserve `forced_check_sat_results` across reset in tests so verification
        // harnesses can synthesize a solver answer for the next query.
    }

    pub(crate) fn set_verbose(&mut self, verbose: bool) {
        self.verbose = verbose;
    }

    /// Enable/disable the executor-first `check_sat` policy (inc-12).
    pub(crate) fn set_executor_first_check_sat(&mut self, on: bool) {
        self.executor_first_check_sat = on;
    }

    /// Set datatype definitions from the CHC problem (#7016).
    /// When set, queries containing UF apps are routed through the executor
    /// adapter to get full DT theory support (constructor/selector/tester axioms).
    pub fn set_datatype_defs(
        &mut self,
        defs: FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>>,
    ) {
        self.datatype_defs = defs;
    }

    /// Reconstruct a full CHC datatype sort from `self.datatype_defs`.
    fn datatype_sort_from_defs(&self, dt_name: &str) -> Option<ChcSort> {
        let ctors = self.datatype_defs.get(dt_name)?;
        Some(ChcSort::Datatype {
            name: dt_name.to_string(),
            constructors: Arc::new(
                ctors
                    .iter()
                    .map(|(ctor_name, fields)| crate::ChcDtConstructor {
                        name: ctor_name.clone(),
                        selectors: fields
                            .iter()
                            .map(|(sel_name, sel_sort)| crate::ChcDtSelector {
                                name: sel_name.clone(),
                                sort: sel_sort.clone(),
                            })
                            .collect(),
                    })
                    .collect(),
            ),
        })
    }

    /// Try to convert a ay-core App to a CHC DT expression (#7016).
    ///
    /// Checks if `name` matches a known DT constructor, selector, or tester
    /// from `self.datatype_defs`. Returns `Some(ChcExpr)` on match, `None` otherwise.
    pub(super) fn try_dt_app_to_chc_expr(
        &self,
        name: &str,
        args: &[TermId],
        mut convert_arg: impl FnMut(TermId) -> Option<ChcExpr>,
    ) -> Option<ChcExpr> {
        for (dt_name, ctors) in &self.datatype_defs {
            for (ctor_name, fields) in ctors {
                // Constructor match: name == ctor_name, args.len() == fields.len()
                if name == ctor_name && args.len() == fields.len() {
                    let field_exprs: Option<Vec<Arc<ChcExpr>>> =
                        args.iter().map(|&a| convert_arg(a).map(Arc::new)).collect();
                    let result_sort = self
                        .datatype_sort_from_defs(dt_name)
                        .unwrap_or_else(|| ChcSort::Uninterpreted(dt_name.clone()));
                    return Some(ChcExpr::FuncApp(
                        ctor_name.clone(),
                        result_sort,
                        field_exprs?,
                    ));
                }
                // Selector match: name == field.0, single arg
                for (sel_name, sel_sort) in fields {
                    if name == sel_name && args.len() == 1 {
                        let arg_expr = convert_arg(args[0])?;
                        return Some(ChcExpr::FuncApp(
                            sel_name.clone(),
                            sel_sort.clone(),
                            vec![Arc::new(arg_expr)],
                        ));
                    }
                }
            }
            // Tester match: name == "is-{ctor_name}", single arg
            for (ctor_name, _) in ctors {
                let tester_name = format!("is-{ctor_name}");
                if name == tester_name && args.len() == 1 {
                    let arg_expr = convert_arg(args[0])?;
                    return Some(ChcExpr::FuncApp(
                        tester_name,
                        ChcSort::Bool,
                        vec![Arc::new(arg_expr)],
                    ));
                }
            }
        }
        None
    }

    pub(super) fn bv_cache_key(
        &self,
        term: TermId,
        memo: &mut FxHashMap<TermId, Option<String>>,
    ) -> Option<String> {
        if let Some(cached) = memo.get(&term) {
            return cached.clone();
        }
        let mut cacheable_memo = FxHashMap::default();
        if !self.term_is_bv_cacheable(term, &mut cacheable_memo) {
            memo.insert(term, None);
            return None;
        }
        let key = self.term_to_chc_expr(term).map(|expr| {
            let expr_key = crate::InvariantModel::expr_to_smtlib(&expr);
            format!("{:?}::{expr_key}", self.terms.sort(term))
        });
        memo.insert(term, key.clone());
        key
    }

    pub(super) fn bv_cache_signature(
        &self,
        terms: impl IntoIterator<Item = TermId>,
        memo: &mut FxHashMap<TermId, Option<String>>,
    ) -> Vec<String> {
        let mut signature: Vec<String> = terms
            .into_iter()
            .filter_map(|term| self.bv_cache_key(term, memo))
            .collect();
        signature.sort_unstable();
        signature.dedup();
        signature
    }

    /// Temporarily install a SAT phase-seed model for the duration of `f`.
    ///
    /// The previous seed (if any) is restored even when `f` early-returns.
    pub(crate) fn with_phase_seed_model<R>(
        &mut self,
        seed_model: Option<&FxHashMap<String, SmtValue>>,
        f: impl FnOnce(&mut Self) -> R,
    ) -> R {
        let prev = self.phase_seed_model.take();
        self.phase_seed_model = seed_model.cloned();
        let result = f(self);
        self.phase_seed_model = prev;
        result
    }

    pub(crate) fn scoped_check_timeout(
        &mut self,
        timeout: Option<std::time::Duration>,
    ) -> SmtCheckTimeoutGuard {
        let prev = self.check_timeout.get();
        self.check_timeout.set(timeout);
        SmtCheckTimeoutGuard {
            cell: std::rc::Rc::clone(&self.check_timeout),
            prev,
        }
    }

    /// Returns true if a per-check timeout is currently active.
    ///
    /// Used by verbose logging to indicate when Unknown results may be due to timeout.
    pub(crate) fn has_active_timeout(&self) -> bool {
        self.check_timeout.get().is_some()
    }

    /// Return the currently-scoped per-check timeout, if any.
    pub(crate) fn current_timeout(&self) -> Option<std::time::Duration> {
        self.check_timeout.get()
    }

    /// Set the absolute wall-clock deadline for the whole enclosing solve. The
    /// DPLL(T) theory loop and the interruptible SAT `should_stop` callback honor
    /// it on EVERY `check_sat`, independent of any per-query timeout, so no
    /// single query (even one handed `timeout = None`) can run past the solve's
    /// own deadline. Idempotent; `None` clears it.
    pub(crate) fn set_global_solve_deadline(&self, deadline: Option<ay_core::time::Instant>) {
        self.global_deadline.set(deadline);
    }

    /// Return the currently-active absolute solve deadline, if any.
    pub(crate) fn current_global_deadline(&self) -> Option<ay_core::time::Instant> {
        self.global_deadline.get()
    }

    /// Set the per-engine term memory budget (#8600).
    pub fn set_term_memory_budget(&mut self, budget: Option<usize>) {
        self.term_memory_budget = budget;
    }

    /// Returns true if the owning `TermStore` has exceeded the per-engine budget.
    #[inline]
    pub fn term_memory_exceeded(&self) -> bool {
        self.term_memory_budget
            .is_some_and(|budget| self.terms.instance_memory_exceeded(budget))
    }

    /// Set the thread-local per-engine term memory budget and return an RAII guard
    /// that restores the previous value on drop.
    ///
    /// Called by portfolio schedule code before launching an engine thread.
    pub(crate) fn scoped_thread_term_memory_budget(
        budget: Option<usize>,
    ) -> SmtTermMemoryBudgetGuard {
        let prev = THREAD_TERM_MEMORY_BUDGET.get();
        THREAD_TERM_MEMORY_BUDGET.set(budget);
        SmtTermMemoryBudgetGuard { prev }
    }

    /// Access the sort-qualified variable name → TermId mapping.
    pub(crate) fn var_map(&self) -> &FxHashMap<String, TermId> {
        &self.var_map
    }

    /// Get the original (unqualified) CHC variable name for a sort-qualified
    /// var_map key. Returns the key itself if no mapping exists (defensive
    /// fallback for predicate-app variables or other non-CHC-variable terms).
    pub(crate) fn original_var_name<'a>(&'a self, qualified: &'a str) -> &'a str {
        self.var_original_names
            .get(qualified)
            .map(String::as_str)
            .unwrap_or(qualified)
    }

    #[cfg(test)]
    pub(crate) fn push_forced_check_sat_result_for_tests(&mut self, result: SmtResult) {
        self.forced_check_sat_results.push_back(result);
    }

    /// Run a satisfiability check with a wall-clock timeout.
    ///
    /// On timeout, returns `SmtResult::Unknown`.
    pub fn check_sat_with_timeout(
        &mut self,
        expr: &ChcExpr,
        timeout: std::time::Duration,
    ) -> SmtResult {
        #[cfg(test)]
        if let Some(result) = self.forced_check_sat_results.pop_front() {
            return result;
        }
        let prev = self.check_timeout.replace(Some(timeout));
        let result = self.check_sat(expr);
        self.check_timeout.set(prev);
        result
    }

    /// Like `check_sat_with_executor_fallback` but with an explicit timeout.
    pub fn check_sat_with_executor_fallback_timeout(
        &mut self,
        expr: &ChcExpr,
        timeout: std::time::Duration,
    ) -> SmtResult {
        let prev = self.check_timeout.replace(Some(timeout));
        let result = self.check_sat_with_executor_fallback(expr);
        self.check_timeout.set(prev);
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_persistent_bv_cache_total_entries_empty() {
        let cache = PersistentBvCache::default();
        assert_eq!(cache.total_entries(), 0);
    }

    #[test]
    fn test_persistent_bv_cache_total_entries_counts_all_maps() {
        let mut cache = PersistentBvCache::default();
        cache.clauses.push(CnfClause(vec![]));
        cache.term_to_bits.insert("a".into(), vec![1]);
        cache.predicate_to_var.insert("b".into(), 2);
        cache.bool_to_var.insert("c".into(), 3);
        cache.ite_conditions.insert("d".into());
        cache.and_cache.insert((1, 2), 3);
        cache.and_children.insert(3, (1, 2));
        cache.or_cache.insert((4, 5), 6);
        cache.xor_cache.insert((7, 8), 9);
        cache.mux_cache.insert((1, 2, 3), 4);
        cache
            .unsigned_div_cache
            .insert(("a".into(), "b".into()), (vec![1], vec![2]));
        cache
            .signed_div_cache
            .insert(("c".into(), "d".into()), (vec![3], vec![4], 5, 6));
        // 12 entries total: 1 clause + 1 term_to_bits + 1 predicate_to_var +
        // 1 bool_to_var + 1 ite_conditions + 1 and + 1 and_children + 1 or +
        // 1 xor + 1 mux + 1 unsigned_div + 1 signed_div
        assert_eq!(cache.total_entries(), 12);
    }

    #[test]
    fn test_persistent_bv_cache_clear_resets_all() {
        let mut cache = PersistentBvCache {
            signature: vec!["sig".into()],
            ..Default::default()
        };
        cache.clauses.push(CnfClause(vec![]));
        cache.next_var = 42;
        cache.term_to_bits.insert("a".into(), vec![1]);
        cache.and_cache.insert((1, 2), 3);
        cache.and_children.insert(3, (1, 2));
        assert!(cache.total_entries() > 0);

        cache.clear();
        assert_eq!(cache.total_entries(), 0);
        assert!(cache.signature.is_empty());
        assert_eq!(cache.next_var, 0);
    }

    #[test]
    fn test_persistent_bv_cache_capacity_clear_is_sound_eviction_policy() {
        let mut cache = PersistentBvCache {
            signature: vec!["sig".into()],
            ..Default::default()
        };
        cache.term_to_bits.insert("a".into(), vec![1]);
        cache.and_cache.insert((1, 2), 3);

        assert_eq!(cache.clear_if_over_capacity(1), Some(2));
        assert_eq!(cache.total_entries(), 0);
        assert!(cache.signature.is_empty());
        assert_eq!(cache.clear_if_over_capacity(2), None);
    }

    #[test]
    fn test_persistent_bv_cache_max_entries_constant_is_reasonable() {
        // Sanity check: the constant should be large enough to be useful
        // but bounded to prevent OOM.
        const {
            assert!(MAX_PERSISTENT_CACHE_ENTRIES >= 10_000);
            assert!(MAX_PERSISTENT_CACHE_ENTRIES <= 1_000_000);
        }
    }
}
