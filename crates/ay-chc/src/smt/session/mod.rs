// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `HornSmt` — a persistent online CDCL(T) session for the CHC engines.
//!
//! Design: the development design notes (§2.1 is
//! this file's interface; §3 the data flow; §5 the lifetime plan; §9 the work
//! breakdown and contracts C1–C8). This module tree is the Rung-1 skeleton:
//! every contract type and signature of C1–C5, C7 and C8 is declared here so the
//! four work packages compile independently; bodies are `todo!()` until their
//! owner lands them, except plain data types and one-line accessors.
//!
//! File ownership (§9, disjoint files):
//! - WP-1 (A): this file, `backend.rs`, `theory_box.rs` — session core, SAT
//!   profile, deadline plumbing, result mapping, the re-entry driver,
//!   `BridgeGuard`.
//! - WP-2 (B): `bridge.rs`, `minting.rs` — the `ay_sat::Extension` adapter and
//!   two-tier minting.
//! - WP-3 (C): `convert_memo.rs`, `shim.rs`, `model.rs`, plus the
//!   `smt/context.rs` wiring and the `try_session` router gate.
//! - WP-4 (D): `ledger.rs`, `dump.rs`, plus `smt/lane.rs`, the soundness pins
//!   and the harness.
//!
//! Contracts owned by this file: C1 (the `pub(super)` accessors WP-2/WP-3 use
//! instead of field access) and C7 (`HornSmt`'s API, `HornCheck`,
//! `UnknownReason`, `SessionStats`; `Backend` lives in `backend.rs`).
//!
//! C6 (`smt::lane::{SmtLane, ScopedVerificationMode, verification_mode_active,
//! session_mode}`) is provided after the Rung 0 merge
//! (`chc-bridge-hygiene-2026-09` adds `SmtLane` to `SmtContext`); nothing in
//! this tree references it yet.
//!
//! Soundness posture (§7): the session is SEARCH guidance only. It must never
//! answer a verdict-bearing query (INV-S1 construction-time lane + INV-S2
//! thread-scoped guard, both WP-4); every `Sat` it returns is re-verified
//! against the ORIGINAL expressions before an engine sees it (INV-S3); every
//! clause the bridge hands ay-sat is a theory tautology or goes to the
//! ORIGINAL clause ledger (INV-S5); the atom<->var binding is append-only for
//! the life of one `ay_sat::Solver` (INV-S6).

// Skeleton: bodies land per work package. Remove once WP-1..4 have landed.
#![allow(dead_code, unused, clippy::unused_self, clippy::needless_pass_by_value)]

pub(crate) mod backend;
pub(crate) mod bridge;
pub(crate) mod convert_memo;
pub(crate) mod dump;
pub(crate) mod harness;
pub(crate) mod ledger;
pub(crate) mod minting;
pub(crate) mod model;
pub(crate) mod shim;
pub(crate) mod theory_box;

/// Per-work-package test files (`tests/unit.rs` WP-3, `tests/bridge_unit.rs`
/// WP-2, WP-4's fuzz/diff/replay); the inline `mod tests` below is WP-1's.
#[cfg(test)]
#[path = "tests/mod.rs"]
mod wp_tests;

use std::collections::VecDeque;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;
use std::time::Duration;

use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::term::TermData;
use ay_core::time::Instant;
use ay_core::{Sort, TermId, TermStore, Tseitin, TseitinState};
use ay_sat::{AssumeResult, Literal, SatUnknownReason, SolverContext};

use crate::smt::model_verify::{
    collect_theory_atoms_into, verify_sat_model_conjunction_strict_with_mod_retry,
};
use crate::smt::types::{FarkasConflict, ModelVerifyResult, Partition, SmtValue};
use crate::smt::SmtContext;
use crate::{ChcExpr, ChcSort};

/// Problem-level datatype declarations, the shape `SmtContext::set_datatype_defs`
/// takes (`smt/context.rs`). The design names `crate::DatatypeDefs`; no such
/// alias exists at HEAD, so it is defined here (contract note in the WP-1
/// status report).
pub(crate) type DatatypeDefs = FxHashMap<String, Vec<(String, Vec<(String, ChcSort)>)>>;

/// `--chc-session-trace`: one stderr line per query with the bridge
/// counters (diagnostics; read once).
pub(crate) fn session_trace() -> bool {
    ay_core::misc_cli_flags().chc_session_trace
}

/// Stable handle for a persistent assertion (index into `HornSmt::assertions`;
/// survives rebuild — dead entries become `Tombstone`s, ids are never reused).
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord)]
pub(crate) struct AssertId(pub(crate) u32);

/// Arithmetic-theory classification used by conversion eligibility and lane
/// census. Persistent `HornSmt` sessions are constructed only for `Lra`;
/// `Lia` remains a classification for unsupported-route accounting.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum TheoryKind {
    Lra,
    /// Rung 2.
    Lia,
}

/// One persistent assertion, encoded once, gated by ONE activation variable
/// `act`: global clause `(root ∨ act)`; assuming `¬act` activates; `act` is
/// never assumed positive (inactive assertions are simply not assumed; their
/// saved phase is `true`, §6.2).
pub(crate) struct Assertion {
    /// Retained: pins the pointer key of the conversion memo.
    pub(crate) expr: Arc<ChcExpr>,
    pub(crate) key: convert_memo::ConjunctKey,
    /// `own.convert_expr` result.
    pub(crate) term: TermId,
    /// From `TseitinEncodedAssertion::root_lit` (DIMACS `d` -> `Variable::new(|d| - 1)`).
    pub(crate) root_lit: ay_sat::Literal,
    pub(crate) act: ay_sat::Variable,
    /// Theory atoms reachable from `term` (`ay_core::is_theory_atom`).
    pub(crate) atoms: Vec<TermId>,
    /// Int/Real vars under `term` (model completeness, §2.8).
    pub(crate) arith_vars: Vec<TermId>,
    pub(crate) bool_vars: Vec<TermId>,
    pub(crate) partition: Partition,
    /// Logical scope depth at assertion (0 = permanent).
    pub(crate) scope: u32,
    /// `Api` | `Shim` — the retention policy differs (§6.2).
    pub(crate) origin: AssertOrigin,
    /// Shim LRU stamp (`query_no` of the last query that activated it).
    pub(crate) last_used_query: u64,
    pub(crate) state: AssertState,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AssertOrigin {
    Api,
    Shim,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum AssertState {
    Live,
    /// Unit-killed (`[+act]` added globally); its id can never be activated again.
    Dead,
    /// Not carried over by `rebuild()`.
    Tombstone,
}

/// Session knobs. Defaults are the design's (§2.1).
#[derive(Debug, Clone)]
pub(crate) struct SessionConfig {
    /// Shim conjuncts unused for this many queries are unit-killed.
    pub(crate) kill_after_queries: u64,
    pub(crate) rebuild_dead_vars: usize,
    /// Must stay below `IC3_GC_MIN_SOLVES = 500` (design F7).
    pub(crate) rebuild_queries_after: u64,
    /// `TermStore::len` threshold.
    pub(crate) rebuild_terms_after: usize,
    /// Assertions active in any of the last N queries are re-asserted on rebuild.
    pub(crate) hot_set_window: u64,
    /// All mint kinds; exceeding it is `Budget(MintCap)`.
    pub(crate) max_mints_per_query: u32,
    /// Counted only when a NEW pair is minted (design F23).
    pub(crate) max_model_eq_rounds: u32,
    /// Originals-restart protocol cap; exceeding it is `Budget(ReentryCap)`.
    pub(crate) max_reentries_per_query: u32,
    /// Session-persistent ledger entries (FIFO eviction).
    pub(crate) ledger_cap: usize,
    /// Entries returned per query (design F23).
    pub(crate) farkas_return_cap: usize,
    pub(crate) random_seed: u64,
    /// Reset the theory's ASSIGNMENT (`TheorySolver::soft_reset`: bounds,
    /// trails and simplex values; atom registrations and the tableau
    /// structure are kept) at the start of every query, so SAT models come
    /// from a cold simplex exactly as the legacy per-query solvers' do.
    ///
    /// Rung 1 integration finding (WP-4 `L2 on/off` lock): a warm simplex
    /// keeps its assignment across queries, so a strict bound reached from
    /// above materialises as `ub - δ` (e.g. `x = 3/2` for `x < 2`) where a
    /// cold solve sits at the other bound (`x = 1`). Both are valid models,
    /// but PDR's derivation-witness reconstruction
    /// (`pdr/verification/cex_entries.rs`) requires consecutive predecessor
    /// models to CHAIN through the head arguments, which the cold-solver
    /// behaviour delivers and the warm one does not — a small unsafe LRA
    /// problem lost its counterexample (500 "spurious" retries -> Unknown)
    /// with the warm assignment. Cost: one O(vars + rows) value reset per
    /// query plus the pivots a cold solve pays anyway (the SAT solver stays
    /// warm). Default on; `HornSmt::with_theory` (test mocks) turns it off.
    pub(crate) cold_theory_assignment: bool,
    /// Queries with more top-level conjuncts are refused
    /// (`Unsupported(ConversionBudget)`; mode 1 falls through to the legacy
    /// bridge): one-shot unrollings gain nothing from the session.
    pub(crate) max_query_conjuncts: usize,
}

impl SessionConfig {
    pub(crate) fn new() -> Self {
        Self {
            kill_after_queries: 4,
            rebuild_dead_vars: 4_096,
            rebuild_queries_after: 256,
            rebuild_terms_after: 200_000,
            hot_set_window: 16,
            max_mints_per_query: 10_000,
            max_model_eq_rounds: 20,
            max_reentries_per_query: 16,
            ledger_cap: 4_096,
            farkas_return_cap: 64,
            random_seed: 0,
            cold_theory_assignment: true,
            max_query_conjuncts: 4_096,
        }
    }
}

impl Default for SessionConfig {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum BudgetKind {
    Deadline,
    Interrupted,
    ConflictBudget,
    Memory,
    MintCap,
    ReentryCap,
    /// The CHC proof run's effort, its one count, was spent (P4a slice 8): a
    /// round's charge said stop, or the solve ran to the run's remainder.
    Effort,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnsupportedKind {
    Sort,
    Shape,
    ConversionBudget,
    IllTyped,
    DisequalityWithoutTerm,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum PoisonKind {
    EmptyCore,
    CoreOutsideQuery,
    InvalidSatModel,
    InvalidUnsatCore,
    EmptyTheoryConflict,
    ScopeMismatch,
    VarAliasing,
    ClauseTooLarge,
    /// ay-sat answered `Unknown` for a reason outside the budget/theory classes
    /// (`UnsupportedConfig`, proof-side failures, `Unspecified`): the solver
    /// profile is wrong for this session, so it is rebuilt.
    SolverUnknown,
}

/// Why a check did not decide. ONLY `Budget` is an allowed Unknown for the
/// exit criteria. `Unsupported`/`Poisoned` make the router fall through to the
/// legacy bridge; `TheoryIncomplete` is counted against the <5 % bar (and falls
/// through in mode 1). A theory `Unknown` observed while `should_stop()` is
/// true is `Budget`, never `TheoryIncomplete` (§3.5).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum UnknownReason {
    Budget(BudgetKind),
    Unsupported(UnsupportedKind),
    /// LRA `TheoryResult::Unknown` not at a deadline, an unmappable conflict
    /// literal, or the strict-verification demotion of a SAT model (the
    /// `missing assignment` class).
    TheoryIncomplete,
    /// An internal invariant tripped; the session is rebuilt before next use.
    Poisoned(PoisonKind),
}

/// Result of one online check.
#[must_use]
#[derive(Debug)]
pub(crate) enum HornCheck {
    /// Model over ORIGINAL CHC names (`own.var_original_names`). For
    /// `check_assuming` the model has already passed
    /// `verify_sat_model_conjunction_strict_with_mod_retry` over the active
    /// exprs; the shim's caller (the router) verifies the ORIGINAL expr instead.
    Sat(FxHashMap<String, SmtValue>),
    /// `core` ⊆ the `assuming` ids of this call (deactivated / inactive
    /// assertions never appear). `over_approximate` is set when ay-sat's
    /// #core-failsafe returned the full assumption list.
    Unsat {
        core: Vec<AssertId>,
        over_approximate: bool,
    },
    Unknown(UnknownReason),
}

/// Fixed-size log2 histogram of `u64` samples: bucket 0 holds 0, bucket `i >= 1`
/// holds `[2^(i-1), 2^i)`. Quantiles are bucket upper bounds — coarse but
/// allocation-free, enough for the board's median / p90 / p99 (§10.4).
#[derive(Debug, Clone)]
pub(crate) struct LogHistogram {
    buckets: [u64; 65],
    count: u64,
    sum: u64,
    max: u64,
}

impl Default for LogHistogram {
    fn default() -> Self {
        Self {
            buckets: [0; 65],
            count: 0,
            sum: 0,
            max: 0,
        }
    }
}

impl LogHistogram {
    pub(crate) fn record(&mut self, v: u64) {
        let bucket = v.bit_width() as usize;
        self.buckets[bucket] += 1;
        self.count += 1;
        self.sum = self.sum.saturating_add(v);
        self.max = self.max.max(v);
    }

    pub(crate) fn count(&self) -> u64 {
        self.count
    }

    pub(crate) fn sum(&self) -> u64 {
        self.sum
    }

    pub(crate) fn max(&self) -> u64 {
        self.max
    }

    /// Upper bound of the bucket holding the `q`-quantile sample (`q` in `[0, 1]`);
    /// 0 when empty.
    pub(crate) fn quantile(&self, q: f64) -> u64 {
        if self.count == 0 {
            return 0;
        }
        let target = ((q.clamp(0.0, 1.0) * self.count as f64).ceil() as u64).max(1);
        let mut seen = 0u64;
        for (i, &n) in self.buckets.iter().enumerate() {
            seen += n;
            if seen >= target {
                return match i {
                    0 => 0,
                    64.. => u64::MAX,
                    _ => (1u64 << i) - 1,
                };
            }
        }
        self.max
    }

    pub(crate) fn median(&self) -> u64 {
        self.quantile(0.5)
    }

    pub(crate) fn p90(&self) -> u64 {
        self.quantile(0.9)
    }

    pub(crate) fn p99(&self) -> u64 {
        self.quantile(0.99)
    }
}

/// Board counters (§2.1 list, §10.4). All `u64` unless noted.
#[derive(Debug, Clone, Default)]
pub(crate) struct SessionStats {
    pub(crate) queries: u64,
    pub(crate) sat: u64,
    pub(crate) unsat: u64,
    pub(crate) unknown_budget: u64,
    pub(crate) unknown_unsupported: u64,
    pub(crate) unknown_theory_incomplete: u64,
    pub(crate) unknown_poisoned: u64,
    pub(crate) strict_demotions: u64,
    pub(crate) missing_assignment: u64,
    pub(crate) assumptions_per_query: LogHistogram,
    pub(crate) decisions_per_query: LogHistogram,
    pub(crate) delta_conjuncts: u64,
    pub(crate) memo_hits_ptr: u64,
    pub(crate) memo_hits_struct: u64,
    pub(crate) memo_misses: u64,
    pub(crate) mints_split: u64,
    pub(crate) mints_diseq: u64,
    pub(crate) mints_expr: u64,
    pub(crate) mints_model_eq: u64,
    pub(crate) mints_originals: u64,
    pub(crate) reentries: u64,
    /// Gauge.
    pub(crate) dead_vars: u64,
    pub(crate) unit_kills: u64,
    pub(crate) rebuilds: u64,
    /// Read from `sat.ext_incremental_reset_hits()` as `lra/mod.rs` does.
    pub(crate) ext_incremental_reset_hits: u64,
    /// MUST stay 0 (design F2/F4; Rung-1 exit criterion).
    pub(crate) ext_full_reset_hits: u64,
    pub(crate) ledger_entries: u64,
    pub(crate) unsat_with_empty_ledger: u64,
    pub(crate) attributions_exact: u64,
    pub(crate) attributions_fallback: u64,
    /// Sum of strict-verification time.
    pub(crate) verify_us: u64,
    pub(crate) query_us: LogHistogram,
    /// MUST stay 0 (§7.4, lock L2).
    pub(crate) constructions_in_verification: u64,
    // --- folded from `BridgeStats` after every query (WP-2's board asks) ---
    /// BCP-time theory checks the bridge runs before opening a theory scope
    /// (WP-2 finding 1: LRA trails bounds in the scope of the check that
    /// applies them).
    pub(crate) scope_flushes: u64,
    /// §4.1 tripwire trips (same inline request thrice, unchanged assignment).
    pub(crate) tripwire_trips: u64,
    /// Re-entered solves that found the theory above scope 0 and popped it in
    /// `init()` (WP-2 finding 2; the between-query pop is `BridgeGuard`'s).
    pub(crate) init_pops: u64,
    /// Per-query theory assignment resets (`SessionConfig::cold_theory_assignment`).
    pub(crate) theory_resets: u64,
}

/// Read-only view of the session parts model extraction needs (contract C5,
/// amended in the skeleton): `model::extract` runs INSIDE the bridge guard
/// (§2.8 — the theory is still at the final scope), but at that moment
/// `TheoryBridge` holds `&mut` borrows of `theory`, `own` and `tseitin`, so a
/// `&HornSmt` cannot exist. The bridge lends this view
/// (`TheoryBridge::model_view`) between the solve and the guard's drop.
pub(crate) struct ModelView<'a> {
    pub(crate) own: &'a SmtContext,
    pub(crate) tseitin: &'a TseitinState,
    pub(crate) theory: &'a theory_box::TheoryBox,
    pub(crate) assertions: &'a [Assertion],
    pub(crate) cfg: &'a SessionConfig,
}

/// Result of `model::extract`: the model plus the counters the session folds
/// into `SessionStats`.
pub(crate) struct ModelExtract {
    pub(crate) model: FxHashMap<String, SmtValue>,
    /// Vars of ACTIVE assertions that had no theory value and were pure
    /// don't-cares (defaulted to 0); a non-don't-care miss is
    /// `Err(TheoryIncomplete)` instead.
    pub(crate) missing_assignment: u64,
}

/// The last `Unsat` this session produced: what `farkas_for_last_unsat` attributes.
struct LastUnsat {
    epoch: u64,
    active: Vec<AssertId>,
    core: Vec<AssertId>,
}

/// The session (§2.1). Field ORDER is the drop order: `theory` (which points
/// into the store) drops before `own`.
pub(crate) struct HornSmt {
    theory: theory_box::TheoryBox,
    /// Persists across solves (§2.4).
    bridge_state: bridge::BridgeState,
    /// Session-owned term universe. Boxed so `&own.terms` has a stable
    /// address; NEVER `own.reset()` (it replaces `terms`, `smt/context.rs`);
    /// append-only (no `rollback_to`).
    own: Box<SmtContext>,
    /// Taken / returned around each encode batch (design F10).
    tseitin: Option<TseitinState>,
    sat: ay_sat::Solver,
    assertions: Vec<Assertion>,
    by_key: FxHashMap<convert_memo::ConjunctKey, AssertId>,
    /// `Variable::index` of an activation var -> its assertion.
    act_to_assert: FxHashMap<u32, AssertId>,
    /// Logical push/pop: `assertions.len()` at each push.
    scopes: Vec<u32>,
    /// Per-atom count of LIVE assertions that mention it (don't-care filter input, §2.4).
    atom_live_refs: FxHashMap<TermId, u32>,
    ledger: ledger::FarkasLedger,
    memo: convert_memo::ConvertMemo,
    cfg: SessionConfig,
    stats: SessionStats,
    query_no: u64,
    dead_vars: usize,
    poisoned: Option<PoisonKind>,
    interrupt: Option<Arc<AtomicBool>>,
    // --- private bookkeeping beyond the §2.1 list (WP-1) ---
    /// Kept for `rebuild()` (the new store needs the same declarations).
    datatype_defs: Option<DatatypeDefs>,
    queries_since_rebuild: u64,
    /// Ring buffer of the active id-sets of the last `hot_set_window` queries (§6.4).
    recent_active: VecDeque<Vec<AssertId>>,
    /// Model of the last `Sat` (for `value()`); `None` otherwise.
    last_model: Option<FxHashMap<String, SmtValue>>,
    last_unsat: Option<LastUnsat>,
    /// `theory.warm_reuse_hint()` has been issued (once, after the first
    /// completed query; design F21).
    warm_hinted: bool,
}

impl HornSmt {
    /// Build the session: fresh `SmtContext` (with `datatype_defs`), Tseitin
    /// state, `ay_sat::Solver` in the `#lra-inc-engine` profile (§2.10), and
    /// the LRA theory.
    pub(crate) fn new(cfg: SessionConfig, datatype_defs: Option<&DatatypeDefs>) -> Self {
        Self::build(cfg, datatype_defs, theory_box::TheoryBox::new)
    }

    /// Test-only: a session over a caller-supplied theory (`TheoryBox::mock`),
    /// the injection hook the bridge unit tests and the Poison locks need.
    /// `rebuild()` builds its replacement with `new`, i.e. the LRA theory,
    /// not the mock.
    #[cfg(test)]
    pub(super) fn with_theory(cfg: SessionConfig, theory: theory_box::TheoryBox) -> Self {
        // Scripted mock theories count their calls; keep their call sequence
        // exactly what WP-1/WP-2 locked (no per-query `soft_reset`).
        let cfg = SessionConfig {
            cold_theory_assignment: false,
            ..cfg
        };
        Self::build(cfg, None, |_| theory)
    }

    fn build(
        cfg: SessionConfig,
        datatype_defs: Option<&DatatypeDefs>,
        make_theory: impl FnOnce(&mut SmtContext) -> theory_box::TheoryBox,
    ) -> Self {
        let mut own = Box::new(SmtContext::new());
        if let Some(defs) = datatype_defs {
            own.set_datatype_defs(defs.clone());
        }
        let sat = Self::new_sat(&cfg);
        let theory = make_theory(&mut own);
        let ledger_cap = cfg.ledger_cap;
        Self {
            theory,
            bridge_state: bridge::BridgeState::default(),
            own,
            tseitin: Some(TseitinState::new()),
            sat,
            assertions: Vec::new(),
            by_key: FxHashMap::default(),
            act_to_assert: FxHashMap::default(),
            scopes: Vec::new(),
            atom_live_refs: FxHashMap::default(),
            ledger: ledger::FarkasLedger::new(ledger_cap),
            memo: convert_memo::ConvertMemo::new(),
            cfg,
            stats: SessionStats::default(),
            query_no: 0,
            dead_vars: 0,
            poisoned: None,
            interrupt: None,
            datatype_defs: datatype_defs.cloned(),
            queries_since_rebuild: 0,
            recent_active: VecDeque::new(),
            last_model: None,
            last_unsat: None,
            warm_hinted: false,
        }
    }

    /// The `#lra-inc-engine` profile (§2.10, `ay-dpll/src/executor/theories/lra/mod.rs`),
    /// applied once per solver. Order matters: `set_ic3_mode` re-enables scoped
    /// BVE, so BVE is switched off AFTER it. `set_inc_engine_reset_mode(true)`
    /// is a HARD precondition of every between-solve add the session makes
    /// (design F3: the adds are deferred and attached by the incremental
    /// reset). NOT called: `set_unguarded_theory_conflict_lemmas` (inert on the
    /// assumption loop, F7), `enable_clause_trace`, `set_constrain_activation`.
    fn new_sat(cfg: &SessionConfig) -> ay_sat::Solver {
        let mut sat = ay_sat::Solver::new(0);
        sat.set_ic3_mode();
        sat.set_bve_enabled(false);
        sat.set_inc_engine_reset_mode(true);
        sat.set_random_seed(cfg.random_seed);
        sat.set_unsat_certificate_enabled(false);
        sat.set_preprocess_enabled(false);
        sat
    }

    /// Engine interrupt flag, forwarded to `sat.set_interrupt` and `should_stop`.
    pub(crate) fn set_interrupt(&mut self, flag: Arc<AtomicBool>) {
        self.sat.set_interrupt(Arc::clone(&flag));
        self.interrupt = Some(flag);
    }

    /// Assert a persistent conjunct. Idempotent on `ConjunctKey` (returns the
    /// existing live id; a `Dead` one is re-asserted under a NEW id — the kill
    /// unit is permanent). Eligibility (§2.6) is checked FIRST; a rejected
    /// conjunct asserts nothing.
    pub(crate) fn assert_persistent(
        &mut self,
        c: &Arc<ChcExpr>,
        partition: Partition,
    ) -> Result<AssertId, UnknownReason> {
        self.assert_with_origin(c, partition, AssertOrigin::Api)
    }

    /// The assertion path shared by the API (`Api`) and the shim (`Shim`).
    /// Allocation order (§3.1 step 4; INV-S6): normalise -> convert -> rebind
    /// -> Tseitin encode -> materialise the Tseitin vars -> `act = new_var()`
    /// -> re-sync `tseitin.next_var` -> definitions and `(root ∨ act)` as
    /// GLOBAL clauses (deferred under `inc_engine_reset_mode`, F3) -> register
    /// the new atoms with the theory and the bridge tables.
    pub(super) fn assert_with_origin(
        &mut self,
        c: &Arc<ChcExpr>,
        partition: Partition,
        origin: AssertOrigin,
    ) -> Result<AssertId, UnknownReason> {
        convert_memo::eligible(c, TheoryKind::Lra, convert_memo::Rung::Rung1)
            .map_err(UnknownReason::Unsupported)?;
        let key = convert_memo::ConvertMemo::key_of(c);
        if let Some(&id) = self.by_key.get(&key) {
            let a = &self.assertions[id.0 as usize];
            // Structural hit: confirm with `==` (Arc::ptr_eq fast path) — a
            // collision falls through to a fresh encoding, never a wrong reuse.
            if a.state == AssertState::Live && *a.expr == **c {
                self.note_used(id);
                return Ok(id);
            }
        }

        // Normalise under a namespace derived from the STRUCTURAL key so
        // re-encounters produce identical auxiliaries (§2.6).
        let convert_memo::ConjunctKey::Structural { h1, h2, .. } = key;
        let namespace = format!("s{h1:016x}{h2:016x}");
        let normalised = Arc::new(SmtContext::preprocess_incremental_assumption(c, &namespace));
        let (_, term) = self.memo.convert(&mut self.own, &normalised)?;
        self.stats.memo_hits_ptr = self.memo.hits_ptr;
        self.stats.memo_hits_struct = self.memo.hits_struct;
        self.stats.memo_misses = self.memo.misses;
        // The store was mutated by the conversion: re-point the theory (§5).
        self.theory.rebind(&mut self.own);

        // Tseitin (design F10): definitions are full equivalences, atoms are
        // reused through `term_to_var` across assertions and later mints.
        let state = self
            .tseitin
            .take()
            .expect("Tseitin state is returned after every encode batch");
        let mut ts = Tseitin::from_state(&self.own.terms, state);
        ts.ensure_min_next_var(SolverContext::num_vars(&self.sat) as u32 + 1);
        let enc = ts.encode_assertion(term);
        let mut state = ts.into_state();
        // Materialise the Tseitin vars FIRST, THEN the activation var, then
        // keep the encoder strictly above `act` (no aliasing, INV-S6).
        self.sat
            .ensure_num_vars(state.next_var.saturating_sub(1) as usize);
        let act = self.sat.new_var();
        self.sat.set_var_phase(act, true);
        state.next_var = SolverContext::num_vars(&self.sat) as u32 + 1;
        debug_assert_eq!(
            state.next_var as usize,
            SolverContext::num_vars(&self.sat) + 1,
            "session invariant: the encoder's next_var is num_vars + 1 at every boundary"
        );
        let root_lit = Literal::from_dimacs(enc.root_lit);
        for clause in &enc.def_clauses {
            self.sat
                .add_clause_global(clause.0.iter().map(|&l| Literal::from_dimacs(l)).collect());
        }
        self.sat
            .add_clause_global(vec![root_lit, Literal::positive(act)]);

        // Atoms and variables reachable from the term; bridge tables; theory.
        let (atoms, arith_vars, bool_vars) = Self::scan_term(&self.own.terms, term);
        let num_vars = SolverContext::num_vars(&self.sat);
        Self::grow_bridge_tables(&mut self.bridge_state, num_vars);
        if session_trace() {
            ay_core::safe_eprintln!(
                "[CHC-SESSION-TRACE] assert id={} act={act:?} root_lit={} expr={}",
                self.assertions.len(),
                enc.root_lit,
                crate::InvariantModel::expr_to_smtlib(c),
            );
        }
        for &atom in &atoms {
            if let Some(&dimacs_var) = state.term_to_var.get(&atom) {
                let vi = (dimacs_var - 1) as usize;
                self.bridge_state.atom_of_var[vi] = Some(atom);
                if !self.bridge_state.registered[vi] {
                    self.bridge_state.registered[vi] = true;
                    self.theory.as_dyn().register_atom(atom);
                }
            }
            *self.atom_live_refs.entry(atom).or_insert(0) += 1;
            self.ledger.tag(atom, partition);
        }
        self.tseitin = Some(state);

        let id = AssertId(self.assertions.len() as u32);
        self.assertions.push(Assertion {
            expr: Arc::clone(c),
            key,
            term,
            root_lit,
            act,
            atoms,
            arith_vars,
            bool_vars,
            partition,
            scope: self.scopes.len() as u32,
            origin,
            last_used_query: self.query_no,
            state: AssertState::Live,
        });
        self.by_key.insert(key, id);
        self.act_to_assert.insert(act.index() as u32, id);
        Ok(id)
    }

    /// Theory atoms (`is_theory_atom`) and Int/Real / Bool variables reachable
    /// from `root`, each sorted and de-duplicated.
    fn scan_term(terms: &TermStore, root: TermId) -> (Vec<TermId>, Vec<TermId>, Vec<TermId>) {
        let mut atom_set: FxHashSet<TermId> = FxHashSet::default();
        collect_theory_atoms_into(terms, [root], &mut atom_set);
        let mut arith = Vec::new();
        let mut bools = Vec::new();
        let mut seen: FxHashSet<TermId> = FxHashSet::default();
        let mut stack = vec![root];
        while let Some(t) = stack.pop() {
            if !seen.insert(t) {
                continue;
            }
            match terms.get(t) {
                TermData::Var(..) => match terms.sort(t) {
                    Sort::Int | Sort::Real => arith.push(t),
                    Sort::Bool => bools.push(t),
                    _ => {}
                },
                TermData::Const(_) => {}
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, a, b) => {
                    stack.push(*c);
                    stack.push(*a);
                    stack.push(*b);
                }
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Let(bindings, body) => {
                    stack.extend(bindings.iter().map(|(_, t)| *t));
                    stack.push(*body);
                }
                TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
                // `TermData` is `#[non_exhaustive]`; an unknown node kind has no
                // children this scan knows how to name.
                _ => {}
            }
        }
        let mut atoms: Vec<TermId> = atom_set.into_iter().collect();
        atoms.sort_unstable();
        arith.sort_unstable();
        arith.dedup();
        bools.sort_unstable();
        bools.dedup();
        (atoms, arith, bools)
    }

    /// Dense bridge tables cover every SAT variable (Tseitin, activation and
    /// minted alike); grown, never shrunk, for the solver's life.
    fn grow_bridge_tables(st: &mut bridge::BridgeState, num_vars: usize) {
        if st.atom_of_var.len() < num_vars {
            st.atom_of_var.resize(num_vars, None);
        }
        if st.active_atom.len() < num_vars {
            st.active_atom.resize(num_vars, false);
        }
        if st.l0_fed.len() < num_vars {
            st.l0_fed.resize(num_vars, false);
        }
        if st.registered.len() < num_vars {
            st.registered.resize(num_vars, false);
        }
    }

    /// Logical scope over activation literals. NO `ay_sat::push()`.
    pub(crate) fn push(&mut self) {
        self.scopes.push(self.assertions.len() as u32);
    }

    /// Retract every assertion asserted since the matching push: state =
    /// `Dead`, `add_clause_global([+act])` (deferred, attached at the next
    /// incremental reset — design F3), removed from `by_key` / `atom_live_refs`.
    /// Returns `false` when there is no scope to pop.
    pub(crate) fn pop(&mut self) -> bool {
        let Some(start) = self.scopes.pop() else {
            return false;
        };
        for i in start..self.assertions.len() as u32 {
            self.kill_assertion(AssertId(i));
        }
        true
    }

    pub(crate) fn scope_depth(&self) -> usize {
        self.scopes.len()
    }

    /// The online check. `assuming` = ids to activate (assumption `¬act`); ids
    /// NOT listed are simply not assumed. `extra` = one-shot conjuncts encoded
    /// under fresh activation vars that are unit-killed right after the call.
    /// Effective deadline = §3.5. SAT models are verified strictly against the
    /// exprs of `assuming ∪ extra` before being returned (a failure is
    /// `Unknown(TheoryIncomplete)`, `strict_demotions += 1`; INV-S3).
    pub(crate) fn check_assuming(
        &mut self,
        assuming: &[AssertId],
        extra: &[Arc<ChcExpr>],
        budget: Option<Duration>,
    ) -> HornCheck {
        match self.check_assuming_unverified(assuming, extra, budget) {
            HornCheck::Sat(model) => {
                let started = Instant::now();
                let exprs: Vec<&ChcExpr> = assuming
                    .iter()
                    .map(|id| &*self.assertions[id.0 as usize].expr)
                    .chain(extra.iter().map(|e| &**e))
                    .collect();
                let verdict = verify_sat_model_conjunction_strict_with_mod_retry(
                    exprs.iter().copied(),
                    &model,
                );
                if matches!(verdict, ModelVerifyResult::Valid) {
                    self.stats.verify_us += started.elapsed().as_micros() as u64;
                    return HornCheck::Sat(model);
                }
                // Same completion the router applies (`sat_or_unknown`): a
                // variable the normaliser folded away (a tautological
                // conjunct such as `x = x` or `b ∨ ¬b`) has no theory value,
                // so the strict evaluator is Indeterminate on it; the
                // scalar-default completion re-verifies the ORIGINAL exprs
                // and accepts only a `Valid` witness (WP-4 fuzz: 2 % of the
                // push/pop checks were demoted on exactly this shape).
                let conj = ChcExpr::and_all(exprs.iter().map(|e| (*e).clone()));
                let completed = SmtContext::sat_or_unknown(&conj, model, "horn-session-api");
                self.stats.verify_us += started.elapsed().as_micros() as u64;
                match completed {
                    crate::smt::types::SmtResult::Sat(model) => {
                        self.last_model = Some(model.clone());
                        HornCheck::Sat(model)
                    }
                    _ => {
                        self.stats.strict_demotions += 1;
                        self.last_model = None;
                        HornCheck::Unknown(UnknownReason::TheoryIncomplete)
                    }
                }
            }
            other => other,
        }
    }

    /// Raw variant used by the shim (the router runs `sat_or_unknown` on the
    /// ORIGINAL expr instead). Drives the re-entry protocol (§4.2) and maps the
    /// ay-sat result (§3.1 step 7) under a `BridgeGuard`.
    pub(crate) fn check_assuming_unverified(
        &mut self,
        assuming: &[AssertId],
        extra: &[Arc<ChcExpr>],
        budget: Option<Duration>,
    ) -> HornCheck {
        if self.should_rebuild() {
            // The ids of THIS query are part of the hot set whatever their
            // origin or age: a rebuild here must never tombstone what the
            // caller is about to check (WP-3 hazard H1).
            self.rebuild_keeping(assuming);
        }
        let started = Instant::now();
        self.query_no += 1;
        self.queries_since_rebuild += 1;
        self.stats.queries += 1;
        self.last_model = None;
        self.last_unsat = None;

        // §3.5: the deadline is folded BEFORE the solver is touched; an already
        // expired SMT deadline is the legacy-identical instant Unknown.
        let deadline = self.effective_deadline(budget);
        if crate::smt::smt_deadline_expired() || deadline.is_some_and(|d| Instant::now() >= d) {
            let outcome = HornCheck::Unknown(UnknownReason::Budget(BudgetKind::Deadline));
            return self.finish(outcome, started, Vec::new());
        }

        // One-shot conjuncts: fresh activation vars, killed after the call
        // (an `extra` that is already live keeps its id and is NOT killed).
        let mut extra_fresh: Vec<AssertId> = Vec::new();
        let mut active: Vec<AssertId> = assuming.to_vec();
        for e in extra {
            let before = self.assertions.len();
            match self.assert_with_origin(e, Partition::AB, AssertOrigin::Api) {
                Ok(id) => {
                    if id.0 as usize >= before {
                        extra_fresh.push(id);
                    }
                    active.push(id);
                }
                Err(reason) => {
                    for id in extra_fresh {
                        self.kill_assertion(id);
                    }
                    return self.finish(HornCheck::Unknown(reason), started, Vec::new());
                }
            }
        }
        active.sort_unstable();
        active.dedup();
        let not_live = active.iter().copied().find(|id| {
            !self
                .assertions
                .get(id.0 as usize)
                .is_some_and(|a| a.state == AssertState::Live)
        });
        if let Some(id) = not_live {
            // A dead/tombstoned/unknown id is a caller bug: the id was popped,
            // killed or belongs to a previous rebuild's world.
            debug_assert!(false, "check_assuming: {id:?} is not a live assertion");
            self.poisoned = Some(PoisonKind::ScopeMismatch);
            for id in extra_fresh {
                self.kill_assertion(id);
            }
            let outcome = HornCheck::Unknown(UnknownReason::Poisoned(PoisonKind::ScopeMismatch));
            return self.finish(outcome, started, active);
        }
        for &id in &active {
            self.note_used(id);
        }

        self.fill_active_atoms(&active);
        if self.cfg.cold_theory_assignment {
            // Cold simplex assignment per query (see `SessionConfig`): the
            // theory is at scope 0 here (the previous query's `BridgeGuard`
            // popped it), so only values/bounds go; registrations stay, and
            // the level-0 facts are re-fed because `l0_fed` is cleared.
            self.theory.rebind(&mut self.own);
            self.theory.as_dyn().soft_reset();
            self.bridge_state.on_theory_assignment_reset();
            self.stats.theory_resets += 1;
        }
        let outcome = self.run_query(&active, deadline);
        for id in extra_fresh {
            self.kill_assertion(id);
        }
        self.finish(outcome, started, active)
    }

    /// Effective deadline (§3.5): min(caller budget, `check_timeout`,
    /// `global_deadline`, thread solve deadline, scoped SMT deadline).
    fn effective_deadline(&self, budget: Option<Duration>) -> Option<Instant> {
        let now = Instant::now();
        let mut deadline: Option<Instant> = None;
        let mut fold = |d: Option<Instant>| {
            if let Some(d) = d {
                deadline = Some(deadline.map_or(d, |cur| cur.min(d)));
            }
        };
        fold(budget.map(|b| now + b));
        fold(self.own.check_timeout.get().map(|t| now + t));
        fold(self.own.global_deadline.get());
        fold(crate::smt::current_thread_solve_deadline());
        fold(crate::smt::deadline::current_smt_deadline());
        deadline
    }

    /// Don't-care filter input (§2.4, §6.2): `active_atom[v]` for the atoms of
    /// the ACTIVE assertions only. O(active atoms) plus one byte-fill.
    fn fill_active_atoms(&mut self, active: &[AssertId]) {
        let num_vars = SolverContext::num_vars(&self.sat);
        Self::grow_bridge_tables(&mut self.bridge_state, num_vars);
        let st = &mut self.bridge_state;
        st.active_atom.fill(false);
        let Some(ts) = self.tseitin.as_ref() else {
            return;
        };
        for &id in active {
            for &atom in &self.assertions[id.0 as usize].atoms {
                if let Some(&dimacs_var) = ts.term_to_var.get(&atom) {
                    let vi = (dimacs_var - 1) as usize;
                    if vi < st.active_atom.len() {
                        st.active_atom[vi] = true;
                    }
                }
            }
        }
    }

    /// One query against the solver: the re-entry loop (§4.2) and the result
    /// mapping (§3.1 step 7), all inside the `BridgeGuard` (model extraction
    /// included). Disjoint field borrows: the bridge takes `theory`, `own`,
    /// `tseitin`, `bridge_state`, `ledger`, `cfg`; this function keeps `sat`,
    /// `assertions`, `stats`, `poisoned`, `act_to_assert`, `last_*`.
    fn run_query(&mut self, active: &[AssertId], deadline: Option<Instant>) -> HornCheck {
        let assumptions: Vec<Literal> = active
            .iter()
            .map(|id| Literal::negative(self.assertions[id.0 as usize].act))
            .collect();
        self.stats
            .assumptions_per_query
            .record(assumptions.len() as u64);
        self.sat.set_solve_deadline(deadline);
        let interrupt = self.interrupt.clone();
        let should_stop = move || {
            ay_core::resource::note_sat_stop_poll();
            deadline.is_some_and(|d| Instant::now() >= d)
                || TermStore::global_memory_exceeded()
                || interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(Ordering::Relaxed))
        };
        let decisions_before = SolverContext::decisions(&self.sat);
        let epoch = self.query_no;
        let max_reentries = self.cfg.max_reentries_per_query;

        let Self {
            theory,
            own,
            tseitin,
            bridge_state,
            ledger,
            cfg,
            sat,
            assertions,
            stats,
            poisoned,
            act_to_assert,
            last_model,
            last_unsat,
            ..
        } = self;
        let parts = bridge::BridgeParts {
            theory,
            own,
            tseitin,
            st: bridge_state,
            ledger,
            epoch,
            cfg,
            deadline,
            should_stop: &should_stop,
            phase_seed: None,
        };
        let mut bridge = bridge::TheoryBridge::new(parts);
        let mut guard = BridgeGuard::new(&mut bridge);
        let mut reentries = 0u32;
        let outcome = loop {
            if crate::run_meter::charge(crate::run_meter::Step::TheoryRound).is_err() {
                break HornCheck::Unknown(UnknownReason::Budget(BudgetKind::Effort));
            }
            let result = crate::run_meter::sat_solve(sat, |sat| {
                sat.solve_with_extension_and_assumptions_core(
                    guard.bridge(),
                    &assumptions,
                    Some(&should_stop),
                )
            });
            match result.into_inner() {
                AssumeResult::Sat(sat_model) => {
                    // Inside the guard: the theory is still at the final scope.
                    let view = guard.bridge().model_view(assertions.as_slice());
                    break match model::extract(&view, &sat_model, active) {
                        Ok(extracted) => {
                            stats.missing_assignment += extracted.missing_assignment;
                            *last_model = Some(extracted.model.clone());
                            HornCheck::Sat(extracted.model)
                        }
                        Err(reason) => HornCheck::Unknown(reason),
                    };
                }
                AssumeResult::Unsat(core, _) => {
                    break Self::map_core(
                        &core,
                        assumptions.len(),
                        active,
                        act_to_assert,
                        last_unsat,
                        epoch,
                        poisoned,
                    );
                }
                AssumeResult::Unknown => {
                    let poison = |kind: PoisonKind, poisoned: &mut Option<PoisonKind>| {
                        *poisoned = Some(kind);
                        HornCheck::Unknown(UnknownReason::Poisoned(kind))
                    };
                    match sat.last_unknown_reason() {
                        Some(SatUnknownReason::DeadlineExceeded) => {
                            break HornCheck::Unknown(UnknownReason::Budget(BudgetKind::Deadline));
                        }
                        Some(SatUnknownReason::Interrupted) => {
                            break HornCheck::Unknown(UnknownReason::Budget(Self::classify_stop(
                                deadline,
                            )));
                        }
                        Some(SatUnknownReason::ResourceBudget) => {
                            // Under an effort the solve's tick stop is the
                            // run's remainder, and its charge latched the stop.
                            let kind = if crate::run_meter::run_stopped() {
                                BudgetKind::Effort
                            } else {
                                BudgetKind::ConflictBudget
                            };
                            break HornCheck::Unknown(UnknownReason::Budget(kind));
                        }
                        Some(SatUnknownReason::TheoryStop | SatUnknownReason::ExtensionUnknown) => {
                            match guard.bridge().exit() {
                                bridge::BridgeExit::RestartWithOriginals => {
                                    reentries += 1;
                                    stats.reentries += 1;
                                    if reentries > max_reentries {
                                        break HornCheck::Unknown(UnknownReason::Budget(
                                            BudgetKind::ReentryCap,
                                        ));
                                    }
                                    // Tier 2: ORIGINAL clauses, deferred and attached
                                    // by the next incremental reset (F3); then re-enter
                                    // with the same assumptions. The bridge handed the
                                    // same clauses to ay-sat as `AddClauses` first (WP-2
                                    // finding 3): `add_theory_lemma` grows the solver to
                                    // the minted variables, which `add_clause_global`
                                    // does not; its deletable copies are subsumed by
                                    // these irredundant ones. The exit then arrives as
                                    // `TheoryStop` (the next `propagate` stops) rather
                                    // than `ExtensionUnknown`; both land here.
                                    let originals = guard.bridge().take_originals();
                                    stats.mints_originals += originals.len() as u64;
                                    for clause in originals {
                                        sat.add_clause_global(clause);
                                    }
                                    continue;
                                }
                                bridge::BridgeExit::Budget(kind) => {
                                    break HornCheck::Unknown(UnknownReason::Budget(kind));
                                }
                                bridge::BridgeExit::TheoryIncomplete => {
                                    break HornCheck::Unknown(UnknownReason::TheoryIncomplete);
                                }
                                bridge::BridgeExit::Unsupported(kind) => {
                                    break HornCheck::Unknown(UnknownReason::Unsupported(kind));
                                }
                                bridge::BridgeExit::Poison(kind) => break poison(kind, poisoned),
                                bridge::BridgeExit::None => {
                                    // The bridge stopped the solve without a verdict:
                                    // a stop while `should_stop()` holds is Budget
                                    // (§3.5), anything else is theory incompleteness.
                                    break if should_stop() {
                                        HornCheck::Unknown(UnknownReason::Budget(
                                            Self::classify_stop(deadline),
                                        ))
                                    } else {
                                        HornCheck::Unknown(UnknownReason::TheoryIncomplete)
                                    };
                                }
                            }
                        }
                        Some(SatUnknownReason::InvalidSatModel) => {
                            // F17: `finalize_sat_fail_count` is sticky for the solver's
                            // life; the rebuild replaces the solver.
                            break poison(PoisonKind::InvalidSatModel, poisoned);
                        }
                        Some(SatUnknownReason::InvalidUnsatCore) => {
                            break poison(PoisonKind::InvalidUnsatCore, poisoned);
                        }
                        Some(SatUnknownReason::EmptyTheoryConflict) => {
                            break poison(PoisonKind::EmptyTheoryConflict, poisoned);
                        }
                        Some(SatUnknownReason::ClauseTooLarge) => {
                            break poison(PoisonKind::ClauseTooLarge, poisoned);
                        }
                        _ => break poison(PoisonKind::SolverUnknown, poisoned),
                    }
                }
                _ => break poison_unknown(poisoned),
            }
        };
        drop(guard);
        // Agreement between the two scope-restoring sites: the guard pops the
        // theory to scope 0 between queries (just now); the bridge's `init()`
        // pops whatever a previous solve of the SAME query left (re-entry,
        // WP-2 finding 2). After the guard nothing may remain.
        debug_assert_eq!(
            bridge.theory_level(),
            0,
            "BridgeGuard left the theory above scope 0"
        );
        {
            let bs = bridge.stats();
            if session_trace() {
                ay_core::safe_eprintln!(
                    "[CHC-SESSION-TRACE] query={} outcome={} {bs:?}",
                    epoch,
                    match &outcome {
                        HornCheck::Sat(_) => "sat",
                        HornCheck::Unsat { .. } => "unsat",
                        HornCheck::Unknown(_) => "unknown",
                    }
                );
            }
            stats.mints_diseq += bs.mints_diseq;
            stats.mints_expr += bs.mints_expr;
            stats.mints_model_eq += bs.mints_model_eq;
            stats.scope_flushes += bs.scope_flushes;
            stats.tripwire_trips += bs.tripwire_trips;
            stats.init_pops += bs.init_pops;
        }
        drop(bridge);
        stats
            .decisions_per_query
            .record(SolverContext::decisions(sat).saturating_sub(decisions_before));
        stats.ext_incremental_reset_hits = sat.ext_incremental_reset_hits();
        stats.ext_full_reset_hits = sat.ext_full_reset_hits();
        outcome
    }

    /// Which budget a cooperative stop was: the deadline if it has passed,
    /// memory if the store tripped, else the engine's interrupt flag.
    fn classify_stop(deadline: Option<Instant>) -> BudgetKind {
        if deadline.is_some_and(|d| Instant::now() >= d) {
            BudgetKind::Deadline
        } else if TermStore::global_memory_exceeded() {
            BudgetKind::Memory
        } else {
            BudgetKind::Interrupted
        }
    }

    /// Map ay-sat's failed-assumption core to `AssertId`s (§3.1 step 7): every
    /// literal must be the `¬act` of an ACTIVE assertion of THIS query (an
    /// inactive `act` is never assumed and scope selectors do not exist), else
    /// `Poisoned(CoreOutsideQuery)`; an empty core is `Poisoned(EmptyCore)`
    /// (INV-S5: the DB is satisfiable by construction). `over_approximate`
    /// flags a core equal to the full assumption list — ay-sat's #core-failsafe
    /// returns exactly that list, and it is not distinguishable from a genuine
    /// full core here.
    fn map_core(
        core: &[Literal],
        num_assumptions: usize,
        active: &[AssertId],
        act_to_assert: &FxHashMap<u32, AssertId>,
        last_unsat: &mut Option<LastUnsat>,
        epoch: u64,
        poisoned: &mut Option<PoisonKind>,
    ) -> HornCheck {
        if core.is_empty() {
            *poisoned = Some(PoisonKind::EmptyCore);
            return HornCheck::Unknown(UnknownReason::Poisoned(PoisonKind::EmptyCore));
        }
        let mut ids: Vec<AssertId> = Vec::with_capacity(core.len());
        for lit in core {
            let id = act_to_assert.get(&(lit.variable().index() as u32)).copied();
            match id {
                Some(id) if !lit.is_positive() && active.binary_search(&id).is_ok() => ids.push(id),
                _ => {
                    *poisoned = Some(PoisonKind::CoreOutsideQuery);
                    return HornCheck::Unknown(UnknownReason::Poisoned(
                        PoisonKind::CoreOutsideQuery,
                    ));
                }
            }
        }
        ids.sort_unstable();
        ids.dedup();
        let over_approximate = num_assumptions > 1 && ids.len() == active.len();
        *last_unsat = Some(LastUnsat {
            epoch,
            active: active.to_vec(),
            core: ids.clone(),
        });
        HornCheck::Unsat {
            core: ids,
            over_approximate,
        }
    }

    /// Per-query bookkeeping on every exit path of `check_assuming_unverified`.
    fn finish(&mut self, outcome: HornCheck, started: Instant, active: Vec<AssertId>) -> HornCheck {
        match &outcome {
            HornCheck::Sat(_) => self.stats.sat += 1,
            HornCheck::Unsat { .. } => self.stats.unsat += 1,
            HornCheck::Unknown(UnknownReason::Budget(_)) => self.stats.unknown_budget += 1,
            HornCheck::Unknown(UnknownReason::Unsupported(_)) => {
                self.stats.unknown_unsupported += 1
            }
            HornCheck::Unknown(UnknownReason::TheoryIncomplete) => {
                self.stats.unknown_theory_incomplete += 1;
            }
            HornCheck::Unknown(UnknownReason::Poisoned(_)) => self.stats.unknown_poisoned += 1,
        }
        self.stats
            .query_us
            .record(started.elapsed().as_micros() as u64);
        self.stats.ledger_entries = self.ledger.len() as u64;
        self.stats.dead_vars = self.dead_vars as u64;
        if !self.warm_hinted && matches!(outcome, HornCheck::Sat(_) | HornCheck::Unsat { .. }) {
            // Once, after the first completed query (design F21).
            self.theory.warm_reuse_hint();
            self.warm_hinted = true;
        }
        if !active.is_empty() {
            self.recent_active.push_back(active);
            while self.recent_active.len() as u64 > self.cfg.hot_set_window.max(1) {
                self.recent_active.pop_front();
            }
        }
        outcome
    }

    // `check_conjunction` (the compatibility shim, §2.7) is defined in
    // `shim.rs` (WP-3) as an inherent method of this type.

    /// Value of an expression in the LAST `Sat` model (`None` if the last
    /// result was not `Sat`, or the expression does not evaluate under it).
    pub(crate) fn value(&self, expr: &ChcExpr) -> Option<SmtValue> {
        self.last_model
            .as_ref()
            .and_then(|model| crate::expr::evaluate_expr(expr, model))
    }

    /// Farkas conflicts attributed to the LAST `Unsat` (Rung 3; `a`/`b` give
    /// the `Partition` view). Rung 1 records the ledger but attributes nothing:
    /// this returns an empty vector until `FarkasLedger::attribute` lands.
    pub(crate) fn farkas_for_last_unsat(
        &mut self,
        _a: &[AssertId],
        _b: &[AssertId],
    ) -> Vec<FarkasConflict> {
        if self.last_unsat.is_none() {
            return Vec::new();
        }
        if self.ledger.is_empty() {
            self.stats.unsat_with_empty_ledger += 1;
        }
        Vec::new()
    }

    /// Rebuild policy (§6.4).
    pub(crate) fn should_rebuild(&self) -> bool {
        self.poisoned.is_some()
            || self.dead_vars > self.cfg.rebuild_dead_vars
            || self.queries_since_rebuild >= self.cfg.rebuild_queries_after
            || self.own.terms.len() > self.cfg.rebuild_terms_after
    }

    /// Construct a NEW session (store, Tseitin state, solver, theory) and
    /// re-assert the hot set in `AssertId` order under the SAME ids; every
    /// other entry becomes a `Tombstone`. Ledger and memo start empty;
    /// cumulative stats, the logical scope stack and the query counter carry
    /// over. The old session is dropped only after the new one is complete.
    ///
    /// Hot set (§6.4, plus the H1 rule): live `Api`-origin assertions;
    /// `Shim`-origin assertions active in any of the last `hot_set_window`
    /// queries; and every LIVE assertion STAGED FOR THE QUERY IN FLIGHT —
    /// `last_used_query >= query_no`, the stamp `assert_with_origin` gives a
    /// conjunct asserted after the previous query ended and before the next
    /// one is numbered. A rebuild must never drop what a caller has staged and
    /// is about to check; `check_assuming_unverified` additionally passes the
    /// ids it was handed (`rebuild_keeping`).
    pub(crate) fn rebuild(&mut self) {
        self.rebuild_keeping(&[]);
    }

    /// `rebuild` with an explicit keep-set: the ids of the check that
    /// triggered it are re-asserted under their ids whatever their origin,
    /// age or window position.
    fn rebuild_keeping(&mut self, keep: &[AssertId]) {
        let live = |a: &Assertion| a.state == AssertState::Live;
        let mut hot: FxHashSet<AssertId> = FxHashSet::default();
        for (i, a) in self.assertions.iter().enumerate() {
            if live(a) && (a.origin == AssertOrigin::Api || a.last_used_query >= self.query_no) {
                hot.insert(AssertId(i as u32));
            }
        }
        for id in self.recent_active.iter().flatten().chain(keep) {
            if self.assertions.get(id.0 as usize).is_some_and(live) {
                hot.insert(*id);
            }
        }

        let mut fresh = Self::new(self.cfg.clone(), self.datatype_defs.as_ref());
        if let Some(flag) = &self.interrupt {
            fresh.set_interrupt(Arc::clone(flag));
        }
        fresh.query_no = self.query_no;
        for (i, a) in self.assertions.iter().enumerate() {
            let id = AssertId(i as u32);
            let expected = fresh.assertions.len();
            debug_assert_eq!(expected, i, "rebuild keeps AssertIds aligned");
            if hot.contains(&id) {
                if let Ok(new_id) = fresh.assert_with_origin(&a.expr, a.partition, a.origin) {
                    if new_id.0 as usize == expected {
                        let entry = &mut fresh.assertions[expected];
                        entry.scope = a.scope;
                        entry.last_used_query = a.last_used_query;
                        continue;
                    }
                    // Structural duplicate of an earlier hot entry: this id
                    // aliases it from now on; leave a tombstone at this index.
                }
            }
            fresh.assertions.push(Assertion {
                expr: Arc::clone(&a.expr),
                key: a.key,
                term: a.term,
                root_lit: a.root_lit,
                act: a.act,
                atoms: Vec::new(),
                arith_vars: Vec::new(),
                bool_vars: Vec::new(),
                partition: a.partition,
                scope: a.scope,
                origin: a.origin,
                last_used_query: a.last_used_query,
                state: AssertState::Tombstone,
            });
        }
        fresh.scopes = self.scopes.clone();
        fresh.recent_active = self.recent_active.clone();
        fresh.stats = self.stats.clone();
        fresh.stats.rebuilds += 1;
        fresh.stats.dead_vars = 0;
        fresh.warm_hinted = false;
        *self = fresh;
    }

    pub(crate) fn stats(&self) -> &SessionStats {
        &self.stats
    }

    pub(crate) fn is_poisoned(&self) -> bool {
        self.poisoned.is_some()
    }

    // ---- C1: accessors for WP-2 / WP-3 (no field access across files) ----

    pub(super) fn own(&self) -> &SmtContext {
        &self.own
    }

    pub(super) fn own_mut(&mut self) -> &mut SmtContext {
        &mut self.own
    }

    pub(super) fn tseitin(&self) -> &Option<TseitinState> {
        &self.tseitin
    }

    pub(super) fn tseitin_mut(&mut self) -> &mut Option<TseitinState> {
        &mut self.tseitin
    }

    pub(super) fn theory(&self) -> &theory_box::TheoryBox {
        &self.theory
    }

    pub(super) fn theory_mut(&mut self) -> &mut theory_box::TheoryBox {
        &mut self.theory
    }

    pub(super) fn bridge_state(&self) -> &bridge::BridgeState {
        &self.bridge_state
    }

    pub(super) fn bridge_state_mut(&mut self) -> &mut bridge::BridgeState {
        &mut self.bridge_state
    }

    pub(super) fn assertions(&self) -> &[Assertion] {
        &self.assertions
    }

    pub(super) fn assertions_mut(&mut self) -> &mut [Assertion] {
        &mut self.assertions
    }

    pub(super) fn assertion(&self, id: AssertId) -> &Assertion {
        &self.assertions[id.0 as usize]
    }

    pub(super) fn atom_live_refs(&self) -> &FxHashMap<TermId, u32> {
        &self.atom_live_refs
    }

    pub(super) fn by_key(&self) -> &FxHashMap<convert_memo::ConjunctKey, AssertId> {
        &self.by_key
    }

    pub(super) fn memo_mut(&mut self) -> &mut convert_memo::ConvertMemo {
        &mut self.memo
    }

    pub(super) fn ledger(&self) -> &ledger::FarkasLedger {
        &self.ledger
    }

    pub(super) fn ledger_mut(&mut self) -> &mut ledger::FarkasLedger {
        &mut self.ledger
    }

    pub(super) fn cfg(&self) -> &SessionConfig {
        &self.cfg
    }

    pub(super) fn stats_mut(&mut self) -> &mut SessionStats {
        &mut self.stats
    }

    /// Number of the query in flight (1-based; the ledger epoch).
    pub(super) fn query_no(&self) -> u64 {
        self.query_no
    }

    /// Unit-kill a LIVE assertion (the retention step, §2.7 step 6, and
    /// `pop`): state = `Dead`, `add_clause_global([+act])` (deferred, F3),
    /// removed from `by_key` / `atom_live_refs`, `dead_vars += vars(assertion)`,
    /// `stats.unit_kills += 1`. No-op on a `Dead`/`Tombstone` entry.
    pub(super) fn kill_assertion(&mut self, id: AssertId) {
        let idx = id.0 as usize;
        let (act, key, vars) = {
            let Some(entry) = self.assertions.get_mut(idx) else {
                return;
            };
            if entry.state != AssertState::Live {
                return;
            }
            entry.state = AssertState::Dead;
            (
                entry.act,
                entry.key,
                1 + entry.atoms.len() + entry.bool_vars.len(),
            )
        };
        // The unit is a GLOBAL clause: deferred now, attached by the next
        // incremental reset (F3); every learned clause mentioning ¬act is
        // satisfied by it and the rest stay implied.
        self.sat.add_clause_global(vec![Literal::positive(act)]);
        if self.by_key.get(&key) == Some(&id) {
            self.by_key.remove(&key);
        }
        for atom in &self.assertions[idx].atoms {
            if let Some(n) = self.atom_live_refs.get_mut(atom) {
                *n = n.saturating_sub(1);
                if *n == 0 {
                    self.atom_live_refs.remove(atom);
                }
            }
        }
        self.dead_vars += vars;
        self.stats.unit_kills += 1;
        self.stats.dead_vars = self.dead_vars as u64;
    }

    /// Mark `id` active in the query in flight (shim LRU stamp).
    pub(super) fn note_used(&mut self, id: AssertId) {
        let stamp = self.query_no;
        self.assertions[id.0 as usize].last_used_query = stamp;
    }
}

/// `Poisoned(SolverUnknown)` for an `AssumeResult` variant this crate does not
/// know (the enum is `#[non_exhaustive]`).
fn poison_unknown(poisoned: &mut Option<PoisonKind>) -> HornCheck {
    *poisoned = Some(PoisonKind::SolverUnknown);
    HornCheck::Unknown(UnknownReason::Poisoned(PoisonKind::SolverUnknown))
}

/// Drop guard created by `run_query` around ONE query: on every exit path —
/// including early `Unknown(Budget)` returns — it pops the theory to scope 0
/// through `bridge.backtrack(0)` (§2.4; A-lifetime minor). Model extraction
/// happens INSIDE the guard's scope, before it drops; theory model values are
/// scope-bound and unavailable after backtracking.
///
/// Division of labour with `TheoryBridge::init()`: a §4.2 re-entry re-solves
/// the same query on the same bridge, and ay-sat's incremental reset drops
/// the SAT trail without an `ext.backtrack(0)`, so `init()` pops the theory to
/// scope 0 itself (WP-2 finding 2). The guard covers the between-query case;
/// `run_query` debug-asserts scope 0 after the guard drops.
pub(super) struct BridgeGuard<'g, 's> {
    bridge: &'g mut bridge::TheoryBridge<'s>,
}

impl<'g, 's> BridgeGuard<'g, 's> {
    pub(super) fn new(bridge: &'g mut bridge::TheoryBridge<'s>) -> Self {
        Self { bridge }
    }

    pub(super) fn bridge(&mut self) -> &mut bridge::TheoryBridge<'s> {
        self.bridge
    }
}

impl Drop for BridgeGuard<'_, '_> {
    fn drop(&mut self) {
        ay_sat::Extension::backtrack(self.bridge, 0);
    }
}

#[cfg(test)]
#[allow(clippy::panic)]
mod tests {
    //! WP-1 locks that need no WP-2/WP-3 body: construction in the SAT
    //! profile, logical scopes, the expired-deadline pre-check (legacy-identical
    //! instant Unknown, §3.5), rebuild of an empty session, the histogram.
    //! Everything that reaches `run_query` waits for `TheoryBridge` (WP-2).

    use std::cell::{Cell, RefCell};
    use std::rc::Rc;

    use super::*;

    #[test]
    fn new_session_is_empty_and_unpoisoned() {
        let s = HornSmt::new(SessionConfig::default(), None);
        assert_eq!(s.scope_depth(), 0);
        assert!(!s.is_poisoned());
        assert!(!s.should_rebuild());
        assert_eq!(s.stats().queries, 0);
        assert_eq!(s.theory().kind(), TheoryKind::Lra);
        assert!(s.value(&ChcExpr::Bool(true)).is_none());
        assert_eq!(s.cfg().rebuild_queries_after, 256);
    }

    #[test]
    fn logical_scopes_push_and_pop() {
        let mut s = HornSmt::new(SessionConfig::default(), None);
        s.push();
        s.push();
        assert_eq!(s.scope_depth(), 2);
        assert!(s.pop());
        assert!(s.pop());
        assert!(!s.pop(), "popping below scope 0 reports false");
        assert_eq!(s.scope_depth(), 0);
        // A kill on an id that does not exist is a no-op.
        s.kill_assertion(AssertId(0));
        assert_eq!(s.stats().unit_kills, 0);
    }

    #[test]
    fn expired_budget_is_an_instant_deadline_unknown() {
        let mut s = HornSmt::new(SessionConfig::default(), None);
        let r = s.check_assuming_unverified(&[], &[], Some(Duration::ZERO));
        assert!(
            matches!(
                r,
                HornCheck::Unknown(UnknownReason::Budget(BudgetKind::Deadline))
            ),
            "{r:?}"
        );
        assert_eq!(s.stats().queries, 1);
        assert_eq!(s.stats().unknown_budget, 1);
        assert_eq!(s.query_no(), 1);
        assert!(s.farkas_for_last_unsat(&[], &[]).is_empty());
    }

    #[test]
    fn rebuild_of_an_empty_session_keeps_counters() {
        let mut s = HornSmt::new(SessionConfig::default(), None);
        s.push();
        let _ = s.check_assuming_unverified(&[], &[], Some(Duration::ZERO));
        s.rebuild();
        assert_eq!(s.stats().rebuilds, 1);
        assert_eq!(s.stats().queries, 1);
        assert_eq!(s.scope_depth(), 1);
        assert_eq!(s.query_no(), 1);
        assert!(!s.is_poisoned());
    }

    fn real_var(name: &str) -> ChcExpr {
        ChcExpr::var(crate::ChcVar::new(name, ChcSort::Real))
    }

    fn bool_var(name: &str) -> ChcExpr {
        ChcExpr::var(crate::ChcVar::new(name, ChcSort::Bool))
    }

    fn ge0(name: &str) -> Arc<ChcExpr> {
        Arc::new(ChcExpr::ge(real_var(name), ChcExpr::Real(0, 1)))
    }

    /// One query that rebuilds on entry (`rebuild_queries_after = 1` after
    /// one priming query), with a `Shim`-origin conjunct staged for it that
    /// is in NO other hot set (not `Api`, not in the recent-active window).
    /// Before the keep rule the rebuild tombstoned it and the query tripped
    /// `Poisoned(ScopeMismatch)`; now it is re-asserted under its id and the
    /// query answers (WP-3 hazard H1).
    #[test]
    fn in_call_rebuild_keeps_the_conjuncts_staged_for_this_query() {
        let base = SessionConfig::default();
        let cfg = SessionConfig {
            rebuild_queries_after: 1,
            ..base
        };
        let mut s = HornSmt::new(cfg, None);
        let _ = s.check_assuming_unverified(&[], &[], Some(Duration::ZERO));
        assert!(s.should_rebuild());

        let staged = s
            .assert_with_origin(&ge0("x"), Partition::AB, AssertOrigin::Shim)
            .expect("x >= 0 is eligible");
        assert!(s.recent_active.iter().all(|set| !set.contains(&staged)));

        let r = s.check_assuming_unverified(&[staged], &[], Some(Duration::from_secs(10)));
        assert_eq!(s.stats().rebuilds, 1, "the query rebuilt on entry");
        assert!(matches!(r, HornCheck::Sat(_)), "{r:?}");
        assert_eq!(s.assertion(staged).state, AssertState::Live);
        assert_eq!(s.assertion(staged).origin, AssertOrigin::Shim);
        assert!(!s.is_poisoned());
        assert_eq!(s.stats().unknown_poisoned, 0);
    }

    /// The generic `rebuild()` applies the same rule by stamp: a `Shim`
    /// conjunct asserted after the last query ended (`last_used_query >=
    /// query_no`) is staged for the query in flight and survives; a `Shim`
    /// conjunct last used before that and outside the window is dropped.
    #[test]
    fn rebuild_keeps_what_is_staged_for_the_query_in_flight_and_drops_stale_shim() {
        let mut s = HornSmt::new(SessionConfig::default(), None);
        let stale = s
            .assert_with_origin(&ge0("a"), Partition::AB, AssertOrigin::Shim)
            .unwrap();
        // The query clock moves past `stale` without using it.
        let _ = s.check_assuming_unverified(&[], &[], Some(Duration::ZERO));
        assert!(s.assertion(stale).last_used_query < s.query_no());
        let staged = s
            .assert_with_origin(&ge0("b"), Partition::AB, AssertOrigin::Shim)
            .unwrap();
        let api = s.assert_persistent(&ge0("c"), Partition::AB).unwrap();
        assert!(s.assertion(staged).last_used_query >= s.query_no());

        s.rebuild();
        assert_eq!(s.stats().rebuilds, 1);
        assert_eq!(s.assertion(stale).state, AssertState::Tombstone);
        assert_eq!(s.assertion(staged).state, AssertState::Live);
        assert_eq!(s.assertion(api).state, AssertState::Live);
        // Same ids, and the kept ones answer.
        let r = s.check_assuming_unverified(&[staged, api], &[], Some(Duration::from_secs(10)));
        assert!(matches!(r, HornCheck::Sat(_)), "{r:?}");
        assert!(!s.is_poisoned());
    }

    /// A theory whose `check()` answers from a script (default `Sat`) and
    /// counts its scope depth; everything else is inert.
    struct ScriptedTheory {
        script: Rc<RefCell<VecDeque<ay_core::TheoryResult>>>,
        checks: Rc<Cell<u32>>,
        depth: Rc<Cell<u32>>,
    }

    impl ay_core::TheorySolver for ScriptedTheory {
        fn assert_literal(&mut self, _literal: TermId, _value: bool) {}

        fn check(&mut self) -> ay_core::TheoryResult {
            self.checks.set(self.checks.get() + 1);
            self.script
                .borrow_mut()
                .pop_front()
                .unwrap_or(ay_core::TheoryResult::Sat)
        }

        /// The default delegates to `check()`, which would let the bridge's
        /// BCP-time check (where `Need*` is a fall-through) consume the script
        /// before the final check runs.
        fn check_during_propagate(&mut self) -> ay_core::TheoryResult {
            ay_core::TheoryResult::Sat
        }

        fn needs_final_check_after_sat(&self) -> bool {
            true
        }

        fn propagate(&mut self) -> Vec<ay_core::TheoryPropagation> {
            Vec::new()
        }

        fn push(&mut self) {
            self.depth.set(self.depth.get() + 1);
        }

        fn pop(&mut self) {
            self.depth.set(self.depth.get().saturating_sub(1));
        }

        fn reset(&mut self) {
            self.depth.set(0);
        }
    }

    /// The §4.2 re-entry driver end to end through `run_query`, with the
    /// bridge's tier-2 form (WP-2 finding 3: `AddClauses(originals)` +
    /// `RestartWithOriginals`, the exit arriving as `TheoryStop`): a scripted
    /// theory answers the first final check with an IMPLIED model equality
    /// `u = v` (empty reason), so the minted `[+eq]` is a tier-2 original. The
    /// session must add it globally, re-enter once, and answer `Sat` from the
    /// second solve; the theory is back at scope 0 afterwards and the `=`
    /// term now exists (the `find_eq` gate).
    #[test]
    fn reentry_driver_handles_tier_two_originals_and_restores_scope_zero() {
        let script = Rc::new(RefCell::new(VecDeque::new()));
        let checks = Rc::new(Cell::new(0u32));
        let depth = Rc::new(Cell::new(0u32));
        let theory = theory_box::TheoryBox::mock(Box::new(ScriptedTheory {
            script: Rc::clone(&script),
            checks: Rc::clone(&checks),
            depth: Rc::clone(&depth),
        }));
        let mut s = HornSmt::with_theory(SessionConfig::default(), theory);

        // A Bool `=` is a theory atom (fed, so a scope is opened) with no
        // arithmetic variables (so the mock's missing values do not matter).
        let pq = Arc::new(ChcExpr::eq(bool_var("p"), bool_var("q")));
        let id = s.assert_persistent(&pq, Partition::AB).unwrap();
        assert!(
            !s.assertion(id).atoms.is_empty(),
            "the `=` atom reaches the theory"
        );
        let u = s.own_mut().terms.mk_var("u", Sort::Real);
        let v = s.own_mut().terms.mk_var("v", Sort::Real);
        assert!(s.own().terms.find_eq(u, v).is_none());
        script
            .borrow_mut()
            .push_back(ay_core::TheoryResult::NeedModelEquality(
                ay_core::ModelEqualityRequest {
                    lhs: u,
                    rhs: v,
                    reason: Vec::new(),
                    implied: true,
                },
            ));

        let r = s.check_assuming_unverified(&[id], &[], Some(Duration::from_secs(10)));
        assert!(matches!(r, HornCheck::Sat(_)), "{r:?}");
        assert!(!s.is_poisoned());
        assert_eq!(
            s.stats().reentries,
            1,
            "exactly one restart for the tier-2 clause"
        );
        assert_eq!(s.stats().mints_originals, 1);
        assert_eq!(s.stats().mints_model_eq, 1);
        // Whether the re-entered `init()` had anything to pop depends on the
        // first solve's trajectory: here the tier-2 clause is a UNIT, and
        // ay-sat installs a unit theory lemma at the root through the
        // analysis skeleton (`backtrack(0)` + `ext.backtrack(0)`) before the
        // stop, so the theory is already at scope 0 at re-entry (observed:
        // `init_pops == 0`); a multi-literal original leaves the scope open
        // and `init()` pops it (WP-2's `init_pops_the_theory_to_scope_zero_
        // for_a_reentered_solve`). The invariant is the end state.
        assert!(s.stats().init_pops <= 1, "{}", s.stats().init_pops);
        assert_eq!(depth.get(), 0, "the guard leaves the theory at scope 0");
        assert!(
            checks.get() >= 2,
            "one final check per solve: {}",
            checks.get()
        );
        let eq = s
            .own()
            .terms
            .find_eq(u, v)
            .expect("the `=` term was minted");
        assert!(
            s.tseitin().as_ref().unwrap().term_to_var.contains_key(&eq),
            "the minted equality keeps its SAT variable"
        );
        assert_eq!(s.stats().ext_full_reset_hits, 0);

        // The same query again: the original is in the clause DB, the theory
        // has nothing to ask, no re-entry.
        let r2 = s.check_assuming_unverified(&[id], &[], Some(Duration::from_secs(10)));
        assert!(matches!(r2, HornCheck::Sat(_)), "{r2:?}");
        assert_eq!(s.stats().reentries, 1);
        assert_eq!(depth.get(), 0);
    }

    #[test]
    fn log_histogram_quantiles_are_bucket_upper_bounds() {
        let mut h = LogHistogram::default();
        assert_eq!(h.median(), 0);
        for v in [0u64, 1, 2, 3, 4, 5, 6, 7, 8, 1000] {
            h.record(v);
        }
        assert_eq!(h.count(), 10);
        assert_eq!(h.max(), 1000);
        assert_eq!(h.sum(), 1036);
        // 5th sample of 10 is 4, in bucket [4, 8) whose upper bound is 7.
        assert_eq!(h.median(), 7);
        // 9th sample is 8, bucket [8, 16) -> 15; the 10th is 1000 -> 1023.
        assert_eq!(h.p90(), 15);
        assert_eq!(h.p99(), 1023);
    }
}
