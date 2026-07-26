// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// SAFETY: LraSolver uses a raw pointer to TermStore for persistent solver
// across split-loop iterations (#6590 Packet 2). The pointer is valid only
// within set_terms() / unset_terms() brackets. All unsafe code is confined
// to the terms() accessor and Send/Sync impls.
#![warn(unsafe_code)]

//! AY LRA - Linear Real Arithmetic theory solver
//!
//! Implements the dual simplex algorithm for linear arithmetic over reals,
//! following the approach from "A Fast Linear-Arithmetic Solver for DPLL(T)"
//! by Dutertre & de Moura (CAV 2006).
//!
//! ## Algorithm Overview
//!
//! The solver maintains:
//! - A tableau of linear equalities: basic_var = Σ(coeff * nonbasic_var)
//! - Bounds for each variable (lower, upper, or both)
//! - Current assignment satisfying the tableau
//!
//! When bounds change (from theory atom assertions), we use dual simplex
//! to restore feasibility or detect conflicts.

#![warn(missing_docs)]
#![warn(clippy::all)]
#![allow(
    clippy::collection_is_never_read,
    clippy::iter_with_drain,
    clippy::too_many_arguments,
    clippy::type_complexity
)]

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

use crate::rational::Rational;
// #8529: Use deterministic hash maps (FixedState) in all builds to prevent
// non-deterministic HashMap iteration order from causing false-SAT results.
// Previously, non-kani builds used hashbrown::{HashMap, HashSet} with
// RandomState, making theory propagation order process-dependent.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::{
    BoundRefinementRequest, DiscoveredDisequality, DiscoveredEquality, DisequalitySplitRequest,
    EqualityPropagationResult, ExpressionSplitRequest, ModelEqualityRequest, Sort, TheoryLit,
    TheoryPropagation, TheoryResult, TheorySolver,
};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use smallvec::SmallVec;
use std::sync::OnceLock;
use tracing::{debug, info, trace};

/// M-A2 lazy-persistent-combiner: a STABLE, append-only `TermStore` arena
/// (ARRAY-PROCEDURE-CLOSER-BLUEPRINT §5 A2). Every [`alloc`](Self::alloc)
/// returns a `&TermStore` valid for the arena's whole lifetime and NEVER
/// invalidated by a later `alloc` — each store is heap-boxed at a stable
/// address. This is the piece that lets a create-once persistent
/// `TheoryCombiner` FOLLOW the executor's append-only `ctx.terms` as it grows
/// between lazy-refinement rounds: the shadow re-clones the current `ctx.terms`
/// into this arena each round and `rebind_terms` the live combiner onto that
/// superset clone. It is hosted here (rather than in `ay-dpll`, which is
/// `#![forbid(unsafe_code)]`) because this crate already owns the term-store
/// lifetime plumbing (`LraSolver`'s raw `terms_ptr`), and the arena keeps its
/// stores in a `Vec<Box<TermStore>>` so `Drop` runs normally (no leak).
///
/// Debug-only: the shadow that uses it is `#[cfg(debug_assertions)]` and is only
/// ever armed in tests/diagnostics (no production caller), so this type is
/// compiled out of release builds.
#[cfg(debug_assertions)]
#[derive(Default)]
pub struct ShadowTermStoreArena {
    // The Box is load-bearing: `alloc` hands out `&TermStore` at the boxed
    // stable heap address while the Vec itself may reallocate on push.
    #[allow(clippy::vec_box)]
    stores: std::cell::UnsafeCell<Vec<Box<TermStore>>>,
}

#[cfg(debug_assertions)]
impl ShadowTermStoreArena {
    /// Create an empty arena.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Append `store` and return a reference valid for the arena's lifetime.
    ///
    /// # Safety (internal)
    /// Standard typed-arena pattern: the store is boxed (stable heap address)
    /// and the `Box` pushed behind an `UnsafeCell<Vec<_>>`. The boxed
    /// `TermStore` never moves, so the returned `&TermStore` (tied to `&self`)
    /// stays valid for the arena's lifetime. Use is single-threaded and strictly
    /// sequential (the shadow runs inline in the solve loop); no `&mut` alias to
    /// any stored store is ever handed out, and no `&`/`&mut` into the same
    /// store overlap. `Drop` of the arena drops the `Vec<Box<TermStore>>`,
    /// running each `TermStore`'s destructor.
    #[allow(unsafe_code)]
    pub fn alloc(&self, store: TermStore) -> &TermStore {
        let boxed = Box::new(store);
        let ptr: *const TermStore = &raw const *boxed;
        // SAFETY: see the doc-comment above; single-threaded sequential push,
        // stable heap address, no aliasing `&mut` ever exposed.
        unsafe {
            (*self.stores.get()).push(boxed);
            &*ptr
        }
    }
}

/// #6359: Cached debug flags for LRA solver.
///
/// Environment variables are read once per process via OnceLock, not per
/// solver construction. In DPLL(T) loops where LraSolver is created fresh
/// on each iteration, this eliminates ~8 syscalls per iteration.
struct LraDebugFlags {
    debug_lra: bool,
    debug_lra_bounds: bool,
    debug_lra_assert: bool,
    debug_lra_reset: bool,
    debug_lra_nelson_oppen: bool,
    debug_intern: bool,
    // #8319: Theory-layer disable flags for soundness debugging.
    no_theory_propagation: bool,
    no_implied_bounds: bool,
    no_bound_refinement: bool,
    /// Kill switch for the Fix #2 BCP implied-bounds restraint (cex lane).
    no_bcp_implied_restraint: bool,
    max_fixpoint_rounds: Option<u32>,
    /// Cumulative implied-bound WORK budget per solve (compute_implied_bounds
    /// calls + derivations). Deterministic backstop to the per-variable Zeno
    /// throttle: the per-var streak bounds work WITHIN a call, but the outer
    /// DPLL(T) re-entry loop can re-call compute_implied_bounds unboundedly with
    /// ever-growing bignums (the u64-offset hang). When this cumulative bound
    /// is hit, stop emitting derivations (sound: weaker propagation only).
    /// (Former `AY_IMPLIED_BUDGET` env override removed; the shipped default
    /// is the permanent value.)
    implied_work_budget: u64,
}

static LRA_DEBUG_FLAGS: OnceLock<LraDebugFlags> = OnceLock::new();

fn lra_debug_flags() -> &'static LraDebugFlags {
    LRA_DEBUG_FLAGS.get_or_init(|| {
        use ay_core::DebugChannel;
        let tdf = ay_core::theory_disable_flags();
        LraDebugFlags {
            debug_lra: ay_core::debug_channel_active(DebugChannel::Lra),
            debug_lra_bounds: ay_core::debug_channel_active(DebugChannel::LraBounds),
            debug_lra_assert: ay_core::debug_channel_active(DebugChannel::LraAssert),
            debug_lra_reset: ay_core::debug_channel_active(DebugChannel::LraReset),
            debug_lra_nelson_oppen: ay_core::debug_channel_active(DebugChannel::LraNelsonOppen),
            debug_intern: ay_core::debug_channel_active(DebugChannel::Intern),
            no_theory_propagation: tdf.no_theory_propagation,
            no_implied_bounds: tdf.no_implied_bounds,
            no_bound_refinement: tdf.no_bound_refinement,
            no_bcp_implied_restraint: tdf.no_bcp_implied_restraint,
            max_fixpoint_rounds: tdf.max_fixpoint_rounds.and_then(|v| u32::try_from(v).ok()),
            implied_work_budget: 4_000_000,
        }
    })
}

mod atom_assertion;
mod atom_parsing;
mod bound_assertion;
mod bound_axioms;
mod check_atoms;
mod disequality_check;
mod expression_forced;
mod farkas;
mod farkas_collect;
mod gomory;
mod implied_bounds;
mod implied_interval;
mod implied_refinement;
mod implied_row_reasons;
mod implied_row_recursive;
mod infrational;
mod lia_patch;
mod lia_support;
mod lifecycle;
mod lifecycle_scope;
mod linear_expr;
mod lra_model;
mod lra_query;
mod lra_region;
mod nelson_oppen;
mod optimality_certificate;
mod optimization;
mod propagation;
pub mod rational;
mod rational_ops;
mod simplex;
mod sparse_matrix;
mod stats;
mod tableau;
mod theory_solver;
mod types;
mod warm_state;

#[cfg(test)]
mod rational_tests;

#[cfg(test)]
mod rational_proptest;

// Explicit re-exports: types used in the public API or by other crates
pub use optimality_certificate::{CertificateAtom, OptimalityCertificate};
pub use types::{
    Bound, BoundProvenance, GcdRowInfo, GomoryCut, LinearExpr, LraModel, OptimizationResult,
    OptimizationSense, VarStatus,
};
// Crate-internal imports
use types::{
    fractional_part, AtomRef, BoundExplanation, BoundType, ColEntry, DenseIdxSet, DenseU32Set,
    ErrorKey, ExprInterval, ImpliedBound, InfRational, IntervalEndpoint, ParsedAtomInfo,
    TableauRow, VarInfo,
};

/// Lazy reason token for deferred reason materialization (#4919 Phase E, #6617 Phase 3).
///
/// Most bound propagations are never consumed by the SAT solver (filtered by
/// `bound_is_interesting`, already assigned, or subsumed by stronger clauses).
/// Computing `collect_row_reasons_dedup()` for every implied bound wastes
/// O(rows) work per propagation.
///
/// Two variants:
/// - `ImpliedRow`: the original deferred path for implied-bound propagations.
///   Stores a fallback row index for interval-based reconstruction.
/// - `DirectBound`: defers `reason_pairs()` collection for direct-bound
///   propagations (#6617 Phase 3). Z3 stores a `u_dependency` index and
///   reconstructs reasons only during conflict analysis. ~90% of propagations
///   are never explained, so deferring avoids O(reason_len) allocation per
///   propagation.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum DeferredReason {
    /// Deferred reason for implied-bound propagation (row-walking).
    #[allow(dead_code)]
    ImpliedRow {
        /// Internal variable whose bound justified the propagation.
        var: u32,
        /// Which side of the variable bound to explain.
        /// `true` = upper bound, `false` = lower bound.
        need_upper: bool,
        /// Optional single-row fallback used when recursive explanation fails.
        fallback_row_idx: Option<usize>,
    },
    /// Deferred reason for direct-bound propagation (#6617 Phase 3).
    /// Materializes by reading `self.vars[var].upper/lower.reason_pairs()`.
    DirectBound {
        /// Internal variable whose direct bound justified the propagation.
        var: u32,
        /// Which side of the variable bound to explain.
        /// `true` = upper bound, `false` = lower bound.
        need_upper: bool,
    },
    /// Deferred reason for interval-based propagation (#8151 Phase 3).
    /// Materializes by calling `collect_interval_reasons()` on the atom's
    /// expression at propagation drain time. Avoids eagerly collecting
    /// reasons for interval propagations that may be filtered out by the
    /// stale-reason filter.
    Interval {
        /// The atom term whose interval bounds imply the propagation.
        atom_term: TermId,
        /// Which side of the expression interval to explain.
        /// `true` = upper bound reasons, `false` = lower bound reasons.
        for_upper: bool,
    },
    /// Deferred reason for implied-bound propagation (#8467 Phase 4).
    /// Instead of eagerly calling make_eager_implied_propagation() or
    /// make_implied_propagation() which iterate contributing_vars and
    /// collect Vec<TheoryLit> reasons, store only the variable index
    /// and direction. Reasons are materialized lazily via
    /// explain_propagation() only when the SAT solver needs them during
    /// conflict analysis (~90% are never explained).
    ImpliedBound {
        /// Internal variable whose implied bound justified the propagation.
        var: u32,
        /// Which side of the variable bound to explain.
        /// `true` = upper bound, `false` = lower bound.
        need_upper: bool,
    },
}

/// Internal pending propagation with optional deferred reason materialization.
#[derive(Debug, Clone)]
struct PendingPropagation {
    propagation: TheoryPropagation,
    deferred: Option<DeferredReason>,
}

impl PendingPropagation {
    #[allow(dead_code)]
    fn eager(literal: TheoryLit, reason: Vec<TheoryLit>) -> Self {
        Self {
            propagation: TheoryPropagation {
                literal,
                reason,
                reason_data: None,
            },
            deferred: None,
        }
    }

    fn eager_propagation(propagation: TheoryPropagation) -> Self {
        Self {
            propagation,
            deferred: None,
        }
    }

    fn deferred(literal: TheoryLit, deferred: DeferredReason) -> Self {
        Self {
            propagation: TheoryPropagation {
                literal,
                reason: Vec::new(),
                reason_data: None,
            },
            deferred: Some(deferred),
        }
    }
}

/// Wakeup entry for a compound atom.
///
/// `slack` is the normalized slack variable representing the compound linear
/// expression. The same atom is indexed under each constituent variable and the
/// slack itself so we can wake it both for same-expression slack tightening and
/// for constituent-variable bound changes.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct CompoundAtomRef {
    term: TermId,
    slack: u32,
    strict: bool,
}

/// Compact, order-preserving set of atom terms supporting O(1) amortized
/// insert / remove / "pick any member" (STAGE B decision-index).
///
/// `items` is the dense membership list (no holes); `pos` maps each present
/// term to its index in `items` so removal is an O(1) swap-with-last. Iterating
/// `items` visits exactly the current members with no empty-slot scanning —
/// unlike a `HashSet`, whose capacity never shrinks after mass removal, so
/// finding the few live members deep in a search would cost O(capacity).
#[derive(Default)]
pub(crate) struct CompactAtomSet {
    items: Vec<TermId>,
    pos: HashMap<TermId, usize>,
}

impl CompactAtomSet {
    #[inline]
    pub(crate) fn insert(&mut self, term: TermId) {
        if self.pos.contains_key(&term) {
            return;
        }
        self.pos.insert(term, self.items.len());
        self.items.push(term);
    }

    #[inline]
    pub(crate) fn remove(&mut self, term: TermId) {
        if let Some(idx) = self.pos.remove(&term) {
            // Swap the last element into the vacated slot to keep `items` dense.
            let last = self.items.pop().expect("items non-empty when pos had key");
            if idx < self.items.len() {
                self.items[idx] = last;
                self.pos.insert(last, idx);
            }
        }
    }

    #[inline]
    pub(crate) fn clear(&mut self) {
        self.items.clear();
        self.pos.clear();
    }

    #[inline]
    pub(crate) fn items(&self) -> &[TermId] {
        &self.items
    }
}

/// STAGE B decision-candidate index: the currently-unasserted theory atoms
/// eligible for LP-guided decision suggestion, partitioned by category so
/// `suggest_decision_atom` is O(degree)/O(1) amortized instead of two full
/// O(registered_atoms) scans per decision. Membership mirrors the invariant
/// { registered non-distinct atom terms that are NOT in `asserted` }; the
/// phase-hint filter is applied at read time. Maintained incrementally on
/// register / assert / pop and fully rebuilt at reset / snapshot boundaries.
#[derive(Default)]
pub(crate) struct DecisionCandidateIndex {
    /// Unasserted equality atoms (priority 1 — fix a linear combination).
    eq: CompactAtomSet,
    /// Unasserted inequality atoms (non-eq, non-distinct; priority 2).
    ineq: CompactAtomSet,
}

/// Structural snapshot for transferring LRA theory state across split-loop
/// iterations without re-parsing the term DAG (#6590).
///
/// Contains all fields preserved by `soft_reset()`: tableau structure,
/// variable mappings, atom caches, and indexing structures. Assertion state
/// (bounds, trail, scopes) is NOT included — the importing solver starts
/// with clean assertion state.
///
/// This avoids the 26-33% overhead of re-creating `LraSolver` and
/// re-registering all atoms on every DPLL(T) iteration.
struct LraStructuralSnapshot {
    rows: Vec<TableauRow>,
    vars: Vec<VarInfo>,
    term_to_var: HashMap<TermId, u32>,
    var_to_term: HashMap<u32, TermId>,
    next_var: u32,
    atom_cache: HashMap<TermId, Option<ParsedAtomInfo>>,
    ite_link_terms: Vec<(TermId, TermId, TermId, TermId)>,
    ite_link_terms_seen: HashSet<TermId>,
    registered_atoms: HashSet<TermId>,
    atom_index: HashMap<u32, Vec<AtomRef>>,
    compound_use_index: HashMap<u32, Vec<CompoundAtomRef>>,
    var_to_atoms: HashMap<u32, Vec<TermId>>,
    atom_slack: HashMap<(TermId, bool), (u32, Rational)>,
    expr_to_slack: HashMap<Vec<(u32, Rational)>, (u32, Rational)>,
    slack_var_set: HashSet<u32>,
    propagated_equality_pairs: HashSet<(TermId, TermId)>,
    propagated_disequality_pairs: HashSet<(TermId, TermId)>,
    basic_var_to_row: HashMap<u32, usize>,
    col_index: Vec<Vec<ColEntry>>,
    to_int_terms: Vec<(u32, TermId)>,
    unassigned_atom_count: Vec<u32>,
    // Warm-path caches (#6590 Packet 1)
    not_inner_cache: HashMap<TermId, (TermId, bool)>,
    const_bool_cache: HashMap<TermId, Option<bool>>,
    refinement_eligible_cache: HashMap<TermId, bool>,
    is_integer_sort_cache: HashMap<TermId, bool>,
    /// BCP implied-bounds dry streak counter (#8200).
    #[allow(dead_code)]
    bcp_implied_dry_streak: u32,
    /// BCP cascade dry streak counter (#8255). Tracks consecutive BCP checks
    /// where cascading beyond depth 1 in compute_implied_bounds produced zero
    /// additional bounds. When >= 3, cascade depth is throttled to 1.
    #[allow(dead_code)]
    bcp_cascade_dry_streak: u32,
    /// Maximum row width for dense LP detection (#8003).
    max_row_width: usize,
    /// Cross-negation bound propagation map (#8008).
    negation_partners: Vec<Option<(u32, Rational)>>,
    /// Persisted theory-propagation JIT (Fix A1): compiled per-variable
    /// propagator tables plus shared native code region. `None` when the JIT
    /// was not compiled at export time or persistence is disabled via
    /// `AY_LRA_JIT_PERSIST=0`. Valid for exactly the exported `atom_index`;
    /// the importing solver re-validates against the atom-index fingerprint
    /// before any rebuild-triggering change (propagation/jit_compile.rs).
    theory_prop_jit: Option<ay_jit::TheoryPropJit>,
}

/// Linear Real Arithmetic theory solver using dual simplex.
///
/// `LraSolver` is `'static` — it does not hold a borrow on the `TermStore`.
/// Instead, a raw pointer (`terms_ptr`) is set via `set_terms()` before each
/// operation batch (register_atom, check, etc.) and cleared after. This allows
/// the solver to persist across split-loop iterations while the `TermStore` is
/// mutated between iterations (#6590 Packet 2).
pub struct LraSolver {
    /// Raw pointer to the term store. Set via `set_terms()`, read via `terms()`.
    /// Valid only while the caller guarantees the TermStore is alive and not
    /// mutably borrowed. Null when not in an active operation.
    terms_ptr: *const TermStore,
    /// Tableau rows
    rows: Vec<TableauRow>,
    /// Variable information (indexed by internal var id)
    vars: Vec<VarInfo>,
    /// Mapping from term IDs to internal variable IDs
    term_to_var: HashMap<TermId, u32>,
    /// Mapping from internal variable IDs to term IDs
    var_to_term: HashMap<u32, TermId>,
    /// Next fresh variable ID
    next_var: u32,
    /// Trail for backtracking: (var_id, which_bound, old_value).
    /// Only the modified bound is saved (halves Bound clone count).
    trail: Vec<(u32, BoundType, Option<Bound>)>,
    /// Monotone revision counter for the variable-bound state.
    ///
    /// Bumped whenever any variable bound MAY have changed: every
    /// `trail.push` site (bound assert / unjustified-bound retraction), once
    /// per `pop()` (trail replay restores bounds), and every reset /
    /// soft-reset / snapshot-import path that clears bound slots wholesale.
    /// Deliberately COARSE: a bump when no bound actually moved only costs a
    /// cache miss, never a stale hit. LIA's `detect_algebraic_equalities`
    /// memo stamps against this, so under-invalidation here would be a
    /// Nelson-Oppen completeness (and thus combined-SAT soundness) hazard —
    /// err on the side of extra bumps.
    bound_revision: u64,
    /// Scope markers: (trail_pos, asserted_trail_len)
    scopes: Vec<(usize, usize)>,
    /// Asserted atoms: term_id -> value
    asserted: HashMap<TermId, bool>,
    /// Trail of asserted keys for scope-based undo (#3676).
    asserted_trail: Vec<TermId>,
    /// Cross-theory propagated literals (Nelson-Oppen shared (dis)equality
    /// reasons, cross-sort bound/tight reasons). These literals are asserted
    /// on sibling theories, not on LRA, but are still valid DPLL-trail
    /// justifications for LRA conflicts (#8747).
    cross_theory_asserted: HashMap<TermId, bool>,
    /// Trail of cross-theory reason writes for scope-based pop. `None` means
    /// the key was absent before insertion; `Some(prev)` restores the prior
    /// value on pop.
    cross_theory_asserted_trail: Vec<(TermId, Option<bool>)>,
    /// Position in `cross_theory_asserted_trail` at each push scope.
    cross_theory_asserted_scopes: Vec<usize>,
    /// Cache of parsed atom information to avoid re-parsing
    atom_cache: HashMap<TermId, Option<ParsedAtomInfo>>,
    /// The atom currently being parsed in check(). When parse_linear_expr hits
    /// an unsupported term, this atom is added to persistent_unsupported_atoms.
    /// None when called from non-atom contexts (shared equalities, cross-sort bounds).
    current_parsing_atom: Option<TermId>,
    /// Term-level arithmetic ITEs interned as opaque variables during parsing.
    ///
    /// Stored as `(ite_term, cond, then_branch, else_branch)`. Before check()
    /// returns Sat, SAT-level link lemmas `cond => (= ite then)` and
    /// `(not cond) => (= ite else)` are requested via `NeedModelEqualities`
    /// with `implied: true`, giving the ITE exact semantics with the condition
    /// literal as a real premise in every downstream explanation.
    ///
    /// This replaces the old parse-time branch substitution, which read the
    /// condition's CURRENT Boolean assignment: conflicts derived from the
    /// substituted parse did not carry the condition literal, so learned
    /// clauses over-generalized to assignments where the condition flips
    /// (false UNSAT), and `atom_cache` pinned the substitution across
    /// backtracking.
    ite_link_terms: Vec<(TermId, TermId, TermId, TermId)>,
    /// Dedup set for `ite_link_terms` (keyed by the ITE term id).
    ite_link_terms_seen: HashSet<TermId>,
    /// Dirty flag: need to recompute
    dirty: bool,
    /// Discovered equalities for Nelson-Oppen propagation.
    /// These are collected during check() when we detect tight bounds.
    pending_equalities: Vec<DiscoveredEquality>,
    /// Track which equality pairs have been propagated to avoid duplicates.
    /// Stores (min(lhs, rhs), max(lhs, rhs)) for canonical ordering.
    propagated_equality_pairs: HashSet<(TermId, TermId)>,
    /// #8469: Track which disequality pairs have been propagated to avoid duplicates.
    /// Stores (min(lhs, rhs), max(lhs, rhs)) for canonical ordering.
    propagated_disequality_pairs: HashSet<(TermId, TermId)>,
    /// Trivial conflict from a constant constraint that is unsatisfiable.
    /// For example, `0 < 0` or `-1 >= 0`.
    /// Stores ALL reason literals so blocking clauses are complete (#8012).
    trivial_conflict: Option<Vec<TheoryLit>>,
    /// Set of (atom TermId, asserted value) pairs whose bounds have been asserted
    /// into the tableau. Prevents creating duplicate slack variables and tableau
    /// rows when the same atom is re-asserted across check() calls (#4919).
    /// Cleared on pop() since bounds are restored by the trail.
    bound_atoms: HashSet<(TermId, bool)>,
    /// Persistent unsupported atoms (#6167): atoms whose parsing triggered
    /// unsupported sub-expressions and whose bounds are in the tableau.
    /// Scope-tracked: push() saves and pop() restores (#4919).
    persistent_unsupported_atoms: HashSet<TermId>,
    /// Undo trail for persistent_unsupported_atoms. We only append terms when
    /// they are first inserted, so pop() can rewind to a scope mark without
    /// cloning the full set on every push/check (#6362).
    persistent_unsupported_trail: Vec<TermId>,
    /// Scope markers into persistent_unsupported_trail.
    persistent_unsupported_scope_marks: Vec<usize>,
    /// When true, all variables are integers and strict bounds are canonicalized:
    /// `expr < 0` becomes `expr <= -1`, `expr > 0` becomes `expr >= 1`.
    /// Set by the LIA solver wrapper.
    integer_mode: bool,
    /// Simple PRNG state for Gomory cut candidate selection.
    /// Uses xorshift32 seeded from check iteration count.
    /// Reference: Z3 gomory.cpp:408-422 (cubic-bias randomized selection).
    gomory_rng: u32,
    /// Simple PRNG state for pivot tiebreaking (reservoir sampling).
    /// Uses xorshift32. When multiple pivot candidates have equal cost,
    /// one is selected at random to break symmetry and prevent cycling.
    /// Reference: Z3 `select_pivot_core` in simplex_def.h:546-585.
    pivot_rng: u32,
    // Cached env vars (#2673)
    debug_lra: bool,
    debug_lra_bounds: bool,
    debug_lra_assert: bool,
    debug_lra_reset: bool,
    debug_lra_nelson_oppen: bool,
    debug_intern: bool,
    // #8319: Theory-layer disable flags for soundness debugging.
    no_theory_propagation: bool,
    no_implied_bounds: bool,
    no_bound_refinement: bool,
    max_fixpoint_rounds: Option<u32>,
    /// Per-theory runtime statistics (#4706, consolidated into sub-struct #8841).
    ///
    /// All u64/u32 counters and running maxima previously declared inline
    /// (check_count, conflict_count, propagation_count, reason materialization
    /// counters, simplex budget telemetry, cascade/fixpoint telemetry, JIT
    /// counters, precision counters, etc.) live in `LraStats`. Access via
    /// `self.stats.<field>`; `stats` is crate-private.
    pub(crate) stats: stats::LraStats,
    /// Set of atom terms already registered via register_atom (#4919).
    /// Prevents duplicate registration when both atom and NOT(atom) are registered.
    registered_atoms: HashSet<TermId>,
    /// STAGE B: incremental decision-candidate index (unasserted eq/ineq atoms).
    /// Read by `suggest_decision_atom` under `AY_LRA_FAST_DECISION`; maintained
    /// on register/assert/pop and rebuilt at reset/snapshot boundaries.
    decision_index: DecisionCandidateIndex,
    /// Atoms grouped by their single arithmetic variable, for bound propagation.
    /// Key: internal var id, Value: list of atoms referencing this variable.
    /// Reference: Z3 Component 3 (same-variable chain propagation).
    atom_index: HashMap<u32, Vec<AtomRef>>,
    /// Buffered theory propagations computed during check(), returned by propagate().
    /// Uses `PendingPropagation` to support lazy reason materialization (#4919 Phase E):
    /// implied-bound propagations store a `DeferredReason` token instead of eagerly
    /// computing `collect_row_reasons_dedup()`. Reasons are materialized only when
    /// drained by `propagate()`.
    pending_propagations: Vec<PendingPropagation>,
    /// Buffered requests to create tighter bound atoms from implied bounds (#4919).
    pending_bound_refinements: Vec<BoundRefinementRequest>,
    /// Atoms already propagated in the current scope. Prevents duplicate
    /// propagations. Cleared on pop() alongside bound restoration.
    propagated_atoms: HashSet<(TermId, bool)>,
    /// When true, this solver is embedded inside a combined theory solver
    /// (e.g., UfLra, AufLra, Lira). Unknown function/term catch-all arms
    /// in parse_linear_expr skip marking atoms as unsupported, because
    /// cross-theory terms (select, UF applications) are expected and handled
    /// by the outer Nelson-Oppen loop (#5524).
    combined_theory_mode: bool,
    /// Persistent mapping from (atom TermId, asserted_value) to (slack_var, orig_constant).
    /// Prevents creating duplicate slack variables when the same atom is re-asserted
    /// after push/pop cycles (#4919). The orig_constant is stored so re-assertions
    /// apply constant compensation even when the slack was created via expr_to_slack
    /// for a different atom's expression (#6205).
    /// Not cleared on pop() — the slack variable and row persist in the tableau.
    atom_slack: HashMap<(TermId, bool), (u32, Rational)>,
    /// Expression-keyed slack variable cache for `get_or_create_slack()`.
    /// Maps normalized coefficient vectors (sorted by var id) to (slack variable id, original constant).
    /// The original constant is stored so that when a slack is reused for an expression with
    /// a different constant offset, the bound can be adjusted accordingly (#6193).
    /// Used by `register_atom` to create slack variables at registration time
    /// (before assertion), enabling `atom_index` to cover compound atoms (#4919).
    expr_to_slack: HashMap<Vec<(u32, Rational)>, (u32, Rational)>,
    /// Set of slack variable IDs created for compound atoms (#6242).
    /// Used to skip `propagate_var_atoms` on slack variables, whose bounds
    /// have incomplete reason sets (missing the structural s = expr link).
    slack_var_set: HashSet<u32>,
    /// Implied variable bounds derived from tableau rows after simplex Sat.
    /// For each variable, stores (implied_lower, implied_upper).
    /// Each bound stores value, strict flag, and the derivation row index for
    /// efficient reason reconstruction in `collect_row_reasons_recursive` (#4919).
    /// Recomputed on every Sat check; not part of the backtrack trail.
    implied_bounds: Vec<(Option<ImpliedBound>, Option<ImpliedBound>)>,
    /// Representative fixed term-backed variable keyed by `(value, is_int)`.
    /// Mirrors Z3's `m_fixed_var_table_*` idea without scanning all fixed terms
    /// for every `discover_cheap_equalities_for_check()` call (#6617).
    fixed_term_value_table: HashMap<(Rational, bool), u32>,
    /// Reverse membership index for `fixed_term_value_table`.
    /// Used to avoid re-registering the same fixed term-backed variable.
    fixed_term_value_members: HashMap<u32, (Rational, bool)>,
    /// Newly discovered fixed-term equalities awaiting check()-time materialization.
    /// Stores `(new_var, representative_var)` pairs in internal var ids.
    pending_fixed_term_equalities: Vec<(u32, u32)>,
    /// Offset equalities discovered from nf==2 rows (#6617 Packet 1).
    /// Unlike fixed-term equalities, the base variables are NOT fixed — the equality
    /// is derived from row structure. Stores (var1, var2, row_idx1, row_idx2) so that
    /// reasons can be constructed from the fixed columns in both rows.
    pending_offset_equalities: Vec<(u32, u32, usize, usize)>,
    /// Column index: for each variable, the list of row indices that contain it.
    /// Enables O(nnz) pivot substitution instead of O(rows) scan (#4919 Phase 1).
    /// Maintained during row creation and pivot operations.
    col_index: Vec<Vec<ColEntry>>,
    /// Work vector for O(1) coefficient lookup during pivot substitution (#8003).
    pivot_work_vec: Vec<i32>,
    /// Dirty list for efficient work vector reset.
    pivot_work_dirty: Vec<u32>,
    /// Persistent buffer for pivot row coefficients (#8003 TL65).
    /// Avoids O(w) clone of `rows[row_idx].coeffs` per pivot by reusing allocation.
    /// Swapped in from the pivot row then swapped back after all substitutions.
    #[allow(dead_code)]
    pivot_row_coeffs_buf: Vec<(u32, Rational)>,
    /// Persistent buffer for pivot row constant (#8003 TL65).
    #[allow(dead_code)]
    pivot_row_constant_buf: Rational,
    /// Persistent buffer for i128 scaled substitution terms (#8003 TL65).
    /// Reused across substitute_var_i64_with_col_deltas calls within a single pivot
    /// to avoid per-affected-row allocation of Vec<(u32, i128)>.
    pivot_subst_i64_buf: Vec<(u32, i128)>,
    /// Bland mode: when true, use smallest-index pivot selection (anti-cycling).
    /// Activated after `basis_repeat_count` exceeds threshold (#4919 Phase 2).
    bland_mode: bool,
    /// Count of consecutive iterations where the basis set repeated.
    /// When this exceeds BLAND_THRESHOLD, bland_mode is activated.
    basis_repeat_count: u32,
    /// Position in `asserted_trail` up to which atoms have been processed by
    /// `check()`. On the next `check()` call, only atoms from this position
    /// onward need to be evaluated, avoiding the O(n log n) clone+sort of the
    /// full asserted map (#4919 incremental check optimization).
    last_check_trail_pos: usize,
    /// True when the last disequality check in check() found a violation
    /// (returned NeedDisequalitySplit or NeedExpressionSplit). Forces re-checking
    /// disequalities even when model_may_have_changed is false, to prevent
    /// the optimization from suppressing known violations (#4919).
    last_diseq_check_had_violation: bool,
    /// Buffered disequality split requests from batch evaluation (#6259).
    /// When check() finds multiple violated disequalities, the first is returned
    /// as NeedDisequalitySplit and the rest are stored here for batch draining
    /// by the DPLL(T) split loop. This avoids O(N) solver restarts for N violated
    /// disequalities (e.g., TTA Startup benchmarks with 400+ equality atoms).
    pending_diseq_splits: Vec<DisequalitySplitRequest>,
    /// Buffered expression split requests from batch evaluation (#8707).
    /// When check() finds multiple violated multi-variable disequalities
    /// (e.g., `(distinct (+ q0 0) (+ q1 1) ...)` in 8-queens), the first is
    /// returned as `NeedExpressionSplit` and the rest are stored here for batch
    /// draining by the DPLL(T) split loop. This avoids O(N) solver restarts
    /// for N violated multi-var disequalities (e.g., 28 pairwise diseqs from a
    /// single `distinct` over 8 arithmetic terms).
    pending_expr_splits: Vec<ExpressionSplitRequest>,
    /// Whether any variable bound was tightened since the last simplex run.
    /// When false and no new tableau rows were added, the current simplex
    /// solution is still feasible and we can skip the simplex call (#4919).
    bounds_tightened_since_simplex: bool,
    /// Whether any variable bound was tightened since the last simplex
    /// completion during the current `check_impl` / `check_during_propagate_impl`
    /// invocation (#8187 soundness gate).
    ///
    /// This is the soundness-gate counterpart of `bounds_tightened_since_simplex`.
    /// Both are set by the same setters (`assert_var_bound` /
    /// `assert_var_bound_with_reasons`) and both are cleared at each simplex
    /// completion. The crucial difference is CONSUMPTION:
    ///
    /// - `bounds_tightened_since_simplex` drives "need simplex" decisions
    ///   (skip the simplex call when false, cache last feasible result).
    /// - `post_simplex_bounds_added` drives the Sat-return soundness gate:
    ///   when TRUE on a Sat return, the `debug_assert_bounds_satisfied` gate
    ///   is bypassed in debug builds AND in release builds we demote the
    ///   result to Unknown. This catches the #8187 race where
    ///   `run_post_simplex_propagation` tightens new direct bounds AFTER the
    ///   simplex-completion clear and BEFORE the gate, producing a false Sat
    ///   on a stale tableau.
    ///
    /// Splitting these two flags lets us tighten the soundness gate without
    /// disturbing the BCP fast-skip logic (which relies on
    /// `bounds_tightened_since_simplex` remaining TRUE until the next simplex
    /// fully incorporates the new bounds — see #8255 / #8468).
    ///
    /// Cleared at the entry of `check_impl` / `check_during_propagate_impl`
    /// so it only tracks additions *inside the current invocation*. Cleared
    /// again at simplex completion so only post-simplex additions surface to
    /// the gate.
    post_simplex_bounds_added: bool,
    /// Variables whose bounds were tightened since the last simplex run (#8064).
    /// Used by `dual_simplex_with_max_iters` for a targeted O(changed) contradiction
    /// check instead of the O(vars) full scan when running with a small budget.
    /// Cleared when simplex completes (alongside `bounds_tightened_since_simplex`).
    vars_tightened_since_simplex: Vec<u32>,
    /// Guard-scan memo (#inc-guard-memo): true when the current (values, bounds)
    /// pair has been verified violation-free — either by a full
    /// `first_current_assignment_bound_violation` scan that found nothing, or by
    /// a feasible dual-simplex completion (`save_feasible_snapshot`), whose
    /// contract already guarantees every variable is within its bounds. While
    /// true, `guard_sat_current_assignment_bounds` can skip its O(num_vars)
    /// rescan (measured at 3.3e9 var-scans on a depth-14 BMC trace).
    ///
    /// SOUNDNESS: every mutation that can create a new violation must set this
    /// false. Bounds only ever TIGHTEN inside a scope (both `assert_var_bound`
    /// variants replace strictly-tighter only). A pop is NOT loosen-only, despite
    /// what this comment claimed before #8471: `retract_unjustified_var_bounds`
    /// (farkas_collect.rs:798-802) `take()`s a live bound and trails it, so the pop
    /// replay (lifecycle_scope.rs:47-56) can reinstate a bound where there is now
    /// None — i.e. a pop CAN create a violation. That is safe because `pop_inner`
    /// clears this memo on every path that replays the trail (lifecycle_scope.rs:304;
    /// the `scopes`-empty early return at :36-38 replays nothing), not because of
    /// any monotonicity; do not weaken that clear. Values change only in `update_nonbasic`
    /// (the single value chokepoint — simplex pivots route through it) plus the
    /// enumerated direct writers (`optimize_impl`, `round_integer_vars_*`,
    /// `try_repair_free_var_pair_disequalities`) and lifecycle resets — each of
    /// those sites clears this flag. A debug assertion in the guard cross-checks
    /// every memo hit against the full scan.
    guard_clean_valid: bool,
    /// True iff the last `dual_simplex_with_max_iters` return was the
    /// fully-verified Sat exit (`all_bounds_satisfied`: infeasible heap empty
    /// AND the full non-basic scan found no `violates_bounds` hit — the same
    /// predicate the fail-close guard uses). False for the pre-loop fast-path
    /// Sat (targeted tightened-vars scan only — trusts invariants #8810 says
    /// not to trust), for budget-exhaustion optimistic Sat (converted
    /// Unknown→Sat in `dual_simplex_propagate`), for the BLAS bridge, and for
    /// all non-Sat exits. Only a verified Sat may anchor `guard_clean_valid`
    /// in `save_feasible_snapshot`.
    last_simplex_verified: bool,
    /// Chain-of-custody for the guard memo (#inc-guard-chain): true while
    /// EVERY value/bound mutation since the last full verification is
    /// tracked-and-reverified — i.e. bound tightenings (recorded in
    /// `vars_tightened_since_simplex`, scanned by the simplex pre-loop fast
    /// path) or in-bounds nonbasic snaps whose basic fallout the infeasible
    /// heap tracks (the fast path requires the heap empty). Under this
    /// invariant the fast path's targeted scan EXTENDS the previous full
    /// verification, so its Sat may set `last_simplex_verified` and anchor
    /// the guard memo. Broken by pops (a popped scope's simplex can leave
    /// values violating retained bounds — pop also clears the tightened list
    /// and marks the heap stale, forcing the next simplex through the
    /// full-loop verified exit, which restores the chain), lifecycle resets,
    /// and the enumerated untracked writers (`optimize_impl`,
    /// `round_integer_vars_*`, `try_repair_free_var_pair_disequalities`,
    /// `try_patch_integer_var`). Restored ONLY by a full verification (the
    /// `all_bounds_satisfied` simplex exit or a clean full guard scan). The
    /// guard's debug_assert cross-check remains the canary for any missed
    /// breaker.
    guard_tracked_only: bool,
    /// `self.rows.len()` at the end of the last FULL `compute_implied_bounds`
    /// sweep (#inc-cib-nodelta). See `ib_overlay_complete`.
    rows_len_at_last_implied: usize,
    /// True when the persistent `implied_bounds` overlay reflects a completed
    /// FULL row sweep with no direct-bound change, overlay clear, or row
    /// addition since (#inc-cib-nodelta). While true — together with an empty
    /// `touched_rows`, a clear `direct_bounds_changed_since_implied`, and an
    /// unchanged row count — a repeat `compute_implied_bounds` call would
    /// derive nothing new (its row generations are all stale), so it returns
    /// empty immediately instead of re-sweeping every accumulated row.
    /// Measured flood at BMC depth 14: ~390k calls and 39M swept rows per
    /// check-sat. Cleared wherever `implied_bounds` is cleared (pop/resets);
    /// set only at the end of a genuinely-full sweep, so the one rebuild pass
    /// per pop epoch is preserved bit-for-bit and only the provably-empty
    /// repeats are skipped. Skipping derivations is the same sound weakening
    /// as the existing work-budget early return (`implied_bounds.rs:50-58`).
    ib_overlay_complete: bool,
    /// Undo trail for DERIVED implied-bound overlay writes (#inc-implied-trail).
    /// Every `compute_implied_bounds` derived write pushes
    /// `(var, is_upper, displaced_old_value)` (zero-clone via `Option::replace`).
    /// `pop_inner` rewinds to the scope mark, restoring the pre-scope derived
    /// bounds — valid by monotonicity: a bound derived at an outer scope used
    /// only antecedents (direct bounds, rows) that still hold after popping
    /// inner scopes. This replaces the wholesale `implied_bounds.clear()` on
    /// pop (which forced a full re-derivation sweep after every CDCL
    /// backtrack). The one retraction hole — direct-bound overlay merges
    /// (`overlay_direct_bound_for_var`) are NOT trailed — is closed in
    /// `pop_inner` by resetting `implied_bounds[v] = (None, None)` for exactly
    /// the vars whose direct bounds the pop restored (`changed_vars`,
    /// O(popped)) and stamping their `var_bound_gen` so their rows re-derive.
    implied_trail: Vec<(u32, bool, Option<ImpliedBound>)>,
    /// Scope marks into `implied_trail`, pushed/popped in lockstep with
    /// `scopes` (#inc-implied-trail).
    implied_trail_scopes: Vec<usize>,
    /// Undo trail for `propagated_atoms` inserts (#inc-prop-trail). Pop
    /// removes exactly the entries inserted in popped scopes (whose literals
    /// the DPLL backtrack just unassigned — theory scopes track DPLL levels),
    /// while outer-scope entries persist (their literals remain assigned, so
    /// re-sending is correctly suppressed). Replaces the wholesale
    /// `propagated_atoms.clear()` on pop, which forced the SAT loop to
    /// re-derive and re-insert every propagation after every backtrack (the
    /// dominant HashMap-churn leaf in the deep-BMC floor profile). A stale
    /// suppression can only skip a re-send — a propagation, never a verdict —
    /// so this is a sound weakening in the worst case and exact under the
    /// per-level scope alignment.
    propagated_trail: Vec<(TermId, bool)>,
    /// Scope marks into `propagated_trail` (#inc-prop-trail).
    propagated_trail_scopes: Vec<usize>,
    /// #uflia-eager-sweep: opt back into the pre-#inc-implied-trail /
    /// pre-#inc-prop-trail pop semantics — wholesale-clear the propagation
    /// memory (`propagated_atoms`, the implied-bound overlay and its
    /// generation stamps, both undo trails) on EVERY pop, so the next check
    /// re-derives and re-propagates everything against the post-backtrack
    /// trail. Set only by the eager DPLL(T) combined-theory lanes
    /// (`LiaSolver::set_combined_theory_mode` consumers via
    /// `set_eager_repropagate_on_pop`): their inline theory-conflict engine
    /// measurably depends on the post-backtrack re-propagation sweep the
    /// incremental persistence slices removed (bisect f72a06aaa6 +
    /// d10d242273/4c7d3963f6; QF_UFLIA eager fingerprint
    /// smt.theory_conflicts 747 -> 132, ~40 lost division sats). Incremental
    /// push-pop consumers (BMC/IC3 — the measured beneficiaries of the
    /// slices) leave this false and keep the trail-restored fast path.
    eager_repropagate_on_pop: bool,
    /// Whether any direct variable bound has changed since the last
    /// `compute_implied_bounds()` call. When false, the O(num_vars) direct-bound
    /// overlay loop can be skipped because no direct bound has been updated.
    /// Set true by `assert_var_bound` and cleared by `compute_implied_bounds`.
    pub(crate) direct_bounds_changed_since_implied: bool,
    /// Transient restraint flag (sat-side-model-search diagnosis Fix #2):
    /// when set, `compute_implied_bounds()` caps the inner row-derivation
    /// cascade to a single pass (direct overlay + one row pass, no transitive
    /// cascade). `run_post_simplex_propagation` sets this only for BCP-time
    /// checks on the propagation-disabled cex lane (`no_theory_propagation`)
    /// and clears it immediately after the call, so final-check cascades and
    /// all propagation-enabled lanes are unaffected. Sound: deriving fewer
    /// implied bounds is always a weaker (sound) propagation; the full cascade
    /// still runs at final check, preserving eager-arm completeness.
    bcp_implied_single_pass: bool,
    /// #lra-inc-engine S3 (warm theory): set when this check-sat runs on a theory
    /// solver REUSED across check-sats (AY_LRA_INC_WARM). Caps the implied-bounds
    /// recursive cascade so a stale warm cache on a region shift can't explode
    /// (implied_row_recursive). The monotone benefit is unaffected (it
    /// early-returns via #inc-cib-nodelta before the cascade). Sound: advisory.
    warm_reuse_hint: bool,
    /// Variables whose direct bounds changed since the last
    /// `compute_implied_bounds()` call. Used for incremental overlay.
    direct_bounds_changed_vars: Vec<u32>,
    /// Monotonic generation counter, incremented each time any variable's
    /// implied bound is tightened in `compute_implied_bounds()`. Used with
    /// `var_bound_gen` and `row_computed_gen` to skip rows whose input
    /// bounds have not changed since last computation (#8003).
    bound_generation: u64,
    /// Per-variable generation: set to `bound_generation` when the variable's
    /// implied bound is tightened. Indexed by variable id.
    var_bound_gen: Vec<u64>,
    /// Per-row generation: set to `bound_generation` after the row is fully
    /// processed in `compute_implied_bounds()`. If all variables in the row
    /// have `var_bound_gen <= row_computed_gen[row_idx]`, the row can be
    /// skipped because no input bound has changed since it was last analyzed.
    row_computed_gen: Vec<u64>,
    /// Per-variable count of implied-bound tightenings that REPLACED an
    /// existing bound since the variable's direct bound last changed (#8857).
    ///
    /// Zeno-cascade throttle: on cyclic tableaus (x and y mutually bounded
    /// through rows), `compute_implied_bounds()` can derive an infinite
    /// sequence of epsilon-tighter bounds (each round strictly "tighter",
    /// never converging). Each tightening bumps `bound_generation`,
    /// re-touching the containing rows, so the generation skip never fires
    /// and every subsequent call re-analyzes the same rows with exact
    /// (bignum) arithmetic and ever-growing denominators.
    ///
    /// Once a variable's replacing-tighten count exceeds
    /// `IMPLIED_TIGHTEN_STREAK_CAP`, further replacing tightenings are only
    /// stored when they cross an atom threshold (`bound_is_interesting`).
    /// Atom thresholds are finite, so the lattice reaches a fixpoint and the
    /// dirty-row machinery (generation skip, touched-row decay,
    /// stale-cascade skip) becomes effective again.
    ///
    /// Soundness: discarding a derived bound only weakens propagation; it
    /// never changes verdicts. The streak resets when the variable's DIRECT
    /// bound changes (new assertions legitimately enable new derivations)
    /// and on pop/reset (bounds revert).
    implied_tighten_streak: Vec<u32>,
    /// Reusable per-call scratch for `compute_implied_bounds`' per-variable
    /// tighten counters (#certora-ib-scratch). Semantically the counters are
    /// PER CALL (previously `let mut tighten_count = vec![0; num_vars]`), but
    /// allocating + zeroing an O(num_vars) vector on EVERY call was ~12% of
    /// the observed solve window on 10^5-variable industrial files (Certora
    /// QF_UFLIA). The scratch persists across calls;
    /// `implied_tighten_touched` records the indices a call dirtied so the
    /// next call restores zeros in O(touched).
    implied_tighten_scratch: Vec<u8>,
    /// Dirty indices of `implied_tighten_scratch` (see above).
    implied_tighten_touched: Vec<u32>,
    /// #cib-alloc: persistent per-call scratch buffers for
    /// `compute_implied_bounds`, replacing the former per-call `Vec::new()`
    /// allocations. The correct-mode profile on fisher_star.ind showed ~500
    /// samples inside `compute_implied_bounds` in `finish_grow`/`grow_one`/
    /// `RawVecInner` (Vec allocation + growth scaffolding), because the
    /// function is re-entered many times per check (the run_post_simplex
    /// fixpoint) and each entry freshly allocated these vectors. Each buffer is
    /// `mem::take`n at entry and restored at exit; every use clears the buffer
    /// before writing, so reuse is byte-identical (same derived bounds, order,
    /// and verdicts) — it only avoids the per-call malloc/realloc.
    ib_lb_contribs_scratch: Vec<(usize, Rational, bool)>,
    ib_ub_contribs_scratch: Vec<(usize, Rational, bool)>,
    ib_lb_contribs_f64_scratch: Vec<f64>,
    ib_ub_contribs_f64_scratch: Vec<f64>,
    ib_updates_scratch: Vec<(usize, Option<ImpliedBound>, Option<ImpliedBound>)>,
    ib_row_indices_scratch: Vec<usize>,
    ib_round_newly_bounded_scratch: Vec<u32>,
    ib_cross_neg_updates_scratch: Vec<(usize, Option<ImpliedBound>, Option<ImpliedBound>)>,
    ib_cascade_rows_scratch: Vec<usize>,
    ib_fixed_vars_scratch: Vec<u32>,
    /// Cumulative implied-bound work (compute_implied_bounds calls + derivations)
    /// this solver lifetime. Bounded by `implied_work_budget` so the outer DPLL(T)
    /// re-entry oscillation terminates deterministically. NOT reset on pop (that is
    /// the oscillation's own action); the verifier builds a fresh solver per
    /// obligation, so this is effectively a per-obligation budget.
    implied_work_done: u64,
    /// Sticky heuristic flag (#certora-bigint-fast): true once any DIRECT
    /// bound with a `Rational::Big` value has been overlaid into the
    /// implied-bounds lattice. On such instances (e.g. Certora VCs with
    /// 2^256-scale range constraints) the exact-Rational row accumulation in
    /// `compute_implied_bounds` is bignum-dominated even on NARROW rows, so
    /// the f64 pre-screen (normally gated to rows with >= 4 coefficients,
    /// where its overhead pays off on i64 workloads) is extended to rows of
    /// width >= 2. Sticky-monotone by design: never cleared on pop/reset —
    /// it only widens a conservative screen whose skip decisions are
    /// sound regardless (a skipped derivation only weakens propagation).
    big_bound_seen: bool,
    /// Whether the last simplex run found a feasible assignment (#6256).
    /// When false, the simplex-skip must not return Sat because variable
    /// values are left in an infeasible state. Returns Unknown instead and
    /// keeps dirty=true so the early-return path doesn't trigger Sat either.
    last_simplex_feasible: bool,
    /// Scope stack for last_simplex_feasible across push/pop (#6209).
    last_simplex_feasible_scopes: Vec<bool>,
    /// Snapshot of variable values from the last feasible simplex solution (#8064).
    feasible_value_snapshot: Vec<Rational>,
    /// #8255: total_pivots value at the time of the last save_feasible_snapshot().
    /// When total_pivots == pivots_at_last_snapshot, simplex didn't pivot since
    /// the last snapshot, so variable values are unchanged and the copy is a no-op.
    /// Initialized to u64::MAX to force the first snapshot to execute.
    pivots_at_last_snapshot: u64,
    /// #8008: Pre-computed phase hints from the last feasible simplex model.
    ///
    /// Maps each registered atom TermId to its model-consistent polarity.
    /// Computed in `save_feasible_snapshot()` alongside the variable value
    /// snapshot, so `suggest_phase()` becomes an O(1) HashMap lookup instead
    /// of O(coefficients) Rational arithmetic per atom.
    ///
    /// Z3's `get_phase()` calls `lp().compare_values()` which is a single
    /// comparison. This cache gives AY the same O(1) phase lookup semantics.
    ///
    /// Invalidated on reset/soft_reset (same lifecycle as feasible_value_snapshot).
    phase_hint_cache: HashMap<TermId, bool>,
    /// Monotonic generation counter for `phase_hint_cache`. Bumped whenever the
    /// cache content could have changed (full/incremental rebuild or clear).
    /// Exposed via `TheorySolver::phase_hint_epoch` so the SAT-side phase
    /// seeder can skip its O(atoms) re-seed when the suggestions are unchanged
    /// since the last seed (#8003 follow-up: phase seeding was the top
    /// in-solver self-time leaf on QF_LRA induction benchmarks). Over-bumping
    /// is safe (an unnecessary re-seed); the invariant that matters is that it
    /// never stays put across a real cache change, which is why every mutation
    /// site bumps it.
    phase_hint_epoch: u64,
    /// Number of tableau rows at the start of check(). Used to detect if
    /// new rows were added during atom processing (which requires simplex).
    rows_at_check_start: usize,
    /// Registered `to_int(x)` terms: `(to_int_var_id, inner_arg_term)`.
    /// Collected during `parse_linear_expr`; floor axiom bounds injected
    /// during `check()`. Floor axiom: `to_int(x) <= x < to_int(x) + 1`,
    /// i.e., `x - to_int(x) >= 0` and `x - to_int(x) < 1` (#5944).
    to_int_terms: Vec<(u32, TermId)>,
    /// Already-injected `to_int` axiom var IDs in this scope (avoid
    /// duplicate injection within one check cycle). Cleared on soft_reset
    /// since bounds are cleared.
    injected_to_int_axioms: HashSet<u32>,
    /// Variables whose bounds tightened since the last `propagate()` call.
    /// Used to avoid scanning ALL atoms in the atom cache — only atoms
    /// involving dirty variables need re-checking (#4919 propagation opt).
    propagation_dirty_vars: DenseU32Set,
    /// Scratch buffer for collecting dirty vars into a Vec for functions that
    /// require `&[u32]`. Reused across calls to avoid per-check allocation (#7719 D3).
    dirty_vars_scratch: Vec<u32>,
    /// Scratch buffer returned by `compute_implied_bounds()` for reuse across
    /// fixpoint iterations, avoiding per-iteration HashSet allocation.
    #[allow(dead_code)]
    newly_bounded_scratch: HashSet<u32>,
    /// Dedicated wakeup list for compound atoms. Unlike `atom_index`, entries
    /// here do not imply a direct bound on the key variable; they only mean the
    /// compound atom should be reconsidered when that variable's bound changes.
    /// Keyed by constituent variables and the compound slack var (#4919 Phase 5).
    compound_use_index: HashMap<u32, Vec<CompoundAtomRef>>,
    /// Reverse index: for each internal variable ID, the list of atom TermIds
    /// whose expression references that variable. Built during `register_atom()`.
    /// Kept as a generic fallback/recount structure; compound propagation now
    /// uses `compound_use_index` as its primary wakeup path (#4919 Phase 5).
    var_to_atoms: HashMap<u32, Vec<TermId>>,
    /// Number of compound propagations queued during the most recent `check()`.
    /// Logged alongside `atom_index` stats to distinguish direct-bound coverage
    /// from compound wakeup coverage (#4919 Phase 5).
    last_compound_propagations_queued: usize,
    /// Number of dirty vars whose key existed in `compound_use_index` (#6579).
    last_compound_wake_dirty_hits: usize,
    /// Number of distinct compound atoms reached from dirty vars before
    /// `try_queue_compound_propagation()` filtering (#6579).
    last_compound_wake_candidates: usize,
    /// O(1) lookup from basic variable ID to its row index in `self.rows`.
    /// Replaces the O(rows) linear scan `self.rows.iter().find(|r| r.basic_var == var)`.
    /// Maintained on row push, pivot, pop, and clear (#4919 Phase B).
    basic_var_to_row: HashMap<u32, usize>,
    /// Rows whose variables had a bound tightened since the last `compute_implied_bounds()`.
    /// Enables skipping untouched rows in the first fixpoint iteration (#4919 Phase A, Gap 2).
    /// Populated from `col_index` when `assert_var_bound` tightens a bound.
    /// Reset after `compute_implied_bounds` completes.
    /// #inc-dense-sets: epoch-stamped dense set — row indices are dense, so
    /// hashing was pure overhead on the per-backtrack reseed path (the
    /// dominant HashMap::insert leaf after the trail wins).
    touched_rows: DenseIdxSet,
    /// True when `touched_rows` contains fresh rows from direct bound assertions
    /// or an implied-bound fixpoint that hit its cap before convergence.
    ///
    /// `compute_implied_bounds()` reseeds `touched_rows` with cascade rows from
    /// newly-derived implied bounds. Callers clear this flag when the fixpoint
    /// converges so those rows can be treated as stale cache state; callers keep
    /// it set only when there is real capped cascade work left to process (#8422).
    propagate_direct_touched_rows_pending: bool,
    /// #8468: True when `compute_implied_bounds` was just run in
    /// `check_during_propagate_impl` via `run_post_simplex_propagation` and no
    /// new direct bounds have been asserted since. When set, `propagate_impl`
    /// can skip its own `compute_implied_bounds` call because the results are
    /// still up-to-date. Cleared by `assert_var_bound` / `assert_var_eq_bound`
    /// (any new direct bound invalidates freshness).
    implied_bounds_fresh: bool,
    /// Incrementally-tracked disequality atoms: (term, expr, asserted_value).
    /// Avoids the O(trail) scan on every check() call by recording disequalities
    /// when they are first asserted. Managed via push/pop for backtracking (#4919).
    disequality_trail: Vec<(TermId, LinearExpr, bool)>,
    /// A5 core (demand-driven equality rows, AY_A5_CORE=1): equality atoms
    /// asserted during BCP-time checks are DEFERRED (no tableau bounds);
    /// after each full-check simplex-Sat, violated deferrals MATERIALIZE and
    /// the solve iterates. (term, expr, value) in assertion order.
    pub(crate) deferred_eq_atoms: Vec<(TermId, LinearExpr, bool)>,
    pub(crate) a5_core: bool,
    /// Position in `disequality_trail` at each push scope, for backtracking.
    disequality_trail_scopes: Vec<usize>,
    /// Shared disequalities from Nelson-Oppen: (expr, reason_lits, eq_term) (#5228).
    /// These are disequalities forwarded from other theories (e.g., negated UF-equalities).
    /// Unlike `disequality_trail`, reasons are TheoryLit vectors rather than a single atom.
    /// The optional `TermId` is the original equality term, used to make split clauses
    /// conditional (#6131): `term OR (x < c) OR (x > c)` instead of unconditional.
    shared_disequality_trail: Vec<(TermId, TermId, LinearExpr, Vec<TheoryLit>, Option<TermId>)>,
    /// Position in `shared_disequality_trail` at each push scope.
    shared_disequality_trail_scopes: Vec<usize>,
    /// Per-variable count of unassigned single-variable bound atoms.
    /// Used to skip rows in `compute_implied_bounds` where no variable has pending atoms,
    /// since bound derivations for those rows cannot produce any propagation (#4919 Phase A, Gap 1).
    /// Indexed by internal var ID. Incremented in `register_atom`, decremented when atom asserted.
    unassigned_atom_count: Vec<u32>,
    /// Max-heap of infeasible basic variables keyed by bound violation magnitude (#4919).
    /// Greatest-error pivot: extracts the variable with the largest bound violation first.
    /// In bland_mode, the heap is rebuilt with error=0 so smallest-var-index wins (anti-cycling).
    /// Reference: Z3 `select_greatest_error_var()` in `theory_arith_core.h:2270-2300`.
    infeasible_heap: std::collections::BinaryHeap<ErrorKey>,
    /// Epoch stamp for `in_infeasible_heap` (#inc-heap-epoch): an entry is a
    /// member iff its stamp equals `heap_epoch`. Bumping the epoch logically
    /// clears the whole membership set in O(1), replacing the O(num_vars)
    /// flag-zeroing loop that ran on EVERY pop / heap rebuild. Starts at 1;
    /// wraps re-zero the vec (once per 2^32 clears).
    heap_epoch: u32,
    /// Membership stamps for infeasible_heap (#inc-heap-epoch): member iff
    /// `in_infeasible_heap[var] == heap_epoch`. Previously `Vec<bool>`:
    /// var is currently in the heap. Prevents duplicate insertion (O(1) check).
    in_infeasible_heap: Vec<u32>,
    /// When true, the infeasible heap needs a full rebuild before simplex.
    /// Set to true by lifecycle methods (pop, reset, soft_reset) and row additions.
    /// Set to false after `rebuild_infeasible_heap()`. When false, incremental
    /// `track_var_feasibility()` calls keep the heap current (#8782).
    heap_stale: bool,
    /// #warm-simplex (`AY_LRA_WARM_SIMPLEX_STATE`, default OFF): delta-only
    /// simplex bookkeeping across pops — persistent infeasible-candidate
    /// structures, a non-basic dirty set replacing the O(vars) SAT-exit scan,
    /// and a last-feasible value delta for conflict recovery. See
    /// `warm_state.rs` for the full invariant story. All reads are gated on
    /// `warm.enabled`; flag OFF keeps today's code paths byte-identical.
    pub(crate) warm: warm_state::WarmSimplexState,
    /// Speculative f64 simplex shadow state (Tier 0, #8184).
    #[allow(dead_code)]
    float_simplex: simplex::float_simplex::FloatSimplex,
    /// Reusable buffer for `collect_row_reasons_recursive` seen set (#6364).
    /// Avoids allocating a fresh HashSet on every `queue_bound_refinement_request` call.
    /// Cleared before each use, but capacity is preserved across calls.
    reason_seen_buf: HashSet<(TermId, bool)>,
    /// NOT-unwrap cache (#6590 Packet 1): maps literal TermId to (inner_term, negated).
    /// For NOT(inner), stores (inner, true). For bare atoms, stores (atom, false).
    /// Eliminates `self.terms().get()` in `assert_literal`'s hot path.
    not_inner_cache: HashMap<TermId, (TermId, bool)>,
    /// Constant-Bool cache (#6590 Packet 1): maps atom TermId to Some(bool_value)
    /// if the term is a constant Bool, None otherwise. Eliminates `self.terms().get()`
    /// in `check()`'s per-atom constant-Bool detection.
    const_bool_cache: HashMap<TermId, Option<bool>>,
    /// Per-term refinement eligibility cache (#6590 Packet 1): maps TermId to whether
    /// `term_supports_bound_refinement` returns true. Eliminates `self.terms().get()`
    /// in the bound refinement warm path.
    refinement_eligible_cache: HashMap<TermId, bool>,
    /// Per-term integer-sort cache (#6590 Packet 1): maps TermId to whether
    /// `self.terms().sort(term) == Sort::Int`. Eliminates `self.terms().sort()` in
    /// the bound refinement warm path.
    is_integer_sort_cache: HashMap<TermId, bool>,
    /// BCP implied-bounds dry streak counter (#8200).
    bcp_implied_dry_streak: u32,
    /// BCP cascade dry streak counter (#8255). Tracks consecutive BCP checks
    /// where cascading beyond depth 1 in compute_implied_bounds produced zero
    /// additional bounds. When >= 3, cascade depth is throttled to 1.
    bcp_cascade_dry_streak: u32,
    /// Maximum row width (number of nonbasic coefficients) across all tableau rows.
    /// Updated when rows are added. Used to detect dense LP problems and adjust
    /// implied-bounds cascade strategy: dense problems (width > 50) skip per-atom
    /// cascade in BCP mode to avoid O(atoms * width * cascade_rounds) cost (#8003).
    max_row_width: usize,
    /// Cross-negation bound propagation map (#8008).
    /// Indexed by internal slack variable ID. Entry `Some((partner, k))` means
    /// this slack var S1 has a negation partner S2 where S1 + S2 = K.
    /// When UB(S1) is tightened, LB(S2) = K - UB(S1).
    /// When LB(S1) is tightened, UB(S2) = K - LB(S1).
    /// Built by `build_negation_partners()` after `expr_to_slack` is populated.
    negation_partners: Vec<Option<(u32, Rational)>>,
    /// JIT-compiled theory bound propagation (#8262).
    /// Pre-compiles per-variable atom bound checks using i64/i128 arithmetic
    /// instead of BigRational, reducing per-atom comparison cost from ~50ns to ~2ns.
    /// Compiled after initial atom registration; used during propagation when
    /// variable bounds are Small(i64, i64).
    theory_prop_jit: ay_jit::TheoryPropJit,
    /// Whether the JIT propagators have been compiled for the current atom_index.
    /// Set to `true` after `compile_theory_propagation_jit()`, reset to `false`
    /// when new atoms are registered.
    theory_prop_jit_compiled: bool,
    /// Reusable result buffer for JIT propagation to avoid per-call allocation.
    theory_prop_results: Vec<ay_jit::PropagationResult>,
    /// JIT-compiled pivot row cache (#8276).
    /// Tracks pivot row reuse counts and caches native-code versions of
    /// frequently-reused rows for fast multiply-add updates.
    pivot_row_cache: ay_jit::PivotRowCache,
    /// Metadata-only basis-region requests captured at safe simplex boundaries.
    lra_basis_region_requests: Vec<ay_jit::LraBasisRegionRequest>,
    /// Last pivot neighborhood awaiting safe-boundary request construction.
    lra_basis_region_candidate: Option<lra_region::LraBasisRegionCandidate>,
    /// Basis-generation epoch used to invalidate LRA basis-region JIT artifacts.
    lra_basis_region_basis_epoch: u64,
    /// #8257: Standalone-simplex mode. When true, check() skips post-simplex
    /// propagation and speculative model-equality discovery. Unsupported atoms
    /// and disequalities retain their soundness gates. Used by both the conflict
    /// verification pipeline and standalone objective optimization to avoid
    /// DPLL(T)-driver obligations and expensive irrelevant propagation.
    standalone_simplex_mode: bool,
    /// #7853: Persistent scratch buffer for interval propagation candidates.
    /// Reused across propagate() calls to avoid per-call Vec allocation.
    /// Contains (atom_term, strict) pairs for dirty-var atoms.
    propagation_candidates_buf: Vec<(TermId, bool)>,
    /// #7853: Persistent scratch buffer for interval propagation seen set.
    /// Tracks which atom_terms have already been added to candidates_buf.
    propagation_seen_buf: HashSet<TermId>,
    /// #7853: Persistent scratch buffer for touched_rows snapshot.
    /// Avoids cloning the full `HashSet<usize>` each propagate() call.
    touched_rows_snapshot_buf: DenseIdxSet,
    /// #7853: Persistent scratch buffer for newly_bounded_sorted in propagate().
    /// Avoids per-fixpoint-iteration Vec allocation.
    newly_bounded_sorted_buf: Vec<u32>,
    /// #8608: Persistent output buffer for propagate_impl() and
    /// drain_pending_propagations_impl(). Avoids per-call Vec allocation by
    /// retaining the high-water-mark capacity across calls. The buffer is
    /// filled during propagation, then transferred via `std::mem::take()`.
    propagation_output_buf: Vec<TheoryPropagation>,
    /// #8599: Persistent buffer for interval reason dedup in the hot propagation
    /// loop. Avoids per-candidate HashSet allocation in collect_interval_reasons.
    interval_reason_seen_buf: HashSet<(TermId, bool)>,
    /// #8599: Persistent buffer for all_newly_bounded in propagate_impl()
    /// fixpoint loop. Avoids per-propagation HashSet allocation.
    all_newly_bounded_buf: DenseU32Set,
    /// reason-alloc-wip: reused DFS scratch for implied-bound reason collection.
    ///
    /// `collect_reasons_from_explanation` / `collect_row_reasons_dedup` /
    /// `collect_single_row_reasons` / `make_eager_implied_propagation_reasons`
    /// walk the implied-bound explanation graph and previously allocated a
    /// fresh `HashSet::default()` for their `visited`/`on_stack`/`seen` working
    /// sets on EVERY call — a hot per-propagation allocation (profiled as
    /// HashMap-insert + reserve_rehash churn on the derivation hot path). These
    /// three cells hold those sets across calls so the allocation is amortized.
    ///
    /// PURE SCRATCH, never solver state (excluded from snapshots / equality).
    /// Behind `RefCell` because the reason-collection methods take `&self`
    /// (callers hold live `&self.implied_bounds` borrows across the call, so
    /// `&mut self` is unavailable). Borrowed via a `ReasonScratch` guard that
    /// `mem::take`s the set out (momentary borrow only) and CLEARS on acquire.
    /// Clearing before every traversal is load-bearing for byte-identity: a
    /// stale membership entry would skip a graph node, drop a real antecedent,
    /// and change the reason set (a potentially different/over-strong UNSAT
    /// core). Taking the set out means accidental future re-entrancy cannot
    /// panic on a double `borrow_mut` — a nested user gets the empty
    /// placeholder and allocates, which stays correct.
    scratch_reason_visited: std::cell::RefCell<HashSet<(u32, bool)>>,
    scratch_reason_on_stack: std::cell::RefCell<HashSet<(u32, bool)>>,
    scratch_reason_seen: std::cell::RefCell<HashSet<(TermId, bool)>>,
}

// SAFETY: LraSolver contains a `*const TermStore` raw pointer (`terms_ptr`)
// which prevents auto-impl of Send. The pointer is set via `set_terms()`
// before each operation batch and cleared via `unset_terms()` after.
//
// Send is sound because:
// 1. The raw pointer is never dereferenced after `unset_terms()` (it is nulled).
// 2. When the pointer IS valid (between set_terms/unset_terms), the solver is
//    used exclusively by a single thread — ownership is transferred, not shared.
// 3. All other fields (Vec, HashMap, HashSet, etc.) are themselves Send.
// 4. The pointer is only dereferenced via `terms()` which takes `&self` and
//    panics if the pointer is null, providing a runtime guard.
//
// Sync is deliberately NOT implemented (#8462 audit). LraSolver is never shared
// as `&LraSolver` across threads — it is always used via `&mut self`. The
// `terms()` method dereferences a raw pointer via `&self`, so concurrent calls
// from multiple threads would be unsound (data race on the TermStore even if
// the pointer itself is not mutated). Removing Sync makes this invariant
// compiler-enforced.
//
// Audit evidence (#8462):
// - Single dereference site: lifecycle.rs `terms()` → `unsafe { &*ptr }`
// - 44 call sites of `self.terms()`, all via `&self`/`&mut self` on methods
// - No `Arc<LraSolver>` exists anywhere in the codebase
// - All usages are owned (`let mut lra = LraSolver::new(...)`) or struct fields
//   accessed via `&mut self` (e.g., `combiner.rs:51`)
// - Kani proof `proof_set_terms_unset_terms_toggle_pointer_6612` in
//   `verification/unsafe_bracket.rs` verifies the pointer state machine
// SAFETY: LraSolver contains a `*const TermStore` raw pointer which is not
// auto-Send. The pointer is safe to send across threads because:
// 1. The pointer is never dereferenced after `unset_terms()` (nulled out).
// 2. When valid (between set_terms/unset_terms), the solver has exclusive
//    single-threaded ownership — it is transferred, not shared.
// 3. All other fields (Vec, HashMap, etc.) are themselves Send.
// 4. No `Arc<LraSolver>` exists in the codebase (Sync is NOT implemented).
// See audit evidence in the block comment above for verification details.
#[allow(unsafe_code)]
unsafe impl Send for LraSolver {}

impl LraSolver {
    /// Record that an atom's propagation was sent to the SAT layer
    /// (#inc-prop-trail). Trails first-time inserts so `pop_inner` can remove
    /// exactly the entries from popped scopes in O(popped) instead of
    /// wholesale-clearing `propagated_atoms` on every backtrack.
    /// Associated fn over the two fields (not `&mut self`) so call sites with
    /// live borrows of other fields keep Rust's disjoint field-borrow rules.
    #[inline]
    pub(crate) fn note_propagated(
        propagated_atoms: &mut HashSet<(TermId, bool)>,
        propagated_trail: &mut Vec<(TermId, bool)>,
        term: TermId,
        value: bool,
    ) {
        if propagated_atoms.insert((term, value)) {
            propagated_trail.push((term, value));
        }
    }

    /// Number of atoms registered with this solver (#certora-phase-epoch).
    /// Used by the combined-theory phase-hint epoch gate to distinguish
    /// giant industrial instances (where the SAT seeder's O(atoms) re-scan
    /// per BCP quiescence is the wall) from small crafted ones (where the
    /// re-scan is cheap and the historical every-quiescence trajectory is
    /// load-bearing for several protected greens).
    #[must_use]
    pub fn registered_atom_count(&self) -> usize {
        self.registered_atoms.len()
    }
}

#[cfg(kani)]
impl LraSolver {
    /// Kani-only constructor: initializes only the pointer field, avoids
    /// `TermStore::new()` and `lra_debug_flags()` which trigger deep
    /// BTree/HashMap symbolic exploration that CBMC cannot handle (#6612).
    #[cfg(kani)]
    pub(crate) fn new_kani_minimal(ptr: *const TermStore) -> Self {
        Self {
            terms_ptr: ptr,
            rows: Vec::new(),
            vars: Vec::new(),
            term_to_var: HashMap::default(),
            var_to_term: HashMap::default(),
            next_var: 0,
            trail: Vec::new(),
            bound_revision: 0,
            scopes: Vec::new(),
            asserted: HashMap::default(),
            asserted_trail: Vec::new(),
            cross_theory_asserted: HashMap::default(),
            cross_theory_asserted_trail: Vec::new(),
            cross_theory_asserted_scopes: Vec::new(),
            atom_cache: HashMap::default(),
            ite_link_terms: Vec::new(),
            ite_link_terms_seen: HashSet::default(),
            current_parsing_atom: None,
            dirty: false,
            pending_equalities: Vec::new(),
            propagated_equality_pairs: HashSet::default(),
            propagated_disequality_pairs: HashSet::default(),
            trivial_conflict: None,
            bound_atoms: HashSet::default(),
            persistent_unsupported_atoms: HashSet::default(),
            persistent_unsupported_trail: Vec::new(),
            persistent_unsupported_scope_marks: Vec::new(),
            integer_mode: false,
            gomory_rng: 1,
            pivot_rng: 1,
            debug_lra: false,
            debug_lra_bounds: false,
            debug_lra_assert: false,
            debug_lra_reset: false,
            debug_lra_nelson_oppen: false,
            debug_intern: false,
            no_theory_propagation: false,
            // #warm-theory probe: AY_LRA_NO_IMPLIED disables compute_implied_bounds
            // (sound: weaker propagation, feasibility still owned by the dual
            // simplex) — used to test whether the implied-bounds cascade over
            // accumulated rows is the O(depth²) wall on the warm-theory lane.
            no_implied_bounds: std::env::var("AY_LRA_NO_IMPLIED")
                .is_ok_and(|v| v != "0" && !v.is_empty()),
            no_bound_refinement: false,
            max_fixpoint_rounds: None,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            propagation_budget_exhaustions: 0,
            bcp_simplex_skips: 0,
            bcp_post_simplex_fast_skips: 0,
            assert_dirty_skips: 0,
            propagate_implied_bounds_fresh_skips: 0,
            full_check_conflict_count: 0,
            eager_reason_count: 0,
            deferred_reason_count: 0,
            deferred_direct_count: 0,
            deferred_interval_count: 0,
            deferred_implied_count: 0,
            lazy_emitted_count: 0,
            lazy_rejected_count: 0,
            emitted_direct_count: 0,
            emitted_implied_count: 0,
            emitted_implied_row_count: 0,
            stale_reason_filtered_count: 0,
            stale_conflict_rejected_count: 0,
            simplex_sat_count: 0,
            total_pivots: 0,
            full_check_pivots: 0,
            simplex_budget_exhaustions: 0,
            global_budget_exhaustions: 0,
            check_pivot_count: 0,
            check_pivot_budget_exhaustions: 0,
            max_inner_cascade_depth: 0,
            total_inner_cascade_rounds: 0,
            f64_rows_skipped: 0,
            f64_vars_skipped: 0,
            max_outer_fixpoint_iters: 0,
            total_outer_fixpoint_iters: 0,
            cascade_depth_throttles: 0,
            registered_atoms: HashSet::default(),
            atom_index: HashMap::default(),
            pending_propagations: Vec::new(),
            pending_bound_refinements: Vec::new(),
            propagated_atoms: HashSet::default(),
            combined_theory_mode: false,
            atom_slack: HashMap::default(),
            expr_to_slack: HashMap::default(),
            slack_var_set: HashSet::default(),
            implied_bounds: Vec::new(),
            fixed_term_value_table: HashMap::default(),
            fixed_term_value_members: HashMap::default(),
            pending_fixed_term_equalities: Vec::new(),
            pending_offset_equalities: Vec::new(),
            col_index: Vec::new(),
            pivot_work_vec: Vec::new(),
            pivot_work_dirty: Vec::new(),
            pivot_row_coeffs_buf: Vec::new(),
            pivot_row_constant_buf: Rational::zero(),
            pivot_subst_i64_buf: Vec::new(),
            bland_mode: false,
            basis_repeat_count: 0,
            last_check_trail_pos: 0,
            last_diseq_check_had_violation: false,
            pending_diseq_splits: Vec::new(),
            pending_expr_splits: Vec::new(),
            bounds_tightened_since_simplex: false,
            post_simplex_bounds_added: false,
            vars_tightened_since_simplex: Vec::new(),
            guard_clean_valid: false,
            last_simplex_verified: false,
            guard_tracked_only: false,
            rows_len_at_last_implied: 0,
            ib_overlay_complete: false,
            implied_trail: Vec::new(),
            implied_trail_scopes: Vec::new(),
            propagated_trail: Vec::new(),
            propagated_trail_scopes: Vec::new(),
            eager_repropagate_on_pop: false,
            direct_bounds_changed_since_implied: true,
            bcp_implied_single_pass: false,
            warm_reuse_hint: false,
            direct_bounds_changed_vars: Vec::new(),
            bound_generation: 0,
            var_bound_gen: Vec::new(),
            row_computed_gen: Vec::new(),
            last_simplex_feasible: false,
            last_simplex_feasible_scopes: Vec::new(),
            feasible_value_snapshot: Vec::new(),
            pivots_at_last_snapshot: u64::MAX,
            snapshot_pivot_skips: 0,
            rows_at_check_start: 0,
            to_int_terms: Vec::new(),
            injected_to_int_axioms: HashSet::default(),
            propagation_dirty_vars: DenseU32Set::default(),
            dirty_vars_scratch: Vec::new(),
            newly_bounded_scratch: HashSet::default(),
            compound_use_index: HashMap::default(),
            var_to_atoms: HashMap::default(),
            last_compound_propagations_queued: 0,
            last_compound_wake_dirty_hits: 0,
            last_compound_wake_candidates: 0,
            basic_var_to_row: HashMap::default(),
            touched_rows: DenseIdxSet::default(),
            propagate_direct_touched_rows_pending: false,
            implied_bounds_fresh: false,
            disequality_trail: Vec::new(),
            deferred_eq_atoms: Vec::new(),
            a5_core: std::env::var_os("AY_A5_CORE").is_some(),
            disequality_trail_scopes: Vec::new(),
            shared_disequality_trail: Vec::new(),
            shared_disequality_trail_scopes: Vec::new(),
            unassigned_atom_count: Vec::new(),
            infeasible_heap: std::collections::BinaryHeap::new(),
            heap_epoch: 1,
            in_infeasible_heap: Vec::new(),
            heap_stale: true,
            warm: warm_state::WarmSimplexState::new(),
            float_simplex: simplex::float_simplex::FloatSimplex::new(),
            reason_seen_buf: HashSet::default(),
            not_inner_cache: HashMap::default(),
            const_bool_cache: HashMap::default(),
            refinement_eligible_cache: HashMap::default(),
            is_integer_sort_cache: HashMap::default(),
            bcp_implied_dry_streak: 0,
            bcp_cascade_dry_streak: 0,
            max_row_width: 0,
            theory_prop_jit: ay_jit::TheoryPropJit::new(),
            theory_prop_jit_compiled: false,
            theory_prop_results: Vec::new(),
            jit_propagation_count: 0,
            pivot_row_cache: ay_jit::PivotRowCache::new(),
            lra_basis_region_requests: Vec::new(),
            lra_basis_region_candidate: None,
            lra_basis_region_basis_epoch: 0,
            precision_i64_rows: 0,
            precision_i128_rows: 0,
            precision_big_rows: 0,
            negation_partners: Vec::new(),
            standalone_simplex_mode: false,
            propagation_candidates_buf: Vec::new(),
            propagation_seen_buf: HashSet::default(),
            touched_rows_snapshot_buf: DenseIdxSet::default(),
            newly_bounded_sorted_buf: Vec::new(),
            propagation_output_buf: Vec::new(),
            interval_reason_seen_buf: HashSet::default(),
            all_newly_bounded_buf: DenseU32Set::default(),
            // reason-alloc-wip: reused reason-collection DFS scratch (pure
            // scratch, cleared on each use — starts empty).
            scratch_reason_visited: std::cell::RefCell::default(),
            scratch_reason_on_stack: std::cell::RefCell::default(),
            scratch_reason_seen: std::cell::RefCell::default(),
        }
    }
}

// ============================================================================
// Kani Verification Harnesses
// ============================================================================
//
// These proofs verify the core invariants of the LRA (Linear Real Arithmetic) solver:
// 1. LinearExpr operations: term combining, scaling, negation
// 2. Bounds consistency: lower <= upper implies feasibility
// 3. Tableau invariants: pivot operations preserve structure
// 4. Push/pop state consistency

#[cfg(kani)]
mod verification;

#[cfg(test)]
mod empty_conflict_tests;
#[cfg(test)]
mod issue_6586_tests;
#[cfg(test)]
mod issue_6588_tests;
#[cfg(test)]
mod issue_6612_tests;
#[cfg(test)]
mod issue_6617_fixed_term_table_tests;
#[allow(clippy::panic)]
#[cfg(test)]
mod tests;
#[cfg(test)]
mod types_tests;
