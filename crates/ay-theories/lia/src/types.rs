// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! LIA type definitions and utility functions.
//!
//! Extracted from `lib.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{TermId, TermStore};
use ay_core::{DiscoveredEquality, TheoryLit};
use ay_lra::LraSolver;
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};
use std::sync::OnceLock;

use crate::assertion_view;
use crate::linear_cache::{AffineCacheMap, DiophParseCacheMap, LinearCacheMap};

/// #6359: Cached debug flags for LIA solver.
///
/// Environment variables are read once per process via OnceLock, not per
/// solver construction. In DPLL(T) loops where LiaSolver is created fresh
/// on each iteration, this eliminates ~13 syscalls per iteration.
pub(crate) struct LiaDebugFlags {
    pub(crate) debug_lia: bool,
    pub(crate) debug_lia_branch: bool,
    pub(crate) debug_lia_check: bool,
    pub(crate) debug_lia_nelson_oppen: bool,
    pub(crate) debug_patch: bool,
    pub(crate) debug_gcd: bool,
    pub(crate) debug_gcd_tab: bool,
    pub(crate) debug_dioph: bool,
    pub(crate) debug_hnf: bool,
    pub(crate) debug_mod: bool,
    pub(crate) debug_enum: bool,
}

static LIA_DEBUG_FLAGS: OnceLock<LiaDebugFlags> = OnceLock::new();

pub(crate) fn lia_debug_flags() -> &'static LiaDebugFlags {
    LIA_DEBUG_FLAGS.get_or_init(|| {
        use ay_core::DebugChannel;
        LiaDebugFlags {
            debug_lia: ay_core::debug_channel_active(DebugChannel::Lia),
            debug_lia_branch: ay_core::debug_channel_active(DebugChannel::LiaBranch),
            debug_lia_check: ay_core::debug_channel_active(DebugChannel::LiaCheck),
            debug_lia_nelson_oppen: ay_core::debug_channel_active(DebugChannel::LiaNelsonOppen),
            debug_patch: ay_core::debug_channel_active(DebugChannel::Patch),
            debug_gcd: ay_core::debug_channel_active(DebugChannel::Gcd),
            debug_gcd_tab: ay_core::debug_channel_active(DebugChannel::GcdTab),
            debug_dioph: ay_core::debug_channel_active(DebugChannel::Dioph),
            debug_hnf: ay_core::debug_channel_active(DebugChannel::Hnf),
            debug_mod: ay_core::debug_channel_active(DebugChannel::Mod),
            debug_enum: ay_core::debug_channel_active(DebugChannel::Enum),
        }
    })
}

/// Borrowed view into a substitution map: TermId → (coefficient pairs, constant).
pub(crate) type SubstitutionMap<'a> = HashMap<TermId, (&'a [(TermId, BigInt)], &'a BigInt)>;

/// A variable-elimination substitution triple: `(var, coefficients, constant)`.
///
/// Represents the expression `var = constant + Σ(coeff * dep_var)`.
/// Used by the Diophantine solver and RREF enumeration engine.
///
/// Generic over `K` (variable key: `TermId` or `usize`) and `V` (numeric
/// type: `BigInt` or `BigRational`).
pub(crate) type SubstitutionTriple<K, V> = (K, Vec<(K, V)>, V);

/// Timing breakdown for LIA solving phases (#4794, #8823).
///
/// Populated in-place by `LiaSolver` via `Instant::now()` measurements
/// around each phase. Before #8823 this struct was returned as a static
/// zero; any dispatcher reading these zeros before that fix was making
/// decisions from fake telemetry.
#[derive(Clone, Debug, Default)]
pub struct LiaTimings {
    /// Time spent in LRA simplex (`LraSolver::check` /
    /// `LraSolver::check_during_propagate`).
    pub simplex: std::time::Duration,
    /// Time spent generating and adding Gomory cuts.
    pub gomory: std::time::Duration,
    /// Time spent in HNF cut generation (`try_hnf_cuts`).
    pub hnf: std::time::Duration,
    /// Time spent in the Diophantine solver, including 2-variable solve,
    /// full Dioph solve, and bound/row tightening passes.
    pub dioph: std::time::Duration,
}

/// Non-negative remainder: `a mod m` with result in `[0, m)`.
///
/// Rust's `%` operator preserves the sign of the dividend, so `-3 % 5 == -3`.
/// This function returns the canonical non-negative representative instead:
/// `positive_mod(-3, 5) == 2`.
pub(crate) fn positive_mod(a: &BigInt, m: &BigInt) -> BigInt {
    debug_assert!(
        m > &BigInt::zero(),
        "BUG: positive_mod called with non-positive modulus {m} (a={a})",
    );
    let r = a % m;
    let result = if r < BigInt::zero() { r + m } else { r };
    debug_assert!(
        result >= BigInt::zero() && result < *m,
        "BUG: positive_mod({a}, {m}) produced out-of-range result {result}",
    );
    result
}

/// Compute the GCD of absolute values yielded by an iterator.
///
/// Returns `BigInt::zero()` for an empty iterator (the identity for GCD).
/// Short-circuits when GCD drops to 1 (it can never decrease further).
pub(crate) fn gcd_of_abs(values: impl Iterator<Item = BigInt>) -> BigInt {
    let mut result = BigInt::zero();
    for v in values {
        let abs_v = v.abs();
        if result.is_zero() {
            result = abs_v;
        } else {
            result = result.gcd(&abs_v);
        }
        if result.is_one() {
            break;
        }
    }
    debug_assert!(
        !result.is_negative(),
        "BUG: gcd_of_abs produced negative result {result}"
    );
    result
}

#[derive(Clone, Copy, Debug)]
pub(crate) enum IneqOp {
    Ge,
    Le,
    Gt,
    Lt,
}

/// Model extracted from LIA solver with variable assignments
#[derive(Debug, Clone)]
pub struct LiaModel {
    /// Variable assignments: term_id -> integer value
    pub values: HashMap<TermId, BigInt>,
}

/// Result from direct lattice enumeration.
///
/// Used to distinguish between UNSAT (with conflict), SAT (with witness model stored
/// in `direct_enum_witness`), and "no conclusion" (requires fallback to branch-and-bound).
#[derive(Debug)]
pub(crate) enum DirectEnumResult {
    /// Enumeration proved UNSAT within bounded search
    Unsat(Vec<TheoryLit>),
    /// Found a satisfying integer assignment (stored in `direct_enum_witness`)
    SatWitness,
    /// Could not reach conclusion (too many solutions, unbounded, etc.)
    NoConclusion,
}

/// The rational equality matrix built by `try_direct_enumeration`:
/// rows of `(coefficients, constant)` meaning `Σ coeff_i · x_i = constant`.
pub(crate) type EnumMatrix = Vec<(Vec<BigRational>, BigRational)>;

/// #probe-rref-memo: memoized outcome of the rational Gaussian elimination in
/// `try_direct_enumeration`, keyed by the exact pre-elimination matrix.
///
/// The elimination is a pure function of the matrix (fixed pivot order, no
/// reads of any other solver state except the cooperative-timeout poll), so a
/// FULL structural compare of the freshly built matrix against `key` makes a
/// hit exact by construction — no hash, no collision risk, no invalidation
/// obligations anywhere (push/pop/reset can keep the entry; a stale key
/// simply never matches again).
///
/// Motivation: `probe_needed_shared_equalities` runs one full LIA check per
/// candidate shared equality (~6 checks per conflict on QF_UFLIA wisas), and
/// each check re-ran this elimination from scratch even though the matrix is
/// built from `assertion_view().positive_equalities` alone — which the probe
/// NEVER mutates between steps (it only adds shared equalities, which do not
/// enter this matrix). Measured 50% of the whole probe-loop cost (78% of it
/// BigRational mul/div inside the elimination) on wisas xs_13_13.
pub(crate) struct EnumRrefCache {
    /// Pre-elimination matrix — the memo key, compared in full on lookup.
    pub(crate) key: EnumMatrix,
    /// Elimination outcome for `key`.
    pub(crate) outcome: EnumRrefOutcome,
}

/// Outcome of one Gaussian elimination run (see `EnumRrefCache`).
#[derive(Clone)]
pub(crate) enum EnumRrefOutcome {
    /// Completed reduced row echelon form plus its pivot columns.
    /// `Rc` so a hit detaches from the cache slot without cloning the rows.
    Rref(std::rc::Rc<(EnumMatrix, Vec<usize>)>),
    /// Deterministic mid-elimination abort: a coefficient exceeded
    /// `MAX_COEFF_BITS`. Same matrix ⇒ same abort, so this is cacheable;
    /// timeout aborts are NOT (they depend on the wall clock) and are never
    /// stored.
    CoeffExplosion,
}

/// A stored HNF cut using TermIds (stable across LRA resets)
#[derive(Clone)]
pub struct StoredCut {
    /// Coefficients: term_id -> coefficient
    pub(crate) coeffs: Vec<(TermId, BigRational)>,
    /// The bound value
    pub(crate) bound: BigRational,
    /// True if lower bound (>= bound), false if upper bound (<= bound)
    pub(crate) is_lower: bool,
    /// Reason atoms (equality TermIds) that derived this cut (#5388).
    /// Used for proper conflict explanation during replay.
    pub(crate) reasons: Vec<(TermId, bool)>,
}

/// Linear expression coefficients for Nelson-Oppen propagation.
/// Represents: Σ(coeff * var) + constant
pub(crate) struct LinearCoeffs {
    pub(crate) vars: HashMap<TermId, BigRational>,
    pub(crate) constant: BigRational,
}

/// Input stamp for the `detect_algebraic_equalities` memo.
///
/// The detection is a deterministic pure function of
/// `(assertion-view positive equalities, shared_equalities, LRA bounds over
/// integer_vars, propagated_equality_pairs)` apart from its appends to
/// `pending_equalities`/`propagated_equality_pairs` — and on a re-run with
/// identical inputs those appends are provably empty (every Case-2 pair is
/// already in `propagated_equality_pairs`; Case-1 tight bounds re-derive into
/// the returned vec, which is what gets cached). Each component below is a
/// revision counter bumped at every mutation site of the corresponding input,
/// NOT a `len()` (pop+push must not alias); `propagated_pairs_len` is the one
/// exception, sound because the set only grows within a scope and every
/// `pop()` bumps `bound_revision` (LIA pop always pops the inner LRA).
#[derive(PartialEq, Eq, Clone, Copy)]
pub(crate) struct AlgebraicDetectStamp {
    /// `AssertionViewCache::epoch()` — covers `positive_equalities`.
    pub(crate) view_epoch: u64,
    /// `LiaSolver::shared_eq_revision` — covers `shared_equalities`.
    pub(crate) shared_eq_revision: u64,
    /// `LraSolver::bound_revision()` — covers every `lra.get_bounds` read.
    pub(crate) bound_revision: u64,
    /// `LiaSolver::var_index_epoch` — covers `integer_vars` growth (e.g.
    /// `register_nelson_oppen_terms`), which widens the tight-bound scan
    /// without touching the view or the LRA bounds themselves.
    pub(crate) var_index_epoch: u64,
    /// Case-2 emission gate reads `propagated_equality_pairs` (see above).
    pub(crate) propagated_pairs_len: usize,
}

/// Detected algebraic equalities: `(term, forced value, reason literals)`.
pub(crate) type AlgebraicEqualities = Vec<(TermId, BigRational, Vec<TheoryLit>)>;

/// Saved cut-related state for push/pop scoping (#3685).
///
/// On `push()`, the current gomory/HNF iteration counters and seen-cut set
/// are snapshotted. On `pop()`, they are restored so that the outer scope
/// resumes with the exact cut state it had before the inner scope.
#[derive(Clone, Default)]
pub(crate) struct CutScopeState {
    pub(crate) gomory_iterations: usize,
    pub(crate) hnf_iterations: usize,
    /// #C7: Saved length of `seen_hnf_cuts_trail` at push time. On `pop()` the
    /// trail is truncated back to this mark, removing exactly the HNF-cut keys
    /// inserted in the popped scope from `seen_hnf_cuts`. Replaces an O(|set|)
    /// `seen_hnf_cuts.clone()` on every push with an O(1) length capture.
    pub(crate) seen_hnf_cuts_mark: usize,
    /// Saved length of `shared_equalities` at push time (#3581).
    pub(crate) shared_eq_mark: usize,
    /// Saved length of `shared_disequalities` at push time.
    pub(crate) shared_diseq_mark: usize,
}

/// LIA theory solver using Gomory cuts, HNF cuts, and branch-and-bound over LRA
pub struct LiaSolver<'a> {
    /// Reference to the term store for parsing expressions
    pub(crate) terms: &'a TermStore,
    /// Underlying LRA solver for the relaxation
    pub(crate) lra: LraSolver,
    /// Set of term IDs known to be integer variables
    pub(crate) integer_vars: HashSet<TermId>,
    /// `integer_vars` kept sorted by raw TermId (#C4).
    ///
    /// Maintained by binary insertion at every `integer_vars.insert` site so
    /// `check_integer_bounds_conflict` no longer collects + sorts the whole
    /// set on every BCP-time call. Invariant: same membership as
    /// `integer_vars` (vars are never removed except via `reset` /
    /// `clear_assertions`, which clear both).
    pub(crate) sorted_integer_vars: Vec<TermId>,
    /// Integer vars whose LRA bounds may have been tightened since the last
    /// conflict-free `check_integer_bounds_conflict` scan (#C4).
    ///
    /// CONSERVATISM (plan §3): LRA bound slots only ever *tighten* within a
    /// scope (`assert_var_bound*` is should-update-gated) and `pop()` only
    /// *widens* them back, so a new integer gap (`lower > upper`) can only
    /// appear on a var whose bounds were tightened since the last
    /// conflict-free scan. Every LIA-reachable tightening path marks this
    /// set (atom assertion via `collect_integer_vars`, dioph/modular/cut
    /// writes at their call sites); paths with imprecise touched-var sets
    /// set `int_bounds_all_dirty` instead.
    pub(crate) int_bounds_dirty: HashSet<TermId>,
    /// When true, the next `check_integer_bounds_conflict` scans ALL integer
    /// vars (#C4). Starts true; set by escape hatches (cuts, cube test,
    /// `lra_solver_mut`, resets); cleared together with `int_bounds_dirty`
    /// by a conflict-free scan.
    pub(crate) int_bounds_all_dirty: bool,
    /// Map from integer values to constant term IDs (#3581).
    /// Used by Nelson-Oppen propagation to create equalities between
    /// variables with derived tight bounds and constant terms. For example,
    /// when Gaussian elimination derives f(1) = 0, this map provides the
    /// TermId for constant 0 so that the equality f(1) = 0 can be propagated.
    pub(crate) int_constant_terms: HashMap<BigInt, TermId>,
    /// Asserted atoms for conflict generation
    pub(crate) asserted: Vec<(TermId, bool)>,
    /// #C3: Asserted literals whose atom is a Boolean constant asserted with the
    /// opposite polarity (e.g. the term layer folded `X = X` to `true` and the
    /// SAT solver assigned it `false`) — an assignment-independent immediate
    /// contradiction. Detected once at `assert_literal` time instead of via an
    /// O(asserted) scan on every `check`/`check_during_propagate`. Each entry is
    /// `(asserted_index, reason_literal)`; `pop()` drops entries at or above the
    /// truncation mark so the reported reason is always a live literal (#8784).
    pub(crate) const_bool_conflicts: Vec<(usize, TheoryLit)>,
    /// Search-phase hint (TheorySolver::set_search_phase): while true, the
    /// full Diophantine passes in check_inner are DEFERRED to the post-SAT
    /// final check (needs_final_check_after_sat == true guarantees one runs
    /// before any SAT is accepted).
    pub(crate) in_search_phase: bool,
    /// Consecutive UNPRODUCTIVE BCP-time Dioph runs (no conflict found).
    /// Once the streak passes the adaptive threshold, further BCP-time Dioph
    /// solves are deferred to the post-SAT final check for the remainder of
    /// the search (reset on pop, giving fresh contexts a fresh chance).
    pub(crate) dioph_bcp_unproductive_streak: u32,
    /// Scope markers for push/pop
    pub(crate) scopes: Vec<usize>,
    /// Scope markers for learned cut truncation on pop.
    pub(crate) cut_scopes: Vec<usize>,
    /// Saved cut state per scope level for proper restore on pop (#3685).
    pub(crate) cut_state_scopes: Vec<CutScopeState>,
    /// Number of Gomory cut iterations attempted
    pub(crate) gomory_iterations: usize,
    /// Maximum Gomory cut iterations before falling back to split
    pub(crate) max_gomory_iterations: usize,
    /// Number of HNF cut iterations attempted
    pub(crate) hnf_iterations: usize,
    /// Maximum HNF cut iterations
    pub(crate) max_hnf_iterations: usize,
    /// Skip memo for HNF cut generation (#hnf-dimension-gate): the
    /// assertion-view epoch + matrix dims of an attempt that produced ZERO
    /// cuts. Rebuilding the same matrix (Bareiss determinant overflow on
    /// large u64-range guards) is pure waste — observed 41 identical
    /// 824x1259 rebuilds at ~0.7s each = a 30s test timeout. Sound to skip:
    /// HNF cuts are an optimization; Gomory cuts and branch-and-bound
    /// still run.
    pub(crate) hnf_barren_fingerprint: Option<(u64, usize, usize)>,
    /// Deduplicate HNF cuts across the solve (cuts are globally valid).
    pub(crate) seen_hnf_cuts: HashSet<HnfCutKey>,
    /// #C7: Insertion trail backing the per-scope undo of `seen_hnf_cuts`.
    /// Records, in order, every key newly inserted into `seen_hnf_cuts` while at
    /// least one scope is open. `push()` saves `seen_hnf_cuts_trail.len()` as the
    /// scope mark and `pop()` truncates back to it (removing those keys from the
    /// set), exactly restoring the pre-push set without cloning it per push.
    /// Inserts made at scope depth 0 are permanent and are NOT trailed, so the
    /// trail is empty whenever no scope is open (e.g. at snapshot boundaries).
    pub(crate) seen_hnf_cuts_trail: Vec<HnfCutKey>,
    /// Stored cuts using TermIds for replay after LRA reset.
    /// These are derived from equality constraints and should be valid
    /// across different SAT models with the same base constraints.
    pub(crate) learned_cuts: Vec<StoredCut>,
    /// Cached set of asserted equality atoms (used to avoid re-running Diophantine
    /// solving when only inequalities change due to branching).
    /// Diophantine solving is skipped if this matches the current equality atoms.
    pub(crate) dioph_equality_key: Vec<TermId>,
    /// Set when a BCP-time scratch Dioph run used the current equality key but
    /// intentionally discarded the resulting caches so the next full `check()`
    /// still reruns Dioph with persistent state.
    pub(crate) dioph_needs_full_check: bool,
    /// #C8: Set by `pop()` (and `soft_reset`) when the assertion trail shrank.
    /// The equality-derived Dioph caches (`dioph_cached_substitutions`,
    /// `dioph_cached_modular_gcds`, `dioph_cached_reasons`,
    /// `dioph_safe_dependent_vars`) are PRESERVED across a backtrack because
    /// they depend only on the asserted equality SET — not on the inequality
    /// bounds that branch-and-bound and BMC backtracking churn. This flag makes
    /// the next `check()`/`check_during_propagate()` re-validate
    /// `dioph_equality_key` against the (now truncated) assertion view before
    /// reusing them: an unchanged key reuses the caches (the win); a changed
    /// key drops them before `propagate_bounds_through_substitutions` or any
    /// modular check can observe substitutions from a popped scope (#3736).
    pub(crate) dioph_needs_revalidation: bool,
    /// Integer variables that are provably dependent on other integer variables
    /// via unit-coefficient equalities (safe substitutions).
    ///
    /// These are typically poor branching candidates because their integrality
    /// is implied by other variables.
    pub(crate) dioph_safe_dependent_vars: HashSet<TermId>,
    /// Cached substitutions from Diophantine solver for bound propagation.
    /// Format: (substituted_term, [(dep_term, coeff)...], constant)
    /// Meaning: substituted_term = constant + Σ(coeff * dep_term)
    pub(crate) dioph_cached_substitutions: Vec<SubstitutionTriple<TermId, BigInt>>,
    /// Modular constraints from Dioph substitutions including free parameters.
    /// Format: (term_id, gcd, residue) meaning `term ≡ residue (mod gcd)`.
    /// Populated by expanding substitutions WITH free fresh parameters,
    /// preserving GCD information that the filtered substitutions lose.
    pub(crate) dioph_cached_modular_gcds: Vec<(TermId, BigInt, BigInt)>,
    /// Equality literals that justify cached substitutions.
    /// These are reused as reasons for propagated bounds.
    pub(crate) dioph_cached_reasons: Vec<(TermId, bool)>,
    /// Set when Diophantine solving has added bounds to LRA. LRA Farkas
    /// conflicts may depend on these bounds and need augmentation (#8147).
    pub(crate) dioph_modified_bounds: bool,
    /// Term IDs whose bounds were set by Diophantine solving.
    /// Used for targeted augmentation: only conflicts involving these
    /// variables need dioph reasons appended (#8147 regression fix).
    pub(crate) dioph_bound_term_ids: HashSet<TermId>,
    /// Discovered equalities for Nelson-Oppen propagation.
    /// These are collected during check() when we detect tight bounds.
    pub(crate) pending_equalities: Vec<DiscoveredEquality>,
    /// Track which equality pairs have been propagated to avoid duplicates.
    /// Stores (min(lhs, rhs), max(lhs, rhs)) for canonical ordering.
    pub(crate) propagated_equality_pairs: HashSet<(TermId, TermId)>,
    /// #8469: Track which disequality pairs have been propagated to avoid duplicates.
    /// Stores (min(lhs, rhs), max(lhs, rhs)) for canonical ordering.
    pub(crate) propagated_disequality_pairs: HashSet<(TermId, TermId)>,
    /// Shared equalities received via `assert_shared_equality` (#3581).
    /// These are (lhs, rhs, reason_lits) tuples from EUF that need to be
    /// processed by `detect_algebraic_equalities` alongside assertion-view
    /// equalities. Without this, variables introduced only via shared
    /// equalities (e.g., UF terms f(0), f(1)) have no tight bounds and
    /// are invisible to the algebraic equality detection phase.
    pub(crate) shared_equalities: Vec<(TermId, TermId, Vec<TheoryLit>)>,
    /// INTERFACE-DIET (`AY_INTERFACE_DIET`): sticky-conservative flag set by the
    /// combiner (`mark_interface_hidden`) whenever it WITHHOLDS a pure-UF=UF Int
    /// equality from `assert_shared_equality`. When set, `shared_equalities`
    /// under-represents the true EUF interface, so every "shared_equalities is
    /// empty ⇒ unlock a Sat-producing finite-domain / enumeration shortcut" site
    /// must fail-closed (see the C4/R2 polarity table). Cleared only on `reset`.
    pub(crate) hidden_interface: bool,
    /// #shared-eq-idempotent: membership index over `shared_equalities`, keyed
    /// by the equality as an UNORDERED pair, so `assert_shared_equality` is
    /// idempotent.
    ///
    /// The Nelson-Oppen fixpoint re-asserts the SAME shared equalities on every
    /// round of every check of every split round. Asserting `a = b` twice is
    /// logically identical to asserting it once, but the unconditional
    /// `shared_equalities.push` made the trail grow once per round, and every
    /// consumer of it (`detect_algebraic_equalities`, `affine_implication`,
    /// `check`, `enumeration`) is at least linear in its length — with
    /// `affine_implication` quadratic. The trail therefore grew without bound
    /// on a fixpoint that had already converged, so the round cost rose even
    /// though no new information was being derived. That is the non-convergence
    /// behind the AUFLIA `ext_eq` hang (#7956): the solver was not searching,
    /// it was re-deriving.
    ///
    /// Maintained in exact lockstep with the trail: `pop()` removes precisely
    /// the keys whose entries it truncates (same discipline as
    /// `seen_hnf_cuts` / `seen_hnf_cuts_trail`, #C7). Because insertion is
    /// deduped, each key occurs at most once on the trail, so the undo is exact.
    pub(crate) shared_eq_seen: HashSet<(TermId, TermId)>,
    /// #shared-eq-core: true on a throwaway solver used by
    /// `probe_needed_shared_equalities` to PROVE which shared equalities a
    /// conflict actually needs. A probe never augments and never probes again.
    pub(crate) conflict_probe: bool,
    /// #probe-subset-cache: opt-in for the cached-subset-first farkas probe
    /// (see `probe_needed_shared_equalities`). Default OFF — the batch guess
    /// changes learned-clause content (a proven superset appends more
    /// reasons), which measurably re-routes SAT trajectories in both
    /// directions (QF_UFLIA wisas: converts `xs_26_26`, derails `xs_22_32`).
    /// The UFLIA hybrid enables it for its bounded lazy DETOUR rounds only,
    /// so the eager arm stays byte-identical to the pre-cache pipeline.
    pub(crate) probe_subset_cache: bool,
    /// #uflia-verify-only: true on isolated VERIFICATION solvers (the
    /// fail-closed semantic conflict/propagation re-check combiners built by
    /// `make_verification_combiner`). Those callers pattern-match ONLY the
    /// `TheoryResult` variant (`Unsat`/`UnsatWithFarkas` vs `Sat`) and discard
    /// the conflict payload, so the post-verdict
    /// `augment_farkas_with_shared_reasons` pass — whose
    /// `probe_needed_shared_equalities` loop re-runs a FULL LIA check per
    /// candidate shared equality — is pure waste there (measured ~50% of
    /// QF_UFLIA wisas runtime inside the verifier, most of it in the probe).
    /// Augmentation runs strictly AFTER the verdict is derived and never
    /// changes the result variant, so skipping it in verify-only mode returns
    /// byte-identical verdicts. Never set on production solvers: their
    /// conflict literals feed learned clauses and MUST stay augmented (#8147).
    pub(crate) verify_only: bool,
    /// Monotone revision counter for `shared_equalities`: bumped on every
    /// push, pop-time truncation, and clear. A revision, not a `len()`, so a
    /// pop+push sequence restoring the same length cannot alias a memo stamp.
    pub(crate) shared_eq_revision: u64,
    /// Memo for `detect_algebraic_equalities`: the conflict-free result for
    /// the stamped inputs. The combined-solver Nelson-Oppen fixpoint calls
    /// the detection on EVERY iteration of every check of every split round;
    /// with unchanged inputs the full Gaussian re-elimination (BigRational
    /// mul/div over 2-limb constants at u64 scale) is a deterministic replay,
    /// so an equal stamp returns the cached vec in O(1). NEVER holds a
    /// conflict run: a conflicting state must re-derive on every call so the
    /// #8783/#8784 stale-drop-then-recheck flow stays byte-identical.
    pub(crate) detect_algebraic_cache: Option<(AlgebraicDetectStamp, AlgebraicEqualities)>,
    /// Observability: total `detect_algebraic_equalities` entries.
    pub(crate) detect_algebraic_calls: u64,
    /// Observability: entries answered from `detect_algebraic_cache`.
    pub(crate) detect_algebraic_cache_hits: u64,
    /// #probe-rref-memo: incremental reason-free conflict-predictor state,
    /// maintained across a conflict PROBE's one-at-a-time shared-equality adds
    /// (`probe_needed_shared_equalities`). Only ever populated on a
    /// `conflict_probe` solver. See [`crate::nelson_oppen::ProbeAlgIncr`] and
    /// `detect_algebraic_probe`.
    pub(crate) probe_alg_incr: Option<crate::nelson_oppen::ProbeAlgIncr>,
    /// Shared disequalities received via `assert_shared_disequality`.
    ///
    /// LRA owns the branch/split machinery for these, but LIA-level affine
    /// implication can often prove a contradiction before a split is needed.
    pub(crate) shared_disequalities: Vec<(TermId, TermId, Vec<TheoryLit>)>,
    /// Pending conflict from `assert_shared_equality` when a constant-expression
    /// equality is provably impossible (#8124). For example, when EUF propagates
    /// `x = 5` but LIA bounds force `x = 3`, the shared equality reduces to
    /// `5 - 3 = 0` which is impossible. The conflict reasons are the TheoryLits
    /// that justify the shared equality. Reported via `propagate_equalities()`
    /// and checked early in `check()`/`check_during_propagate()`.
    pub(crate) pending_shared_eq_conflict: Option<Vec<TheoryLit>>,
    /// When true, `detect_algebraic_equalities` skips shared equalities (#6282).
    /// Set in AUFLIA mode where array store axioms create dense shared equality
    /// systems that overwhelm Gaussian elimination with O(n²) derived equalities.
    pub(crate) skip_shared_algebraic: bool,
    /// Optional timeout callback for cooperative interruption.
    /// When the callback returns true, the solver will return Unknown at the next check point.
    pub(crate) timeout_callback: Option<Box<dyn Fn() -> bool>>,
    /// Optional hard wall-clock deadline (#8749). Propagated to the IntSat
    /// probe so its BigInt conflict loop honours `--timeout` instead of
    /// overshooting it by seconds while exhausting its conflict budget.
    pub(crate) deadline: Option<ay_core::time::Instant>,
    /// When direct enumeration finds a satisfying integer assignment, store it here so
    /// `check()` can return SAT without branch-and-bound and `extract_model()` can succeed.
    pub(crate) direct_enum_witness: Option<LiaModel>,
    /// #probe-rref-memo: last Gaussian elimination of `try_direct_enumeration`
    /// (see `EnumRrefCache`). Content-keyed — never needs invalidation.
    pub(crate) enum_rref_cache: Option<EnumRrefCache>,
    // Cached env vars (#2673)
    pub(crate) debug_lia: bool,
    pub(crate) debug_lia_branch: bool,
    pub(crate) debug_lia_check: bool,
    pub(crate) debug_lia_nelson_oppen: bool,
    pub(crate) debug_patch: bool,
    pub(crate) debug_gcd: bool,
    pub(crate) debug_gcd_tab: bool,
    pub(crate) debug_dioph: bool,
    pub(crate) debug_hnf: bool,
    pub(crate) debug_mod: bool,
    pub(crate) debug_enum: bool,
    /// Always-valid incremental assertion classification (#4742, #C1).
    /// Updated in `assert_literal`, truncated via scope marks in `push`/`pop`,
    /// rebuilt defensively on the shared-equality paths.
    pub(crate) assertion_view_cache: assertion_view::AssertionViewCache,
    /// Atom-indexed linear parse cache (#C2): `(lhs, rhs) → exact linear
    /// form + assignment-independent GCD/modular facts`. Sound because
    /// `TermStore` is append-only; survives `reset`/`clear_assertions`.
    pub(crate) linear_cache: LinearCacheMap,
    /// `term → affine BigRational form` cache for `term_to_linear_coeffs`
    /// (shared-equality / Nelson-Oppen paths, #C2).
    pub(crate) affine_cache: AffineCacheMap,
    /// Dioph row parse cache keyed by `(lhs, rhs)`, valid while
    /// `var_index_epoch` matches the stored epoch (#C2).
    pub(crate) dioph_parse_cache: DiophParseCacheMap,
    /// Bumped whenever `integer_vars` changes (insert or clear), i.e.
    /// whenever the `build_var_index` bijection may change. Guards
    /// `dioph_parse_cache` entries, which store variable *indices*.
    pub(crate) var_index_epoch: u64,
    // Per-theory runtime statistics (#4706)
    pub(crate) check_count: u64,
    pub(crate) conflict_count: u64,
    pub(crate) propagation_count: u64,
    /// Minimal-core affine conflict narrowing attempts (#23 Stage 2).
    pub(crate) affine_min_core_attempts: u64,
    /// Minimal-core affine conflict narrowing successes (#23 Stage 2): a
    /// re-verified core was used in place of the fat all-equations conflict.
    pub(crate) affine_min_core_successes: u64,
    /// Persistent buffer for reachable vars in augment_farkas (#8599).
    pub(crate) reachable_vars_buf: HashSet<TermId>,
    /// Persistent buffer for conflict vars in augment_farkas (#8599).
    pub(crate) conflict_vars_buf: HashSet<TermId>,
    /// Accumulated per-phase timings (#8823). Populated by `Instant::now()`
    /// measurements in `check_inner` / `check_during_propagate_inner` around
    /// the simplex, Gomory, HNF, and Diophantine phases.
    pub(crate) timings: LiaTimings,
}

/// Key for deduplicating HNF cuts (uses TermIds for stability across theory instances)
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct HnfCutKey {
    /// Coefficients
    pub(crate) coeffs: Vec<(TermId, BigInt)>,
    /// Bound
    pub(crate) bound: BigInt,
}

/// Diophantine solver state for external storage.
///
/// Stores the results of Diophantine analysis so they can be preserved across
/// solver recreations during branch-and-bound. Since equalities don't change
/// during branching, the analysis can be reused.
#[derive(Default)]
pub struct DiophState {
    /// List of asserted equality atoms (used to detect when re-analysis is needed)
    pub equality_key: Vec<TermId>,
    /// Whether the next full `check()` must rerun Dioph even if `equality_key`
    /// matches because BCP only performed a scratch analysis.
    pub needs_full_check: bool,
    /// Variables that are poor branching candidates (dependent on others via
    /// unit-coefficient equalities)
    pub safe_dependent_vars: HashSet<TermId>,
    /// Variable elimination expressions for bound propagation.
    /// Format: (substituted_term, [(dep_term, coeff)...], constant)
    pub cached_substitutions: Vec<SubstitutionTriple<TermId, BigInt>>,
    /// Modular constraints from fully-expanded substitutions (including free params).
    /// Format: (term_id, gcd, residue) meaning `term ≡ residue (mod gcd)`.
    pub cached_modular_gcds: Vec<(TermId, BigInt, BigInt)>,
    /// Equality literals justifying the substitutions (for conflict analysis)
    pub cached_reasons: Vec<(TermId, bool)>,
    /// LIA-level equality pairs already proposed to Nelson-Oppen/DPLL(T).
    pub propagated_equality_pairs: HashSet<(TermId, TermId)>,
    /// LIA-level disequality pairs already proposed to Nelson-Oppen/DPLL(T).
    pub propagated_disequality_pairs: HashSet<(TermId, TermId)>,
    /// Embedded LRA equality pairs already proposed by `assume_eqs`.
    pub lra_propagated_equality_pairs: HashSet<(TermId, TermId)>,
    /// Embedded LRA disequality pairs already proposed by `assume_eqs`.
    pub lra_propagated_disequality_pairs: HashSet<(TermId, TermId)>,
}
