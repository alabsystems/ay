#![forbid(unsafe_code)]

//! AY NIA - Non-linear Integer Arithmetic theory solver
//!
//! Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//!
//! Implements model-based incremental linearization for non-linear arithmetic,
//! following the DPLL(T) approach where the SAT solver handles branching.
//!
//! ## Algorithm Overview
//!
//! The solver uses a combination of techniques:
//!
//! 1. **Monomial tracking**: Map nonlinear terms like `x*y` to auxiliary variables
//! 2. **Sign lemmas**: Infer sign of product from signs of factors
//! 3. **McCormick envelopes**: Globally valid convex relaxations for bounded monomials
//! 4. **Tangent hyperplane lemmas**: Linear approximations at the current model point
//! 5. **Model patching**: Fix model values before generating lemmas (Z3 nla_core.cpp)
//! 6. **Even-power non-negativity**: x^2k >= 0 algebraic identity
//! 7. **Delegate to LIA**: Linear constraints are handled by the LIA solver
//!
//! ## Key Insight
//!
//! QF_NIA is undecidable (Hilbert's 10th Problem), but model-based refinement
//! works well on practical problems. The solver iteratively refines bounds using
//! lemmas derived from the current model, converging to a solution or UNSAT.
//!
//! ## Reference
//!
//! Based on Z3's NLA solver (`reference/z3/src/math/lp/nla_*.cpp`).

#![warn(missing_docs)]
#![warn(clippy::all)]
#![allow(clippy::type_complexity)]

// Import safe_eprintln! from ay-core (non-panicking eprintln replacement)
#[macro_use]
extern crate ay_core;

mod bounded_enum;
mod check_loop;
mod factor_split;
mod factor_split_provenance;
pub(crate) mod feasible_set;
mod full_conflict;
mod interval_contract;
mod local_search;
mod local_search_order;
mod model_state;
mod monomial;
mod nlsat;
mod patch;
mod sign_check;
mod sign_lemmas;
pub(crate) mod sos;
mod sos_check;
mod tangent_add;
mod tangent_lemmas;
mod theory_impl;
mod univariate_int;
mod zero_bound_lemmas;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::{Sort, TheoryLit, TheoryPropagation, TheoryResult, TheorySolver};
use ay_lia::LiaSolver;
use ay_lra::GomoryCut;
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::One;

/// A purified division: `(/ num denom)` -> fresh LRA variable `div_term`,
/// with side constraint `denom * div_term = num`.
/// Ported from NRA (#8453).
#[derive(Debug, Clone, Copy)]
struct DivPurification {
    /// The original `(/ num denom)` term (has an LRA variable via `intern_var`)
    div_term: TermId,
    /// The numerator term
    numerator: TermId,
    /// The denominator term
    denominator: TermId,
}

/// Red zone: if remaining stack is below this threshold, grow before entering
/// the NIA check loop. The NIA check loop (via LIA/LRA simplex + monomial
/// refinement) needs significant stack in debug. A 4 MiB red zone triggers
/// growth when a default 8 MiB test thread has less than 4 MiB remaining.
const NIA_STACK_RED_ZONE: usize = 4 * 1024 * 1024;

/// Size of the new stack segment allocated when the red zone is reached.
/// 16 MiB to provide ample room for NIA check iterations in debug mode.
const NIA_STACK_SIZE: usize = 16 * 1024 * 1024;

/// Guard the NIA entrypoint against stack overflow on small thread stacks.
fn maybe_grow_nia_stack<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(NIA_STACK_RED_ZONE, NIA_STACK_SIZE, f)
}

pub use local_search_order::is_integer_unit_conjunction;
pub use monomial::Monomial;

/// Per-phase timing breakdown for NIA-specific work (#8823).
///
/// Before #8823, `NiaSolver` exposed only `lia_timings()`, which delegated
/// to a LIA stub that always returned zero. That meant any dispatcher
/// consulting NIA timings saw fake telemetry. NIA now tracks its own
/// wall-clock cost separately from the embedded LIA solver — callers who
/// want LIA timings go through `lia_timings()`, callers who want NIA's
/// own overhead go through `timings()`.
#[derive(Clone, Debug, Default)]
pub struct NiaTimings {
    /// Time spent inside `nia_check_loop` (total, including embedded LIA
    /// calls). Callers that want NIA-only overhead should compute
    /// `check_loop - lia_timings().total()`.
    pub check_loop: std::time::Duration,
    /// Time spent in sign consistency and monomial consistency checks.
    pub sign_check: std::time::Duration,
    /// Time spent in tentative model patching (`try_tentative_patch`
    /// + `try_integer_rounding`).
    pub patching: std::time::Duration,
    /// Time spent generating tangent / McCormick / division refinement
    /// lemmas.
    pub tangent: std::time::Duration,
    /// Time spent in bounded enumeration fallbacks.
    pub enumeration: std::time::Duration,
}

impl NiaTimings {
    /// Sum across all NIA-specific phases (excluding the embedded LIA time
    /// already billed via `LiaTimings`).
    #[must_use]
    pub fn nia_only(&self) -> std::time::Duration {
        self.sign_check + self.patching + self.tangent + self.enumeration
    }
}

/// Sum across all LIA phases (simplex + gomory + hnf + dioph).
///
/// Dispatchers often want a single "how expensive was LIA" number.
/// Provided as a free function so we do not need to add a method to the
/// struct in the LIA crate.
#[must_use]
pub fn lia_timings_total(t: &ay_lia::LiaTimings) -> std::time::Duration {
    t.simplex + t.gomory + t.hnf + t.dioph
}

/// Trail entry for sign constraint push/pop (#8626).
/// Records which map received an addition so it can be undone on pop.
#[derive(Debug, Clone)]
enum SignConstraintTrailEntry {
    /// A constraint was pushed onto `sign_constraints[key]`.
    Monomial(Vec<TermId>),
    /// A constraint was pushed onto `var_sign_constraints[var]`.
    Variable(TermId),
}

/// Model extracted from NIA solver with variable assignments
#[derive(Debug, Clone)]
pub struct NiaModel {
    /// Variable assignments: term_id -> integer value
    pub values: HashMap<TermId, BigInt>,
}

use ay_core::nonlinear::SignConstraint;

/// NIA theory solver using model-based incremental linearization
pub struct NiaSolver<'a> {
    /// Reference to the term store for parsing expressions
    terms: &'a TermStore,
    /// Underlying LIA solver for linear constraints
    lia: LiaSolver<'a>,
    /// Tracked monomials: sorted var list -> Monomial info
    monomials: HashMap<Vec<TermId>, Monomial>,
    /// Auxiliary variable to monomial mapping (reverse index)
    aux_to_monomial: HashMap<TermId, Vec<TermId>>,
    /// Sign constraints on monomials: monomial key -> (constraint, assertion term)
    sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>>,
    /// Sign constraints on variables: var -> (constraint, assertion term)
    var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>>,
    /// Trail of sign constraint additions for efficient push/pop (#8626).
    /// Each entry records which map (monomial or variable) received an
    /// addition, and the key. On pop(), the last element is popped from
    /// the corresponding inner Vec; if it becomes empty, the key is removed.
    /// This replaces full HashMap clones with O(k) undo where k = additions
    /// in the popped scope.
    sign_constraint_trail: Vec<SignConstraintTrailEntry>,
    /// Scope markers for sign constraint trail: saved trail length at push().
    sign_constraint_trail_marks: Vec<usize>,
    /// Trail for monomial push/pop scoping (#3735).
    /// Each entry records (vars_key, aux_var) pairs inserted during that scope level.
    /// On pop, these entries are removed from `monomials` and `aux_to_monomial`.
    monomial_trail: Vec<Vec<(Vec<TermId>, TermId)>>,
    /// Division purifications: `(/ num denom)` -> side constraint `denom * div = num`.
    /// Tracked separately from monomials because the numerator may be a constant
    /// with no LRA variable. Ported from NRA (#8453, #6811).
    div_purifications: Vec<DivPurification>,
    /// Asserted atoms for conflict generation
    asserted: Vec<(TermId, bool)>,

    /// Incremental SOS fragment translation cache (see
    /// `sos_check::SosFragmentCache`): `build_sos_fragment_with_progress`
    /// runs on every NIA check and previously retranslated the whole
    /// asserted set -- the top profile stack on Certora QF_UFDTNIA
    /// 39657...48. Interior-mutable because fragment building is `&self`.
    pub(crate) sos_fragment_cache: std::cell::RefCell<sos_check::SosFragmentCache>,
    /// Scope markers for push/pop: (asserted_len, div_purifications_len)
    scopes: Vec<(usize, usize)>,
    /// Debug flag
    debug: bool,
    // Per-theory runtime statistics (#4706)
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
    /// Number of tangent plane lemmas added
    tangent_lemma_count: u64,
    /// Number of successful model patches
    patch_count: u64,
    /// Number of tentative sign cuts injected
    sign_cut_count: u64,
    /// Number of iteration >= 1 LIA refutations published while model guesses
    /// were in the tentative scope (#nia-sign-cut-soundness telemetry,
    /// `nia_unsat_with_guesses`). Sound by the justified-bound discipline in
    /// the LIA/LRA; the count lets a census see how often that discipline
    /// carried a verdict.
    unsat_with_guesses_count: u64,
    /// Number of tentative LIA scopes active (sign-cut + patch scopes).
    /// The sign-cut path and try_tentative_patch each push one scope.
    /// undo_tentative_patch() must pop ALL of them to avoid leaking
    /// model-dependent bounds into future queries.
    tentative_depth: u32,
    /// Number of MODEL GUESSES asserted into the open tentative scope(s)
    /// (#nia-sign-cut-soundness): tentative sign cuts (`x >= 0` / `x <= 0`
    /// from the current model value) and integer-rounding / patch pins
    /// (`x = round(model(x))`). Every producer goes through
    /// `inject_tentative_sign_cuts` or `apply_patch`, the two chokepoints
    /// that bump this. A guess is a heuristic that steers the LP toward a
    /// model the monomial check can verify; it is NOT a theorem. Nothing
    /// downstream can build a verdict on one — its reason is the variable
    /// term, which the LRA's Farkas guard and the LIA's justified-bound reads
    /// see as unasserted — and debug builds audit that by re-deriving any
    /// LIA UNSAT observed while this is non-zero in a guess-free scope (z3
    /// `nla_basics_lemmas::sign_lemma` discipline: a model-guessed sign is a
    /// decision, never a fact). Reset to zero by `undo_tentative_patch`.
    tentative_guess_count: u32,

    // --- clauseSMT NLSAT techniques (#8453, ported from NRA #8445) ---
    /// Per-variable feasible sets: intersection of clause-level feasible sets.
    /// Updated during check() when a clause becomes univariate.
    /// Maps term_id of variables involved in nonlinear constraints to their
    /// current feasible sets.
    pub(crate) feasible_sets: HashMap<TermId, feasible_set::FeasibleSet>,

    /// Variables whose feasible set has become empty (blocked).
    /// These are prioritized for branching (highest priority).
    pub(crate) blocked_vars: Vec<TermId>,

    /// Variables whose feasible set has become a single point (fixed).
    /// Second-highest priority for branching.
    pub(crate) fixed_vars: Vec<(TermId, BigRational)>,

    /// Count of feasible-set computations for statistics.
    feasible_set_count: u64,

    /// All registered (internalized) theory atoms. Used by suggest_decision_atom
    /// to find unassigned atoms involving blocked/fixed variables. Unlike
    /// `asserted` (which only has atoms with truth values), this includes atoms
    /// that may not yet be decided by the SAT solver.
    pub(crate) registered_atoms: Vec<TermId>,

    /// Set of currently asserted atoms (for fast lookup in suggest_decision_atom).
    /// Tracks which atoms from `registered_atoms` already have truth values.
    pub(crate) asserted_atom_set: HashSet<TermId>,

    /// Every theory atom the DPLL layer has registered (`register_atom`), i.e.
    /// the instance's SAT-visible arithmetic vocabulary. Sizes the phase-hint
    /// epoch gate (#nonlinear-phase-hints); nothing else reads it. Cleared by
    /// `reset`, which the eager lanes call before re-registering.
    pub(crate) sat_atoms: HashSet<TermId>,

    /// Memo of `suggest_phase` results keyed by the wrapped LRA's
    /// `phase_state_epoch` (the same generation `phase_hint_epoch`
    /// reports when size-gated in). The SAT seeder re-queries every
    /// atom after every BCP quiescence; below the epoch-skip size
    /// gate that re-seed is deliberately unconditional for
    /// trajectory reasons, so the per-atom feasible-set sign walk
    /// repeated identically thousands of times per solve (~17% of
    /// the wall on Certora QF_UFDTNIA 39657...48). Suggestions are a
    /// pure function of the term store and the state that epoch
    /// covers (the contract `phase_hint_epoch` already asserts and
    /// the DPLL debug canary checks), so serving them from this memo
    /// is value- AND trajectory-exact: the seeder still overwrites
    /// phase arrays every quiescence, just without recomputing.
    pub(crate) phase_memo: std::cell::RefCell<(Option<u64>, HashMap<TermId, Option<bool>>)>,

    /// Per-epoch memo of leaf value signs for the feasible-set look-ahead
    /// (`term_value_sign` / `term_has_value` in nlsat.rs), keyed by the
    /// same `phase_state_epoch` as `phase_memo`. The seeder's per-atom
    /// sign walk re-reads the signs of shared operand leaves for every
    /// atom at every quiescence; the per-atom memo cannot reuse those
    /// across atoms, so leaf reads (column lookup + materialised sign)
    /// dominated the walk on Certora QF_UFDTNIA. A leaf's sign is a pure
    /// function of the state the epoch covers, so this is value- and
    /// trajectory-exact exactly as `phase_memo` is.
    pub(crate) leaf_sign_memo:
        std::cell::RefCell<(Option<u64>, HashMap<TermId, Option<std::cmp::Ordering>>)>,

    /// Real per-phase timings for NIA-specific work (#8823). Populated by
    /// `Instant::now()` measurements in `nia_check_loop`. Separate from
    /// `self.lia.timings()` so a dispatcher can see NIA overhead distinct
    /// from the embedded LIA cost.
    pub(crate) timings: NiaTimings,
    /// Exact integer witness found by bounded enumeration.
    ///
    /// The LIA relaxation can remain `Unknown` for small bounded nonlinear
    /// problems even when exhaustive integer enumeration finds a satisfying
    /// point. Keep that witness available for executor model validation.
    bounded_enum_model: Option<HashMap<TermId, BigInt>>,
    bounded_enum_bool_model: HashMap<TermId, bool>,

    /// Interval-contracted integer bounds from the most recent
    /// `try_bounded_enumeration` in the CURRENT asserted scope
    /// (#nia-mccormick-contracted-bounds). The contractor derives bounds
    /// that flow through nonlinear atoms and compound linear equalities
    /// (e.g. `main - 3 = 0 ∧ c + main <= 0` gives `c <= -3`) which the
    /// LRA's stored variable bounds may only carry in weaker sentinel
    /// form (`c <= 0`, reason = the variable term). McCormick envelopes
    /// consult this stash and keep the tighter side; a contracted
    /// endpoint is justified by the asserted literals as a whole (the
    /// contractor's soundness contract: seeds are justified bounds and
    /// every rule only removes values excluded by asserted atoms).
    /// Cleared whenever the asserted set changes (assert/pop/reset and
    /// at `check()` entry), so a stale endpoint can never outlive its
    /// justifying trail.
    contracted_bounds: HashMap<TermId, (Option<i64>, Option<i64>)>,

    /// Narrow premise literals for product-sum-derived contracted
    /// endpoints, keyed by `(var, is_lower)` (#nia-product-sum-bound).
    /// Factor split cites these for a contracted-completed box instead
    /// of every asserted literal, keeping learned conflicts small.
    /// Cleared together with `contracted_bounds`.
    contracted_bound_reasons: HashMap<(TermId, bool), Vec<(TermId, bool)>>,

    /// Monomial-congruence aux-var pairs already linked via
    /// `add_monomial_congruence_lemmas` (#nia-congruence). NIA's `check()` can
    /// fire multiple times within one scope; this set makes the congruence
    /// lemma idempotent so the inner LIA's `shared_equalities` does not
    /// accumulate duplicate entries. Pairs are stored canonically (smaller
    /// `TermId` first). Cleared on `pop`/`reset` (re-deriving after a scope
    /// change is sound — the equality is universally valid given its reasons).
    congruence_linked: HashSet<(TermId, TermId)>,

    /// Zero-lower-bound product lemmas already emitted in this scope
    /// (#nia-zero-bound, see `zero_bound_lemmas.rs`). Keys are
    /// `(aux, aux, is_lower)` for product-sign cuts and `(m_lo, m_hi,
    /// is_lower)` for monotonicity cuts (the two families cannot collide:
    /// monotonicity requires `m_lo != m_hi`). Cleared on `pop`/`reset`;
    /// re-deriving after a scope change is sound because each lemma is
    /// re-justified from the then-current asserted literals.
    zero_bound_emitted: HashSet<(TermId, TermId, bool)>,

    /// Non-negative-box product upper cuts already emitted in this scope
    /// (#nia-zero-bound family 4, see
    /// `zero_bound_lemmas.rs::add_box_product_upper_lemmas`). Keyed by
    /// `(aux, bound)` — the bound value is part of the key so a TIGHTER box
    /// discovered later in the same scope still emits its (different) cut.
    /// Cleared on `pop`/`reset` with the same re-derivation discipline as
    /// `zero_bound_emitted`.
    box_bound_emitted: HashSet<(TermId, BigRational)>,

    /// Zero-product / quotient / interval-product cuts already emitted in
    /// this scope (#nia-zero-product, see
    /// `zero_bound_lemmas.rs::add_zero_product_lemmas`). Keyed by
    /// `(target, bound, is_lower)` with the same pop/reset clearing
    /// discipline as `box_bound_emitted`.
    zero_product_emitted: HashSet<(TermId, BigRational, bool)>,

    /// Set by the NIA check loop when the most recent UNSAT verdict carries a
    /// replayable rational Positivstellensatz / SOS certificate of infeasibility
    /// (see [`sos`] and [`sos_check`]). A REAL SOS refutation certifies emptiness
    /// over ℝ ⊇ ℤ, hence over the integers. It is `None` when the (sound but
    /// incomplete) degree-2 search declines or the UNSAT is degenerate
    /// (syntactically-false atom). Reset to `None` at the start of every
    /// `check()`. Any stored certificate has already passed the module's
    /// independent checker.
    pub(crate) last_unsat_certificate: Option<sos::SosCertificate>,

    /// Cooperative wall-clock deadline for the refinement loop (#nia-deadline).
    ///
    /// Mirror of `LiaSolver::deadline` (#lia-deadline-forward): the DPLL/N-O
    /// callers only poll their own deadline BETWEEN theory checks, so a single
    /// dense `nia_check_loop` (Gomory/tangent cut escalation with BigRational
    /// arithmetic) could overshoot the caller's wall budget without bound.
    /// Polled at every refinement iteration boundary; `set_deadline` also
    /// forwards the deadline INTO the embedded `LiaSolver` so its cascade
    /// checkpoints observe the same wall. `None` (the default) preserves the
    /// old un-budgeted behavior.
    deadline: Option<ay_core::time::Instant>,

    /// Original (post-preprocessing) assertion FORMULAS for this solve, with
    /// their Boolean structure intact (#nia-clausal-sls).
    ///
    /// `asserted` only ever holds theory ATOMS under the SAT solver's current
    /// trail, which is enough for the box-shaped fallbacks but destroys exactly
    /// the clause structure the clausal local search needs. The executor
    /// installs the roots via [`NiaSolver::set_root_assertions`]; empty (the
    /// default) disables the lane.
    root_assertions: Vec<TermId>,

    /// The clausal local search is a whole-formula search whose result does not
    /// depend on the SAT trail, so it is attempted at most once per solver
    /// instance (#nia-clausal-sls).
    local_search_done: bool,

    /// Scheduling shape of the source roots before arithmetic purification.
    /// These roots supply no assertions or proof/model authority.
    local_search_first_offer: Option<local_search_order::FirstOffer>,

    /// Absolute wall cutoff for the clausal local-search lane
    /// (#nia-clausal-sls), shared by every theory instance the split loop
    /// creates during one solve.
    ///
    /// The executor recreates `NiaSolver` on every split iteration, so a
    /// per-instance budget compounds: each new instance would claim a fresh
    /// slice of the REMAINING wall and, between them, the whole deadline. That
    /// starves work that would still have finished — measured: one QF_NIA
    /// `unsat` that needed 12.3s of a 15s budget degraded to `unknown`. One
    /// absolute cutoff installed before the split loop caps the lane's TOTAL
    /// share of the solve and leaves the remainder to the rest of the pipeline.
    local_search_deadline: Option<ay_core::time::Instant>,

    /// Once-per-solve flag of the split probe (#nia-split-probe): a short,
    /// time-sliced clausal local search offered when the solve's first factor
    /// split is about to enumerate. Shared by every theory instance the split
    /// loop creates, like `local_search_deadline`; `None` disables it.
    split_probe: Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
}

impl<'a> NiaSolver<'a> {
    /// Create a new NIA solver
    pub fn new(terms: &'a TermStore) -> Self {
        let debug = ay_core::debug_channel_active(ay_core::DebugChannel::Nia);
        let mut lia = LiaSolver::new(terms);
        // NIA handles nonlinear multiplication — tell the inner LIA/LRA not to
        // flag it as unsupported. This mirrors NraSolver::new (nra/lib.rs:166-168),
        // making standalone NIA over-approximate nonlinear `*` as a fresh opaque
        // LRA variable (a sound relaxation) instead of poisoning LRA to Unknown.
        lia.set_combined_theory_mode(true);
        // The NIA's loop steers its own refinement from the inner LIA's split
        // requests; the lattice closure stays a pure-LIA tool (see the setter).
        lia.set_lattice_closure(false);
        Self {
            terms,
            lia,
            monomials: HashMap::default(),
            aux_to_monomial: HashMap::default(),
            sign_constraints: HashMap::default(),
            var_sign_constraints: HashMap::default(),
            sign_constraint_trail: Vec::new(),
            sign_constraint_trail_marks: Vec::new(),
            monomial_trail: Vec::new(),
            div_purifications: Vec::new(),
            asserted: Vec::new(),
            sos_fragment_cache: std::cell::RefCell::default(),
            scopes: Vec::new(),
            debug,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            tangent_lemma_count: 0,
            patch_count: 0,
            sign_cut_count: 0,
            unsat_with_guesses_count: 0,
            tentative_depth: 0,
            tentative_guess_count: 0,
            feasible_sets: HashMap::default(),
            blocked_vars: Vec::new(),
            fixed_vars: Vec::new(),
            feasible_set_count: 0,
            registered_atoms: Vec::new(),
            asserted_atom_set: HashSet::default(),
            sat_atoms: HashSet::default(),
            phase_memo: std::cell::RefCell::new((None, HashMap::default())),
            leaf_sign_memo: std::cell::RefCell::new((None, HashMap::default())),
            timings: NiaTimings::default(),
            bounded_enum_model: None,
            bounded_enum_bool_model: HashMap::default(),
            contracted_bounds: HashMap::default(),
            contracted_bound_reasons: HashMap::default(),
            congruence_linked: HashSet::default(),
            zero_bound_emitted: HashSet::default(),
            box_bound_emitted: HashSet::default(),
            zero_product_emitted: HashSet::default(),
            last_unsat_certificate: None,
            deadline: None,
            root_assertions: Vec::new(),
            local_search_done: false,
            local_search_first_offer: None,
            local_search_deadline: None,
            split_probe: None,
        }
    }

    /// Install the solve's original assertion formulas (#nia-clausal-sls).
    ///
    /// Only the clausal local-search lane reads these, and only to build its
    /// own clause set and to exactly re-verify a candidate witness. Nothing on
    /// the UNSAT side consults them, so an inaccurate or empty list can cost
    /// completeness but never soundness.
    pub fn set_root_assertions(&mut self, roots: Vec<TermId>) {
        self.root_assertions = roots;
        self.bounded_enum_model = None;
        self.bounded_enum_bool_model.clear();
        self.local_search_done = false;
        self.local_search_first_offer = None;
    }

    /// Install the shared absolute wall cutoff for the clausal local-search
    /// lane (#nia-clausal-sls); see the `local_search_deadline` field.
    ///
    /// Callers must compute this ONCE per solve, before the split loop, so
    /// every theory instance the loop creates shares one budget. Completeness
    /// only: a cutoff in the past simply disables the lane.
    pub fn set_local_search_deadline(&mut self, cutoff: ay_core::time::Instant) {
        self.local_search_deadline = Some(cutoff);
    }

    /// Install the once-per-solve split-probe flag (#nia-split-probe). Callers
    /// create ONE flag per solve, before the split loop, and hand every theory
    /// instance a clone, so the probe runs at most once per solve.
    pub fn set_split_probe_flag(&mut self, flag: std::sync::Arc<std::sync::atomic::AtomicBool>) {
        self.split_probe = Some(flag);
    }

    /// Install a cooperative wall-clock deadline on the NIA solver (#nia-deadline).
    ///
    /// Mirrors `LiaSolver::set_deadline` (#8749) and follows the
    /// #lia-deadline-forward pattern: the deadline is stored here for the
    /// `nia_check_loop` refinement-iteration polls AND pushed into the
    /// embedded `LiaSolver`, whose own cascade/IntSat checkpoints poll it —
    /// without the forward a single dense `lia.check()` inside the NIA loop
    /// could overshoot the caller's wall budget by whole seconds. The
    /// deadline survives `push`/`pop`/`reset` (the inner LIA keeps its copy
    /// across `reset()` too), matching the LIA semantics: it is a property of
    /// the enclosing solve, not of the assertion stack.
    pub fn set_deadline(&mut self, deadline: ay_core::time::Instant) {
        self.deadline = Some(deadline);
        self.lia.set_deadline(deadline);
    }

    /// Whether the enclosing solve's wall or live Check stop is exhausted.
    /// The shared poll also observes cancellation and ancestor work grants;
    /// a missing solver-owned deadline does not hide those controls.
    pub(crate) fn should_timeout(&self) -> bool {
        self.deadline
            .is_some_and(|dl| ay_core::time::Instant::now() >= dl)
            || ay_core::resource::check_stop_requested()
    }

    /// True iff the most recent `check()` retained a privately checked rational
    /// Positivstellensatz / SOS certificate (see [`sos`]). Its factor positions
    /// refer to the translated theory subset, not an authenticated public query.
    /// The renderer is diagnostic; exact-source native publication separately
    /// constructs and replays a typed `NraSos` bundle.
    pub fn took_sos_unsat_certificate(&self) -> bool {
        self.last_unsat_certificate.is_some()
    }

    /// Render the private certificate as diagnostic comments followed by an
    /// honest Alethe `:rule hole`, or `None` when none was retained. This is not
    /// an externally supported rule or portable proof. Names use the term store.
    pub fn render_sos_unsat_certificate(&self, step: &str) -> Option<String> {
        let cert = self.last_unsat_certificate.as_ref()?;
        Some(cert.render_alethe(step, |t| match self.terms.get(t) {
            TermData::Var(name, _) => name.clone(),
            _ => format!("v{}", t.0),
        }))
    }

    /// Register a monomial term and return its auxiliary variable
    pub fn register_monomial(&mut self, vars: Vec<TermId>, aux_var: TermId) {
        let mon = Monomial::new(vars.clone(), aux_var);
        // #3735: Record insertion on the monomial trail for push/pop scoping.
        if let Some(scope) = self.monomial_trail.last_mut() {
            scope.push((vars.clone(), aux_var));
        }
        self.aux_to_monomial.insert(aux_var, vars.clone());
        self.monomials.insert(vars, mon);
    }

    /// Get the value of a variable from the current LIA model
    pub(crate) fn var_value(&self, var: TermId) -> Option<BigRational> {
        // Use direct LRA access to get current value
        // (extract_model() returns None when integer variables have non-integer values)
        self.lia.lra_solver().get_value(var)
    }

    /// LIA timing breakdown from the underlying solver (#4794, #8823).
    ///
    /// Returns the embedded `LiaSolver`'s real per-phase timings. NIA-specific
    /// overhead (sign checks, patching, tangent lemmas, enumeration) is
    /// tracked separately — see [`NiaSolver::timings`] for that breakdown.
    pub fn lia_timings(&self) -> &ay_lia::LiaTimings {
        self.lia.timings()
    }

    /// NIA-specific phase timings (#8823).
    ///
    /// Tracks wall-clock time spent in NIA's own refinement phases
    /// (sign checks, patching, tangent lemma generation, bounded
    /// enumeration). Before #8823 NIA had no independent timing — callers
    /// reading `lia_timings()` got a static zero stub, and there was no
    /// way to separate NIA overhead from LIA cost at all.
    ///
    /// Pair with [`NiaSolver::lia_timings`] for a full picture.
    pub fn timings(&self) -> &NiaTimings {
        &self.timings
    }

    /// Reset accumulated NIA phase timings (#8823).
    pub fn reset_timings(&mut self) {
        self.timings = NiaTimings::default();
        self.lia.reset_timings();
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod sign_cut_soundness_tests;

#[cfg(test)]
mod shared_reason_tests;

#[cfg(test)]
mod factor_split_premise_tests;

#[cfg(test)]
mod factor_split_premise_provenance_tests;

#[cfg(test)]
mod split_giveup_tests;

#[cfg(test)]
mod stale_accept_tests;

#[cfg(test)]
mod split_probe_tests;

#[cfg(test)]
mod factor_split_precision_tests;
