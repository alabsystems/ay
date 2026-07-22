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
pub(crate) mod feasible_set;
mod interval_contract;
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
    /// Number of tentative LIA scopes active (sign-cut + patch scopes).
    /// The sign-cut path and try_tentative_patch each push one scope.
    /// undo_tentative_patch() must pop ALL of them to avoid leaking
    /// model-dependent bounds into future queries.
    tentative_depth: u32,

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

    /// Set by the NIA check loop when the most recent UNSAT verdict carries a
    /// replayable rational Positivstellensatz / SOS certificate of infeasibility
    /// (see [`sos`] and [`sos_check`]). A REAL SOS refutation certifies emptiness
    /// over ℝ ⊇ ℤ, hence over the integers. It is `None` when the (sound but
    /// incomplete) degree-2 search declines or the UNSAT is degenerate
    /// (syntactically-false atom). Reset to `None` at the start of every
    /// `check()`. Any stored certificate has already passed the module's
    /// independent checker.
    pub(crate) last_unsat_certificate: Option<sos::SosCertificate>,

    /// Hard wall-clock deadline for the refinement loop (#nia-deadline).
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
            scopes: Vec::new(),
            debug,
            check_count: 0,
            conflict_count: 0,
            propagation_count: 0,
            tangent_lemma_count: 0,
            patch_count: 0,
            sign_cut_count: 0,
            tentative_depth: 0,
            feasible_sets: HashMap::default(),
            blocked_vars: Vec::new(),
            fixed_vars: Vec::new(),
            feasible_set_count: 0,
            registered_atoms: Vec::new(),
            asserted_atom_set: HashSet::default(),
            timings: NiaTimings::default(),
            bounded_enum_model: None,
            congruence_linked: HashSet::default(),
            zero_bound_emitted: HashSet::default(),
            box_bound_emitted: HashSet::default(),
            last_unsat_certificate: None,
            deadline: None,
        }
    }

    /// Install a hard wall-clock deadline on the NIA solver (#nia-deadline).
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

    /// Whether the enclosing solve's wall-clock budget is exhausted
    /// (#nia-deadline). `false` when no deadline was installed.
    pub(crate) fn should_timeout(&self) -> bool {
        self.deadline
            .is_some_and(|dl| ay_core::time::Instant::now() >= dl)
    }

    /// True iff the most recent `check()` returned UNSAT with a replayable
    /// rational Positivstellensatz / SOS certificate attached (see [`sos`]). When
    /// true, [`NiaSolver::render_sos_unsat_certificate`] yields an independently
    /// checkable algebraic proof of infeasibility.
    pub fn took_sos_unsat_certificate(&self) -> bool {
        self.last_unsat_certificate.is_some()
    }

    /// Render the last UNSAT's Positivstellensatz certificate as an Alethe-style
    /// proof step (empty clause, `:rule nia_positivstellensatz`), or `None` if
    /// the last UNSAT had no certificate. Variable names are resolved from the
    /// term store.
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

    /// Extract a model from the solver
    pub fn extract_model(&self) -> Option<NiaModel> {
        if let Some(enum_model) = &self.bounded_enum_model {
            let mut values = self
                .lia
                .extract_model()
                .map(|lia_model| lia_model.values)
                .unwrap_or_default();
            values.extend(
                enum_model
                    .iter()
                    .map(|(&term, value)| (term, value.clone())),
            );
            return Some(NiaModel { values });
        }

        self.lia.extract_model().map(|lia_model| NiaModel {
            values: lia_model.values,
        })
    }

    /// Get the auxiliary variable for a monomial (if registered)
    pub fn get_monomial_aux(&self, vars: &[TermId]) -> Option<TermId> {
        self.monomials.get(vars).map(|m| m.aux_var)
    }

    /// All registered monomials, sorted by variable list for deterministic iteration.
    pub fn monomials_sorted(&self) -> Vec<&Monomial> {
        let mut ms: Vec<&Monomial> = self.monomials.values().collect();
        ms.sort_unstable_by(|a, b| a.vars.cmp(&b.vars));
        ms
    }

    /// Passthrough: get the underlying LRA solver (via LIA) for bound
    /// conflict collection in the split-loop pipeline.
    pub fn lra_solver(&self) -> &ay_lra::LraSolver {
        self.lia.lra_solver()
    }

    /// Passthrough: replay learned cuts into the underlying LIA solver
    /// after asserting new literals in a fresh theory instance.
    pub fn replay_learned_cuts(&mut self) {
        self.lia.replay_learned_cuts();
    }

    /// Passthrough: take learned state from the underlying LIA solver for
    /// cross-iteration persistence in the split-loop pipeline.
    pub fn take_learned_state(&mut self) -> (Vec<ay_lia::StoredCut>, HashSet<ay_lia::HnfCutKey>) {
        self.lia.take_learned_state()
    }

    /// Passthrough: import previously learned state into the underlying LIA solver.
    pub fn import_learned_state(
        &mut self,
        cuts: Vec<ay_lia::StoredCut>,
        seen: HashSet<ay_lia::HnfCutKey>,
    ) {
        self.lia.import_learned_state(cuts, seen);
    }

    /// Passthrough: take Diophantine solver state from the underlying LIA solver.
    pub fn take_dioph_state(&mut self) -> ay_lia::DiophState {
        self.lia.take_dioph_state()
    }

    /// Passthrough: import Diophantine solver state into the underlying LIA solver.
    pub fn import_dioph_state(&mut self, state: ay_lia::DiophState) {
        self.lia.import_dioph_state(state);
    }

    /// Enable combined theory mode on the underlying LIA solver.
    ///
    /// When enabled, the LIA solver tracks shared equalities from EUF and
    /// participates in the Nelson-Oppen equality-propagation fixpoint loop.
    /// Required for UF+NIA theory combination (#4525).
    pub fn set_combined_theory_mode(&mut self, enabled: bool) {
        self.lia.set_combined_theory_mode(enabled);
    }

    /// Access the underlying LIA solver for model value extraction in N-O loops.
    ///
    /// Used by the UfNiaSolver adapter to evaluate interface terms under the
    /// LIA model and propagate equalities to EUF (#4525).
    pub fn lia(&self) -> &LiaSolver<'a> {
        &self.lia
    }
}

#[cfg(test)]
mod tests;

#[cfg(kani)]
mod verification;
