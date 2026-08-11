#![forbid(unsafe_code)]

//! AY NRA - Non-linear Real Arithmetic theory solver
//!
//! Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//!
//! Implements model-based incremental linearization for nonlinear real arithmetic,
//! following the DPLL(T) approach where the SAT solver handles branching.
//!
//! ## Algorithm Overview
//!
//! 1. **Monomial tracking**: Map nonlinear terms like `x*y` to auxiliary variables
//! 2. **Sign lemmas**: Infer sign of product from signs of factors
//! 3. **Tangent plane lemmas**: Linear approximations at the current model point
//! 4. **Delegate to LRA**: Linear constraints are handled by the LRA solver
//!
//! Based on Z3's NLA solver (`reference/z3/src/math/lp/nla_*.cpp`).
//!
//! Check loop + refinement: see `check_loop.rs`

#![warn(missing_docs)]
#![warn(clippy::all)]
#![allow(
    clippy::doc_lazy_continuation,
    clippy::type_complexity,
    clippy::wrong_self_convention
)]

pub mod algebraic;
mod check_loop;
pub(crate) mod feasible_set;
mod icp;
mod monomial;
mod nlsat;
mod patch;
pub mod rcf_api;
mod sign;
mod sos;
// Fraction-free subresultant / PSC-chain substrate for CAD projection.
// Deliberately not wired into a solve path yet: it cannot change a verdict.
#[allow(dead_code)]
mod subresultant;
mod tangent;
mod theory_impl;
mod univariate;
mod verification;

#[cfg(test)]
mod theory_tests;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::DetHashMap as HashMap;
#[cfg(not(kani))]
type HashSet<T> = hashbrown::HashSet<T>;
use num_rational::BigRational;
#[cfg(kani)]
type HashSet<T> = ay_core::kani_compat::DetHashSet<T>;
use ay_core::term::{Constant, Symbol, TermData, TermId, TermStore};
use ay_core::{TheoryLit, TheoryPropagation, TheoryResult, TheorySolver};

use feasible_set::FeasibleSet;
use monomial::Monomial;
use num_traits::One;
use sign::SignConstraint;

/// The rational value of `term` if it is a numeric literal, else `None`.
///
/// Handles `Int` literals, `Rational` literals, and unary negation of either —
/// SMT-LIB writes negative literals as `(- 2)`, which is an `App`, not a `Const`.
/// Used by `#nra-const-factor` to separate the constant factors of a flattened
/// product from its variable factors.
fn constant_value_of(terms: &TermStore, term: TermId) -> Option<BigRational> {
    match terms.get(term) {
        TermData::Const(Constant::Int(n)) => Some(BigRational::from_integer(n.clone())),
        TermData::Const(Constant::Rational(r)) => Some(r.0.clone()),
        TermData::App(Symbol::Named(name), args) if name == "-" && args.len() == 1 => {
            constant_value_of(terms, args[0]).map(|c| -c)
        }
        _ => None,
    }
}

/// The product of the constant factors of `term` when it is a `*` application,
/// else `1`. `#nra-const-factor` invariant helper: a term that may be used as a
/// monomial `aux_var` must have a constant factor of exactly 1.
fn constant_factor_of(terms: &TermStore, term: TermId) -> BigRational {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "*" => {
            let mut product = BigRational::one();
            for &arg in args {
                if let Some(c) = constant_value_of(terms, arg) {
                    product *= c;
                }
            }
            product
        }
        _ => BigRational::one(),
    }
}

/// A purified division: `(/ num denom)` → fresh LRA variable `div_term`,
/// with side constraint `denom * div_term = num`.
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
/// the NRA check loop. The NRA check loop (via LRA simplex + monomial
/// refinement) needs significant stack in debug. A 4 MiB red zone triggers
/// growth when a default 8 MiB test thread has less than 4 MiB remaining.
const NRA_STACK_RED_ZONE: usize = 4 * 1024 * 1024;

/// Size of the new stack segment allocated when the red zone is reached.
/// 16 MiB to provide ample room for NRA check iterations in debug mode.
const NRA_STACK_SIZE: usize = 16 * 1024 * 1024;

/// Guard the NRA entrypoint against stack overflow on small thread stacks.
fn maybe_grow_nra_stack<R>(f: impl FnOnce() -> R) -> R {
    stacker::maybe_grow(NRA_STACK_RED_ZONE, NRA_STACK_SIZE, f)
}

pub use algebraic::{RealAlgebraic, RealAlgebraicValue, RealScalar};
pub use ay_lra::LraModel;
/// Measurement harness for the fraction-free subresultant substrate; see
/// [`subresultant::diag_subresultant_incumbent_versus_fraction_free`]. Exposed
/// for `examples/subresultant_measurement.rs` so the measurement is a runnable
/// target rather than an `#[ignore]`d test that never runs.
#[doc(hidden)]
pub use subresultant::diag_subresultant_incumbent_versus_fraction_free;

/// Trail entry for sign constraint push/pop (#8626).
/// Records which map received an addition so it can be undone on pop.
#[derive(Debug, Clone)]
enum SignConstraintTrailEntry {
    /// A constraint was pushed onto `sign_constraints[key]`.
    Monomial(Vec<TermId>),
    /// A constraint was pushed onto `var_sign_constraints[var]`.
    Variable(TermId),
}

/// NRA theory solver using model-based incremental linearization
pub struct NraSolver<'a> {
    /// Reference to the term store
    terms: &'a TermStore,
    /// Underlying LRA solver for linear constraints
    pub(crate) lra: ay_lra::LraSolver,
    /// Tracked monomials: sorted var list -> Monomial info
    pub(crate) monomials: HashMap<Vec<TermId>, Monomial>,
    /// Auxiliary variable to monomial mapping (reverse index)
    aux_to_monomial: HashMap<TermId, Vec<TermId>>,
    /// Sign constraints on monomials
    sign_constraints: HashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>>,
    /// Sign constraints on variables
    var_sign_constraints: HashMap<TermId, Vec<(SignConstraint, TermId)>>,
    /// Trail of sign constraint additions for efficient push/pop (#8626).
    /// Each entry records which map received an addition. On pop(), the
    /// last element is popped from the corresponding inner Vec.
    sign_constraint_trail: Vec<SignConstraintTrailEntry>,
    /// Scope markers for sign constraint trail: saved trail length at push().
    sign_constraint_trail_marks: Vec<usize>,
    /// Division purifications: `(/ num denom)` → side constraint `denom * div = num`.
    /// Tracked separately from monomials because the numerator may be a constant
    /// with no LRA variable (#6811).
    div_purifications: Vec<DivPurification>,
    /// Every real-division term seen, regardless of whether the denominator is
    /// symbolic (purified) or a constant. Used for division-by-zero soundness:
    /// SMT-LIB leaves `(/ a 0)` UNCONSTRAINED but still a total FUNCTION of its
    /// arguments, so a candidate model with a zero divisor is a sound SAT
    /// witness only when every pair of zero-denominator divisions whose
    /// numerators agree in the model also agree on the division value (the
    /// purification constraint `denom*div=num` is vacuous at denom=0, and
    /// distinct `(/ a 0)` occurrences would otherwise be over-approximated as
    /// independent free variables — wrong-sat). When the model cannot be
    /// certified functionally consistent we return Unknown (#div0-soundness,
    /// see `zero_divisor_model_is_unsound`).
    div_terms: Vec<DivPurification>,
    /// Asserted atoms for conflict generation
    asserted: Vec<(TermId, bool)>,
    /// Scope markers for push/pop: (asserted_len, div_purifications_len,
    /// div_terms_len).
    scopes: Vec<(usize, usize, usize)>,
    /// Debug flag
    pub(crate) debug: bool,
    check_count: u64,
    conflict_count: u64,
    propagation_count: u64,
    tangent_lemma_count: u64,
    patch_count: u64,
    sign_cut_count: u64,
    /// Number of tentative LRA scopes active (sign-cut + patch scopes).
    /// The sign-cut path (lib.rs:322) and try_tentative_patch (patch.rs:245)
    /// each push one scope. undo_tentative_patch() must pop ALL of them
    /// to avoid leaking model-dependent bounds into future queries.
    tentative_depth: u32,

    // --- clauseSMT NLSAT techniques (#8445) ---
    /// Per-variable feasible sets: intersection of clause-level feasible sets.
    /// Updated during clause-level propagation when a clause becomes univariate.
    /// Maps term_id of variables involved in nonlinear constraints to their
    /// current feasible sets.
    pub(crate) feasible_sets: HashMap<TermId, FeasibleSet>,

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

    /// Exact ALGEBRAIC model witnesses, set by the exact decision procedures on
    /// the SAME `check()` that returns [`TheoryResult::Sat`] when
    /// satisfiability was proven by a Sturm / IVT real-root certificate whose
    /// witness is IRRATIONAL (e.g. `x*x = 2`, whose only roots are `±√2`).
    /// The certificate is an exact `BigRational` sign-invariant cell analysis
    /// (see `univariate.rs` `decide_single_variable` /
    /// `SingleVarResult::IrrationalSat`), and each entry carries the full
    /// witness as a [`RealAlgebraicValue`] (defining square-free polynomial,
    /// 1-based root index, isolating interval — z3 `root-obj` data).
    ///
    /// The executor reads this (via [`NraSolver::algebraic_model`]) after a
    /// SAT check and stores the witnesses in its model, where variable lookup,
    /// polynomial evaluation, `(get-value)`/`(get-model)` printing and FULL
    /// model validation all handle them exactly. Rational witnesses for the
    /// remaining variables are injected into the LRA model as usual.
    ///
    /// Reset at the start of every `check()`; only ever populated when an
    /// exact procedure returns [`UniResult::SatAlgebraic`] with witnesses.
    pub(crate) algebraic_model: Vec<(TermId, RealAlgebraicValue)>,

    /// Set by the NRA check loop when the most recent UNSAT verdict carries a
    /// replayable rational Positivstellensatz / SOS certificate of infeasibility
    /// (see [`sos`]). This is the algebraic proof that replaces the audited
    /// `:rule trust` hole for the theory conflict; it is `None` when the
    /// (sound but incomplete) degree-2 search declines, in which case the
    /// interval-exhaustion UNSAT keeps its trust fallback. Reset to `None` at the
    /// start of every check. Any stored certificate has already passed the
    /// independent checker.
    pub(crate) last_unsat_certificate: Option<sos::SosCertificate>,

    /// SOLVE-WIDE node budget for the ICP dyadic grid search
    /// ([`NraSolver::dyadic_grid_search`]), decremented across every `check()`
    /// **of this solver instance**.
    ///
    /// # This is NOT a solve-wide cap, despite the intent
    ///
    /// An earlier revision of this comment claimed the budget bounded the whole
    /// solve ("once the whole solve has spent it, the phase declines"). That is
    /// **false**, and the code cannot deliver it as written:
    /// `solve_nra` (`ay-dpll/src/executor/theories/nra/mod.rs`) drives
    /// `solve_incremental_theory_pipeline!`, whose body is
    /// `loop { … let mut theory = $create_theory; … }` — a **fresh `NraSolver`
    /// per DPLL(T) refinement**. Each new instance resets this field to
    /// [`GRID_SOLVE_NODES`](crate::icp::GRID_SOLVE_NODES), so on the
    /// boolean-heavy instances the cap was meant to protect it is re-granted
    /// exactly as often as the cost is re-paid.
    ///
    /// The effective bound is therefore
    /// [`GRID_MAX_NODES`](crate::icp::GRID_MAX_NODES) **per `check()`**, times
    /// the number of refinements — precisely the situation this field was added
    /// to prevent. It is cost-only, never soundness: exhausting the budget
    /// declines the phase and leaves the verdict at the `unknown` it would
    /// otherwise have been.
    ///
    /// Measured: no pool exercised so far is bitten by this (worst observed
    /// slowdowns are 21.3→34.3 s and 192.2→204.3 s, both well inside a 300 s
    /// cap), which is why the field is kept rather than deleted — it does bound
    /// a single instance's grid work. **Making it genuinely solve-wide requires
    /// threading the counter through the pipeline macro; do that before relying
    /// on it for anything, and do not re-add a solve-wide claim to this comment
    /// until the plumbing exists.**
    ///
    /// A [`Cell`](std::cell::Cell) because `check()`'s exact procedures take
    /// `&self`.
    pub(crate) grid_budget: std::cell::Cell<usize>,
}

impl<'a> NraSolver<'a> {
    /// Create a new NRA solver
    pub fn new(terms: &'a TermStore) -> Self {
        let debug = ay_core::debug_channel_active(ay_core::DebugChannel::Nra);
        let mut lra = ay_lra::LraSolver::new(terms);
        // NRA handles nonlinear multiplication — tell LRA not to flag it as unsupported.
        lra.set_combined_theory_mode(true);
        Self {
            terms,
            lra,
            monomials: HashMap::default(),
            aux_to_monomial: HashMap::default(),
            sign_constraints: HashMap::default(),
            var_sign_constraints: HashMap::default(),
            sign_constraint_trail: Vec::new(),
            sign_constraint_trail_marks: Vec::new(),
            div_purifications: Vec::new(),
            div_terms: Vec::new(),
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
            algebraic_model: Vec::new(),
            last_unsat_certificate: None,
            grid_budget: std::cell::Cell::new(icp::GRID_SOLVE_NODES),
        }
    }

    /// Exact algebraic model witnesses from the most recent `check()`, when it
    /// returned SAT via an exact Sturm/IVT real-root certificate with at least
    /// one irrational witness (empty otherwise). Each entry is a variable's
    /// exact [`RealAlgebraicValue`]; rational witnesses for the remaining
    /// variables were injected into the LRA model. See the `algebraic_model`
    /// field doc and `univariate.rs`. Sound: a SAT is reported here only with
    /// the exact certificate behind it, and the executor's full model
    /// validation re-confirms every assertion under these witnesses.
    pub fn algebraic_model(&self) -> &[(TermId, RealAlgebraicValue)] {
        &self.algebraic_model
    }

    /// True iff the most recent `check()` returned UNSAT with a replayable
    /// rational Positivstellensatz / SOS certificate attached (see [`sos`]). When
    /// true, [`NraSolver::render_sos_unsat_certificate`] yields an independently
    /// checkable algebraic proof of infeasibility that can replace the audited
    /// `:rule trust` hole for that theory conflict in the certificate stream.
    pub fn took_sos_unsat_certificate(&self) -> bool {
        self.last_unsat_certificate.is_some()
    }

    /// Render the last UNSAT's Positivstellensatz certificate as an Alethe-style
    /// proof step (empty clause, `:rule nra_positivstellensatz`), or `None` if
    /// the last UNSAT had no certificate (interval-exhaustion with the trust
    /// fallback). Variable names are resolved from the term store.
    pub fn render_sos_unsat_certificate(&self, step: &str) -> Option<String> {
        let cert = self.last_unsat_certificate.as_ref()?;
        Some(cert.render_alethe(step, |t| match self.terms.get(t) {
            TermData::Var(name, _) => name.clone(),
            _ => format!("v{}", t.0),
        }))
    }

    /// Get the value of a variable from the current LRA model
    pub(crate) fn var_value(&self, var: TermId) -> Option<BigRational> {
        self.lra.get_value(var)
    }

    /// Register a monomial
    ///
    /// INVARIANT (`#nra-const-factor`): `aux_var` must denote EXACTLY
    /// `product(vars)`, with no residual constant factor. Every consumer of a
    /// registered monomial (sign lemmas, McCormick/tangent cuts, even-power
    /// non-negativity, `check_monomial_consistency`, `propagate_monomial_signs`)
    /// relies on that equality; registering `c * product(vars)` under the key
    /// `vars` makes them enforce a FALSE relation and can yield a wrong `unsat`.
    fn register_monomial(&mut self, vars: Vec<TermId>, aux_var: TermId) {
        debug_assert!(
            constant_factor_of(self.terms, aux_var).is_one(),
            "#nra-const-factor: register_monomial called with a SCALED aux term \
             {aux_var:?} (constant factor {:?} != 1); aux_var must equal \
             product(vars) exactly or every monomial consumer enforces a false \
             relation (wrong-unsat)",
            constant_factor_of(self.terms, aux_var)
        );
        if self.debug {
            tracing::debug!(
                "[NRA] register_monomial: vars={:?}, aux_var={:?}",
                vars,
                aux_var
            );
        }
        let mon = Monomial::new(vars.clone(), aux_var);
        self.aux_to_monomial.insert(aux_var, vars.clone());
        self.monomials.insert(vars, mon);
    }

    /// Recursively scan a term for nonlinear subterms and register them
    fn collect_nonlinear_terms(&mut self, term: TermId) {
        match self.terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                match name.as_str() {
                    "*" => {
                        // SOUNDNESS (`#nra-const-factor`, sibling of
                        // `#nia-const-factor` in nia/src/tangent_add.rs).
                        //
                        // The frontend flattens nested products, so
                        // `(* x (* y (- 2)))` arrives here as the single n-ary
                        // node `(* x y (- 2))`. Splitting the args into
                        // constants and variables and then registering the WHOLE
                        // node as the aux var of the monomial `[x, y]` asserts
                        // `aux_var == x*y` for a term whose value is `-2*x*y`.
                        // Every consumer then reasons with that false equality:
                        //   * `record_sign_constraint` files the atom's sign
                        //     verbatim on the bare monomial, so `-2*x*y <= 0`
                        //     becomes `x*y <= 0` — the OPPOSITE of what was
                        //     asserted — and `check_sign_consistency` reports a
                        //     conflict against `x > 0, y > 0`. That is a wrong
                        //     `unsat` (a false theorem), the P0 meti-tarski bug.
                        //   * McCormick/tangent cuts (tangent.rs) and
                        //     `add_even_power_nonneg` inject linear bounds that
                        //     are false for the scaled term.
                        //   * `check_monomial_consistency` (check_loop.rs)
                        //     enforces `c*prod == prod`.
                        //
                        // Track the product of the constant factors and only
                        // register when it is exactly 1, so the invariant
                        // `aux_var == product(vars)` holds. Otherwise leave the
                        // term as an opaque LRA variable: LRA over-approximates
                        // it (any value), which is sound — it can cost
                        // completeness (`unknown` instead of a verdict) but can
                        // never produce a wrong answer.
                        let mut var_args = Vec::new();
                        let mut const_product = BigRational::one();
                        for &arg in args {
                            match constant_value_of(self.terms, arg) {
                                Some(c) => const_product *= c,
                                None => var_args.push(arg),
                            }
                        }

                        if var_args.len() >= 2 && const_product.is_one() {
                            var_args.sort_by_key(|t| t.0);
                            if !self.monomials.contains_key(&var_args) {
                                self.register_monomial(var_args, term);
                            }
                        } else if var_args.len() >= 2 && self.debug {
                            tracing::debug!(
                                "[NRA] Skipping scaled monomial {:?} (const factor {:?} != 1) \
                                 to preserve aux==product(vars) invariant",
                                term,
                                const_product
                            );
                        }
                    }
                    "/" if args.len() == 2 => {
                        // Division purification (#6811): (/ num denom) with symbolic
                        // denominator → track for refinement via denom * div = num.
                        let num = args[0];
                        let denom = args[1];
                        let denom_is_const = self.terms.extract_integer_constant(denom).is_some()
                            || matches!(
                                self.terms.get(denom),
                                TermData::Const(Constant::Rational(_))
                            );
                        if !denom_is_const
                            && !self.div_purifications.iter().any(|p| p.div_term == term)
                        {
                            self.div_purifications.push(DivPurification {
                                div_term: term,
                                numerator: num,
                                denominator: denom,
                            });
                        }
                        // #div0-soundness: record EVERY division term (const or
                        // symbolic denominator) so the zero-divisor functional-
                        // consistency check can inspect the candidate model. A
                        // literal-0 denominator (e.g. `(/ x 0.0)`) is never
                        // purified, and a symbolic denominator may evaluate to 0
                        // — in either case `(/ a 0)` is unconstrained but must
                        // still be a consistent FUNCTION of its arguments, which
                        // `zero_divisor_model_is_unsound` certifies per model.
                        if !self.div_terms.iter().any(|p| p.div_term == term) {
                            self.div_terms.push(DivPurification {
                                div_term: term,
                                numerator: num,
                                denominator: denom,
                            });
                        }
                    }
                    _ => {}
                }
                for &arg in args {
                    self.collect_nonlinear_terms(arg);
                }
            }
            TermData::Not(inner) => self.collect_nonlinear_terms(*inner),
            TermData::Ite(c, t, e) => {
                self.collect_nonlinear_terms(*c);
                self.collect_nonlinear_terms(*t);
                self.collect_nonlinear_terms(*e);
            }
            TermData::Let(_, body) => self.collect_nonlinear_terms(*body),
            _ => {}
        }
    }

    /// Extract a model from the solver, returning an LRA-compatible model.
    pub fn extract_model(&self) -> LraModel {
        self.lra.extract_model()
    }

    /// Access the underlying LRA solver for value queries in combined theory adapters.
    pub fn lra(&self) -> &ay_lra::LraSolver {
        &self.lra
    }
}
