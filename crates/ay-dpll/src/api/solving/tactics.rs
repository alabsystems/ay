// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Goal-to-goal tactics (Z3-compatible surface).
//!
//! A *goal* in Z3 terms is a set of assertions (formulas). A *tactic* transforms
//! a goal into **one or more** subgoals. A case-splitting tactic (e.g.
//! `split-clause`) yields several subgoals whose *disjunction* is equivalent to
//! the input; every other tactic yields exactly one. This module implements that
//! framework:
//!
//! - Primitive passes: [`Tactic::FlattenAnd`] (Z3's `simplify`/`elim-and`),
//!   [`Tactic::SolveEqs`], [`Tactic::PropagateValues`], [`Tactic::QeLight`],
//!   [`Tactic::TseitinCnf`] (Z3's `tseitin-cnf`/`cnf`), and the multi-subgoal
//!   [`Tactic::SplitClause`].
//! - The always-failing [`Tactic::Fail`] and the identity [`Tactic::Skip`].
//! - Combinators: [`Tactic::Then`], [`Tactic::OrElse`], [`Tactic::Repeat`],
//!   [`Tactic::When`], [`Tactic::FailIf`].
//! - [`Tactic::solver`] — a [`TacticSolver`] that applies the tactic before
//!   solving.
//!
//! # Soundness (goal preservation)
//!
//! Every transformation here is **model-preserving as a disjunction**: the set
//! of models of the input goal equals the union of the models of the produced
//! subgoals. For a single-subgoal tactic that is plain equivalence; for
//! `split-clause` it is the case-split identity `(a ∨ b) ∧ R  ≡  (a ∧ R) ∨ (b ∧
//! R)`. Consequently the input is SAT iff *some* subgoal is SAT, and any model
//! of a subgoal is a model of the input. Combinators only compose sound tactics,
//! so they preserve the property.
//!
//! Because of that, a solver that applies a tactic before solving returns the
//! SAME SAT/UNSAT verdict as solving the original goal. Public decision queries
//! additionally require an exact-source proof: until a tactic equivalence
//! certificate exists, [`TacticSolver`] executes the tactic against a detached
//! clone of the source term store and root vector, discards every speculative
//! term it builds, and solves the untouched source assertions. It never
//! substitutes a merely changed root vector for the exact authored query or
//! lets scratch terms enter later whole-store scans. When a tactic *splits* into
//! several subgoals, the single-goal solver path likewise solves the ORIGINAL
//! goal, which is equisatisfiable to their disjunction. A tactic that honestly
//! fails returns `Unknown` and retires every preceding solve artefact; it never
//! reuses a stale verdict or model.
//!
//! A few tactics are **equisatisfiable but not model-preserving**:
//! [`Tactic::TseitinCnf`] (fresh Boolean definition variables),
//! [`Tactic::ElimTermIte`] (fresh term-ite definition variables), and
//! [`Tactic::ReduceArgs`] (fresh per-constant-tuple function symbols `f!k`).
//! Their models differ from the input's on the new symbols, but they still
//! preserve the property the solver relies on — `check-sat(result) ==
//! check-sat(input)` with the fresh symbols treated as free — because every
//! input model extends to a result model and every result model restricts to an
//! input model. We never claim equivalence for them (see the pass docs in
//! `preprocess::tseitin_cnf`, `TermStore::name_non_bool_ites_all`, and
//! `preprocess::reduce_args`).

use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};
use ay_frontend::{Probe, ProbeCmp};

use crate::api::types::{
    NativeReplayEventKind, SolveResult, SolverError, Term, VerifiedSolveResult,
};
use crate::api::{Logic, Solver};
use crate::preprocess::{
    BitBlast, DistributeForall, FlattenAnd, Nnf, PreprocessingPass, PropagateIneqs,
    PropagateValues, QeLight, ReduceArgs, TseitinCnf, VariableSubstitution,
};
use crate::UnknownReason;

/// A single goal produced by a tactic: a set of assertion formulas plus the
/// Z3-style *depth* (number of primitive tactic applications) reached to
/// produce it.
#[derive(Debug, Clone)]
pub struct Goal {
    /// The goal's formulas (an implicit conjunction).
    pub formulas: Vec<TermId>,
    /// The Z3 goal depth reached to produce this goal.
    pub depth: usize,
    /// Immutable typed reconstruction; absent for identity transformations.
    /// Created only by the solver's context-bound converted-goal entry.
    pub model_converter: Option<super::tactic_model::TacticModelConverter>,
}

/// A public subgoal retaining the model reconstruction its terms require.
#[derive(Debug, Clone)]
pub struct TacticSubgoal {
    /// The transformed formulas in this subgoal.
    pub formulas: Vec<Term>,
    /// The goal depth reached by the transformation.
    pub depth: usize,
    /// Typed model reconstruction required by the transformed formulas.
    pub model_converter: Option<super::tactic_model::TacticModelConverter>,
}

/// Retained native request for an adapter's input/output metadata copies.
/// It borrows the existing evaluation controls/counter/arena and supplies no
/// machine admission, proof or model authority. Nested requests share it.
pub struct TacticOperation {
    scope: crate::executor::TacticConstructionScope,
    _read: crate::executor::EvaluationReadScope,
    started_at: std::time::Instant,
}
/// The same original operation after its explicit native assertion handoff.
/// Keeps construction scratch and controls alive through adapter publication.
pub struct TacticDecision {
    scope: crate::executor::TacticDeclarationScope,
    _read: crate::executor::EvaluationReadScope,
    /// The verified result authorized by the declaration handoff.
    pub result: VerifiedSolveResult,
    /// The optional model paired with `result`.
    pub model: Option<super::super::Model>,
}
impl TacticDecision {
    /// Publish a terminal adapter failure before releasing this original read.
    pub fn publish_failure(&self, solver: &mut Solver, error: &SolverError) {
        solver.set_tactic_error_unknown(error);
    }
    /// Debit the actual native declaration table traversal, including vacant
    /// buckets retained after scope rollback, before a borrowed adapter scan.
    pub fn admit_declaration_scan(&self, solver: &Solver) -> bool {
        self.validate(solver)
            && self
                .admission()
                .admit(solver.var_names.allocation_size(), 0)
                .is_ok()
            && self.validate(solver)
    }
    /// Validate that the declaration handoff remains active for `solver`.
    pub fn validate(&self, solver: &Solver) -> bool {
        self.scope.validate_decision(&solver.executor)
    }
    /// Return the construction admission retained by the declaration scope.
    pub fn admission(&self) -> &dyn ay_core::term::TermConstructionAdmission {
        self.scope.admission()
    }
}
impl TacticOperation {
    pub(super) fn sublimit_end(
        &self,
        milliseconds: Option<u32>,
    ) -> Result<Option<std::time::Instant>, SolverError> {
        match milliseconds.filter(|v| *v != 0 && *v != u32::MAX) {
            None => Ok(None),
            Some(ms) => self
                .started_at
                .checked_add(std::time::Duration::from_millis(u64::from(ms)))
                .map(Some)
                .ok_or_else(|| SolverError::TacticFailed("direct timeout overflow".into())),
        }
    }
    /// Retire a failed adapter request while its original first refusal is
    /// still live. This publishes negative evidence only.
    pub fn publish_failure(self, solver: &mut Solver, error: &SolverError) {
        solver.set_tactic_error_unknown(error);
    }
    /// Return the construction admission retained by this operation.
    pub fn admission(&self) -> &dyn ay_core::term::TermConstructionAdmission {
        self.scope.admission()
    }
    /// Validate that this operation still belongs to `solver`'s live query.
    pub fn validate(&self, solver: &Solver) -> bool {
        self.scope.validate(&solver.executor)
    }
}

impl Goal {
    pub(crate) fn capture_model_converter<'a>(
        &mut self,
        terms: &TermStore,
        names: impl Iterator<Item = (&'a String, &'a ay_frontend::SymbolInfo)>,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<(), TacticFailure> {
        self.model_converter = Some(super::tactic_model::TacticModelConverter::capture(
            terms,
            &self.formulas,
            names,
            owner,
        )?);
        Ok(())
    }
    /// A root goal (depth 0) over `formulas`, exactly as given.
    #[must_use]
    pub fn root(formulas: Vec<TermId>) -> Self {
        Goal {
            formulas,
            depth: 0,
            model_converter: None,
        }
    }

    /// A root goal (depth 0) built the way Z3's `goal` is: every top-level
    /// conjunction is RECURSIVELY split into separate formulas, trivially-`true`
    /// conjuncts are dropped, and the whole goal collapses to the single literal
    /// `false` if any conjunct is `false`.
    ///
    /// Z3 does this decomposition when assertions are inserted into a goal, so it
    /// is visible for EVERY tactic — even the identity `skip` prints `(and a b c)`
    /// as the three formulas `a`, `b`, `c` at depth 0. This constructor reproduces
    /// that goal shape; it needs the [`TermStore`] to inspect term structure,
    /// which is why the raw [`Goal::root`] cannot do it. The decomposition is
    /// equisatisfiability-preserving (in fact equivalence-preserving): the implicit
    /// conjunction of the returned formulas has exactly the models of the input.
    #[must_use]
    pub fn root_flattened(terms: &TermStore, formulas: &[TermId]) -> Self {
        Goal {
            formulas: flatten_goal_formulas(terms, formulas),
            depth: 0,
            model_converter: None,
        }
    }
}

/// An honest tactic failure (Z3's `tactic failed: …`).
///
/// A failing tactic (`fail`, `fail-if` with a true probe, `split-clause` on a
/// goal with no clause) produces NO goal — the surface reports the failure
/// rather than fabricating a result.
#[derive(Debug, Clone)]
pub struct TacticFailure {
    /// The Z3-style failure reason (without the `tactic failed: ` prefix).
    pub message: String,
    pub(crate) local_limit: Option<crate::api::TacticLimitKind>,
}

impl TacticFailure {
    pub(super) fn limited(kind: crate::api::TacticLimitKind) -> Self {
        Self {
            message: kind.to_string(),
            local_limit: Some(kind),
        }
    }
    pub(super) fn into_solver_error(self) -> SolverError {
        match self.local_limit {
            Some(kind) => SolverError::TacticLimit(kind),
            None => SolverError::TacticFailed(self.message),
        }
    }

    pub(super) fn new(message: impl Into<String>) -> Self {
        TacticFailure {
            message: message.into(),
            local_limit: None,
        }
    }
}

/// The result of applying a tactic to one goal: either the produced subgoals
/// (whose disjunction is equisatisfiable to the input), or an honest failure.
pub type ApplyResult = Result<Vec<Goal>, TacticFailure>;

/// Internal per-step outcome: the produced subgoals plus whether the step made
/// progress (used by `repeat` to detect a fixpoint without relying on a possibly
/// order-shuffling formula comparison).
struct StepOutcome {
    goals: Vec<Goal>,
    progressed: bool,
}

fn logical_failure(
    owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
    message: &str,
) -> Result<StepOutcome, TacticFailure> {
    if let Some(owner) = owner {
        owner
            .admit(message.len(), message.len())
            .map_err(|_| TacticFailure::new("tactic original owner stopped"))?;
    }
    Err(TacticFailure::new(message))
}

fn reserve_owned<T>(
    values: &mut Vec<T>,
    additional: usize,
    owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
) -> Result<(), TacticFailure> {
    if let Some(owner) = owner {
        ay_core::term::reserve_counted(values, additional, owner)
            .map_err(|_| TacticFailure::new("tactic original buffer admission refused"))
    } else {
        values.reserve(additional);
        Ok(())
    }
}
fn singleton_outcome(
    goal: Goal,
    progressed: bool,
    owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
) -> Result<StepOutcome, TacticFailure> {
    let mut goals = Vec::new();
    reserve_owned(&mut goals, 1, owner)?;
    goals.push(goal);
    Ok(StepOutcome { goals, progressed })
}
fn clone_goal_owned(
    goal: &Goal,
    owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
) -> Result<Goal, TacticFailure> {
    let mut formulas = Vec::new();
    reserve_owned(&mut formulas, goal.formulas.len(), owner)?;
    if let Some(owner) = owner {
        owner
            .admit(goal.formulas.len(), 0)
            .map_err(|_| TacticFailure::new("tactic goal copy stopped"))?;
    }
    formulas.extend_from_slice(&goal.formulas);
    Ok(Goal {
        formulas,
        depth: goal.depth,
        model_converter: goal.model_converter.clone(),
    })
}
fn append_goals_owned(
    target: &mut Vec<Goal>,
    source: Vec<Goal>,
    owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
) -> Result<(), TacticFailure> {
    reserve_owned(target, source.len(), owner)?;
    target.extend(source);
    Ok(())
}

fn flatten_owned(
    terms: &TermStore,
    roots: &[TermId],
    owner: &dyn ay_core::term::TermConstructionAdmission,
) -> Result<Vec<TermId>, TacticFailure> {
    let mut seen = Vec::new();
    reserve_owned(&mut seen, terms.len(), Some(owner))?;
    seen.resize(terms.len(), false);
    let mut pending = Vec::new();
    reserve_owned(&mut pending, roots.len(), Some(owner))?;
    pending.extend(roots.iter().rev().copied());
    let mut result = Vec::new();
    while let Some(id) = pending.pop() {
        owner
            .admit(1, 0)
            .map_err(|_| TacticFailure::new("tactic flatten stopped"))?;
        if id.index() >= terms.len() || terms.sort(id) != &Sort::Bool {
            return Err(TacticFailure::new("invalid Boolean goal"));
        }
        if seen[id.index()] {
            continue;
        }
        seen[id.index()] = true;
        if let TermData::App(ay_core::Symbol::Named(name), _) = terms.get(id) {
            owner
                .admit(name.len(), 0)
                .map_err(|_| TacticFailure::new("tactic flatten stopped"))?;
        }
        match terms.get(id) {
            TermData::App(ay_core::Symbol::Named(name), args)
                if name == "and" && !terms.is_declared_function(name) =>
            {
                reserve_owned(&mut pending, args.len(), Some(owner))?;
                for &child in args.iter().rev() {
                    if child.index() >= id.index() {
                        return Err(TacticFailure::new("invalid goal edge"));
                    }
                    pending.push(child);
                }
            }
            TermData::Const(ay_core::Constant::Bool(true)) => {}
            TermData::Const(ay_core::Constant::Bool(false)) => {
                result.clear();
                reserve_owned(&mut result, 1, Some(owner))?;
                result.push(id);
                return Ok(result);
            }
            _ => {
                reserve_owned(&mut result, 1, Some(owner))?;
                result.push(id);
            }
        }
    }
    Ok(result)
}

/// A goal-to-goal transformation.
///
/// A tactic transforms a goal (a set of assertions) into one or more subgoals
/// whose disjunction has exactly the input's models, then the result is solved
/// or printed.
///
/// ```
/// use ay_dpll::api::Tactic;
///
/// let t = Tactic::flatten_and()
///     .then(Tactic::flatten_and())
///     .or_else(Tactic::flatten_and());
/// assert_eq!(t.name(), "(or-else (then flatten-and flatten-and) flatten-and)");
/// ```
#[derive(Debug, Clone)]
pub enum Tactic {
    /// Shared immutable expression with the existing C tactic's settings.
    Shared(std::sync::Arc<super::tactic_parameters::TacticInstance>),
    /// Existing try-for API: an additional deadline, never a renewed owner.
    TryFor(Box<Tactic>, u32),
    /// Typed, validated existing simplifier parameters.
    WithParams(Box<Tactic>, super::tactic_parameters::TacticParameters),
    /// The native simplifier, distinct from the standalone flatten-and pass.
    Simplify,
    /// Exact modular BV encoding with a typed finite-field model converter.
    FieldToBv,
    /// Modular field constant propagation/ring reduction, retaining defining
    /// equations and original free variables (identity model converter).
    FieldSimplify,
    /// Owned affine functional-dependency propagation; stalling keeps roots.
    FieldUnique,
    /// Owned field conjunction decision with independent model/theorem replay.
    FieldSolve,
    /// Owned lazy Boolean SAT/field algebra with native resolution checking.
    FieldSat,
    /// The identity tactic (`skip`): one subgoal, unchanged, depth unchanged.
    Skip,
    /// The always-failing tactic (`fail`): yields an honest failure, no goal.
    Fail,
    /// Flatten nested `and` into individual conjuncts (Z3's `simplify` /
    /// `elim-and`): `(and (and a b) c)` becomes `{a, b, c}`.
    FlattenAnd,
    /// Solve variable equalities and eliminate the solved variables (Z3's
    /// `solve-eqs`). Top-level conjunctions are flattened first so a nested
    /// equality is visible; the whole thing is ONE depth increment.
    SolveEqs,
    /// Propagate asserted values through the goal (Z3's `propagate-values`):
    /// harvest `(= expr const)` equalities and asserted Boolean literals from
    /// the top-level conjuncts (forward and backward sweeps), substitute them
    /// into the OTHER conjuncts, drop conjuncts that fold to `true`, and
    /// collapse a conflicting goal to `{false}`. Equivalence-preserving.
    /// Flattens top-level conjunctions before and after; one depth increment.
    PropagateValues,
    /// Bound subsumption over top-level inequalities (Z3's `propagate-ineqs`):
    /// drop an inequality implied by a RETAINED same-variable/same-direction
    /// bound of the SAME strictness or by an asserted `(= var const)` value
    /// equality, and re-emit the value equalities at the END of the goal.
    /// Only drops implied conjuncts and reorders — equivalence-preserving;
    /// anything unrecognized is retained verbatim in place. One depth
    /// increment.
    PropagateIneqs,
    /// Eliminate in-fragment existential LIA quantifiers via Cooper's algorithm
    /// (Z3's `qe-light`). Flattens top-level conjunctions first; one depth
    /// increment.
    QeLight,
    /// Rewrite the goal into negation normal form (Z3's `nnf`): push negations
    /// to atoms and eliminate `=>`/`<->`/`xor`/`ite`-over-Bool into `and`/`or`.
    /// Flattens the resulting top-level conjunctions (so a `(and …)` prints as
    /// separate goal formulas, like Z3); one depth increment. NNF is
    /// equivalence-preserving (stronger than equisatisfiable).
    Nnf,
    /// Convert the goal to CNF via Tseitin encoding (Z3's `tseitin-cnf` /
    /// `cnf`). Introduces fresh auxiliary Boolean definition variables, so the
    /// result is **equisatisfiable** (NOT equivalent) to the input: with the aux
    /// variables treated as free, `check-sat(result) == check-sat(input)`. One
    /// depth increment.
    TseitinCnf,
    /// Bit-blast a QF_BV goal to a pure-Boolean goal (Z3's `bit-blast`): each
    /// `n`-bit BV variable becomes `n` fresh Boolean bits and each BV operator
    /// becomes its Boolean circuit. Equisatisfiable. On a goal that contains a
    /// bit-vector construct outside the supported fragment (bvudiv/bvurem/…, a UF
    /// or array over BV, bv2nat/int2bv, …) it HONESTLY FAILS with a
    /// [`TacticFailure`] — never a fabricated or silent-identity blast.
    BitBlast,
    /// Split the first top-level disjunction `(or c1 … cn)` into `n` subgoals,
    /// one per disjunct (Z3's `split-clause`). Fails if the goal contains no
    /// clause. The disjunction of the subgoals is equivalent to the input.
    SplitClause,
    /// Contextual simplification USING THE SOLVER (Z3's `ctx-solver-simplify`).
    ///
    /// Walks the goal's top-level assertions and, for each assertion `A_i`, uses
    /// a nested solver to check whether the CONTEXT — the conjunction of the
    /// OTHER assertions — proves `A_i` redundant or contradicted:
    ///
    /// - if `context ⇒ A_i` (i.e. `context ∧ ¬A_i` is UNSAT), `A_i` is dropped;
    /// - if `context ⇒ ¬A_i` (i.e. `context ∧ A_i` is UNSAT), the whole goal is
    ///   unsatisfiable and collapses to the single literal `false`;
    /// - otherwise (SAT **or** unknown) `A_i` is kept **verbatim** — a sub-check
    ///   that returns unknown NEVER triggers a simplification.
    ///
    /// SOUNDNESS: the result is EQUIVALENT to the input (every model preserved).
    /// The context used to drop `A_i` is `(kept earlier assertions) ∧ (original
    /// later assertions)`; a dropped assertion is therefore implied by the final
    /// kept set (proof by reverse induction over the assertion order), and the
    /// `false` collapse only fires when a subset of the ORIGINAL assertions is
    /// itself UNSAT. Every drop/collapse is on a PROVEN implication, so no needed
    /// constraint is ever lost and no goal is wrongly declared unsat. On a goal
    /// with quantifiers or a non-arithmetic/BV theory (UF/array/string/FP/…) it
    /// is the identity (a sound no-op).
    CtxSolverSimplify,
    /// Apply the first tactic, then apply the second to EACH resulting subgoal.
    Then(Box<Tactic>, Box<Tactic>),
    /// Apply the first tactic; if it *fails*, apply the second instead (on the
    /// original goal). Z3's `or-else` falls through on failure, not on a mere
    /// lack of progress.
    OrElse(Box<Tactic>, Box<Tactic>),
    /// Apply the body repeatedly to fixpoint, or at most `bound` iterations when
    /// a bound is given (Z3's `repeat`).
    Repeat(Box<Tactic>, Option<usize>),
    /// Apply the body iff the probe holds on the goal, else `skip` (Z3's `when`).
    When(Probe, Box<Tactic>),
    /// Fail iff the probe holds on the goal, else `skip` (Z3's `fail-if`).
    FailIf(Probe),
    /// Apply the first body iff the probe holds on the goal, else apply the
    /// second body (Z3's `cond`). Unlike `(or-else (when p t1) t2)`, a FAILURE of
    /// the chosen branch propagates — it never silently falls through to the
    /// other branch (matching Z3, where `cond(p, fail, skip)` on a goal where `p`
    /// holds genuinely fails rather than running `skip`).
    Cond(Probe, Box<Tactic>, Box<Tactic>),
    /// Fail unless the goal is *trivially decided* — either empty (⇒ decided
    /// SAT) or containing the literal `false` (⇒ decided UNSAT) — Z3's
    /// `fail-if-not-decided`. On a decided goal it is the identity (`skip`); on
    /// any other goal it HONESTLY FAILS, producing no goal.
    FailIfNotDecided,
    /// Name every non-Boolean term-level `ite` with a fresh definition variable
    /// (Z3's `elim-term-ite`): replace `(ite c t e)` by a fresh `k` and append
    /// the guard definitions `(or (not c) (= k t))`, `(or c (= k e))`. Introduces
    /// fresh variables, so the result is **equisatisfiable** (NOT equivalent) —
    /// with the fresh variables treated as free, `check-sat(result) ==
    /// check-sat(input)`. `ite`s under a quantifier are left in place (a
    /// documented sound divergence: z3 names them outside the binder). One depth
    /// increment.
    ElimTermIte,
    /// Lift every non-Boolean term-level `ite` out over its enclosing
    /// predicate/function by Shannon expansion (Z3's `blast-term-ite`, and AY's
    /// realization of `cofactor-term-ite`): `(<= (ite c x y) 5)` →
    /// `(ite c (<= x 5) (<= y 5))`. Equivalence-preserving. On a budget-exhausted
    /// DAG the partial lift is still equivalence-preserving. `ite`s under a
    /// quantifier are left in place (sound divergence: z3 descends). One depth
    /// increment.
    BlastTermIte,
    /// Destructive equality resolution (Z3's `der`): resolve `(not (= x t))`
    /// literals out of universally quantified clauses by the one-point rule.
    /// Equivalence-preserving; fail-closes on nested binders to stay
    /// capture-safe. One depth increment.
    Der,
    /// Distribute `forall` over `and` (and `¬exists` over `or`) — Z3's
    /// `distribute-forall`: one goal formula per conjunct/disjunct.
    /// Equivalence-preserving. One depth increment.
    DistributeForall,
    /// Eliminate always-constant function arguments (Z3's `reduce-args`),
    /// specializing each function per constant tuple into fresh `f!k` symbols.
    /// Introduces fresh symbols, so the result is **equisatisfiable** (NOT
    /// equivalent). One depth increment.
    ReduceArgs,
    /// Share common binary circuits in BV addition, multiplication, AND and OR.
    MaxBvSharing,
    /// A CLASS F fragment tactic (`diff-neq`, `nlqsat`, `pb2bv`, `horn`,
    /// `horn-simplify`): every application is an HONEST failure carrying
    /// `message` — it produces NO goal, never a fabricated transform. z3
    /// likewise fails these tactics on generic goals (measured), so `or-else`
    /// routing matches z3: `(or-else diff-neq simplify)` takes the fallback on
    /// both solvers. On an in-fragment goal z3 succeeds where AY honestly
    /// fails — sound (a failure can never mint a verdict), catchable by
    /// `or-else`, and documented per name in `Z3_tactic_get_descr`.
    FailMsg {
        /// The z3 tactic name (diagnostics, `Tactic::name`).
        name: &'static str,
        /// The `tactic failed: …` message body (z3 byte text where fixed).
        message: &'static str,
    },
    /// z3's `bv1-blast`, realized honestly from its MEASURED behavior
    /// (z3 4.15.4): on a goal containing ANY bit-vector term it fails with
    /// `bv1 blaster cannot be applied to goal` (z3 byte text); on a BV-free
    /// goal it succeeds as the identity (one depth increment, like z3's no-op
    /// pass). On a pure bv1 goal z3 transforms where AY honestly fails — a
    /// documented sound divergence (never a fabricated blast).
    Bv1Blast,
}

/// Execution metadata, not a resource grant or a claim of tactic completeness.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TacticExecutionKind {
    /// Legacy execution that does not retain typed reconstruction authority.
    Legacy,
    /// Execution retaining typed equivalence reconstruction.
    OwnedEquivalence,
    /// Execution retaining typed model-conversion reconstruction.
    OwnedModelConversion,
}
struct Requirements {
    kind: TacticExecutionKind,
    solver: bool,
    simplifier: bool,
    proof_transport: bool,
}

impl Tactic {
    /// Shared sequence rewriter for an existing explicit simplify request.
    /// The caller retains the same source/construction and output fences.
    pub(crate) fn simplify_sequence_term(
        terms: &mut TermStore,
        source: TermId,
        maximum: u32,
        polynomial: super::PolynomialParameters,
        limits: super::TacticParameters,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<TermId, TacticFailure> {
        let restricted = super::tactic_parameters::Restricted::new(owner, None, limits.max_memory)?;
        let result = (|| {
            let mut steps = super::tactic_parameters::Steps::new(limits.max_steps);
            let roots = super::tactic_polynomial::rewrite_with_sequences(
                terms,
                &[source],
                maximum,
                polynomial,
                &mut steps,
                &restricted,
            )?;
            let roots = if limits.elim_and == Some(true) {
                super::tactic_bool_rewrite::rewrite(
                    terms,
                    &roots,
                    super::tactic_bool_rewrite::ConjunctionMode::Eliminate,
                    &mut steps,
                    &restricted,
                )?
            } else {
                roots
            };
            let source = roots
                .first()
                .copied()
                .ok_or_else(|| TacticFailure::new("simplifier produced no term"))?;
            // Ring/sequence normalization can create closed conditionals and
            // comparisons after frontend elaboration. Finish through the same
            // paid scalar worker as the direct API, retaining this request's
            // Steps, deadline, arena and namespace checks.
            super::tactic_propagate_values::simplify_term(
                terms,
                source,
                super::tactic_bool_rewrite::ConjunctionMode::Retain,
                &mut steps,
                &restricted,
            )
        })();
        restricted.settle(result)
    }

    /// Whether this tactic needs the caller's original construction owner.
    pub fn requires_construction_admission(&self) -> bool {
        self.requirements(None)
            .map_or(true, |r| r.kind != TacticExecutionKind::Legacy)
    }

    /// Whether formulas alone are insufficient to reconstruct original models.
    pub fn requires_model_conversion(&self) -> bool {
        self.requirements(None).map_or(true, |r| {
            r.kind == TacticExecutionKind::OwnedModelConversion
        })
    }

    /// Inspect the actual tactic tree under the adapter's retained owner,
    /// including traversal storage. A refusal must never select a fallback.
    pub fn execution_kind_admitted(
        &self,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<TacticExecutionKind, TacticFailure> {
        self.requirements(Some(owner)).map(|r| r.kind)
    }

    pub(crate) fn execution_metadata_admitted(
        &self,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<(TacticExecutionKind, bool), TacticFailure> {
        self.requirements(Some(owner))
            .map(|required| (required.kind, required.solver))
    }

    /// Whether this tree contains a transformation whose proof/core transport
    /// is unavailable. This is inspected under the SAME original owner.
    pub fn unsupported_goal_proof_transport_admitted(
        &self,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<bool, TacticFailure> {
        self.requirements(Some(owner)).map(|r| r.proof_transport)
    }

    fn requirements(
        &self,
        owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
    ) -> Result<Requirements, TacticFailure> {
        let mut pending = Vec::new();
        reserve_owned(&mut pending, 1, owner)?;
        pending.push(self);
        let mut result = Requirements {
            kind: TacticExecutionKind::Legacy,
            solver: false,
            simplifier: false,
            proof_transport: false,
        };
        while let Some(tactic) = pending.pop() {
            if let Some(owner) = owner {
                owner
                    .admit(1, 0)
                    .map_err(|_| TacticFailure::new("tactic metadata inspection stopped"))?;
            }
            match tactic {
                Self::Shared(instance) => {
                    reserve_owned(&mut pending, 1, owner)?;
                    pending.push(&instance.body);
                }
                Self::TryFor(body, _) | Self::WithParams(body, _) => {
                    if result.kind == TacticExecutionKind::Legacy {
                        result.kind = TacticExecutionKind::OwnedEquivalence;
                    }
                    reserve_owned(&mut pending, 1, owner)?;
                    pending.push(body);
                }
                Self::Simplify => {
                    result.simplifier = true;
                    // Ring normalization is equivalent, but this path does
                    // not yet produce an independently replayable proof/core
                    // converter. Never publish an identity certificate.
                    result.proof_transport = true;
                    if result.kind == TacticExecutionKind::Legacy {
                        result.kind = TacticExecutionKind::OwnedEquivalence;
                    }
                }
                Self::FieldToBv => result.kind = TacticExecutionKind::OwnedModelConversion,
                Self::SolveEqs => {
                    result.kind = TacticExecutionKind::OwnedModelConversion;
                    result.proof_transport = true;
                }
                Self::PropagateValues => {
                    if result.kind == TacticExecutionKind::Legacy {
                        result.kind = TacticExecutionKind::OwnedEquivalence;
                    }
                    result.proof_transport = true;
                }
                Self::FieldSolve | Self::FieldSat => {
                    result.kind = TacticExecutionKind::OwnedModelConversion;
                    result.proof_transport = true;
                }
                Self::FieldUnique => {
                    result.proof_transport = true;
                    if result.kind == TacticExecutionKind::Legacy {
                        result.kind = TacticExecutionKind::OwnedEquivalence;
                    }
                }
                Self::FieldSimplify if result.kind == TacticExecutionKind::Legacy => {
                    result.kind = TacticExecutionKind::OwnedEquivalence
                }
                Self::CtxSolverSimplify => result.solver = true,
                Self::Then(a, b) | Self::OrElse(a, b) | Self::Cond(_, a, b) => {
                    reserve_owned(&mut pending, 2, owner)?;
                    pending.push(a.as_ref());
                    pending.push(b.as_ref());
                }
                Self::Repeat(a, _) | Self::When(_, a) => {
                    reserve_owned(&mut pending, 1, owner)?;
                    pending.push(a.as_ref());
                }
                _ => {}
            }
        }
        if let Some(owner) = owner {
            owner
                .check()
                .map_err(|_| TacticFailure::new("tactic metadata inspection stopped"))?;
        }
        Ok(result)
    }

    pub(crate) fn apply_goals_admitted(
        &self,
        terms: &mut TermStore,
        goal: Goal,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> ApplyResult {
        self.apply_step_admitted(terms, goal, Some(owner))
            .map(|out| out.goals)
    }

    fn apply_or_fail_admitted(
        &self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<bool, TacticFailure> {
        if self.requirements(Some(owner))?.kind == TacticExecutionKind::OwnedModelConversion {
            return Err(TacticFailure::new(
                "in-place tactic API cannot discard a model converter",
            ));
        }
        owner
            .admit(
                assertions.len(),
                assertions
                    .len()
                    .checked_mul(size_of::<TermId>())
                    .ok_or_else(|| TacticFailure::new("tactic root size overflow"))?,
            )
            .map_err(|_| TacticFailure::new("tactic original root admission refused"))?;
        let out = self.apply_step_admitted(terms, Goal::root(assertions.clone()), Some(owner))?;
        if out.goals.len() == 1 && out.progressed {
            let mut goals = out.goals.into_iter();
            if let Some(goal) = goals.next() {
                *assertions = goal.formulas;
            }
            Ok(true)
        } else {
            Ok(false)
        }
    }
    /// The `flatten-and` tactic.
    #[must_use]
    pub fn flatten_and() -> Self {
        Tactic::FlattenAnd
    }

    /// The `qe-light` tactic.
    #[must_use]
    pub fn qe_light() -> Self {
        Tactic::QeLight
    }

    /// The `tseitin-cnf` tactic (equisatisfiable CNF conversion).
    #[must_use]
    pub fn tseitin_cnf() -> Self {
        Tactic::TseitinCnf
    }

    /// Whether this descriptor union contains the implemented simplifier.
    pub fn has_simplifier_parameters(
        &self,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<bool, TacticFailure> {
        self.requirements(Some(owner)).map(|r| r.simplifier)
    }

    /// Validate the supported descriptor union before changing configuration.
    pub fn validate_parameters(
        &self,
        params: super::tactic_parameters::TacticParameters,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<(), TacticFailure> {
        let required = self.requirements(Some(owner))?;
        if !params.is_empty() && !required.simplifier {
            return Err(TacticFailure::new(
                "these parameters are unsupported by this tactic",
            ));
        }
        owner
            .check()
            .map_err(|_| TacticFailure::new("original parameter owner stopped"))
    }

    /// Apply a validated update to actual shared tactic identities. Collect the
    /// complete paid plan before changing any setting; no lock spans callbacks.
    /// Stored using-params options override later updates, as upstream append.
    pub fn update_parameters(
        &self,
        params: super::tactic_parameters::TacticParameters,
        owner: &dyn ay_core::term::TermConstructionAdmission,
    ) -> Result<(), TacticFailure> {
        self.validate_parameters(params, owner)?;
        let mut pending = Vec::new();
        reserve_owned(&mut pending, 1, Some(owner))?;
        pending.push((self, params));
        let mut updates: Vec<(
            &super::tactic_parameters::TacticInstance,
            super::tactic_parameters::TacticParameters,
        )> = Vec::new();
        while let Some((node, incoming)) = pending.pop() {
            owner
                .admit(1, 0)
                .map_err(|_| TacticFailure::new("original parameter owner stopped"))?;
            match node {
                Self::Shared(instance) => {
                    owner
                        .admit(updates.len(), 0)
                        .map_err(|_| TacticFailure::new("original parameter owner stopped"))?;
                    if let Some((_, configured)) = updates
                        .iter_mut()
                        .find(|(entry, _)| std::ptr::eq(*entry, instance.as_ref()))
                    {
                        *configured = incoming.over(*configured);
                    } else {
                        let configured = incoming.over(instance.configured()?);
                        reserve_owned(&mut updates, 1, Some(owner))?;
                        updates.push((instance.as_ref(), configured));
                    }
                    reserve_owned(&mut pending, 1, Some(owner))?;
                    pending.push((&instance.body, incoming));
                }
                Self::WithParams(body, stored) => {
                    reserve_owned(&mut pending, 1, Some(owner))?;
                    pending.push((body, stored.over(incoming)));
                }
                Self::Then(a, b) | Self::OrElse(a, b) | Self::Cond(_, a, b) => {
                    reserve_owned(&mut pending, 2, Some(owner))?;
                    pending.push((b, incoming));
                    pending.push((a, incoming));
                }
                Self::TryFor(body, _) | Self::Repeat(body, _) | Self::When(_, body) => {
                    reserve_owned(&mut pending, 1, Some(owner))?;
                    pending.push((body, incoming));
                }
                _ => {}
            }
        }
        owner
            .check()
            .map_err(|_| TacticFailure::new("original parameter owner stopped"))?;
        // Existing C contexts are single-threaded/non-aliased. These fixed
        // scalar commits invoke no callbacks or allocations.
        for (instance, configured) in updates {
            instance.install(configured)?;
        }
        Ok(())
    }

    /// Translate a front-end [`ApplyTactic`](ay_frontend::ApplyTactic) — the
    /// shared tactic registry — into an executable [`Tactic`].
    ///
    /// This is THE single name→transform mapping used by BOTH Z3-compatible
    /// tactic surfaces (the SMT-LIB `(apply <name>)` executor and the C-API
    /// `Z3_mk_tactic('<name>')` path), so they cannot drift.
    ///
    /// Each primitive is ONE depth-incrementing step. `solve-eqs`,
    /// `propagate-values` and `qe-light`/`qe` flatten top-level conjunctions
    /// internally (so a nested equality/quantifier is visible) but still count as
    /// a single primitive — matching Z3, where `(apply solve-eqs)` is depth 1.
    /// The parallel combinators `par-then`/`par-or` compose sequentially (same
    /// result set); `try-for`/`using-params`/`with` reduce to the wrapped tactic
    /// because AY always applies the equivalence-preserving transform (params and
    /// wall-clock bounds do not change the model set).
    #[must_use]
    pub fn from_apply(tactic: &ay_frontend::ApplyTactic) -> Tactic {
        use ay_frontend::ApplyTactic;
        match tactic {
            ApplyTactic::Skip => Tactic::Skip,
            ApplyTactic::Fail => Tactic::Fail,
            ApplyTactic::Simplify => Tactic::Simplify,
            ApplyTactic::ElimAnd => Tactic::FlattenAnd,
            ApplyTactic::SolveEqs => Tactic::SolveEqs,
            ApplyTactic::PropagateValues => Tactic::PropagateValues,
            ApplyTactic::PropagateIneqs => Tactic::PropagateIneqs,
            // `qe` shares `qe-light`'s Cooper engine arm (the alias pattern
            // `simplify`/`elim-and` → `FlattenAnd` already sets): in-fragment
            // single-Int-var existentials are eliminated, out-of-fragment
            // quantifiers kept verbatim — a documented sound divergence from
            // z3's LIA-complete `qe`.
            ApplyTactic::QeLight | ApplyTactic::Qe => Tactic::QeLight,
            ApplyTactic::Nnf => Tactic::Nnf,
            ApplyTactic::TseitinCnf => Tactic::TseitinCnf,
            ApplyTactic::BitBlast => Tactic::BitBlast,
            ApplyTactic::FieldSimplify => Tactic::FieldSimplify,
            ApplyTactic::FieldUnique => Tactic::FieldUnique,
            ApplyTactic::FieldSolve => Tactic::FieldSolve,
            ApplyTactic::FieldSat => Tactic::FieldSat,
            ApplyTactic::FieldToBv => Tactic::FieldToBv,
            ApplyTactic::SplitClause => Tactic::SplitClause,
            ApplyTactic::CtxSolverSimplify => Tactic::CtxSolverSimplify,
            ApplyTactic::ElimTermIte => Tactic::ElimTermIte,
            ApplyTactic::BlastTermIte => Tactic::BlastTermIte,
            ApplyTactic::Der => Tactic::Der,
            ApplyTactic::DistributeForall => Tactic::DistributeForall,
            ApplyTactic::ReduceArgs => Tactic::ReduceArgs,
            ApplyTactic::MaxBvSharing => Tactic::MaxBvSharing,
            ApplyTactic::Then(children) | ApplyTactic::ParThen(children) => {
                Self::fold_children(children, Tactic::then)
            }
            ApplyTactic::OrElse(children) | ApplyTactic::ParOr(children) => {
                Self::fold_children(children, Tactic::or_else)
            }
            ApplyTactic::Repeat(body, bound) => {
                Tactic::Repeat(Box::new(Tactic::from_apply(body)), *bound)
            }
            ApplyTactic::TryFor(body, ms) => match u32::try_from(*ms) {
                Ok(ms) => Tactic::TryFor(Box::new(Tactic::from_apply(body)), ms),
                Err(_) => Tactic::FailMsg {
                    name: "try-for",
                    message: "tactic timeout exceeds uint32",
                },
            },
            ApplyTactic::UsingParams(body, params) => {
                let mut configured = super::tactic_parameters::TacticParameters::default();
                for (key, value) in params {
                    use super::tactic_parameters::TacticParameterValue as V;
                    use ay_frontend::ParamValue;
                    let typed = match value {
                        ParamValue::Bool(b) => V::Bool(*b),
                        ParamValue::Int(n) => {
                            u32::try_from(*n).map(V::UInt).unwrap_or(V::Unsupported)
                        }
                        _ => V::Unsupported,
                    };
                    if configured.set(key, typed).is_err() {
                        return Tactic::FailMsg {
                            name: "using-params",
                            message: "unsupported tactic parameter name or type",
                        };
                    }
                }
                Tactic::WithParams(Box::new(Tactic::from_apply(body)), configured)
            }
            ApplyTactic::When(probe, body) => {
                Tactic::When(probe.clone(), Box::new(Tactic::from_apply(body)))
            }
            ApplyTactic::FailIf(probe) => Tactic::FailIf(probe.clone()),
            ApplyTactic::Cond(probe, t1, t2) => Tactic::Cond(
                probe.clone(),
                Box::new(Tactic::from_apply(t1)),
                Box::new(Tactic::from_apply(t2)),
            ),
            ApplyTactic::Unsupported { name, message } => Tactic::FailMsg { name, message },
            ApplyTactic::Bv1Blast => Tactic::Bv1Blast,
            ApplyTactic::FailIfUndecided => Tactic::FailIfNotDecided,
            // NO wildcard arm — deliberately. `ApplyTactic` is exhaustive (not
            // `#[non_exhaustive]`), so a future variant without an explicit
            // mapping is a COMPILE ERROR here. A silent `_ => Tactic::Skip`
            // fallback would convert an honest-failure tactic into a silent
            // identity success, defeating the `or-else` routing the failure
            // classes exist for — with no test failure to catch it.
        }
    }

    /// Fold a non-empty child list left with `combine` (`then`/`or_else`).
    fn fold_children(
        children: &[ay_frontend::ApplyTactic],
        combine: impl Fn(Tactic, Tactic) -> Tactic,
    ) -> Tactic {
        let mut it = children.iter().map(Tactic::from_apply);
        let first = it.next().unwrap_or(Tactic::Skip);
        it.fold(first, combine)
    }

    /// Sequential composition: apply `self`, then `next` on each subgoal.
    #[must_use]
    pub fn then(self, next: Tactic) -> Self {
        Tactic::Then(Box::new(self), Box::new(next))
    }

    /// Alternative composition: apply `self`; if it *fails*, apply `alt` on the
    /// original goal instead.
    #[must_use]
    pub fn or_else(self, alt: Tactic) -> Self {
        Tactic::OrElse(Box::new(self), Box::new(alt))
    }

    /// Repeat this tactic to fixpoint (Z3's `repeat`).
    #[must_use]
    pub fn repeat(self) -> Self {
        Tactic::Repeat(Box::new(self), None)
    }

    /// Repeat this tactic at most `bound` times (Z3's `(repeat t n)`).
    #[must_use]
    pub fn repeat_up_to(self, bound: usize) -> Self {
        Tactic::Repeat(Box::new(self), Some(bound))
    }

    /// Build Z3's `cond(p, t1, t2)`: apply `t1` if `probe` holds on the goal,
    /// else apply `t2`. A failure of the chosen branch propagates (it does not
    /// fall through to the other branch).
    #[must_use]
    pub fn cond(probe: Probe, t1: Tactic, t2: Tactic) -> Self {
        Tactic::Cond(probe, Box::new(t1), Box::new(t2))
    }

    /// Build Z3's `fail-if-not-decided`: the identity on a trivially-decided goal
    /// (empty, or containing `false`), an honest failure on any other goal.
    #[must_use]
    pub fn fail_if_not_decided() -> Self {
        Tactic::FailIfNotDecided
    }

    /// A stable, Z3-style name for this tactic (diagnostics/tests).
    #[must_use]
    pub fn name(&self) -> String {
        match self {
            Tactic::Skip => "skip".to_string(),
            Tactic::Fail => "fail".to_string(),
            Tactic::Shared(instance) => instance.body.name(),
            Tactic::TryFor(body, ms) => format!("(try-for {} {ms})", body.name()),
            Tactic::WithParams(body, _) => format!("(using-params {})", body.name()),
            Tactic::Simplify => "simplify".to_string(),
            Tactic::FlattenAnd => "flatten-and".to_string(),
            Tactic::SolveEqs => "solve-eqs".to_string(),
            Tactic::PropagateValues => "propagate-values".to_string(),
            Tactic::PropagateIneqs => "propagate-ineqs".to_string(),
            Tactic::QeLight => "qe-light".to_string(),
            Tactic::Nnf => "nnf".to_string(),
            Tactic::TseitinCnf => "tseitin-cnf".to_string(),
            Tactic::BitBlast => "bit-blast".to_string(),
            Tactic::FieldSimplify => "ff-simplify".to_string(),
            Tactic::FieldUnique => "ff-unique".to_string(),
            Tactic::FieldSolve => "ff-solve".to_string(),
            Tactic::FieldSat => "ff-sat".to_string(),
            Tactic::FieldToBv => "ff2bv".to_string(),
            Tactic::SplitClause => "split-clause".to_string(),
            Tactic::CtxSolverSimplify => "ctx-solver-simplify".to_string(),
            Tactic::Then(a, b) => format!("(then {} {})", a.name(), b.name()),
            Tactic::OrElse(a, b) => format!("(or-else {} {})", a.name(), b.name()),
            Tactic::Repeat(a, None) => format!("(repeat {})", a.name()),
            Tactic::Repeat(a, Some(n)) => format!("(repeat {} {n})", a.name()),
            Tactic::When(_, a) => format!("(when <probe> {})", a.name()),
            Tactic::FailIf(_) => "(fail-if <probe>)".to_string(),
            Tactic::Cond(_, a, b) => format!("(cond <probe> {} {})", a.name(), b.name()),
            Tactic::FailIfNotDecided => "fail-if-not-decided".to_string(),
            Tactic::ElimTermIte => "elim-term-ite".to_string(),
            Tactic::BlastTermIte => "blast-term-ite".to_string(),
            Tactic::Der => "der".to_string(),
            Tactic::DistributeForall => "distribute-forall".to_string(),
            Tactic::ReduceArgs => "reduce-args".to_string(),
            Tactic::MaxBvSharing => "max-bv-sharing".to_string(),
            Tactic::FailMsg { name, .. } => (*name).to_string(),
            Tactic::Bv1Blast => "bv1-blast".to_string(),
        }
    }

    /// Apply this tactic to a root goal (`formulas`, depth 0), producing the
    /// subgoals (each carrying its own depth) or an honest failure.
    ///
    /// This is the multi-subgoal engine entry point used by the `(apply …)`
    /// print surface. The disjunction of the returned goals is equisatisfiable
    /// to `formulas`.
    pub(crate) fn apply_goals(&self, terms: &mut TermStore, goal: Goal) -> ApplyResult {
        self.apply_step(terms, goal).map(|o| o.goals)
    }

    /// The recursive worker: apply to one goal, returning the subgoals and a
    /// progress flag.
    fn apply_step(&self, terms: &mut TermStore, goal: Goal) -> Result<StepOutcome, TacticFailure> {
        self.apply_step_admitted(terms, goal, None)
    }

    fn apply_step_admitted(
        &self,
        terms: &mut TermStore,
        goal: Goal,
        owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
    ) -> Result<StepOutcome, TacticFailure> {
        if let Some(owner) = owner {
            return ay_core::render_admission::stacked(
                Some(owner),
                || {
                    Err(TacticFailure::new(
                        "tactic original stack admission refused",
                    ))
                },
                || self.apply_step_owned_body(terms, goal, Some(owner)),
            );
        }
        self.apply_step_owned_body(terms, goal, None)
    }

    fn apply_step_owned_body(
        &self,
        terms: &mut TermStore,
        goal: Goal,
        owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
    ) -> Result<StepOutcome, TacticFailure> {
        use super::tactic_parameters as configured;
        match self {
            Self::Shared(instance) => {
                let _settings = configured::install(instance.configured()?);
                return instance.body.apply_step_admitted(terms, goal, owner);
            }
            Self::WithParams(body, params) => {
                let owner = owner.ok_or_else(|| {
                    TacticFailure::new("parameterized tactic requires original admission")
                })?;
                body.validate_parameters(*params, owner)?;
                let _settings = configured::install(*params);
                return body.apply_step_admitted(terms, goal, Some(owner));
            }
            Self::TryFor(body, ms) => {
                let owner = owner
                    .ok_or_else(|| TacticFailure::new("try-for requires original admission"))?;
                let duration = (*ms != 0 && *ms != u32::MAX)
                    .then(|| std::time::Duration::from_millis(u64::from(*ms)));
                let _deadline = tactic_deadline::install(duration);
                let restricted = configured::Restricted::new(owner, tactic_deadline::end(), None)?;
                let result = body.apply_step_admitted(terms, goal, Some(&restricted));
                return restricted.settle(result);
            }
            Self::Simplify => {
                let owner = owner
                    .ok_or_else(|| TacticFailure::new("simplify requires original admission"))?;
                let params = configured::current();
                let restricted = configured::Restricted::new(owner, None, params.max_memory)?;
                let result = (|| -> Result<StepOutcome, TacticFailure> {
                    let mut steps = configured::Steps::new(params.max_steps);
                    let sequence_roots = super::tactic_polynomial::rewrite_with_sequences(
                        terms,
                        &goal.formulas,
                        params.max_power_expansion.unwrap_or(2),
                        params.polynomial,
                        &mut steps,
                        &restricted,
                    )?;
                    let formulas = if params.elim_and == Some(true)
                        || params.max_steps.is_some_and(|v| v != u32::MAX)
                    {
                        let roots = super::tactic_bool_rewrite::rewrite(
                            terms,
                            &sequence_roots,
                            if params.elim_and == Some(true) {
                                super::tactic_bool_rewrite::ConjunctionMode::Eliminate
                            } else {
                                super::tactic_bool_rewrite::ConjunctionMode::Retain
                            },
                            &mut steps,
                            &restricted,
                        )?;
                        flatten_owned(terms, &roots, &restricted)?
                    } else {
                        flatten_owned(terms, &sequence_roots, &restricted)?
                    };
                    let progressed = formulas != goal.formulas;
                    singleton_outcome(
                        Goal {
                            formulas,
                            depth: goal
                                .depth
                                .checked_add(1)
                                .ok_or_else(|| TacticFailure::new("tactic depth overflow"))?,
                            model_converter: goal.model_converter,
                        },
                        progressed,
                        Some(&restricted),
                    )
                })();
                return restricted.settle(result);
            }
            _ => {}
        }
        if let Some(owner) = owner {
            owner
                .admit(1, 0)
                .map_err(|_| TacticFailure::new("tactic original owner stopped"))?;
            if goal.depth == usize::MAX && !matches!(self, Self::Skip) {
                return Err(TacticFailure::new("tactic depth overflow"));
            }
            if matches!(self, Self::SplitClause) {
                for (position, &root) in goal.formulas.iter().enumerate() {
                    owner
                        .admit(1, 0)
                        .map_err(|_| TacticFailure::new("original split owner stopped"))?;
                    if root.index() >= terms.len() {
                        return Err(TacticFailure::new("invalid split root"));
                    }
                    if let TermData::App(symbol, children) = terms.get(root) {
                        owner
                            .admit(symbol.name().len(), 0)
                            .map_err(|_| TacticFailure::new("original split owner stopped"))?;
                        if symbol.name() == "or"
                            && !terms.is_declared_function(symbol.name())
                            && children.len() >= 2
                        {
                            let mut result = Vec::new();
                            reserve_owned(&mut result, children.len(), Some(owner))?;
                            for &child in children {
                                owner.admit(1, 0).map_err(|_| {
                                    TacticFailure::new("original split owner stopped")
                                })?;
                                if child.index() >= terms.len() || terms.sort(child) != &Sort::Bool
                                {
                                    return Err(TacticFailure::new("invalid split disjunct"));
                                }
                                let mut branch = clone_goal_owned(&goal, Some(owner))?;
                                branch.formulas[position] = child;
                                branch.depth = branch
                                    .depth
                                    .checked_add(1)
                                    .ok_or_else(|| TacticFailure::new("split depth overflow"))?;
                                result.push(branch);
                            }
                            return Ok(StepOutcome {
                                goals: result,
                                progressed: true,
                            });
                        }
                    }
                }
                return logical_failure(
                    Some(owner),
                    "split-clause tactic failed, goal does not contain any clause",
                );
            }
            if matches!(self, Self::FlattenAnd) {
                let formulas = flatten_owned(terms, &goal.formulas, owner)?;
                let progressed = formulas != goal.formulas;
                return singleton_outcome(
                    Goal {
                        formulas,
                        depth: goal.depth + 1,
                        model_converter: goal.model_converter,
                    },
                    progressed,
                    Some(owner),
                );
            }
            if matches!(self, Self::SolveEqs) {
                let formulas = flatten_owned(terms, &goal.formulas, owner)?;
                let eliminated = super::tactic_solve_eqs::eliminate(terms, formulas, owner)?;
                let converter = goal
                    .model_converter
                    .as_ref()
                    .ok_or_else(|| {
                        TacticFailure::new("solve-eqs requires a context-bound model converter")
                    })?
                    .equations(terms, eliminated.definitions, owner)?;
                let progressed = eliminated.roots != goal.formulas;
                let depth = goal
                    .depth
                    .checked_add(1)
                    .ok_or_else(|| TacticFailure::new("solve-eqs depth overflow"))?;
                return singleton_outcome(
                    Goal {
                        formulas: eliminated.roots,
                        depth,
                        model_converter: Some(converter),
                    },
                    progressed,
                    Some(owner),
                );
            }
            if matches!(self, Self::PropagateValues) {
                let formulas = flatten_owned(terms, &goal.formulas, owner)?;
                let formulas = super::tactic_propagate_values::apply(terms, formulas, owner)?;
                let formulas = flatten_owned(terms, &formulas, owner)?;
                let progressed = formulas != goal.formulas;
                let depth = goal
                    .depth
                    .checked_add(1)
                    .ok_or_else(|| TacticFailure::new("propagate-values depth overflow"))?;
                return singleton_outcome(
                    Goal {
                        formulas,
                        depth,
                        model_converter: goal.model_converter,
                    },
                    progressed,
                    Some(owner),
                );
            }
            if !matches!(
                self,
                Self::FieldSimplify
                    | Self::FieldUnique
                    | Self::FieldSolve
                    | Self::FieldSat
                    | Self::FieldToBv
                    | Self::Skip
                    | Self::Fail
                    | Self::FailMsg { .. }
                    | Self::Then(..)
                    | Self::OrElse(..)
                    | Self::Repeat(..)
                    | Self::When(..)
                    | Self::Cond(..)
                    | Self::FailIf(..)
                    | Self::FailIfNotDecided
            ) {
                return logical_failure(Some(owner),"this composite primitive has no original-owner execution/model-conversion path");
            }
        }
        match self {
            Tactic::Shared(..) | Tactic::TryFor(..) | Tactic::WithParams(..) | Tactic::Simplify => {
                Err(TacticFailure::new("tactic control dispatch invariant"))
            }
            Tactic::FieldSolve | Tactic::FieldSat => {
                let owner = owner.ok_or_else(|| {
                    TacticFailure::new("ff-solve requires original construction admission")
                })?;
                let converter = goal.model_converter.as_ref().ok_or_else(|| {
                    TacticFailure::new("ff-solve requires a context-bound model converter")
                })?;
                let (formulas, converter) = if matches!(self, Self::FieldSat) {
                    super::field_sat::apply(terms, &goal.formulas, converter, owner)?
                } else {
                    super::field_solve::apply(terms, &goal.formulas, converter, owner)?
                };
                let progressed = formulas != goal.formulas;
                singleton_outcome(
                    Goal {
                        formulas,
                        depth: goal.depth + 1,
                        model_converter: Some(converter),
                    },
                    progressed,
                    Some(owner),
                )
            }
            Tactic::FieldToBv => {
                let owner = owner.ok_or_else(|| {
                    TacticFailure::new("ff2bv requires original construction admission")
                })?;
                let converter = goal.model_converter.as_ref().ok_or_else(|| {
                    TacticFailure::new("ff2bv requires a context-bound model converter")
                })?;
                if !converter.valid(terms) {
                    return Err(TacticFailure::new("ff2bv source context retired"));
                }
                if converter.is_active() {
                    let mut goal = goal;
                    goal.depth += 1;
                    return singleton_outcome(goal, false, Some(owner));
                }
                let encoded = super::field_to_bv::encode(
                    terms,
                    &goal.formulas,
                    converter.namespace(),
                    owner,
                )?;
                let progressed = encoded.formulas != goal.formulas;
                let converter = converter.encoded(encoded.bindings, owner)?;
                singleton_outcome(
                    Goal {
                        formulas: encoded.formulas,
                        depth: goal.depth + 1,
                        model_converter: Some(converter),
                    },
                    progressed,
                    Some(owner),
                )
            }
            Tactic::FieldSimplify | Tactic::FieldUnique => {
                let owner = owner.ok_or_else(|| {
                    TacticFailure::new("ff-simplify requires original construction admission")
                })?;
                let formulas = if matches!(self, Self::FieldUnique) {
                    super::field_unique::apply(terms, &goal.formulas, owner)?
                } else {
                    super::field_simplify::apply(terms, &goal.formulas, owner)?
                };
                owner
                    .admit(1, size_of::<Goal>())
                    .map_err(|_| TacticFailure::new("tactic original output admission refused"))?;
                let progressed = formulas != goal.formulas;
                Ok(StepOutcome {
                    goals: vec![Goal {
                        formulas,
                        depth: goal.depth + 1,
                        model_converter: goal.model_converter,
                    }],
                    progressed,
                })
            }
            Tactic::Skip => singleton_outcome(goal, false, owner),
            Tactic::Fail => logical_failure(owner, "fail tactic"),
            Tactic::FlattenAnd => Ok(Self::primitive(
                goal,
                |terms, fs| FlattenAnd::new().apply(terms, fs),
                terms,
            )),
            Tactic::SolveEqs => Ok(Self::primitive(
                goal,
                |terms, fs| {
                    let flattened = FlattenAnd::new().apply(terms, fs);
                    let solved = VariableSubstitution::new().apply(terms, fs);
                    flattened || solved
                },
                terms,
            )),
            Tactic::PropagateValues => Ok(Self::primitive(
                goal,
                |terms, fs| {
                    let flattened = FlattenAnd::new().apply(terms, fs);
                    let propagated = PropagateValues::new().apply_goal(terms, fs);
                    // Goal-mode folding can mint a NEW top-level `and` (e.g.
                    // `(or false (and a b))` folds to `(and a b)`) — flatten
                    // again so the subgoal prints one conjunct per line,
                    // matching z3.
                    let reflattened = FlattenAnd::new().apply(terms, fs);
                    flattened || propagated || reflattened
                },
                terms,
            )),
            Tactic::PropagateIneqs => Ok(Self::primitive(
                goal,
                |terms, fs| PropagateIneqs::new().apply_goal(terms, fs),
                terms,
            )),
            Tactic::QeLight => Ok(Self::primitive(
                goal,
                |terms, fs| {
                    let flattened = FlattenAnd::new().apply(terms, fs);
                    let eliminated = QeLight::new().apply(terms, fs);
                    flattened || eliminated
                },
                terms,
            )),
            Tactic::Nnf => Ok(Self::primitive(
                goal,
                |terms, fs| {
                    // Rewrite to NNF, then split the resulting top-level `and`
                    // into separate goal formulas — matching Z3's `(apply nnf)`
                    // goal shape (e.g. `(= a b)` prints as two `or` formulas).
                    let rewritten = Nnf::new().apply(terms, fs);
                    let flattened = FlattenAnd::new().apply(terms, fs);
                    rewritten || flattened
                },
                terms,
            )),
            Tactic::TseitinCnf => Ok(Self::primitive(
                goal,
                |terms, fs| TseitinCnf::new().apply(terms, fs),
                terms,
            )),
            Tactic::BitBlast => {
                // HONESTY: classify the goal BEFORE rewriting. A goal containing a
                // bit-vector construct outside the supported fragment (bvudiv,
                // bvurem, a UF/array over BV, bv2nat/int2bv, …) must HONESTLY FAIL
                // — never a silent successful identity for a goal it did not
                // actually blast. A BV-free goal is z3's genuine no-op identity.
                match BitBlast::new().classify_goal(terms, &goal.formulas) {
                    Err(detail) => Err(TacticFailure::new(format!(
                        "{detail} not supported by bit-blast"
                    ))),
                    Ok(_has_bv) => Ok(Self::primitive(
                        goal,
                        |terms, fs| {
                            // Replace every BV variable with fresh Boolean bits and
                            // every BV operator with its Boolean circuit, then split
                            // the resulting top-level conjunctions into separate goal
                            // formulas (matching Z3's goal model). Equisatisfiable. A
                            // BV-free goal is left unchanged (z3's no-op identity).
                            let blasted = BitBlast::new().apply(terms, fs);
                            let flattened = FlattenAnd::new().apply(terms, fs);
                            blasted || flattened
                        },
                        terms,
                    )),
                }
            }
            Tactic::SplitClause => split_clause(terms, goal),
            Tactic::CtxSolverSimplify => Ok(Self::primitive(goal, ctx_solver_simplify, terms)),
            Tactic::Then(first, second) => {
                let first_out = first.apply_step_admitted(terms, goal, owner)?;
                let mut goals = Vec::new();
                let mut progressed = first_out.progressed;
                for g in first_out.goals {
                    let second_out = second.apply_step_admitted(terms, g, owner)?;
                    progressed |= second_out.progressed;
                    append_goals_owned(&mut goals, second_out.goals, owner)?;
                }
                Ok(StepOutcome { goals, progressed })
            }
            Tactic::OrElse(first, alt) => {
                let copy = clone_goal_owned(&goal, owner)?;
                match first.apply_step_admitted(terms, copy, owner) {
                    Ok(out) => Ok(out),
                    // Z3's or-else falls through on FAILURE only.
                    Err(failure) => {
                        if owner.is_some_and(|owner| owner.check().is_err()) {
                            Err(failure)
                        } else {
                            alt.apply_step_admitted(terms, goal, owner)
                        }
                    }
                }
            }
            Tactic::Repeat(body, bound) => Self::apply_repeat(body, *bound, terms, goal, owner),
            Tactic::When(probe, body) => {
                let depth = goal.depth;
                if eval_probe_owned(probe, terms, &goal.formulas, depth, owner)? {
                    body.apply_step_admitted(terms, goal, owner)
                } else {
                    singleton_outcome(goal, false, owner)
                }
            }
            Tactic::FailIf(probe) => {
                if eval_probe_owned(probe, terms, &goal.formulas, goal.depth, owner)? {
                    logical_failure(owner, "fail-if tactic")
                } else {
                    singleton_outcome(goal, false, owner)
                }
            }
            Tactic::Cond(probe, t1, t2) => {
                // Evaluate the probe once on the goal, then commit to that branch.
                // A failure of the chosen branch propagates (no fall-through) —
                // Z3's `cond` is NOT `(or-else (when p t1) t2)`.
                if eval_probe_owned(probe, terms, &goal.formulas, goal.depth, owner)? {
                    t1.apply_step_admitted(terms, goal, owner)
                } else {
                    t2.apply_step_admitted(terms, goal, owner)
                }
            }
            Tactic::FailIfNotDecided => {
                if let Some(owner) = owner {
                    owner
                        .admit(goal.formulas.len(), 0)
                        .map_err(|_| TacticFailure::new("tactic decided scan stopped"))?;
                }
                // Decided ⟺ empty goal (trivially SAT) OR the goal carries the
                // literal `false` (trivially UNSAT) — exactly Z3's goal
                // `inconsistent()`/`size()==0` test. Decided ⇒ identity; anything
                // else ⇒ honest failure (no fabricated goal).
                let decided = goal.formulas.is_empty()
                    || goal.formulas.iter().any(|&f| is_false_literal(terms, f));
                if decided {
                    singleton_outcome(goal, false, owner)
                } else {
                    // z3's byte text: `(error "tactic failed: undecided")`
                    // (measured, z3 4.15.4 `(apply fail-if-undecided)`).
                    logical_failure(owner, "undecided")
                }
            }
            Tactic::ElimTermIte => Ok(Self::primitive(
                goal,
                |terms, fs| {
                    // Name each non-Bool term-ite with a fresh definition var; z3
                    // emits the renamed formulas FIRST, then the guard defs.
                    let mut defs = Vec::new();
                    let renamed = terms.name_non_bool_ites_all(fs, &mut defs);
                    let changed = !defs.is_empty() || renamed != *fs;
                    *fs = renamed;
                    fs.extend(defs);
                    // z3 goal-shape parity: split any top-level conjunctions.
                    let flattened = FlattenAnd::new().apply(terms, fs);
                    changed || flattened
                },
                terms,
            )),
            Tactic::BlastTermIte => Ok(Self::primitive(
                goal,
                |terms, fs| {
                    // Shannon-lift term-ites out over their enclosing atoms. A
                    // budget-truncated partial lift is still equivalence-preserving.
                    let (lifted, _budget) = terms.lift_arithmetic_ite_all_with_status(fs);
                    let changed = lifted != *fs;
                    *fs = lifted;
                    let flattened = FlattenAnd::new().apply(terms, fs);
                    changed || flattened
                },
                terms,
            )),
            // The quantifier pipeline's DER pass (one implementation).
            Tactic::Der => Ok(Self::primitive(
                goal,
                |terms, fs| crate::simplifier::der_tactic(terms, fs),
                terms,
            )),
            Tactic::DistributeForall => Ok(Self::primitive(
                goal,
                |terms, fs| DistributeForall::new().apply(terms, fs),
                terms,
            )),
            Tactic::MaxBvSharing => Ok(Self::primitive(
                goal,
                |terms, fs| terms.maximize_bv_sharing(fs),
                terms,
            )),
            Tactic::ReduceArgs => Ok(Self::primitive(
                goal,
                |terms, fs| ReduceArgs::new().apply(terms, fs),
                terms,
            )),
            // CLASS F: always an honest failure — NO goal is ever produced, so
            // this can never mint or change a verdict; `or-else` catches it
            // exactly as on z3 (which fails these tactics on generic goals).
            Tactic::FailMsg { message, .. } => logical_failure(owner, message),
            Tactic::Bv1Blast => {
                // Measured z3 semantics: fail iff the goal contains a
                // bit-vector term; identity (one applied primitive, depth+1)
                // otherwise. Never a fabricated blast.
                if GoalFeatures::collect(terms, &goal.formulas).uses_bv {
                    Err(TacticFailure::new("bv1 blaster cannot be applied to goal"))
                } else {
                    Ok(Self::primitive(goal, |_terms, _fs| false, terms))
                }
            }
        }
    }

    /// Run a primitive pass over a clone of the goal's formulas, returning the
    /// transformed single subgoal at depth+1 and whether it made progress.
    ///
    /// The depth is incremented whether or not the pass changed anything (Z3
    /// increments a goal's depth for every applied primitive); `repeat` uses the
    /// returned `progressed` flag — not the depth — to detect its fixpoint.
    fn primitive(
        goal: Goal,
        run: impl FnOnce(&mut TermStore, &mut Vec<TermId>) -> bool,
        terms: &mut TermStore,
    ) -> StepOutcome {
        let mut formulas = goal.formulas;
        let progressed = run(terms, &mut formulas);
        StepOutcome {
            goals: vec![Goal {
                formulas,
                depth: goal.depth + 1,
                model_converter: goal.model_converter,
            }],
            progressed,
        }
    }

    /// The `repeat` loop: apply `body` to every live subgoal until none makes
    /// progress (or `bound` iterations elapse). The application that reaches the
    /// fixpoint is a genuine application, so its depth increment is KEPT — Z3
    /// counts every applied primitive, so `repeat elim-and` on an already-flat
    /// goal is depth 1 (one no-op application), not depth 0 (byte-confirmed
    /// against z3 4.x: `(then elim-and elim-and)` on a flat goal is depth 2). The
    /// identity `skip` contributes no increment (it returns the goal unchanged),
    /// so `(repeat skip)` stays at depth 0. A body FAILURE propagates (matching
    /// Z3, where `repeat split-clause` errors once a subgoal has no remaining
    /// clause).
    fn apply_repeat(
        body: &Tactic,
        bound: Option<usize>,
        terms: &mut TermStore,
        goal: Goal,
        owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
    ) -> Result<StepOutcome, TacticFailure> {
        let mut frontier = Vec::new();
        reserve_owned(&mut frontier, 1, owner)?;
        frontier.push(goal);
        let mut done: Vec<Goal> = Vec::new();
        let mut any_progress_overall = false;
        let mut iterations = 0usize;

        loop {
            if let Some(limit) = bound {
                if iterations >= limit {
                    append_goals_owned(&mut done, frontier, owner)?;
                    break;
                }
            }
            let mut next = Vec::new();
            let mut progressed_this_round = false;
            for g in std::mem::take(&mut frontier) {
                let out = body.apply_step_admitted(terms, g, owner)?;
                if out.progressed {
                    progressed_this_round = true;
                    any_progress_overall = true;
                    append_goals_owned(&mut next, out.goals, owner)?;
                } else {
                    // Fixpoint: keep the APPLIED result (its depth increment
                    // counts — Z3 counts every applied primitive). The formulas
                    // are unchanged from the input goal; only the depth may have
                    // ticked (0 for `skip`, +1 for a depth-incrementing body).
                    append_goals_owned(&mut done, out.goals, owner)?;
                }
            }
            if !progressed_this_round {
                append_goals_owned(&mut done, next, owner)?;
                break;
            }
            frontier = next;
            iterations += 1;
        }

        Ok(StepOutcome {
            goals: done,
            progressed: any_progress_overall,
        })
    }

    /// Apply this tactic to a goal in place, distinguishing an HONEST FAILURE
    /// from a benign no-op.
    ///
    /// Transforms `assertions` and returns:
    /// - `Ok(true)`  — the goal changed (a single transformed subgoal),
    /// - `Ok(false)` — no progress OR a case split (several subgoals): leave the
    ///   goal untouched; solving the original is sound (the subgoals' disjunction
    ///   is equisatisfiable to it),
    /// - `Err(failure)` — the tactic HONESTLY FAILED (e.g. `bit-blast` on an
    ///   out-of-fragment BV goal, `fail`), producing NO goal. The caller must
    ///   surface the failure rather than fabricate a verdict or silently solve a
    ///   goal the tactic did not produce.
    pub(crate) fn apply_or_fail(
        &self,
        terms: &mut TermStore,
        assertions: &mut Vec<TermId>,
    ) -> Result<bool, TacticFailure> {
        let goal = Goal::root(assertions.clone());
        let out = self.apply_step(terms, goal)?;
        if out.goals.len() == 1 && out.progressed {
            *assertions = out.goals.into_iter().next().expect("len == 1").formulas;
            Ok(true)
        } else {
            // No progress or a case split (len != 1): benign no-op.
            Ok(false)
        }
    }

    /// Apply this tactic to a goal in place, reporting only whether it made
    /// progress (a genuine failure is swallowed to `false`).
    ///
    /// Convenience shim for tests that treat an honest failure the same as a
    /// no-op. Prefer [`apply_or_fail`](Self::apply_or_fail) when the failure
    /// must be surfaced (the solver paths do).
    #[cfg(test)]
    pub(crate) fn apply(&self, terms: &mut TermStore, assertions: &mut Vec<TermId>) -> bool {
        self.apply_or_fail(terms, assertions).unwrap_or(false)
    }

    /// Apply this tactic to `goal`, returning EVERY resulting subgoal (Z3's
    /// apply-result). A case-splitting tactic (`split-clause`) yields several
    /// subgoals whose disjunction is equivalent to the input; every other tactic
    /// yields exactly one. A no-progress primitive still yields the (unchanged)
    /// goal as a single subgoal, matching Z3's `(apply <t>)`.
    ///
    /// This is the multi-subgoal surface behind the C-API `Z3_tactic_apply`,
    /// distinct from [`apply_or_fail`](Self::apply_or_fail) — which collapses a
    /// split (or no-progress) run to a benign no-op for the solve path. Here the
    /// full subgoal list is preserved so a caller can inspect each subgoal.
    ///
    /// # Errors
    ///
    /// Returns the [`TacticFailure`] verbatim if the tactic HONESTLY FAILS (e.g.
    /// `bit-blast` on an out-of-fragment BV goal, `fail`, `split-clause` on a
    /// clause-free goal) — never a fabricated subgoal for a transform that did
    /// not actually run.
    pub fn apply_subgoals(
        &self,
        terms: &mut TermStore,
        goal: Goal,
    ) -> Result<Vec<Goal>, TacticFailure> {
        Ok(self.apply_step(terms, goal)?.goals)
    }

    /// Produce a [`TacticSolver`] for `logic` that applies this tactic to the
    /// goal before each `check_sat`.
    ///
    /// # Errors
    ///
    /// Returns an error if a solver cannot be created for `logic`.
    #[must_use = "this returns a Result that must be checked"]
    pub fn solver(self, logic: Logic) -> Result<TacticSolver, SolverError> {
        Ok(TacticSolver {
            inner: Solver::try_new(logic)?,
            tactic: self,
        })
    }
}

/// Split the first top-level disjunction `(or c1 … cn)` in `goal` into `n`
/// subgoals, one per disjunct (the other assertions carried through). Fails if
/// no formula is a clause, exactly like Z3's `split-clause`.
///
/// SOUNDNESS: with the clause at index `i`, the produced subgoals are
/// `{…, c_k, …}` for each disjunct `c_k`; their disjunction is `(⋀_{j≠i} f_j) ∧
/// (c_1 ∨ … ∨ c_n)` = the original goal. So the input is SAT iff some subgoal is.
fn split_clause(terms: &TermStore, goal: Goal) -> Result<StepOutcome, TacticFailure> {
    for (i, &formula) in goal.formulas.iter().enumerate() {
        if let Some(disjuncts) = as_clause(terms, formula) {
            let goals = disjuncts
                .into_iter()
                .map(|d| {
                    let mut formulas = goal.formulas.clone();
                    formulas[i] = d;
                    Goal {
                        formulas,
                        depth: goal.depth + 1,
                        model_converter: goal.model_converter.clone(),
                    }
                })
                .collect();
            return Ok(StepOutcome {
                goals,
                progressed: true,
            });
        }
    }
    Err(TacticFailure::new(
        "split-clause tactic failed, goal does not contain any clause",
    ))
}

/// The deadline of the tactic application in progress on this thread: the
/// nested checks of a solver-invoking pass (`ctx-solver-simplify`) run under
/// the applying solver's timeout instead of without one.
mod tactic_deadline {
    use std::cell::Cell;
    use std::time::{Duration, Instant};

    thread_local! {
        static DEADLINE: Cell<Option<Instant>> = const { Cell::new(None) };
    }

    /// Restores the enclosing application's deadline when dropped.
    pub(super) struct Installed(Option<Instant>);

    impl Drop for Installed {
        fn drop(&mut self) {
            DEADLINE.with(|cell| cell.set(self.0));
        }
    }

    /// Install `now + timeout` (the earlier of it and an enclosing deadline).
    pub(super) fn install(timeout: Option<Duration>) -> Installed {
        let previous = DEADLINE.with(Cell::get);
        let mine = timeout.and_then(|t| Instant::now().checked_add(t));
        let effective = match (previous, mine) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (a, b) => a.or(b),
        };
        DEADLINE.with(|cell| cell.set(effective));
        Installed(previous)
    }

    /// `None` without a deadline; `Some(None)` once it passed; otherwise the
    /// time left.
    pub(super) fn remaining() -> Option<Option<Duration>> {
        DEADLINE.with(Cell::get).map(|deadline| {
            deadline
                .checked_duration_since(Instant::now())
                .filter(|d| !d.is_zero())
        })
    }

    pub(super) fn end() -> Option<Instant> {
        DEADLINE.with(Cell::get)
    }
}

/// The outcome of a single nested context-implication sub-check.
enum SubCheck {
    /// The queried conjunction is provably UNSAT (a decided refutation).
    Unsat,
    /// SAT, or the sub-solver returned unknown — in EITHER case the caller must
    /// NOT simplify (soundness on unknown: never act on an unproven implication).
    NotProven,
}

/// Check whether `(⋀ before) ∧ (⋀ after) ∧ target` is UNSAT in `sub`, using a
/// fresh push/pop scope so `sub`'s base assertion set (empty) is untouched.
///
/// Only a genuine UNSAT verdict counts as proven; a SAT or unknown result maps to
/// [`SubCheck::NotProven`] so the caller keeps the assertion (sound on unknown).
/// All terms are already interned in `sub`'s term store.
fn ctx_check_unsat(
    sub: &mut Solver,
    before: &[TermId],
    after: &[TermId],
    target: TermId,
) -> SubCheck {
    // The caller's deadline bounds every nested check (an expired one proves
    // nothing, which keeps the assertion: sound).
    match tactic_deadline::remaining() {
        Some(Some(remaining)) => sub.set_timeout(Some(remaining)),
        Some(None) => return SubCheck::NotProven,
        None => {}
    }
    if sub.try_push().is_err() {
        return SubCheck::NotProven;
    }
    for &t in before
        .iter()
        .chain(after.iter())
        .chain(std::iter::once(&target))
    {
        let term = sub.wrap_term(t);
        if sub.try_assert_term(term).is_err() {
            // Could not build the sub-goal faithfully -> do not simplify.
            let _ = sub.try_pop();
            return SubCheck::NotProven;
        }
    }
    let unsat = sub.check_sat_internal_api().is_unsat();
    // A failed pop would corrupt subsequent checks; if it fails, signal not-proven
    // (the caller falls back to keeping assertions, which is always sound).
    if sub.try_pop().is_err() {
        return SubCheck::NotProven;
    }
    if unsat {
        SubCheck::Unsat
    } else {
        SubCheck::NotProven
    }
}

/// Contextual simplification using the solver — the `ctx-solver-simplify` pass.
///
/// See [`Tactic::CtxSolverSimplify`] for the full contract. Returns `true` iff the
/// goal changed. SOUND: only PROVEN-redundant assertions are dropped, and the
/// goal collapses to `{false}` only on a PROVEN contradiction among a subset of
/// the original assertions; an unknown sub-check never simplifies.
///
/// The nested checks run in a FRESH sub-solver (`Logic::All`, auto-detecting the
/// theory) whose base goal stays empty — each check is a `push`/assert/`pop`
/// scope. The pass is the identity on goals with quantifiers or a
/// non-arithmetic/BV theory (UF/array/string/FP/datatype), which it cannot
/// faithfully replay in the sub-solver; being the identity there is always sound.
fn ctx_solver_simplify(terms: &mut TermStore, formulas: &mut Vec<TermId>) -> bool {
    // Nothing to simplify on the empty goal.
    if formulas.is_empty() {
        return false;
    }
    // Only run where we can faithfully rebuild every assertion in a fresh
    // sub-solver over free 0-ary constants: quantifier-free, and confined to the
    // Bool/Int/Real/BitVec world (no UF/array/string/FP/datatype and no bound
    // variables). Anywhere else this pass is the identity (sound no-op).
    let feats = GoalFeatures::collect(terms, formulas);
    if feats.has_quant || feats.has_other {
        return false;
    }

    // Fresh sub-solver whose base assertion set stays empty; if it cannot be
    // created we simply do not simplify (sound identity).
    let Ok(mut sub) = Solver::try_new(Logic::All) else {
        return false;
    };

    // Declare every distinct free constant into the sub-solver so its symbol is
    // registered, then graft each assertion's term DAG across. `mk_var` interns
    // by name, so the grafted variable nodes reuse the declared ids.
    let mut var_ids: Vec<TermId> = Vec::new();
    let mut seen: std::collections::HashSet<TermId> = std::collections::HashSet::new();
    for &f in formulas.iter() {
        walk(terms, f, &mut seen, &mut |id, data| {
            if matches!(data, TermData::Var(_, _)) {
                var_ids.push(id);
            }
        });
    }
    let mut declared: std::collections::HashSet<String> = std::collections::HashSet::new();
    for id in var_ids {
        let (name, sort) = match terms.get(id) {
            TermData::Var(name, _) => (name.clone(), terms.sort(id).clone()),
            _ => continue,
        };
        if declared.insert(name.clone()) {
            let _ = sub.declare_const(&name, sort);
        }
    }

    let mut memo: std::collections::HashMap<TermId, TermId> = std::collections::HashMap::new();
    let mut grafted: Vec<TermId> = Vec::with_capacity(formulas.len());
    for &f in formulas.iter() {
        grafted.push(graft_term(&*terms, sub.terms_mut(), f, &mut memo));
    }

    let n = formulas.len();
    let mut kept_main: Vec<TermId> = Vec::with_capacity(n);
    let mut kept_sub: Vec<TermId> = Vec::with_capacity(n);
    let mut changed = false;

    for i in 0..n {
        let ci_sub = grafted[i];
        let after = &grafted[i + 1..];

        // Redundancy: context ∧ ¬A_i UNSAT  ⇔  context ⇒ A_i  ⇒ drop A_i.
        let neg = sub.terms_mut().mk_not(ci_sub);
        if matches!(
            ctx_check_unsat(&mut sub, &kept_sub, after, neg),
            SubCheck::Unsat
        ) {
            changed = true;
            continue;
        }

        // Contradiction: context ∧ A_i UNSAT  ⇔  a subset of the ORIGINAL
        // assertions is unsatisfiable  ⇒ the whole goal is UNSAT ⇒ collapse to
        // the single literal `false` (Z3's inconsistent-goal shape).
        if matches!(
            ctx_check_unsat(&mut sub, &kept_sub, after, ci_sub),
            SubCheck::Unsat
        ) {
            let f = terms.mk_bool(false);
            *formulas = vec![f];
            return true;
        }

        // SAT or unknown: keep A_i verbatim (sound on unknown).
        kept_main.push(formulas[i]);
        kept_sub.push(ci_sub);
    }

    if changed {
        *formulas = kept_main;
        true
    } else {
        false
    }
}

/// Is `id` the Boolean `false` literal? This is exactly Z3's goal-inconsistency
/// marker (`goal::inconsistent()` keys on the goal carrying the `false` term), so
/// [`Tactic::FailIfNotDecided`] treats such a goal as trivially decided-UNSAT.
fn is_false_literal(terms: &TermStore, id: TermId) -> bool {
    matches!(
        terms.get(id),
        TermData::Const(ay_core::term::Constant::Bool(false))
    )
}

/// If `id` is a top-level disjunction `(or c1 … cn)` with `n ≥ 2`, return its
/// disjuncts; otherwise `None`.
fn as_clause(terms: &TermStore, id: TermId) -> Option<Vec<TermId>> {
    match terms.get(id) {
        TermData::App(ay_core::Symbol::Named(name), args)
            if name == "or" && !terms.is_declared_function(name) && args.len() >= 2 =>
        {
            Some(args.clone())
        }
        _ => None,
    }
}

/// Evaluate a Z3 probe over a goal to a boolean (`> 0` is true, mirroring Z3's
/// numeric-probe-as-condition convention).
fn eval_probe_owned(
    probe: &Probe,
    terms: &TermStore,
    formulas: &[TermId],
    depth: usize,
    owner: Option<&dyn ay_core::term::TermConstructionAdmission>,
) -> Result<bool, TacticFailure> {
    let Some(owner) = owner else {
        return Ok(eval_probe(probe, terms, formulas, depth));
    };
    let mut pending = Vec::new();
    let mut values: Vec<f64> = Vec::new();
    reserve_owned(&mut pending, 1, Some(owner))?;
    pending.push((probe, false));
    while let Some((probe, finish)) = pending.pop() {
        owner
            .admit(1, 0)
            .map_err(|_| TacticFailure::new("tactic probe stopped"))?;
        let value = match probe {
            Probe::Not(a) if !finish => {
                reserve_owned(&mut pending, 2, Some(owner))?;
                pending.push((probe, true));
                pending.push((a, false));
                continue;
            }
            Probe::And(a, b) | Probe::Or(a, b) | Probe::Cmp(_, a, b) if !finish => {
                reserve_owned(&mut pending, 3, Some(owner))?;
                pending.push((probe, true));
                pending.push((b, false));
                pending.push((a, false));
                continue;
            }
            Probe::Not(_) => f64::from(
                values
                    .pop()
                    .ok_or_else(|| TacticFailure::new("invalid probe"))?
                    == 0.0,
            ),
            Probe::And(..) | Probe::Or(..) | Probe::Cmp(..) => {
                let b = values
                    .pop()
                    .ok_or_else(|| TacticFailure::new("invalid probe"))?;
                let a = values
                    .pop()
                    .ok_or_else(|| TacticFailure::new("invalid probe"))?;
                f64::from(match probe {
                    Probe::And(..) => a != 0.0 && b != 0.0,
                    Probe::Or(..) => a != 0.0 || b != 0.0,
                    Probe::Cmp(op, ..) => match op {
                        ProbeCmp::Lt => a < b,
                        ProbeCmp::Le => a <= b,
                        ProbeCmp::Gt => a > b,
                        ProbeCmp::Ge => a >= b,
                        ProbeCmp::Eq => a == b,
                    },
                    _ => false,
                })
            }
            Probe::Const(text) => {
                owner
                    .admit(text.len(), 0)
                    .map_err(|_| TacticFailure::new("probe parse stopped"))?;
                text.parse::<f64>()
                    .map_err(|_| TacticFailure::new("invalid numeric probe"))?
            }
            Probe::Depth => depth as f64,
            Probe::Size => flatten_owned(terms, formulas, owner)?.len() as f64,
            _ => {
                return Err(TacticFailure::new(
                    "this probe has no original-owner execution path",
                ))
            }
        };
        reserve_owned(&mut values, 1, Some(owner))?;
        values.push(value);
    }
    owner
        .check()
        .map_err(|_| TacticFailure::new("tactic probe stopped"))?;
    Ok(values.len() == 1 && values[0] != 0.0)
}

fn eval_probe(probe: &Probe, terms: &TermStore, formulas: &[TermId], depth: usize) -> bool {
    eval_probe_num(probe, terms, formulas, depth) != 0.0
}

/// Evaluate a probe to its numeric value over the goal.
///
/// # Z3 goal-model parity
///
/// Z3's goal model pre-splits every top-level conjunction into separate
/// formulas before a probe runs, so `size`/`num-exprs` are computed over the
/// SPLIT formula list — `(assert (and A B))` reads as `size = 2` and its
/// `num-exprs` excludes the `and` node. We reproduce that here by flattening the
/// goal's top-level conjunctions ([`flatten_top_conjunctions`]) for exactly the
/// probes whose value depends on it, so `when`/`fail-if` gate identically to Z3.
/// `num-consts` is invariant under this flattening (the `and` node contributes no
/// constant), so it reads the raw formulas.
fn eval_probe_num(probe: &Probe, terms: &TermStore, formulas: &[TermId], depth: usize) -> f64 {
    match probe {
        Probe::Const(text) => text.parse::<f64>().unwrap_or(0.0),
        // Z3 counts the goal's formulas AFTER splitting top-level conjunctions.
        Probe::Size => flatten_top_conjunctions(terms, formulas).len() as f64,
        Probe::NumConsts => count_consts(terms, formulas) as f64,
        // Z3 counts sub-expressions over the split formulas, so the split-away
        // top-level `and` nodes are not counted.
        Probe::NumExprs => count_exprs(terms, &flatten_top_conjunctions(terms, formulas)) as f64,
        // Z3's `depth` probe returns the goal's transformation depth verbatim.
        Probe::Depth => depth as f64,
        Probe::NumBoolConsts => count_consts_where(terms, formulas, |s| s == &Sort::Bool) as f64,
        Probe::NumArithConsts => {
            count_consts_where(terms, formulas, |s| matches!(s, Sort::Int | Sort::Real)) as f64
        }
        Probe::NumBvConsts => {
            count_consts_where(terms, formulas, |s| matches!(s, Sort::BitVec(_))) as f64
        }
        Probe::HasQuantifiers => bool_to_num(GoalFeatures::collect(terms, formulas).has_quant),
        Probe::IsPropositional => {
            bool_to_num(GoalFeatures::collect(terms, formulas).is_propositional())
        }
        Probe::IsQfbv => bool_to_num(GoalFeatures::collect(terms, formulas).is_qfbv()),
        Probe::IsQflia => bool_to_num(GoalFeatures::collect(terms, formulas).is_qflia()),
        Probe::IsQflra => bool_to_num(GoalFeatures::collect(terms, formulas).is_qflra()),
        Probe::IsQflira => bool_to_num(GoalFeatures::collect(terms, formulas).is_qflira()),
        Probe::IsLia => bool_to_num(GoalFeatures::collect(terms, formulas).is_lia()),
        Probe::IsLra => bool_to_num(GoalFeatures::collect(terms, formulas).is_lra()),
        Probe::IsLira => bool_to_num(GoalFeatures::collect(terms, formulas).is_lira()),
        Probe::IsQfnia => bool_to_num(GoalFeatures::collect(terms, formulas).is_qfnia()),
        Probe::IsQfnra => bool_to_num(GoalFeatures::collect(terms, formulas).is_qfnra()),
        Probe::IsNia => bool_to_num(GoalFeatures::collect(terms, formulas).is_nia()),
        Probe::IsNra => bool_to_num(GoalFeatures::collect(terms, formulas).is_nra()),
        // --- Full z3-4.15.4 probe-name coverage. Every value below either is
        // computed honestly from the real goal or is a DOCUMENTED conservative
        // approximation (see the `ay_frontend::Probe` variant docs). A probe
        // value only picks between two SOUND tactics in `when`/`fail-if`/
        // `if`/`cond`, so an approximation can shift goal SHAPE, never a
        // verdict. Cross-checked against libz3 4.15.4 on an 8-goal battery
        // (empty/prop/int/int-bounded/bv/real/uf/quantified). ---
        Probe::HasPatterns => bool_to_num(has_patterns(terms, formulas)),
        Probe::IsIlp => {
            // Measured z3 semantics: QF linear-Int-only goals with NO Boolean
            // constants (the empty goal qualifies; a propositional goal does
            // not).
            let f = GoalFeatures::collect(terms, formulas);
            bool_to_num(
                f.qf()
                    && !f.uses_real
                    && !f.uses_bv
                    && !f.has_other
                    && !f.nonlinear
                    && count_consts_where(terms, formulas, |s| s == &Sort::Bool) == 0,
            )
        }
        Probe::IsNira => {
            // Measured z3 semantics: requires genuinely NONLINEAR arithmetic
            // (linear goals read 0).
            let f = GoalFeatures::collect(terms, formulas);
            bool_to_num((f.uses_int || f.uses_real) && f.nonlinear && !f.uses_bv && !f.has_other)
        }
        // Measured propositional core for is-pb; is-quasi-pb shares it as a
        // documented conservative under-approximation.
        Probe::IsPb | Probe::IsQuasiPb => {
            bool_to_num(GoalFeatures::collect(terms, formulas).is_propositional())
        }
        // Measured: z3 accepts the bool/BV core for all three (an FP-free BV
        // goal reads 1 on is-qffp/is-qffpbv); arrays/UF/FP terms read 0 in AY
        // (documented under-approximation).
        Probe::IsQfaufbv | Probe::IsQffp | Probe::IsQffpbv => {
            bool_to_num(GoalFeatures::collect(terms, formulas).is_qfbv())
        }
        Probe::IsQfauflia => bool_to_num(GoalFeatures::collect(terms, formulas).is_qflia()),
        Probe::IsQfbvEq => {
            // Measured z3 semantics: QF goals WITHOUT bit-vector arithmetic
            // read 1 (even pure-arith goals); AY conservatively reads 0 as
            // soon as any BV term appears (documented under-approximation for
            // pure =/concat/extract BV goals).
            let f = GoalFeatures::collect(terms, formulas);
            bool_to_num(f.qf() && !f.uses_bv)
        }
        // Measured: z3 reads 0 even on the empty and pure-LRA goals; AY cannot
        // classify FP terms and never claims membership (conservative 0).
        Probe::IsQffplra => 0.0,
        Probe::IsQfufnra => {
            // The nonlinear-real core; genuine UF goals read 0 (documented
            // under-approximation — AY cannot separate UF from other theories
            // in its fragment features).
            let f = GoalFeatures::collect(terms, formulas);
            bool_to_num(
                f.qf() && f.uses_real && f.nonlinear && !f.uses_int && !f.uses_bv && !f.has_other,
            )
        }
        Probe::IsUnbounded => bool_to_num(is_unbounded(terms, formulas)),
        Probe::AckrBoundProbe => ackr_bound(terms, formulas),
        Probe::ArithAvgBw => {
            let bws = arith_coefficient_bws(terms, formulas);
            average(&bws)
        }
        Probe::ArithMaxBw => arith_coefficient_bws(terms, formulas)
            .into_iter()
            .fold(0.0, f64::max),
        Probe::ArithAvgDeg => {
            let degs = arith_atom_degrees(terms, formulas);
            average(&degs)
        }
        Probe::ArithMaxDeg => arith_atom_degrees(terms, formulas)
            .into_iter()
            .fold(0.0, f64::max),
        // AY does not meter allocator usage; a fabricated reading would be
        // worse than a documented conservative 0.
        Probe::Memory => 0.0,
        // AY goals always support model extraction and never carry proof/core
        // mode — exactly z3's default goal flags (measured: 1/0/0).
        Probe::ProduceModel => 1.0,
        Probe::ProduceProofs | Probe::ProduceUnsatCores => 0.0,
        Probe::Not(a) => bool_to_num(eval_probe_num(a, terms, formulas, depth) == 0.0),
        Probe::And(a, b) => bool_to_num(
            eval_probe_num(a, terms, formulas, depth) != 0.0
                && eval_probe_num(b, terms, formulas, depth) != 0.0,
        ),
        Probe::Or(a, b) => bool_to_num(
            eval_probe_num(a, terms, formulas, depth) != 0.0
                || eval_probe_num(b, terms, formulas, depth) != 0.0,
        ),
        Probe::Cmp(op, a, b) => {
            let x = eval_probe_num(a, terms, formulas, depth);
            let y = eval_probe_num(b, terms, formulas, depth);
            let held = match op {
                ProbeCmp::Lt => x < y,
                ProbeCmp::Le => x <= y,
                ProbeCmp::Gt => x > y,
                ProbeCmp::Ge => x >= y,
                ProbeCmp::Eq => x == y,
            };
            bool_to_num(held)
        } // NO wildcard arm — deliberately. `Probe` is exhaustive, so a future
          // probe variant without an evaluation arm is a COMPILE ERROR here,
          // never a silently-fabricated constant.
    }
}

fn bool_to_num(b: bool) -> f64 {
    if b {
        1.0
    } else {
        0.0
    }
}

/// Mean of a probe-value sample, `0.0` on an empty sample (z3's convention for
/// the `arith-avg-*` probes on goals with nothing to measure).
fn average(values: &[f64]) -> f64 {
    if values.is_empty() {
        0.0
    } else {
        values.iter().sum::<f64>() / values.len() as f64
    }
}

/// `has-patterns` — does any quantifier in the goal carry patterns/triggers?
/// HONEST: AY quantifier terms store their trigger groups verbatim.
fn has_patterns(terms: &TermStore, formulas: &[TermId]) -> bool {
    let mut seen = std::collections::HashSet::new();
    let mut found = false;
    for &f in formulas {
        walk(terms, f, &mut seen, &mut |_, data| {
            if let TermData::Forall(_, _, triggers) | TermData::Exists(_, _, triggers) = data {
                if triggers.iter().any(|group| !group.is_empty()) {
                    found = true;
                }
            }
        });
    }
    found
}

/// `ackr-bound-probe` — an upper bound on the Ackermann congruence lemmas the
/// goal could generate: Σ over uninterpreted functions of C(n, 2), where `n`
/// counts the DISTINCT application terms of that function. HONEST: computed
/// from the goal's real application set (matches libz3 on the measured
/// battery, e.g. 0 for a single `f(x)` occurrence).
fn ackr_bound(terms: &TermStore, formulas: &[TermId]) -> f64 {
    let mut seen = std::collections::HashSet::new();
    let mut apps: std::collections::HashMap<String, std::collections::HashSet<TermId>> =
        std::collections::HashMap::new();
    for &f in formulas {
        walk(terms, f, &mut seen, &mut |id, data| {
            if let TermData::App(sym, args) = data {
                if is_uninterpreted_function(sym, args) {
                    apps.entry(sym.name().to_string()).or_default().insert(id);
                }
            }
        });
    }
    apps.values()
        .map(|set| {
            let n = set.len() as f64;
            n * (n - 1.0) / 2.0
        })
        .sum()
}

/// Collect the bit widths of the goal's arithmetic numerals (`arith-avg-bw` /
/// `arith-max-bw`). An integer numeral contributes `max(1, bits(|n|))`; a
/// rational contributes `bits(|numerator|) + bits(|denominator|)` (matches
/// libz3 on the measured battery: `5` → 3, `5/2` → 5, `0` → 1). BV numerals
/// are NOT arithmetic coefficients and are excluded. Documented approximation
/// of z3's per-atom coefficient harvesting (AY collects every arith numeral
/// reachable in the goal).
fn arith_coefficient_bws(terms: &TermStore, formulas: &[TermId]) -> Vec<f64> {
    use ay_core::term::Constant;
    let mut seen = std::collections::HashSet::new();
    let mut bws = Vec::new();
    for &f in formulas {
        walk(terms, f, &mut seen, &mut |_, data| match data {
            TermData::Const(Constant::Int(n)) => {
                bws.push((n.magnitude().bits().max(1)) as f64);
            }
            TermData::Const(Constant::Rational(r)) => {
                let num_bits = r.0.numer().magnitude().bits();
                let den_bits = r.0.denom().magnitude().bits();
                bws.push(((num_bits + den_bits).max(1)) as f64);
            }
            _ => {}
        });
    }
    bws
}

/// Collect the polynomial total degrees of the goal's arithmetic atom sides
/// (`arith-avg-deg` / `arith-max-deg`): for every comparison/equality atom over
/// Int/Real terms, each argument side contributes its degree (constant → 0,
/// variable/UF-application → 1, `+`/`-` → max of operands, `*` → sum of
/// operands, `^` → 2). Matches libz3 on the measured battery (`x > 5` → sides
/// 1 and 0, avg 0.5, max 1). Documented approximation of z3's monomial walk.
fn arith_atom_degrees(terms: &TermStore, formulas: &[TermId]) -> Vec<f64> {
    let mut seen = std::collections::HashSet::new();
    let mut degs = Vec::new();
    for &f in formulas {
        walk(terms, f, &mut seen, &mut |_, data| {
            if let TermData::App(sym, args) = data {
                let name = sym.name();
                let is_cmp = matches!(name, "<" | "<=" | ">" | ">=");
                let is_arith_eq = name == "="
                    && args
                        .iter()
                        .all(|&a| matches!(terms.sort(a), Sort::Int | Sort::Real));
                if (is_cmp || is_arith_eq) && !args.is_empty() {
                    for &a in args {
                        if matches!(terms.sort(a), Sort::Int | Sort::Real) {
                            degs.push(poly_degree(terms, a) as f64);
                        }
                    }
                }
            }
        });
    }
    degs
}

/// Total degree of an arithmetic term viewed as a polynomial (see
/// [`arith_atom_degrees`]). Bounded recursion over the term DAG.
fn poly_degree(terms: &TermStore, id: TermId) -> usize {
    match terms.get(id) {
        TermData::Const(_) => 0,
        TermData::Var(_, _) => 1,
        TermData::Ite(_, t, e) => poly_degree(terms, *t).max(poly_degree(terms, *e)),
        TermData::App(sym, args) => match sym.name() {
            "+" | "-" => args
                .iter()
                .map(|&a| poly_degree(terms, a))
                .max()
                .unwrap_or(0),
            "*" => args.iter().map(|&a| poly_degree(terms, a)).sum(),
            "^" | "power" => 2,
            "/" | "div" | "mod" | "rem" | "abs" | "to_real" | "to_int" => args
                .iter()
                .map(|&a| poly_degree(terms, a))
                .max()
                .unwrap_or(0),
            // Any other application (an uninterpreted function over arith)
            // reads as an atomic unknown of degree 1 (measured: z3 treats
            // `f(x)` as degree 1 in `f(x) > x`).
            _ => 1,
        },
        _ => 0,
    }
}

/// `is-unbounded` — does the goal contain an Int/Real constant with no derived
/// lower or upper bound? AY's light bound scan: every top-level atom of shape
/// `var <op> numeral` / `numeral <op> var` (after z3-style top-conjunction
/// splitting) contributes a bound; `=` contributes both. A quantified goal
/// reads 0 (matching the measured libz3 battery — its bound manager works on
/// the ground fragment). A documented approximation of z3's bound manager:
/// only direct var-vs-numeral atoms are recognized.
fn is_unbounded(terms: &TermStore, formulas: &[TermId]) -> bool {
    use ay_core::term::Constant;
    let feats = GoalFeatures::collect(terms, formulas);
    if feats.has_quant || (!feats.uses_int && !feats.uses_real) {
        return false;
    }

    // Collect the arith constants (by name) and their derived bounds.
    #[derive(Default, Clone, Copy)]
    struct Bounds {
        lower: bool,
        upper: bool,
    }
    let mut bounds: std::collections::HashMap<String, Bounds> = std::collections::HashMap::new();
    let mut seen = std::collections::HashSet::new();
    for &f in formulas {
        walk(terms, f, &mut seen, &mut |id, data| {
            if let TermData::Var(name, _) = data {
                if matches!(terms.sort(id), Sort::Int | Sort::Real) {
                    bounds.entry(name.clone()).or_default();
                }
            }
        });
    }
    if bounds.is_empty() {
        return false;
    }

    let is_numeral = |id: TermId| {
        matches!(
            terms.get(id),
            TermData::Const(Constant::Int(_)) | TermData::Const(Constant::Rational(_))
        )
    };
    let var_name = |id: TermId| match terms.get(id) {
        TermData::Var(name, _) if matches!(terms.sort(id), Sort::Int | Sort::Real) => {
            Some(name.clone())
        }
        _ => None,
    };

    for &f in flatten_top_conjunctions(terms, formulas).iter() {
        let TermData::App(sym, args) = terms.get(f) else {
            continue;
        };
        let name = sym.name();
        if !matches!(name, "<" | "<=" | ">" | ">=" | "=") || args.len() != 2 {
            continue;
        }
        // `var op numeral` (upper for </<=, lower for >/>=, both for =) and
        // the mirrored `numeral op var`.
        let (var, upper, lower) = if let (Some(v), true) = (var_name(args[0]), is_numeral(args[1]))
        {
            match name {
                "<" | "<=" => (Some(v), true, false),
                ">" | ">=" => (Some(v), false, true),
                _ => (Some(v), true, true), // "="
            }
        } else if let (true, Some(v)) = (is_numeral(args[0]), var_name(args[1])) {
            match name {
                "<" | "<=" => (Some(v), false, true),
                ">" | ">=" => (Some(v), true, false),
                _ => (Some(v), true, true), // "="
            }
        } else {
            (None, false, false)
        };
        if let Some(v) = var {
            let entry = bounds.entry(v).or_default();
            entry.upper |= upper;
            entry.lower |= lower;
        }
    }

    bounds.values().any(|b| !b.lower || !b.upper)
}

/// Count the distinct NON-Boolean uninterpreted constants (0-ary variables) in
/// the goal, matching Z3's `num-consts`.
///
/// Z3's `num-consts` counts uninterpreted constants but EXCLUDES Boolean-sorted
/// ones (a Boolean constant is a propositional atom, not a first-class term for
/// this probe). So `(or a b)` with `a, b : Bool` reads `num-consts = 0`, while a
/// single `Int` constant reads `1`. We therefore filter each `Var` by its sort
/// and drop the Bool-sorted ones before de-duplicating by name.
fn count_consts(terms: &TermStore, formulas: &[TermId]) -> usize {
    let mut seen = std::collections::HashSet::new();
    let mut names = std::collections::HashSet::new();
    for &f in formulas {
        walk(terms, f, &mut seen, &mut |id, data| {
            if let TermData::Var(name, _) = data {
                // Z3 excludes Boolean constants from num-consts.
                if terms.sort(id) != &Sort::Bool {
                    names.insert(name.clone());
                }
            }
        });
    }
    // De-dup by name (a declared constant is one uninterpreted symbol).
    names.len()
}

/// Count the distinct 0-ary uninterpreted constants (variables) whose sort
/// satisfies `keep`, de-duplicated by name. Backs Z3's sort-partitioned const
/// probes (`num-bool-consts`, `num-arith-consts`, `num-bv-consts`).
fn count_consts_where(
    terms: &TermStore,
    formulas: &[TermId],
    keep: impl Fn(&Sort) -> bool,
) -> usize {
    let mut seen = std::collections::HashSet::new();
    let mut names = std::collections::HashSet::new();
    for &f in formulas {
        walk(terms, f, &mut seen, &mut |id, data| {
            if let TermData::Var(name, _) = data {
                if keep(terms.sort(id)) {
                    names.insert(name.clone());
                }
            }
        });
    }
    names.len()
}

/// Structural features of a goal used to classify it into a Z3 logic fragment.
///
/// Collected by a single DAG walk over the goal's formulas ([`Self::collect`]);
/// the `is_*` methods then reproduce Z3's probe classification (`is-qflia`,
/// `is-qfbv`, `is-propositional`, …) EXACTLY as the built-in Z3 probes report it
/// (cross-checked against libz3 on LIA/LRA/LIRA/NIA/BV/UF/quantified goals).
#[derive(Debug, Default, Clone, Copy)]
struct GoalFeatures {
    /// The goal contains a `forall`/`exists` quantifier.
    has_quant: bool,
    /// An `Int`-sorted subterm appears.
    uses_int: bool,
    /// A `Real`-sorted subterm appears.
    uses_real: bool,
    /// A `BitVec`-sorted subterm appears.
    uses_bv: bool,
    /// A construct outside the {Bool, Int, Real, BitVec} arithmetic/BV world
    /// appears — an array/string/FP/uninterpreted/datatype/seq sort, OR an
    /// uninterpreted-function application (arity ≥ 1 with a non-builtin symbol).
    /// This is what kicks a goal out of every pure arithmetic/BV fragment.
    has_other: bool,
    /// A nonlinear arithmetic operation appears (a `*` of two non-constant
    /// operands, or a `/`/`div`/`mod` by a non-constant divisor, or `^`).
    nonlinear: bool,
}

impl GoalFeatures {
    /// Collect the goal's features by walking every reachable subterm once.
    fn collect(terms: &TermStore, formulas: &[TermId]) -> Self {
        let mut f = GoalFeatures::default();
        let mut seen = std::collections::HashSet::new();
        for &root in formulas {
            walk(terms, root, &mut seen, &mut |id, data| {
                match terms.sort(id) {
                    Sort::Bool => {}
                    Sort::Int => f.uses_int = true,
                    Sort::Real => f.uses_real = true,
                    Sort::BitVec(_) => f.uses_bv = true,
                    // Arrays / strings / FP / uninterpreted / datatypes / seq /
                    // regex: outside every pure arithmetic/BV fragment.
                    _ => f.has_other = true,
                }
                match data {
                    TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => f.has_quant = true,
                    TermData::App(sym, args) => {
                        if is_uninterpreted_function(sym, args) {
                            f.has_other = true;
                        } else if is_nonlinear_app(terms, sym, args) {
                            f.nonlinear = true;
                        }
                    }
                    _ => {}
                }
            });
        }
        f
    }

    /// Quantifier-free.
    fn qf(&self) -> bool {
        !self.has_quant
    }

    /// Only Boolean structure — no arithmetic, bit-vectors, arrays, or UFs.
    fn pure_bool(&self) -> bool {
        !self.uses_int && !self.uses_real && !self.uses_bv && !self.has_other
    }

    fn is_propositional(&self) -> bool {
        self.pure_bool() && self.qf()
    }

    fn is_qfbv(&self) -> bool {
        self.qf() && !self.uses_int && !self.uses_real && !self.has_other
    }

    fn is_qflia(&self) -> bool {
        self.qf() && !self.uses_real && !self.uses_bv && !self.has_other && !self.nonlinear
    }

    fn is_qflra(&self) -> bool {
        self.qf() && !self.uses_int && !self.uses_bv && !self.has_other && !self.nonlinear
    }

    fn is_qflira(&self) -> bool {
        self.qf() && !self.uses_bv && !self.has_other && !self.nonlinear
    }

    fn is_lia(&self) -> bool {
        !self.uses_real && !self.uses_bv && !self.has_other && !self.nonlinear
    }

    fn is_lra(&self) -> bool {
        !self.uses_int && !self.uses_bv && !self.has_other && !self.nonlinear
    }

    fn is_lira(&self) -> bool {
        !self.uses_bv && !self.has_other && !self.nonlinear
    }

    fn is_qfnia(&self) -> bool {
        self.qf()
            && self.uses_int
            && !self.uses_real
            && !self.uses_bv
            && !self.has_other
            && self.nonlinear
    }

    fn is_qfnra(&self) -> bool {
        self.qf()
            && self.uses_real
            && !self.uses_int
            && !self.uses_bv
            && !self.has_other
            && self.nonlinear
    }

    fn is_nia(&self) -> bool {
        self.uses_int && !self.uses_real && !self.uses_bv && !self.has_other && self.nonlinear
    }

    fn is_nra(&self) -> bool {
        self.uses_real && !self.uses_int && !self.uses_bv && !self.has_other && self.nonlinear
    }
}

/// Is `App(sym, args)` an application of an uninterpreted function (arity ≥ 1
/// with a symbol that is not a recognized theory/core operator)?
///
/// A 0-ary `App` (none arise in AY — constants are `Var`) or a recognized
/// builtin/BV/array/arith operator is NOT an uninterpreted function. Everything
/// else with arguments is (the EUF fragment), which places the goal outside the
/// pure arithmetic/BV fragments.
fn is_uninterpreted_function(sym: &ay_core::term::Symbol, args: &[TermId]) -> bool {
    use ay_core::term::Symbol;
    if args.is_empty() {
        return false;
    }
    match sym {
        // Indexed symbols in AY are theory operators (BV extract/extend/rotate,
        // `(_ divisible k)`, …), never uninterpreted functions.
        Symbol::Indexed(_, _) => false,
        Symbol::Named(name) => !is_known_operator(name),
        // `Symbol` is `#[non_exhaustive]`; a future symbol kind with arguments is
        // conservatively treated as uninterpreted (kicks the goal out of the pure
        // arithmetic/BV fragments rather than silently claiming membership).
        _ => true,
    }
}

/// Recognized core/Boolean/arithmetic/bit-vector/array operator names. Anything
/// else with arguments is treated as an uninterpreted function.
fn is_known_operator(name: &str) -> bool {
    matches!(
        name,
        // Core / Boolean / equality.
        "true" | "false" | "and" | "or" | "not" | "=>" | "implies" | "xor"
            | "iff" | "<=>" | "=" | "distinct" | "ite"
        // Linear/nonlinear arithmetic.
            | "+" | "-" | "*" | "/" | "div" | "mod" | "rem" | "abs"
            | "<" | "<=" | ">" | ">=" | "^" | "power"
            | "to_real" | "to_int" | "is_int" | "divisible"
        // Arrays.
            | "select" | "store" | "map" | "const"
        // Bit-vectors.
            | "bvadd" | "bvsub" | "bvmul" | "bvudiv" | "bvurem" | "bvsdiv"
            | "bvsrem" | "bvsmod" | "bvand" | "bvor" | "bvxor" | "bvnand"
            | "bvnor" | "bvxnor" | "bvnot" | "bvneg" | "bvshl" | "bvlshr"
            | "bvashr" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt"
            | "bvsle" | "bvsgt" | "bvsge" | "bvcomp" | "concat" | "bv2int"
            | "bv2nat" | "int2bv" | "nat2bv"
    )
}

/// Does `App(sym, args)` introduce nonlinear arithmetic?
///
/// A multiplication with two or more non-constant operands, or a
/// division/`div`/`mod` whose divisor is not a numeric constant, or an
/// exponentiation, is nonlinear. Multiplication by a constant (`2*x`) stays
/// linear.
fn is_nonlinear_app(terms: &TermStore, sym: &ay_core::term::Symbol, args: &[TermId]) -> bool {
    use ay_core::term::Symbol;
    let Symbol::Named(name) = sym else {
        return false;
    };
    match name.as_str() {
        "*" => {
            args.iter()
                .filter(|&&a| !is_numeric_constant(terms, a))
                .count()
                >= 2
        }
        "/" | "div" | "mod" | "rem" => args.len() == 2 && !is_numeric_constant(terms, args[1]),
        "^" | "power" => true,
        _ => false,
    }
}

/// Is `id` a literal numeric constant (Int / Real / BitVec numeral)?
fn is_numeric_constant(terms: &TermStore, id: TermId) -> bool {
    matches!(terms.get(id), TermData::Const(_))
}

/// Rebuild source term `id` inside the destination store, memoizing on the
/// source id so shared subterms are grafted once (preserving DAG sharing).
///
/// Backs [`Solver::translate_terms_from`]. Every current [`TermData`]/
/// [`Constant`](ay_core::term::Constant) variant is reconstructed with the
/// matching destination builder, using the *raw* `not`/`ite` builders so the
/// grafted DAG mirrors the source structurally (not just semantically).
fn graft_term(
    src: &TermStore,
    dst: &mut TermStore,
    id: TermId,
    memo: &mut std::collections::HashMap<TermId, TermId>,
) -> TermId {
    use ay_core::term::Constant;
    if let Some(&existing) = memo.get(&id) {
        return existing;
    }
    let sort = src.sort(id).clone();
    let new_id = match src.get(id).clone() {
        TermData::Const(c) => match c {
            Constant::Bool(b) => dst.mk_bool(b),
            Constant::Int(n) => dst.mk_int(n),
            Constant::Rational(r) => dst.mk_rational(r.0),
            Constant::BitVec { value, width } => dst.mk_bitvec(value, width),
            Constant::String(s) => dst.mk_string(s),
            Constant::FiniteField { value, field } => dst.mk_finite_field(value, field),
            // `Constant` is `#[non_exhaustive]`; all present variants are handled
            // above. A future kind reaching here fails the translate loudly (the
            // FFI guard turns the panic into an honest NULL + error) rather than
            // grafting a wrong value.
            other => unreachable!("graft_term: unhandled constant {other:?}"),
        },
        TermData::Var(name, _) => dst.mk_var(name, sort),
        TermData::App(sym, args) => {
            let new_args: Vec<TermId> = args
                .iter()
                .map(|&a| graft_term(src, dst, a, memo))
                .collect();
            dst.mk_app(sym, new_args, sort)
        }
        TermData::Not(t) => {
            let nt = graft_term(src, dst, t, memo);
            dst.mk_not_raw(nt)
        }
        TermData::Ite(c, t, e) => {
            let nc = graft_term(src, dst, c, memo);
            let nt = graft_term(src, dst, t, memo);
            let ne = graft_term(src, dst, e, memo);
            dst.mk_ite_raw(nc, nt, ne)
        }
        TermData::Let(bindings, body) => {
            let new_bindings: Vec<(String, TermId)> = bindings
                .into_iter()
                .map(|(n, v)| (n, graft_term(src, dst, v, memo)))
                .collect();
            let new_body = graft_term(src, dst, body, memo);
            dst.mk_let(new_bindings, new_body)
        }
        TermData::Forall(vars, body, triggers) => {
            let new_body = graft_term(src, dst, body, memo);
            let new_triggers = graft_triggers(src, dst, &triggers, memo);
            dst.mk_forall_with_triggers(vars, new_body, new_triggers)
        }
        TermData::Exists(vars, body, triggers) => {
            let new_body = graft_term(src, dst, body, memo);
            let new_triggers = graft_triggers(src, dst, &triggers, memo);
            dst.mk_exists_with_triggers(vars, new_body, new_triggers)
        }
        // `TermData` is `#[non_exhaustive]`; all present variants are handled.
        other => unreachable!("graft_term: unhandled term {other:?}"),
    };
    memo.insert(id, new_id);
    new_id
}

/// Graft a quantifier's multi-trigger set into the destination store.
fn graft_triggers(
    src: &TermStore,
    dst: &mut TermStore,
    triggers: &[Vec<TermId>],
    memo: &mut std::collections::HashMap<TermId, TermId>,
) -> Vec<Vec<TermId>> {
    triggers
        .iter()
        .map(|group| {
            group
                .iter()
                .map(|&t| graft_term(src, dst, t, memo))
                .collect()
        })
        .collect()
}

/// Build the formula list of a freshly-constructed Z3 goal from raw assertions.
///
/// This is the decomposition Z3 performs as assertions are inserted into a
/// `goal`, and it backs [`Goal::root_flattened`]:
/// - every top-level `and` is RECURSIVELY split into its conjuncts (so
///   `(and (and a b) c)` becomes `a`, `b`, `c`), preserving left-to-right order;
/// - a trivially-`true` conjunct is dropped (an all-`true` goal is empty, which
///   Z3 prints as a bare `(goal :precision precise :depth n)`);
/// - if any conjunct is `false` the whole goal collapses to the single literal
///   `false` (Z3's inconsistent-goal shape) — `false ∧ anything ≡ false`.
///
/// Duplicate conjuncts are NOT removed: Z3 keeps `a` and `a` as two formulas, so
/// this must too. The transform is equivalence-preserving.
fn flatten_goal_formulas(terms: &TermStore, formulas: &[TermId]) -> Vec<TermId> {
    use ay_core::term::Constant;
    let mut out = Vec::new();
    // Reverse onto a stack so the pop order is the original left-to-right order.
    let mut stack: Vec<TermId> = formulas.iter().rev().copied().collect();
    while let Some(id) = stack.pop() {
        match terms.get(id) {
            TermData::App(sym, args) if sym.name() == "and" && !args.is_empty() => {
                for &arg in args.iter().rev() {
                    stack.push(arg);
                }
            }
            // Drop trivially-true conjuncts (Z3's empty/one-shorter goal).
            TermData::Const(Constant::Bool(true)) => {}
            // A false conjunct makes the whole goal `false` regardless of order.
            TermData::Const(Constant::Bool(false)) => return vec![id],
            _ => out.push(id),
        }
    }
    out
}

/// Split every top-level conjunction in `formulas` into its conjuncts,
/// recursively, mirroring Z3's goal model (which never keeps a top-level `and`
/// as a single formula). A conjunct that is itself an `and` is split in turn;
/// non-conjunction formulas pass through unchanged and in order. Used only to
/// give `size`/`num-exprs` Z3's goal-split semantics — it does not mutate the
/// real goal, so goal printing and tactic depth are unaffected.
fn flatten_top_conjunctions(terms: &TermStore, formulas: &[TermId]) -> Vec<TermId> {
    let mut out = Vec::new();
    // Reverse onto a stack so the pop order is the original left-to-right order.
    let mut stack: Vec<TermId> = formulas.iter().rev().copied().collect();
    while let Some(id) = stack.pop() {
        match terms.get(id) {
            TermData::App(sym, args) if sym.name() == "and" && !args.is_empty() => {
                for &arg in args.iter().rev() {
                    stack.push(arg);
                }
            }
            _ => out.push(id),
        }
    }
    out
}

/// Count the distinct sub-expression nodes reachable from the goal's formulas.
fn count_exprs(terms: &TermStore, formulas: &[TermId]) -> usize {
    let mut seen = std::collections::HashSet::new();
    for &f in formulas {
        walk(terms, f, &mut seen, &mut |_, _| {});
    }
    seen.len()
}

/// DAG walk: visit each reachable term once, invoking `visit(id, data)`.
fn walk(
    terms: &TermStore,
    root: TermId,
    seen: &mut std::collections::HashSet<TermId>,
    visit: &mut impl FnMut(TermId, &TermData),
) {
    let mut stack = vec![root];
    while let Some(id) = stack.pop() {
        if !seen.insert(id) {
            continue;
        }
        let data = terms.get(id);
        visit(id, data);
        match data {
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(t) => stack.push(*t),
            TermData::Ite(c, t, e) => {
                stack.push(*c);
                stack.push(*t);
                stack.push(*e);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings {
                    stack.push(*v);
                }
                stack.push(*body);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => stack.push(*body),
            TermData::Const(_) | TermData::Var(_, _) => {}
            // `TermData` is `#[non_exhaustive]`; any future leaf has no children.
            _ => {}
        }
    }
}

/// A [`Solver`] front-end that applies a [`Tactic`] to the goal before solving.
///
/// Build terms and assert them through [`solver_mut`](Self::solver_mut) (or the
/// convenience [`assert_term`](Self::assert_term)). When you call
/// [`check_sat`](Self::check_sat), the configured tactic is executed first.
/// Public exact-source queries run it on a detached clone of the term store and
/// assertion-root vector, then solve the untouched source roots until the
/// transformed roots have a checked equivalence certificate. This preserves
/// exact proof authority without turning a successful, changed tactic into
/// `Unknown`; an honest tactic failure still returns `Unknown`.
pub struct TacticSolver {
    inner: Solver,
    tactic: Tactic,
}

impl TacticSolver {
    fn inspect_request(&self) -> Result<(TacticOperation, TacticExecutionKind), SolverError> {
        let operation = self.inner.begin_tactic_operation()?;
        let kind = self
            .tactic
            .execution_kind_admitted(operation.admission())
            .map_err(TacticFailure::into_solver_error)?;
        if !operation.validate(&self.inner) {
            return Err(SolverError::TacticFailed(
                "tactic source changed during inspection".into(),
            ));
        }
        Ok((operation, kind))
    }
    /// Mutable access to the underlying solver for building terms and asserting.
    pub fn solver_mut(&mut self) -> &mut Solver {
        &mut self.inner
    }

    /// Shared access to the underlying solver.
    #[must_use]
    pub fn solver(&self) -> &Solver {
        &self.inner
    }

    /// The tactic this solver applies before solving.
    #[must_use]
    pub fn tactic(&self) -> &Tactic {
        &self.tactic
    }

    /// Assert a Boolean constraint into the goal.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::SortMismatch`] if `term` is not a Bool sort.
    #[must_use = "this returns a Result that must be checked"]
    pub fn try_assert_term(&mut self, term: Term) -> Result<(), SolverError> {
        self.inner.try_assert_term(term)
    }

    /// Assert a Boolean constraint into the goal.
    ///
    /// # Panics
    ///
    /// Panics if `term` is not Bool sort. Use [`try_assert_term`] for a
    /// fallible version.
    ///
    /// [`try_assert_term`]: TacticSolver::try_assert_term
    #[allow(clippy::panic)]
    pub fn assert_term(&mut self, term: Term) {
        self.inner.assert_term(term);
    }

    /// The current goal (set of asserted terms).
    #[must_use]
    pub fn assertions(&self) -> Vec<Term> {
        self.inner.assertions()
    }

    /// Execute the tactic, then check satisfiability.
    ///
    /// For a public exact-source query, the tactic runs against a detached clone
    /// of the source goal and term store. Its validation happens, but neither an
    /// unproved changed root vector nor any speculative term-store effects are
    /// committed. The untouched exact source assertions are solved instead. A
    /// future equivalence-certificate path may authorize solving transformed
    /// roots; structural equality or a tactic/shape whitelist never does.
    pub fn check_sat(&mut self) -> VerifiedSolveResult {
        let _read = self.inner.begin_model_evaluation_read();
        let _deadline = tactic_deadline::install(self.inner.timeout());
        // Applying the tactic is itself fallible work in this PUBLIC decision
        // query. Retire the previous model/certificate before it starts, rather
        // than relying on Solver::check_sat (which is never reached on failure).
        self.inner.clear_last_solve_state(true, false);
        let (_operation, kind) = match self.inspect_request() {
            Ok(value) => value,
            Err(error) => {
                self.inner.set_tactic_error_unknown(&error);
                return self.inner.finish_verified_result(SolveResult::Unknown);
            }
        };
        let owned = kind != TacticExecutionKind::Legacy;
        let source_requires_strict = self
            .inner
            .executor
            .active_unsat_query_requires_strict_proof();
        let (source_assertions, source_custody) = if owned && source_requires_strict {
            match self
                .inner
                .executor
                .capture_tactic_source_roots(tactic_deadline::end())
            {
                Ok((roots, scope)) => (roots, Some(scope)),
                Err(origin) => {
                    self.inner.set_internal_error_unknown(&format!(
                        "tactic source admission refused: {origin:?}"
                    ));
                    return self.inner.finish_verified_result(SolveResult::Unknown);
                }
            }
        } else if owned {
            (Vec::new(), None)
        } else {
            (self.inner.executor.context().assertions.clone(), None)
        };
        let tactic_result = if source_requires_strict {
            self.inner
                .validate_tactic_on_detached_goal(&self.tactic, &source_assertions)
        } else {
            self.inner.apply_tactic(&self.tactic)
        };
        if let Err(e) = tactic_result {
            // A transformation failure must never fabricate a verdict; surface
            // it as Unknown rather than silently solving a possibly-wrong goal.
            self.inner
                .record_native_replay_event(NativeReplayEventKind::CheckSat);
            self.inner.set_tactic_error_unknown(&e);
            return self.inner.finish_verified_result(SolveResult::Unknown);
        }
        if source_custody
            .as_ref()
            .is_some_and(|owner| !owner.validate(&self.inner.executor))
            || (source_requires_strict
                && self.inner.executor.context().assertions != source_assertions)
        {
            self.inner
                .record_native_replay_event(NativeReplayEventKind::CheckSat);
            self.inner.set_internal_error_unknown(
                "detached strict-source tactic execution changed the authored assertion roots",
            );
            return self.inner.finish_verified_result(SolveResult::Unknown);
        }
        drop(source_assertions);
        drop(source_custody);
        // This is the caller-visible authored decision, not a solver-internal
        // probe. Enter through the authored wrapper so quantified SAT can use
        // the exact source/declaration capability minted there. This begins the
        // final solve epoch after detached validation; the earlier epoch exists
        // solely to revoke stale artefacts before fallible tactic execution.
        self.inner.check_sat_authored_continuation()
    }

    /// Execute the tactic, then check satisfiability under temporary assumptions.
    ///
    /// The strict-source behavior is the same as [`Self::check_sat`]: the tactic
    /// receives a detached copy of the term store and permanent assertion roots,
    /// while the exact caller-supplied assumptions remain bound to the source
    /// query.
    pub fn check_sat_assuming(&mut self, assumptions: &[Term]) -> VerifiedSolveResult {
        let _read = self.inner.begin_model_evaluation_read();
        let _deadline = tactic_deadline::install(self.inner.timeout());
        // Retire the prior query before even validating caller handles. A stale
        // or foreign assumption is itself a failed public decision attempt and
        // must not leave the preceding assumption map or artefacts observable.
        self.inner.clear_last_solve_state(true, false);
        let (_operation, kind) = match self.inspect_request() {
            Ok(value) => value,
            Err(error) => {
                self.inner.set_tactic_error_unknown(&error);
                return self.inner.finish_verified_result(SolveResult::Unknown);
            }
        };
        let owned = kind != TacticExecutionKind::Legacy;
        let mut assumption_ids = Vec::new();
        if owned {
            if ay_core::term::reserve_counted(
                &mut assumption_ids,
                assumptions.len(),
                _operation.admission(),
            )
            .is_err()
                || !_operation.validate(&self.inner)
            {
                self.inner
                    .set_internal_error_unknown("tactic assumption metadata refused");
                return self.inner.finish_verified_result(SolveResult::Unknown);
            }
            for &term in assumptions {
                match self.inner.resolve_term("tactic_check_sat_assuming", term) {
                    Ok(id) => assumption_ids.push(id),
                    Err(error) => {
                        self.inner.last_executor_error = Some(error.to_string());
                        return self.inner.preflight_unknown(UnknownReason::Incomplete);
                    }
                }
            }
        } else {
            assumption_ids = match self
                .inner
                .resolve_terms("tactic_check_sat_assuming", assumptions)
            {
                Ok(ids) => ids,
                Err(error) => {
                    self.inner.last_executor_error = Some(error.to_string());
                    return self.inner.preflight_unknown(UnknownReason::Incomplete);
                }
            };
        }
        self.inner
            .executor
            .bind_native_query_assumptions(&assumption_ids);
        let source_requires_strict = self
            .inner
            .executor
            .active_unsat_query_requires_strict_proof();
        let (source_assertions, source_custody) = if owned && source_requires_strict {
            match self
                .inner
                .executor
                .capture_tactic_source_roots(tactic_deadline::end())
            {
                Ok((roots, scope)) => (roots, Some(scope)),
                Err(origin) => {
                    self.inner.set_internal_error_unknown(&format!(
                        "tactic source admission refused: {origin:?}"
                    ));
                    return self.inner.finish_verified_result(SolveResult::Unknown);
                }
            }
        } else if owned {
            (Vec::new(), None)
        } else {
            (self.inner.executor.context().assertions.clone(), None)
        };
        let tactic_result = if source_requires_strict {
            self.inner
                .validate_tactic_on_detached_goal(&self.tactic, &source_assertions)
        } else {
            self.inner.apply_tactic(&self.tactic)
        };
        if let Err(e) = tactic_result {
            self.inner
                .record_native_replay_event(NativeReplayEventKind::CheckSatAssuming {
                    assumptions: assumption_ids.clone(),
                });
            self.inner.set_tactic_error_unknown(&e);
            return self.inner.finish_verified_result(SolveResult::Unknown);
        }
        if source_custody
            .as_ref()
            .is_some_and(|owner| !owner.validate(&self.inner.executor))
            || (source_requires_strict
                && self.inner.executor.context().assertions != source_assertions)
        {
            self.inner
                .record_native_replay_event(NativeReplayEventKind::CheckSatAssuming {
                    assumptions: assumption_ids,
                });
            self.inner.set_internal_error_unknown(
                "detached strict-source tactic execution changed the authored assertion roots",
            );
            return self.inner.finish_verified_result(SolveResult::Unknown);
        }
        drop(source_assertions);
        drop(source_custody);
        self.inner.check_sat_assuming_continuation(assumptions)
    }
}

impl Solver {
    /// Begin one explicit native tactic adapter operation; nested calls reuse
    /// the retained original evaluation attempt rather than replenish it.
    pub fn begin_tactic_operation(&self) -> Result<TacticOperation, SolverError> {
        let started_at = std::time::Instant::now();
        let read = self.begin_model_evaluation_read();
        let scope = self
            .executor
            .capture_tactic_construction_until(tactic_deadline::end())
            .map_err(|e| SolverError::TacticFailed(format!("tactic operation refused: {e:?}")))?;
        Ok(TacticOperation {
            scope,
            _read: read,
            started_at,
        })
    }

    /// Decision adapters retire old artifacts on constructor failure while
    /// retaining the same original read through first-origin publication.
    pub fn begin_tactic_operation_for_check(&mut self) -> Result<TacticOperation, SolverError> {
        let _read = self.begin_model_evaluation_read();
        let result = self.begin_tactic_operation();
        if let Err(error) = &result {
            self.set_tactic_error_unknown(error);
        }
        result
    }

    // Capture the original request BEFORE inspecting an arbitrarily large
    // tactic tree. Metadata failure is a failure, never a legacy classification.
    fn inspect_tactic_request(
        &self,
        tactic: &Tactic,
    ) -> Result<(TacticOperation, Requirements), SolverError> {
        let operation = self.begin_tactic_operation()?;
        let requirements = tactic
            .requirements(Some(operation.admission()))
            .map_err(TacticFailure::into_solver_error)?;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "tactic source changed during metadata inspection".into(),
            ));
        }
        Ok((operation, requirements))
    }
    /// Execute `tactic` against a fully detached copy of the term universe and
    /// `source_assertions`.
    ///
    /// The clone preserves every source [`TermId`] while isolating fresh names,
    /// metadata, caches, memory accounting, and appended terms. Both the changed
    /// roots and all speculative term-store effects are discarded because
    /// transformation success, structural equality, and tactic identity are not
    /// equivalence certificates. Honest failure is preserved.
    fn validate_tactic_on_detached_goal(
        &mut self,
        tactic: &Tactic,
        source_assertions: &[TermId],
    ) -> Result<(), SolverError> {
        let _deadline = tactic_deadline::install(self.timeout());
        let (operation, requirements) = self.inspect_tactic_request(tactic)?;
        let TacticOperation {
            scope,
            _read,
            started_at: _,
        } = operation;
        if requirements.solver {
            self.reject_composite_bv_cnf_export(
                "validate_tactic_on_detached_goal(ctx-solver-simplify)",
            )?;
        }
        let owner = scope.admission();
        let bytes = source_assertions
            .len()
            .checked_mul(size_of::<TermId>())
            .ok_or_else(|| SolverError::TacticFailed("detached roots size overflow".into()))?;
        owner.admit(source_assertions.len(), bytes).map_err(|_| {
            SolverError::TacticFailed("detached roots original admission refused".into())
        })?;
        let mut detached_terms = self
            .terms()
            .clone_with_progress(&mut |work, bytes| owner.admit(work, bytes).is_ok())
            .map_err(|_| SolverError::TacticFailed("detached term clone refused".into()))?;
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed(
                "detached source changed during clone".into(),
            ));
        }
        let mut detached_roots = source_assertions.to_vec();
        if requirements.kind != TacticExecutionKind::Legacy {
            let result = (|| {
                let mut detached_goal = Goal::root(detached_roots);
                if requirements.kind == TacticExecutionKind::OwnedModelConversion {
                    detached_goal.capture_model_converter(
                        &detached_terms,
                        self.executor.ctx.symbols_iter(),
                        owner,
                    )?;
                }
                if !scope.validate(&self.executor) {
                    return Err(TacticFailure::new(
                        "detached source changed during converter capture",
                    ));
                }
                tactic.apply_goals_admitted(&mut detached_terms, detached_goal, owner)?;
                Ok(())
            })();
            if !scope.validate(&self.executor) {
                return Err(SolverError::TacticFailed(
                    "tactic original construction fence refused".into(),
                ));
            }
            return result.map_err(TacticFailure::into_solver_error);
        }
        tactic
            .apply_or_fail(&mut detached_terms, &mut detached_roots)
            .map_err(TacticFailure::into_solver_error)?;
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed(
                "detached tactic original request refused".into(),
            ));
        }
        Ok(())
    }

    /// Apply `tactic` to this solver's goal in place.
    ///
    /// Snapshots the current assertions, runs the tactic's transformation in the
    /// solver's own term store, then rebuilds the assertion stack from the
    /// transformed goal via [`try_reset_assertions`](Self::try_reset_assertions)
    /// + re-assert. Routing the rewritten goal back through the normal assert
    /// path keeps `assertions`/`assertions_parsed`/proof provenance aligned, and
    /// preserves declarations.
    ///
    /// No-op (and leaves the goal byte-for-byte unchanged) when the tactic makes
    /// no progress or splits into several subgoals — in each case solving the
    /// original goal yields the identical verdict (the subgoals' disjunction is
    /// equisatisfiable to the original).
    ///
    /// This is public so a front-end that owns a [`Solver`] directly (e.g. the
    /// C FFI's `Z3_mk_solver_from_tactic`) can apply the tactic to that solver's
    /// goal before `check_sat`.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::TacticFailed`] if the tactic HONESTLY FAILS (e.g.
    /// `bit-blast` on an out-of-fragment BV goal) — the caller must surface the
    /// failure rather than solve a goal the tactic did not actually produce. Also
    /// returns an error if resetting or re-asserting fails.
    pub fn apply_tactic(&mut self, tactic: &Tactic) -> Result<(), SolverError> {
        let _deadline = tactic_deadline::install(self.timeout());
        let (operation, requirements) = self.inspect_tactic_request(tactic)?;
        let TacticOperation {
            scope,
            _read,
            started_at: _,
        } = operation;
        if requirements.kind == TacticExecutionKind::OwnedModelConversion {
            return Err(SolverError::TacticFailed(
                "in-place tactic API requires a retained model converter".into(),
            ));
        }
        if requirements.solver {
            self.reject_composite_bv_cnf_export("apply_tactic(ctx-solver-simplify)")?;
        }
        let (goal, changed) = if requirements.kind != TacticExecutionKind::Legacy {
            let count = self.executor.context().assertions.len();
            scope
                .admission()
                .admit(
                    count,
                    count
                        .checked_mul(size_of::<TermId>())
                        .ok_or_else(|| SolverError::TacticFailed("tactic roots overflow".into()))?,
                )
                .map_err(|_| {
                    SolverError::TacticFailed("tactic original root admission refused".into())
                })?;
            if !scope.validate(&self.executor) {
                return Err(SolverError::TacticFailed(
                    "tactic source changed during admission".into(),
                ));
            }
            let mut goal = self.executor.context().assertions.clone();
            let changed = tactic
                .apply_or_fail_admitted(self.terms_mut(), &mut goal, scope.admission())
                .map_err(TacticFailure::into_solver_error)?;
            if !scope.validate(&self.executor) {
                return Err(SolverError::TacticFailed(
                    "tactic source changed during construction".into(),
                ));
            }
            (goal, changed)
        } else {
            let mut goal = self.executor.context().assertions.clone();
            let changed = tactic
                .apply_or_fail(self.terms_mut(), &mut goal)
                .map_err(TacticFailure::into_solver_error)?;
            (goal, changed)
        };
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed(
                "tactic source changed before assertion publication".into(),
            ));
        }
        if !changed {
            return Ok(());
        }
        // Finish immutable construction before the existing authored assertion
        // update. Keep the same read controls/counter alive through that update.
        drop(scope);
        self.try_reset_assertions()?;
        for id in goal {
            let term = self.wrap_term(id);
            self.try_assert_term(term)?;
        }
        Ok(())
    }

    /// Apply `tactic` to an explicit goal (a list of Boolean terms) inside this
    /// solver's term store, WITHOUT touching the solver's own assertion stack.
    ///
    /// This is the front-end primitive behind per-handle C FFI solvers
    /// (`Z3_mk_solver_from_tactic`): each `Z3_solver` handle owns its own logical
    /// assertion list, so its tactic must transform that list rather than the
    /// shared engine's assertion stack. A splitting/no-progress tactic leaves the
    /// goal unchanged (`Ok(false)`); the disjunction of the subgoals is
    /// equisatisfiable to the input, so the eventual verdict is unchanged.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::TacticFailed`] if the tactic HONESTLY FAILS (e.g.
    /// `bit-blast` on an out-of-fragment BV goal). The FFI check path surfaces
    /// this as an error / `unknown` rather than silently solving the untransformed
    /// goal — never a fabricated verdict for a goal the tactic did not blast.
    /// On success, `Ok(true)` means the tactic made progress (the goal changed).
    pub fn apply_tactic_to_goal(
        &mut self,
        tactic: &Tactic,
        goal: &mut Vec<Term>,
    ) -> Result<bool, SolverError> {
        let _deadline = tactic_deadline::install(self.timeout());
        let (operation, requirements) = self.inspect_tactic_request(tactic)?;
        let TacticOperation {
            scope,
            _read,
            started_at: _,
        } = operation;
        if requirements.kind == TacticExecutionKind::OwnedModelConversion {
            return Err(SolverError::TacticFailed(
                "in-place tactic API requires a retained model converter".into(),
            ));
        }
        if requirements.solver {
            self.reject_composite_bv_cnf_export("apply_tactic_to_goal(ctx-solver-simplify)")?;
        }
        if requirements.kind != TacticExecutionKind::Legacy {
            let bytes = goal
                .len()
                .checked_mul(size_of::<TermId>() + size_of::<Term>())
                .ok_or_else(|| SolverError::TacticFailed("tactic input size overflow".into()))?;
            scope.admission().admit(goal.len(), bytes).map_err(|_| {
                SolverError::TacticFailed("tactic original input admission refused".into())
            })?;
            if !scope.validate(&self.executor) {
                return Err(SolverError::TacticFailed(
                    "tactic source changed during admission".into(),
                ));
            }
            let mut ids = self.resolve_terms("apply_tactic_to_goal", goal)?;
            let changed = tactic
                .apply_or_fail_admitted(self.terms_mut(), &mut ids, scope.admission())
                .map_err(TacticFailure::into_solver_error)?;
            if !scope.validate(&self.executor) {
                return Err(SolverError::TacticFailed(
                    "tactic source changed during construction".into(),
                ));
            }
            if changed {
                *goal = ids.into_iter().map(|id| self.wrap_term(id)).collect();
            }
            return Ok(changed);
        }
        let mut ids = self.resolve_terms("apply_tactic_to_goal", goal)?;
        // A solver-invoking pass runs its nested checks under this solver's
        // timeout (measured: `ctx-simplify` in a tactic solver with a 3 s
        // timeout ran 43-50 s before the solver's own check began).
        let changed = tactic
            .apply_or_fail(self.terms_mut(), &mut ids)
            .map_err(TacticFailure::into_solver_error)?;
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed(
                "tactic original request refused before goal publication".into(),
            ));
        }
        if changed {
            *goal = ids.into_iter().map(|id| self.wrap_term(id)).collect();
        }
        Ok(changed)
    }

    /// Apply `tactic` to an explicit goal (a list of Boolean terms) inside this
    /// solver's term store, returning EVERY subgoal's `(formula list, depth)` —
    /// the Z3 apply-result — WITHOUT touching the solver's own assertion stack.
    ///
    /// This is the front-end primitive behind the C-API `Z3_tactic_apply`: it
    /// preserves the full multi-subgoal structure (a `split-clause` yields
    /// several formula lists; a normal tactic yields one; a no-progress run
    /// yields the unchanged goal as a single list). Each subgoal carries its Z3
    /// transformation `depth` (the number of primitive tactic applications that
    /// produced it) so the caller can report `Z3_goal_depth` faithfully. Any
    /// fresh terms minted by the transform (e.g. `nnf`/`tseitin-cnf` aux vars)
    /// live in this solver's term store, so the returned [`Term`]s stay valid for
    /// the caller.
    ///
    /// # Errors
    ///
    /// Returns [`SolverError::TacticFailed`] if the tactic HONESTLY FAILS. The
    /// caller must surface the failure rather than fabricate a subgoal for a
    /// transform that did not run.
    pub fn apply_tactic_subgoals(
        &mut self,
        tactic: &Tactic,
        goal: &[Term],
    ) -> Result<Vec<(Vec<Term>, usize)>, SolverError> {
        let _deadline = tactic_deadline::install(self.timeout());
        let (operation, requirements) = self.inspect_tactic_request(tactic)?;
        let TacticOperation {
            scope,
            _read,
            started_at: _,
        } = operation;
        if requirements.kind == TacticExecutionKind::OwnedModelConversion {
            return Err(SolverError::TacticFailed(
                "this tactic requires the typed model-converting subgoal API".into(),
            ));
        }
        if requirements.solver {
            self.reject_composite_bv_cnf_export("apply_tactic_subgoals(ctx-solver-simplify)")?;
        }
        if requirements.kind != TacticExecutionKind::Legacy {
            let bytes = goal
                .len()
                .checked_mul(size_of::<TermId>())
                .ok_or_else(|| SolverError::TacticFailed("tactic input size overflow".into()))?;
            scope.admission().admit(goal.len(), bytes).map_err(|_| {
                SolverError::TacticFailed("tactic original input admission refused".into())
            })?;
            if !scope.validate(&self.executor) {
                return Err(SolverError::TacticFailed(
                    "tactic source changed during admission".into(),
                ));
            }
            let ids = self.resolve_terms("apply_tactic_subgoals", goal)?;
            let subgoals = tactic
                .apply_goals_admitted(self.terms_mut(), Goal::root(ids), scope.admission())
                .map_err(TacticFailure::into_solver_error)?;
            for g in &subgoals {
                scope
                    .admission()
                    .admit(
                        g.formulas.len(),
                        g.formulas
                            .len()
                            .checked_mul(size_of::<Term>())
                            .ok_or_else(|| {
                                SolverError::TacticFailed("tactic output size overflow".into())
                            })?,
                    )
                    .map_err(|_| {
                        SolverError::TacticFailed("tactic original output admission refused".into())
                    })?;
            }
            scope
                .admission()
                .admit(
                    subgoals.len(),
                    subgoals
                        .len()
                        .checked_mul(size_of::<(Vec<Term>, usize)>())
                        .ok_or_else(|| {
                            SolverError::TacticFailed("tactic output size overflow".into())
                        })?,
                )
                .map_err(|_| {
                    SolverError::TacticFailed("tactic original output admission refused".into())
                })?;
            if !scope.validate(&self.executor) {
                return Err(SolverError::TacticFailed(
                    "tactic source changed during construction".into(),
                ));
            }
            return Ok(subgoals
                .into_iter()
                .map(|g| {
                    (
                        g.formulas
                            .into_iter()
                            .map(|id| self.wrap_term(id))
                            .collect(),
                        g.depth,
                    )
                })
                .collect());
        }
        let ids = self.resolve_terms("apply_tactic_subgoals", goal)?;
        let subgoals = tactic
            .apply_subgoals(self.terms_mut(), Goal::root(ids))
            .map_err(TacticFailure::into_solver_error)?;
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed(
                "tactic original request refused before subgoal publication".into(),
            ));
        }
        Ok(subgoals
            .into_iter()
            .map(|g| {
                (
                    g.formulas
                        .into_iter()
                        .map(|id| self.wrap_term(id))
                        .collect(),
                    g.depth,
                )
            })
            .collect())
    }

    /// Apply with typed reconstruction retained on every returned subgoal.
    /// Reusing a converter requires the same original physical term universe.
    pub fn apply_tactic_subgoals_converted(
        &mut self,
        tactic: &Tactic,
        goal: &[Term],
        depth: usize,
        converter: Option<super::tactic_model::TacticModelConverter>,
    ) -> Result<Vec<TacticSubgoal>, SolverError> {
        let operation = self.begin_tactic_operation()?;
        self.apply_tactic_subgoals_in_operation(&operation, tactic, goal, depth, converter)
    }

    /// Adapter entry retaining exactly the supplied operation's arena through
    /// input decoding, construction, output handles and final publication.
    pub fn apply_tactic_subgoals_in_operation(
        &mut self,
        operation: &TacticOperation,
        tactic: &Tactic,
        goal: &[Term],
        depth: usize,
        converter: Option<super::tactic_model::TacticModelConverter>,
    ) -> Result<Vec<TacticSubgoal>, SolverError> {
        let scope = &operation.scope;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "foreign or stopped tactic operation".into(),
            ));
        }
        let requirements = tactic
            .requirements(Some(scope.admission()))
            .map_err(TacticFailure::into_solver_error)?;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "tactic source changed during inspection".into(),
            ));
        }
        let mut ids = Vec::new();
        ay_core::term::reserve_counted(&mut ids, goal.len(), scope.admission())
            .map_err(|e| SolverError::TacticFailed(e.to_string()))?;
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed("tactic source changed".into()));
        }
        for &term in goal {
            ids.push(self.resolve_term("apply_tactic_subgoals_converted", term)?);
        }
        let converter = if let Some(converter) = converter {
            if !converter.valid(self.terms()) {
                return Err(SolverError::TacticFailed(
                    "foreign or retired model converter".into(),
                ));
            }
            Some(converter)
        } else if requirements.kind == TacticExecutionKind::OwnedModelConversion {
            Some(
                super::tactic_model::TacticModelConverter::capture(
                    self.terms(),
                    &ids,
                    self.executor.ctx.symbols_iter(),
                    scope.admission(),
                )
                .map_err(TacticFailure::into_solver_error)?,
            )
        } else {
            None
        };
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed("tactic source changed".into()));
        }
        let root = Goal {
            formulas: ids,
            depth,
            model_converter: converter,
        };
        let goals = tactic
            .apply_goals_admitted(self.terms_mut(), root, scope.admission())
            .map_err(TacticFailure::into_solver_error)?;
        let mut result = Vec::new();
        ay_core::term::reserve_counted(&mut result, goals.len(), scope.admission())
            .map_err(|e| SolverError::TacticFailed(e.to_string()))?;
        for goal in goals {
            let mut formulas = Vec::new();
            ay_core::term::reserve_counted(&mut formulas, goal.formulas.len(), scope.admission())
                .map_err(|e| SolverError::TacticFailed(e.to_string()))?;
            if !scope.validate(&self.executor) {
                return Err(SolverError::TacticFailed("tactic source changed".into()));
            }
            for id in goal.formulas {
                formulas.push(self.wrap_term(id));
            }
            result.push(TacticSubgoal {
                formulas,
                depth: goal.depth,
                model_converter: goal.model_converter,
            });
        }
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed("tactic source changed".into()));
        }
        Ok(result)
    }

    /// Register the exact auxiliary constants of an owned converted subgoal
    /// for ordinary solver model extraction. This is an explicit declaration
    /// command; it does not assert the goal or supply any model verdict.
    pub fn adopt_tactic_model_constants(
        &mut self,
        converter: &super::tactic_model::TacticModelConverter,
    ) -> Result<(), SolverError> {
        let operation = self.begin_tactic_operation()?;
        self.adopt_tactic_model_constants_in_operation(operation, converter)
    }

    /// Consume the adapter's original read/construction operation into the
    /// declaration-only phase, retaining its same counter, arena and controls.
    pub fn adopt_tactic_model_constants_in_operation(
        &mut self,
        operation: TacticOperation,
        converter: &super::tactic_model::TacticModelConverter,
    ) -> Result<(), SolverError> {
        let (_scope, _read) = self.adopt_tactic_constants_retained(operation, converter)?;
        Ok(())
    }

    fn adopt_tactic_constants_retained(
        &mut self,
        operation: TacticOperation,
        converter: &super::tactic_model::TacticModelConverter,
    ) -> Result<
        (
            crate::executor::TacticDeclarationScope,
            crate::executor::EvaluationReadScope,
        ),
        SolverError,
    > {
        use ay_core::term::{reserve_counted, reserve_map_counted};
        let failure =
            || SolverError::TacticFailed("tactic representative declaration refused".into());
        if !operation.validate(self) || !converter.valid(self.terms()) {
            return Err(failure());
        }
        converter
            .check_namespace(
                self.terms(),
                self.executor.ctx.symbols_iter(),
                &self.adopted_tactic_declarations,
                operation.admission(),
            )
            .map_err(|e| SolverError::TacticFailed(e.message))?;
        let TacticOperation {
            scope,
            _read,
            started_at: _,
        } = operation;
        let declarations = scope
            .into_declarations(&self.executor)
            .map_err(|_| failure())?;
        let owner = declarations.admission();
        for binding in converter.bindings() {
            if binding.field.is_none() {
                continue;
            }
            if !declarations.validate_controls(&self.executor) {
                return Err(failure());
            }
            let id = binding.representative;
            let TermData::Var(name, _) = self.terms().get(id) else {
                return Err(failure());
            };
            let sort = self.terms().sort(id).clone();
            if !matches!(sort, Sort::BitVec(_)) {
                return Err(failure());
            }
            owner
                .admit(
                    name.len()
                        .checked_add(self.adopted_tactic_declarations.len())
                        .ok_or_else(failure)?,
                    0,
                )
                .map_err(|_| failure())?;
            if let Some(existing) = self.var_terms_by_name.get(name) {
                if *existing != id
                    || !self
                        .adopted_tactic_declarations
                        .iter()
                        .any(|(term, _)| *term == id)
                {
                    return Err(failure());
                }
                continue;
            }
            // Four native name copies are made by the canonical adoption
            // operation, plus this temporary borrowed-name escape.
            let bytes = name.len().checked_mul(5).ok_or_else(failure)?;
            owner.admit(bytes, bytes).map_err(|_| failure())?;
            if !declarations.validate_controls(&self.executor) {
                return Err(failure());
            }
            let name = name.clone();
            reserve_map_counted(&mut self.var_names, 1, owner).map_err(|_| failure())?;
            if self.var_terms_by_name.len() == self.var_terms_by_name.capacity() {
                owner
                    .admit(self.var_terms_by_name.capacity(), 0)
                    .map_err(|_| failure())?;
                for key in self.var_terms_by_name.keys() {
                    owner.admit(key.len(), 0).map_err(|_| failure())?;
                }
            }
            reserve_map_counted(&mut self.var_terms_by_name, 1, owner).map_err(|_| failure())?;
            reserve_map_counted(&mut self.var_sorts, 1, owner).map_err(|_| failure())?;
            reserve_counted(&mut self.native_replay_events, 1, owner).map_err(|_| failure())?;
            reserve_counted(&mut self.adopted_tactic_declarations, 1, owner)
                .map_err(|_| failure())?;
            self.executor
                .context_mut_internal()
                .reserve_native_global_constant_adoption(&name, id, owner)
                .map_err(|_| failure())?;
            if !declarations.validate_controls(&self.executor) {
                return Err(failure());
            }
            // No callbacks occur inside the canonical, now prepaid update.
            // It registers this existing id, never a substitute variable.
            self.try_adopt_translated_constant(self.wrap_term(id), sort.clone())?;
            let info = self
                .executor
                .context()
                .symbol_info_with_signature(&name, &[], &sort)
                .ok_or_else(failure)?;
            if info.term != Some(id) {
                return Err(failure());
            }
            self.adopted_tactic_declarations
                .push((id, info.declaration_identity().clone()));
            declarations.recorded_native_declaration(&self.executor);
            if !declarations.validate_controls(&self.executor) {
                return Err(failure());
            }
        }
        if !declarations.validate_controls(&self.executor) {
            return Err(failure());
        }
        Ok((declarations, _read))
    }

    /// Consume a converted single goal using its original operation. The
    /// exact supplied semantic roots replace the old assertion stack; native
    /// replay still checks the actual reduced decision. Reconstruction then
    /// independently checks the converter's original authored roots.
    pub fn check_converted_tactic_goal_in_operation(
        &mut self,
        operation: TacticOperation,
        converter: &super::tactic_model::TacticModelConverter,
        roots: &[Term],
        assumptions: &[Term],
    ) -> Result<TacticDecision, SolverError> {
        let _original_read = operation._read.retain();
        let result =
            self.check_converted_tactic_goal_retained(operation, converter, roots, assumptions);
        if let Err(error) = &result {
            self.set_tactic_error_unknown(error);
        }
        result
    }

    fn check_converted_tactic_goal_retained(
        &mut self,
        operation: TacticOperation,
        converter: &super::tactic_model::TacticModelConverter,
        roots: &[Term],
        assumptions: &[Term],
    ) -> Result<TacticDecision, SolverError> {
        let failure = || SolverError::TacticFailed("converted tactic decision refused".into());
        if self.is_producing_proofs() || !operation.validate(self) {
            return Err(failure());
        }
        // Resolve every handle before the explicit assertion handoff.
        for &term in roots.iter().chain(assumptions) {
            operation.admission().admit(1, 0).map_err(|_| failure())?;
            if !operation.validate(self) {
                return Err(failure());
            }
            if self
                .terms()
                .sort(self.resolve_term("converted tactic decision", term)?)
                != &Sort::Bool
            {
                return Err(failure());
            }
        }
        if !operation.validate(self) {
            return Err(failure());
        }
        let (scope, _read) = self.adopt_tactic_constants_retained(operation, converter)?;
        if !scope.validate_controls(&self.executor) {
            return Err(failure());
        }
        // These are canonical synchronous source commands, not observer
        // callbacks. Record each exact expected source update immediately.
        self.try_reset_assertions()?;
        scope.recorded_native_declaration(&self.executor);
        for &term in roots {
            if !scope.validate_controls(&self.executor) {
                return Err(failure());
            }
            self.try_assert_term(term)?;
            scope.recorded_native_declaration(&self.executor);
        }
        if !scope.validate_controls(&self.executor) {
            return Err(failure());
        }
        let result = if assumptions.is_empty() {
            self.check_sat_authored_continuation()
        } else {
            self.check_sat_assuming_continuation(assumptions)
        };
        if !scope.validate_decision(&self.executor) {
            return Err(failure());
        }
        let model = if matches!(result.result(), SolveResult::Sat) {
            let mut input = self.model().ok_or_else(failure)?.into_inner();
            if !scope.validate_decision(&self.executor) {
                return Err(failure());
            }
            // The native text model lists unused declared constants too.
            // They are completion defaults, not assignments constrained by
            // this reduced goal; a fixed converter must supply those source
            // leaves itself. Keep exactly the actual reduced free leaves.
            let mut ids = Vec::new();
            ay_core::term::reserve_counted(
                &mut ids,
                roots
                    .len()
                    .checked_add(assumptions.len())
                    .ok_or_else(failure)?,
                scope.admission(),
            )
            .map_err(|_| failure())?;
            ids.extend(roots.iter().chain(assumptions).map(|term| term.id()));
            let reachable =
                super::tactic_solve_eqs::reachable(self.terms(), &ids, scope.admission())
                    .map_err(TacticFailure::into_solver_error)?;
            let mut names = Vec::new();
            for (index, present) in reachable.into_iter().enumerate() {
                scope.admission().admit(1, 0).map_err(|_| failure())?;
                if !scope.validate_decision(&self.executor) {
                    return Err(failure());
                }
                if present {
                    let id = TermId(u32::try_from(index).map_err(|_| failure())?);
                    if let TermData::Var(name, _) = self.terms().get(id) {
                        let len = name.len();
                        scope.admission().admit(len, len).map_err(|_| failure())?;
                        ay_core::term::reserve_counted(&mut names, 1, scope.admission())
                            .map_err(|_| failure())?;
                        if !scope.validate_decision(&self.executor) {
                            return Err(failure());
                        }
                        let TermData::Var(name, _) = self.terms().get(id) else {
                            return Err(failure());
                        };
                        names.push(name.clone());
                    }
                }
            }
            let paid = std::cell::Cell::new(true);
            input.retain_names(|name| {
                if scope
                    .admission()
                    .admit(name.len().saturating_add(1), 0)
                    .is_err()
                {
                    paid.set(false);
                    return false;
                }
                names.iter().any(|candidate| {
                    if scope
                        .admission()
                        .admit(name.len().saturating_add(candidate.len()), 0)
                        .is_err()
                    {
                        paid.set(false);
                        return false;
                    }
                    name == candidate
                })
            });
            if !paid.get() || !scope.validate_decision(&self.executor) {
                return Err(failure());
            }
            converter
                .check_namespace(
                    self.terms(),
                    self.executor.ctx.symbols_iter(),
                    &self.adopted_tactic_declarations,
                    scope.admission(),
                )
                .map_err(TacticFailure::into_solver_error)?;
            if !scope.validate_decision(&self.executor) {
                return Err(failure());
            }
            let model = converter
                .convert(self.terms(), &input, scope.admission())
                .map_err(TacticFailure::into_solver_error)?;
            if !scope.validate_decision(&self.executor) {
                return Err(failure());
            }
            Some(model)
        } else {
            None
        };
        Ok(TacticDecision {
            scope,
            _read,
            result,
            model,
        })
    }

    /// Preserve an encoded goal's scalar model DATA when the existing C goal
    /// disabled model reconstruction. Uses the caller's same original owner;
    /// this does not validate or claim the original goal has a model.
    pub fn copy_unconverted_tactic_model_in_operation(
        &self,
        operation: &TacticOperation,
        converter: &super::tactic_model::TacticModelConverter,
        model: &crate::api::Model,
    ) -> Result<crate::api::Model, SolverError> {
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "model copy original owner refused".into(),
            ));
        }
        let result = converter
            .copy_unconverted(self.terms(), model, operation.admission())
            .map_err(|e| SolverError::TacticFailed(e.message))?;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "model copy source changed".into(),
            ));
        }
        Ok(result)
    }

    /// Reconstruct DATA and freshly check the complete original goal using the
    /// independent evaluator under this operation's original controls.
    pub fn convert_tactic_model(
        &self,
        converter: &super::tactic_model::TacticModelConverter,
        model: &crate::api::Model,
    ) -> Result<crate::api::Model, SolverError> {
        let operation = self.begin_tactic_operation()?;
        self.convert_tactic_model_in_operation(&operation, converter, model)
    }

    /// Reuse the adapter's retained original arena; output storage remains
    /// charged until that adapter has completed handle publication.
    pub fn convert_tactic_model_in_operation(
        &self,
        operation: &TacticOperation,
        converter: &super::tactic_model::TacticModelConverter,
        model: &crate::api::Model,
    ) -> Result<crate::api::Model, SolverError> {
        let scope = &operation.scope;
        if !operation.validate(self) {
            return Err(SolverError::TacticFailed(
                "foreign or stopped model conversion operation".into(),
            ));
        }
        converter
            .check_namespace(
                self.terms(),
                self.executor.ctx.symbols_iter(),
                &self.adopted_tactic_declarations,
                scope.admission(),
            )
            .map_err(|e| SolverError::TacticFailed(e.message))?;
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed(
                "model conversion namespace changed".into(),
            ));
        }
        let result = converter
            .convert(self.terms(), model, scope.admission())
            .map_err(|e| SolverError::TacticFailed(e.message))?;
        if !scope.validate(&self.executor) {
            return Err(SolverError::TacticFailed(
                "model conversion source changed".into(),
            ));
        }
        Ok(result)
    }

    /// Evaluate a Z3 *probe* over an explicit goal, returning the REAL double
    /// value Z3's same probe reports for the same goal.
    ///
    /// This is the front-end primitive behind the C-API `Z3_probe_apply`: it
    /// runs the identical probe evaluator the SMT-LIB `(apply (when <probe> …))`
    /// path uses, over `goal`'s formulas interned in this solver's term store,
    /// at the goal's transformation `depth`. Structural probes (`num-consts`,
    /// `num-exprs`, `size`, `depth`, the sort-partitioned const counts) and the
    /// logic-fragment probes (`is-qflia`, `is-qfbv`, `is-propositional`, …) all
    /// return exactly what libz3 returns. Boolean probes return `1.0`/`0.0`.
    #[must_use]
    pub fn apply_probe(&self, probe: &Probe, goal: &[Term], depth: usize) -> f64 {
        let ids = self.require_terms("apply_probe", goal);
        eval_probe_num(probe, self.terms(), &ids, depth)
    }

    /// Deep-copy a goal's formulas from `source`'s term store into THIS solver's
    /// term store, returning the re-interned formula handles.
    ///
    /// Backs the C-API `Z3_goal_translate` for the cross-context case: a `Term`
    /// handle is a term-store index, so a goal built in one context cannot be
    /// read in another without re-interning its whole term DAG here. Each source
    /// node is rebuilt once (memoized on its source id), preserving sharing.
    /// Constants, variables (by name+sort), applications, `not`/`ite`, `let`,
    /// and quantifiers (with triggers) are all reconstructed faithfully; the
    /// result denotes the same formulas over this solver's store.
    #[must_use]
    pub fn translate_terms_from(&mut self, source: &Solver, formulas: &[Term]) -> Vec<Term> {
        let source_ids = source.require_terms("translate_terms_from", formulas);
        self.translate_native_terms_from(source.terms(), &source_ids)
    }

    /// Internal authenticated-arena bridge used by the SMT-LIB proof view.
    /// Source IDs are consumed only against the explicitly borrowed store;
    /// returned capabilities are minted by this destination Solver.
    pub(crate) fn translate_native_terms_from(
        &mut self,
        source: &TermStore,
        source_ids: &[TermId],
    ) -> Vec<Term> {
        // Propagate the `to_real`-shadowed latch for the same reason as the
        // `is_int` latch below. `graft_term` rebuilds applications directly and
        // therefore does not revisit declaration-time shadow detection. Losing
        // this sticky bit would let destination equality/comparison builders
        // assign builtin integrality semantics to a translated user UF named
        // `to_real`, which is a wrong-verdict channel. Carrying it is
        // conservative and can only disable an optimization. (#to-real-bridge)
        if source.to_real_is_shadowed() {
            self.terms_mut().mark_to_real_shadowed();
        }
        // Propagate the `is_int`-shadowed latch across the context boundary. The
        // deep copy below rebuilds a user `App(Named("is_int"), ..)` byte-
        // identically to the builtin integrality predicate, but `graft_term`
        // does not re-run the shadow-marking apply path, so a UF `is_int` built
        // and marked in `source`'s store would otherwise reach THIS store
        // unmarked — re-opening the wrong-UNSAT the `is_int` quantifier
        // eliminator produces (`ForAll([x], is_int(x))` over the UF → `unsat`
        // where z3 exhibits `is_int ≡ λx.true`). The latch is sticky and
        // conservative, so carrying it forward can only fail-close. (#isint-shadow)
        if source.is_int_is_shadowed() {
            self.terms_mut().mark_is_int_shadowed();
        }
        let src = source;
        let mut memo: std::collections::HashMap<TermId, TermId> = std::collections::HashMap::new();
        let out: Vec<TermId> = source_ids
            .iter()
            .map(|&id| graft_term(src, self.terms_mut(), id, &mut memo))
            .collect();
        out.into_iter().map(|id| self.wrap_term(id)).collect()
    }

    /// Record an internal error and mark the next/last result as Unknown.
    ///
    /// Used by tactic front-ends so a transformation failure surfaces honestly
    /// as Unknown(InternalError) instead of a fabricated SAT/UNSAT.
    pub(crate) fn set_internal_error_unknown(&mut self, detail: &str) {
        self.publish_tactic_failure(detail, None);
    }

    // A local tactic limit is negative evidence only. Capture the original
    // owner's first refusal before retiring its read or publishing diagnostics.
    fn set_tactic_error_unknown(&mut self, error: &SolverError) {
        let local = match error {
            SolverError::TacticLimit(crate::api::TacticLimitKind::Deadline) => {
                Some(crate::UnknownOrigin::SolveDeadline)
            }
            SolverError::TacticLimit(crate::api::TacticLimitKind::Work) => {
                Some(crate::UnknownOrigin::DeterministicResourceBudget)
            }
            SolverError::TacticLimit(crate::api::TacticLimitKind::Memory) => {
                Some(crate::UnknownOrigin::MemoryBudget)
            }
            _ => None,
        };
        self.publish_tactic_failure(&error.to_string(), local);
    }

    fn publish_tactic_failure(&mut self, detail: &str, local: Option<crate::UnknownOrigin>) {
        // Capture while the enclosing native read still owns its first cause;
        // dropping that read restores the unrelated parked decision.
        let origin = self
            .executor
            .tactic_refusal_origin()
            .or(local)
            .unwrap_or_else(|| UnknownReason::InternalError.origin());
        // A composite tactic can itself issue internal solves before a later
        // step fails. Revoke both the preceding public result and every partial
        // tactic-probe artefact before publishing Unknown diagnostics.
        self.executor.begin_public_solve(false);
        self.executor.publish_unknown_from_origin(origin);
        self.last_assumptions = None;
        self.last_unknown_reason = Some(origin.reason());
        self.last_executor_error = Some(detail.to_string());
    }
}

#[cfg(test)]
#[path = "tactics_tests.rs"]
mod tests;
