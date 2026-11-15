// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Fully-ground derivations over a problem's ORIGINAL clauses.
//!
//! # Why this exists
//!
//! Preprocessing transforms (condense / array-store forwarding / ground-table
//! read concretization / datatype flattening / dead-parameter slicing) can make
//! a hard problem tractable, but AY never promotes a verdict on transformed
//! evidence. Historically the only Unsafe acceptance path for a transformed
//! counterexample was a FRESH BOUNDED SEARCH on the original clauses
//! (`BmcSolver::replay_confirm_unsafe_on_problem`), which re-enters exactly the
//! theory gap the transforms were introduced to avoid (DT + array + BV
//! combinations): the search returns Unknown and the verdict is discarded.
//!
//! A [`GroundDerivation`] closes that loop WITHOUT any search. It is a concrete
//! derivation of `false` over the original clause list: a topologically ordered
//! list of steps, each naming an original clause index, a total assignment of
//! that clause's variables to concrete [`SmtValue`]s, and the premise steps that
//! justify its body predicate applications.
//!
//! Checking such an object is *pure ground evaluation* — no SMT search, no
//! theory reasoning, no incompleteness. [`validate_ground_derivation`] verifies
//! that every clause constraint evaluates to `true`, that every body-predicate
//! argument tuple equals the corresponding premise's head-argument tuple, and
//! that the root step is a query clause. A derivation that passes is a complete
//! Unsafe proof at the same trust level as
//! `PdrSolver::verify_counterexample`'s Valid verdict — strictly stronger in
//! fact, since it is decided rather than discharged.
//!
//! # Trust model
//!
//! - The validator is ALWAYS re-run against the problem held by the validating
//!   component. A derivation carried on a [`crate::pdr::Counterexample`] proves
//!   nothing by being present; it proves something only when it validates
//!   against THAT component's clause list. There is no trust transfer.
//! - Every failure mode (missing clause, non-ground value, constraint that does
//!   not evaluate to `true`, premise mismatch, ill-founded premise graph) is a
//!   REJECTION. There is no "assume ok" branch.
//! - Rejection is never a soundness event; it only means the caller must fall
//!   back to its previous behavior.
//! - Caller-requested interruption is distinct from proof rejection. It is
//!   terminal for that validation attempt and must not trigger more replay or
//!   solver work under the cancelled budget.

use crate::clause::{ClauseHead, HornClause};
use crate::expr::evaluate_expr;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcProblem, ChcVar};
use ay_core::kani_compat::DetHashMap as FxHashMap;

mod artifact;
pub(crate) mod compact;
pub(crate) use artifact::compact_artifact;
mod control;
use control::GroundValidationControl;
pub(crate) mod clause_map;
pub(crate) mod complete;
mod exact_bindings;
pub(crate) mod forward;
mod lambda_replay;
mod lambda_scope;
pub(crate) mod linear_trace;
pub(crate) mod propositional;
pub(crate) mod reresolve;
pub(crate) mod witness;

/// Maximum derivation-wide work spent authenticating source-clause surfaces.
///
/// One unique source expression occurrence reserves four units: one bounded
/// preflight visit, one variable walk, and the two walks used by ordinary-UF
/// classification. Source structure, sort nodes, names, datatype
/// constructors/selectors, and each bounded cache entry also consume units.
/// Every step then reserves its cached clause's expression/predicate replay,
/// recursive value/sort typechecking, declared bitvector-width work, variables,
/// and UF applications. Producer environments are additionally multiplied by
/// exact incoming head-argument fanout. The accounting is completed before
/// evaluating any derivation step, so repeated references to a hostile clause
/// cannot multiply source walks, datatype lookup, aggregate comparison, or
/// evaluator allocation outside this envelope.
pub const CHC_GROUND_DERIVATION_MAX_SOURCE_WORK: usize = 4_194_304;
/// The per-derivation source-surface envelope for NATIVE validation
/// (`validate_ground_derivation`, i.e. derivations AY built in-process and
/// re-checks on a problem it holds in memory), 64× the wire cap — the same
/// factor the whole-problem preflight already uses in native mode
/// (`artifact::source_identity::NATIVE_WHOLE_SOURCE_WORK`). The wire cap
/// prices hostile artifacts; the native envelope keeps the walk finite while
/// admitting the tree-expanded transition clauses of preprocessed
/// (inlined / local-variable-eliminated) problems, whose derivations the
/// back-translation passes self-check on their input problems and every
/// acceptance site re-validates on the original clauses
/// (LRACORE_CH4B_owner_2026-09-23 §3.4: 16 kind2 counterexamples per LIA
/// 100-sample were refused at the wire cap, never on semantics). Wire
/// callers (`validate_ground_derivation_with_control` with a wire control)
/// are unchanged.
pub(crate) const CHC_GROUND_DERIVATION_NATIVE_SOURCE_WORK: usize =
    CHC_GROUND_DERIVATION_MAX_SOURCE_WORK * 64;
pub(crate) const CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH: usize = 512;
const CHC_GROUND_DERIVATION_MAX_VALUE_DEPTH: usize = 128;

fn bitvector_width_replay_work(width: u32) -> Result<usize, GroundSourceSurfaceError> {
    if width == 0 || width > crate::MAX_BITVECTOR_WIDTH {
        return Err(GroundSourceSurfaceError::SourceWorkLimitExceeded);
    }
    usize::try_from((u64::from(width) + 7) / 8)
        .map_err(|_| GroundSourceSurfaceError::SourceWorkLimitExceeded)
}

fn source_sort_typecheck_work(
    root: &crate::ChcSort,
    control: &mut GroundValidationControl<'_>,
) -> Result<usize, GroundSourceSurfaceError> {
    let mut work = 0usize;
    let mut stack = vec![(root, 1usize)];
    while let Some((sort, depth)) = stack.pop() {
        control.poll()?;
        if depth > CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
            return Err(GroundSourceSurfaceError::SourceWorkLimitExceeded);
        }
        let mut add = |amount: usize| -> Result<(), GroundSourceSurfaceError> {
            work = work
                .checked_add(amount)
                .filter(|work| *work <= CHC_GROUND_DERIVATION_MAX_SOURCE_WORK)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            Ok(())
        };
        match sort {
            crate::ChcSort::Array(index, value) => {
                add(32usize
                    .checked_mul(depth)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?)?;
                let child_depth = depth
                    .checked_add(1)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                stack.push((index, child_depth));
                stack.push((value, child_depth));
            }
            crate::ChcSort::Datatype { name, constructors } => {
                add(name
                    .len()
                    .checked_add(constructors.len())
                    .and_then(|amount| amount.checked_mul(depth))
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?)?;
                let child_depth = depth
                    .checked_add(1)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                for constructor in constructors.iter() {
                    control.poll()?;
                    add(constructor
                        .name
                        .len()
                        .checked_add(constructor.selectors.len())
                        .and_then(|amount| amount.checked_mul(depth))
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?)?;
                    for selector in &constructor.selectors {
                        control.poll()?;
                        add(selector
                            .name
                            .len()
                            .checked_mul(depth)
                            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?)?;
                        stack.push((&selector.sort, child_depth));
                    }
                }
            }
            crate::ChcSort::Uninterpreted(name) => add(name
                .len()
                .checked_mul(depth)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?)?,
            crate::ChcSort::Bool
            | crate::ChcSort::Int
            | crate::ChcSort::Real
            | crate::ChcSort::BitVec(_) => add(depth)?,
        }
    }
    control.poll()?;
    Ok(work.max(1))
}

pub use artifact::{
    validate_chc_ground_derivation_artifact, validate_chc_ground_derivation_artifact_v2,
    validate_chc_ground_derivation_artifact_v2_with_progress,
    validate_chc_ground_derivation_artifact_with_progress, ChcGroundDerivationArtifactError,
    ChcGroundDerivationArtifactErrorReason, ChcGroundDerivationStepView,
    ChcValidatedGroundDerivation, CHC_GROUND_DERIVATION_ARTIFACT_MAX_BINDINGS,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_BYTES, CHC_GROUND_DERIVATION_ARTIFACT_MAX_CLAUSES,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_NESTING_DEPTH,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREDICATES,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_PREMISE_EDGES, CHC_GROUND_DERIVATION_ARTIFACT_MAX_STEPS,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_STRING_OR_TOKEN_BYTES,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_UF_OBSERVATIONS,
    CHC_GROUND_DERIVATION_ARTIFACT_MAX_VALUE_NODES, CHC_GROUND_DERIVATION_ARTIFACT_ROLE,
    CHC_GROUND_DERIVATION_ARTIFACT_SCHEMA, CHC_GROUND_DERIVATION_ARTIFACT_V2_ROLE,
    CHC_GROUND_DERIVATION_ARTIFACT_V2_SCHEMA,
};

#[cfg(test)]
mod tests;

/// Bound playback source using unchanged wire-artifact admission.
/// This grants no cumulative storage or native solver authority.
pub(crate) fn preflight_playback_source_with_progress(
    problem: &ChcProblem,
    progress: &mut dyn FnMut() -> bool,
) -> Result<(), ChcGroundDerivationArtifactError> {
    let mut control = GroundValidationControl::new(progress);
    artifact::validate_problem_bounds_with_control(problem, &mut control)
}

/// One step of a [`GroundDerivation`]: a single original clause fired under a
/// completely concrete variable assignment.
#[derive(Debug, Clone)]
pub(crate) struct GroundDerivationStep {
    /// Index into `ChcProblem::clauses()` of the ORIGINAL problem.
    pub(crate) clause_index: usize,
    /// Total assignment for this clause instance: every variable occurring in
    /// the clause's body constraint, body predicate arguments and head
    /// arguments must be bound to a concrete value.
    pub(crate) env: FxHashMap<String, SmtValue>,
    /// Premise step indices, positionally aligned with
    /// `clause.body.predicates`. Must be strictly less than this step's own
    /// index (the derivation is stored in topological order, which makes
    /// well-foundedness structural rather than a graph search).
    pub(crate) premises: Vec<usize>,
}

/// A concrete derivation of `false` over a problem's original clauses.
#[derive(Debug, Clone, Default)]
pub(crate) struct GroundDerivation {
    /// Derivation steps in topological order (premises precede consumers).
    pub(crate) steps: Vec<GroundDerivationStep>,
    /// Index of the root step. Its clause must be a query (`head = false`).
    pub(crate) query_step: usize,
}

impl GroundDerivation {
    /// Number of steps in the derivation.
    pub(crate) fn len(&self) -> usize {
        self.steps.len()
    }

    /// Whether the derivation has no steps (always invalid).
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.steps.is_empty()
    }
}

/// Why a candidate ground derivation was rejected.
///
/// No variant grants proof authority. Interruption is distinct from an invalid
/// derivation and must remain terminal for the caller's cancelled attempt.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum GroundDerivationError {
    /// The caller refused cooperative progress. This is not a proof rejection.
    Interrupted,
    /// The derivation has no steps.
    Empty,
    /// `query_step` is out of range.
    RootOutOfRange,
    /// A step names a clause index the problem does not have.
    ClauseOutOfRange { step: usize, clause_index: usize },
    /// A premise index is not strictly smaller than the consuming step index
    /// (would permit a self-justifying or cyclic derivation).
    PremiseNotWellFounded { step: usize, premise: usize },
    /// A step's premise count does not match its clause's body predicate count.
    PremiseArityMismatch {
        step: usize,
        expected: usize,
        found: usize,
    },
    /// A premise step derives a different predicate than the body position
    /// requires (or derives nothing, i.e. it is itself a query).
    PremisePredicateMismatch { step: usize, position: usize },
    /// The root step's clause is not a query clause.
    RootNotQuery { step: usize },
    /// A non-root step's clause is a query clause (queries derive nothing, so
    /// they cannot serve as a premise).
    NonRootIsQuery { step: usize },
    /// A clause constraint did not evaluate to a concrete Boolean under the
    /// step's environment (unbound variable, uninterpreted function, overflow,
    /// unsupported operator, ...).
    ConstraintNotGround { step: usize },
    /// A clause constraint evaluated concretely to `false`.
    ConstraintFalse { step: usize },
    /// A source variable has no binding in its derivation step.
    VariableBindingMissing { step: usize, variable: usize },
    /// A source variable binding is not an exact canonical inhabitant of its
    /// declared source sort.
    VariableBindingSortMismatch { step: usize, variable: usize },
    /// A body-predicate argument or the corresponding premise head argument did
    /// not evaluate to a concrete value.
    ArgumentNotGround {
        step: usize,
        position: usize,
        argument: usize,
    },
    /// A body-predicate argument's value differs from the premise's head
    /// argument value at the same position.
    ArgumentMismatch {
        step: usize,
        position: usize,
        argument: usize,
    },
    /// A step is not reachable from the root (padding / unrelated material).
    UnreachableStep { step: usize },
    /// The selected source clause's ordinary-UF surface could not be classified
    /// within the fixed expression-resource bounds.
    UfSurfaceInvalid { step: usize },
    /// One source ordinary-UF application lacked an exact, well-sorted finite
    /// observation under this step's environment.
    UfObservationNotGround { step: usize, application: usize },
    /// Two applications of one ordinary UF at equal concrete argument tuples
    /// were assigned different results.
    UfCongruenceViolation { step: usize, application: usize },
    /// Canonical source-surface authentication exceeded its fixed
    /// derivation-wide work envelope.
    SourceWorkLimitExceeded,
    /// The live source problem has an inconsistent ordinary-UF signature or
    /// collides with the typed source term namespace.
    InvalidSourceProblem,
}

impl std::fmt::Display for GroundDerivationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Interrupted => write!(f, "ground derivation validation interrupted"),
            Self::Empty => write!(f, "empty derivation"),
            Self::RootOutOfRange => write!(f, "root step index out of range"),
            Self::ClauseOutOfRange { step, clause_index } => write!(
                f,
                "step {step} names clause index {clause_index} which the problem does not have"
            ),
            Self::PremiseNotWellFounded { step, premise } => write!(
                f,
                "step {step} premises step {premise} (not strictly earlier: ill-founded)"
            ),
            Self::PremiseArityMismatch {
                step,
                expected,
                found,
            } => write!(
                f,
                "step {step} has {found} premises but its clause body has {expected} predicates"
            ),
            Self::PremisePredicateMismatch { step, position } => write!(
                f,
                "step {step} body position {position} is justified by a premise deriving a \
                 different predicate"
            ),
            Self::RootNotQuery { step } => {
                write!(f, "root step {step} does not fire a query clause")
            }
            Self::NonRootIsQuery { step } => {
                write!(f, "non-root step {step} fires a query clause")
            }
            Self::ConstraintNotGround { step } => write!(
                f,
                "step {step} constraint does not evaluate to a concrete Boolean"
            ),
            Self::ConstraintFalse { step } => {
                write!(f, "step {step} constraint evaluates to false")
            }
            Self::VariableBindingMissing { step, variable } => write!(
                f,
                "step {step} source variable {variable} has no ground binding"
            ),
            Self::VariableBindingSortMismatch { step, variable } => write!(
                f,
                "step {step} source variable {variable} binding is noncanonical or has the wrong sort"
            ),
            Self::ArgumentNotGround {
                step,
                position,
                argument,
            } => write!(
                f,
                "step {step} body position {position} argument {argument} does not evaluate to a \
                 concrete value"
            ),
            Self::ArgumentMismatch {
                step,
                position,
                argument,
            } => write!(
                f,
                "step {step} body position {position} argument {argument} disagrees with its \
                 premise"
            ),
            Self::UnreachableStep { step } => {
                write!(f, "step {step} is not reachable from the root step")
            }
            Self::UfSurfaceInvalid { step } => write!(
                f,
                "step {step} source clause ordinary-UF surface is invalid or exceeds bounds"
            ),
            Self::UfObservationNotGround { step, application } => write!(
                f,
                "step {step} ordinary-UF application {application} has no exact ground observation"
            ),
            Self::UfCongruenceViolation { step, application } => write!(
                f,
                "step {step} ordinary-UF application {application} violates finite congruence"
            ),
            Self::SourceWorkLimitExceeded => write!(
                f,
                "ground derivation source-surface work exceeds its validation envelope (wire cap {}, native {})",
                CHC_GROUND_DERIVATION_MAX_SOURCE_WORK,
                CHC_GROUND_DERIVATION_NATIVE_SOURCE_WORK
            ),
            Self::InvalidSourceProblem => write!(
                f,
                "ground derivation source problem has invalid function signatures or namespace"
            ),
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GroundSourceSurfaceError {
    Interrupted,
    ClauseOutOfRange,
    SourceWorkLimitExceeded,
    InvalidVariableSurface,
    PrivateSourceNamespace,
    InvalidUfSurface,
}

impl From<control::GroundValidationInterrupted> for GroundSourceSurfaceError {
    fn from(_: control::GroundValidationInterrupted) -> Self {
        Self::Interrupted
    }
}

pub(crate) struct GroundClauseSurface {
    pub(crate) variables: Vec<ChcVar>,
    /// Conservative recursive sort/type-validation work aligned with
    /// `variables`.
    variable_typecheck_work: Vec<usize>,
    pub(crate) uf_applications: Vec<ChcExpr>,
    pub(crate) uf_argument_occurrences: usize,
    pub(crate) value_replay_occurrences: usize,
    /// Conservative source work repeated by one native replay of this clause.
    pub(crate) replay_work: usize,
}

/// Per-pass cache for canonical source material used by ground evidence.
///
/// Entries are indexed by the immutable source-clause ordinal. A clause is
/// walked at most once per encode, decode, or native-validation pass; repeated
/// derivation steps borrow the same owned canonical vectors.
pub(crate) struct GroundSourceSurfaceCache<'a> {
    problem: &'a ChcProblem,
    entries: FxHashMap<usize, GroundClauseSurface>,
    work_used: usize,
    work_limit: usize,
    #[cfg(test)]
    walked_clauses: usize,
    #[cfg(test)]
    profiled_typecheck_bindings: usize,
}

impl<'a> GroundSourceSurfaceCache<'a> {
    pub(crate) fn new(problem: &'a ChcProblem) -> Self {
        Self::with_work_limit(problem, CHC_GROUND_DERIVATION_MAX_SOURCE_WORK)
    }

    fn with_work_limit(problem: &'a ChcProblem, work_limit: usize) -> Self {
        Self {
            problem,
            // Deliberately sparse: native validation is crate-private and does
            // not impose the artifact clause-count bound. A tiny derivation
            // over a huge in-memory problem must allocate only for clauses it
            // actually selects.
            entries: FxHashMap::default(),
            work_used: 0,
            work_limit,
            #[cfg(test)]
            walked_clauses: 0,
            #[cfg(test)]
            profiled_typecheck_bindings: 0,
        }
    }

    #[cfg(test)]
    pub(crate) fn with_work_limit_for_test(problem: &'a ChcProblem, work_limit: usize) -> Self {
        Self::with_work_limit(problem, work_limit)
    }

    #[cfg(test)]
    pub(crate) fn walked_clause_count(&self) -> usize {
        self.walked_clauses
    }

    #[cfg(test)]
    pub(crate) fn work_used_for_test(&self) -> usize {
        self.work_used
    }

    #[cfg(test)]
    pub(crate) fn profiled_typecheck_bindings_for_test(&self) -> usize {
        self.profiled_typecheck_bindings
    }

    fn charge(&mut self, work: usize) -> Result<(), GroundSourceSurfaceError> {
        self.work_used = self
            .work_used
            .checked_add(work)
            .filter(|used| *used <= self.work_limit)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        Ok(())
    }

    /// Work charged so far (diagnostics only).
    pub(crate) fn work_used(&self) -> usize {
        self.work_used
    }

    /// This cache's envelope (diagnostics only).
    pub(crate) fn work_limit(&self) -> usize {
        self.work_limit
    }

    fn reserve_unique_clause_walks(
        &mut self,
        clause: &HornClause,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<(usize, Vec<ChcVar>, Vec<usize>, usize), GroundSourceSurfaceError> {
        const UNIQUE_NODE_WALKS: usize = 4;

        // Each source walker also visits the clause and every body-predicate
        // position even when all applications are nullary. Reserve that work
        // before iterating the potentially hostile source vectors.
        let structural_occurrences = clause
            .body
            .predicates
            .len()
            .checked_add(1)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        self.charge(
            structural_occurrences
                .checked_mul(UNIQUE_NODE_WALKS)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
        )?;

        let mut stack = Vec::new();
        let mut variables_by_name: FxHashMap<String, crate::ChcSort> = FxHashMap::default();
        let mut unique_variable_name_bytes = 0usize;
        if let Some(constraint) = &clause.body.constraint {
            self.push_pending_source_expr(
                &mut stack,
                constraint,
                0,
                1,
                UNIQUE_NODE_WALKS,
                control,
            )?;
        }
        for (_, arguments) in &clause.body.predicates {
            control.poll()?;
            for argument in arguments {
                self.push_pending_source_expr(
                    &mut stack,
                    argument,
                    0,
                    1,
                    UNIQUE_NODE_WALKS,
                    control,
                )?;
            }
        }
        if let ClauseHead::Predicate(_, arguments) = &clause.head {
            for argument in arguments {
                self.push_pending_source_expr(
                    &mut stack,
                    argument,
                    0,
                    1,
                    UNIQUE_NODE_WALKS,
                    control,
                )?;
            }
        }
        let mut expression_occurrences = 0usize;
        let mut replay_work = structural_occurrences;
        let mut function_occurrences = 0usize;
        let mut nested_identity_work = 0usize;
        let mut bounded_expression_sorts = Vec::new();
        let mut bounded_lambdas = Vec::new();
        while let Some((expression, function_ancestors, depth, binding_scope)) = stack.pop() {
            control.poll()?;
            if depth > CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
                return Err(GroundSourceSurfaceError::SourceWorkLimitExceeded);
            }
            self.charge(UNIQUE_NODE_WALKS)?;
            expression_occurrences = expression_occurrences
                .checked_add(1)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            replay_work = replay_work
                .checked_add(1)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            // `ChcExpr::sort` recursively derives operator outputs. Charge its
            // depth-dependent traversal first, then charge every bitvector
            // output by declared storage width. This covers Int2Bv,
            // extensions, concat/repeat, and later BvNot masks even when all
            // operand payloads are zero.
            self.charge(
                64usize
                    .checked_mul(depth)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            )?;
            bounded_expression_sorts.push(expression);
            let function_memberships = function_ancestors
                .checked_add(usize::from(matches!(expression, ChcExpr::FuncApp(..))))
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            if matches!(expression, ChcExpr::FuncApp(..)) {
                function_occurrences = function_occurrences
                    .checked_add(1)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            }
            let identity_unit = match expression {
                ChcExpr::ArrayLambda(_) => Some(64),
                ChcExpr::Var(variable) => variable.name.len().checked_add(64),
                ChcExpr::FuncApp(name, _, arguments) => name
                    .len()
                    .checked_add(arguments.len())
                    .and_then(|work| work.checked_add(96)),
                ChcExpr::PredicateApp(name, _, _) | ChcExpr::IsTesterMarker(name) => {
                    name.len().checked_add(64)
                }
                _ => Some(64),
            }
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            let identity_work = identity_unit
                .checked_mul(function_memberships)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            self.charge(identity_work)?;
            nested_identity_work = nested_identity_work
                .checked_add(identity_work)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            match expression {
                ChcExpr::ArrayLambda(lambda) => {
                    let cost = self.reserve_lambda_metadata(lambda, control)?;
                    replay_work = replay_work
                        .checked_add(cost)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                    bounded_lambdas.push(lambda.as_ref());
                }
                ChcExpr::Var(variable) => {
                    self.charge(variable.name.len())?;
                    replay_work = replay_work
                        .checked_add(variable.name.len())
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                    let sort_work = self.reserve_source_sort(&variable.sort, control)?;
                    let nested_sort_work = sort_work
                        .checked_mul(function_memberships)
                        .and_then(|work| work.checked_mul(32))
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                    self.charge(nested_sort_work)?;
                    nested_identity_work = nested_identity_work
                        .checked_add(nested_sort_work)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                    if let Some(lambda) = binding_scope {
                        self.reserve_bound_variable(lambda, variable, sort_work)?;
                    } else if let Some(previous_sort) = variables_by_name.get(&variable.name) {
                        if previous_sort != &variable.sort {
                            return Err(GroundSourceSurfaceError::InvalidVariableSurface);
                        }
                    } else {
                        unique_variable_name_bytes = unique_variable_name_bytes
                            .checked_add(variable.name.len())
                            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                        variables_by_name.insert(variable.name.clone(), variable.sort.clone());
                    }
                }
                ChcExpr::FuncApp(name, return_sort, arguments) => {
                    // Bound-code observations need instantiated argument keys.
                    // Until that accounting exists, keep this path closed.
                    if binding_scope.is_some() {
                        return Err(GroundSourceSurfaceError::InvalidUfSurface);
                    }
                    let signature_work = name
                        .len()
                        .checked_add(arguments.len())
                        .and_then(|work| work.checked_add(2))
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                    self.charge(signature_work)?;
                    replay_work = replay_work
                        .checked_add(signature_work)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                    let sort_work = self.reserve_source_sort(return_sort, control)?;
                    let nested_sort_work = sort_work
                        .checked_mul(function_memberships)
                        .and_then(|work| work.checked_mul(32))
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                    self.charge(nested_sort_work)?;
                    nested_identity_work = nested_identity_work
                        .checked_add(nested_sort_work)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                }
                ChcExpr::PredicateApp(name, _, _) | ChcExpr::IsTesterMarker(name) => {
                    self.charge(name.len())?;
                    replay_work = replay_work
                        .checked_add(name.len())
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                }
                ChcExpr::ConstArray(key_sort, _) | ChcExpr::ConstArrayMarker(key_sort) => {
                    let sort_work = self.reserve_source_sort(key_sort, control)?;
                    let nested_sort_work = sort_work
                        .checked_mul(function_memberships)
                        .and_then(|work| work.checked_mul(32))
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                    self.charge(nested_sort_work)?;
                    nested_identity_work = nested_identity_work
                        .checked_add(nested_sort_work)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Op(_, _) => {}
            }
            let children: &[std::sync::Arc<ChcExpr>] = match expression {
                ChcExpr::Op(_, arguments)
                | ChcExpr::PredicateApp(_, _, arguments)
                | ChcExpr::FuncApp(_, _, arguments) => arguments,
                ChcExpr::ArrayLambda(lambda) => {
                    self.charge(UNIQUE_NODE_WALKS)?;
                    stack.push((lambda.body(), function_memberships, depth + 1, Some(lambda)));
                    lambda.captures()
                }
                ChcExpr::ConstArray(_, value) => std::slice::from_ref(value),
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::Var(_)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => &[],
            };
            let child_depth = depth
                .checked_add(1)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            stack
                .len()
                .checked_add(children.len())
                .and_then(|nodes| nodes.checked_mul(UNIQUE_NODE_WALKS))
                .and_then(|work| self.work_used.checked_add(work))
                .filter(|projected| *projected <= self.work_limit)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            for child in children {
                control.poll()?;
                stack.push((
                    child.as_ref(),
                    function_memberships,
                    child_depth,
                    binding_scope,
                ));
            }
        }

        for lambda in &bounded_lambdas {
            control.poll()?;
            let typed = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
                lambda.captures_are_well_typed()
            }))
            .map_err(|_| GroundSourceSurfaceError::InvalidVariableSurface)?;
            control.poll()?;
            if !typed {
                return Err(GroundSourceSurfaceError::InvalidVariableSurface);
            }
        }
        // Only derive recursive operator sorts after the complete iterative
        // source walk has established every expression/sort depth bound.
        // `catch_unwind` contains malformed typed nodes; it is not relied on
        // for stack safety.
        for expression in bounded_expression_sorts {
            control.poll()?;
            let expression_sort =
                std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| expression.sort()));
            control.poll()?;
            let expression_sort =
                expression_sort.map_err(|_| GroundSourceSurfaceError::InvalidUfSurface)?;
            if let crate::ChcSort::BitVec(width) = expression_sort {
                let width_work = bitvector_width_replay_work(width)?;
                self.charge(width_work)?;
                replay_work = replay_work
                    .checked_add(width_work)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            }
        }

        if !bounded_lambdas.is_empty() {
            let profile = self.reserve_lambda_replay(clause, control)?;
            // Every UF observation can reevaluate an argument subtree, then
            // native replay has two evaluator and four normalization phases.
            // Keep expanded aggregate reads under the same per-step envelope.
            let rounds = function_occurrences
                .checked_add(1)
                .and_then(|rounds| rounds.checked_mul(6))
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            replay_work = replay_work
                .checked_add(
                    profile
                        .work
                        .checked_mul(rounds)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                )
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            expression_occurrences = expression_occurrences
                .checked_add(
                    profile
                        .value_occurrences
                        .checked_mul(rounds)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                )
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        }
        let function_sort_rounds = function_occurrences
            .checked_sub(1)
            .map_or(0, |maximum_index| {
                usize::BITS as usize - maximum_index.leading_zeros() as usize
            });
        let collector_identity_passes = function_sort_rounds
            .checked_add(2)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        self.charge(
            nested_identity_work
                .checked_mul(collector_identity_passes)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
        )?;
        replay_work = replay_work
            .checked_add(
                nested_identity_work
                    .checked_mul(3)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            )
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;

        let mut variables = variables_by_name
            .into_iter()
            .map(|(name, sort)| ChcVar::new(name, sort))
            .collect::<Vec<_>>();
        let sort_rounds = variables.len().checked_sub(1).map_or(0, |maximum_index| {
            usize::BITS as usize - maximum_index.leading_zeros() as usize
        });
        let sort_work = unique_variable_name_bytes
            .checked_add(variables.len())
            .and_then(|work| work.checked_mul(sort_rounds))
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        self.charge(sort_work)?;
        control.poll()?;
        variables.sort_by(|left, right| left.name.cmp(&right.name));
        control.poll()?;
        // Codec/native type validation scans datatype constructor tables and
        // nested selector sorts once per variable value and per reused step.
        // Cache an aligned cost now, after the bounded iterative source walk,
        // so repeated clauses cannot multiply a wide datatype declaration
        // outside the fixed envelope.
        let mut variable_typecheck_work = Vec::with_capacity(variables.len());
        for variable in &variables {
            let work = source_sort_typecheck_work(&variable.sort, control)?;
            self.charge(work)?;
            variable_typecheck_work.push(work);
        }
        replay_work = replay_work
            .checked_add(
                variable_typecheck_work
                    .iter()
                    .try_fold(0usize, |total, work| total.checked_add(*work))
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            )
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        control.poll()?;
        Ok((
            expression_occurrences,
            variables,
            variable_typecheck_work,
            replay_work,
        ))
    }

    fn reserve_source_sort(
        &mut self,
        root: &crate::ChcSort,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<usize, GroundSourceSurfaceError> {
        let starting_work = self.work_used;
        let mut stack = vec![(root, 1usize)];
        while let Some((sort, depth)) = stack.pop() {
            control.poll()?;
            if depth > CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
                return Err(GroundSourceSurfaceError::SourceWorkLimitExceeded);
            }
            // Derived sort formatting, hashing, ordering, and equality expand
            // nested structure bottom-up. Weight each occurrence by its sort
            // ancestor depth so a deep shared datatype DAG cannot hide
            // quadratic work behind Arc identity. Occurrences are deliberately
            // not deduplicated: the downstream derived operations do not
            // deduplicate them either. The depth/work caps terminate cycles.
            self.charge(
                32usize
                    .checked_mul(depth)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            )?;
            let child_depth = depth
                .checked_add(1)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            match sort {
                crate::ChcSort::Array(index, value) => {
                    self.charge(
                        2usize
                            .checked_mul(depth)
                            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                    )?;
                    stack
                        .len()
                        .checked_add(2)
                        .and_then(|work| self.work_used.checked_add(work))
                        .filter(|projected| *projected <= self.work_limit)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                    stack.push((index, child_depth));
                    stack.push((value, child_depth));
                }
                crate::ChcSort::Datatype { name, constructors } => {
                    self.charge(
                        name.len()
                            .checked_add(constructors.len())
                            .and_then(|work| work.checked_mul(depth))
                            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                    )?;
                    for constructor in constructors.iter() {
                        control.poll()?;
                        self.charge(
                            constructor
                                .name
                                .len()
                                .checked_add(constructor.selectors.len())
                                .and_then(|work| work.checked_mul(depth))
                                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                        )?;
                        for selector in &constructor.selectors {
                            control.poll()?;
                            self.charge(
                                selector
                                    .name
                                    .len()
                                    .checked_mul(depth)
                                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                            )?;
                            stack.push((&selector.sort, child_depth));
                        }
                    }
                }
                crate::ChcSort::Uninterpreted(name) => self.charge(
                    name.len()
                        .checked_mul(depth)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                )?,
                crate::ChcSort::BitVec(width) => self.charge(
                    bitvector_width_replay_work(*width)?
                        .checked_mul(depth)
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                )?,
                crate::ChcSort::Bool | crate::ChcSort::Int | crate::ChcSort::Real => {}
            }
        }
        control.poll()?;
        self.work_used
            .checked_sub(starting_work)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)
    }

    fn push_pending_source_expr<'b>(
        &self,
        stack: &mut Vec<(
            &'b ChcExpr,
            usize,
            usize,
            Option<&'b crate::expr::ChcArrayLambda>,
        )>,
        expression: &'b ChcExpr,
        function_ancestors: usize,
        depth: usize,
        work_per_node: usize,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<(), GroundSourceSurfaceError> {
        control.poll()?;
        if depth > CHC_GROUND_DERIVATION_MAX_SOURCE_DEPTH {
            return Err(GroundSourceSurfaceError::SourceWorkLimitExceeded);
        }
        stack
            .len()
            .checked_add(1)
            .and_then(|nodes| nodes.checked_mul(work_per_node))
            .and_then(|work| self.work_used.checked_add(work))
            .filter(|projected| *projected <= self.work_limit)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        stack.push((expression, function_ancestors, depth, None));
        Ok(())
    }

    pub(crate) fn surface(
        &mut self,
        clause_index: usize,
    ) -> Result<&GroundClauseSurface, GroundSourceSurfaceError> {
        self.surface_with_control(
            clause_index,
            &mut GroundValidationControl::new(&mut || true),
        )
    }

    fn surface_with_control(
        &mut self,
        clause_index: usize,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<&GroundClauseSurface, GroundSourceSurfaceError> {
        control.poll()?;
        if clause_index >= self.problem.clauses().len() {
            return Err(GroundSourceSurfaceError::ClauseOutOfRange);
        }
        if !self.entries.contains_key(&clause_index) {
            // This makes the sparse map itself bounded by the same fixed work
            // envelope, including clauses with no variables or expressions.
            self.charge(1)?;
            let problem = self.problem;
            let clause = &problem.clauses()[clause_index];
            let (expression_occurrences, variables, variable_typecheck_work, replay_work) =
                self.reserve_unique_clause_walks(clause, control)?;
            for variable in &variables {
                control.poll()?;
                if variable.name.starts_with('\0') {
                    return Err(GroundSourceSurfaceError::PrivateSourceNamespace);
                }
            }
            let uf_applications = clause_ordinary_uf_applications(clause);
            control.poll()?;
            let uf_applications =
                uf_applications.map_err(|_| GroundSourceSurfaceError::InvalidUfSurface)?;
            let uf_key_structure_work =
                uf_applications
                    .iter()
                    .try_fold(0usize, |work, application| {
                        control.poll()?;
                        match application {
                            ChcExpr::FuncApp(name, _, arguments) => work
                                .checked_add(name.len())
                                .and_then(|work| work.checked_add(arguments.len()))
                                .and_then(|work| work.checked_add(2))
                                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded),
                            _ => Err(GroundSourceSurfaceError::InvalidUfSurface),
                        }
                    })?;
            let uf_argument_occurrences =
                uf_applications
                    .iter()
                    .try_fold(0usize, |count, application| {
                        control.poll()?;
                        match application {
                            ChcExpr::FuncApp(_, _, arguments) => count
                                .checked_add(arguments.len())
                                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded),
                            _ => Err(GroundSourceSurfaceError::InvalidUfSurface),
                        }
                    })?;
            let replay_work = replay_work
                .checked_add(uf_key_structure_work)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            self.entries.insert(
                clause_index,
                GroundClauseSurface {
                    variables,
                    variable_typecheck_work,
                    uf_applications,
                    uf_argument_occurrences,
                    value_replay_occurrences: expression_occurrences.max(1),
                    replay_work,
                },
            );
            #[cfg(test)]
            {
                self.walked_clauses += 1;
            }
        }
        control.poll()?;
        self.entries
            .get(&clause_index)
            .ok_or(GroundSourceSurfaceError::InvalidVariableSurface)
    }

    pub(crate) fn charge_step_reuse(
        &mut self,
        clause_index: usize,
    ) -> Result<(usize, usize), GroundSourceSurfaceError> {
        self.charge_step_reuse_with_control(
            clause_index,
            &mut GroundValidationControl::new(&mut || true),
        )
    }

    fn charge_step_reuse_with_control(
        &mut self,
        clause_index: usize,
        control: &mut GroundValidationControl<'_>,
    ) -> Result<(usize, usize), GroundSourceSurfaceError> {
        let (variables, applications, replay_work) = {
            let surface = self.surface_with_control(clause_index, control)?;
            (
                surface.variables.len(),
                surface.uf_applications.len(),
                surface.replay_work,
            )
        };
        self.charge(
            replay_work
                .checked_add(variables)
                .and_then(|work| work.checked_add(applications))
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
        )?;
        control.poll()?;
        Ok((variables, applications))
    }

    /// Reserve work for scalar material that one step's UF observations can
    /// clone or hash. The multiplication happens before any observation key is
    /// constructed, preventing a shared 1 MiB value from becoming gigabytes of
    /// replay work across thousands of applications.
    pub(crate) fn charge_step_scalar_replay(
        &mut self,
        clause_index: usize,
        env: &FxHashMap<String, SmtValue>,
        additional_results: &[SmtValue],
    ) -> Result<(), GroundSourceSurfaceError> {
        let (application_count, argument_occurrences, value_replay_occurrences, variable_count) = {
            let surface = self.surface(clause_index)?;
            (
                surface.uf_applications.len(),
                surface.uf_argument_occurrences,
                surface.value_replay_occurrences,
                surface.variables.len(),
            )
        };
        // Apply the remaining cache budget after every binding. In particular,
        // do not profile all values into one deferred sum: an adversarial step
        // with many individually admissible aggregates must stop as soon as
        // the cumulative typecheck envelope is exhausted.
        let mut remaining = self
            .work_limit
            .checked_sub(self.work_used)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        let mut binding_typecheck_work = 0usize;
        for variable_index in 0..variable_count {
            let (sort_work, value) = {
                let surface = self.surface(clause_index)?;
                let variable = &surface.variables[variable_index];
                (
                    surface.variable_typecheck_work[variable_index],
                    env.get(&variable.name),
                )
            };
            let Some(value) = value else {
                continue;
            };
            // Every storage profile contains at least its root node. Refuse
            // before walking it when even that minimum cannot fit.
            if sort_work > remaining {
                return Err(GroundSourceSurfaceError::SourceWorkLimitExceeded);
            }
            let storage_limit = remaining
                .checked_div(sort_work)
                .filter(|limit| *limit > 0)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            #[cfg(test)]
            {
                self.profiled_typecheck_bindings += 1;
            }
            let entry_work = sort_work
                .checked_mul(ground_value_storage_profile_with_limit(value, storage_limit)?.0)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            remaining = remaining
                .checked_sub(entry_work)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            binding_typecheck_work = binding_typecheck_work
                .checked_add(entry_work)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
        }
        self.charge(binding_typecheck_work)?;
        self.charge_scalar_replay(
            application_count,
            argument_occurrences,
            value_replay_occurrences,
            env,
            additional_results,
        )
    }

    /// Reserve recursive sort/type-validation work for decoded wire values
    /// before the codec scans datatype constructor tables.
    pub(crate) fn charge_step_wire_type_replay(
        &mut self,
        clause_index: usize,
        value_occurrences: &[usize],
    ) -> Result<(), GroundSourceSurfaceError> {
        let work = {
            let surface = self.surface(clause_index)?;
            if value_occurrences.len() != surface.variable_typecheck_work.len() {
                return Err(GroundSourceSurfaceError::InvalidVariableSurface);
            }
            surface
                .variable_typecheck_work
                .iter()
                .zip(value_occurrences)
                .try_fold(0usize, |total, (sort_work, occurrences)| {
                    total
                        .checked_add(
                            sort_work
                                .checked_mul((*occurrences).max(1))
                                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
                        )
                        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)
                })?
        };
        self.charge(work)
    }

    /// Reserve producer-head evaluation and aggregate comparison work for all
    /// incoming body-argument uses before any head value is materialized.
    pub(crate) fn charge_step_head_fanout_replay(
        &mut self,
        clause_index: usize,
        argument_fanout: usize,
        env: &FxHashMap<String, SmtValue>,
    ) -> Result<(), GroundSourceSurfaceError> {
        if argument_fanout == 0 {
            return Ok(());
        }
        let replay_work = self.surface(clause_index)?.replay_work;
        self.charge(
            replay_work
                .checked_mul(argument_fanout)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
        )?;
        // Each incoming use compares the whole head tuple: every binding it
        // reads, once per use.
        self.charge_each_binding(env, argument_fanout).map(|_| ())
    }

    /// Charge every binding (name and value) `multiplier` times; returns the
    /// widest value's work.
    fn charge_each_binding(
        &mut self,
        env: &FxHashMap<String, SmtValue>,
        multiplier: usize,
    ) -> Result<usize, GroundSourceSurfaceError> {
        let mut widest = 0usize;
        for (name, value) in env {
            let value_work = ground_value_replay_work(value)?
                .checked_add(1)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            widest = widest.max(value_work);
            let entry_work = name
                .len()
                .checked_add(value_work)
                .and_then(|work| work.checked_mul(multiplier))
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            self.charge(entry_work)?;
        }
        Ok(widest)
    }

    pub(crate) fn charge_scalar_replay(
        &mut self,
        application_count: usize,
        argument_occurrences: usize,
        value_replay_occurrences: usize,
        env: &FxHashMap<String, SmtValue>,
        additional_results: &[SmtValue],
    ) -> Result<(), GroundSourceSurfaceError> {
        // A UF application or argument occurrence may clone or hash ANY
        // binding into an observation key, so each binding is charged once per
        // such occurrence (at least once). Every other expression occurrence
        // reads ONE value, so the expression surface costs its occurrence
        // count times the widest value. (Charging every binding per expression
        // occurrence priced a plain 250-variable, 100k-node transition at
        // gigabytes and refused its ground derivations.)
        let uf_multiplier = application_count
            .checked_add(argument_occurrences)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?
            .max(1);
        let mut widest = self.charge_each_binding(env, uf_multiplier)?;
        for result in additional_results {
            let result_work = ground_value_replay_work(result)?
                .checked_add(1)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
            widest = widest.max(result_work);
            self.charge(
                result_work
                    .checked_mul(uf_multiplier)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
            )?;
        }
        self.charge(
            widest
                .checked_mul(value_replay_occurrences)
                .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?,
        )
    }
}

fn bigint_storage_work(value: &num_bigint::BigInt) -> Result<usize, GroundSourceSurfaceError> {
    usize::try_from(value.bits().saturating_add(7) / 8)
        .map_err(|_| GroundSourceSurfaceError::SourceWorkLimitExceeded)
}

fn biguint_storage_work(value: &num_bigint::BigUint) -> Result<usize, GroundSourceSurfaceError> {
    usize::try_from(value.bits().saturating_add(7) / 8)
        .map_err(|_| GroundSourceSurfaceError::SourceWorkLimitExceeded)
}

fn add_ground_value_work(
    work: &mut usize,
    amount: usize,
    work_limit: usize,
) -> Result<(), GroundSourceSurfaceError> {
    *work = work
        .checked_add(amount)
        .filter(|work| *work <= work_limit)
        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
    Ok(())
}

fn reserve_ground_value_children(
    work: usize,
    pending: usize,
    additional: usize,
    work_limit: usize,
) -> Result<(), GroundSourceSurfaceError> {
    work.checked_add(pending)
        .and_then(|projected| projected.checked_add(additional))
        .filter(|projected| *projected <= work_limit)
        .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
    Ok(())
}

fn ground_value_storage_profile(
    root: &SmtValue,
) -> Result<(usize, bool), GroundSourceSurfaceError> {
    ground_value_storage_profile_with_limit(root, CHC_GROUND_DERIVATION_MAX_SOURCE_WORK)
}

fn ground_value_storage_profile_with_limit(
    root: &SmtValue,
    work_limit: usize,
) -> Result<(usize, bool), GroundSourceSurfaceError> {
    let mut work = 0usize;
    let mut has_nonlinear_aggregate = false;
    let mut stack = vec![(root, 1usize)];
    while let Some((value, depth)) = stack.pop() {
        if depth > CHC_GROUND_DERIVATION_MAX_VALUE_DEPTH {
            return Err(GroundSourceSurfaceError::SourceWorkLimitExceeded);
        }
        add_ground_value_work(&mut work, 1, work_limit)?;
        match value {
            SmtValue::Bool(_) | SmtValue::Int(_) => {}
            SmtValue::BitVec(_, width) => {
                add_ground_value_work(&mut work, bitvector_width_replay_work(*width)?, work_limit)?
            }
            SmtValue::BigInt(value) => {
                add_ground_value_work(&mut work, bigint_storage_work(value)?, work_limit)?
            }
            SmtValue::Real(value) => {
                add_ground_value_work(&mut work, bigint_storage_work(value.numer())?, work_limit)?;
                add_ground_value_work(&mut work, bigint_storage_work(value.denom())?, work_limit)?;
            }
            SmtValue::BigBitVec(value, width) => {
                add_ground_value_work(&mut work, bitvector_width_replay_work(*width)?, work_limit)?;
                add_ground_value_work(&mut work, biguint_storage_work(value)?, work_limit)?
            }
            SmtValue::Opaque(text) => add_ground_value_work(&mut work, text.len(), work_limit)?,
            SmtValue::ConstArray(default) => {
                reserve_ground_value_children(work, stack.len(), 1, work_limit)?;
                let child_depth = depth
                    .checked_add(1)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                stack.push((default, child_depth));
            }
            SmtValue::ArrayMap { default, entries } => {
                has_nonlinear_aggregate = true;
                let children = entries
                    .len()
                    .checked_mul(2)
                    .and_then(|children| children.checked_add(1))
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                reserve_ground_value_children(work, stack.len(), children, work_limit)?;
                let child_depth = depth
                    .checked_add(1)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                stack.push((default, child_depth));
                for (key, entry) in entries {
                    stack.push((key, child_depth));
                    stack.push((entry, child_depth));
                }
            }
            SmtValue::Datatype(constructor, fields) => {
                has_nonlinear_aggregate = true;
                add_ground_value_work(&mut work, constructor.len(), work_limit)?;
                reserve_ground_value_children(work, stack.len(), fields.len(), work_limit)?;
                let child_depth = depth
                    .checked_add(1)
                    .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)?;
                stack.extend(fields.iter().map(|field| (field, child_depth)));
            }
        }
    }
    Ok((work, has_nonlinear_aggregate))
}

fn ground_value_replay_work(value: &SmtValue) -> Result<usize, GroundSourceSurfaceError> {
    let (storage_work, has_nonlinear_aggregate) = ground_value_storage_profile(value)?;
    if has_nonlinear_aggregate {
        storage_work
            .checked_mul(storage_work)
            .filter(|work| *work <= CHC_GROUND_DERIVATION_MAX_SOURCE_WORK)
            .ok_or(GroundSourceSurfaceError::SourceWorkLimitExceeded)
    } else {
        Ok(storage_work)
    }
}

/// Whether a native producer value is one exact canonical inhabitant of a
/// source sort.
///
/// This mirrors artifact decoding's representation invariants: small integers
/// cannot inhabit `BigInt`, bitvectors must use the width-selected variant and
/// have no set bits outside that width, and aggregates are checked recursively
/// against their source index/field sorts. The value and source preflights run
/// before this walk, so both sides already satisfy fixed depth/work bounds.
///
/// A recursive datatype's sort is a finite snapshot: the parser cuts the
/// cycle, so past the first unfolding a selector names its datatype by an
/// uninterpreted placeholder (`Uninterpreted("Nat")` inside `succ`'s field).
/// Such a placeholder stands for the enclosing datatype of that name, whose
/// constructors this walk has already seen; without resolving it every
/// value nested two constructors deep (`succ(succ(zero))`) was refused.
fn canonical_ground_value_matches_sort(root_value: &SmtValue, root_sort: &crate::ChcSort) -> bool {
    let mut enclosing: FxHashMap<&str, &[crate::ChcDtConstructor]> = FxHashMap::default();
    let mut stack = vec![(root_value, root_sort, 1usize)];
    while let Some((value, sort, depth)) = stack.pop() {
        if depth > CHC_GROUND_DERIVATION_MAX_VALUE_DEPTH {
            return false;
        }
        let placeholder_constructors = match (value, sort) {
            (SmtValue::Datatype(..), crate::ChcSort::Uninterpreted(name)) => {
                enclosing.get(name.as_str()).copied()
            }
            _ => None,
        };
        if let crate::ChcSort::Datatype { name, constructors } = sort {
            enclosing
                .entry(name.as_str())
                .or_insert(constructors.as_slice());
        }
        if let (SmtValue::Datatype(constructor, fields), Some(constructors)) =
            (value, placeholder_constructors)
        {
            let Some(definition) = constructors
                .iter()
                .find(|definition| definition.name == *constructor)
            else {
                return false;
            };
            if fields.len() != definition.selectors.len() {
                return false;
            }
            let Some(child_depth) = depth.checked_add(1) else {
                return false;
            };
            stack.extend(
                fields
                    .iter()
                    .zip(&definition.selectors)
                    .map(|(field, selector)| (field, &selector.sort, child_depth)),
            );
            continue;
        }
        match (value, sort) {
            (value, sort) if canonical_scalar_value_matches_sort(value, sort) => {}
            (SmtValue::ConstArray(default), crate::ChcSort::Array(_, value_sort)) => {
                let Some(child_depth) = depth.checked_add(1) else {
                    return false;
                };
                stack.push((default, value_sort, child_depth));
            }
            (
                SmtValue::ArrayMap { default, entries },
                crate::ChcSort::Array(index_sort, value_sort),
            ) => {
                let Some(child_depth) = depth.checked_add(1) else {
                    return false;
                };
                stack.push((default, value_sort, child_depth));
                for (index, entry) in entries {
                    stack.push((index, index_sort, child_depth));
                    stack.push((entry, value_sort, child_depth));
                }
            }
            (
                SmtValue::Datatype(constructor, fields),
                crate::ChcSort::Datatype { constructors, .. },
            ) => {
                let Some(definition) = constructors
                    .iter()
                    .find(|definition| definition.name == *constructor)
                else {
                    return false;
                };
                if fields.len() != definition.selectors.len() {
                    return false;
                }
                let Some(child_depth) = depth.checked_add(1) else {
                    return false;
                };
                stack.extend(
                    fields
                        .iter()
                        .zip(&definition.selectors)
                        .map(|(field, selector)| (field, &selector.sort, child_depth)),
                );
            }
            (SmtValue::Opaque(_), _)
            | (_, crate::ChcSort::Uninterpreted(_))
            | (_, crate::ChcSort::Bool)
            | (_, crate::ChcSort::Int)
            | (_, crate::ChcSort::Real)
            | (_, crate::ChcSort::BitVec(_))
            | (_, crate::ChcSort::Array(_, _))
            | (_, crate::ChcSort::Datatype { .. }) => return false,
        }
    }
    true
}

/// Whether an environment entry is AY's exact finite-UF observation marker.
///
/// The marker is intentionally an `Opaque` value because it is metadata, not a
/// source-theory value. Completion may preserve this one exact pair while still
/// dropping every ordinary opaque placeholder.
pub(crate) fn is_exact_uf_model_marker(name: &str, value: &SmtValue) -> bool {
    use crate::expr::evaluate::{
        UF_APPLICATION_MODEL_MARKER_KEY, UF_APPLICATION_MODEL_MARKER_VALUE,
    };

    name == UF_APPLICATION_MODEL_MARKER_KEY
        && matches!(value, SmtValue::Opaque(marker) if marker == UF_APPLICATION_MODEL_MARKER_VALUE)
}

/// Canonical distinct ordinary-UF applications owned by one source clause.
///
/// All expression positions that native derivation validation evaluates are
/// included. Structural sorting makes artifact ordinals independent of walker
/// stack order and hash-table iteration.
pub(crate) fn clause_ordinary_uf_applications(
    clause: &HornClause,
) -> crate::ChcResult<Vec<ChcExpr>> {
    let head_arguments = match &clause.head {
        ClauseHead::Predicate(_, arguments) => arguments.as_slice(),
        ClauseHead::False => &[],
    };
    let roots = clause
        .body
        .constraint
        .iter()
        .chain(
            clause
                .body
                .predicates
                .iter()
                .flat_map(|(_, arguments)| arguments),
        )
        .chain(head_arguments);
    let mut applications =
        crate::smt::executor_adapter::collect_uninterpreted_function_applications_for_exprs(roots)?;
    applications.sort();
    applications.dedup();
    Ok(applications)
}

fn scalar_value_matches_sort(value: &SmtValue, sort: &crate::ChcSort) -> bool {
    canonical_scalar_value_matches_sort(value, sort)
}

fn canonical_scalar_value_matches_sort(value: &SmtValue, sort: &crate::ChcSort) -> bool {
    match (value, sort) {
        (SmtValue::Bool(_), crate::ChcSort::Bool) | (SmtValue::Int(_), crate::ChcSort::Int) => true,
        (SmtValue::BigInt(value), crate::ChcSort::Int) => {
            num_traits::ToPrimitive::to_i128(value.as_ref()).is_none()
        }
        (SmtValue::Real(value), crate::ChcSort::Real) => canonical_real_value(value),
        (SmtValue::BitVec(value, width), crate::ChcSort::BitVec(expected_width)) => {
            if width != expected_width || *width == 0 || *width > 128 {
                return false;
            }
            let normalized = match *width {
                128 => *value,
                _ => *value & ((1u128 << *width) - 1),
            };
            normalized == *value
        }
        (SmtValue::BigBitVec(value, width), crate::ChcSort::BitVec(expected_width)) => {
            width == expected_width
                && *width > 128
                && *width <= crate::MAX_BITVECTOR_WIDTH
                && value.bits() <= u64::from(*width)
        }
        _ => false,
    }
}

fn canonical_real_value(value: &num_rational::BigRational) -> bool {
    if value.denom().sign() != num_bigint::Sign::Plus {
        return false;
    }
    let reduced = num_rational::BigRational::new(value.numer().clone(), value.denom().clone());
    reduced.numer() == value.numer() && reduced.denom() == value.denom()
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum GroundScalarSortKey {
    Bool,
    Int,
    Real,
    BitVec(u32),
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum GroundScalarValueKey {
    Bool(bool),
    Int(i128),
    BigInt(std::sync::Arc<num_bigint::BigInt>),
    Real(std::sync::Arc<num_rational::BigRational>),
    BitVec(std::sync::Arc<num_bigint::BigUint>, u32),
}

/// Typed congruence identity for one ordinary-UF application at concrete
/// scalar arguments.
///
/// In particular, wide integers and bitvectors retain their existing `Arc`
/// allocation. They are never expanded into decimal/hex strings merely to be
/// used as derivation-wide hash keys.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct GroundUfCongruenceKey {
    function: String,
    return_sort: GroundScalarSortKey,
    argument_sorts: Vec<GroundScalarSortKey>,
    arguments: Vec<GroundScalarValueKey>,
}

fn ground_scalar_sort_key(sort: &crate::ChcSort) -> Option<GroundScalarSortKey> {
    match sort {
        crate::ChcSort::Bool => Some(GroundScalarSortKey::Bool),
        crate::ChcSort::Int => Some(GroundScalarSortKey::Int),
        crate::ChcSort::Real => Some(GroundScalarSortKey::Real),
        crate::ChcSort::BitVec(width) => Some(GroundScalarSortKey::BitVec(*width)),
        crate::ChcSort::Array(_, _)
        | crate::ChcSort::Uninterpreted(_)
        | crate::ChcSort::Datatype { .. } => None,
    }
}

fn ground_scalar_value_key(value: &SmtValue) -> Option<GroundScalarValueKey> {
    match value {
        SmtValue::Bool(value) => Some(GroundScalarValueKey::Bool(*value)),
        SmtValue::Int(value) => Some(GroundScalarValueKey::Int(*value)),
        SmtValue::BigInt(value) => Some(GroundScalarValueKey::BigInt(value.clone())),
        SmtValue::Real(value) => Some(GroundScalarValueKey::Real(std::sync::Arc::new(
            value.clone(),
        ))),
        SmtValue::BitVec(_, _) | SmtValue::BigBitVec(_, _) => {
            let (value, width) = value.bitvec_to_biguint()?;
            Some(GroundScalarValueKey::BitVec(
                std::sync::Arc::new(value),
                width,
            ))
        }
        SmtValue::Opaque(_)
        | SmtValue::ConstArray(_)
        | SmtValue::ArrayMap { .. }
        | SmtValue::Datatype(_, _) => None,
    }
}

pub(crate) fn ground_uf_congruence_key(
    application: &ChcExpr,
    argument_values: &[SmtValue],
) -> Option<GroundUfCongruenceKey> {
    let ChcExpr::FuncApp(function, return_sort, arguments) = application else {
        return None;
    };
    if arguments.len() != argument_values.len() {
        return None;
    }
    Some(GroundUfCongruenceKey {
        function: function.clone(),
        return_sort: ground_scalar_sort_key(return_sort)?,
        argument_sorts: arguments
            .iter()
            .map(|argument| ground_scalar_sort_key(&argument.sort()))
            .collect::<Option<Vec<_>>>()?,
        arguments: argument_values
            .iter()
            .map(ground_scalar_value_key)
            .collect::<Option<Vec<_>>>()?,
    })
}

/// Validate the finite ordinary-UF observations used by one derivation step.
///
/// A finite set of scalar observations extends to a total uninterpreted
/// function exactly when equal concrete argument tuples have equal results.
/// `congruence` is shared by every step, so the derivation cannot silently use
/// a different interpretation of the same source function in another clause.
fn validate_step_uf_observations(
    step_index: usize,
    applications: &[ChcExpr],
    env: &FxHashMap<String, SmtValue>,
    congruence: &mut FxHashMap<GroundUfCongruenceKey, SmtValue>,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), GroundDerivationError> {
    for (application_index, application) in applications.iter().enumerate() {
        control.poll()?;
        let ChcExpr::FuncApp(_, return_sort, arguments) = application else {
            return Err(GroundDerivationError::UfSurfaceInvalid { step: step_index });
        };
        let Some(result) = eval_ground_with_control(application, env, control)? else {
            return Err(GroundDerivationError::UfObservationNotGround {
                step: step_index,
                application: application_index,
            });
        };
        if !scalar_value_matches_sort(&result, return_sort) {
            return Err(GroundDerivationError::UfObservationNotGround {
                step: step_index,
                application: application_index,
            });
        }
        let mut argument_values = Vec::with_capacity(arguments.len());
        for argument in arguments {
            argument_values.push(eval_ground_with_control(argument, env, control)?.ok_or(
                GroundDerivationError::UfObservationNotGround {
                    step: step_index,
                    application: application_index,
                },
            )?);
        }
        let key = ground_uf_congruence_key(application, &argument_values);
        control.poll()?;
        let Some(key) = key else {
            return Err(GroundDerivationError::UfObservationNotGround {
                step: step_index,
                application: application_index,
            });
        };
        let conflicts = congruence
            .get(&key)
            .is_some_and(|previous| !smt_values_equal(previous, &result));
        control.poll()?;
        if conflicts {
            return Err(GroundDerivationError::UfCongruenceViolation {
                step: step_index,
                application: application_index,
            });
        }
        congruence.entry(key).or_insert(result);
        control.poll()?;
    }
    Ok(())
}

/// Whether ground-witness back-translation is enabled.
///
/// Kill switch `AY_CHC_DISABLE_GROUND_BACKTRANSLATION=1` restores the previous
/// behavior exactly (search-replay only), matching the `AY_CHC_DISABLE_*`
/// convention used by the other transform-side features.
pub(crate) fn ground_backtranslation_enabled() -> bool {
    // B27: CLI-owned (--chc-no-ground-backtranslation); env retired.
    crate::ab_switches::get().ground_backtranslation
}

/// Whether ground back-translation diagnostics should be printed.
///
/// Enabled by `--chc-ground-bt-debug`. The landing sites print their own
/// one-line outcome under `--verbose`; this switch adds the per-pass detail
/// used to find which transform in a chain is the blocker.
pub(crate) fn ground_backtranslation_debug() -> bool {
    static FLAG: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *FLAG.get_or_init(|| ay_core::misc_cli_flags().chc_ground_bt_debug)
}

/// Record that `pass` could not ground-back-translate a derivation.
pub(crate) fn log_ground_translation_failure(pass: &str) {
    if ground_backtranslation_debug() {
        ay_core::safe_eprintln!("ground-bt: pass `{pass}` cannot map the derivation (fail-closed)");
    }
}

/// Record a per-pass diagnostic.
pub(crate) fn log_ground_translation_detail(args: std::fmt::Arguments<'_>) {
    if ground_backtranslation_debug() {
        ay_core::safe_eprintln!("ground-bt: {args}");
    }
}

/// Ground-evaluate `expr` under `env`, retrying once through the array/constant
/// simplifiers.
///
/// The direct evaluation covers literals, Booleans, arithmetic, the full
/// bitvector fragment, array select/store over concrete `ArrayMap`/`ConstArray`
/// values and datatype constructor/selector/tester applications. The retry
/// exists because some encodings park a `select` over a syntactic `store` chain
/// (or a nested constructor/selector pair) in a shape the evaluator only
/// discharges after normalization.
///
/// Returns `None` whenever the result is not a single concrete value; callers
/// treat that as rejection.
fn eval_ground(expr: &ChcExpr, env: &FxHashMap<String, SmtValue>) -> Option<SmtValue> {
    eval_ground_with_control(expr, env, &mut GroundValidationControl::new(&mut || true))
        .ok()
        .flatten()
}

/// Cancellation is an error, never an indeterminate value that could trigger
/// another simplification/evaluation attempt. Individual evaluator and
/// simplifier calls remain opaque cooperative-cancellation intervals.
fn eval_ground_with_control(
    expr: &ChcExpr,
    env: &FxHashMap<String, SmtValue>,
    control: &mut GroundValidationControl<'_>,
) -> Result<Option<SmtValue>, GroundDerivationError> {
    control.poll()?;
    let direct = evaluate_expr(expr, env);
    control.poll()?;
    let value = match direct {
        Some(value) => value,
        None => {
            let normalized = expr.clone();
            control.poll()?;
            let normalized = normalized.simplify_array_ops();
            control.poll()?;
            let normalized = normalized.simplify_constants();
            control.poll()?;
            let normalized = normalized.simplify_array_ops();
            control.poll()?;
            let normalized = normalized.simplify_constants();
            control.poll()?;
            let value = evaluate_expr(&normalized, env);
            control.poll()?;
            let Some(value) = value else { return Ok(None) };
            value
        }
    };
    // `SmtValue::Opaque` is a solver placeholder, not a value. Letting one
    // through would make two unrelated placeholders compare equal and a
    // constraint "evaluate" without ever being decided, so it is rejected here
    // rather than at each use site.
    let concrete = is_concrete(&value);
    control.poll()?;
    Ok(concrete.then_some(value))
}

/// Crate-visible wrapper around [`eval_ground`] for transform back-translators.
pub(crate) fn eval_ground_pub(
    expr: &ChcExpr,
    env: &FxHashMap<String, SmtValue>,
) -> Option<SmtValue> {
    eval_ground(expr, env)
}

/// Whether a value is a genuine concrete value (no `Opaque` placeholder
/// anywhere inside it).
fn is_concrete(value: &SmtValue) -> bool {
    match value {
        SmtValue::Opaque(_) => false,
        SmtValue::ConstArray(default) => is_concrete(default),
        SmtValue::ArrayMap { default, entries } => {
            is_concrete(default)
                && entries
                    .iter()
                    .all(|(key, entry)| is_concrete(key) && is_concrete(entry))
        }
        SmtValue::Datatype(_, fields) => fields.iter().all(is_concrete),
        _ => true,
    }
}

/// Head-argument expressions of `clause`, or `None` when the head is `false`.
fn head_args(clause: &HornClause) -> Option<&[ChcExpr]> {
    match &clause.head {
        ClauseHead::Predicate(_, args) => Some(args),
        ClauseHead::False => None,
    }
}

/// Validate a candidate ground derivation against `problem`.
///
/// This is a DECISION, not a discharge: it succeeds only when every step's
/// clause constraint evaluates to `true` and every body-predicate argument
/// tuple is value-identical to the head-argument tuple of the premise that
/// justifies it, under totally concrete assignments. Success means `false` is
/// derivable from `problem`'s clauses, i.e. the problem is UNSAFE.
///
/// The check is deliberately structural about well-foundedness: premises must
/// point strictly backwards, so no step can (transitively) justify itself.
/// Whether `problem` passes the whole-source preflight that native
/// [`validate_ground_derivation`] runs first. `false` means that function
/// refuses EVERY derivation on `problem`, so a search for ground evidence on it
/// can stop before it starts. Bounded by the preflight's native work envelope.
pub(crate) fn problem_admits_native_ground_validation(problem: &ChcProblem) -> bool {
    let mut progress = || true;
    let mut control = GroundValidationControl::new_native(&mut progress);
    control
        .with_native_whole_source_scope(|control| {
            artifact::validate_ground_source_problem_with_control(problem, control)
        })
        .is_ok()
}

pub(crate) fn validate_ground_derivation(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<(), GroundDerivationError> {
    validate_ground_derivation_with_progress(problem, derivation, &mut || true)
}

/// Native ground validation under a borrowed existing stop owner.
///
/// The native finite source envelope and semantic checks are unchanged; this
/// is not wire-artifact admission and conveys no retained proof authority.
pub(crate) fn validate_ground_derivation_with_progress(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
    progress: &mut dyn FnMut() -> bool,
) -> Result<(), GroundDerivationError> {
    let mut control = GroundValidationControl::new_native(progress);
    let result = validate_ground_derivation_with_control(problem, derivation, &mut control);
    // The validator's evaluator/cache temporaries have now been released.
    // Keep its sticky control for this final caller observation.
    control.poll()?;
    result
}

/// Cooperatively check ground evidence without converting cancellation into
/// proof rejection. Source authentication, aggregate comparisons and each
/// evaluator/normalizer call remain opaque phases; this is not a hard deadline.
fn validate_ground_derivation_with_control(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
    control: &mut GroundValidationControl<'_>,
) -> Result<(), GroundDerivationError> {
    control.poll()?;
    if derivation.steps.is_empty() {
        return Err(GroundDerivationError::Empty);
    }
    if derivation.query_step >= derivation.steps.len() {
        return Err(GroundDerivationError::RootOutOfRange);
    }
    if derivation.steps.len() > CHC_GROUND_DERIVATION_MAX_SOURCE_WORK {
        return Err(GroundDerivationError::SourceWorkLimitExceeded);
    }
    let mut work = derivation.steps.len();
    for step in &derivation.steps {
        control.poll()?;
        work = work
            .checked_add(step.premises.len())
            .filter(|work| *work <= CHC_GROUND_DERIVATION_MAX_SOURCE_WORK)
            .ok_or(GroundDerivationError::SourceWorkLimitExceeded)?;
    }
    // Native mode: the same depth guard and semantic validators, but the
    // larger, still FINITE native work envelope instead of the wire artifact's
    // (`source_identity::NATIVE_WHOLE_SOURCE_WORK`). Artifact callers ran the
    // wire-limited preflight on this problem before reaching here.
    let source_result = control.with_native_whole_source_scope(|control| {
        artifact::validate_ground_source_problem_with_control(problem, control)
    });
    control.poll()?;
    source_result.map_err(|source_error| match source_error.reason {
        ChcGroundDerivationArtifactErrorReason::Interrupted => GroundDerivationError::Interrupted,
        ChcGroundDerivationArtifactErrorReason::SourceWorkLimitExceeded => {
            log_ground_translation_detail(format_args!(
                "validator: whole-source preflight exceeded the native envelope ({} clauses, native={})",
                problem.clauses().len(),
                control.is_native()
            ));
            GroundDerivationError::SourceWorkLimitExceeded
        }
        reason => {
            log_ground_translation_detail(format_args!(
                "validator: whole-source check refused the problem ({reason:?}): {}",
                source_error.detail
            ));
            GroundDerivationError::InvalidSourceProblem
        }
    })?;
    let clauses = problem.clauses();

    // Pass 1: structural well-formedness. Resolving every clause up front means
    // the value checks below can index without re-validating.
    for (idx, step) in derivation.steps.iter().enumerate() {
        control.poll()?;
        let Some(clause) = clauses.get(step.clause_index) else {
            return Err(GroundDerivationError::ClauseOutOfRange {
                step: idx,
                clause_index: step.clause_index,
            });
        };
        for &premise in &step.premises {
            control.poll()?;
            // Strictly-backwards premises make the premise graph a DAG by
            // construction; an entry can never justify itself, directly or
            // through a cycle. This is the adversarial-witness defense the SMT
            // witness validator implements with an explicit cycle search.
            if premise >= idx {
                return Err(GroundDerivationError::PremiseNotWellFounded { step: idx, premise });
            }
        }
        if step.premises.len() != clause.body.predicates.len() {
            return Err(GroundDerivationError::PremiseArityMismatch {
                step: idx,
                expected: clause.body.predicates.len(),
                found: step.premises.len(),
            });
        }
        let is_query = clause.is_query();
        if idx == derivation.query_step && !is_query {
            return Err(GroundDerivationError::RootNotQuery { step: idx });
        }
        if idx != derivation.query_step && is_query {
            return Err(GroundDerivationError::NonRootIsQuery { step: idx });
        }
    }

    // Pass 2: reachability from the root. A derivation may not carry unrelated
    // padding steps — everything present must participate in the proof.
    let mut reachable = vec![false; derivation.steps.len()];
    let mut stack = vec![derivation.query_step];
    reachable[derivation.query_step] = true;
    while let Some(idx) = stack.pop() {
        control.poll()?;
        for &premise in &derivation.steps[idx].premises {
            control.poll()?;
            if !reachable[premise] {
                reachable[premise] = true;
                stack.push(premise);
            }
        }
    }
    for (step, hit) in reachable.iter().enumerate() {
        control.poll()?;
        if !hit {
            return Err(GroundDerivationError::UnreachableStep { step });
        }
    }

    // One cached producer head can feed many consumer arguments. Equality of
    // aggregate values is not constant-time, so derive exact incoming argument
    // multiplicity without evaluating either side and reserve producer replay
    // work before Pass 3 materializes any head value.
    let mut premise_head_argument_fanout = vec![0usize; derivation.steps.len()];
    let mut total_head_argument_fanout = 0usize;
    for step in &derivation.steps {
        control.poll()?;
        let clause = &clauses[step.clause_index];
        for ((_, arguments), premise) in clause.body.predicates.iter().zip(&step.premises) {
            control.poll()?;
            total_head_argument_fanout = total_head_argument_fanout
                .checked_add(arguments.len())
                .filter(|fanout| *fanout <= CHC_GROUND_DERIVATION_MAX_SOURCE_WORK)
                .ok_or(GroundDerivationError::SourceWorkLimitExceeded)?;
            premise_head_argument_fanout[*premise] = premise_head_argument_fanout[*premise]
                .checked_add(arguments.len())
                .ok_or(GroundDerivationError::SourceWorkLimitExceeded)?;
        }
    }

    // Authenticate and budget every distinct source surface before evaluating
    // any step. Repeated references use one clause-indexed cache entry, while
    // their per-step variable/UF processing is charged up front.
    // Native validation admits the derivation's clause surfaces against the
    // native envelope; a wire control keeps the wire cap.
    let native = control.is_native();
    let mut source_surfaces = GroundSourceSurfaceCache::with_work_limit(
        problem,
        if native {
            CHC_GROUND_DERIVATION_NATIVE_SOURCE_WORK
        } else {
            CHC_GROUND_DERIVATION_MAX_SOURCE_WORK
        },
    );
    for (step_index, step) in derivation.steps.iter().enumerate() {
        control.poll()?;
        let map_surface_error = |surface_error| match surface_error {
            GroundSourceSurfaceError::Interrupted => GroundDerivationError::Interrupted,
            GroundSourceSurfaceError::SourceWorkLimitExceeded => {
                GroundDerivationError::SourceWorkLimitExceeded
            }
            _ => GroundDerivationError::UfSurfaceInvalid { step: step_index },
        };
        // A surface refusal names its budget (`--chc-ground-bt-debug`): the
        // error variant is shared with the whole-source preflight above.
        let refuse = |cache: &GroundSourceSurfaceCache<'_>,
                      phase: &str,
                      surface_error: GroundSourceSurfaceError| {
            if matches!(
                surface_error,
                GroundSourceSurfaceError::SourceWorkLimitExceeded
            ) {
                log_ground_translation_detail(format_args!(
                    "validator: source-surface work {} of {} exhausted in {phase} at step {step_index} (clause {}, native={native})",
                    cache.work_used(),
                    cache.work_limit(),
                    step.clause_index
                ));
            }
            map_surface_error(surface_error)
        };
        if let Err(surface_error) =
            source_surfaces.charge_step_reuse_with_control(step.clause_index, control)
        {
            return Err(refuse(&source_surfaces, "clause walk", surface_error));
        }
        control.poll()?;
        if let Err(surface_error) =
            source_surfaces.charge_step_scalar_replay(step.clause_index, &step.env, &[])
        {
            return Err(refuse(&source_surfaces, "scalar replay", surface_error));
        }
        control.poll()?;
        if let Err(surface_error) = source_surfaces.charge_step_head_fanout_replay(
            step.clause_index,
            premise_head_argument_fanout[step_index],
            &step.env,
        ) {
            return Err(refuse(
                &source_surfaces,
                "head fan-out replay",
                surface_error,
            ));
        }
        control.poll()?;
        let variables = &source_surfaces
            .surface(step.clause_index)
            .map_err(map_surface_error)?
            .variables;
        for (variable_index, variable) in variables.iter().enumerate() {
            control.poll()?;
            let Some(value) = step.env.get(&variable.name) else {
                return Err(GroundDerivationError::VariableBindingMissing {
                    step: step_index,
                    variable: variable_index,
                });
            };
            let matches_sort = canonical_ground_value_matches_sort(value, &variable.sort);
            control.poll()?;
            if !matches_sort {
                return Err(GroundDerivationError::VariableBindingSortMismatch {
                    step: step_index,
                    variable: variable_index,
                });
            }
        }
    }

    // Pass 3: the actual proof check — pure ground evaluation. Ordinary-UF
    // observations share one congruence table across every clause instance;
    // step-local function interpretations would not constitute one CHC model.
    let mut uf_congruence = FxHashMap::default();
    // A premise head may fan out to arbitrarily many incoming body edges.
    // Evaluate its tuple exactly once after the producing step validates, then
    // reuse the concrete/indeterminate cells at every consumer.
    let mut evaluated_heads: Vec<Option<Vec<Option<SmtValue>>>> =
        vec![None; derivation.steps.len()];
    for (idx, step) in derivation.steps.iter().enumerate() {
        control.poll()?;
        let clause = &clauses[step.clause_index];
        let applications = &source_surfaces
            .surface(step.clause_index)
            .map_err(|surface_error| match surface_error {
                GroundSourceSurfaceError::Interrupted => GroundDerivationError::Interrupted,
                GroundSourceSurfaceError::SourceWorkLimitExceeded => {
                    GroundDerivationError::SourceWorkLimitExceeded
                }
                _ => GroundDerivationError::UfSurfaceInvalid { step: idx },
            })?
            .uf_applications;

        validate_step_uf_observations(idx, applications, &step.env, &mut uf_congruence, control)?;

        if let Some(constraint) = &clause.body.constraint {
            match eval_ground_with_control(constraint, &step.env, control)? {
                Some(SmtValue::Bool(true)) => {}
                Some(SmtValue::Bool(false)) => {
                    diagnose_false_constraint(idx, step.clause_index, constraint, &step.env);
                    return Err(GroundDerivationError::ConstraintFalse { step: idx });
                }
                _ => {
                    diagnose_indeterminate_constraint(
                        idx,
                        step.clause_index,
                        constraint,
                        &step.env,
                    );
                    return Err(GroundDerivationError::ConstraintNotGround { step: idx });
                }
            }
        }

        for (position, (pred, args)) in clause.body.predicates.iter().enumerate() {
            control.poll()?;
            let premise_idx = step.premises[position];
            let premise = &derivation.steps[premise_idx];
            let premise_clause = &clauses[premise.clause_index];
            let Some(declared_predicate) = problem.get_predicate(*pred) else {
                return Err(GroundDerivationError::PremisePredicateMismatch {
                    step: idx,
                    position,
                });
            };
            let Some(premise_head_args) = head_args(premise_clause) else {
                return Err(GroundDerivationError::PremisePredicateMismatch {
                    step: idx,
                    position,
                });
            };
            let Some(premise_head_values) = evaluated_heads[premise_idx].as_ref() else {
                return Err(GroundDerivationError::PremisePredicateMismatch {
                    step: idx,
                    position,
                });
            };
            let premise_pred = premise_clause.head.predicate_id();
            if premise_pred != Some(*pred)
                || premise_head_args.len() != args.len()
                || premise_head_values.len() != args.len()
            {
                return Err(GroundDerivationError::PremisePredicateMismatch {
                    step: idx,
                    position,
                });
            }
            for (argument, ((use_arg, def_arg), def_value)) in args
                .iter()
                .zip(premise_head_args.iter())
                .zip(premise_head_values)
                .enumerate()
            {
                control.poll()?;
                let (Some(use_value), Some(def_value)) = (
                    eval_ground_with_control(use_arg, &step.env, control)?,
                    def_value.as_ref(),
                ) else {
                    return Err(GroundDerivationError::ArgumentNotGround {
                        step: idx,
                        position,
                        argument,
                    });
                };
                let Some(expected_sort) = declared_predicate.arg_sorts.get(argument) else {
                    return Err(GroundDerivationError::PremisePredicateMismatch {
                        step: idx,
                        position,
                    });
                };
                let sorts_match = canonical_ground_value_matches_sort(&use_value, expected_sort)
                    && canonical_ground_value_matches_sort(def_value, expected_sort);
                control.poll()?;
                if !sorts_match {
                    return Err(GroundDerivationError::ArgumentNotGround {
                        step: idx,
                        position,
                        argument,
                    });
                }
                let equal = smt_values_equal(&use_value, &def_value);
                control.poll()?;
                if !equal {
                    if ground_backtranslation_debug() {
                        log_ground_translation_detail(format_args!(
                            "step {idx} (clause {}) body position {position} argument {argument}: \
                             use `{use_arg}` = {use_value:?} but premise step {premise_idx} \
                             (clause {}) head `{def_arg}` = {def_value:?}",
                            step.clause_index, premise.clause_index
                        ));
                    }
                    return Err(GroundDerivationError::ArgumentMismatch {
                        step: idx,
                        position,
                        argument,
                    });
                }
            }
        }
        evaluated_heads[idx] = if let Some(arguments) = head_args(clause) {
            let mut values = Vec::with_capacity(arguments.len());
            for argument in arguments {
                values.push(eval_ground_with_control(argument, &step.env, control)?);
            }
            Some(values)
        } else {
            None
        };
    }

    // #completed-check-accepted: no poll here. Every step has been decided;
    // a stop that arrives now cannot un-decide it, and the verdict on a
    // finished check must not depend on when the caller's deadline landed.
    Ok(())
}

/// Report the first conjunct of an indeterminate constraint that does not
/// evaluate, together with the variables it needs that the environment lacks.
///
/// Diagnostics only (`--chc-ground-bt-debug`); this is how a chain-level
/// fail-closed is traced back to the specific pass whose reconstruction was
/// incomplete.
fn diagnose_indeterminate_constraint(
    step: usize,
    clause_index: usize,
    constraint: &ChcExpr,
    env: &FxHashMap<String, SmtValue>,
) {
    if !ground_backtranslation_debug() {
        return;
    }
    for (position, conjunct) in constraint.collect_conjuncts().iter().enumerate() {
        if eval_ground(conjunct, env).is_some() {
            continue;
        }
        let missing: Vec<String> = conjunct
            .vars()
            .into_iter()
            .filter(|var| !env.contains_key(&var.name))
            .map(|var| var.name)
            .collect();
        let rendered = truncate_debug_expr(conjunct.to_string());
        log_ground_translation_detail(format_args!(
            "step {step} (clause {clause_index}) conjunct {position} is indeterminate;              unbound vars {missing:?}; expr {rendered}"
        ));
        return;
    }
}

/// Debug-only: name the first conjunct a step's environment falsifies, and the
/// values it was read under.
///
/// A false constraint is the validator doing its job — some value the
/// reconstruction proposed is not the one the original clause requires — so the
/// useful detail is WHICH conjunct and under WHICH bindings.
fn diagnose_false_constraint(
    step: usize,
    clause_index: usize,
    constraint: &ChcExpr,
    env: &FxHashMap<String, SmtValue>,
) {
    if !ground_backtranslation_debug() {
        return;
    }
    for (position, conjunct) in constraint.collect_conjuncts().iter().enumerate() {
        if !matches!(eval_ground(conjunct, env), Some(SmtValue::Bool(false))) {
            continue;
        }
        let bindings: Vec<String> = conjunct
            .vars()
            .into_iter()
            .take(6)
            .map(|var| match env.get(&var.name) {
                Some(value) => format!("{}={value:?}", var.name),
                None => format!("{}=<unbound>", var.name),
            })
            .collect();
        let rendered = truncate_debug_expr(conjunct.to_string());
        log_ground_translation_detail(format_args!(
            "step {step} (clause {clause_index}) conjunct {position} is FALSE; \
             bindings {bindings:?}; expr {rendered}"
        ));
        return;
    }
}

/// Bound a rendered diagnostic without slicing through a UTF-8 code point.
///
/// Expression identifiers are user-controlled and may contain non-ASCII
/// characters. Byte-indexing the rendered string at 220 made the debug-only
/// path panic when that offset landed inside a multi-byte character.
fn truncate_debug_expr(rendered: String) -> String {
    if rendered.len() <= 220 {
        return rendered;
    }
    let mut boundary = 220;
    while !rendered.is_char_boundary(boundary) {
        boundary -= 1;
    }
    format!("{}…", &rendered[..boundary])
}

/// Value equality for derivation argument passing.
///
/// Delegating to the shared tri-valued evaluator is load-bearing for arrays:
/// syntactic equality is too strict, while a different stored default does not
/// prove disequality when a finite index domain may be fully overridden. A
/// premise link is accepted only for decided semantic equality; `None` stays a
/// fail-closed mismatch.
fn smt_values_equal(lhs: &SmtValue, rhs: &SmtValue) -> bool {
    crate::expr::evaluate::smt_values_equal(lhs, rhs) == Some(true)
}
