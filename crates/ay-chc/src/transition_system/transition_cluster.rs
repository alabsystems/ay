// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Metadata-only model-checker transition-cluster extraction for solver-program pilots.
//!
//! This module deliberately stops at a deterministic external code generation descriptor. It
//! does not enqueue compiler work, install native code, or add runtime deopt
//! paths; those are owned by the solver-program runtime lanes.
//!
//! The legacy `Tla2*` item names and
//! [`TransitionSystem::tla2_transition_cluster_requests`] are retained for API
//! and stats-key compatibility. Internal hash domain-separation seeds use the
//! current `b"ay.model_checker.transition_cluster.*"` namespace.

use std::collections::BTreeMap;

use super::TransitionSystem;
use crate::{
    ActionId, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, PredicateId,
};

/// Semantic version for TLA2 transition-cluster normalization and lowering.
pub(crate) const TLA2_TRANSITION_CLUSTER_SEMANTIC_VERSION: u64 = 1;

/// Stable stats prefix for future TLA2 transition-cluster counters.
pub(crate) const TLA2_TRANSITION_CLUSTER_STATS_PREFIX: &str =
    "solver_program.tla2_transition_cluster";

const SOLVER_PROGRAM_DESCRIPTOR_SCHEMA_VERSION: u32 = 1;
const DEFAULT_MAX_CLUSTER_CLAUSES: u32 = 64;
const DEFAULT_MAX_EXPR_NODES: u32 = 20_000;
const FNV_OFFSET_BASIS: u64 = 0xcbf2_9ce4_8422_2325;
const FNV_PRIME: u64 = 0x0000_0100_0000_01b3;

/// Mutable-state epochs captured by a TLA2 transition-cluster request.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq, Hash)]
pub(crate) struct Tla2TransitionClusterEpochs {
    /// Clause/constraint arena generation.
    pub(crate) constraints: u64,
    /// Theory atom table generation.
    pub(crate) theory_atoms: u64,
    /// Simplex/LRA basis generation. TLA2 clusters do not use it, so callers
    /// should leave it at zero unless a future shared runtime requires it.
    pub(crate) basis: u64,
    /// Trail or assignment generation.
    pub(crate) trail: u64,
    /// Runtime policy/configuration generation.
    pub(crate) config: u64,
}

/// Deterministic invalidation key shaped like solver-program artifact keys.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Tla2TransitionClusterInvalidationKey {
    /// Mutable state epochs captured at request time.
    pub(crate) epochs: Tla2TransitionClusterEpochs,
    /// Deterministic shape hash for action, state variables, and clauses.
    pub(crate) shape_hash: u64,
    /// Deterministic semantic hash for normalization/lowering policy.
    pub(crate) semantic_hash: u64,
}

impl Tla2TransitionClusterInvalidationKey {
    /// Returns true when this key is still valid for the runtime key.
    #[must_use]
    pub(crate) fn is_valid_for(self, runtime: Self) -> bool {
        self == runtime
    }
}

/// Scalar state sorts admitted by the pilot extractor.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Tla2TransitionScalarSort {
    /// Boolean state or local variable.
    Bool,
    /// Integer state or local variable.
    Int,
}

impl Tla2TransitionScalarSort {
    fn try_from_chc(sort: &ChcSort) -> Option<Self> {
        match sort {
            ChcSort::Bool => Some(Self::Bool),
            ChcSort::Int => Some(Self::Int),
            _ => None,
        }
    }

    const fn stable_tag(self) -> u64 {
        match self {
            Self::Bool => 1,
            Self::Int => 2,
        }
    }
}

/// Canonical state-variable shape captured in cluster identity.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Tla2TransitionStateVar {
    /// Canonical variable name (`v0`, `v1`, ...).
    pub(crate) name: String,
    /// Supported scalar sort.
    pub(crate) sort: Tla2TransitionScalarSort,
}

/// Canonical clause shape captured in a transition cluster.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Tla2TransitionClauseShape {
    /// Index into `ChcProblem::clauses()`.
    pub(crate) clause_index: u32,
    /// Index among transition clauses, matching transition-system canonicalization.
    pub(crate) transition_ordinal: u32,
    /// Stable structural hash of the canonical transition constraint.
    pub(crate) constraint_hash: u64,
    /// Canonical transition constraint node count.
    pub(crate) constraint_nodes: u32,
}

/// One TLA2 action cluster considered as a future solver-program unit.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Tla2TransitionCluster {
    /// Single predicate represented by the extracted transition system.
    pub(crate) predicate: PredicateId,
    /// TLA2 action shared by the cluster clauses.
    pub(crate) action_id: ActionId,
    /// Human-readable TLA2 action name.
    pub(crate) action_name: String,
    /// Canonical state variables.
    pub(crate) state_vars: Vec<Tla2TransitionStateVar>,
    /// Canonical transition-clause shapes in problem order.
    pub(crate) clauses: Vec<Tla2TransitionClauseShape>,
}

/// Stable identity and profiling key for one TLA2 transition cluster.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Tla2TransitionClusterProfileKey {
    /// Predicate represented by the cluster.
    pub(crate) predicate: PredicateId,
    /// TLA2 action represented by the cluster.
    pub(crate) action_id: ActionId,
    /// Deterministic shape hash.
    pub(crate) shape_hash: u64,
    /// Deterministic semantic hash.
    pub(crate) semantic_hash: u64,
}

impl Tla2TransitionClusterProfileKey {
    /// Stable 64-bit hash for counters, snapshots, and artifact IDs.
    #[must_use]
    pub(crate) fn stable_hash(&self) -> u64 {
        let mut state = stable_hash_seed(b"ay.model_checker.transition_cluster.profile");
        stable_hash_u64(&mut state, self.predicate.index() as u64);
        stable_hash_u64(&mut state, self.action_id.index() as u64);
        stable_hash_u64(&mut state, self.shape_hash);
        stable_hash_u64(&mut state, self.semantic_hash);
        state
    }

    /// Stable stats prefix shared by this artifact family.
    #[must_use]
    pub(crate) const fn stats_prefix(&self) -> &'static str {
        TLA2_TRANSITION_CLUSTER_STATS_PREFIX
    }
}

/// Solver-program kind exposed by this descriptor bridge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Tla2SolverProgramKind {
    /// TLA2 action-local transition cluster.
    Tla2TransitionCluster,
}

/// Backend admitted by this descriptor bridge.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Tla2SolverProgramBackend {
    /// Active verified compiler path: ay emits ExternalCodegenIr and EXTERNAL_CODEGEN lowers it.
    ExternalCodegenBackend,
}

/// Compile timing admitted by this foundation slice.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Tla2TransitionClusterCompileTiming {
    /// Requests may only be handed to a future async/background compiler.
    BackgroundOnly,
}

/// Conservative guard evidence captured before a cluster may be compiled.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) struct Tla2TransitionClusterGuardMetadata {
    /// Runtime generations must be checked before applying the artifact.
    pub(crate) require_generation_match: bool,
    /// The generic CHC/PDR path must remain available for fallback.
    pub(crate) interpreter_fallback_available: bool,
    /// A differential/oracle check must be available before default-on use.
    pub(crate) oracle_check_available: bool,
    /// No compiled region frame may be active while installing/applying.
    pub(crate) no_active_compiled_frame: bool,
    /// Synchronous compilation is forbidden for this foundation slice.
    pub(crate) allow_synchronous_compile: bool,
    /// Conservative cap on the number of clauses captured by one cluster.
    pub(crate) max_cluster_clauses: u32,
    /// Conservative cap on one canonical transition expression.
    pub(crate) max_expr_nodes: u32,
}

impl Tla2TransitionClusterGuardMetadata {
    /// Fail-closed guard metadata for pre-production TLA2 clusters.
    #[must_use]
    pub(crate) const fn conservative() -> Self {
        Self {
            require_generation_match: true,
            interpreter_fallback_available: true,
            oracle_check_available: true,
            no_active_compiled_frame: true,
            allow_synchronous_compile: false,
            max_cluster_clauses: DEFAULT_MAX_CLUSTER_CLAUSES,
            max_expr_nodes: DEFAULT_MAX_EXPR_NODES,
        }
    }

    /// Returns true when the guard metadata satisfies the conservative contract.
    #[must_use]
    pub(crate) const fn satisfies_conservative_contract(self) -> bool {
        self.require_generation_match
            && self.interpreter_fallback_available
            && self.oracle_check_available
            && self.no_active_compiled_frame
            && !self.allow_synchronous_compile
            && self.max_cluster_clauses > 0
            && self.max_cluster_clauses <= DEFAULT_MAX_CLUSTER_CLAUSES
            && self.max_expr_nodes > 0
            && self.max_expr_nodes <= DEFAULT_MAX_EXPR_NODES
    }
}

/// Metadata-only bridge to the solver-program artifact contract.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Tla2TransitionClusterSolverProgramDescriptor {
    /// Serialized descriptor schema version.
    pub(crate) schema_version: u32,
    /// Solver-program region represented by this descriptor.
    pub(crate) kind: Tla2SolverProgramKind,
    /// Required compiler backend.
    pub(crate) backend: Tla2SolverProgramBackend,
    /// Semantic hash for normalization and lowering policy.
    pub(crate) semantic_version: u64,
    /// Invalidation key captured at extraction time.
    pub(crate) invalidation_key: Tla2TransitionClusterInvalidationKey,
    /// Guard/oracle requirements for safe future application.
    pub(crate) guards: Tla2TransitionClusterGuardMetadata,
    /// Compile timing admitted by this request.
    pub(crate) compile_timing: Tla2TransitionClusterCompileTiming,
    /// Stable stats prefix for observability.
    pub(crate) stats_prefix: &'static str,
    /// Explicitly records that the descriptor requires external code generation lowering.
    pub(crate) external_codegen_backend_backend_required: bool,
}

impl Tla2TransitionClusterSolverProgramDescriptor {
    /// Whether this descriptor admits only the external code generation backend.
    #[must_use]
    pub(crate) const fn requires_external_codegen_backend_only(&self) -> bool {
        matches!(
            self.backend,
            Tla2SolverProgramBackend::ExternalCodegenBackend
        ) && self.external_codegen_backend_backend_required
    }
}

/// Metadata-only request for a future TLA2 transition-cluster solver program.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct Tla2TransitionClusterRequest {
    /// Action-local transition cluster.
    pub(crate) cluster: Tla2TransitionCluster,
    /// Stable identity and profiling key.
    pub(crate) profile_key: Tla2TransitionClusterProfileKey,
    /// Solver-program-shaped descriptor.
    pub(crate) solver_program: Tla2TransitionClusterSolverProgramDescriptor,
}

impl Tla2TransitionClusterRequest {
    /// This request contains metadata only; native code is produced elsewhere.
    #[must_use]
    pub(crate) const fn is_metadata_only(&self) -> bool {
        true
    }
}

/// Conservative reason a candidate cluster cannot be described for compilation.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) enum Tla2TransitionClusterRejection {
    /// Runtime generation matching was not captured.
    MissingGenerationGuard,
    /// Generic fallback was unavailable.
    MissingInterpreterFallback,
    /// Differential/oracle validation was unavailable.
    MissingOracleCheck,
    /// A compiled region frame was already active.
    ActiveCompiledFrame,
    /// The caller attempted to permit synchronous compilation.
    SynchronousCompileForbidden,
    /// The caller supplied transition-cluster caps outside the conservative range.
    GuardLimitOutOfRange {
        max_cluster_clauses: u32,
        max_expr_nodes: u32,
    },
    /// The problem did not declare TLA2 actions.
    MissingActionDecomposition,
    /// The pilot handles one transition-system predicate.
    MultiplePredicates { count: usize },
    /// A clause body had multiple predicate applications.
    NonLinearClause { clause_index: usize },
    /// A canonical state variable had an unsupported sort.
    UnsupportedStateSort { var_name: String, sort: ChcSort },
    /// No transition clauses were available to cluster.
    NoTransitionClauses,
    /// A transition clause was not tagged with a TLA2 action.
    UntaggedTransition { clause_index: usize },
    /// A transition clause referenced an undeclared TLA2 action.
    UnknownAction {
        clause_index: usize,
        action_id: ActionId,
    },
    /// A transition did not map the single predicate to itself.
    TransitionPredicateMismatch { clause_index: usize },
    /// A canonical transition expression is outside the admitted pilot fragment.
    UnsupportedExpression {
        clause_index: usize,
        reason: Tla2TransitionClusterExpressionRejection,
    },
    /// The problem or cluster exceeded a conservative metadata cap.
    ClusterTooLarge { action_id: Option<ActionId> },
}

/// Reason one expression is outside the admitted TLA2 pilot fragment.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Tla2TransitionClusterExpressionRejection {
    /// An expression sort was outside scalar Bool/Int.
    UnsupportedSort,
    /// An operator requires lowering that this foundation slice has not admitted.
    UnsupportedOperator,
    /// A literal or expression form was outside scalar Bool/Int.
    NonScalarLiteral,
    /// Expression exceeded the conservative descriptor cap.
    ExpressionTooLarge,
    /// Operator arity or child sorts were malformed for the admitted fragment.
    MalformedOperator,
}

impl TransitionSystem {
    /// Extract deterministic, metadata-only TLA2 transition-cluster requests.
    pub(crate) fn tla2_transition_cluster_requests(
        problem: &ChcProblem,
        epochs: Tla2TransitionClusterEpochs,
        guards: Tla2TransitionClusterGuardMetadata,
    ) -> Result<Vec<Tla2TransitionClusterRequest>, Tla2TransitionClusterRejection> {
        validate_guards(guards)?;

        if !problem.has_action_decomposition() {
            return Err(Tla2TransitionClusterRejection::MissingActionDecomposition);
        }
        if problem.predicates().len() != 1 {
            return Err(Tla2TransitionClusterRejection::MultiplePredicates {
                count: problem.predicates().len(),
            });
        }
        for (clause_index, clause) in problem.clauses().iter().enumerate() {
            if clause.body.predicates.len() > 1 {
                return Err(Tla2TransitionClusterRejection::NonLinearClause { clause_index });
            }
        }

        let pred = &problem.predicates()[0];
        let pred_id = pred.id;
        let state_vars = canonical_state_vars(pred)?;
        let canonical_vars: Vec<ChcVar> = pred
            .arg_sorts
            .iter()
            .enumerate()
            .map(|(i, sort)| ChcVar::new(format!("v{i}"), sort.clone()))
            .collect();

        let mut clusters: BTreeMap<ActionId, PartialCluster> = BTreeMap::new();
        let mut saw_transition = false;

        for (transition_ordinal, (clause_index, clause)) in problem
            .clauses()
            .iter()
            .enumerate()
            .filter(|(_, clause)| !clause.is_fact() && !clause.is_query())
            .enumerate()
        {
            saw_transition = true;
            validate_self_transition_clause(clause, pred_id).map_err(|()| {
                Tla2TransitionClusterRejection::TransitionPredicateMismatch { clause_index }
            })?;

            let action_id = clause
                .action_id
                .ok_or(Tla2TransitionClusterRejection::UntaggedTransition { clause_index })?;
            let action_name = problem.action_name(action_id).ok_or(
                Tla2TransitionClusterRejection::UnknownAction {
                    clause_index,
                    action_id,
                },
            )?;

            let canonical = Self::canonical_transition_clause_constraint(
                clause,
                pred_id,
                &canonical_vars,
                transition_ordinal,
            )
            .ok_or(Tla2TransitionClusterRejection::TransitionPredicateMismatch { clause_index })?;

            let constraint_nodes = validate_supported_expr(&canonical, guards.max_expr_nodes)
                .map_err(
                    |reason| Tla2TransitionClusterRejection::UnsupportedExpression {
                        clause_index,
                        reason,
                    },
                )?;

            let clause_shape = Tla2TransitionClauseShape {
                clause_index: u32::try_from(clause_index).map_err(|_| {
                    Tla2TransitionClusterRejection::ClusterTooLarge {
                        action_id: Some(action_id),
                    }
                })?,
                transition_ordinal: u32::try_from(transition_ordinal).map_err(|_| {
                    Tla2TransitionClusterRejection::ClusterTooLarge {
                        action_id: Some(action_id),
                    }
                })?,
                constraint_hash: stable_expr_hash(&canonical),
                constraint_nodes,
            };

            clusters
                .entry(action_id)
                .or_insert_with(|| PartialCluster {
                    action_name: action_name.to_string(),
                    clauses: Vec::new(),
                })
                .clauses
                .push(clause_shape);
        }

        if !saw_transition {
            return Err(Tla2TransitionClusterRejection::NoTransitionClauses);
        }

        clusters
            .into_iter()
            .map(|(action_id, partial)| {
                if partial.clauses.len() > guards.max_cluster_clauses as usize {
                    return Err(Tla2TransitionClusterRejection::ClusterTooLarge {
                        action_id: Some(action_id),
                    });
                }

                let cluster = Tla2TransitionCluster {
                    predicate: pred_id,
                    action_id,
                    action_name: partial.action_name,
                    state_vars: state_vars.clone(),
                    clauses: partial.clauses,
                };
                let shape_hash = stable_cluster_shape_hash(&cluster);
                let semantic_hash = stable_semantic_hash();
                let profile_key = Tla2TransitionClusterProfileKey {
                    predicate: pred_id,
                    action_id,
                    shape_hash,
                    semantic_hash,
                };
                let invalidation_key = Tla2TransitionClusterInvalidationKey {
                    epochs,
                    shape_hash,
                    semantic_hash,
                };
                let solver_program = Tla2TransitionClusterSolverProgramDescriptor {
                    schema_version: SOLVER_PROGRAM_DESCRIPTOR_SCHEMA_VERSION,
                    kind: Tla2SolverProgramKind::Tla2TransitionCluster,
                    backend: Tla2SolverProgramBackend::ExternalCodegenBackend,
                    semantic_version: semantic_hash,
                    invalidation_key,
                    guards,
                    compile_timing: Tla2TransitionClusterCompileTiming::BackgroundOnly,
                    stats_prefix: TLA2_TRANSITION_CLUSTER_STATS_PREFIX,
                    external_codegen_backend_backend_required: true,
                };

                Ok(Tla2TransitionClusterRequest {
                    cluster,
                    profile_key,
                    solver_program,
                })
            })
            .collect()
    }
}

struct PartialCluster {
    action_name: String,
    clauses: Vec<Tla2TransitionClauseShape>,
}

fn validate_guards(
    guards: Tla2TransitionClusterGuardMetadata,
) -> Result<(), Tla2TransitionClusterRejection> {
    if !guards.require_generation_match {
        return Err(Tla2TransitionClusterRejection::MissingGenerationGuard);
    }
    if !guards.interpreter_fallback_available {
        return Err(Tla2TransitionClusterRejection::MissingInterpreterFallback);
    }
    if !guards.oracle_check_available {
        return Err(Tla2TransitionClusterRejection::MissingOracleCheck);
    }
    if !guards.no_active_compiled_frame {
        return Err(Tla2TransitionClusterRejection::ActiveCompiledFrame);
    }
    if guards.allow_synchronous_compile {
        return Err(Tla2TransitionClusterRejection::SynchronousCompileForbidden);
    }
    if guards.max_cluster_clauses == 0
        || guards.max_cluster_clauses > DEFAULT_MAX_CLUSTER_CLAUSES
        || guards.max_expr_nodes == 0
        || guards.max_expr_nodes > DEFAULT_MAX_EXPR_NODES
    {
        return Err(Tla2TransitionClusterRejection::GuardLimitOutOfRange {
            max_cluster_clauses: guards.max_cluster_clauses,
            max_expr_nodes: guards.max_expr_nodes,
        });
    }
    Ok(())
}

fn canonical_state_vars(
    pred: &crate::Predicate,
) -> Result<Vec<Tla2TransitionStateVar>, Tla2TransitionClusterRejection> {
    pred.arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| {
            let var_name = format!("v{i}");
            let sort = Tla2TransitionScalarSort::try_from_chc(sort).ok_or_else(|| {
                Tla2TransitionClusterRejection::UnsupportedStateSort {
                    var_name: var_name.clone(),
                    sort: sort.clone(),
                }
            })?;
            Ok(Tla2TransitionStateVar {
                name: var_name,
                sort,
            })
        })
        .collect()
}

fn validate_self_transition_clause(clause: &HornClause, pred_id: PredicateId) -> Result<(), ()> {
    if clause.body.predicates.len() != 1 {
        return Err(());
    }
    let (body_pred, _) = &clause.body.predicates[0];
    if *body_pred != pred_id {
        return Err(());
    }
    match &clause.head {
        ClauseHead::Predicate(head_pred, _) if *head_pred == pred_id => Ok(()),
        _ => Err(()),
    }
}

fn validate_supported_expr(
    expr: &ChcExpr,
    max_expr_nodes: u32,
) -> Result<u32, Tla2TransitionClusterExpressionRejection> {
    let limit = (max_expr_nodes as usize).saturating_add(1);
    let node_count = expr.node_count(limit);
    if node_count > max_expr_nodes as usize {
        return Err(Tla2TransitionClusterExpressionRejection::ExpressionTooLarge);
    }
    validate_supported_expr_inner(expr)?;
    u32::try_from(node_count)
        .map_err(|_| Tla2TransitionClusterExpressionRejection::ExpressionTooLarge)
}

fn validate_supported_expr_inner(
    expr: &ChcExpr,
) -> Result<(), Tla2TransitionClusterExpressionRejection> {
    match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) => Ok(()),
        ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
            Err(Tla2TransitionClusterExpressionRejection::NonScalarLiteral)
        }
        ChcExpr::Var(var) => validate_supported_sort(&var.sort).map(|_| ()),
        ChcExpr::Op(op, args) => {
            validate_supported_op(*op, args)?;
            for arg in args {
                validate_supported_expr_inner(arg)?;
            }
            Ok(())
        }
        ChcExpr::PredicateApp(_, _, _)
        | ChcExpr::FuncApp(_, _, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_)
        | ChcExpr::ConstArray(_, _) => {
            Err(Tla2TransitionClusterExpressionRejection::UnsupportedOperator)
        }
    }
}

fn validate_supported_op(
    op: ChcOp,
    args: &[std::sync::Arc<ChcExpr>],
) -> Result<(), Tla2TransitionClusterExpressionRejection> {
    match op {
        ChcOp::Not => {
            require_arity(args, 1)?;
            require_bool(args)
        }
        ChcOp::And | ChcOp::Or => require_bool(args),
        ChcOp::Implies | ChcOp::Iff => {
            require_arity(args, 2)?;
            require_bool(args)
        }
        ChcOp::Add | ChcOp::Sub => {
            require_non_empty(args)?;
            require_int(args)
        }
        ChcOp::Neg => {
            require_arity(args, 1)?;
            require_int(args)
        }
        ChcOp::Eq | ChcOp::Ne => {
            require_arity(args, 2)?;
            let left = validate_supported_sort(&args[0].sort())?;
            let right = validate_supported_sort(&args[1].sort())?;
            if left == right {
                Ok(())
            } else {
                Err(Tla2TransitionClusterExpressionRejection::MalformedOperator)
            }
        }
        ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge => {
            require_arity(args, 2)?;
            require_int(args)
        }
        _ => Err(Tla2TransitionClusterExpressionRejection::UnsupportedOperator),
    }
}

fn require_arity(
    args: &[std::sync::Arc<ChcExpr>],
    expected: usize,
) -> Result<(), Tla2TransitionClusterExpressionRejection> {
    if args.len() == expected {
        Ok(())
    } else {
        Err(Tla2TransitionClusterExpressionRejection::MalformedOperator)
    }
}

fn require_non_empty(
    args: &[std::sync::Arc<ChcExpr>],
) -> Result<(), Tla2TransitionClusterExpressionRejection> {
    if args.is_empty() {
        Err(Tla2TransitionClusterExpressionRejection::MalformedOperator)
    } else {
        Ok(())
    }
}

fn require_bool(
    args: &[std::sync::Arc<ChcExpr>],
) -> Result<(), Tla2TransitionClusterExpressionRejection> {
    for arg in args {
        if validate_supported_sort(&arg.sort())? != Tla2TransitionScalarSort::Bool {
            return Err(Tla2TransitionClusterExpressionRejection::MalformedOperator);
        }
    }
    Ok(())
}

fn require_int(
    args: &[std::sync::Arc<ChcExpr>],
) -> Result<(), Tla2TransitionClusterExpressionRejection> {
    for arg in args {
        if validate_supported_sort(&arg.sort())? != Tla2TransitionScalarSort::Int {
            return Err(Tla2TransitionClusterExpressionRejection::MalformedOperator);
        }
    }
    Ok(())
}

fn validate_supported_sort(
    sort: &ChcSort,
) -> Result<Tla2TransitionScalarSort, Tla2TransitionClusterExpressionRejection> {
    Tla2TransitionScalarSort::try_from_chc(sort)
        .ok_or(Tla2TransitionClusterExpressionRejection::UnsupportedSort)
}

fn stable_semantic_hash() -> u64 {
    let mut state = stable_hash_seed(b"ay.model_checker.transition_cluster.semantic");
    stable_hash_u64(&mut state, TLA2_TRANSITION_CLUSTER_SEMANTIC_VERSION);
    stable_hash_bytes(&mut state, b"external_codegen_backend");
    stable_hash_bytes(&mut state, b"scalar_bool_int_linear");
    state
}

fn stable_cluster_shape_hash(cluster: &Tla2TransitionCluster) -> u64 {
    let mut state = stable_hash_seed(b"ay.model_checker.transition_cluster.shape");
    stable_hash_u64(&mut state, cluster.predicate.index() as u64);
    stable_hash_u64(&mut state, cluster.action_id.index() as u64);
    stable_hash_bytes(&mut state, cluster.action_name.as_bytes());
    stable_hash_u64(&mut state, cluster.state_vars.len() as u64);
    for var in &cluster.state_vars {
        stable_hash_bytes(&mut state, var.name.as_bytes());
        stable_hash_u64(&mut state, var.sort.stable_tag());
    }
    stable_hash_u64(&mut state, cluster.clauses.len() as u64);
    for clause in &cluster.clauses {
        stable_hash_u64(&mut state, u64::from(clause.clause_index));
        stable_hash_u64(&mut state, u64::from(clause.transition_ordinal));
        stable_hash_u64(&mut state, clause.constraint_hash);
        stable_hash_u64(&mut state, u64::from(clause.constraint_nodes));
    }
    state
}

fn stable_expr_hash(expr: &ChcExpr) -> u64 {
    let mut state = stable_hash_seed(b"ay.model_checker.transition_cluster.expr");
    stable_hash_expr(&mut state, expr);
    state
}

fn stable_hash_expr(state: &mut u64, expr: &ChcExpr) {
    match expr {
        ChcExpr::Bool(value) => {
            stable_hash_u64(state, 1);
            stable_hash_bool(state, *value);
        }
        ChcExpr::Int(value) => {
            stable_hash_u64(state, 2);
            stable_hash_i128(state, *value);
        }
        ChcExpr::Real(num, den) => {
            stable_hash_u64(state, 3);
            stable_hash_i64(state, *num);
            stable_hash_i64(state, *den);
        }
        ChcExpr::BitVec(value, width) => {
            stable_hash_u64(state, 4);
            stable_hash_u128(state, *value);
            stable_hash_u64(state, u64::from(*width));
        }
        ChcExpr::Var(var) => {
            stable_hash_u64(state, 5);
            stable_hash_bytes(state, var.name.as_bytes());
            stable_hash_sort(state, &var.sort);
        }
        ChcExpr::Op(op, args) => {
            stable_hash_u64(state, 6);
            stable_hash_bytes(state, format!("{op:?}").as_bytes());
            stable_hash_u64(state, args.len() as u64);
            for arg in args {
                stable_hash_expr(state, arg);
            }
        }
        ChcExpr::PredicateApp(name, pred, args) => {
            stable_hash_u64(state, 7);
            stable_hash_bytes(state, name.as_bytes());
            stable_hash_u64(state, pred.index() as u64);
            stable_hash_u64(state, args.len() as u64);
            for arg in args {
                stable_hash_expr(state, arg);
            }
        }
        ChcExpr::FuncApp(name, sort, args) => {
            stable_hash_u64(state, 8);
            stable_hash_bytes(state, name.as_bytes());
            stable_hash_sort(state, sort);
            stable_hash_u64(state, args.len() as u64);
            for arg in args {
                stable_hash_expr(state, arg);
            }
        }
        ChcExpr::ConstArrayMarker(sort) => {
            stable_hash_u64(state, 9);
            stable_hash_sort(state, sort);
        }
        ChcExpr::IsTesterMarker(name) => {
            stable_hash_u64(state, 10);
            stable_hash_bytes(state, name.as_bytes());
        }
        ChcExpr::ConstArray(key_sort, value) => {
            stable_hash_u64(state, 11);
            stable_hash_sort(state, key_sort);
            stable_hash_expr(state, value);
        }
    }
}

fn stable_hash_sort(state: &mut u64, sort: &ChcSort) {
    match sort {
        ChcSort::Bool => stable_hash_u64(state, 1),
        ChcSort::Int => stable_hash_u64(state, 2),
        ChcSort::Real => stable_hash_u64(state, 3),
        ChcSort::BitVec(width) => {
            stable_hash_u64(state, 4);
            stable_hash_u64(state, u64::from(*width));
        }
        ChcSort::Array(key, value) => {
            stable_hash_u64(state, 5);
            stable_hash_sort(state, key);
            stable_hash_sort(state, value);
        }
        ChcSort::Uninterpreted(name) => {
            stable_hash_u64(state, 6);
            stable_hash_bytes(state, name.as_bytes());
        }
        ChcSort::Datatype { name, constructors } => {
            stable_hash_u64(state, 7);
            stable_hash_bytes(state, name.as_bytes());
            stable_hash_u64(state, constructors.len() as u64);
            for constructor in constructors.iter() {
                stable_hash_bytes(state, constructor.name.as_bytes());
                stable_hash_u64(state, constructor.selectors.len() as u64);
                for selector in &constructor.selectors {
                    stable_hash_bytes(state, selector.name.as_bytes());
                    stable_hash_sort(state, &selector.sort);
                }
            }
        }
    }
}

fn stable_hash_seed(domain: &[u8]) -> u64 {
    let mut state = FNV_OFFSET_BASIS;
    stable_hash_bytes(&mut state, domain);
    state
}

fn stable_hash_bytes(state: &mut u64, bytes: &[u8]) {
    stable_hash_u64(state, bytes.len() as u64);
    for byte in bytes {
        *state ^= u64::from(*byte);
        *state = state.wrapping_mul(FNV_PRIME);
    }
}

fn stable_hash_bool(state: &mut u64, value: bool) {
    stable_hash_u64(state, u64::from(value));
}

fn stable_hash_u64(state: &mut u64, value: u64) {
    for byte in value.to_le_bytes() {
        *state ^= u64::from(byte);
        *state = state.wrapping_mul(FNV_PRIME);
    }
}

fn stable_hash_i64(state: &mut u64, value: i64) {
    for byte in value.to_le_bytes() {
        *state ^= u64::from(byte);
        *state = state.wrapping_mul(FNV_PRIME);
    }
}

fn stable_hash_i128(state: &mut u64, value: i128) {
    for byte in value.to_le_bytes() {
        *state ^= u64::from(byte);
        *state = state.wrapping_mul(FNV_PRIME);
    }
}

fn stable_hash_u128(state: &mut u64, value: u128) {
    for byte in value.to_le_bytes() {
        *state ^= u64::from(byte);
        *state = state.wrapping_mul(FNV_PRIME);
    }
}
