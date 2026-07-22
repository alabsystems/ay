// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Fail-closed projection for Solidity-style arrays of struct-like datatypes.
//!
//! This prototype handles the narrow shape `Array K DT`, where `DT` has exactly
//! one constructor and non-DT fields. A predicate argument of that sort is
//! projected to one array argument per constructor field:
//!
//! `P(a: Array K Pair{lo:T, hi:U})` becomes `P(a__lo: Array K T, a__hi: Array K U)`.
//!
//! The module is intentionally not wired into the solving pipeline yet. Callers
//! must opt in through `SolidityArrayDtProjector::project`, which reports
//! `NotApplicable` or `Unsupported` instead of silently leaving risky shapes
//! half-transformed.

use std::sync::{Arc, Mutex};

use ay_core::kani_compat::DetHashSet as FxHashSet;

use crate::{
    ChcDtConstructor, ChcDtSelector, ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseBody,
    ClauseHead, Counterexample, HornClause, InvariantModel, PredicateId, PredicateInterpretation,
};

use super::{
    BackTranslator, IdentityBackTranslator, TransformMemoryReport, TransformObligation,
    TransformationResult, Transformer, ValidityWitness,
};

/// Prototype projector for `Array K SingleCtorDT` predicate arguments.
pub(crate) struct SolidityArrayDtProjector;

/// Result of attempting the Solidity ADT-array projection.
#[derive(Debug)]
pub(crate) enum SolidityArrayDtProjectionOutcome {
    /// A new problem with at least one predicate argument projected.
    Projected {
        problem: ChcProblem,
        projected_args: usize,
        stats: SolidityArrayDtProjectionStats,
        plans: Vec<PredicateProjectionPlan>,
    },
    /// The problem has no direct predicate arguments of the supported shape.
    NotApplicable,
    /// A relevant ADT-array shape was found, but the prototype cannot rewrite
    /// every use while preserving shape.
    Unsupported(SolidityArrayDtProjectionRejection),
}

/// Route-level applicability result for the Solidity ADT-array projection.
///
/// This is intentionally separate from [`SolidityArrayDtProjectionOutcome`]:
/// callers that only need a routing decision can distinguish
/// `NotApplicable` from an identity/fail-closed transform without running the
/// transformer and inspecting whether the problem changed.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SolidityArrayDtProjectionRoute {
    /// The projection can rewrite this problem safely.
    Applicable {
        stats: SolidityArrayDtProjectionStats,
    },
    /// No direct predicate arguments have the supported `Array K SingleCtorDT`
    /// shape.
    NotApplicable {
        stats: SolidityArrayDtProjectionStats,
    },
    /// A projection-relevant shape exists, but this prototype must fail closed.
    Unsupported {
        stats: SolidityArrayDtProjectionStats,
        reason: SolidityArrayDtProjectionRejection,
    },
}

impl SolidityArrayDtProjectionRoute {
    pub(crate) fn is_applicable(&self) -> bool {
        matches!(self, Self::Applicable { .. })
    }

    pub(crate) fn stats(&self) -> &SolidityArrayDtProjectionStats {
        match self {
            Self::Applicable { stats }
            | Self::NotApplicable { stats }
            | Self::Unsupported { stats, .. } => stats,
        }
    }
}

/// Signature-level projection statistics used by route selection.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub(crate) struct SolidityArrayDtProjectionStats {
    /// Number of predicates in the input problem.
    pub(crate) predicates: usize,
    /// Number of original predicate arguments across all predicates.
    pub(crate) predicate_args: usize,
    /// Number of predicates with at least one projected argument.
    pub(crate) projected_predicates: usize,
    /// Number of original predicate arguments selected for projection.
    pub(crate) projected_args: usize,
    /// Number of field-array arguments emitted by those projected arguments.
    pub(crate) projected_field_args: usize,
    /// Net predicate-arity growth after replacing projected arguments.
    pub(crate) added_predicate_args: usize,
}

/// Fail-closed rejection reason for the prototype projection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum SolidityArrayDtProjectionRejection {
    NonSingleConstructorArrayElement {
        datatype: String,
        constructors: usize,
    },
    EmptyConstructorArrayElement {
        datatype: String,
    },
    DatatypeNestedInArrayElementField {
        datatype: String,
        field: String,
    },
    DatatypeNestedInArrayKey {
        datatype: String,
    },
    NestedArrayDtArgument {
        sort: ChcSort,
    },
    PredicateArgumentCountMismatch {
        predicate: PredicateId,
        expected: usize,
        actual: usize,
    },
    UnsupportedArrayExpression {
        context: &'static str,
        sort: ChcSort,
    },
    UnsupportedDatatypeExpression {
        context: &'static str,
        sort: ChcSort,
    },
}

type ProjectionResult<T> = Result<T, SolidityArrayDtProjectionRejection>;

#[derive(Debug, Clone)]
struct ArrayDtProjection {
    array_sort: ChcSort,
    key_sort: ChcSort,
    dt: SingleCtorDt,
}

#[derive(Debug, Clone)]
struct SingleCtorDt {
    sort: ChcSort,
    ctor: ChcDtConstructor,
}

#[derive(Debug, Clone)]
enum PredArgPlan {
    Original {
        original_arg: usize,
    },
    Projected {
        original_arg: usize,
        info: ArrayDtProjection,
    },
}

#[derive(Debug, Clone)]
pub(crate) struct PredicateProjectionPlan {
    args: Vec<PredArgPlan>,
    field_obligations: Vec<ProjectedArrayFieldObligation>,
}

/// Backtranslation/refinement obligation for one projected field array.
///
/// If validation of the original problem fails after a SAFE result, this record
/// identifies the original array argument, key sort, projected field array sort,
/// and selector needed to add pointwise refinement facts for remembered keys.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct ProjectedArrayFieldObligation {
    pub(crate) original_arg: usize,
    pub(crate) field_idx: usize,
    pub(crate) key_sort: ChcSort,
    pub(crate) original_array_sort: ChcSort,
    pub(crate) projected_array_sort: ChcSort,
    pub(crate) selector: ChcDtSelector,
}

/// Transformer wrapper for the fail-closed Solidity array-DT projection.
///
/// This intentionally does not panic or half-transform unsupported formulas. If
/// the narrow projection cannot be applied, the transformer returns the original
/// problem with an identity backtranslator.
pub(crate) struct SolidityArrayDtProjectionTransformer {
    verbose: bool,
}

impl SolidityArrayDtProjectionTransformer {
    pub(crate) fn new() -> Self {
        Self { verbose: false }
    }

    pub(crate) fn with_verbose(mut self, verbose: bool) -> Self {
        self.verbose = verbose;
        self
    }
}

impl Transformer for SolidityArrayDtProjectionTransformer {
    fn transform(self: Box<Self>, problem: ChcProblem) -> TransformationResult {
        let original_predicate_sorts: Vec<Vec<ChcSort>> = problem
            .predicates()
            .iter()
            .map(|pred| pred.arg_sorts.clone())
            .collect();

        match build_projection_plans(&problem) {
            Ok((_plans, 0)) => TransformationResult {
                problem,
                back_translator: Box::new(IdentityBackTranslator),
            },
            Ok((plans, _projected_args)) => match project_problem(&problem, &plans) {
                Ok(projected) => {
                    let source_observed_keys = collect_source_projected_array_keys(&problem);
                    TransformationResult {
                        problem: projected,
                        back_translator: Box::new(SolidityArrayDtProjectionBackTranslator {
                            original_predicate_sorts,
                            plans,
                            observed_keys: Arc::new(Mutex::new(ObservedProjectedArrayKeys {
                                source: source_observed_keys,
                                backtranslated: Vec::new(),
                            })),
                        }),
                    }
                }
                Err(reason) => {
                    if self.verbose {
                        tracing::debug!(
                            reason = ?reason,
                            "SolidityArrayDtProjection: unsupported formula; leaving problem unchanged"
                        );
                    }
                    TransformationResult {
                        problem,
                        back_translator: Box::new(IdentityBackTranslator),
                    }
                }
            },
            Err(reason) => {
                if self.verbose {
                    tracing::debug!(
                        reason = ?reason,
                        "SolidityArrayDtProjection: unsupported signature; leaving problem unchanged"
                    );
                }
                TransformationResult {
                    problem,
                    back_translator: Box::new(IdentityBackTranslator),
                }
            }
        }
    }
}

struct SolidityArrayDtProjectionBackTranslator {
    original_predicate_sorts: Vec<Vec<ChcSort>>,
    plans: Vec<PredicateProjectionPlan>,
    observed_keys: Arc<Mutex<ObservedProjectedArrayKeys>>,
}

#[derive(Clone)]
struct ProjectedFieldBinding {
    original_var: ChcVar,
    obligation: ProjectedArrayFieldObligation,
}

#[derive(Debug, Clone)]
#[allow(dead_code)]
struct ObservedProjectedArrayKey {
    key: ChcExpr,
    obligation: ProjectedArrayFieldObligation,
}

#[derive(Debug, Clone, Default)]
struct ObservedProjectedArrayKeys {
    source: Vec<ObservedProjectedArrayKey>,
    backtranslated: Vec<ObservedProjectedArrayKey>,
}

impl BackTranslator for SolidityArrayDtProjectionBackTranslator {
    fn translate_validity(&self, witness: ValidityWitness) -> ValidityWitness {
        let mut result = InvariantModel::new();
        let mut observed_keys = Vec::new();

        for (pid, interp) in witness.iter() {
            let Some(plan) = self.plans.get(pid.index()) else {
                result.set(*pid, interp.clone());
                continue;
            };
            let Some(original_sorts) = self.original_predicate_sorts.get(pid.index()) else {
                result.set(*pid, interp.clone());
                continue;
            };

            match translate_projection_interpretation(
                *pid,
                interp,
                original_sorts,
                plan,
                &mut observed_keys,
            ) {
                Ok(translated) => result.set(*pid, translated),
                Err(()) => {
                    // Fail closed: invalid arity makes portfolio/PDR validation reject
                    // this candidate instead of accepting an under-translated SAFE model.
                    result.set(
                        *pid,
                        PredicateInterpretation::new(Vec::new(), ChcExpr::Bool(false)),
                    );
                }
            }
        }

        if !observed_keys.is_empty() {
            if let Ok(mut remembered) = self.observed_keys.lock() {
                remembered.backtranslated.extend(observed_keys);
            }
        }

        result
    }

    fn translate_invalidity(&self, _witness: Counterexample) -> Counterexample {
        // Projection splits array-of-DT predicate arguments into several array
        // arguments. Concrete reconstruction for UNSAFE witnesses is not
        // implemented here, so return a deliberately invalid empty trace. The
        // portfolio's mandatory unsafe validation will demote it to Unknown.
        Counterexample::new(Vec::new())
    }

    fn transform_memory(&self) -> TransformMemoryReport {
        let (source_observed_keys, backtranslated_observed_keys) = self
            .observed_keys
            .lock()
            .map(|keys| (keys.source.len(), keys.backtranslated.len()))
            .unwrap_or_default();
        let observed_keys = source_observed_keys + backtranslated_observed_keys;
        let refinement_indices = self.array_refinement_indices().len();
        let projected_predicate_args = self
            .plans
            .iter()
            .flat_map(|plan| &plan.args)
            .filter(|arg| matches!(arg, PredArgPlan::Projected { .. }))
            .count();
        let projected_field_obligations: usize = self
            .plans
            .iter()
            .map(|plan| plan.field_obligations.len())
            .sum();

        TransformMemoryReport::with_original_validation_obligations(
            "solidity_array_dt_projection",
            [
                TransformObligation::named("projected-array-field-backtranslation"),
                TransformObligation::named("observed-select-store-key-refinement"),
                TransformObligation::named("original-validation-on-safe"),
                TransformObligation::named("unsafe-demotion-required"),
            ],
        )
        .with_fact("projection_predicate_maps", self.plans.len().to_string())
        .with_fact(
            "projected_predicate_args",
            projected_predicate_args.to_string(),
        )
        .with_fact(
            "projected_field_obligations",
            projected_field_obligations.to_string(),
        )
        .with_fact(
            "source_observed_projected_array_keys",
            source_observed_keys.to_string(),
        )
        .with_fact(
            "backtranslated_projected_array_keys",
            backtranslated_observed_keys.to_string(),
        )
        .with_fact("observed_projected_array_keys", observed_keys.to_string())
        .with_fact("array_refinement_indices", refinement_indices.to_string())
        .with_incomplete_unsafe_backtranslation()
    }

    fn array_refinement_indices(&self) -> Vec<(ChcSort, ChcExpr)> {
        let Ok(keys) = self.observed_keys.lock() else {
            return Vec::new();
        };
        let mut seen = FxHashSet::default();
        keys.source
            .iter()
            .chain(keys.backtranslated.iter())
            .filter_map(|key| {
                let index = (key.obligation.key_sort.clone(), key.key.clone());
                seen.insert(index.clone()).then_some(index)
            })
            .collect()
    }
}

impl SolidityArrayDtProjector {
    pub(crate) fn route(problem: &ChcProblem) -> SolidityArrayDtProjectionRoute {
        match build_projection_plans(problem) {
            Ok((plans, projected_args)) => {
                let stats = projection_stats(problem, &plans, projected_args);
                if projected_args == 0 {
                    SolidityArrayDtProjectionRoute::NotApplicable { stats }
                } else {
                    match project_problem(problem, &plans) {
                        Ok(_) => SolidityArrayDtProjectionRoute::Applicable { stats },
                        Err(reason) => {
                            SolidityArrayDtProjectionRoute::Unsupported { stats, reason }
                        }
                    }
                }
            }
            Err(reason) => SolidityArrayDtProjectionRoute::Unsupported {
                stats: projection_signature_stats(problem),
                reason,
            },
        }
    }

    pub(crate) fn project(problem: &ChcProblem) -> SolidityArrayDtProjectionOutcome {
        match build_projection_plans(problem) {
            Ok((_plans, 0)) => SolidityArrayDtProjectionOutcome::NotApplicable,
            Ok((plans, projected_args)) => match project_problem(problem, &plans) {
                Ok(projected_problem) => SolidityArrayDtProjectionOutcome::Projected {
                    problem: projected_problem,
                    projected_args,
                    stats: projection_stats(problem, &plans, projected_args),
                    plans,
                },
                Err(reason) => SolidityArrayDtProjectionOutcome::Unsupported(reason),
            },
            Err(reason) => SolidityArrayDtProjectionOutcome::Unsupported(reason),
        }
    }
}

fn translate_projection_interpretation(
    pid: PredicateId,
    interp: &PredicateInterpretation,
    original_sorts: &[ChcSort],
    plan: &PredicateProjectionPlan,
    observed_keys: &mut Vec<ObservedProjectedArrayKey>,
) -> Result<PredicateInterpretation, ()> {
    let mut original_vars = Vec::with_capacity(original_sorts.len());
    let mut direct_subst = Vec::new();
    let mut projected_fields = Vec::new();
    let mut transformed_idx = 0;

    for arg_plan in &plan.args {
        match arg_plan {
            PredArgPlan::Original { original_arg } => {
                let Some(original_sort) = original_sorts.get(*original_arg) else {
                    return Err(());
                };
                let Some(transformed_var) = interp.vars.get(transformed_idx) else {
                    return Err(());
                };
                let original_var = projection_original_var(pid, *original_arg, original_sort);
                original_vars.push(original_var.clone());
                direct_subst.push((transformed_var.clone(), ChcExpr::var(original_var)));
                transformed_idx += 1;
            }
            PredArgPlan::Projected { original_arg, info } => {
                let Some(original_sort) = original_sorts.get(*original_arg) else {
                    return Err(());
                };
                let original_var = projection_original_var(pid, *original_arg, original_sort);
                original_vars.push(original_var.clone());
                for obligation in plan
                    .field_obligations
                    .iter()
                    .filter(|obligation| obligation.original_arg == *original_arg)
                {
                    let Some(transformed_var) = interp.vars.get(transformed_idx) else {
                        return Err(());
                    };
                    if transformed_var.sort != obligation.projected_array_sort {
                        return Err(());
                    }
                    projected_fields.push((
                        transformed_var.clone(),
                        ProjectedFieldBinding {
                            original_var: original_var.clone(),
                            obligation: obligation.clone(),
                        },
                    ));
                    transformed_idx += 1;
                }
                if plan
                    .field_obligations
                    .iter()
                    .filter(|obligation| obligation.original_arg == *original_arg)
                    .count()
                    != info.dt.ctor.selectors.len()
                {
                    return Err(());
                }
            }
        }
    }

    if transformed_idx != interp.vars.len() {
        return Err(());
    }

    let formula = translate_projected_formula(
        &interp.formula,
        &direct_subst,
        &projected_fields,
        observed_keys,
    )?;
    Ok(PredicateInterpretation::new(original_vars, formula))
}

fn projection_original_var(pid: PredicateId, arg_idx: usize, sort: &ChcSort) -> ChcVar {
    ChcVar::new(format!("__sadp_p{}_a{arg_idx}", pid.index()), sort.clone())
}

fn translate_projected_formula(
    expr: &ChcExpr,
    direct_subst: &[(ChcVar, ChcExpr)],
    projected_fields: &[(ChcVar, ProjectedFieldBinding)],
    observed_keys: &mut Vec<ObservedProjectedArrayKey>,
) -> Result<ChcExpr, ()> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Var(v) => {
            if let Some((_, replacement)) = direct_subst.iter().find(|(from, _)| from == v) {
                Ok(replacement.clone())
            } else if projected_fields.iter().any(|(from, _)| from == v) {
                Err(())
            } else {
                Ok(expr.clone())
            }
        }
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
            Ok(expr.clone())
        }
        ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
            if let ChcExpr::Var(array_var) = args[0].as_ref() {
                if let Some((_, binding)) =
                    projected_fields.iter().find(|(from, _)| from == array_var)
                {
                    let index = translate_projected_formula(
                        args[1].as_ref(),
                        direct_subst,
                        projected_fields,
                        observed_keys,
                    )?;
                    if index.sort() != binding.obligation.key_sort {
                        return Err(());
                    }
                    observed_keys.push(ObservedProjectedArrayKey {
                        key: index.clone(),
                        obligation: binding.obligation.clone(),
                    });
                    let selected_dt =
                        ChcExpr::select(ChcExpr::var(binding.original_var.clone()), index);
                    return Ok(ChcExpr::FuncApp(
                        binding.obligation.selector.name.clone(),
                        binding.obligation.selector.sort.clone(),
                        vec![Arc::new(selected_dt)],
                    ));
                }
            }
            Ok(ChcExpr::Op(
                ChcOp::Select,
                translate_projected_args(args, direct_subst, projected_fields, observed_keys)?,
            ))
        }
        ChcExpr::Op(op, args) => Ok(ChcExpr::Op(
            *op,
            translate_projected_args(args, direct_subst, projected_fields, observed_keys)?,
        )),
        ChcExpr::PredicateApp(name, id, args) => Ok(ChcExpr::PredicateApp(
            name.clone(),
            *id,
            translate_projected_args(args, direct_subst, projected_fields, observed_keys)?,
        )),
        ChcExpr::FuncApp(name, sort, args) => Ok(ChcExpr::FuncApp(
            name.clone(),
            sort.clone(),
            translate_projected_args(args, direct_subst, projected_fields, observed_keys)?,
        )),
        ChcExpr::ConstArray(key_sort, value) => Ok(ChcExpr::ConstArray(
            key_sort.clone(),
            Arc::new(translate_projected_formula(
                value,
                direct_subst,
                projected_fields,
                observed_keys,
            )?),
        )),
        ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => Ok(expr.clone()),
    })
}

fn translate_projected_args(
    args: &[Arc<ChcExpr>],
    direct_subst: &[(ChcVar, ChcExpr)],
    projected_fields: &[(ChcVar, ProjectedFieldBinding)],
    observed_keys: &mut Vec<ObservedProjectedArrayKey>,
) -> Result<Vec<Arc<ChcExpr>>, ()> {
    args.iter()
        .map(|arg| {
            translate_projected_formula(arg.as_ref(), direct_subst, projected_fields, observed_keys)
                .map(Arc::new)
        })
        .collect()
}

fn build_projection_plans(
    problem: &ChcProblem,
) -> ProjectionResult<(Vec<PredicateProjectionPlan>, usize)> {
    let mut plans = Vec::with_capacity(problem.predicates().len());
    let mut projected_args = 0;

    for pred in problem.predicates() {
        let mut arg_plans = Vec::with_capacity(pred.arg_sorts.len());
        let mut field_obligations = Vec::new();
        for (arg_idx, sort) in pred.arg_sorts.iter().enumerate() {
            if let Some(info) = projectable_array_dt_sort(sort)? {
                projected_args += 1;
                field_obligations.extend(projected_array_field_obligations(arg_idx, &info));
                arg_plans.push(PredArgPlan::Projected {
                    original_arg: arg_idx,
                    info,
                });
            } else if contains_array_dt_sort(sort) {
                return Err(SolidityArrayDtProjectionRejection::NestedArrayDtArgument {
                    sort: sort.clone(),
                });
            } else {
                arg_plans.push(PredArgPlan::Original {
                    original_arg: arg_idx,
                });
            }
        }
        plans.push(PredicateProjectionPlan {
            args: arg_plans,
            field_obligations,
        });
    }

    Ok((plans, projected_args))
}

fn projected_array_field_obligations(
    original_arg: usize,
    info: &ArrayDtProjection,
) -> Vec<ProjectedArrayFieldObligation> {
    info.dt
        .ctor
        .selectors
        .iter()
        .enumerate()
        .map(|(field_idx, selector)| ProjectedArrayFieldObligation {
            original_arg,
            field_idx,
            key_sort: info.key_sort.clone(),
            original_array_sort: info.array_sort.clone(),
            projected_array_sort: array_sort(&info.key_sort, &selector.sort),
            selector: selector.clone(),
        })
        .collect()
}

fn projection_signature_stats(problem: &ChcProblem) -> SolidityArrayDtProjectionStats {
    SolidityArrayDtProjectionStats {
        predicates: problem.predicates().len(),
        predicate_args: problem
            .predicates()
            .iter()
            .map(|pred| pred.arg_sorts.len())
            .sum(),
        ..SolidityArrayDtProjectionStats::default()
    }
}

fn projection_stats(
    problem: &ChcProblem,
    plans: &[PredicateProjectionPlan],
    projected_args: usize,
) -> SolidityArrayDtProjectionStats {
    let mut stats = projection_signature_stats(problem);
    stats.projected_args = projected_args;

    for plan in plans {
        let mut plan_projected_args = 0;
        for arg in &plan.args {
            if let PredArgPlan::Projected { info, .. } = arg {
                plan_projected_args += 1;
                stats.projected_field_args += info.dt.ctor.selectors.len();
            }
        }
        if plan_projected_args > 0 {
            stats.projected_predicates += 1;
        }
    }

    stats.added_predicate_args = stats
        .projected_field_args
        .saturating_sub(stats.projected_args);
    stats
}

fn project_problem(
    problem: &ChcProblem,
    plans: &[PredicateProjectionPlan],
) -> ProjectionResult<ChcProblem> {
    let mut projected = ChcProblem::new();
    if problem.is_fixedpoint_format() {
        projected.set_fixedpoint_format();
    }
    for name in problem.action_names() {
        projected.declare_action(name.clone());
    }
    for (name, constructors) in problem.datatype_defs() {
        projected.add_datatype_def(name.clone(), constructors.clone());
    }

    for (pred, plan) in problem.predicates().iter().zip(plans.iter()) {
        let mut new_sorts = Vec::new();
        for arg in &plan.args {
            match arg {
                PredArgPlan::Original { original_arg } => {
                    new_sorts.push(pred.arg_sorts[*original_arg].clone());
                }
                PredArgPlan::Projected { info, .. } => {
                    for selector in &info.dt.ctor.selectors {
                        new_sorts.push(array_sort(&info.key_sort, &selector.sort));
                    }
                }
            }
        }
        projected.declare_predicate(pred.name.clone(), new_sorts);
    }

    for clause in problem.clauses() {
        let body_preds = clause
            .body
            .predicates
            .iter()
            .map(|(pred_id, args)| {
                let plan = plans.get(pred_id.index()).ok_or(
                    SolidityArrayDtProjectionRejection::PredicateArgumentCountMismatch {
                        predicate: *pred_id,
                        expected: 0,
                        actual: args.len(),
                    },
                )?;
                Ok((*pred_id, project_predicate_args(*pred_id, plan, args)?))
            })
            .collect::<ProjectionResult<Vec<_>>>()?;

        let constraint = clause
            .body
            .constraint
            .as_ref()
            .map(rewrite_expr)
            .transpose()?;

        let head = match &clause.head {
            ClauseHead::Predicate(pred_id, args) => {
                let plan = plans.get(pred_id.index()).ok_or(
                    SolidityArrayDtProjectionRejection::PredicateArgumentCountMismatch {
                        predicate: *pred_id,
                        expected: 0,
                        actual: args.len(),
                    },
                )?;
                ClauseHead::Predicate(*pred_id, project_predicate_args(*pred_id, plan, args)?)
            }
            ClauseHead::False => ClauseHead::False,
        };

        let mut new_clause = HornClause::new(ClauseBody::new(body_preds, constraint), head);
        new_clause.action_id = clause.action_id;
        projected.add_clause(new_clause);
    }

    Ok(projected)
}

fn collect_source_projected_array_keys(problem: &ChcProblem) -> Vec<ObservedProjectedArrayKey> {
    let mut keys = Vec::new();
    for clause in problem.clauses() {
        if let Some(constraint) = &clause.body.constraint {
            collect_source_projected_array_keys_from_expr(constraint, &mut keys);
        }
        for (_, args) in &clause.body.predicates {
            for arg in args {
                collect_source_projected_array_keys_from_expr(arg, &mut keys);
            }
        }
        if let ClauseHead::Predicate(_, args) = &clause.head {
            for arg in args {
                collect_source_projected_array_keys_from_expr(arg, &mut keys);
            }
        }
    }
    keys
}

fn collect_source_projected_array_keys_from_expr(
    expr: &ChcExpr,
    keys: &mut Vec<ObservedProjectedArrayKey>,
) {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
            remember_source_array_key(args[0].as_ref(), args[1].as_ref(), keys);
            collect_source_projected_array_keys_from_expr(args[0].as_ref(), keys);
            collect_source_projected_array_keys_from_expr(args[1].as_ref(), keys);
        }
        ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
            remember_source_array_key(args[0].as_ref(), args[1].as_ref(), keys);
            for arg in args {
                collect_source_projected_array_keys_from_expr(arg.as_ref(), keys);
            }
        }
        ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) | ChcExpr::FuncApp(_, _, args) => {
            for arg in args {
                collect_source_projected_array_keys_from_expr(arg.as_ref(), keys);
            }
        }
        ChcExpr::ConstArray(_, value) => {
            collect_source_projected_array_keys_from_expr(value.as_ref(), keys);
        }
        ChcExpr::Var(_)
        | ChcExpr::Bool(_)
        | ChcExpr::Int(_)
        | ChcExpr::Real(_, _)
        | ChcExpr::BitVec(_, _)
        | ChcExpr::ConstArrayMarker(_)
        | ChcExpr::IsTesterMarker(_) => {}
    });
}

fn remember_source_array_key(
    array: &ChcExpr,
    index: &ChcExpr,
    keys: &mut Vec<ObservedProjectedArrayKey>,
) {
    let Ok(Some(info)) = projectable_array_dt_sort(&array.sort()) else {
        return;
    };
    if index.sort() != info.key_sort {
        return;
    }
    let Some(obligation) = projected_array_field_obligations(0, &info)
        .into_iter()
        .next()
    else {
        return;
    };
    keys.push(ObservedProjectedArrayKey {
        key: index.clone(),
        obligation,
    });
}

fn project_predicate_args(
    pred_id: PredicateId,
    plan: &PredicateProjectionPlan,
    args: &[ChcExpr],
) -> ProjectionResult<Vec<ChcExpr>> {
    if plan.args.len() != args.len() {
        return Err(
            SolidityArrayDtProjectionRejection::PredicateArgumentCountMismatch {
                predicate: pred_id,
                expected: plan.args.len(),
                actual: args.len(),
            },
        );
    }

    let mut out = Vec::new();
    for arg_plan in &plan.args {
        match arg_plan {
            PredArgPlan::Original { original_arg } => {
                out.push(rewrite_expr(&args[*original_arg])?);
            }
            PredArgPlan::Projected { original_arg, info } => {
                for field_idx in 0..info.dt.ctor.selectors.len() {
                    out.push(project_array_expr(
                        &args[*original_arg],
                        info,
                        field_idx,
                        "predicate argument",
                    )?);
                }
            }
        }
    }
    Ok(out)
}

fn rewrite_expr(expr: &ChcExpr) -> ProjectionResult<ChcExpr> {
    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Bool(_) | ChcExpr::Int(_) | ChcExpr::Real(_, _) | ChcExpr::BitVec(_, _) => {
            Ok(expr.clone())
        }
        ChcExpr::Var(v) => {
            if projectable_array_dt_sort(&v.sort)?.is_some() {
                Err(
                    SolidityArrayDtProjectionRejection::UnsupportedArrayExpression {
                        context: "raw array variable",
                        sort: v.sort.clone(),
                    },
                )
            } else {
                Ok(expr.clone())
            }
        }
        ChcExpr::PredicateApp(name, id, args) => {
            let new_args = args
                .iter()
                .map(|a| rewrite_expr(a).map(Arc::new))
                .collect::<ProjectionResult<Vec<_>>>()?;
            Ok(ChcExpr::PredicateApp(name.clone(), *id, new_args))
        }
        ChcExpr::FuncApp(name, ret_sort, args) if args.len() == 1 => {
            let arg_sort = args[0].sort();
            if let Some((dt, field_idx)) = selector_field_for_sort(&arg_sort, name, ret_sort) {
                return project_dt_value(args[0].as_ref(), &dt, field_idx, "selector");
            }

            let new_args = args
                .iter()
                .map(|a| rewrite_expr(a).map(Arc::new))
                .collect::<ProjectionResult<Vec<_>>>()?;
            Ok(ChcExpr::FuncApp(name.clone(), ret_sort.clone(), new_args))
        }
        ChcExpr::FuncApp(name, ret_sort, args) => {
            let new_args = args
                .iter()
                .map(|a| rewrite_expr(a).map(Arc::new))
                .collect::<ProjectionResult<Vec<_>>>()?;
            Ok(ChcExpr::FuncApp(name.clone(), ret_sort.clone(), new_args))
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            rewrite_comparison(ChcOp::Eq, args[0].as_ref(), args[1].as_ref())
        }
        ChcExpr::Op(ChcOp::Ne, args) if args.len() == 2 => {
            rewrite_comparison(ChcOp::Ne, args[0].as_ref(), args[1].as_ref())
        }
        ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
            let arr_sort = args[0].sort();
            if projectable_array_dt_sort(&arr_sort)?.is_some() {
                Err(
                    SolidityArrayDtProjectionRejection::UnsupportedDatatypeExpression {
                        context: "raw select from projected array",
                        sort: expr.sort(),
                    },
                )
            } else {
                let new_args = args
                    .iter()
                    .map(|a| rewrite_expr(a).map(Arc::new))
                    .collect::<ProjectionResult<Vec<_>>>()?;
                Ok(ChcExpr::Op(ChcOp::Select, new_args))
            }
        }
        ChcExpr::Op(op, args) => {
            if projectable_array_dt_sort(&expr.sort())?.is_some() {
                return Err(
                    SolidityArrayDtProjectionRejection::UnsupportedArrayExpression {
                        context: "raw array expression",
                        sort: expr.sort(),
                    },
                );
            }
            let new_args = args
                .iter()
                .map(|a| rewrite_expr(a).map(Arc::new))
                .collect::<ProjectionResult<Vec<_>>>()?;
            Ok(ChcExpr::Op(*op, new_args))
        }
        ChcExpr::ConstArray(key_sort, val) => {
            if projectable_array_dt_sort(&expr.sort())?.is_some() {
                Err(
                    SolidityArrayDtProjectionRejection::UnsupportedArrayExpression {
                        context: "raw const array",
                        sort: expr.sort(),
                    },
                )
            } else {
                Ok(ChcExpr::ConstArray(
                    key_sort.clone(),
                    Arc::new(rewrite_expr(val)?),
                ))
            }
        }
        ChcExpr::ConstArrayMarker(_) | ChcExpr::IsTesterMarker(_) => Ok(expr.clone()),
    })
}

fn rewrite_comparison(op: ChcOp, lhs: &ChcExpr, rhs: &ChcExpr) -> ProjectionResult<ChcExpr> {
    let lhs_sort = lhs.sort();
    if let Some(info) = projectable_array_dt_sort(&lhs_sort)? {
        if rhs.sort() != lhs_sort {
            return Err(
                SolidityArrayDtProjectionRejection::UnsupportedArrayExpression {
                    context: "array comparison sort mismatch",
                    sort: rhs.sort(),
                },
            );
        }
        let comparisons = (0..info.dt.ctor.selectors.len())
            .map(|field_idx| {
                let lhs_field = project_array_expr(lhs, &info, field_idx, "array comparison")?;
                let rhs_field = project_array_expr(rhs, &info, field_idx, "array comparison")?;
                Ok(ChcExpr::Op(
                    op,
                    vec![Arc::new(lhs_field), Arc::new(rhs_field)],
                ))
            })
            .collect::<ProjectionResult<Vec<_>>>()?;
        return Ok(if op == ChcOp::Eq {
            ChcExpr::and_all(comparisons)
        } else {
            ChcExpr::or_all(comparisons)
        });
    }

    if let Some(dt) = single_ctor_dt_sort(&lhs_sort) {
        if rhs.sort() != lhs_sort {
            return Err(
                SolidityArrayDtProjectionRejection::UnsupportedDatatypeExpression {
                    context: "datatype comparison sort mismatch",
                    sort: rhs.sort(),
                },
            );
        }
        let comparisons = (0..dt.ctor.selectors.len())
            .map(|field_idx| {
                let lhs_field = project_dt_value(lhs, &dt, field_idx, "datatype comparison")?;
                let rhs_field = project_dt_value(rhs, &dt, field_idx, "datatype comparison")?;
                Ok(ChcExpr::Op(
                    op,
                    vec![Arc::new(lhs_field), Arc::new(rhs_field)],
                ))
            })
            .collect::<ProjectionResult<Vec<_>>>()?;
        return Ok(if op == ChcOp::Eq {
            ChcExpr::and_all(comparisons)
        } else {
            ChcExpr::or_all(comparisons)
        });
    }

    Ok(ChcExpr::Op(
        op,
        vec![Arc::new(rewrite_expr(lhs)?), Arc::new(rewrite_expr(rhs)?)],
    ))
}

fn project_array_expr(
    expr: &ChcExpr,
    info: &ArrayDtProjection,
    field_idx: usize,
    context: &'static str,
) -> ProjectionResult<ChcExpr> {
    if expr.sort() != info.array_sort {
        return Err(
            SolidityArrayDtProjectionRejection::UnsupportedArrayExpression {
                context,
                sort: expr.sort(),
            },
        );
    }

    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::Var(v) => Ok(ChcExpr::Var(projected_array_var(v, info, field_idx))),
        ChcExpr::Op(ChcOp::Store, args) if args.len() == 3 => {
            let base = project_array_expr(&args[0], info, field_idx, context)?;
            let index = rewrite_expr(&args[1])?;
            let value = project_dt_value(&args[2], &info.dt, field_idx, context)?;
            Ok(ChcExpr::store(base, index, value))
        }
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            let cond = rewrite_expr(&args[0])?;
            let then_array = project_array_expr(&args[1], info, field_idx, context)?;
            let else_array = project_array_expr(&args[2], info, field_idx, context)?;
            Ok(ChcExpr::ite(cond, then_array, else_array))
        }
        ChcExpr::ConstArray(key_sort, value) => {
            let field_value = project_dt_value(value, &info.dt, field_idx, context)?;
            Ok(ChcExpr::ConstArray(key_sort.clone(), Arc::new(field_value)))
        }
        _ => Err(
            SolidityArrayDtProjectionRejection::UnsupportedArrayExpression {
                context,
                sort: expr.sort(),
            },
        ),
    })
}

fn project_dt_value(
    expr: &ChcExpr,
    dt: &SingleCtorDt,
    field_idx: usize,
    context: &'static str,
) -> ProjectionResult<ChcExpr> {
    if expr.sort() != dt.sort {
        return Err(
            SolidityArrayDtProjectionRejection::UnsupportedDatatypeExpression {
                context,
                sort: expr.sort(),
            },
        );
    }

    let selector = dt.ctor.selectors.get(field_idx).ok_or(
        SolidityArrayDtProjectionRejection::UnsupportedDatatypeExpression {
            context,
            sort: dt.sort.clone(),
        },
    )?;

    crate::expr::maybe_grow_expr_stack(|| match expr {
        ChcExpr::FuncApp(name, _, args) if *name == dt.ctor.name => {
            let field_arg = args.get(field_idx).ok_or(
                SolidityArrayDtProjectionRejection::UnsupportedDatatypeExpression {
                    context,
                    sort: expr.sort(),
                },
            )?;
            rewrite_expr(field_arg)
        }
        ChcExpr::Op(ChcOp::Ite, args) if args.len() == 3 => {
            let cond = rewrite_expr(&args[0])?;
            let then_value = project_dt_value(&args[1], dt, field_idx, context)?;
            let else_value = project_dt_value(&args[2], dt, field_idx, context)?;
            Ok(ChcExpr::ite(cond, then_value, else_value))
        }
        ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
            let arr_sort = args[0].sort();
            let Some(info) = projectable_array_dt_sort(&arr_sort)? else {
                return Ok(ChcExpr::FuncApp(
                    selector.name.clone(),
                    selector.sort.clone(),
                    vec![Arc::new(rewrite_expr(expr)?)],
                ));
            };
            if info.dt.sort != dt.sort {
                return Err(
                    SolidityArrayDtProjectionRejection::UnsupportedDatatypeExpression {
                        context,
                        sort: expr.sort(),
                    },
                );
            }
            let array_field = project_array_expr(&args[0], &info, field_idx, context)?;
            let index = rewrite_expr(&args[1])?;
            Ok(ChcExpr::select(array_field, index))
        }
        _ => Ok(ChcExpr::FuncApp(
            selector.name.clone(),
            selector.sort.clone(),
            vec![Arc::new(rewrite_expr(expr)?)],
        )),
    })
}

fn projectable_array_dt_sort(sort: &ChcSort) -> ProjectionResult<Option<ArrayDtProjection>> {
    let ChcSort::Array(key, value) = sort else {
        return Ok(None);
    };

    let ChcSort::Datatype { name, constructors } = value.as_ref() else {
        return Ok(None);
    };
    if datatype_name_in_sort(key).is_some() {
        return Err(
            SolidityArrayDtProjectionRejection::DatatypeNestedInArrayKey {
                datatype: datatype_name_in_sort(key).unwrap_or_default(),
            },
        );
    }
    if constructors.len() != 1 {
        return Err(
            SolidityArrayDtProjectionRejection::NonSingleConstructorArrayElement {
                datatype: name.clone(),
                constructors: constructors.len(),
            },
        );
    }
    let ctor = constructors[0].clone();
    if ctor.selectors.is_empty() {
        return Err(
            SolidityArrayDtProjectionRejection::EmptyConstructorArrayElement {
                datatype: name.clone(),
            },
        );
    }
    for selector in &ctor.selectors {
        if let Some(datatype) = datatype_name_in_sort(&selector.sort) {
            return Err(
                SolidityArrayDtProjectionRejection::DatatypeNestedInArrayElementField {
                    datatype,
                    field: selector.name.clone(),
                },
            );
        }
    }

    Ok(Some(ArrayDtProjection {
        array_sort: sort.clone(),
        key_sort: key.as_ref().clone(),
        dt: SingleCtorDt {
            sort: value.as_ref().clone(),
            ctor,
        },
    }))
}

fn single_ctor_dt_sort(sort: &ChcSort) -> Option<SingleCtorDt> {
    let ChcSort::Datatype { constructors, .. } = sort else {
        return None;
    };
    if constructors.len() != 1 || constructors[0].selectors.is_empty() {
        return None;
    }
    if constructors[0]
        .selectors
        .iter()
        .any(|selector| datatype_name_in_sort(&selector.sort).is_some())
    {
        return None;
    }
    Some(SingleCtorDt {
        sort: sort.clone(),
        ctor: constructors[0].clone(),
    })
}

fn selector_field_for_sort(
    sort: &ChcSort,
    selector_name: &str,
    ret_sort: &ChcSort,
) -> Option<(SingleCtorDt, usize)> {
    let dt = single_ctor_dt_sort(sort)?;
    let field_idx = dt
        .ctor
        .selectors
        .iter()
        .position(|selector| selector.name == selector_name && selector.sort == *ret_sort)?;
    Some((dt, field_idx))
}

fn contains_array_dt_sort(sort: &ChcSort) -> bool {
    fn go<'a>(sort: &'a ChcSort, seen_datatypes: &mut FxHashSet<&'a str>) -> bool {
        match sort {
            ChcSort::Array(_, value) if matches!(value.as_ref(), ChcSort::Datatype { .. }) => true,
            ChcSort::Array(key, value) => go(key, seen_datatypes) || go(value, seen_datatypes),
            ChcSort::Datatype { name, constructors } => {
                if !seen_datatypes.insert(name.as_str()) {
                    return false;
                }
                constructors
                    .iter()
                    .flat_map(|ctor| ctor.selectors.iter())
                    .any(|selector| go(&selector.sort, seen_datatypes))
            }
            ChcSort::Bool
            | ChcSort::Int
            | ChcSort::Real
            | ChcSort::BitVec(_)
            | ChcSort::Uninterpreted(_) => false,
        }
    }

    go(sort, &mut FxHashSet::default())
}

fn datatype_name_in_sort(sort: &ChcSort) -> Option<String> {
    fn go<'a>(sort: &'a ChcSort, seen_datatypes: &mut FxHashSet<&'a str>) -> Option<String> {
        match sort {
            ChcSort::Datatype { name, constructors } => {
                if !seen_datatypes.insert(name.as_str()) {
                    return Some(name.clone());
                }
                for selector in constructors.iter().flat_map(|ctor| ctor.selectors.iter()) {
                    if let Some(nested) = go(&selector.sort, seen_datatypes) {
                        return Some(nested);
                    }
                }
                Some(name.clone())
            }
            ChcSort::Array(key, value) => {
                go(key, seen_datatypes).or_else(|| go(value, seen_datatypes))
            }
            ChcSort::Bool
            | ChcSort::Int
            | ChcSort::Real
            | ChcSort::BitVec(_)
            | ChcSort::Uninterpreted(_) => None,
        }
    }

    go(sort, &mut FxHashSet::default())
}

fn array_sort(key: &ChcSort, value: &ChcSort) -> ChcSort {
    ChcSort::Array(Box::new(key.clone()), Box::new(value.clone()))
}

fn projected_array_var(array_var: &ChcVar, info: &ArrayDtProjection, field_idx: usize) -> ChcVar {
    let selector = &info.dt.ctor.selectors[field_idx];
    ChcVar::new(
        projected_array_name(&array_var.name, selector),
        array_sort(&info.key_sort, &selector.sort),
    )
}

fn projected_array_name(array_name: &str, selector: &ChcDtSelector) -> String {
    if let Some(base) = array_name.strip_suffix('\'') {
        format!("{base}__{}'", selector.name)
    } else {
        format!("{array_name}__{}", selector.name)
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests {
    use super::*;
    use crate::{ChcDtConstructor, ChcDtSelector};

    fn arc(expr: ChcExpr) -> Arc<ChcExpr> {
        Arc::new(expr)
    }

    fn pair_sort() -> ChcSort {
        ChcSort::Datatype {
            name: "Pair".to_string(),
            constructors: Arc::new(vec![ChcDtConstructor {
                name: "mkPair".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "balance".to_string(),
                        sort: ChcSort::BitVec(256),
                    },
                    ChcDtSelector {
                        name: "live".to_string(),
                        sort: ChcSort::Bool,
                    },
                ],
            }]),
        }
    }

    fn option_sort() -> ChcSort {
        ChcSort::Datatype {
            name: "OptionPair".to_string(),
            constructors: Arc::new(vec![
                ChcDtConstructor {
                    name: "None".to_string(),
                    selectors: vec![],
                },
                ChcDtConstructor {
                    name: "Some".to_string(),
                    selectors: vec![ChcDtSelector {
                        name: "value".to_string(),
                        sort: ChcSort::Int,
                    }],
                },
            ]),
        }
    }

    fn array_pair_sort() -> ChcSort {
        ChcSort::Array(Box::new(ChcSort::BitVec(160)), Box::new(pair_sort()))
    }

    fn erc777_key_sort() -> ChcSort {
        ChcSort::Datatype {
            name: "ecrecover_input_type".to_string(),
            constructors: Arc::new(vec![ChcDtConstructor {
                name: "ecrecover_input_type".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "hash".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "v".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "r".to_string(),
                        sort: ChcSort::Int,
                    },
                    ChcDtSelector {
                        name: "s".to_string(),
                        sort: ChcSort::Int,
                    },
                ],
            }]),
        }
    }

    fn erc777_mapping_value_sort() -> ChcSort {
        ChcSort::Datatype {
            name: "mapping$addressuint256$_tuple".to_string(),
            constructors: Arc::new(vec![ChcDtConstructor {
                name: "mapping$addressuint256$_tuple".to_string(),
                selectors: vec![
                    ChcDtSelector {
                        name: "mapping$addressuint256$_tuple_accessor_array".to_string(),
                        sort: ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int)),
                    },
                    ChcDtSelector {
                        name: "mapping$addressuint256$_tuple_accessor_length".to_string(),
                        sort: ChcSort::Int,
                    },
                ],
            }]),
        }
    }

    fn pair_value(balance: ChcExpr, live: ChcExpr) -> ChcExpr {
        ChcExpr::FuncApp(
            "mkPair".to_string(),
            pair_sort(),
            vec![arc(balance), arc(live)],
        )
    }

    #[test]
    fn not_applicable_for_scalar_arrays() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate(
            "Inv",
            vec![ChcSort::Array(
                Box::new(ChcSort::BitVec(160)),
                Box::new(ChcSort::BitVec(256)),
            )],
        );

        assert!(matches!(
            SolidityArrayDtProjector::project(&problem),
            SolidityArrayDtProjectionOutcome::NotApplicable
        ));
    }

    #[test]
    fn route_reports_not_applicable_with_signature_stats() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate(
            "Inv",
            vec![ChcSort::Array(
                Box::new(ChcSort::BitVec(160)),
                Box::new(ChcSort::BitVec(256)),
            )],
        );

        let route = SolidityArrayDtProjector::route(&problem);

        assert!(!route.is_applicable());
        assert_eq!(
            *route.stats(),
            SolidityArrayDtProjectionStats {
                predicates: 1,
                predicate_args: 1,
                projected_predicates: 0,
                projected_args: 0,
                projected_field_args: 0,
                added_predicate_args: 0,
            }
        );
        assert!(matches!(
            route,
            SolidityArrayDtProjectionRoute::NotApplicable { .. }
        ));
    }

    #[test]
    fn route_reports_applicable_with_projection_stats() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate(
            "Inv",
            vec![array_pair_sort(), ChcSort::BitVec(160), array_pair_sort()],
        );

        let route = SolidityArrayDtProjector::route(&problem);

        assert!(route.is_applicable());
        assert_eq!(
            *route.stats(),
            SolidityArrayDtProjectionStats {
                predicates: 1,
                predicate_args: 3,
                projected_predicates: 1,
                projected_args: 2,
                projected_field_args: 4,
                added_predicate_args: 2,
            }
        );
        assert!(matches!(
            route,
            SolidityArrayDtProjectionRoute::Applicable { .. }
        ));
    }

    #[test]
    fn projection_plan_remembers_field_key_obligations() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate("Inv", vec![array_pair_sort()]);

        let (plans, projected_args) = build_projection_plans(&problem).unwrap();

        assert_eq!(projected_args, 1);
        let obligations = &plans[0].field_obligations;
        assert_eq!(obligations.len(), 2);
        assert_eq!(obligations[0].original_arg, 0);
        assert_eq!(obligations[0].field_idx, 0);
        assert_eq!(obligations[0].key_sort, ChcSort::BitVec(160));
        assert_eq!(obligations[0].selector.name, "balance");
        assert_eq!(
            obligations[0].projected_array_sort,
            ChcSort::Array(
                Box::new(ChcSort::BitVec(160)),
                Box::new(ChcSort::BitVec(256))
            )
        );
        assert_eq!(obligations[1].selector.name, "live");
    }

    #[test]
    fn route_reports_unsupported_with_projection_stats() {
        let arr_sort = array_pair_sort();
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Inv", vec![arr_sort.clone()]);

        let balances = ChcVar::new("balances", arr_sort.clone());
        let owner = ChcVar::new("owner", ChcSort::BitVec(160));
        let raw_select = ChcExpr::select(ChcExpr::var(balances.clone()), ChcExpr::var(owner));
        let opaque = ChcExpr::FuncApp("opaque".to_string(), ChcSort::Bool, vec![arc(raw_select)]);

        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(pred, vec![ChcExpr::var(balances.clone())])],
                Some(opaque),
            ),
            ClauseHead::Predicate(pred, vec![ChcExpr::var(balances)]),
        ));

        let route = SolidityArrayDtProjector::route(&problem);

        assert!(!route.is_applicable());
        assert_eq!(
            *route.stats(),
            SolidityArrayDtProjectionStats {
                predicates: 1,
                predicate_args: 1,
                projected_predicates: 1,
                projected_args: 1,
                projected_field_args: 2,
                added_predicate_args: 1,
            }
        );
        assert!(matches!(
            route,
            SolidityArrayDtProjectionRoute::Unsupported {
                reason:
                    SolidityArrayDtProjectionRejection::UnsupportedDatatypeExpression {
                        context: "raw select from projected array",
                        sort
                    },
                ..
            } if sort == pair_sort()
        ));
    }

    #[test]
    fn rejects_multi_constructor_array_elements() {
        let mut problem = ChcProblem::new();
        problem.declare_predicate(
            "Inv",
            vec![ChcSort::Array(
                Box::new(ChcSort::Int),
                Box::new(option_sort()),
            )],
        );

        assert!(matches!(
            SolidityArrayDtProjector::project(&problem),
            SolidityArrayDtProjectionOutcome::Unsupported(
                SolidityArrayDtProjectionRejection::NonSingleConstructorArrayElement {
                    datatype,
                    constructors: 2
                }
            ) if datatype == "OptionPair"
        ));
    }

    // Regression for erc777_safe_000: after DT flattening, crypto_type exposes
    // ecrecover as `Array ecrecover_input_type Int`. That scalar-valued map
    // previously rejected the projection route with DatatypeNestedInArrayKey
    // before the route could split the Solidity mapping tuple arrays.
    #[test]
    fn route_ignores_datatype_key_scalar_arrays_before_projecting_value_datatypes() {
        let datatype_key_scalar_map =
            ChcSort::Array(Box::new(erc777_key_sort()), Box::new(ChcSort::Int));
        let projectable_nested_map = ChcSort::Array(
            Box::new(ChcSort::Int),
            Box::new(erc777_mapping_value_sort()),
        );
        let mut problem = ChcProblem::new();
        problem.declare_predicate("Inv", vec![datatype_key_scalar_map, projectable_nested_map]);

        let route = SolidityArrayDtProjector::route(&problem);

        assert!(
            route.is_applicable(),
            "erc777-style non-projected Array DTKey Int must not block projecting Array Int SingleCtorDT; route={route:?}"
        );
        assert_eq!(
            *route.stats(),
            SolidityArrayDtProjectionStats {
                predicates: 1,
                predicate_args: 2,
                projected_predicates: 1,
                projected_args: 1,
                projected_field_args: 2,
                added_predicate_args: 1,
            }
        );
    }

    #[test]
    fn rejects_projected_array_values_with_datatype_keys() {
        let unsupported = ChcSort::Array(Box::new(erc777_key_sort()), Box::new(pair_sort()));
        let mut problem = ChcProblem::new();
        problem.declare_predicate("Inv", vec![unsupported]);

        assert!(matches!(
            SolidityArrayDtProjector::route(&problem),
            SolidityArrayDtProjectionRoute::Unsupported {
                reason:
                    SolidityArrayDtProjectionRejection::DatatypeNestedInArrayKey {
                        datatype
                    },
                ..
            } if datatype == "ecrecover_input_type"
        ));
    }

    #[test]
    fn projects_predicate_signature_and_store_update() {
        let arr_sort = array_pair_sort();
        let owner_sort = ChcSort::BitVec(160);
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Inv", vec![arr_sort.clone(), owner_sort.clone()]);

        let balances = ChcVar::new("balances", arr_sort.clone());
        let owner = ChcVar::new("owner", owner_sort.clone());
        let updated = ChcExpr::store(
            ChcExpr::var(balances.clone()),
            ChcExpr::var(owner.clone()),
            pair_value(ChcExpr::BitVec(7, 256), ChcExpr::Bool(true)),
        );

        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(
                    pred,
                    vec![ChcExpr::var(balances.clone()), ChcExpr::var(owner.clone())],
                )],
                None,
            ),
            ClauseHead::Predicate(pred, vec![updated, ChcExpr::var(owner)]),
        ));

        let SolidityArrayDtProjectionOutcome::Projected {
            problem: projected,
            projected_args,
            ..
        } = SolidityArrayDtProjector::project(&problem)
        else {
            panic!("projection should apply");
        };

        assert_eq!(projected_args, 1);
        assert_eq!(projected.predicates()[0].arity(), 3);
        assert_eq!(
            projected.predicates()[0].arg_sorts,
            vec![
                ChcSort::Array(
                    Box::new(ChcSort::BitVec(160)),
                    Box::new(ChcSort::BitVec(256))
                ),
                ChcSort::Array(Box::new(ChcSort::BitVec(160)), Box::new(ChcSort::Bool)),
                owner_sort,
            ]
        );

        let body_args = &projected.clauses()[0].body.predicates[0].1;
        assert_eq!(
            body_args,
            &vec![
                ChcExpr::var(ChcVar::new(
                    "balances__balance",
                    ChcSort::Array(
                        Box::new(ChcSort::BitVec(160)),
                        Box::new(ChcSort::BitVec(256))
                    )
                )),
                ChcExpr::var(ChcVar::new(
                    "balances__live",
                    ChcSort::Array(Box::new(ChcSort::BitVec(160)), Box::new(ChcSort::Bool))
                )),
                ChcExpr::var(ChcVar::new("owner", ChcSort::BitVec(160))),
            ]
        );

        let ClauseHead::Predicate(_, head_args) = &projected.clauses()[0].head else {
            panic!("expected predicate head");
        };
        assert_eq!(head_args.len(), 3);
        assert!(matches!(
            &head_args[0],
            ChcExpr::Op(ChcOp::Store, args)
                if args.len() == 3
                && matches!(args[0].as_ref(), ChcExpr::Var(v) if v.name == "balances__balance")
                && matches!(args[2].as_ref(), ChcExpr::BitVec(7, 256))
        ));
        assert!(matches!(
            &head_args[1],
            ChcExpr::Op(ChcOp::Store, args)
                if args.len() == 3
                && matches!(args[0].as_ref(), ChcExpr::Var(v) if v.name == "balances__live")
                && matches!(args[2].as_ref(), ChcExpr::Bool(true))
        ));
    }

    #[test]
    fn rewrites_selector_on_array_select() {
        let arr_sort = array_pair_sort();
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Inv", vec![arr_sort.clone()]);

        let balances = ChcVar::new("balances", arr_sort);
        let owner = ChcVar::new("owner", ChcSort::BitVec(160));
        let selected = ChcExpr::select(ChcExpr::var(balances.clone()), ChcExpr::var(owner.clone()));
        let balance = ChcExpr::FuncApp(
            "balance".to_string(),
            ChcSort::BitVec(256),
            vec![arc(selected)],
        );
        let constraint = ChcExpr::eq(balance, ChcExpr::BitVec(9, 256));

        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(pred, vec![ChcExpr::var(balances.clone())])],
                Some(constraint),
            ),
            ClauseHead::Predicate(pred, vec![ChcExpr::var(balances)]),
        ));

        let SolidityArrayDtProjectionOutcome::Projected {
            problem: projected, ..
        } = SolidityArrayDtProjector::project(&problem)
        else {
            panic!("projection should apply");
        };

        let constraint = projected.clauses()[0]
            .body
            .constraint
            .as_ref()
            .expect("constraint should be preserved");
        assert!(matches!(
            constraint,
            ChcExpr::Op(ChcOp::Eq, eq_args)
                if matches!(
                    eq_args[0].as_ref(),
                    ChcExpr::Op(ChcOp::Select, select_args)
                        if matches!(select_args[0].as_ref(), ChcExpr::Var(v) if v.name == "balances__balance")
                        && matches!(select_args[1].as_ref(), ChcExpr::Var(v) if v.name == "owner")
                )
                && matches!(eq_args[1].as_ref(), ChcExpr::BitVec(9, 256))
        ));
    }

    #[test]
    fn transformer_backtranslates_field_select_invariant() {
        let arr_sort = array_pair_sort();
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Inv", vec![arr_sort.clone()]);

        let result = Box::new(SolidityArrayDtProjectionTransformer::new()).transform(problem);
        assert_eq!(result.problem.predicates()[0].arity(), 2);

        let balance_array = ChcVar::new(
            "balance_array",
            result.problem.predicates()[0].arg_sorts[0].clone(),
        );
        let live_array = ChcVar::new(
            "live_array",
            result.problem.predicates()[0].arg_sorts[1].clone(),
        );
        let formula = ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(balance_array.clone()), ChcExpr::BitVec(4, 160)),
            ChcExpr::BitVec(9, 256),
        );
        let mut model = InvariantModel::new();
        model.set(
            pred,
            PredicateInterpretation::new(vec![balance_array, live_array], formula),
        );

        let translated = result.back_translator.translate_validity(model);
        let interp = translated.get(&pred).expect("predicate should translate");
        assert_eq!(interp.vars.len(), 1);
        assert_eq!(interp.vars[0].sort, arr_sort);
        assert!(matches!(
            &interp.formula,
            ChcExpr::Op(ChcOp::Eq, eq_args)
                if matches!(
                    eq_args[0].as_ref(),
                    ChcExpr::FuncApp(name, ChcSort::BitVec(256), selector_args)
                        if name == "balance"
                        && matches!(
                            selector_args[0].as_ref(),
                            ChcExpr::Op(ChcOp::Select, select_args)
                                if matches!(select_args[0].as_ref(), ChcExpr::Var(v) if v == &interp.vars[0])
                                && matches!(select_args[1].as_ref(), ChcExpr::BitVec(4, 160))
                        )
                )
                && matches!(eq_args[1].as_ref(), ChcExpr::BitVec(9, 256))
        ));
    }

    #[test]
    fn transformer_memory_records_observed_backtranslation_keys() {
        let arr_sort = array_pair_sort();
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Inv", vec![arr_sort]);

        let result = Box::new(SolidityArrayDtProjectionTransformer::new()).transform(problem);
        assert_eq!(
            result
                .back_translator
                .transform_memory()
                .fact_value("observed_projected_array_keys"),
            Some("0")
        );
        assert_eq!(
            result
                .back_translator
                .transform_memory()
                .fact_value("projection_predicate_maps"),
            Some("1")
        );
        assert_eq!(
            result
                .back_translator
                .transform_memory()
                .fact_value("projected_field_obligations"),
            Some("2")
        );

        let balance_array = ChcVar::new(
            "balance_array",
            result.problem.predicates()[0].arg_sorts[0].clone(),
        );
        let live_array = ChcVar::new(
            "live_array",
            result.problem.predicates()[0].arg_sorts[1].clone(),
        );
        let formula = ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(balance_array.clone()), ChcExpr::BitVec(4, 160)),
            ChcExpr::BitVec(9, 256),
        );
        let mut model = InvariantModel::new();
        model.set(
            pred,
            PredicateInterpretation::new(vec![balance_array, live_array], formula),
        );

        let _ = result.back_translator.translate_validity(model);
        let memory = result.back_translator.transform_memory();
        assert_eq!(
            memory.fact_value("observed_projected_array_keys"),
            Some("1")
        );
        assert_eq!(memory.fact_value("array_refinement_indices"), Some("1"));
        assert_eq!(
            memory.fact_value("backtranslated_projected_array_keys"),
            Some("1")
        );
        assert_eq!(
            result.back_translator.array_refinement_indices(),
            vec![(ChcSort::BitVec(160), ChcExpr::BitVec(4, 160))]
        );
    }

    #[test]
    fn transformer_memory_records_source_store_keys_for_refinement() {
        let arr_sort = array_pair_sort();
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Inv", vec![arr_sort.clone()]);

        let balances = ChcVar::new("balances", arr_sort);
        let updated = ChcExpr::store(
            ChcExpr::var(balances.clone()),
            ChcExpr::BitVec(11, 160),
            pair_value(ChcExpr::BitVec(7, 256), ChcExpr::Bool(true)),
        );
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(pred, vec![ChcExpr::var(balances)])], None),
            ClauseHead::Predicate(pred, vec![updated]),
        ));

        let result = Box::new(SolidityArrayDtProjectionTransformer::new()).transform(problem);
        let memory = result.back_translator.transform_memory();

        assert_eq!(
            memory.fact_value("source_observed_projected_array_keys"),
            Some("1")
        );
        assert_eq!(
            memory.fact_value("observed_projected_array_keys"),
            Some("1")
        );
        assert_eq!(memory.fact_value("array_refinement_indices"), Some("1"));
        assert_eq!(
            result.back_translator.array_refinement_indices(),
            vec![(ChcSort::BitVec(160), ChcExpr::BitVec(11, 160))]
        );
    }

    #[test]
    fn transformer_refinement_indices_deduplicate_source_and_backtranslation_keys() {
        let arr_sort = array_pair_sort();
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Inv", vec![arr_sort.clone()]);

        let balances = ChcVar::new("balances", arr_sort);
        let updated = ChcExpr::store(
            ChcExpr::var(balances.clone()),
            ChcExpr::BitVec(4, 160),
            pair_value(ChcExpr::BitVec(7, 256), ChcExpr::Bool(true)),
        );
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(pred, vec![ChcExpr::var(balances)])], None),
            ClauseHead::Predicate(pred, vec![updated]),
        ));

        let result = Box::new(SolidityArrayDtProjectionTransformer::new()).transform(problem);
        let balance_array = ChcVar::new(
            "balance_array",
            result.problem.predicates()[0].arg_sorts[0].clone(),
        );
        let live_array = ChcVar::new(
            "live_array",
            result.problem.predicates()[0].arg_sorts[1].clone(),
        );
        let formula = ChcExpr::eq(
            ChcExpr::select(ChcExpr::var(balance_array.clone()), ChcExpr::BitVec(4, 160)),
            ChcExpr::BitVec(9, 256),
        );
        let mut model = InvariantModel::new();
        model.set(
            pred,
            PredicateInterpretation::new(vec![balance_array, live_array], formula),
        );

        let _ = result.back_translator.translate_validity(model);
        let memory = result.back_translator.transform_memory();
        assert_eq!(
            memory.fact_value("observed_projected_array_keys"),
            Some("2")
        );
        assert_eq!(memory.fact_value("array_refinement_indices"), Some("1"));
        assert_eq!(
            result.back_translator.array_refinement_indices(),
            vec![(ChcSort::BitVec(160), ChcExpr::BitVec(4, 160))]
        );
    }

    #[test]
    fn transformer_rejects_raw_projected_array_in_backtranslation() {
        let arr_sort = array_pair_sort();
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Inv", vec![arr_sort]);

        let result = Box::new(SolidityArrayDtProjectionTransformer::new()).transform(problem);
        let balance_array = ChcVar::new(
            "balance_array",
            result.problem.predicates()[0].arg_sorts[0].clone(),
        );
        let live_array = ChcVar::new(
            "live_array",
            result.problem.predicates()[0].arg_sorts[1].clone(),
        );
        let formula = ChcExpr::eq(
            ChcExpr::var(balance_array.clone()),
            ChcExpr::var(balance_array.clone()),
        );
        let mut model = InvariantModel::new();
        model.set(
            pred,
            PredicateInterpretation::new(vec![balance_array, live_array], formula),
        );

        let translated = result.back_translator.translate_validity(model);
        let interp = translated.get(&pred).expect("predicate should be present");
        assert!(
            interp.vars.is_empty(),
            "unsupported raw projected arrays must poison the model so validation rejects SAFE"
        );
    }

    #[test]
    fn rejects_raw_select_of_projected_array() {
        let arr_sort = array_pair_sort();
        let mut problem = ChcProblem::new();
        let pred = problem.declare_predicate("Inv", vec![arr_sort.clone()]);

        let balances = ChcVar::new("balances", arr_sort.clone());
        let owner = ChcVar::new("owner", ChcSort::BitVec(160));
        let raw_select = ChcExpr::select(ChcExpr::var(balances.clone()), ChcExpr::var(owner));
        let opaque = ChcExpr::FuncApp("opaque".to_string(), ChcSort::Bool, vec![arc(raw_select)]);

        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(pred, vec![ChcExpr::var(balances.clone())])],
                Some(opaque),
            ),
            ClauseHead::Predicate(pred, vec![ChcExpr::var(balances)]),
        ));

        assert!(matches!(
            SolidityArrayDtProjector::project(&problem),
            SolidityArrayDtProjectionOutcome::Unsupported(
                SolidityArrayDtProjectionRejection::UnsupportedDatatypeExpression {
                    context: "raw select from projected array",
                    sort
                }
            ) if sort == pair_sort()
        ));
    }

    #[test]
    fn rejects_nested_array_dt_argument() {
        let wrapped_sort = ChcSort::Datatype {
            name: "State".to_string(),
            constructors: Arc::new(vec![ChcDtConstructor {
                name: "mkState".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "items".to_string(),
                    sort: array_pair_sort(),
                }],
            }]),
        };
        let mut problem = ChcProblem::new();
        problem.declare_predicate("Inv", vec![wrapped_sort.clone()]);

        assert!(matches!(
            SolidityArrayDtProjector::project(&problem),
            SolidityArrayDtProjectionOutcome::Unsupported(
                SolidityArrayDtProjectionRejection::NestedArrayDtArgument { sort }
            ) if sort == wrapped_sort
        ));
    }
}
