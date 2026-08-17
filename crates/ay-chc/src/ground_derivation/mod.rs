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

use crate::clause::{ClauseHead, HornClause};
use crate::expr::evaluate_expr;
use crate::smt::SmtValue;
use crate::{ChcExpr, ChcProblem};
use ay_core::kani_compat::DetHashMap as FxHashMap;

pub(crate) mod clause_map;
pub(crate) mod complete;
pub(crate) mod witness;

#[cfg(test)]
mod tests;

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
/// Carried for logging only; every variant is a hard rejection.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum GroundDerivationError {
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
}

impl std::fmt::Display for GroundDerivationError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
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
        }
    }
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
    let value = match evaluate_expr(expr, env) {
        Some(value) => value,
        None => {
            let normalized = expr
                .clone()
                .simplify_array_ops()
                .simplify_constants()
                .simplify_array_ops()
                .simplify_constants();
            evaluate_expr(&normalized, env)?
        }
    };
    // `SmtValue::Opaque` is a solver placeholder, not a value. Letting one
    // through would make two unrelated placeholders compare equal and a
    // constraint "evaluate" without ever being decided, so it is rejected here
    // rather than at each use site.
    is_concrete(&value).then_some(value)
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
pub(crate) fn validate_ground_derivation(
    problem: &ChcProblem,
    derivation: &GroundDerivation,
) -> Result<(), GroundDerivationError> {
    if derivation.steps.is_empty() {
        return Err(GroundDerivationError::Empty);
    }
    if derivation.query_step >= derivation.steps.len() {
        return Err(GroundDerivationError::RootOutOfRange);
    }
    let clauses = problem.clauses();

    // Pass 1: structural well-formedness. Resolving every clause up front means
    // the value checks below can index without re-validating.
    for (idx, step) in derivation.steps.iter().enumerate() {
        let Some(clause) = clauses.get(step.clause_index) else {
            return Err(GroundDerivationError::ClauseOutOfRange {
                step: idx,
                clause_index: step.clause_index,
            });
        };
        for &premise in &step.premises {
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
        for &premise in &derivation.steps[idx].premises {
            if !reachable[premise] {
                reachable[premise] = true;
                stack.push(premise);
            }
        }
    }
    if let Some(step) = reachable.iter().position(|hit| !hit) {
        return Err(GroundDerivationError::UnreachableStep { step });
    }

    // Pass 3: the actual proof check — pure ground evaluation.
    for (idx, step) in derivation.steps.iter().enumerate() {
        let clause = &clauses[step.clause_index];

        if let Some(constraint) = &clause.body.constraint {
            match eval_ground(constraint, &step.env) {
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
            let premise_idx = step.premises[position];
            let premise = &derivation.steps[premise_idx];
            let premise_clause = &clauses[premise.clause_index];
            let Some(premise_head_args) = head_args(premise_clause) else {
                return Err(GroundDerivationError::PremisePredicateMismatch {
                    step: idx,
                    position,
                });
            };
            let premise_pred = premise_clause.head.predicate_id();
            if premise_pred != Some(*pred) || premise_head_args.len() != args.len() {
                return Err(GroundDerivationError::PremisePredicateMismatch {
                    step: idx,
                    position,
                });
            }
            for (argument, (use_arg, def_arg)) in
                args.iter().zip(premise_head_args.iter()).enumerate()
            {
                let (Some(use_value), Some(def_value)) = (
                    eval_ground(use_arg, &step.env),
                    eval_ground(def_arg, &premise.env),
                ) else {
                    return Err(GroundDerivationError::ArgumentNotGround {
                        step: idx,
                        position,
                        argument,
                    });
                };
                if !smt_values_equal(&use_value, &def_value) {
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
    }

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
/// `SmtValue`'s derived equality is syntactic, which is too strict for arrays:
/// the same array function has many `ArrayMap`/`ConstArray` spellings (shadowed
/// entries, a default-only map vs a const array). Comparing arrays through the
/// evaluator's own select semantics keeps the check exact without accepting
/// genuinely different functions: two maps agree only when they agree on the
/// union of their explicit keys AND on their defaults.
fn smt_values_equal(lhs: &SmtValue, rhs: &SmtValue) -> bool {
    match (lhs, rhs) {
        (
            SmtValue::ArrayMap { .. } | SmtValue::ConstArray(_),
            SmtValue::ArrayMap { .. } | SmtValue::ConstArray(_),
        ) => array_values_equal(lhs, rhs),
        (SmtValue::Datatype(lctor, largs), SmtValue::Datatype(rctor, rargs)) => {
            lctor == rctor
                && largs.len() == rargs.len()
                && largs
                    .iter()
                    .zip(rargs.iter())
                    .all(|(l, r)| smt_values_equal(l, r))
        }
        _ => lhs == rhs,
    }
}

/// Explicit keys of an array value (empty for a const array).
fn array_keys(value: &SmtValue) -> Vec<SmtValue> {
    match value {
        SmtValue::ArrayMap { entries, .. } => entries.iter().map(|(key, _)| key.clone()).collect(),
        _ => Vec::new(),
    }
}

/// Default (else-branch) value of an array value.
fn array_default(value: &SmtValue) -> Option<&SmtValue> {
    match value {
        SmtValue::ArrayMap { default, .. } | SmtValue::ConstArray(default) => Some(default),
        _ => None,
    }
}

/// Read an array value at `key` (last store wins), falling back to the default.
fn array_read(value: &SmtValue, key: &SmtValue) -> Option<SmtValue> {
    match value {
        SmtValue::ArrayMap { default, entries } => {
            for (entry_key, entry_value) in entries.iter().rev() {
                if entry_key == key {
                    return Some(entry_value.clone());
                }
            }
            Some((**default).clone())
        }
        SmtValue::ConstArray(default) => Some((**default).clone()),
        _ => None,
    }
}

/// Extensional equality on concrete array values, restricted to the finitely
/// many points where the two values can differ (their explicit keys) plus the
/// defaults.
fn array_values_equal(lhs: &SmtValue, rhs: &SmtValue) -> bool {
    let (Some(lhs_default), Some(rhs_default)) = (array_default(lhs), array_default(rhs)) else {
        return false;
    };
    if !smt_values_equal(lhs_default, rhs_default) {
        return false;
    }
    let mut keys = array_keys(lhs);
    keys.extend(array_keys(rhs));
    for key in keys {
        let (Some(lhs_value), Some(rhs_value)) = (array_read(lhs, &key), array_read(rhs, &key))
        else {
            return false;
        };
        if !smt_values_equal(&lhs_value, &rhs_value) {
            return false;
        }
    }
    true
}
