// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Algebraic invariant synthesis from polynomial closed forms.
//!
//! When a loop has a triangular recurrence with polynomial closed forms
//! (e.g., B' = B + A where A increments linearly), this module derives
//! algebraic invariants by eliminating the iteration count variable n.
//!
//! The resulting invariants are non-linear (e.g., 2*B = A*(A+1)) and
//! cannot be discovered by PDR or CEGAR operating in LIA.
//!
//! # Design Source
//!
//! the development design notes
//! Issue: #7170 (s_multipl_22), #5651 (s_multipl_25)

use crate::cancellation::CancellationToken;
use crate::pdr::model::{InvariantModel, InvariantVerificationMethod, PredicateInterpretation};
use crate::recurrence::{analyze_transition, ClosedForm};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, Predicate, PredicateId};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;
use std::cell::Cell;

mod bv_gate;
mod init;
mod polynomial;
mod transfer;
mod transfer_entry;
mod validate;

#[cfg(test)]
mod tests;

use self::bv_gate::has_bv_variables;
use self::init::extract_init_values;
use self::polynomial::eliminate_iteration_count;
use self::transfer::{derive_conserved_invariant, derive_transferred_invariant_from_incoming};
pub(crate) use self::validate::AlgebraicValidationStats;
use self::validate::{validate_model_with_algebraic_fallback_and_stats, AlgebraicValidationResult};

struct NormalizedSelfLoop {
    pre_vars: Vec<String>,
    updates: FxHashMap<String, ChcExpr>,
    constraint: ChcExpr,
    /// Sort of each pre-state variable, keyed by name (#8717).
    /// Populated from body predicate args so that downstream code reconstructing
    /// `_next` variables or substituting post-vars preserves the real sort
    /// (BitVec, Int, Real, ...) instead of defaulting to `ChcSort::Int`.
    var_sorts: FxHashMap<String, ChcSort>,
}

/// Cooperative stop condition for algebraic synthesis and validation.
///
/// Bundles the wall-clock deadline the caller hands down with the portfolio's
/// cancellation token so both are checked by one call.
///
/// # The budget this replaced was unenforceable (#9110)
///
/// The deadline used to be consulted in exactly three places: the transfer
/// loop (#9004), the per-clause head of the SMT validation loop (#8753), and
/// the pre-query check inside it. Every one of them sits at the top of a loop
/// whose SINGLE iteration is where the time actually goes, so the checks
/// looked correct and bounded nothing:
///
/// * The pre-strategy had no entry gate, and it is entered up to three times
///   per solve (original problem, BvToInt retry, adaptive escalation round)
///   sharing one deadline — so entries two and three replayed the entire
///   phase against a deadline that had already passed.
/// * The per-predicate synthesis loop never polled at all.
/// * [`conjoin`] folded with `reduce(ChcExpr::and)`, which is Θ(n²)
///   hash-consing (see its docs) and a single un-pollable statement.
/// * `validation_body_syntactically_implies_head` scans every head conjunct
///   against the whole body — Θ(|head|·|body|) inside ONE iteration of the
///   per-clause loop, and it took no deadline in any form.
///
/// The last of those dominated: on a 120-variable lockstep problem given a
/// 10 ms budget, 2.024 s of the 2.035 s spent was that one loop. The symptom
/// this produces is a total runtime that does not move when the budget moves,
/// which is what the corpus cells showed (33.67 s at a nominal 5 s, 33.63 s at
/// 20 s).
///
/// The cancellation token never reached this module in any form either, so a
/// caller that armed `cancellation_handle().cancel_after(..)` saw no effect
/// beyond the cost of arming it.
///
/// `tripped` latches: once either condition has fired, further polls are a
/// single `Cell` load rather than a clock read. This matters because the polls
/// are now on hot inner loops.
pub(super) struct SynthesisBudget {
    deadline: Option<Instant>,
    cancellation: Option<CancellationToken>,
    tripped: Cell<bool>,
}

impl SynthesisBudget {
    pub(super) fn new(deadline: Option<Instant>, cancellation: Option<CancellationToken>) -> Self {
        Self {
            deadline,
            cancellation,
            tripped: Cell::new(false),
        }
    }

    /// A budget that never trips, for callers with no deadline and no token.
    #[cfg(test)]
    pub(super) fn unbounded() -> Self {
        Self::new(None, None)
    }

    /// The wall-clock deadline, for the phases that still take one directly.
    pub(super) fn deadline(&self) -> Option<Instant> {
        self.deadline
    }

    /// True once the deadline has passed or the caller cancelled.
    ///
    /// Every caller of this treats `true` as "abandon synthesis and report
    /// [`AlgebraicResult::NotApplicable`]". No caller may keep a partial
    /// result: weakening a candidate interpretation is not a safe default here
    /// because the validator can read a too-weak interpretation as evidence
    /// that bad states are reachable and report `Unsafe`.
    pub(super) fn expired(&self) -> bool {
        if self.tripped.get() {
            return true;
        }
        let done = self
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
            || self
                .cancellation
                .as_ref()
                .is_some_and(CancellationToken::is_cancelled);
        if done {
            self.tripped.set(true);
        }
        done
    }
}

/// Result of algebraic invariant synthesis.
#[derive(Debug)]
pub(crate) enum AlgebraicResult {
    /// The system is safe: an inductive invariant was found.
    Safe(InvariantModel),
    /// The system is unsafe: concrete evaluation proved bad states are reachable
    /// from a correct algebraic invariant. The algebraic closed form is valid
    /// (init and transition clauses hold) but the query clause admits bad states.
    Unsafe,
    /// Algebraic synthesis is not applicable or failed.
    NotApplicable,
}

/// Try to solve the CHC problem using algebraic invariant synthesis.
///
/// Returns `AlgebraicResult::Safe(model)` if algebraic invariants can be derived
/// and the safety condition is implied. Returns `AlgebraicResult::Unsafe` when
/// the algebraic invariant is correct but bad states are reachable (concrete
/// evaluation proves the query clause is satisfiable). Returns
/// `AlgebraicResult::NotApplicable` if the approach doesn't apply or fails.
#[allow(dead_code)] // thin wrapper retained for future deadline-less callers
pub(crate) fn try_algebraic_solve(problem: &ChcProblem, verbose: bool) -> AlgebraicResult {
    try_algebraic_solve_with_deadline(problem, verbose, None)
}

/// Deadline-aware variant of [`try_algebraic_solve`].
///
/// When `deadline` is `Some`, the SMT validation phase enforces the budget by
/// bailing out with `AlgebraicResult::NotApplicable` once the deadline passes.
/// This prevents the pre-strategy from consuming the full CHC wall clock when
/// validation hits thousands of hard SMT queries (#8753).
pub(crate) fn try_algebraic_solve_with_deadline(
    problem: &ChcProblem,
    verbose: bool,
    deadline: Option<Instant>,
) -> AlgebraicResult {
    try_algebraic_solve_with_deadline_impl(
        problem,
        verbose,
        &SynthesisBudget::new(deadline, None),
        None,
    )
}

/// [`try_algebraic_solve_with_deadline`] that also observes a cancellation
/// token.
///
/// The portfolio and adaptive layers pass their own token here so an embedding
/// driver's `cancellation_handle().cancel()` / `.cancel_after(..)` winds the
/// pre-strategy down, exactly as it already does for the engine lanes.
pub(crate) fn try_algebraic_solve_with_budget(
    problem: &ChcProblem,
    verbose: bool,
    deadline: Option<Instant>,
    cancellation: Option<CancellationToken>,
) -> AlgebraicResult {
    try_algebraic_solve_with_deadline_impl(
        problem,
        verbose,
        &SynthesisBudget::new(deadline, cancellation),
        None,
    )
}

/// Deadline-only shim over [`try_algebraic_solve_with_budget_and_stats`].
///
/// Production callers pass a cancellation token as well and go through the
/// budget entry point directly; this spelling is kept for the regression tests,
/// which exercise deadline behaviour on its own.
#[cfg(test)]
pub(crate) fn try_algebraic_solve_with_deadline_and_stats(
    problem: &ChcProblem,
    verbose: bool,
    deadline: Option<Instant>,
) -> (AlgebraicResult, AlgebraicValidationStats) {
    try_algebraic_solve_with_budget_and_stats(problem, verbose, deadline, None)
}

pub(crate) fn try_algebraic_solve_with_budget_and_stats(
    problem: &ChcProblem,
    verbose: bool,
    deadline: Option<Instant>,
    cancellation: Option<CancellationToken>,
) -> (AlgebraicResult, AlgebraicValidationStats) {
    let mut stats = AlgebraicValidationStats::default();
    let result = try_algebraic_solve_with_deadline_impl(
        problem,
        verbose,
        &SynthesisBudget::new(deadline, cancellation),
        Some(&mut stats),
    );
    (result, stats)
}

fn try_algebraic_solve_with_deadline_impl(
    problem: &ChcProblem,
    verbose: bool,
    budget: &SynthesisBudget,
    mut validation_stats: Option<&mut AlgebraicValidationStats>,
) -> AlgebraicResult {
    let predicates = problem.predicates();
    if predicates.is_empty() {
        return AlgebraicResult::NotApplicable;
    }

    // Entry gate. The pre-strategy is entered twice per solve on BV problems
    // (once on the original problem, once on the BvToInt abstraction, sharing
    // one deadline), and the adaptive layer's escalation round re-enters it
    // again. Without this check the second and third entries each replayed the
    // whole unpolled synthesis phase against a deadline that had already
    // passed — the dominant term in the measured overrun.
    if budget.expired() {
        if verbose {
            safe_eprintln!("Algebraic: deadline already expired on entry; not starting synthesis");
        }
        return AlgebraicResult::NotApplicable;
    }

    let mut model = InvariantModel::new();
    let mut solved_preds: FxHashSet<PredicateId> = FxHashSet::default();
    let mut solved_invariants: FxHashMap<PredicateId, Vec<ChcExpr>> = FxHashMap::default();
    let mut synthesis_stats = AlgebraicValidationStats::default();

    seed_fact_predicates(
        problem,
        predicates,
        &mut model,
        &mut solved_preds,
        &mut solved_invariants,
        verbose,
    );

    for pred in predicates {
        // Per-predicate poll. One clock read against a synthesis pipeline that
        // scans every clause in the problem is free, and without it this loop
        // ran to completion over every predicate no matter how long ago the
        // budget expired.
        if budget.expired() {
            if verbose {
                safe_eprintln!(
                    "Algebraic: synthesis deadline exceeded, handing control back to the portfolio"
                );
            }
            if let Some(validation_stats) = validation_stats.as_deref_mut() {
                validation_stats.merge(&synthesis_stats);
            }
            return AlgebraicResult::NotApplicable;
        }
        if verbose {
            safe_eprintln!("Algebraic: checking pred {} (id {:?})", pred.name, pred.id);
        }
        let self_loop = find_self_loop(problem, pred.id);
        let self_loop = match self_loop {
            Some(c) => c,
            None => {
                if verbose {
                    safe_eprintln!("Algebraic: pred {} has no self-loop", pred.name);
                }
                continue;
            }
        };

        let normalized = match extract_normalized_self_loop(self_loop) {
            Some(t) => t,
            None => {
                if verbose {
                    safe_eprintln!("Algebraic: pred {} transition extraction failed", pred.name);
                }
                continue;
            }
        };

        // Phase 2 of #8717: bail out when any transition variable has a BV sort.
        // Polynomial recurrence synthesis is algorithmically wrong for BV
        // updates (bvshl, bvor, bvudiv, ...); letting the synthesizer run wastes
        // the portfolio's time budget before PDR/IC3 can try.
        // See crates/ay-chc/src/algebraic_invariant/bv_gate.rs.
        if has_bv_variables(&normalized.var_sorts) {
            tracing::debug!(
                pred = %pred.name,
                "algebraic_invariant: skipping BV transition (#8717 Phase 2 gate)"
            );
            if verbose {
                safe_eprintln!(
                    "Algebraic: pred {} skipped — BV transition (#8717 Phase 2 gate)",
                    pred.name
                );
            }
            continue;
        }

        let pre_vars = normalized.pre_vars.clone();
        let transition = normalized_transition_expr(&normalized.updates, &normalized.var_sorts);
        let init_values = match extract_init_values(problem, pred.id, &pre_vars) {
            Some(v) => v,
            None => {
                if verbose {
                    safe_eprintln!("Algebraic: pred {} init value extraction failed", pred.name);
                }
                continue;
            }
        };
        let constant_deltas = extract_constant_deltas(&normalized.updates);

        if verbose {
            safe_eprintln!(
                "Algebraic: pred {} pre_vars={:?}, transition={:?}",
                pred.name,
                pre_vars,
                transition
            );
        }

        if verbose {
            safe_eprintln!(
                "Algebraic: pred {} init_values={:?}",
                pred.name,
                init_values
            );
        }

        let mut invariants = derive_auxiliary_invariants(
            problem,
            pred.id,
            &normalized,
            &constant_deltas,
            &init_values,
        );

        // #8660 Phase 2: bounds/monotonicity over select(arr, const_idx)
        // projections when the transition stores to `arr` at a constant index.
        // Complements the fact-clause conjunct lifter (Phase 1) by proposing
        // range and difference invariants that are needed for PDR to close
        // benchmarks where the safety query depends on an upper bound the
        // array cell shares with a scalar counter.
        invariants.extend(derive_select_projection_invariants(
            problem,
            pred.id,
            &normalized,
            &constant_deltas,
            &init_values,
            verbose,
        ));
        invariants.extend(derive_query_active_diff_bound_invariants(
            problem,
            pred,
            &normalized.pre_vars,
            verbose,
        ));

        let mut has_polynomial = false;
        if let Some(system) = analyze_transition(&transition, &pre_vars) {
            if verbose {
                for (name, cf) in &system.solutions {
                    safe_eprintln!(
                        "Algebraic: pred {} var {} closed form: {:?}",
                        pred.name,
                        name,
                        cf
                    );
                }
            }

            has_polynomial = system
                .solutions
                .values()
                .any(|cf| matches!(cf, ClosedForm::Polynomial { .. }));

            if has_polynomial {
                invariants.extend(eliminate_iteration_count(&system, &init_values));

                // Add constant-value invariants for ConstantDelta(0) variables.
                // These are needed so that transfer clause validation can constrain
                // the constant variables' values (e.g., G=0 in s_multipl_25).
                for (name, cf) in &system.solutions {
                    if matches!(cf, ClosedForm::ConstantDelta { delta: 0 }) {
                        if let Some(&val) = init_values.get(name) {
                            let var = ChcVar::new(name.clone(), ChcSort::Int);
                            invariants.push(ChcExpr::eq(ChcExpr::var(var), ChcExpr::int(val)));
                        }
                    }
                }
            }
        } else if verbose {
            safe_eprintln!(
                "Algebraic: pred {} analyze_transition returned None",
                pred.name
            );
        }

        if !has_polynomial && invariants.is_empty() {
            if verbose {
                safe_eprintln!(
                    "Algebraic: pred {} has no polynomial or auxiliary invariants",
                    pred.name
                );
            }
            continue;
        }
        if invariants.is_empty() {
            continue;
        }

        if verbose {
            safe_eprintln!(
                "Algebraic: pred {} has {} invariant(s) from algebraic/auxiliary synthesis",
                pred.name,
                invariants.len()
            );
        }

        let pred_vars: Vec<ChcVar> = pre_vars
            .iter()
            .enumerate()
            .map(|(i, name)| {
                let sort = pred.arg_sorts.get(i).cloned().unwrap_or(ChcSort::Int);
                ChcVar::new(name.clone(), sort)
            })
            .collect();

        solved_invariants.insert(pred.id, invariants.clone());
        // The conjunction itself is polled: hash-consing one large invariant
        // set is a single outer iteration with unbounded inner cost, so a
        // per-predicate check cannot bound it. A trip abandons synthesis
        // outright — see `conjoin_checked` for why no partial conjunction may
        // be kept.
        let Some(formula) = conjoin_checked(invariants, budget) else {
            if verbose {
                safe_eprintln!(
                    "Algebraic: deadline exceeded while conjoining pred {} invariants",
                    pred.name
                );
            }
            if let Some(validation_stats) = validation_stats.as_deref_mut() {
                validation_stats.merge(&synthesis_stats);
            }
            return AlgebraicResult::NotApplicable;
        };
        if verbose {
            safe_eprintln!("Algebraic: pred {} formula {:?}", pred.name, formula);
        }
        model.set(pred.id, PredicateInterpretation::new(pred_vars, formula));
        model.verification_method = InvariantVerificationMethod::AlgebraicClosedForm;
        solved_preds.insert(pred.id);
    }

    // Phase 2: For unsolved predicates, try conserved quantity approach first
    // (exact invariant from self-loop + entry conditions), then fall back to
    // transferred source/edge facts. The iteration is important for compiler
    // basic-block CHCs, where a launch-critical loop can sit hundreds of
    // single-predecessor blocks away from the fact clause (#9004).
    let self_loop_preds: FxHashSet<PredicateId> = problem
        .clauses()
        .iter()
        .filter_map(|clause| {
            if let ClauseHead::Predicate(pred, _) = &clause.head {
                is_self_loop_clause_for_pred(clause, *pred).then_some(*pred)
            } else {
                None
            }
        })
        .collect();
    let mut incoming_by_head: FxHashMap<PredicateId, Vec<&crate::HornClause>> =
        FxHashMap::default();
    for clause in problem.clauses() {
        if let Some(head_pred) = clause.head.predicate_id() {
            incoming_by_head.entry(head_pred).or_default().push(clause);
        }
    }

    loop {
        if budget.expired() {
            if verbose {
                safe_eprintln!(
                    "Algebraic: transfer deadline exceeded, handing control back to portfolio (#9004)"
                );
            }
            if let Some(validation_stats) = validation_stats.as_deref_mut() {
                validation_stats.merge(&synthesis_stats);
            }
            return AlgebraicResult::NotApplicable;
        }
        let mut changed = false;
        for pred in predicates {
            if budget.expired() {
                if verbose {
                    safe_eprintln!(
                        "Algebraic: transfer deadline exceeded, handing control back to portfolio (#9004)"
                    );
                }
                if let Some(validation_stats) = validation_stats.as_deref_mut() {
                    validation_stats.merge(&synthesis_stats);
                }
                return AlgebraicResult::NotApplicable;
            }
            if solved_preds.contains(&pred.id) {
                continue;
            }
            let mut formula = if self_loop_preds.contains(&pred.id) {
                derive_conserved_invariant(problem, pred, &model, &solved_preds, verbose)
            } else {
                None
            };
            if formula.is_none() {
                let incoming = incoming_by_head
                    .get(&pred.id)
                    .map_or(&[][..], Vec::as_slice);
                formula = derive_transferred_invariant_from_incoming(
                    problem,
                    pred,
                    incoming,
                    &model,
                    &solved_preds,
                    &solved_invariants,
                    Some(&mut synthesis_stats),
                    verbose,
                );
            }
            if let Some(formula) = formula {
                let pred_vars = canonical_predicate_vars(pred);
                let Some(formula) =
                    close_transferred_formula_over_predicate(problem, pred, formula, &pred_vars)
                else {
                    if verbose {
                        safe_eprintln!(
                            "Algebraic: transferred pred {} produced unclosed formula; skipping",
                            pred.name
                        );
                    }
                    continue;
                };
                solved_invariants
                    .insert(pred.id, formula.conjuncts().into_iter().cloned().collect());
                model.set(pred.id, PredicateInterpretation::new(pred_vars, formula));
                model.verification_method = InvariantVerificationMethod::AlgebraicClosedForm;
                solved_preds.insert(pred.id);
                changed = true;
                if verbose {
                    safe_eprintln!("Algebraic: solved transferred pred {}", pred.name);
                }
            }
        }
        if !changed {
            break;
        }
    }

    // Fill remaining unsolved predicates with `true`
    for pred in predicates {
        if !solved_preds.contains(&pred.id) {
            let pred_vars = canonical_predicate_vars(pred);
            model.set(
                pred.id,
                PredicateInterpretation::new(pred_vars, ChcExpr::Bool(true)),
            );
        }
    }

    if solved_preds.is_empty() {
        if let Some(validation_stats) = validation_stats.as_deref_mut() {
            validation_stats.merge(&synthesis_stats);
        }
        return AlgebraicResult::NotApplicable;
    }

    // Validate via SMT. Validation takes the whole budget, not just the
    // deadline: its per-clause and pre-query polls now observe cancellation
    // too, and its Θ(|head|·|body|) syntactic fast path polls on a stride
    // (#9110) so a clause cannot outrun the budget from the inside.
    if budget.expired() {
        if let Some(validation_stats) = validation_stats.as_deref_mut() {
            validation_stats.merge(&synthesis_stats);
        }
        return AlgebraicResult::NotApplicable;
    }
    let (validation, stats) = validate_model_with_algebraic_fallback_and_stats(
        problem,
        &model,
        &solved_preds,
        verbose,
        budget,
    );
    if let Some(validation_stats) = validation_stats {
        validation_stats.merge(&synthesis_stats);
        validation_stats.merge(&stats);
    }
    match validation {
        AlgebraicValidationResult::Valid => {
            if verbose {
                safe_eprintln!("Algebraic: model validated successfully");
            }
            AlgebraicResult::Safe(model)
        }
        AlgebraicValidationResult::UnsafeDetected => {
            if verbose {
                safe_eprintln!(
                    "Algebraic: model validation detected UNSAFE \
                     (invariant correct but bad states reachable)"
                );
            }
            AlgebraicResult::Unsafe
        }
        AlgebraicValidationResult::Invalid => {
            if verbose {
                safe_eprintln!("Algebraic: model validation failed");
            }
            AlgebraicResult::NotApplicable
        }
        AlgebraicValidationResult::DeadlineExceeded => {
            if verbose {
                safe_eprintln!(
                    "Algebraic: validation deadline exceeded, handing control back to portfolio (#8753)"
                );
            }
            AlgebraicResult::NotApplicable
        }
    }
}

/// Conjoin a derived invariant set into one formula.
///
/// `reduce(ChcExpr::and)` looked linear and was not: `ChcExpr::and(a, b)` is
/// `and_all([a, b])`, which re-flattens and re-deep-hashes the whole
/// accumulator on every step, so folding `n` conjuncts did Θ(n²) hash-consing.
/// A single `and_all` over the whole vector produces the identical expression
/// — same left-to-right order, same nested-`And` flattening, same
/// first-occurrence deduplication, same `false`/`true` folding — in one pass.
/// The zero- and one-element cases keep their original spellings so a lone
/// conjunct is still returned untouched rather than normalized.
pub(super) fn conjoin(exprs: Vec<ChcExpr>) -> ChcExpr {
    match exprs.len() {
        0 => ChcExpr::Bool(true),
        1 => exprs.into_iter().next().expect("len==1"),
        _ => ChcExpr::and_all(exprs),
    }
}

/// [`conjoin`] under a [`SynthesisBudget`], returning `None` when it trips.
///
/// SOUNDNESS: `None` means "abandon synthesis", never "use what was built so
/// far". Truncating the conjunction would hand the validator a WEAKER
/// interpretation than the one the synthesizer derived, and a too-weak
/// interpretation is not merely useless — `validate_model_with_algebraic_
/// fallback` reads a query clause that the interpretation fails to exclude as
/// evidence that bad states are reachable and reports `UnsafeDetected`. Every
/// caller therefore maps `None` to [`AlgebraicResult::NotApplicable`], which
/// yields no verdict at all and returns the budget to the portfolio.
fn conjoin_checked(exprs: Vec<ChcExpr>, budget: &SynthesisBudget) -> Option<ChcExpr> {
    match exprs.len() {
        0 => Some(ChcExpr::Bool(true)),
        1 => Some(exprs.into_iter().next().expect("len==1")),
        _ => ChcExpr::and_all_checked(exprs, || budget.expired()),
    }
}

fn canonical_predicate_vars(pred: &Predicate) -> Vec<ChcVar> {
    pred.arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
        .collect()
}

fn close_transferred_formula_over_predicate(
    problem: &ChcProblem,
    pred: &Predicate,
    formula: ChcExpr,
    pred_vars: &[ChcVar],
) -> Option<ChcExpr> {
    if formula_is_closed_over(&formula, pred_vars) {
        return Some(formula);
    }

    let self_loop = find_self_loop(problem, pred.id)?;
    let body_args = &self_loop.body.predicates.first()?.1;
    if body_args.len() != pred_vars.len() {
        return None;
    }

    let mut substitutions = Vec::with_capacity(body_args.len());
    for (arg, pred_var) in body_args.iter().zip(pred_vars) {
        let ChcExpr::Var(source_var) = arg else {
            return None;
        };
        if source_var.sort != pred_var.sort {
            return None;
        }
        substitutions.push((source_var.clone(), ChcExpr::var(pred_var.clone())));
    }

    let renamed = formula.substitute(&substitutions).simplify_constants();
    formula_is_closed_over(&renamed, pred_vars).then_some(renamed)
}

fn formula_is_closed_over(formula: &ChcExpr, allowed: &[ChcVar]) -> bool {
    let allowed: FxHashSet<ChcVar> = allowed.iter().cloned().collect();
    formula.vars().iter().all(|var| allowed.contains(var))
}

fn seed_fact_predicates(
    problem: &ChcProblem,
    predicates: &[Predicate],
    model: &mut InvariantModel,
    solved_preds: &mut FxHashSet<PredicateId>,
    solved_invariants: &mut FxHashMap<PredicateId, Vec<ChcExpr>>,
    verbose: bool,
) {
    for pred in predicates {
        let fact_formulas: Vec<ChcExpr> = problem
            .clauses()
            .iter()
            .filter(|clause| clause.is_fact() && clause.head.predicate_id() == Some(pred.id))
            .filter_map(|clause| fact_clause_formula(pred, clause))
            .collect();
        if fact_formulas.is_empty() {
            continue;
        }

        let formula = ChcExpr::or_all(fact_formulas).simplify_constants();
        let pred_vars = canonical_predicate_vars(pred);
        let allowed_vars: FxHashSet<ChcVar> = pred_vars.iter().cloned().collect();
        if !formula.vars().iter().all(|var| allowed_vars.contains(var)) {
            continue;
        }

        if verbose {
            safe_eprintln!(
                "Algebraic: seeded fact pred {} with {:?}",
                pred.name,
                formula
            );
        }
        solved_invariants.insert(pred.id, formula.conjuncts().into_iter().cloned().collect());
        model.set(pred.id, PredicateInterpretation::new(pred_vars, formula));
        model.verification_method = InvariantVerificationMethod::AlgebraicClosedForm;
        solved_preds.insert(pred.id);
    }
}

fn fact_clause_formula(pred: &Predicate, clause: &crate::HornClause) -> Option<ChcExpr> {
    let ClauseHead::Predicate(_, head_args) = &clause.head else {
        return None;
    };
    if head_args.len() != pred.arg_sorts.len() {
        return None;
    }

    let pred_vars = canonical_predicate_vars(pred);
    let mut substitution = Vec::new();
    let mut constraints = Vec::new();
    for (idx, head_arg) in head_args.iter().enumerate() {
        let formal = pred_vars[idx].clone();
        if let ChcExpr::Var(v) = head_arg {
            substitution.push((v.clone(), ChcExpr::var(formal)));
        }
    }
    for (idx, head_arg) in head_args.iter().enumerate() {
        if !matches!(head_arg, ChcExpr::Var(_)) {
            constraints.push(ChcExpr::eq(
                ChcExpr::var(pred_vars[idx].clone()),
                head_arg.substitute(&substitution),
            ));
        }
    }
    constraints.push(
        clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true))
            .substitute(&substitution),
    );

    Some(ChcExpr::and_all(constraints).simplify_constants())
}

fn is_self_loop_clause_for_pred(clause: &crate::HornClause, pred: PredicateId) -> bool {
    clause.head.predicate_id() == Some(pred)
        && clause.body.predicates.len() == 1
        && clause.body.predicates[0].0 == pred
}

/// Find the self-loop clause for a predicate.
fn find_self_loop(problem: &ChcProblem, pred: PredicateId) -> Option<&crate::HornClause> {
    problem.clauses().iter().find(|c| {
        c.head.predicate_id() == Some(pred)
            && c.body.predicates.len() == 1
            && c.body.predicates[0].0 == pred
    })
}

/// Extract normalized transition from a self-loop clause.
///
/// Returns (pre_var_names, transition_expr) where the transition uses
/// `{var}_next` naming for post-state variables, with all inter-variable
/// references resolved (forward substitution).
///
/// Example: body(A,B), constraint (= C (+ 1 A)) (= D (+ B C)), head(C,D)
/// → pre_vars = [`A`, `B`]
///   transition = (and (= A_next (+ 1 A)) (= B_next (+ B (+ 1 A))))
fn extract_normalized_transition(clause: &crate::HornClause) -> Option<(Vec<String>, ChcExpr)> {
    let normalized = extract_normalized_self_loop(clause)?;
    let transition = normalized_transition_expr(&normalized.updates, &normalized.var_sorts);
    Some((normalized.pre_vars, transition))
}

fn extract_normalized_self_loop(clause: &crate::HornClause) -> Option<NormalizedSelfLoop> {
    let body_args = &clause.body.predicates[0].1;
    let head_args = match &clause.head {
        ClauseHead::Predicate(_, args) => args,
        ClauseHead::False => return None,
    };

    // Pre-state variable names from body predicate args
    let pre_vars: Vec<String> = body_args
        .iter()
        .filter_map(|a| match a {
            ChcExpr::Var(v) => Some(v.name.clone()),
            _ => None,
        })
        .collect();

    if pre_vars.len() != body_args.len() || pre_vars.len() != head_args.len() {
        return None;
    }

    // Record each variable's real sort so that `_next` vars constructed later
    // (and post-var substitutions) preserve BitVec/Int/Real sorts instead of
    // defaulting to ChcSort::Int (#8717). Prefer the body arg's sort (pre-var),
    // fall back to the head arg's sort (post-var when it appears directly).
    let mut var_sorts: FxHashMap<String, ChcSort> = FxHashMap::default();
    for arg in body_args.iter().chain(head_args.iter()) {
        if let ChcExpr::Var(v) = arg {
            var_sorts
                .entry(v.name.clone())
                .or_insert_with(|| v.sort.clone());
        }
    }

    let constraint = clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));

    // Step 1: Collect head variables that may be defined in the body constraint.
    let post_vars: Vec<String> = head_args
        .iter()
        .filter_map(|arg| match arg {
            ChcExpr::Var(v) => Some(v.name.clone()),
            _ => None,
        })
        .collect();

    // Step 2: Extract definitions of head variables from constraint.
    // Look for (= post_var expr) patterns.
    let mut post_defs: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for conj in constraint.conjuncts() {
        if let ChcExpr::Op(ChcOp::Eq, args) = conj {
            if args.len() == 2 {
                if let ChcExpr::Var(v) = &*args[0] {
                    if post_vars.contains(&v.name) {
                        post_defs.insert(v.name.clone(), (*args[1]).clone());
                    }
                }
                // Also check reversed: (= expr post_var)
                if let ChcExpr::Var(v) = &*args[1] {
                    if post_vars.contains(&v.name) && !post_defs.contains_key(&v.name) {
                        post_defs.insert(v.name.clone(), (*args[0]).clone());
                    }
                }
            }
        }
    }

    // Step 3: Topologically resolve post-var references in definitions.
    // If post_var C appears in D's definition, substitute C's definition first.
    let resolved = resolve_post_var_refs(&post_vars, &post_defs, &var_sorts);
    let substitution: Vec<(ChcVar, ChcExpr)> = resolved
        .iter()
        .map(|(name, expr)| {
            let sort = var_sorts.get(name).cloned().unwrap_or(ChcSort::Int);
            (ChcVar::new(name.clone(), sort), expr.clone())
        })
        .collect();

    // Step 4: Build normalized updates keyed by pre-state variable name.
    // Strip BvToInt ITE/mod wrappers (#7931) so that extract_constant_deltas
    // and derive_auxiliary_invariants see the underlying linear structure.
    // Without stripping, updates like ite(i+1 < 2^32, i+1, i+1 - 2^32)
    // won't match the x+K or x-K patterns needed for bound derivation.
    let mut updates: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for (head_arg, pre_var) in head_args.iter().zip(pre_vars.iter()) {
        let update = match head_arg {
            ChcExpr::Var(v) => resolved
                .get(&v.name)
                .cloned()
                .unwrap_or_else(|| ChcExpr::var(v.clone())),
            expr => expr.clone(),
        };
        let update = if substitution.is_empty() {
            update
        } else {
            update.substitute(&substitution)
        };
        let update = crate::recurrence::strip_bv_wrapping(&update);
        updates.insert(pre_var.clone(), update);
    }

    if updates.is_empty() {
        return None;
    }

    Some(NormalizedSelfLoop {
        pre_vars,
        updates,
        constraint,
        var_sorts,
    })
}

fn normalized_transition_expr(
    updates: &FxHashMap<String, ChcExpr>,
    var_sorts: &FxHashMap<String, ChcSort>,
) -> ChcExpr {
    let mut transition_conjuncts: Vec<ChcExpr> = updates
        .iter()
        .map(|(pre_var, def)| {
            // Preserve the pre-var's real sort on the `_next` var so BitVec
            // state doesn't silently become Int-sorted (#8717).
            let sort = var_sorts.get(pre_var).cloned().unwrap_or(ChcSort::Int);
            let next_var = ChcVar::new(format!("{pre_var}_next"), sort);
            ChcExpr::eq(ChcExpr::var(next_var), def.clone())
        })
        .collect();
    transition_conjuncts.sort_by_cached_key(|expr| format!("{expr:?}"));
    conjoin(transition_conjuncts)
}

/// Resolve post-variable references in definitions by forward substitution.
///
/// If D is defined as (+ B C) and C is defined as (+ 1 A),
/// the resolved definition of D is (+ B (+ 1 A)).
///
/// `var_sorts` maps each pre-state variable name to its declared sort so
/// substitution keys preserve sort information; hashing `ChcVar` depends on
/// BOTH name and sort, so a hardcoded `ChcSort::Int` key would silently miss
/// post-state variables of other sorts (e.g., BitVec — see #8717).
fn resolve_post_var_refs(
    post_vars: &[String],
    defs: &FxHashMap<String, ChcExpr>,
    var_sorts: &FxHashMap<String, ChcSort>,
) -> FxHashMap<String, ChcExpr> {
    let mut resolved = defs.clone();

    // Simple iterative resolution (handles single-level dependencies)
    // For deeper chains, we'd need topological ordering, but CHC benchmarks
    // typically have at most 1 level of post-var dependency.
    for _pass in 0..post_vars.len() {
        let snapshot = resolved.clone();
        for (var, def) in resolved.iter_mut() {
            let substitution: Vec<(ChcVar, ChcExpr)> = post_vars
                .iter()
                .filter(|pv| *pv != var)
                .filter_map(|pv| {
                    snapshot.get(pv).map(|d| {
                        let sort = var_sorts.get(pv).cloned().unwrap_or(ChcSort::Int);
                        (ChcVar::new(pv.clone(), sort), d.clone())
                    })
                })
                .collect();
            if !substitution.is_empty() {
                *def = def.substitute(&substitution);
            }
        }
    }

    resolved
}

fn derive_auxiliary_invariants(
    problem: &ChcProblem,
    pred: PredicateId,
    normalized: &NormalizedSelfLoop,
    constant_deltas: &FxHashMap<String, i128>,
    init_values: &FxHashMap<String, i128>,
) -> Vec<ChcExpr> {
    let mut invariants = Vec::new();
    let mut lower_bounds: FxHashMap<String, i128> = FxHashMap::default();

    for (name, delta) in constant_deltas {
        let Some(&init) = init_values.get(name) else {
            continue;
        };
        let var = int_var_expr(name);
        if *delta > 0 {
            invariants.push(ChcExpr::ge(var, ChcExpr::int(init)));
            lower_bounds
                .entry(name.clone())
                .and_modify(|bound| *bound = (*bound).max(init))
                .or_insert(init);
        } else if *delta < 0 {
            invariants.push(ChcExpr::le(var, ChcExpr::int(init)));
        }
        if *delta > 1 {
            invariants.push(
                ChcExpr::eq(
                    ChcExpr::mod_op(
                        ChcExpr::sub(int_var_expr(name), ChcExpr::int(init)),
                        ChcExpr::int(*delta),
                    ),
                    ChcExpr::int(0),
                )
                .simplify_constants(),
            );
        }
    }

    let unchanged_vars: FxHashSet<String> = constant_deltas
        .iter()
        .filter_map(|(name, delta)| (*delta == 0).then_some(name.clone()))
        .collect();

    for fact_conjunct in normalized_fact_conjuncts(problem, pred, &normalized.pre_vars) {
        if fact_conjunct
            .vars()
            .iter()
            .all(|var| unchanged_vars.contains(&var.name))
        {
            if let Some((var, lower)) = lower_bound_from_atom(&fact_conjunct) {
                lower_bounds
                    .entry(var.clone())
                    .and_modify(|bound| *bound = (*bound).max(lower))
                    .or_insert(lower);
            }
            invariants.push(fact_conjunct);
        }
    }

    for guard_conjunct in normalized.constraint.conjuncts() {
        if !guard_conjunct
            .vars()
            .iter()
            .all(|var| normalized.pre_vars.contains(&var.name))
        {
            continue;
        }

        if let Some(inv) =
            derive_guard_bridge_invariant(guard_conjunct, constant_deltas, &unchanged_vars)
        {
            invariants.push(inv);
        }
    }

    derive_monotone_additive_lower_bound_invariants(
        &normalized.updates,
        init_values,
        &mut lower_bounds,
        &mut invariants,
    );

    for (var_name, update) in &normalized.updates {
        let Some(&init) = init_values.get(var_name) else {
            continue;
        };
        if init < 1 {
            continue;
        }

        let Some(factor_lb) = multiplicative_factor_lower_bound(update, var_name, &lower_bounds)
        else {
            continue;
        };
        if factor_lb >= 1 {
            invariants.push(ChcExpr::ge(int_var_expr(var_name), ChcExpr::int(init)));
        }
    }

    // Same-delta constant-difference invariants (#8419).
    //
    // When two variables have the same constant delta, their difference is
    // preserved across all transitions: if A' = A + d and B' = B + d, then
    // (B' - A') = (B - A). When the initial difference is a known constant
    // (extracted from init_values), we emit:
    //   - A == B              when init_diff == 0
    //   - B == A + init_diff  when init_diff != 0
    //
    // This is critical for DT+BV after flattening (#8419): two Option<BV8>
    // fields incremented in lockstep produce x_val8 and y_val8 with the same
    // delta=1 and same init=0. Without this, PDR cannot discover x_val8 == y_val8
    // and the solve times out.
    //
    // Sort variables by name for deterministic pair enumeration.
    let mut delta_vars: Vec<(&String, &i128)> = constant_deltas.iter().collect();
    delta_vars.sort_by_key(|(name, _)| name.as_str());
    for i in 0..delta_vars.len() {
        let (name_a, delta_a) = delta_vars[i];
        let Some(&init_a) = init_values.get(name_a) else {
            continue;
        };
        for (name_b, delta_b) in delta_vars.iter().copied().skip(i + 1) {
            if delta_a != delta_b {
                continue;
            }
            let Some(&init_b) = init_values.get(name_b) else {
                continue;
            };
            // i128-lockstep: checked i128 subtraction; skip the pair on
            // overflow instead of wrapping.
            let Some(diff) = init_b.checked_sub(init_a) else {
                continue;
            };
            let var_a = int_var_expr(name_a);
            let var_b = int_var_expr(name_b);
            if diff == 0 {
                // A == B
                invariants.push(ChcExpr::eq(var_a, var_b));
            } else {
                // B - A == diff  =>  B = A + diff
                invariants.push(ChcExpr::eq(var_b, ChcExpr::add(var_a, ChcExpr::int(diff))));
            }
        }
    }

    // Proportional-delta affine invariants.
    //
    // Same-delta reasoning above covers lockstep counters (`A == B`). CHC-COMP
    // LIA transfer cases also use counters with different constant deltas, for
    // example `A' = A + 1` and `C' = C - 2` from the same concrete entry.  The
    // affine combination `delta_b * A - delta_a * C` is preserved, and the
    // concrete fact entry gives its constant.  Emitting these source facts gives
    // downstream transfer a proof-safe relation to close under successor loops.
    for i in 0..delta_vars.len() {
        let (name_a, delta_a) = delta_vars[i];
        let Some(&init_a) = init_values.get(name_a) else {
            continue;
        };
        for (name_b, delta_b) in delta_vars.iter().copied().skip(i + 1) {
            if delta_a == delta_b {
                continue;
            }
            let Some(&init_b) = init_values.get(name_b) else {
                continue;
            };
            // i128-lockstep: checked i128 arithmetic (the old saturating_mul
            // could clamp); skip the pair on any overflow instead of
            // saturating/wrapping.
            let Some(neg_delta_a) = delta_a.checked_neg() else {
                continue;
            };
            let Some(rhs_const) = delta_b.checked_mul(init_a).and_then(|ba| {
                delta_a
                    .checked_mul(init_b)
                    .and_then(|ab| ba.checked_sub(ab))
            }) else {
                continue;
            };
            let lhs = affine_two_var_expr(*delta_b, name_a, neg_delta_a, name_b);
            let rhs = ChcExpr::int(rhs_const);
            invariants.push(ChcExpr::eq(lhs, rhs).simplify_constants());
        }
    }

    invariants
}

fn derive_monotone_additive_lower_bound_invariants(
    updates: &FxHashMap<String, ChcExpr>,
    init_values: &FxHashMap<String, i128>,
    lower_bounds: &mut FxHashMap<String, i128>,
    invariants: &mut Vec<ChcExpr>,
) {
    let mut ordered_updates: Vec<(&String, &ChcExpr)> = updates.iter().collect();
    ordered_updates.sort_by_key(|(name, _)| name.as_str());

    for _ in 0..ordered_updates.len() {
        let mut changed = false;
        for (var_name, update) in &ordered_updates {
            let Some(&init) = init_values.get(*var_name) else {
                continue;
            };
            if lower_bounds
                .get(*var_name)
                .is_some_and(|bound| *bound >= init)
            {
                continue;
            }
            let Some(increment) = additive_self_increment(update, var_name) else {
                continue;
            };
            let Some(increment_lb) = expr_lower_bound(&increment, lower_bounds) else {
                continue;
            };
            if increment_lb < 0 {
                continue;
            }

            invariants.push(ChcExpr::ge(int_var_expr(var_name), ChcExpr::int(init)));
            lower_bounds.insert((*var_name).clone(), init);
            changed = true;
        }
        if !changed {
            break;
        }
    }
}

fn additive_self_increment(update: &ChcExpr, var_name: &str) -> Option<ChcExpr> {
    let mut terms = Vec::new();
    collect_additive_terms(update, &mut terms);

    let mut saw_self = false;
    let mut increment_terms = Vec::new();
    for term in terms {
        if matches!(term, ChcExpr::Var(var) if var.name == var_name) {
            if saw_self {
                return None;
            }
            saw_self = true;
            continue;
        }
        if term.contains_var_name(var_name) {
            return None;
        }
        increment_terms.push(term.clone());
    }

    if !saw_self {
        return None;
    }
    Some(additive_terms_expr(increment_terms))
}

fn collect_additive_terms<'a>(expr: &'a ChcExpr, out: &mut Vec<&'a ChcExpr>) {
    match expr {
        ChcExpr::Op(ChcOp::Add, args) => {
            for arg in args {
                collect_additive_terms(arg, out);
            }
        }
        _ => out.push(expr),
    }
}

fn additive_terms_expr(terms: Vec<ChcExpr>) -> ChcExpr {
    terms
        .into_iter()
        .reduce(ChcExpr::add)
        .unwrap_or_else(|| ChcExpr::int(0))
        .simplify_constants()
}

#[derive(Debug, Clone)]
struct ActiveDiffBound {
    active_a: ChcVar,
    active_b: ChcVar,
    value_a: ChcVar,
    value_b: ChcVar,
    epsilon: ChcVar,
}

fn derive_query_active_diff_bound_invariants(
    problem: &ChcProblem,
    pred: &Predicate,
    pre_vars: &[String],
    verbose: bool,
) -> Vec<ChcExpr> {
    if !pred
        .arg_sorts
        .iter()
        .any(|sort| matches!(sort, ChcSort::Bool))
        || !pred
            .arg_sorts
            .iter()
            .any(|sort| matches!(sort, ChcSort::Real))
    {
        return Vec::new();
    }

    let mut invariants = Vec::new();
    let mut seen: FxHashSet<String> = FxHashSet::default();
    for clause in problem
        .clauses()
        .iter()
        .filter(|clause| matches!(clause.head, ClauseHead::False))
    {
        let [(body_pred, args)] = clause.body.predicates.as_slice() else {
            continue;
        };
        if *body_pred != pred.id || args.len() != pre_vars.len() {
            continue;
        }

        let mut substitution = Vec::new();
        for (idx, arg) in args.iter().enumerate() {
            let ChcExpr::Var(var) = arg else {
                continue;
            };
            let sort = pred
                .arg_sorts
                .get(idx)
                .cloned()
                .unwrap_or_else(|| var.sort.clone());
            substitution.push((
                var.clone(),
                ChcExpr::var(ChcVar::new(pre_vars[idx].clone(), sort)),
            ));
        }
        let query = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true))
            .substitute(&substitution);

        let mut bounds = Vec::new();
        collect_active_diff_bounds(&query, &mut Vec::new(), &mut bounds);
        for bound in bounds {
            let key = format!(
                "{}|{}|{}|{}|{}",
                bound.active_a.name,
                bound.active_b.name,
                bound.epsilon.name,
                bound.value_a.name,
                bound.value_b.name
            );
            if !seen.insert(key) {
                continue;
            }

            invariants.push(ChcExpr::or_all([
                ChcExpr::not(ChcExpr::var(bound.active_a)),
                ChcExpr::not(ChcExpr::var(bound.active_b)),
                ChcExpr::not(ChcExpr::le(
                    ChcExpr::var(bound.epsilon),
                    ChcExpr::sub(ChcExpr::var(bound.value_a), ChcExpr::var(bound.value_b)),
                )),
            ]));
        }
    }

    if verbose && !invariants.is_empty() {
        safe_eprintln!(
            "Algebraic: derived {} active diff-bound invariant(s) from safety query",
            invariants.len()
        );
    }
    invariants
}

fn collect_active_diff_bounds(
    expr: &ChcExpr,
    active_context: &mut Vec<ChcVar>,
    out: &mut Vec<ActiveDiffBound>,
) {
    if let Some((epsilon, value_a, value_b)) = parse_epsilon_distance_guard(expr) {
        let mut active = active_context.clone();
        active.sort_by(|a, b| a.name.cmp(&b.name));
        active.dedup_by(|a, b| a.name == b.name);
        if active.len() == 2 {
            out.push(ActiveDiffBound {
                active_a: active[0].clone(),
                active_b: active[1].clone(),
                value_a,
                value_b,
                epsilon,
            });
        }
        return;
    }

    let ChcExpr::Op(op, args) = expr else {
        return;
    };

    match op {
        ChcOp::And => {
            let original_len = active_context.len();
            for arg in args {
                if let Some(var) = positive_bool_var(arg) {
                    if !active_context.iter().any(|active| active.name == var.name) {
                        active_context.push(var);
                    }
                }
            }
            for arg in args {
                collect_active_diff_bounds(arg, active_context, out);
            }
            active_context.truncate(original_len);
        }
        ChcOp::Or | ChcOp::Ite | ChcOp::Implies => {
            for arg in args {
                collect_active_diff_bounds(arg, active_context, out);
            }
        }
        ChcOp::Not => {}
        _ => {
            for arg in args {
                collect_active_diff_bounds(arg, active_context, out);
            }
        }
    }
}

fn positive_bool_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Var(var) if matches!(var.sort, ChcSort::Bool) => Some(var.clone()),
        _ => None,
    }
}

fn parse_epsilon_distance_guard(expr: &ChcExpr) -> Option<(ChcVar, ChcVar, ChcVar)> {
    let ChcExpr::Op(ChcOp::Le, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let ChcExpr::Var(epsilon) = args[0].as_ref() else {
        return None;
    };
    if !matches!(epsilon.sort, ChcSort::Real | ChcSort::Int) {
        return None;
    }
    let (value_a, value_b) = parse_var_difference(args[1].as_ref())?;
    Some((epsilon.clone(), value_a, value_b))
}

fn parse_var_difference(expr: &ChcExpr) -> Option<(ChcVar, ChcVar)> {
    match expr {
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let ChcExpr::Var(lhs) = args[0].as_ref() else {
                return None;
            };
            let ChcExpr::Var(rhs) = args[1].as_ref() else {
                return None;
            };
            Some((lhs.clone(), rhs.clone()))
        }
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            if let (ChcExpr::Var(lhs), Some(rhs)) =
                (args[0].as_ref(), parse_negated_var(args[1].as_ref()))
            {
                return Some((lhs.clone(), rhs));
            }
            if let (ChcExpr::Var(lhs), Some(rhs)) =
                (args[1].as_ref(), parse_negated_var(args[0].as_ref()))
            {
                return Some((lhs.clone(), rhs));
            }
            None
        }
        _ => None,
    }
}

fn parse_negated_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => match args[0].as_ref() {
            ChcExpr::Var(var) => Some(var.clone()),
            _ => None,
        },
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            if is_minus_one(args[0].as_ref()) {
                if let ChcExpr::Var(var) = args[1].as_ref() {
                    return Some(var.clone());
                }
            }
            if is_minus_one(args[1].as_ref()) {
                if let ChcExpr::Var(var) = args[0].as_ref() {
                    return Some(var.clone());
                }
            }
            None
        }
        _ => None,
    }
}

fn is_minus_one(expr: &ChcExpr) -> bool {
    matches!(expr, ChcExpr::Int(-1) | ChcExpr::Real(-1, 1))
        || matches!(expr, ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 && matches!(args[0].as_ref(), ChcExpr::Int(1) | ChcExpr::Real(1, 1)))
}

fn normalized_fact_conjuncts(
    problem: &ChcProblem,
    pred: PredicateId,
    pre_vars: &[String],
) -> Vec<ChcExpr> {
    let Some(fact) = problem
        .clauses()
        .iter()
        .find(|clause| clause.is_fact() && clause.head.predicate_id() == Some(pred))
    else {
        return Vec::new();
    };

    let ClauseHead::Predicate(_, head_args) = &fact.head else {
        return Vec::new();
    };

    let substitution: Vec<(ChcVar, ChcExpr)> = head_args
        .iter()
        .zip(pre_vars.iter())
        .filter_map(|(head_arg, pre_var)| match head_arg {
            ChcExpr::Var(v) => Some((
                v.clone(),
                ChcExpr::var(ChcVar::new(pre_var.clone(), v.sort.clone())),
            )),
            _ => None,
        })
        .collect();

    fact.body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true))
        .conjuncts()
        .into_iter()
        .map(|conjunct| conjunct.substitute(&substitution))
        .collect()
}

fn derive_guard_bridge_invariant(
    guard: &ChcExpr,
    constant_deltas: &FxHashMap<String, i128>,
    unchanged_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    let (op, lhs, rhs) = bridgeable_comparison_parts(guard)?;

    if let Some(inv) = bridge_counter_comparison(lhs, rhs, &op, constant_deltas, unchanged_vars) {
        return Some(inv);
    }
    bridge_counter_comparison(
        rhs,
        lhs,
        &swap_comparison(&op)?,
        constant_deltas,
        unchanged_vars,
    )
}

fn bridgeable_comparison_parts(expr: &ChcExpr) -> Option<(ChcOp, &ChcExpr, &ChcExpr)> {
    let ChcExpr::Op(op, args) = expr else {
        return None;
    };
    if args.len() == 2 {
        return comparison_op(*op).map(|op| (op, args[0].as_ref(), args[1].as_ref()));
    }
    if !matches!(op, ChcOp::Not) || args.len() != 1 {
        return None;
    }
    let ChcExpr::Op(inner_op, inner_args) = args[0].as_ref() else {
        return None;
    };
    if inner_args.len() != 2 {
        return None;
    }
    negated_comparison_op(*inner_op).map(|op| (op, inner_args[0].as_ref(), inner_args[1].as_ref()))
}

fn comparison_op(op: ChcOp) -> Option<ChcOp> {
    match op {
        ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge => Some(op),
        _ => None,
    }
}

fn negated_comparison_op(op: ChcOp) -> Option<ChcOp> {
    Some(match op {
        ChcOp::Lt => ChcOp::Ge,
        ChcOp::Le => ChcOp::Gt,
        ChcOp::Gt => ChcOp::Le,
        ChcOp::Ge => ChcOp::Lt,
        _ => return None,
    })
}

fn bridge_counter_comparison(
    counter_side: &ChcExpr,
    bound_side: &ChcExpr,
    op: &ChcOp,
    constant_deltas: &FxHashMap<String, i128>,
    unchanged_vars: &FxHashSet<String>,
) -> Option<ChcExpr> {
    let ChcExpr::Var(counter_var) = counter_side else {
        return None;
    };
    let delta = *constant_deltas.get(&counter_var.name)?;
    if !bound_side
        .vars()
        .iter()
        .all(|var| unchanged_vars.contains(&var.name))
    {
        return None;
    }

    match (delta.signum(), op) {
        (1, &ChcOp::Lt) | (1, &ChcOp::Le) => Some(ChcExpr::le(
            int_var_expr(&counter_var.name),
            upper_bridge_bound(bound_side, matches!(op, ChcOp::Le)),
        )),
        (-1, &ChcOp::Gt) | (-1, &ChcOp::Ge) => Some(ChcExpr::ge(
            int_var_expr(&counter_var.name),
            lower_bridge_bound(bound_side, matches!(op, ChcOp::Ge)),
        )),
        _ => None,
    }
}

fn upper_bridge_bound(bound_side: &ChcExpr, inclusive_guard: bool) -> ChcExpr {
    if inclusive_guard {
        ChcExpr::add(bound_side.clone(), ChcExpr::int(1)).simplify_constants()
    } else {
        bound_side.clone()
    }
}

fn lower_bridge_bound(bound_side: &ChcExpr, inclusive_guard: bool) -> ChcExpr {
    if inclusive_guard {
        ChcExpr::sub(bound_side.clone(), ChcExpr::int(1)).simplify_constants()
    } else {
        bound_side.clone()
    }
}

fn multiplicative_factor_lower_bound(
    update: &ChcExpr,
    updated_var: &str,
    lower_bounds: &FxHashMap<String, i128>,
) -> Option<i128> {
    let ChcExpr::Op(ChcOp::Mul, args) = update else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    let lhs = &args[0];
    let rhs = &args[1];

    if matches!(lhs.as_ref(), ChcExpr::Var(v) if v.name == updated_var) {
        return expr_lower_bound(rhs, lower_bounds);
    }
    if matches!(rhs.as_ref(), ChcExpr::Var(v) if v.name == updated_var) {
        return expr_lower_bound(lhs, lower_bounds);
    }
    None
}

fn expr_lower_bound(expr: &ChcExpr, lower_bounds: &FxHashMap<String, i128>) -> Option<i128> {
    match expr {
        ChcExpr::Int(value) => Some(*value),
        ChcExpr::Var(v) => lower_bounds.get(&v.name).copied(),
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut acc = 0i128;
            for arg in args {
                acc = acc.checked_add(expr_lower_bound(arg, lower_bounds)?)?;
            }
            Some(acc)
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let lhs = expr_lower_bound(&args[0], lower_bounds)?;
            let rhs = args[1].as_i128()?;
            lhs.checked_sub(rhs)
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
            (ChcExpr::Int(coeff), expr) | (expr, ChcExpr::Int(coeff)) if *coeff >= 0 => {
                expr_lower_bound(expr, lower_bounds)?.checked_mul(*coeff)
            }
            _ => None,
        },
        _ => None,
    }
}

fn lower_bound_from_atom(atom: &ChcExpr) -> Option<(String, i128)> {
    let ChcExpr::Op(op, args) = atom else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }

    match (&*args[0], &*args[1], op) {
        (ChcExpr::Var(v), ChcExpr::Int(c), ChcOp::Ge) => Some((v.name.clone(), *c)),
        (ChcExpr::Var(v), ChcExpr::Int(c), ChcOp::Gt) => Some((v.name.clone(), c.checked_add(1)?)),
        (ChcExpr::Int(c), ChcExpr::Var(v), ChcOp::Le) => Some((v.name.clone(), *c)),
        (ChcExpr::Int(c), ChcExpr::Var(v), ChcOp::Lt) => Some((v.name.clone(), c.checked_add(1)?)),
        _ => None,
    }
}

fn swap_comparison(op: &ChcOp) -> Option<ChcOp> {
    Some(match *op {
        ChcOp::Lt => ChcOp::Gt,
        ChcOp::Le => ChcOp::Ge,
        ChcOp::Gt => ChcOp::Lt,
        ChcOp::Ge => ChcOp::Le,
        _ => return None,
    })
}

fn int_var_expr(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name.to_string(), ChcSort::Int))
}

fn affine_two_var_expr(coeff_a: i128, name_a: &str, coeff_b: i128, name_b: &str) -> ChcExpr {
    ChcExpr::add(
        scale_int_expr(coeff_a, int_var_expr(name_a)),
        scale_int_expr(coeff_b, int_var_expr(name_b)),
    )
    .simplify_constants()
}

fn scale_int_expr(coeff: i128, expr: ChcExpr) -> ChcExpr {
    match coeff {
        0 => ChcExpr::int(0),
        1 => expr,
        -1 => ChcExpr::neg(expr),
        n => ChcExpr::mul(ChcExpr::int(n), expr),
    }
    .simplify_constants()
}

fn extract_constant_deltas(updates: &FxHashMap<String, ChcExpr>) -> FxHashMap<String, i128> {
    let mut deltas = FxHashMap::default();
    for (var_name, update) in updates {
        let delta = match update {
            ChcExpr::Var(v) if v.name == *var_name => Some(0),
            ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == *var_name => Some(*c),
                (ChcExpr::Int(c), ChcExpr::Var(v)) if v.name == *var_name => Some(*c),
                _ => None,
            },
            ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
                (ChcExpr::Var(v), ChcExpr::Int(c)) if v.name == *var_name => (*c).checked_neg(),
                _ => None,
            },
            _ => None,
        };
        if let Some(delta) = delta {
            deltas.insert(var_name.clone(), delta);
        }
    }
    deltas
}

/// Derive bounds and difference invariants over `select(arr, const_idx)` when
/// the transition stores to `arr` at a constant index.
///
/// Issue: #8660 Phase 2. Complements the fact-clause conjunct lifter (Phase 1
/// in `fact_joint.rs`) by feeding the algebraic synthesizer enough information
/// to prove properties that mix array cells with scalar counters (e.g., the
/// upper bound `(<= (select mem 0) 100)` when `mem[0]` increments in lockstep
/// with `i`).
///
/// For each array pre-state variable whose update reduces to
/// `store(arr, c, arr[c] + k)` at some constant index `c`, with init fact
/// `(= (select arr c) v0)`:
///   - delta +k > 0: emit `(>= (select arr c) v0)`
///   - delta -k < 0: emit `(<= (select arr c) v0)`
///   - delta 0 (preservation): emit `(= (select arr c) v0)`
///
/// Cross-product with scalar counters: when the select-delta equals a scalar
/// counter's delta and we know both init values, emit the same-delta
/// constant-difference invariant `(= (select arr c) (+ scalar (v0 - s0)))`.
/// This mirrors the existing same-delta invariant (#8419) for scalars and is
/// what lets PDR close upper-bound queries.
///
/// All array-cell reasoning uses `expand_select_store_symbolic`, which is
/// guarded by `MAX_PREPROCESSING_NODES` and `MAX_EXPR_RECURSION_DEPTH`, so no
/// additional budget caps are needed here.
fn derive_select_projection_invariants(
    problem: &ChcProblem,
    pred: PredicateId,
    normalized: &NormalizedSelfLoop,
    constant_deltas: &FxHashMap<String, i128>,
    init_values: &FxHashMap<String, i128>,
    verbose: bool,
) -> Vec<ChcExpr> {
    // Collect constant-index fact values: (arr_name, const_idx, init_val) for
    // each fact conjunct shaped `(= (select arr c) v)` where `c` and `v` are
    // integer constants. Deduplicate by (arr_name, const_idx) keeping the
    // first seen init.
    let mut fact_projections: FxHashMap<(String, i128), i128> = FxHashMap::default();
    for conjunct in normalized_fact_conjuncts(problem, pred, &normalized.pre_vars) {
        let ChcExpr::Op(ChcOp::Eq, args) = &conjunct else {
            continue;
        };
        if args.len() != 2 {
            continue;
        }
        let (select_expr, value_expr) = match (&*args[0], &*args[1]) {
            (select @ ChcExpr::Op(ChcOp::Select, _), value) => (select, value),
            (value, select @ ChcExpr::Op(ChcOp::Select, _)) => (select, value),
            _ => continue,
        };
        let ChcExpr::Op(ChcOp::Select, sel_args) = select_expr else {
            continue;
        };
        if sel_args.len() != 2 {
            continue;
        }
        let ChcExpr::Var(arr_var) = &*sel_args[0] else {
            continue;
        };
        if !normalized.pre_vars.contains(&arr_var.name) {
            continue;
        }
        let ChcExpr::Int(idx) = &*sel_args[1] else {
            continue;
        };
        let ChcExpr::Int(val) = value_expr else {
            continue;
        };
        fact_projections
            .entry((arr_var.name.clone(), *idx))
            .or_insert(*val);
    }

    if fact_projections.is_empty() {
        return Vec::new();
    }

    // For each array pre-var, compute the select-delta at each known index.
    // A select-delta exists when the post-state update, restricted to
    // `select(post_arr, c)`, reduces to either `select(arr, c)` (preservation)
    // or `(+/- (select arr c) k)` (constant delta).
    let mut select_deltas: FxHashMap<(String, i128), i128> = FxHashMap::default();
    for (arr_name, post_expr) in &normalized.updates {
        let Some(arr_sort) = normalized.var_sorts.get(arr_name) else {
            continue;
        };
        if !matches!(arr_sort, ChcSort::Array(_, _)) {
            continue;
        }
        for (key, _init) in fact_projections.iter() {
            if key.0 != *arr_name {
                continue;
            }
            let idx = key.1;
            let select_post = ChcExpr::select(post_expr.clone(), ChcExpr::int(idx))
                .expand_select_store_symbolic();
            let simplified = select_post.simplify_constants();
            if let Some(delta) = classify_select_delta(&simplified, arr_name, idx) {
                select_deltas.insert(key.clone(), delta);
            }
        }
    }

    if verbose {
        safe_eprintln!(
            "Algebraic: pred #8660 select projections fact_projections={:?} select_deltas={:?}",
            fact_projections,
            select_deltas
        );
    }

    let mut invariants = Vec::new();

    // Emit bounds on select(arr, c) based on init value + select-delta sign.
    // Sort for determinism.
    let mut projection_keys: Vec<(&(String, i128), &i128)> = fact_projections.iter().collect();
    projection_keys.sort_by(|a, b| a.0.cmp(b.0));
    for (key, init_val) in projection_keys.iter() {
        let Some(&delta) = select_deltas.get(*key) else {
            continue;
        };
        let (arr_name, idx) = (&key.0, key.1);
        let arr_sort = match normalized.var_sorts.get(arr_name) {
            Some(sort) => sort.clone(),
            None => continue,
        };
        let select_pre = ChcExpr::select(
            ChcExpr::var(ChcVar::new(arr_name.clone(), arr_sort)),
            ChcExpr::int(idx),
        );
        if delta > 0 {
            invariants.push(ChcExpr::ge(select_pre, ChcExpr::int(**init_val)));
        } else if delta < 0 {
            invariants.push(ChcExpr::le(select_pre, ChcExpr::int(**init_val)));
        } else {
            // delta == 0: preservation — the cell never changes.
            invariants.push(ChcExpr::eq(select_pre, ChcExpr::int(**init_val)));
        }
    }

    // Same-delta cross-product between array-cell projections and scalar
    // counters (analog of #8419 for scalars). When `select(arr, c)` and
    // scalar `s` share delta `d`, their difference is preserved:
    //   (select arr c) - s == v0 - s0
    // We rewrite this as (= (select arr c) (+ s (v0 - s0))) so downstream LIA
    // simplification can fold it.
    let mut scalar_deltas: Vec<(&String, &i128)> = constant_deltas
        .iter()
        .filter(|(name, _)| init_values.contains_key(*name))
        .collect();
    scalar_deltas.sort_by_key(|(name, _)| name.as_str());

    let mut projection_deltas: Vec<((&String, &i128), i128, i128)> = select_deltas
        .iter()
        .filter_map(|(key, delta)| {
            fact_projections
                .get(key)
                .map(|init| ((&key.0, &key.1), *delta, *init))
        })
        .collect();
    projection_deltas.sort_by(|a, b| a.0.cmp(&b.0));

    for ((arr_name, idx), proj_delta, init_val) in projection_deltas.iter() {
        let arr_sort = match normalized.var_sorts.get(*arr_name) {
            Some(sort) => sort.clone(),
            None => continue,
        };
        let select_pre = ChcExpr::select(
            ChcExpr::var(ChcVar::new((*arr_name).clone(), arr_sort)),
            ChcExpr::int(**idx),
        );
        for (scalar_name, scalar_delta) in &scalar_deltas {
            if **scalar_delta != *proj_delta {
                continue;
            }
            let Some(&scalar_init) = init_values.get(*scalar_name) else {
                continue;
            };
            // i128-lockstep: checked i128 subtraction; skip on overflow.
            let Some(diff) = init_val.checked_sub(scalar_init) else {
                continue;
            };
            let scalar_expr = int_var_expr(scalar_name);
            let rhs = if diff == 0 {
                scalar_expr
            } else {
                ChcExpr::add(scalar_expr, ChcExpr::int(diff)).simplify_constants()
            };
            invariants.push(ChcExpr::eq(select_pre.clone(), rhs));
        }
    }

    invariants
}

/// Classify `(select arr const_idx) = <expanded post-state expr>` into a
/// constant delta relative to the pre-state cell, returning `None` if no
/// constant delta can be inferred.
///
/// Handles:
///   - `select(arr, idx)`                       → delta 0 (preservation)
///   - `(+ (select arr idx) k)` / `(+ k ...)`   → delta +k
///   - `(- (select arr idx) k)`                 → delta -k
fn classify_select_delta(expr: &ChcExpr, arr_name: &str, idx: i128) -> Option<i128> {
    fn is_same_select(e: &ChcExpr, arr_name: &str, idx: i128) -> bool {
        match e {
            ChcExpr::Op(ChcOp::Select, args) if args.len() == 2 => {
                matches!(&*args[0], ChcExpr::Var(v) if v.name == arr_name)
                    && matches!(&*args[1], ChcExpr::Int(i) if *i == idx)
            }
            _ => false,
        }
    }

    if is_same_select(expr, arr_name, idx) {
        return Some(0);
    }
    match expr {
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
            (sel, ChcExpr::Int(k)) if is_same_select(sel, arr_name, idx) => Some(*k),
            (ChcExpr::Int(k), sel) if is_same_select(sel, arr_name, idx) => Some(*k),
            _ => None,
        },
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
            (sel, ChcExpr::Int(k)) if is_same_select(sel, arr_name, idx) => (*k).checked_neg(),
            _ => None,
        },
        _ => None,
    }
}
