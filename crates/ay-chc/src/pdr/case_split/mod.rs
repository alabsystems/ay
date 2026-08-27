// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Case-splitting preprocessing for unconstrained constant arguments.

mod candidates;

use crate::cancellation::{CancellationGuard, CancellationToken};
use crate::{ChcExpr, ChcOp, ChcProblem, ChcVar, PredicateId};
use ay_core::time::Instant;
use std::time::Duration;

use super::frame::PdrResult;
use super::model::{InvariantModel, PredicateInterpretation};
use super::solver::PdrSolver;
use super::PdrConfig;

const DEFAULT_BRANCH_BUDGET: Duration = Duration::from_secs(4);
const FUTURE_BRANCH_RESERVE: Duration = Duration::from_secs(2);
const MERGE_VERIFY_RESERVE: Duration = Duration::from_millis(500);
/// Wall cap for the whole minimize-before-validate pass (#4751 modelmin).
const MODEL_MIN_BUDGET: Duration = Duration::from_millis(500);
/// Per-probe SMT timeout inside model minimization.
const MODEL_MIN_CHECK_TIMEOUT: Duration = Duration::from_millis(100);

/// A case constraint for case-splitting on constant arguments.
///
/// Case constraints partition the state space based on equality/disequality
/// conditions on an unconstrained constant argument. For example, if a mode
/// argument is compared only against `1` in the transition, the cases are:
/// - `mode = 1` (equality case)
/// - `mode ≠ 1` (other case, ensures exhaustive partition)
#[derive(Debug, Clone, PartialEq, Eq)]
struct CaseConstraint {
    /// Human-readable name for logging (e.g., "mode = 1" or "mode ∉ {1, 2}")
    name: String,
    kind: CaseConstraintKind,
}

#[derive(Debug, Clone, PartialEq, Eq)]
enum CaseConstraintKind {
    Eq(i128),
    NeAll(Vec<i128>),
}

impl CaseConstraint {
    /// Create an equality case: `var = value`
    fn eq(var_name: &str, value: i128) -> Self {
        Self {
            name: format!("{var_name} = {value}"),
            kind: CaseConstraintKind::Eq(value),
        }
    }

    /// Create a disequality for all given values: `var ≠ v1 ∧ var ≠ v2 ∧ ...`
    fn ne_all(var_name: &str, values: &[i128]) -> Self {
        let mut values: Vec<i128> = values.to_vec();
        values.sort_unstable();
        values.dedup();

        Self {
            name: format!(
                "{} ∉ {{{}}}",
                var_name,
                values
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
                    .join(", ")
            ),
            kind: CaseConstraintKind::NeAll(values),
        }
    }

    fn constraint_for_var(&self, var: ChcVar) -> ChcExpr {
        match &self.kind {
            CaseConstraintKind::Eq(value) => ChcExpr::eq(ChcExpr::var(var), ChcExpr::int(*value)),
            CaseConstraintKind::NeAll(values) => ChcExpr::and_vec(
                values
                    .iter()
                    .map(|v| ChcExpr::not(ChcExpr::eq(ChcExpr::var(var.clone()), ChcExpr::int(*v))))
                    .collect(),
            ),
        }
    }
}

impl PdrSolver {
    /// Attempt to solve via case-split on unconstrained constant arguments.
    ///
    /// Returns Some(result) if case-split was applied and yielded a definitive result,
    /// None if case-split doesn't apply or all cases returned Unknown.
    ///
    /// # When to use directly
    ///
    /// This function is called automatically by `solve_problem()`. Call it directly only
    /// when you need case-split as a standalone preprocessing step with dedicated limits
    /// (e.g., at the adaptive layer before portfolio with higher iteration budget).
    ///
    /// Reference: #1306 - Constant-argument case-splitting for dillig-style benchmarks.
    pub(crate) fn try_case_split_solve(
        problem: &ChcProblem,
        config: PdrConfig,
    ) -> Option<PdrResult> {
        // Find candidates: predicates with constant arguments that are unconstrained at init
        let candidates = Self::find_case_split_candidates(problem, config.verbose);

        if candidates.is_empty() {
            return None;
        }

        // Take the first candidate - typically there's at most one
        let (pred_id, arg_idx, var_name, cases) = &candidates[0];

        if config.verbose {
            let case_names: Vec<&str> = cases.iter().map(|c| c.name.as_str()).collect();
            safe_eprintln!(
                "PDR: Attempting case-split on pred {} arg {} ({}) with cases {:?}",
                pred_id.index(),
                arg_idx,
                var_name,
                case_names
            );
        }

        // Wall-clock deadline for the entire case-split attempt.
        // This ensures case-split cannot consume more than its allocated budget,
        // even if individual branches take longer than expected.
        let case_split_deadline = config.solve_timeout.map(|t| Instant::now() + t);

        // Solve for each case
        let mut safe_models: Vec<(CaseConstraint, InvariantModel)> = Vec::new();
        let mut had_unknown = false;

        for (case_index, case) in cases.iter().enumerate() {
            // Check wall-clock deadline before starting each branch
            if Self::case_split_deadline_expired(case_split_deadline) {
                if config.verbose {
                    safe_eprintln!("PDR: Case-split: wall-clock deadline expired, returning None");
                }
                return None;
            }
            let constrained_problem =
                Self::add_init_constraint_expr(problem, *pred_id, *arg_idx, case);

            if config.verbose {
                safe_eprintln!("PDR: Case-split: solving with {}", case.name);
            }

            let mut sub_config = config.clone();
            sub_config.verbose = config.verbose;
            // Case-split is a preprocessing optimization. Keep every branch
            // bounded, but make the allocation work-conserving within the
            // unchanged stage deadline: reserve two seconds for every sibling
            // still to run and 500ms for merged-model strict verification,
            // then let the current branch use the remaining slack. This avoids
            // discarding stage budget when a hard explicit-value case needs a
            // final certificate recheck and the complement case is cheap
            // (dillig12_m E=1 / E!=1).
            let remaining = case_split_deadline
                .map(|d| d.saturating_duration_since(ay_core::time::Instant::now()));
            let future_branches = cases.len().saturating_sub(case_index + 1);
            let branch_budget = Self::case_split_branch_budget(remaining, future_branches);
            if config.verbose {
                safe_eprintln!(
                    "PDR: Case-split: branch budget {:.3}s ({} future case(s), stage remaining {:.3}s)",
                    branch_budget.as_secs_f64(),
                    future_branches,
                    remaining.unwrap_or(branch_budget).as_secs_f64()
                );
            }
            sub_config.solve_timeout = Some(branch_budget);
            // Entry-CEGAR discharge, ON for every branch (#4751).
            //
            // `multi_pred_pdr_config` turns it off, and the parent config we
            // just cloned inherits that. Its reason is budget: the discharge
            // loop can burn an UNBOUNDED portfolio share re-rejecting the same
            // near-inductive lemmas. That reason does not apply here — the two
            // lines above give this branch a hard `solve_timeout` and a
            // cancellation guard, which is the same bounded-stage argument that
            // already justifies re-enabling it for the non-inlined stage.
            //
            // Without it a branch cannot admit any lemma whose entry check needs
            // a SAT model discharged, and on a case split that is precisely the
            // interesting kind. `dillig12_m_000`'s `E = 1` branch fails on
            // `SAD`'s `__p0_a0 <= 2`: it holds only because `FUN` pins
            // `D = 2*C`, so the `FUN -> SAD` entry check produces a model to
            // discharge, reports `entry_cegar_disabled`, and the bound never
            // reaches the model — leaving the query with `B <= A + 2` but not
            // the `A <= 2` that contradicts `B >= 5`. The branch then returns
            // Unknown and sinks the whole case split.
            sub_config.use_entry_cegar_discharge = true;
            let _branch_cancel_guard =
                Self::install_case_split_branch_cancellation(&mut sub_config, branch_budget);

            let mut solver = Self::new(constrained_problem, sub_config);
            let result = solver.solve();

            if config.verbose {
                safe_eprintln!(
                    "PDR: Case-split: {} -> {:?}",
                    case.name,
                    match &result {
                        PdrResult::Safe(_) => "Safe",
                        PdrResult::Unsafe(_) => "Unsafe",
                        PdrResult::Unknown | PdrResult::NotApplicable => "Unknown",
                    }
                );
            }

            match result {
                PdrResult::Safe(model) => {
                    safe_models.push((case.clone(), model));
                }
                PdrResult::Unsafe(cex) => {
                    // Early termination: any Unsafe case means the whole problem is Unsafe
                    if config.verbose {
                        safe_eprintln!(
                            "PDR: Case-split: early termination - {} is Unsafe",
                            case.name
                        );
                    }
                    return Some(PdrResult::Unsafe(cex));
                }
                PdrResult::Unknown | PdrResult::NotApplicable => {
                    had_unknown = true;
                    if Self::case_split_deadline_expired(case_split_deadline) {
                        if config.verbose {
                            safe_eprintln!(
                                "PDR: Case-split: branch exhausted wall-clock deadline, returning None"
                            );
                        }
                        return None;
                    }
                }
            }
        }

        if had_unknown || safe_models.is_empty() {
            // Some cases Unknown - don't claim a result
            if config.verbose {
                safe_eprintln!("PDR: Case-split: Some cases Unknown, returning None");
            }
            return None;
        }

        // All cases returned Safe - merge models and verify on the original problem.
        if Self::case_split_deadline_expired(case_split_deadline) {
            if config.verbose {
                safe_eprintln!(
                    "PDR: Case-split: deadline expired before merge/verify, returning None"
                );
            }
            return None;
        }
        if config.verbose {
            safe_eprintln!(
                "PDR: Case-split: All {} cases safe, attempting merge + verify",
                safe_models.len()
            );
        }

        let merged = Self::merge_case_split_safe_models(&safe_models, *pred_id, *arg_idx);
        if Self::case_split_deadline_expired(case_split_deadline) {
            if config.verbose {
                safe_eprintln!(
                    "PDR: Case-split: deadline expired before strict verification, returning None"
                );
            }
            return None;
        }
        // Minimize-before-validate (#4751 modelmin): the merged model carries
        // every frame lemma from every branch (dillig12_m at HEAD: ~141 lemmas
        // per branch), and strict re-validation cost scales badly with model
        // size. Shrink the model to a small subset of conjuncts that still
        // blocks every error obligation and is still preserved by the
        // self-loop transitions, then validate the SMALL candidate first.
        //
        // SOUNDNESS: purely a candidate transformation. The minimized model is
        // strictly weaker (a subset of conjuncts), and it passes through the
        // SAME mandatory strict `verify_model_fresh` gate below — if the
        // weaker model verifies against ALL clauses (init, transition, query)
        // it is a correct safety proof; if it does not, we fall through and
        // validate the full merged model exactly as before. No acceptance
        // path is weakened and validation still fails closed.
        //
        // BOUNDED: `MODEL_MIN_BUDGET` wall cap over the whole pass and every
        // SMT probe timeout-bounded, so minimization cannot become its own
        // blow-up.
        if let Some(minimized) =
            Self::minimize_case_split_model(problem, &config, &merged, case_split_deadline)
        {
            if !Self::case_split_deadline_expired(case_split_deadline) {
                let mut verifier =
                    Self::case_split_strict_verifier(problem, &config, case_split_deadline);
                let minimized_verify_start = Instant::now();
                if verifier.verify_model_fresh(&minimized) {
                    if config.verbose {
                        safe_eprintln!(
                            "PDR: Case-split: minimized model verified in {:.3}s, returning Safe",
                            minimized_verify_start.elapsed().as_secs_f64()
                        );
                    }
                    return Some(PdrResult::Safe(minimized));
                }
                if config.verbose {
                    safe_eprintln!(
                        "PDR: Case-split: minimized model failed strict validation in {:.3}s, \
                         falling back to full merged model",
                        minimized_verify_start.elapsed().as_secs_f64()
                    );
                }
            }
        }

        let mut verifier = Self::case_split_strict_verifier(problem, &config, case_split_deadline);
        let merged_verify_start = Instant::now();
        if verifier.verify_model_fresh(&merged) {
            if config.verbose {
                safe_eprintln!(
                    "PDR: Case-split: merged model verified in {:.3}s, returning Safe",
                    merged_verify_start.elapsed().as_secs_f64()
                );
            }
            return Some(PdrResult::Safe(merged));
        }

        // #9227: If the merged model cannot be strictly re-validated against the
        // original problem, do not mark it Safe with a trust flag. Let callers
        // continue with the normal portfolio fallback instead.
        if config.verbose {
            safe_eprintln!(
                "PDR: Case-split: merged model failed strict validation in {:.3}s, returning None (#9227)",
                merged_verify_start.elapsed().as_secs_f64()
            );
        }
        None
    }

    fn case_split_deadline_expired(deadline: Option<Instant>) -> bool {
        deadline.is_some_and(|d| Instant::now() >= d)
    }

    fn case_split_branch_budget(remaining: Option<Duration>, future_branches: usize) -> Duration {
        let Some(remaining) = remaining else {
            return DEFAULT_BRANCH_BUDGET;
        };

        let future_count = u32::try_from(future_branches).unwrap_or(u32::MAX);
        let reserve = FUTURE_BRANCH_RESERVE
            .saturating_mul(future_count)
            .saturating_add(MERGE_VERIFY_RESERVE);
        if let Some(slack) = remaining.checked_sub(reserve) {
            if !slack.is_zero() {
                return slack;
            }
        }

        // If the advertised reserves no longer fit, split the remaining
        // envelope fairly. The enclosing stage deadline is still authoritative.
        let branch_count = u32::try_from(future_branches.saturating_add(1)).unwrap_or(u32::MAX);
        remaining / branch_count.max(1)
    }

    fn install_case_split_branch_cancellation(
        config: &mut PdrConfig,
        branch_budget: Duration,
    ) -> Option<CancellationGuard> {
        if config.cancellation_token.is_some() {
            return None;
        }

        let branch_cancellation = CancellationToken::new();
        let guard = branch_cancellation.cancel_after(branch_budget);
        config.cancellation_token = Some(branch_cancellation);
        Some(guard)
    }

    fn case_split_strict_verifier(
        problem: &ChcProblem,
        config: &PdrConfig,
        case_split_deadline: Option<Instant>,
    ) -> Self {
        let mut verifier_config = config.clone();
        verifier_config.strict_proofs = true;
        verifier_config.disable_array_scalarization = true;
        let mut verifier = Self::new(problem.clone(), verifier_config);
        verifier.solve_deadline = case_split_deadline;
        verifier
    }

    /// Try to shrink the merged case-split model before strict validation.
    /// Returns `None` when no shrink was found within budget — the caller
    /// then validates the full merged model unchanged. See the call site for
    /// the soundness argument: the result is only ever a CANDIDATE for the
    /// same mandatory strict validation.
    ///
    /// Per predicate, two stages driven by cheap timeout-bounded probes:
    /// - Stage 1 (shrink): ddmin-style deletion keeps only the conjuncts
    ///   needed to keep every BLOCKING obligation UNSAT. Obligations are the
    ///   predicate's query clauses (`interp ∧ c`), plus — for predicates that
    ///   never appear in a query — unary implication clauses into an
    ///   already-minimized head (`interp ∧ c ∧ ¬head-interp`), which is
    ///   exactly the obligation final validation checks for that clause.
    ///   This reaches "fat" predicates with no query of their own
    ///   (dillig12_m: the query is on SAD, the ~280-conjunct interpretation
    ///   belongs to FUN). Blocking is monotone (a superset of a blocking
    ///   subset still blocks), so chunked deletion is sound.
    /// - Stage 2 (regrow): a blocking-minimal subset is usually NOT
    ///   inductive. For every self-loop clause of the predicate, per-lemma
    ///   preservation (`cand ∧ T ∧ ¬lemma'` — only ONE negated lemma per
    ///   probe, so probes stay cheap regardless of model size) is restored
    ///   by adding back dropped conjuncts, minimized the same chunked way
    ///   (monotone: more premises only make preservation easier). If
    ///   preservation cannot be restored within budget the predicate keeps
    ///   its full merged interpretation.
    fn minimize_case_split_model(
        problem: &ChcProblem,
        config: &PdrConfig,
        merged: &InvariantModel,
        case_split_deadline: Option<Instant>,
    ) -> Option<InvariantModel> {
        use crate::smt::SmtContext;

        let start = Instant::now();
        let mut budget = MODEL_MIN_BUDGET;
        if let Some(d) = case_split_deadline {
            budget = budget.min(d.saturating_duration_since(start));
        }
        if budget.is_zero() {
            return None;
        }
        let deadline = start + budget;
        let mut smt = SmtContext::new();

        // Predicates already processed, with their (possibly shrunk)
        // formulas: (pred, formula, kept_count, total_count).
        let mut final_formulas: Vec<(PredicateId, ChcExpr, usize, usize)> = Vec::new();
        let mut processed: Vec<PredicateId> = Vec::new();

        // Pass 0 minimizes query-adjacent predicates; pass k > 0 propagates
        // backwards through unary implication clauses whose head predicate
        // was processed in an earlier pass.
        const MAX_PASSES: usize = 4;
        for pass in 0..MAX_PASSES {
            if Instant::now() >= deadline {
                break;
            }
            struct Pending {
                pred: PredicateId,
                obligations: Vec<(Vec<(ChcVar, ChcExpr)>, ChcExpr)>,
            }
            let mut pending: Vec<Pending> = Vec::new();
            for clause in problem.clauses() {
                let (target, target_args, error) = if clause.is_query() {
                    if pass != 0 {
                        continue;
                    }
                    if clause.body.predicates.len() != 1 {
                        // Hyper-queries not handled; refuse to minimize.
                        return None;
                    }
                    let (p, args) = &clause.body.predicates[0];
                    (
                        *p,
                        args,
                        clause
                            .body
                            .constraint
                            .clone()
                            .unwrap_or(ChcExpr::Bool(true)),
                    )
                } else {
                    if pass == 0 {
                        continue;
                    }
                    let crate::ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
                        continue;
                    };
                    if clause.body.predicates.len() != 1 {
                        continue;
                    }
                    let (p, args) = &clause.body.predicates[0];
                    if p == head_pred || !processed.contains(head_pred) {
                        continue;
                    }
                    let Some((_, head_formula, _, _)) =
                        final_formulas.iter().find(|(fp, ..)| fp == head_pred)
                    else {
                        continue;
                    };
                    let Some(head_interp) = merged.get(head_pred) else {
                        continue;
                    };
                    if head_interp.vars.len() != head_args.len() {
                        continue;
                    }
                    let head_map: Vec<(ChcVar, ChcExpr)> = head_interp
                        .vars
                        .iter()
                        .cloned()
                        .zip(head_args.iter().cloned())
                        .collect();
                    let head_sub = head_formula.substitute(&head_map);
                    let constraint = clause
                        .body
                        .constraint
                        .clone()
                        .unwrap_or(ChcExpr::Bool(true));
                    (*p, args, ChcExpr::and(constraint, ChcExpr::not(head_sub)))
                };
                if processed.contains(&target) {
                    continue;
                }
                let is_query = clause.is_query();
                let Some(interp) = merged.get(&target) else {
                    if is_query {
                        // A query predicate without an interpretation cannot
                        // be minimized against; validation will reject the
                        // model anyway.
                        return None;
                    }
                    continue;
                };
                if interp.vars.len() != target_args.len() {
                    if is_query {
                        return None;
                    }
                    continue;
                }
                let var_map: Vec<(ChcVar, ChcExpr)> = interp
                    .vars
                    .iter()
                    .cloned()
                    .zip(target_args.iter().cloned())
                    .collect();
                match pending.iter_mut().find(|e| e.pred == target) {
                    Some(entry) => entry.obligations.push((var_map, error)),
                    None => pending.push(Pending {
                        pred: target,
                        obligations: vec![(var_map, error)],
                    }),
                }
            }
            if pending.is_empty() {
                break;
            }
            for p in &pending {
                processed.push(p.pred);
            }
            for p in pending {
                if Instant::now() >= deadline {
                    break;
                }
                let Some(interp) = merged.get(&p.pred) else {
                    continue;
                };
                let conjuncts = Self::flatten_guarded_conjuncts(&interp.formula);
                let total = conjuncts.len();
                if total <= 1 {
                    final_formulas.push((p.pred, interp.formula.clone(), total, total));
                    continue;
                }
                let self_loops = Self::collect_self_loops(problem, p.pred, &interp.vars);
                let kept = Self::minimize_pred_conjuncts(
                    &mut smt,
                    &conjuncts,
                    &p.obligations,
                    &self_loops,
                    deadline,
                );
                let (formula, kept_len) = match &kept {
                    Some(indices) if indices.len() < total => (
                        ChcExpr::and_vec(indices.iter().map(|&i| conjuncts[i].clone()).collect()),
                        indices.len(),
                    ),
                    _ => (interp.formula.clone(), total),
                };
                if config.verbose {
                    safe_eprintln!(
                        "PDR: Case-split: minimize pred {}: {} -> {} conjuncts",
                        p.pred.index(),
                        total,
                        kept_len
                    );
                }
                final_formulas.push((p.pred, formula, kept_len, total));
            }
        }

        // Build the minimized model from the shrunk predicates.
        let mut minimized = merged.clone();
        let mut dropped_total = 0usize;
        let mut kept_total = 0usize;
        for (pred, formula, kept_len, total) in &final_formulas {
            if kept_len >= total {
                continue;
            }
            let interp = merged.get(pred)?;
            dropped_total += total - kept_len;
            kept_total += kept_len;
            minimized.set(
                *pred,
                PredicateInterpretation::new(interp.vars.clone(), formula.clone()),
            );
        }
        if dropped_total == 0 {
            return None;
        }
        if config.verbose {
            safe_eprintln!(
                "PDR: Case-split: model minimization kept {} / dropped {} conjuncts in {:.3}s",
                kept_total,
                dropped_total,
                start.elapsed().as_secs_f64()
            );
        }
        Some(minimized)
    }

    /// Pre/post substitution maps and transition guard for every self-loop
    /// clause of `pred` (single body predicate equal to the head predicate).
    #[allow(clippy::type_complexity)]
    fn collect_self_loops(
        problem: &ChcProblem,
        pred: PredicateId,
        vars: &[ChcVar],
    ) -> Vec<(Vec<(ChcVar, ChcExpr)>, Vec<(ChcVar, ChcExpr)>, ChcExpr)> {
        let mut out = Vec::new();
        for clause in problem.clauses() {
            let crate::ClauseHead::Predicate(head_pred, head_args) = &clause.head else {
                continue;
            };
            if *head_pred != pred
                || clause.body.predicates.len() != 1
                || clause.body.predicates[0].0 != pred
            {
                continue;
            }
            let body_args = &clause.body.predicates[0].1;
            if vars.len() != head_args.len() || vars.len() != body_args.len() {
                continue;
            }
            let pre_map: Vec<(ChcVar, ChcExpr)> = vars
                .iter()
                .cloned()
                .zip(body_args.iter().cloned())
                .collect();
            let post_map: Vec<(ChcVar, ChcExpr)> = vars
                .iter()
                .cloned()
                .zip(head_args.iter().cloned())
                .collect();
            let guard = clause
                .body
                .constraint
                .clone()
                .unwrap_or(ChcExpr::Bool(true));
            out.push((pre_map, post_map, guard));
        }
        out
    }

    /// Two-stage conjunct minimization for one predicate. Returns the kept
    /// index set (sorted), or `None` when minimization failed (deadline,
    /// undecidable probes, or preservation could not be restored) — the
    /// caller keeps the full interpretation in that case.
    #[allow(clippy::type_complexity)]
    fn minimize_pred_conjuncts(
        smt: &mut crate::smt::SmtContext,
        conjuncts: &[ChcExpr],
        obligations: &[(Vec<(ChcVar, ChcExpr)>, ChcExpr)],
        self_loops: &[(Vec<(ChcVar, ChcExpr)>, Vec<(ChcVar, ChcExpr)>, ChcExpr)],
        deadline: Instant,
    ) -> Option<Vec<usize>> {
        // Stage 1: chunked deletion under the (monotone) blocking probes.
        let mut kept: Vec<usize> = (0..conjuncts.len()).collect();
        let mut chunk = kept.len().div_ceil(2);
        loop {
            let mut i = 0;
            while i < kept.len() && kept.len() > 1 {
                if Instant::now() >= deadline {
                    return None;
                }
                let end = (i + chunk).min(kept.len());
                let candidate: Vec<usize> = kept[..i]
                    .iter()
                    .chain(kept[end..].iter())
                    .copied()
                    .collect();
                if !candidate.is_empty()
                    && Self::conjuncts_block_obligations(
                        smt,
                        conjuncts,
                        &candidate,
                        obligations,
                        deadline,
                    )
                {
                    kept = candidate;
                    // Do not advance `i`: the next chunk slid into place.
                } else {
                    i = end;
                }
            }
            if chunk == 1 {
                break;
            }
            chunk = (chunk / 2).max(1);
        }
        if kept.len() >= conjuncts.len() {
            return None;
        }

        // Stage 2: restore per-lemma preservation on every self-loop clause.
        const MAX_REGROW_ROUNDS: usize = 32;
        let mut rounds = 0;
        'outer: loop {
            rounds += 1;
            if rounds > MAX_REGROW_ROUNDS || Instant::now() >= deadline {
                return None;
            }
            for probe_idx in 0..kept.len() {
                let lemma = kept[probe_idx];
                for (pre_map, post_map, guard) in self_loops {
                    if Instant::now() >= deadline {
                        return None;
                    }
                    if Self::lemma_preserved(
                        smt, conjuncts, &kept, lemma, pre_map, post_map, guard, deadline,
                    ) {
                        continue;
                    }
                    // Preservation of `lemma` fails from `kept` alone: add
                    // back dropped conjuncts until it holds, then minimize
                    // the additions (monotone acceptance).
                    let dropped: Vec<usize> =
                        (0..conjuncts.len()).filter(|i| !kept.contains(i)).collect();
                    let full: Vec<usize> = kept.iter().chain(dropped.iter()).copied().collect();
                    if !Self::lemma_preserved(
                        smt, conjuncts, &full, lemma, pre_map, post_map, guard, deadline,
                    ) {
                        // Even the full merged premise cannot show
                        // preservation within the probe budget; give up on
                        // this predicate.
                        return None;
                    }
                    let mut add = dropped;
                    let mut chunk = add.len().div_ceil(2).max(1);
                    loop {
                        let mut i = 0;
                        while i < add.len() {
                            if Instant::now() >= deadline {
                                return None;
                            }
                            let end = (i + chunk).min(add.len());
                            let candidate_add: Vec<usize> =
                                add[..i].iter().chain(add[end..].iter()).copied().collect();
                            let premise: Vec<usize> =
                                kept.iter().chain(candidate_add.iter()).copied().collect();
                            if Self::lemma_preserved(
                                smt, conjuncts, &premise, lemma, pre_map, post_map, guard, deadline,
                            ) {
                                add = candidate_add;
                            } else {
                                i = end;
                            }
                        }
                        if chunk == 1 {
                            break;
                        }
                        chunk = (chunk / 2).max(1);
                    }
                    if add.is_empty() {
                        // `kept` alone failed a moment ago but now passes:
                        // probe flakiness; give up rather than loop.
                        return None;
                    }
                    kept.extend(add);
                    kept.sort_unstable();
                    if kept.len() >= conjuncts.len() {
                        return None;
                    }
                    continue 'outer;
                }
            }
            // Every kept lemma is preserved on every self-loop clause.
            break;
        }
        Some(kept)
    }

    /// True when `subset` of `conjuncts` keeps every blocking obligation
    /// UNSAT.
    fn conjuncts_block_obligations(
        smt: &mut crate::smt::SmtContext,
        conjuncts: &[ChcExpr],
        subset: &[usize],
        obligations: &[(Vec<(ChcVar, ChcExpr)>, ChcExpr)],
        deadline: Instant,
    ) -> bool {
        obligations.iter().all(|(var_map, error)| {
            let mut parts: Vec<ChcExpr> = subset
                .iter()
                .map(|&i| conjuncts[i].substitute(var_map))
                .collect();
            parts.push(error.clone());
            Self::model_min_probe_unsat(smt, ChcExpr::and_vec(parts), deadline)
        })
    }

    /// True when `premise ∧ guard ∧ ¬lemma'` is UNSAT — i.e. the premise
    /// subset preserves `lemma` across one self-loop step. Only one negated
    /// conjunct per probe, so the query stays cheap at any model size.
    #[allow(clippy::too_many_arguments)]
    fn lemma_preserved(
        smt: &mut crate::smt::SmtContext,
        conjuncts: &[ChcExpr],
        premise: &[usize],
        lemma: usize,
        pre_map: &[(ChcVar, ChcExpr)],
        post_map: &[(ChcVar, ChcExpr)],
        guard: &ChcExpr,
        deadline: Instant,
    ) -> bool {
        let mut parts: Vec<ChcExpr> = premise
            .iter()
            .map(|&i| conjuncts[i].substitute(pre_map))
            .collect();
        parts.push(guard.clone());
        parts.push(ChcExpr::not(conjuncts[lemma].substitute(post_map)));
        Self::model_min_probe_unsat(smt, ChcExpr::and_vec(parts), deadline)
    }

    /// One timeout-bounded UNSAT probe (equality propagation + bounded ITE
    /// case-split, mirroring `try_verification_case_split`). `false` on
    /// SAT/Unknown/deadline — callers treat that as "cannot accept".
    fn model_min_probe_unsat(
        smt: &mut crate::smt::SmtContext,
        query: ChcExpr,
        deadline: Instant,
    ) -> bool {
        use crate::smt::SmtResult;
        let now = Instant::now();
        if now >= deadline {
            return false;
        }
        let per_check = MODEL_MIN_CHECK_TIMEOUT.min(deadline.saturating_duration_since(now));
        let simplified = query.propagate_equalities();
        if matches!(simplified, ChcExpr::Bool(false)) {
            return true;
        }
        smt.reset();
        let _probe_deadline = crate::smt::ScopedSmtDeadline::install(per_check);
        let _timeout = smt.scoped_check_timeout(Some(per_check));
        let (result, _) = Self::check_sat_with_ite_case_split(smt, false, &simplified);
        matches!(
            result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
        )
    }

    /// Flatten a formula into semantically-equivalent top-level conjuncts,
    /// distributing guarded conjunctions: `g => (a ∧ b)` yields `g => a` and
    /// `g => b`. This exposes the per-lemma structure of merged case-split
    /// models (the owner predicate is `AND_c (guard_c => frame_lemmas_c)`) so
    /// individual lemmas can be dropped.
    fn flatten_guarded_conjuncts(formula: &ChcExpr) -> Vec<ChcExpr> {
        let mut out = Vec::new();
        for conjunct in formula.conjuncts() {
            match conjunct {
                ChcExpr::Op(ChcOp::Implies, args) if args.len() == 2 => {
                    let body_conjuncts = args[1].conjuncts();
                    if body_conjuncts.len() > 1 {
                        for b in body_conjuncts {
                            out.push(ChcExpr::implies(args[0].as_ref().clone(), b.clone()));
                        }
                    } else {
                        out.push(conjunct.clone());
                    }
                }
                _ => out.push(conjunct.clone()),
            }
        }
        out
    }

    fn merge_case_split_safe_models(
        safe_models: &[(CaseConstraint, InvariantModel)],
        split_pred_id: PredicateId,
        split_arg_idx: usize,
    ) -> InvariantModel {
        debug_assert!(!safe_models.is_empty(), "merge requires at least one model");

        let first_model = &safe_models[0].1;
        let mut pred_ids: Vec<PredicateId> = first_model.iter().map(|(id, _)| *id).collect();
        pred_ids.sort_by_key(|p| p.index());

        let mut merged = InvariantModel::new();
        for pred_id in pred_ids {
            let first_interp = first_model
                .get(&pred_id)
                .expect("InvariantModel::iter must match get()");
            let vars = first_interp.vars.clone();

            let mut case_interps: Vec<(&CaseConstraint, &PredicateInterpretation)> = Vec::new();
            for (case, model) in safe_models {
                let interp = model
                    .get(&pred_id)
                    .expect("case-split model missing predicate interpretation");
                debug_assert_eq!(
                    interp.vars, vars,
                    "case-split models disagree on predicate vars"
                );
                case_interps.push((case, interp));
            }

            // Only the predicate selected for case splitting carries the
            // discriminator at `split_arg_idx`. An unrelated predicate may
            // happen to have an argument at the same numeric position, but
            // that argument has no semantic connection to the split. Guarding
            // its interpretations with that value rejects reachable states.
            // Merge every non-owner predicate by branch union instead. (#1306)
            let formula = if pred_id == split_pred_id {
                debug_assert!(
                    vars.len() > split_arg_idx,
                    "case-split argument index is out of range for its predicate"
                );
                let mode_var = vars[split_arg_idx].clone();
                ChcExpr::and_vec(
                    case_interps
                        .iter()
                        .map(|(case, interp)| {
                            let guard = case.constraint_for_var(mode_var.clone());
                            ChcExpr::implies(guard, interp.formula.clone())
                        })
                        .collect(),
                )
            } else {
                ChcExpr::or_vec(
                    case_interps
                        .iter()
                        .map(|(_, interp)| interp.formula.clone())
                        .collect(),
                )
            };

            merged.set(pred_id, PredicateInterpretation::new(vars, formula));
        }

        merged
    }

    /// Create a new problem with an additional constraint expression on init.
    ///
    /// The constraint expression should be over the variable at arg_idx in the fact clause.
    /// Accepts arbitrary ChcExpr (e.g., disequalities or conjunctions for the "other" case).
    fn add_init_constraint_expr(
        problem: &ChcProblem,
        pred_id: PredicateId,
        arg_idx: usize,
        case: &CaseConstraint,
    ) -> ChcProblem {
        let mut new_problem = problem.clone();

        for clause in new_problem.clauses_mut() {
            if clause.head.predicate_id() != Some(pred_id) {
                continue;
            }

            if clause.is_fact() {
                // Fact clause: guard on the head variable at arg_idx.
                let var = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => {
                        if arg_idx >= args.len() {
                            continue;
                        }
                        match &args[arg_idx] {
                            ChcExpr::Var(v) => v.clone(),
                            _ => continue,
                        }
                    }
                    crate::ClauseHead::False => continue,
                };

                let case_constraint = case.constraint_for_var(var);
                let combined = match &clause.body.constraint {
                    Some(existing) => ChcExpr::and(existing.clone(), case_constraint),
                    None => case_constraint,
                };
                clause.body.constraint = Some(combined);
            } else if clause.body.predicates.len() == 1 && clause.body.predicates[0].0 == pred_id {
                // D13 (#1306): Self-loop clause — thread the case guard into the
                // transition constraint. The arg is constant (head == body), so
                // the guard on the body-side variable is equivalent. This makes
                // preservation queries (e.g., is_scaled_diff_preserved) branch-aware.
                let body_args = &clause.body.predicates[0].1;
                if arg_idx >= body_args.len() {
                    continue;
                }
                let var = match &body_args[arg_idx] {
                    ChcExpr::Var(v) => v.clone(),
                    _ => continue,
                };

                let case_constraint = case.constraint_for_var(var);
                let combined = match &clause.body.constraint {
                    Some(existing) => ChcExpr::and(existing.clone(), case_constraint),
                    None => case_constraint,
                };
                clause.body.constraint = Some(combined);
            }
        }

        new_problem
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod safe_tests;
