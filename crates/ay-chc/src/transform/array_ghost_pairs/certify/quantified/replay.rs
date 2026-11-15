// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

mod fanout;
mod records;

pub(super) struct Prepared<'a> {
    pub(super) obligation: ChcReplayObligation,
    finite_query: ChcExpr,
    forwarding: bool,
    source: &'a QuantifiedChcProblem,
}

pub(super) fn prepare<'a>(
    problem: &'a QuantifiedChcProblem,
    interpretation: &GhostPairModel,
    index: usize,
    control: &SourceControl<'_>,
    projection: Option<&RecordProjection>,
) -> Option<Prepared<'a>> {
    control.poll()?;
    let original = problem.source_problem().clauses().get(index)?;
    let premises = problem.premises().get(index)?;
    let registry = records::registry(problem, projection, control)?;
    let projected_clause;
    let clause = if let Some(projection) = projection {
        projected_clause = records::project_clause(original, projection, control)?;
        &projected_clause
    } else {
        original
    };
    fanout::precharge(interpretation, clause, control)?;
    let variables = source_premises::clause_variables(original, premises, control)?;
    let mut used: FxHashSet<String> = variables.iter().map(|var| var.name.clone()).collect();
    source_premises::reserve_names(premises, &mut used, control)?;
    if let Some(registry) = &registry {
        for name in registry.term_names() {
            control.bytes(name.len())?;
            if !used.insert(name.to_owned()) {
                return None;
            }
        }
    }
    reserve_function_names(problem, interpretation, clause, &mut used, control)?;
    let (head_negation, fresh_vars) = skolemize_head(interpretation, clause, &mut used)?;
    let fresh: Vec<ChcExpr> = fresh_vars.iter().cloned().map(ChcExpr::var).collect();
    let indices = collect_index_terms(clause, INDEX_TERM_CAP);
    let mut hints = body_instance_conjuncts(interpretation, clause, &fresh, &indices)?;
    let forwarding = has_exact_forwarding_contradiction(&hints, head_negation.as_ref());
    let mut source_indices = fresh;
    source_indices.extend(indices);
    hints.extend(source_premises::instances(
        premises,
        &source_indices,
        control,
    )?);
    let mut conjuncts: Vec<ChcExpr> = clause.body.constraint.iter().cloned().collect();
    conjuncts.extend(hints.iter().cloned());
    conjuncts.extend(head_negation.iter().cloned());
    let finite_query = ChcExpr::and_all_checked(conjuncts, || control.poll().is_none())?;
    source_premises::preflight(&finite_query, control, &mut 0)?;
    control.poll()?;
    let smtlib = if let Some(registry) = &registry {
        records::render(
            problem,
            registry,
            interpretation,
            clause,
            &variables,
            &fresh_vars,
            head_negation.as_ref(),
            &mut used,
            &hints,
            premises,
            control,
        )?
    } else {
        quantified_discharge_smtlib(
            interpretation,
            clause,
            &variables,
            &fresh_vars,
            head_negation.as_ref(),
            &mut used,
            &hints,
            premises,
            Some(control),
        )?
    };
    control.poll()?;
    if smtlib.len() > MAX_REPLAY_BYTES {
        return None;
    }
    let kind = match clause.head {
        ClauseHead::Predicate(..) if clause.body.predicates.is_empty() => {
            crate::ChcReplayObligationKind::Initiation
        }
        ClauseHead::Predicate(..) => crate::ChcReplayObligationKind::Consecution,
        ClauseHead::False => crate::ChcReplayObligationKind::Safety,
    };
    Some(Prepared {
        obligation: ChcReplayObligation {
            name: format!("source-clause-{index}-{}", kind.as_str()),
            kind,
            clause_index: index,
            smtlib,
        },
        finite_query,
        forwarding,
        source: problem,
    })
}

fn reserve_function_names(
    problem: &QuantifiedChcProblem,
    interpretation: &GhostPairModel,
    clause: &HornClause,
    used: &mut FxHashSet<String>,
    control: &SourceControl<'_>,
) -> Option<()> {
    reserve_global_function_names(interpretation, clause, used)?;
    // Used applications may already have reserved the same symbol. The source
    // constructor authenticates disjoint variable/record/function namespaces.
    for name in crate::quantified::functions::controlled::names(problem, control)? {
        used.insert(name.to_owned());
    }
    control.poll()
}

pub(super) fn discharge(
    prepared: Prepared<'_>,
    remaining_clauses: usize,
    control: &SourceControl<'_>,
) -> bool {
    if control.poll().is_none() {
        return false;
    }
    let remaining = control.deadline.saturating_duration_since(Instant::now());
    // A fair share of the caller's envelope, not the flat lane's five-second
    // ceiling: a projected nested-record fact takes about two seconds of finite
    // solving (see `source_premises::clause_budget`).
    let rule_budget = source_premises::clause_budget(remaining, remaining_clauses);
    let Some(rule_deadline) = Instant::now()
        .checked_add(rule_budget)
        .map(|d| d.min(control.deadline))
    else {
        return false;
    };
    let result = if prepared.source.function_declarations().is_empty() {
        let Some(finite_budget) = bounded_executor_budget(rule_budget, 2) else {
            return false;
        };
        discharge_inner(prepared, rule_deadline, finite_budget, control)
    } else {
        // No forwarding shortcut or independently reconstructed finite UF model
        // has original-source authority. Keep all declared UFs uninterpreted.
        full_source_discharge(prepared, rule_deadline, control)
    };
    result && control.poll().is_some() && Instant::now() < rule_deadline
}

fn discharge_inner(
    prepared: Prepared<'_>,
    rule_deadline: Instant,
    finite_budget: Duration,
    control: &SourceControl<'_>,
) -> bool {
    if control.poll().is_none() {
        return false;
    }
    if prepared.forwarding {
        return true;
    }
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(rule_deadline);
    // The original source registry is needed even for finite instances:
    // selectors/constructors must not become ordinary uninterpreted functions.
    // Registry copies were precharged when preparing this obligation.
    let mut smt = prepared.source.source_problem().make_smt_context();
    if smt.exact_term_memory_exceeded() {
        return false;
    }
    let result =
        smt.check_sat_with_executor_fallback_timeout(&prepared.finite_query, finite_budget);
    if control.poll().is_none()
        || smt.exact_term_memory_exceeded()
        || Instant::now() >= rule_deadline
    {
        return false;
    }
    if matches!(result, SmtResult::Unsat) {
        return true;
    }
    // Inconclusive finite instances have no Unsafe authority. A complete
    // original quantified check may still discharge the same obligation.
    let verdict = crate::smt::executor_adapter::smtlib_first_verdict_via_executor_with_limit(
        &prepared.obligation.smtlib,
        crate::smt::executor_adapter::ReplayLimit::Cancellable {
            deadline: rule_deadline,
            cancellation: &control.replay_cancellation,
        },
        smt.term_memory_budget,
    );
    verdict.as_deref() == Some("unsat")
        && !smt.exact_term_memory_exceeded()
        && control.poll().is_some()
        && Instant::now() < rule_deadline
}

fn full_source_discharge(
    prepared: Prepared<'_>,
    deadline: Instant,
    control: &SourceControl<'_>,
) -> bool {
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(deadline);
    let context = SmtContext::new();
    if control.poll().is_none() || context.exact_term_memory_exceeded() {
        return false;
    }
    let verdict = crate::smt::executor_adapter::smtlib_first_verdict_via_executor_with_limit(
        &prepared.obligation.smtlib,
        crate::smt::executor_adapter::ReplayLimit::Cancellable {
            deadline,
            cancellation: &control.replay_cancellation,
        },
        context.term_memory_budget,
    );
    verdict.as_deref() == Some("unsat")
        && !context.exact_term_memory_exceeded()
        && control.poll().is_some()
        && Instant::now() < deadline
}
