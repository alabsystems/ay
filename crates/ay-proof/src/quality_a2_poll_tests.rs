// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::kani_compat::DetHashMap;

#[test]
fn cost_memo_fill_polls_cancellation_without_extra_debit() {
    let mut terms = TermStore::new();
    let mut root = terms.mk_var("memo_poll_root", Sort::Bool);
    for _ in 0..TERM_COST_MEMO_POLL_INTERVAL {
        root = terms.mk_app(Symbol::Named("memo_poll_f".to_string()), [root], Sort::Bool);
    }

    let mut memo = TermCostMemo::default();
    let mut polls = 0_usize;
    let mut cancel_at_poll = |work: usize, bytes: usize| {
        assert_eq!((work, bytes), (0, 0), "memo polls must not alter debits");
        polls += 1;
        false
    };
    let result = unfolded_work_memoized(&mut memo, &terms, &[root], &mut cancel_at_poll);

    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(polls, 1, "the first bounded memo-fill poll must cancel");
}

#[test]
fn warm_cost_memo_root_scan_still_polls_cancellation() {
    let mut terms = TermStore::new();
    let roots: Vec<_> = (0..TERM_COST_MEMO_POLL_INTERVAL)
        .map(|index| terms.mk_var(format!("memo_poll_{index}"), Sort::Bool))
        .collect();
    let mut memo = TermCostMemo::default();
    let mut unbounded = |_: usize, _: usize| true;
    unfolded_work_memoized(&mut memo, &terms, &roots, &mut unbounded)
        .expect("cold memo fill succeeds");

    let mut polls = 0_usize;
    let mut cancel_at_poll = |work: usize, bytes: usize| {
        assert_eq!((work, bytes), (0, 0), "memo polls must not alter debits");
        polls += 1;
        false
    };
    let result = unfolded_work_memoized(&mut memo, &terms, &roots, &mut cancel_at_poll);

    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(polls, 1, "warm-root scan must remain cancellable");
}

#[test]
fn cold_cost_memo_high_fanout_copy_still_polls_cancellation() {
    let mut terms = TermStore::new();
    let children: Vec<_> = (0..TERM_COST_MEMO_POLL_INTERVAL)
        .map(|index| terms.mk_var(format!("memo_child_{index}"), Sort::Bool))
        .collect();
    let root = terms.mk_app(
        Symbol::Named("memo_high_fanout".to_string()),
        &children,
        Sort::Bool,
    );

    let mut memo = TermCostMemo::default();
    let mut polls = 0_usize;
    let mut cancel_at_poll = |work: usize, bytes: usize| {
        assert_eq!((work, bytes), (0, 0), "memo polls must not alter debits");
        polls += 1;
        false
    };
    let result = unfolded_work_memoized(&mut memo, &terms, &[root], &mut cancel_at_poll);

    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(polls, 1, "high-fanout child copying must be cancellable");
}

// ---------------------------------------------------------------------------
// A2 resource-parity pin (the development design notes).
//
// The three `reference_*` functions below are VERBATIM copies of the
// unmemoized production metering at origin/main e49607360 (pre-A2):
// `meter_reachable_terms`, `unfolded_term_work`, and the body of
// `meter_step_term_payload`. They are the review-mandated acceptance bar: for
// EVERY step, the memoized production metering must produce byte-identical
// `PayloadStats.{work,bytes,unfolded_work}` — not merely equal totals across
// the proof — because those per-step stats feed the pre-charges that bound
// the unmetered semantic validators.
// ---------------------------------------------------------------------------

fn reference_meter_reachable_terms(
    terms: &TermStore,
    mut pending: Vec<TermId>,
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let mut visited = DetHashSet::default();
    while let Some(term) = pending.pop() {
        charge_progress(progress, 1, 0)?;
        if visited.contains(&term) {
            continue;
        }
        charge_progress(progress, 1, checked_add_usize(size_of::<TermId>(), 32)?)?;
        visited.insert(term);

        charge_progress(
            progress,
            1,
            checked_add_usize(size_of::<TermData>(), size_of::<Sort>())?,
        )?;
        meter_sort(terms.sort(term), progress)?;
        match terms.get(term) {
            TermData::Const(constant) => meter_constant(constant, progress)?,
            TermData::Var(name, _) => {
                charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?
            }
            TermData::App(symbol, args) => {
                meter_symbol(symbol, progress)?;
                charge_progress(
                    progress,
                    1,
                    checked_mul_usize(args.capacity(), size_of::<TermId>())?,
                )?;
                push_term_slice(&mut pending, args, progress)?;
            }
            TermData::Let(bindings, body) => {
                charge_progress(
                    progress,
                    bindings.len(),
                    checked_mul_usize(bindings.capacity(), size_of::<(String, TermId)>())?,
                )?;
                for (name, value) in bindings {
                    charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
                    push_term(&mut pending, *value, progress)?;
                }
                push_term(&mut pending, *body, progress)?;
            }
            TermData::Not(inner) => push_term(&mut pending, *inner, progress)?,
            TermData::Ite(condition, then_branch, else_branch) => {
                push_term(&mut pending, *condition, progress)?;
                push_term(&mut pending, *then_branch, progress)?;
                push_term(&mut pending, *else_branch, progress)?;
            }
            TermData::Forall(variables, body, triggers)
            | TermData::Exists(variables, body, triggers) => {
                let variable_bytes =
                    checked_mul_usize(variables.capacity(), size_of::<(String, Sort)>())?;
                let trigger_bytes =
                    checked_mul_usize(triggers.capacity(), size_of::<Vec<TermId>>())?;
                charge_progress(
                    progress,
                    variables.len(),
                    checked_add_usize(variable_bytes, trigger_bytes)?,
                )?;
                for (name, sort) in variables {
                    charge_progress(progress, checked_add_usize(name.len(), 1)?, name.capacity())?;
                    meter_sort(sort, progress)?;
                }
                push_term(&mut pending, *body, progress)?;
                for trigger in triggers {
                    charge_progress(
                        progress,
                        1,
                        checked_mul_usize(trigger.capacity(), size_of::<TermId>())?,
                    )?;
                    push_term_slice(&mut pending, trigger, progress)?;
                }
            }
            _ => charge_progress(progress, 1, 0)?,
        }
    }
    Ok(())
}

fn reference_unfolded_term_work(
    terms: &TermStore,
    roots: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<usize, ProofCheckError> {
    let mut costs: DetHashMap<TermId, usize> = DetHashMap::default();
    let mut active = DetHashSet::default();
    let mut stack: Vec<(TermId, bool)> = Vec::new();

    for &root in roots {
        if costs.contains_key(&root) {
            continue;
        }
        charge_progress(progress, 1, size_of::<(TermId, bool)>())?;
        stack.push((root, false));
        while let Some((term, expanded)) = stack.pop() {
            charge_progress(progress, 1, 0)?;
            if costs.contains_key(&term) {
                continue;
            }
            if expanded {
                active.remove(&term);
                let mut children = Vec::new();
                append_term_children(terms, term, &mut children, progress)?;
                let mut cost = 1_usize;
                for child in children {
                    let child_cost = costs
                        .get(&child)
                        .copied()
                        .ok_or(ProofCheckError::ResourceLimit)?;
                    cost = checked_add_usize(cost, child_cost)?;
                }
                charge_progress(
                    progress,
                    1,
                    checked_add_usize(size_of::<(TermId, usize)>(), 32)?,
                )?;
                costs.insert(term, cost);
                continue;
            }

            charge_progress(progress, 1, checked_add_usize(size_of::<TermId>(), 32)?)?;
            if !active.insert(term) {
                return Err(ProofCheckError::ResourceLimit);
            }
            charge_progress(progress, 1, size_of::<(TermId, bool)>())?;
            stack.push((term, true));
            let mut children = Vec::new();
            append_term_children(terms, term, &mut children, progress)?;
            for child in children.into_iter().rev() {
                if active.contains(&child) {
                    return Err(ProofCheckError::ResourceLimit);
                }
                if !costs.contains_key(&child) {
                    charge_progress(progress, 1, size_of::<(TermId, bool)>())?;
                    stack.push((child, false));
                }
            }
        }
    }

    let mut total = 0_usize;
    for root in roots {
        total = checked_add_usize(
            total,
            costs
                .get(root)
                .copied()
                .ok_or(ProofCheckError::ResourceLimit)?,
        )?;
    }
    Ok(total)
}

fn reference_meter_step_term_payload(
    step: &ProofStep,
    terms: &TermStore,
    derived_clauses: &[Option<Vec<TermId>>],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<PayloadStats, ProofCheckError> {
    let mut stats = PayloadStats::default();
    let mut overflow = false;
    let unfolded_work = {
        let mut counting_progress = |work: usize, bytes: usize| {
            let Some(next_work) = stats.work.checked_add(work) else {
                overflow = true;
                return false;
            };
            let Some(next_bytes) = stats.bytes.checked_add(bytes) else {
                overflow = true;
                return false;
            };
            stats.work = next_work;
            stats.bytes = next_bytes;
            progress(work, bytes)
        };

        let mut roots = Vec::new();
        match step {
            ProofStep::Resolution {
                clause,
                pivot,
                clause1,
                clause2,
            } => {
                push_term_slice(&mut roots, clause, &mut counting_progress)?;
                push_term(&mut roots, *pivot, &mut counting_progress)?;
                for premise in [*clause1, *clause2] {
                    if let Some(Some(premise_clause)) = derived_clauses.get(premise.0 as usize) {
                        push_term_slice(&mut roots, premise_clause, &mut counting_progress)?;
                    }
                }
            }
            ProofStep::TheoryLemma { clause, .. } => {
                push_term_slice(&mut roots, clause, &mut counting_progress)?;
            }
            ProofStep::Step {
                clause,
                premises,
                args,
                ..
            } => {
                push_term_slice(&mut roots, clause, &mut counting_progress)?;
                push_term_slice(&mut roots, args, &mut counting_progress)?;
                for premise in premises {
                    if let Some(Some(premise_clause)) = derived_clauses.get(premise.0 as usize) {
                        push_term_slice(&mut roots, premise_clause, &mut counting_progress)?;
                    }
                }
            }
            _ => {}
        }
        let unfolded_work = reference_unfolded_term_work(terms, &roots, &mut counting_progress)?;
        reference_meter_reachable_terms(terms, roots, &mut counting_progress)?;
        unfolded_work
    };
    if overflow {
        Err(ProofCheckError::ResourceLimit)
    } else {
        stats.unfolded_work = unfolded_work;
        Ok(stats)
    }
}

struct A2ParityFixture {
    terms: TermStore,
    steps: [ProofStep; 4],
    derived: Vec<Option<Vec<TermId>>>,
}

fn a2_parity_fixture() -> A2ParityFixture {
    let mut terms = TermStore::new();
    let base = terms.mk_var("a2_parity_base", Sort::Int);
    let mut shared = base;
    for _ in 0..20 {
        shared = terms.mk_app(Symbol::named("g"), [shared, shared], Sort::Int);
    }
    let zero = terms.mk_int(0.into());
    let big = terms.mk_int(num_bigint::BigInt::from(1) << 300);

    let d = terms.mk_app(Symbol::named("dwrap"), [shared], Sort::Int);
    let e = terms.mk_app(Symbol::named("h"), [d], Sort::Int);
    let fe = terms.mk_app(Symbol::named("f"), [e, d], Sort::Int);
    let le_lit = terms.mk_app(Symbol::named("<="), [shared, zero], Sort::Bool);
    let lt_lit = terms.mk_app(Symbol::named("<"), [zero, fe], Sort::Bool);
    let cond = terms.mk_var("a2_cond", Sort::Bool);
    let ite_node = terms.mk_ite_raw(cond, fe, big);
    let ite_lit = terms.mk_app(Symbol::named("="), [ite_node, zero], Sort::Bool);
    let not_lit = terms.mk_not_raw(le_lit);
    let let_node = terms.mk_let(vec![("l0".to_string(), shared)], le_lit);
    let quant = terms.mk_forall_with_triggers(
        vec![("q0".to_string(), Sort::Int)],
        le_lit,
        vec![vec![shared, d], vec![e]],
    );
    let str_const = terms.mk_string("a2 payload parity content".to_string());
    let rat_const = terms.mk_rational(num_rational::BigRational::new(3.into(), 7.into()));

    let steps = [
        ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![le_lit, lt_lit],
            farkas: None,
            kind: TheoryLemmaKind::Generic,
            lia: None,
        },
        // Duplicate root (le_lit cited directly AND inside not_lit).
        ProofStep::TheoryLemma {
            theory: "LIA".to_string(),
            clause: vec![not_lit, ite_lit, le_lit],
            farkas: None,
            kind: TheoryLemmaKind::Generic,
            lia: None,
        },
        // Premise re-metering path: both premise clauses re-walked per step.
        ProofStep::Resolution {
            clause: vec![lt_lit],
            pivot: le_lit,
            clause1: ProofId(0),
            clause2: ProofId(1),
        },
        ProofStep::Step {
            rule: AletheRule::Trust,
            clause: vec![ite_lit],
            premises: vec![ProofId(0)],
            args: vec![quant, let_node, str_const, rat_const, big],
        },
    ];
    let derived = vec![
        Some(vec![le_lit, lt_lit]),
        Some(vec![not_lit, ite_lit]),
        None,
        None,
    ];
    A2ParityFixture {
        terms,
        steps,
        derived,
    }
}

#[test]
fn a2_per_step_payload_stats_are_byte_identical_to_the_unmemoized_metering() {
    // The memoized production meter must remain byte-identical to the
    // unmemoized per-step reference because those stats bound unmetered
    // semantic validators. Only the pure cost may be cached, unchanged.
    let A2ParityFixture {
        terms,
        steps,
        derived,
    } = a2_parity_fixture();

    // ONE memo across all steps, exactly as validate_strict_steps_with_context
    // threads it. The reference runs fully unmemoized every step.
    let mut memo = TermCostMemo::default();
    let mut reference_stats = Vec::new();
    for (index, step) in steps.iter().enumerate() {
        let mut unbounded = |_: usize, _: usize| true;
        let reference = reference_meter_step_term_payload(step, &terms, &derived, &mut unbounded)
            .expect("reference metering fits usize");
        let mut unbounded = |_: usize, _: usize| true;
        let memoized = meter_step_term_payload(step, &terms, &derived, &mut memo, &mut unbounded)
            .expect("memoized metering fits usize");
        assert_eq!(
            memoized.work, reference.work,
            "step {index}: PayloadStats.work must be byte-identical to the unmemoized metering"
        );
        assert_eq!(
            memoized.bytes, reference.bytes,
            "step {index}: PayloadStats.bytes must be byte-identical to the unmemoized metering"
        );
        assert_eq!(
            memoized.unfolded_work, reference.unfolded_work,
            "step {index}: unfolded_work (pure cost sum) must be identical"
        );
        reference_stats.push(reference);
    }

    // The DAG is genuinely shared: the unfolded tree bound dwarfs the number
    // of unique terms in the store, so cross-step memoization has real reuse.
    assert!(
        reference_stats[0].unfolded_work > 1 << 20,
        "shared DAG must unfold past 2^20 (got {})",
        reference_stats[0].unfolded_work
    );

    // Re-metering a step with the fully warm memo must STILL charge the full
    // per-step payload — per-step charges are independent of memo state. This
    // is precisely where the rejected shared-visited design collapsed.
    let mut unbounded = |_: usize, _: usize| true;
    let warm = meter_step_term_payload(&steps[0], &terms, &derived, &mut memo, &mut unbounded)
        .expect("warm-memo metering fits usize");
    assert_eq!(warm.work, reference_stats[0].work);
    assert_eq!(warm.bytes, reference_stats[0].bytes);
    assert_eq!(warm.unfolded_work, reference_stats[0].unfolded_work);

    // Budget-decline parity with a warm memo: a budget one unit short of the
    // step's total work must refuse the step in BOTH implementations. The
    // rejected design validated here because the warm walk charged almost
    // nothing.
    let cap = reference_stats[0].work - 1;
    let mut used = 0_usize;
    let mut capped = move |work: usize, _bytes: usize| {
        used = used.saturating_add(work);
        used <= cap
    };
    let reference_declined =
        reference_meter_step_term_payload(&steps[0], &terms, &derived, &mut capped);
    assert!(
        matches!(reference_declined, Err(ProofCheckError::ResourceLimit)),
        "reference must decline one work unit short"
    );
    let mut used = 0_usize;
    let mut capped = move |work: usize, _bytes: usize| {
        used = used.saturating_add(work);
        used <= cap
    };
    let memoized_declined =
        meter_step_term_payload(&steps[0], &terms, &derived, &mut memo, &mut capped);
    assert!(
        matches!(memoized_declined, Err(ProofCheckError::ResourceLimit)),
        "memoized metering must decline one work unit short even with a warm memo"
    );
}
