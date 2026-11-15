// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use std::cell::Cell;

#[test]
fn guarded_unit_authentication_uses_the_shared_budget_without_resetting_it() {
    use crate::executor::proof_propagated_rewrite::array_units::ArrayReplayBudget;

    let mut f = Fixture::new(129);
    let unit = f.units[0].term();
    let set = f.roots.iter().copied().collect();
    let used = Cell::new((0usize, 0usize));
    let progress = |work, bytes| {
        let before = used.get();
        used.set((
            before.0.checked_add(work).unwrap(),
            before.1.checked_add(bytes).unwrap(),
        ));
        true
    };
    let mut measured = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
        .with_array_units(&f.units, &progress);
    let id = PropagationChainPlanner {
        terms: &mut f.terms,
    }
    .plan_array_unit_base(&mut measured, unit)
    .expect("genuine guarded definition fits the planner-node envelope");
    assert_eq!(
        authenticate(&f.terms, &f.roots, &measured.chain)
            .unwrap()
            .clause(id),
        Some([unit].as_slice())
    );
    let (work, bytes) = used.get();
    let local = PLAN_NODE_BUDGET - measured.budget;
    assert!(work > 0 && bytes > 0 && local > 0);
    assert!(
        work + bytes.div_ceil(64) > local,
        "full checker work is charged, but is not a planner-node count"
    );

    let executor = Executor::new();
    for (work_left, bytes_left, admitted) in [
        (work, bytes, true),
        (work - 1, bytes, false),
        (work, bytes - 1, false),
    ] {
        let shared = ArrayReplayBudget::new(&executor);
        assert!(shared.charge(
            PLAN_NODE_BUDGET * MAX_STORED_PROPAGATION_RECORDS - work_left,
            64 * 1024 * 1024 - bytes_left,
        ));
        let progress = |work, bytes| shared.charge(work, bytes);
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
            .with_array_units(&f.units, &progress);
        let result = PropagationChainPlanner {
            terms: &mut f.terms,
        }
        .plan_array_unit_base(&mut cx, unit);
        assert_eq!(result.is_some(), admitted);
        if admitted {
            assert_eq!(PLAN_NODE_BUDGET - cx.budget, local);
            assert!(shared.charge(0, 0));
            assert!(
                !shared.charge(1, 1),
                "the exact shared allowance is exhausted"
            );
        } else {
            assert!(cx.chain.steps.is_empty());
        }
        assert!(!shared.charge(0, 0), "observed refusal stays sticky");
        let mut retry = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
            .with_array_units(&f.units, &progress);
        assert!(PropagationChainPlanner {
            terms: &mut f.terms
        }
        .plan_array_unit_base(&mut retry, unit)
        .is_none());
        assert!(retry.chain.steps.is_empty());
    }
    let mut missing = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
        .with_array_units(&f.units, &allow);
    missing.array_progress = None;
    assert!(PropagationChainPlanner {
        terms: &mut f.terms
    }
    .plan_array_unit_base(&mut missing, unit)
    .is_none());
    assert!(missing.chain.steps.is_empty());
}

#[test]
fn shared_callback_and_exact_plan_allowance_precede_the_retry_suffix() {
    let mut f = Fixture::new(8);
    let (prefix, child) = f.changed_child();
    let required = RETRY_WORK + RETRY_BYTES.div_ceil(64);
    let set = f.roots.iter().copied().collect();
    for allowance in [0, required - 1, required] {
        let observed = Cell::new((0, 0, 0));
        let progress = |work, bytes| {
            let (calls, used_work, used_bytes) = observed.get();
            observed.set((calls + 1, used_work + work, used_bytes + bytes));
            true
        };
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
            .with_array_units(&f.units, &progress);
        cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
        cx.chain = prefix.clone();
        cx.budget = allowance;
        let result = PropagationChainPlanner {
            terms: &mut f.terms,
        }
        .plan_scalar_canonical_fold(
            &mut cx,
            f.scalar,
            &Symbol::named("="),
            &[f.value, f.high],
            &[f.payload, f.high],
            &[child, EqRes::Unchanged],
        );
        assert_eq!(result.is_some(), allowance == required);
        assert_eq!(observed.get(), (1, RETRY_WORK, RETRY_BYTES));
        if result.is_none() {
            assert_eq!(cx.chain, prefix);
        } else {
            assert_eq!(cx.budget, 0);
            authenticate(&f.terms, &f.roots, &cx.chain).unwrap();
        }
    }
    let stop = Cell::new(true);
    let progress = |_, _| !stop.get();
    let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
        .with_array_units(&f.units, &progress);
    cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
    cx.chain = prefix.clone();
    let mut planner = PropagationChainPlanner {
        terms: &mut f.terms,
    };
    assert!(planner
        .plan_scalar_canonical_fold(
            &mut cx,
            f.scalar,
            &Symbol::named("="),
            &[f.value, f.high],
            &[f.payload, f.high],
            &[child, EqRes::Unchanged],
        )
        .is_none());
    assert_eq!(cx.chain, prefix);
    stop.set(false);
    let mut fresh = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
        .with_array_units(&f.units, &progress);
    fresh.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
    fresh.chain = prefix;
    assert!(planner
        .plan_scalar_canonical_fold(
            &mut fresh,
            f.scalar,
            &Symbol::named("="),
            &[f.value, f.high],
            &[f.payload, f.high],
            &[child, EqRes::Unchanged],
        )
        .is_some());
}

#[test]
fn malformed_metadata_dead_operands_and_partial_licenses_do_not_append_steps() {
    for change in 0..14 {
        let mut f = Fixture::new(8);
        let (prefix, child) = f.changed_child();
        let mut term = f.scalar;
        let mut symbol = Symbol::named("=");
        let mut args = vec![f.value, f.high];
        let mut rewritten = vec![f.payload, f.high];
        let mut children = vec![child, EqRes::Unchanged];
        match change {
            0 => symbol = Symbol::indexed("=", vec![0]),
            1 => term = TermId(u32::MAX),
            2 => {
                args.pop();
            }
            3 => rewritten[0] = TermId(u32::MAX),
            4 => rewritten[1] = f.terms.true_term(),
            5 => term = f.terms.mk_app(symbol.clone(), &args, Sort::bitvec(8)),
            6 => args.swap(0, 1),
            7..=10 => {
                let TermData::Ite(condition, yes, no) = f.terms.get(f.payload) else {
                    unreachable!()
                };
                let (mut condition, mut yes, mut no) = (*condition, *yes, *no);
                match change {
                    7 => condition = f.high,
                    8 => yes = f.terms.true_term(),
                    9 => no = TermId(u32::MAX),
                    10 => no = f.terms.true_term(),
                    _ => unreachable!(),
                }
                // A checker-only snapshot can represent malformed input without
                // bypassing the ordinary builder's typed debug assertions. This
                // case must refuse before the helper tries to intern any node.
                let mut snapshot = f.terms.entries_snapshot();
                let bad = TermId(snapshot.len() as u32);
                snapshot.push((TermData::Ite(condition, yes, no), Sort::bitvec(8)));
                f.terms = TermStore::from_entries(
                    snapshot,
                    Some(f.terms.true_term()),
                    Some(f.terms.false_term()),
                    f.terms.var_counter(),
                );
                if change == 10 {
                    // A valid first ITE must not hide malformed metadata in the second.
                    rewritten[1] = bad;
                } else {
                    rewritten[0] = bad;
                }
            }
            11 => {
                children.pop();
            }
            12 => rewritten[0] = f.high,
            13 => {
                let zero = f.terms.mk_var("zero width", Sort::bitvec(0));
                args[0] = zero;
                args[1] = zero;
                rewritten.fill(zero);
                term = app(&mut f.terms, "=", &args);
            }
            _ => unreachable!(),
        }
        let set = f.roots.iter().copied().collect();
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
            .with_array_units(&f.units, &allow);
        cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
        cx.chain = prefix.clone();
        assert!(PropagationChainPlanner {
            terms: &mut f.terms
        }
        .plan_scalar_canonical_fold(&mut cx, term, &symbol, &args, &rewritten, &children,)
        .is_none());
        assert_eq!(cx.chain, prefix);
    }
}

#[test]
fn absent_callback_and_exact_conclusion_guard_keep_existing_refusals() {
    let mut f = Fixture::new(8);
    let (prefix, child) = f.changed_child();
    let candidate = app(&mut f.terms, "=", &[f.high, f.payload]);
    let set = f.roots.iter().copied().collect();
    for change in 0..2 {
        let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false)
            .with_array_units(&f.units, &allow);
        cx.scalar_equality_mode = ScalarEqualityMode::ArrayCanonical;
        cx.chain = prefix.clone();
        if change == 0 {
            cx.array_progress = None;
        } else {
            // A private plan exercises the exact existing conclusion guard;
            // public callers use this field only for a literal Bool target.
            cx.constant_target = Some(candidate);
        }
        assert!(PropagationChainPlanner {
            terms: &mut f.terms
        }
        .plan_scalar_canonical_fold(
            &mut cx,
            f.scalar,
            &Symbol::named("="),
            &[f.value, f.high],
            &[f.payload, f.high],
            &[child, EqRes::Unchanged],
        )
        .is_none());
        assert_eq!(cx.chain, prefix);
    }
}

#[test]
fn negative_and_unchanged_memo_outcomes_also_include_the_spelling_mode() {
    let mut f = Fixture::new(8);
    let set = f.roots.iter().copied().collect();
    // Without the array-unit channel the array replacement is deliberately
    // unavailable. Both attempts refuse, rather than minting missing authority.
    let mut cx = PlanCx::new(&set, &f.roots, &f.records, &f.entries, &[], false);
    let mut planner = PropagationChainPlanner {
        terms: &mut f.terms,
    };
    for mode in [
        ScalarEqualityMode::Legacy,
        ScalarEqualityMode::ArrayCanonical,
    ] {
        cx.scalar_equality_mode = mode;
        assert!(planner.plan_derive_eq(&mut cx, f.before, f.stamp).is_none());
        assert!(matches!(
            planner.plan_derive_eq(&mut cx, f.high, f.stamp),
            Some(EqRes::Unchanged)
        ));
    }
    for mode in [
        ScalarEqualityMode::Legacy,
        ScalarEqualityMode::ArrayCanonical,
    ] {
        assert!(matches!(
            cx.eq_memo.get(&(f.before, f.stamp, mode)),
            Some(None)
        ));
        assert!(matches!(
            cx.eq_memo.get(&(f.high, f.stamp, mode)),
            Some(Some(EqRes::Unchanged))
        ));
    }
}
