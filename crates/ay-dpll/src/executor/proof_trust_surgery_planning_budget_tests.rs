// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Sort, TermData, TermStore};
use ay_frontend::command::Term as FrontendTerm;

use super::{surface_source_work, SurgeryPlanningBudget};

#[test]
fn unmetered_probe_keeps_its_results_with_an_accepting_meter() {
    let mut terms = TermStore::new();
    let leaf = terms.mk_var("legacy_probe", Sort::Bool);
    let negated = terms.mk_not_raw(leaf);
    let shared = terms.mk_app(
        ay_core::Symbol::named("pair"),
        vec![negated, negated],
        Sort::Bool,
    );
    let binder = terms.mk_forall(vec![("bound".into(), Sort::Bool)], leaf);
    let node = size_of::<TermData>();
    for (root, expected, expected_visits) in [
        (leaf, Ok("legacy_probe".len() + node), 1),
        (negated, Ok(1 + "legacy_probe".len() + 2 * node), 2),
        (
            shared,
            Ok("pair".len() + 8 + 2 * (1 + "legacy_probe".len()) + 5 * node),
            5,
        ),
        (binder, Err(super::CanonicalWorkRefusal::Binder), 1),
    ] {
        assert_eq!(
            super::canonical_term_work_probe(&terms, root),
            (expected, expected_visits)
        );
        let (actual, actual_visits) =
            super::canonical_term_work_probe_metered(&terms, root, |_| true);
        assert_eq!(actual, Some(expected));
        assert_eq!(actual_visits, expected_visits);
    }
}

#[test]
fn farkas_attempts_share_one_global_boundary() {
    let mut terms = TermStore::new();
    let atom = terms.mk_var("planning_budget_atom", Sort::Bool);
    let mut budget = SurgeryPlanningBudget::new();
    for _ in 0..super::MAX_FARKAS_ATTEMPTS {
        assert!(budget.spend_farkas_attempt(&terms, &[atom]));
    }
    assert!(!budget.spend_farkas_attempt(&terms, &[atom]));
}

/// The tri-state charge must separate "cannot price this" from "budget
/// gone" — the conflation that made one authored `forall` abort the whole
/// ground ITE-lift scan (#shannon-lift-checkable).
#[test]
fn charging_a_binder_operand_is_unpriceable_not_exhaustion() {
    let mut terms = TermStore::new();
    let body = terms.mk_var("charge_binder_body", Sort::Bool);
    let binder = terms.mk_forall(vec![("charge_z".to_string(), Sort::Int)], body);
    assert!(
        super::canonical_term_work(&terms, binder).is_none(),
        "the cost model refuses to price a binder",
    );
    let mut budget = SurgeryPlanningBudget::new();
    assert!(matches!(
        budget.charge_operand(&terms, binder),
        super::OperandCharge::Unpriceable
    ));
    // The scan may go on to price and use an ordinary ground operand.
    assert!(matches!(
        budget.charge_operand(&terms, body),
        super::OperandCharge::Charged
    ));
}

/// A refusal is still billed, so a file of binders cannot buy unbounded
/// planning work one free probe at a time.
#[test]
fn an_unpriceable_operand_still_spends_the_aggregate_budget() {
    let mut terms = TermStore::new();
    let body = terms.mk_var("charge_drain_body", Sort::Bool);
    let binder = terms.mk_forall(vec![("charge_drain_z".to_string(), Sort::Int)], body);
    let mut budget = SurgeryPlanningBudget::new();
    budget.set_remaining_work_for_test(1);
    assert!(matches!(
        budget.charge_operand(&terms, binder),
        super::OperandCharge::Exhausted
    ));
}

#[test]
fn one_canonical_source_cannot_reuse_another_surface_address() {
    let mut budget = SurgeryPlanningBudget::new();
    let first = FrontendTerm::Symbol("first_source".to_string());
    let second = FrontendTerm::Symbol("second_source".to_string());
    assert!(budget.spend_surface(ay_core::TermId(7), &first));
    assert!(!budget.spend_surface(ay_core::TermId(7), &second));
}

#[test]
fn repeated_whole_surface_operations_spend_the_aggregate_budget() {
    let fragment = FrontendTerm::App(
        "+".to_string(),
        (0..4_096)
            .map(|index| FrontendTerm::Symbol(format!("fragment_{index}")))
            .collect(),
    );
    let work = surface_source_work(&fragment).expect("bounded fragment has a cost");
    let mut budget = SurgeryPlanningBudget::new();
    budget.set_remaining_work_for_test(work * 2 - 1);
    assert!(budget.spend_surface(ay_core::TermId(8), &fragment));
    assert!(!budget.spend_surface(ay_core::TermId(8), &fragment));
}

#[test]
fn whole_source_estimate_dominates_all_immediate_fragment_estimates() {
    let rows: Vec<FrontendTerm> = (0..64)
        .map(|index| {
            FrontendTerm::App(
                "=".to_string(),
                vec![
                    FrontendTerm::Symbol(format!("surface_row_{index}")),
                    FrontendTerm::Const(ay_frontend::command::Constant::Numeral(index.to_string())),
                ],
            )
        })
        .collect();
    let fragment_work = rows.iter().try_fold(0usize, |used, row| {
        used.checked_add(surface_source_work(row)?)
    });
    let whole = FrontendTerm::App("and".to_string(), rows);
    assert!(
        surface_source_work(&whole).expect("whole source is bounded")
            >= fragment_work.expect("all fragments are bounded"),
        "one complete-source charge must dominate a pass over every child",
    );
}
