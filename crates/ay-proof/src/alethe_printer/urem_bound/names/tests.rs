// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{Sort, Symbol, TermStore};

#[test]
fn compact_prefix_is_stable_injective_and_separated_from_adjacent_ids() {
    let terms = TermStore::new();
    let printer = AlethePrinter::new(&terms);
    let mut seen = DetHashSet::default();
    for id in [0, 1, 15, 16, 255, 256, u32::MAX] {
        let name = printer.urem_definition_prefix(ProofId(id)).unwrap();
        assert!(seen.insert(name.clone()));
        assert_eq!(name, printer.urem_definition_prefix(ProofId(id)).unwrap());
        assert_eq!(name, format!("@u{id:x}_0_"));
        assert!(name.len() < format!("@ay_ur_t{id}_0_").len());
    }
    assert_eq!(
        printer.urem_definition_prefix(ProofId(1)).unwrap(),
        "@u1_0_"
    );
}

#[test]
fn variables_functions_let_and_quantifier_binders_each_reserve_the_namespace() {
    for kind in 0..5 {
        let mut terms = TermStore::new();
        let body = terms.mk_var("body", Sort::Bool);
        let name = "@u1_0_existing";
        match kind {
            0 => {
                let _variable_binding = terms.mk_var(name, Sort::Bool);
            }
            1 => {
                let _function_application = terms.mk_app(Symbol::named(name), [body], Sort::Bool);
            }
            2 => {
                let _let_binding = terms.mk_let(vec![(name.into(), body)], body);
            }
            3 => {
                let _forall_binding = terms.mk_forall(vec![(name.into(), Sort::Bool)], body);
            }
            _ => {
                let _exists_binding = terms.mk_exists(vec![(name.into(), Sort::Bool)], body);
            }
        }
        let printer = AlethePrinter::new(&terms);
        assert_eq!(
            printer.urem_definition_prefix(ProofId(1)).unwrap(),
            "@u1_1_"
        );
    }
}

#[test]
fn every_rendering_override_channel_reserves_names_even_off_the_theorem_path() {
    for channel in 0..3 {
        let mut terms = TermStore::new();
        let unrelated = terms.mk_var("unrelated", Sort::Bool);
        let mut overrides = DetHashMap::default();
        if channel == 0 {
            overrides.insert(unrelated, "(not |@u1_0_existing|)".to_string());
        }
        let printer = AlethePrinter::new_with_overrides_and_budget(&terms, Some(&overrides), None);
        if channel == 1 {
            printer
                .skolem_overrides
                .borrow_mut()
                .insert(unrelated, "@u1_0_existing".into());
        }
        if channel == 2 {
            printer
                .let_bridge_renderings
                .borrow_mut()
                .insert(unrelated, "@u1_0_existing".into());
        }
        assert_eq!(
            printer.urem_definition_prefix(ProofId(1)).unwrap(),
            "@u1_1_"
        );
    }
}

#[test]
fn all_sixty_four_collisions_refuse_without_reusing_a_source_name() {
    let mut terms = TermStore::new();
    for nonce in 0..64 {
        let _occupied_variable = terms.mk_var(format!("@u1_{nonce:x}_occupied"), Sort::Bool);
    }
    let printer = AlethePrinter::new(&terms);
    assert!(printer.urem_definition_prefix(ProofId(1)).is_none());
    assert_eq!(
        printer.urem_definition_prefix(ProofId(2)).unwrap(),
        "@u2_0_"
    );
}

#[test]
fn original_export_budget_pays_namespace_scans_and_refusal_is_sticky() {
    let mut terms = TermStore::new();
    let _namespace_collision = terms.mk_var("@u1_0_occupied", Sort::Bool);
    let printer = AlethePrinter::new(&terms);
    let expected = printer.urem_definition_prefix(ProofId(1)).unwrap();
    let used = printer.work_used();
    assert!(used > 64);
    for budget in [0, used - 1, used] {
        let printer = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(budget));
        let result = printer.urem_definition_prefix(ProofId(1));
        if budget == used {
            assert_eq!(result.as_deref(), Some(expected.as_str()));
            assert_eq!(printer.work_used(), used);
        } else {
            assert!(result.is_none());
            let stopped = printer.work_used();
            assert!(printer.urem_definition_prefix(ProofId(2)).is_none());
            assert_eq!(printer.work_used(), stopped);
        }
    }
}

#[test]
fn every_original_namespace_observer_cut_refuses_without_a_late_callback() {
    use std::cell::Cell;
    let mut terms = TermStore::new();
    let _namespace_collision = terms.mk_var("@u1_0_occupied", Sort::Bool);
    let calls = Cell::new(0);
    let mut accept = || {
        calls.set(calls.get() + 1);
        true
    };
    let printer = AlethePrinter::new(&terms).with_emission_progress(&mut accept);
    assert_eq!(
        printer.urem_definition_prefix(ProofId(1)).unwrap(),
        "@u1_1_"
    );
    let total = calls.get();
    assert!(total > 8);
    for cut in 1..=total {
        let seen = Cell::new(0);
        let mut callback = || {
            seen.set(seen.get() + 1);
            seen.get() != cut
        };
        let printer = AlethePrinter::new(&terms).with_emission_progress(&mut callback);
        assert!(printer.urem_definition_prefix(ProofId(1)).is_none());
        assert_eq!(seen.get(), cut);
        let stopped = printer.work_used();
        assert!(printer.urem_definition_prefix(ProofId(2)).is_none());
        assert_eq!(seen.get(), cut);
        assert_eq!(printer.work_used(), stopped);
    }
}

#[test]
fn real_remainder_export_uses_shorter_names_without_holes_or_an_altered_conclusion() {
    use crate::alethe_printer::{emission_progress::EmissionProgress, mul_overflow_cert};
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::bitvec(1));
    let d = terms.mk_var("d", Sort::bitvec(1));
    let zero = terms.mk_bitvec(0.into(), 1);
    let rem = terms.mk_app(Symbol::named("bvurem"), [x, d], Sort::bitvec(1));
    let guard = terms.mk_app(Symbol::named("="), [d, zero], Sort::Bool);
    let range = terms.mk_app(Symbol::named("bvult"), [rem, d], Sort::Bool);
    let root = terms.mk_app(Symbol::named("or"), [guard, range], Sort::Bool);
    let printer = AlethePrinter::new(&terms);
    let compact = printer.format_urem_bound(ProofId(1), &[root]).unwrap();
    let original = mul_overflow_cert::remainder::certificate(
        1,
        "x",
        "d",
        "@ay_ur_t1_0_",
        "t1",
        &printer.format_clause(&[root]),
        EmissionProgress::default(),
    )
    .unwrap();
    assert!(compact.len() < original.len());
    assert!(compact.contains("(define-fun @u1_0_"));
    assert!(!compact.contains("@ay_ur_"));
    assert!(!compact.contains(":rule hole"));
    assert!(!compact.contains(":rule trust"));
    assert_eq!(compact.lines().last(), original.lines().last());
    // Structural exporter coverage only: independent Clean replay is required.
}
