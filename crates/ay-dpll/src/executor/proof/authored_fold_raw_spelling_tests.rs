// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::Sort;

fn fixture(assertion: &str) -> (Executor, FrontendTerm, TermId, TermId, TermId) {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse(&format!("(declare-const x Int)(assert {assertion})"))
        .expect("fixture parses");
    executor.execute_all(&commands).expect("fixture elaborates");
    let ay_frontend::Command::Assert(assertion) = &commands[1] else {
        panic!("assertion");
    };
    let root = executor.raw_intern_surface(assertion).expect("raw root");
    let FrontendTerm::App(_, args) = assertion else {
        panic!("and root");
    };
    let alias = executor.raw_intern_surface(&args[1]).expect("raw bound");
    let unrelated = executor.ctx.terms.mk_var("unrelated", Sort::Bool);
    let mut overrides = HashMap::default();
    overrides.insert(alias, "(>= x 0)".into());
    overrides.insert(unrelated, "unrelated".into());
    executor.last_proof_term_overrides = Some(overrides);
    (executor, assertion.clone(), root, alias, unrelated)
}

#[test]
fn raw_alias_mask_preserves_unrelated_overrides_and_exact_source() {
    let (mut executor, assertion, root, alias, unrelated) =
        fixture("(and (>= x 0) (<= 0 x) (= x 0))");
    assert!(!executor.rebuilt_root_prints_as_authored(root, &assertion));
    assert!(executor.try_raw_descendant_spellings(root, &assertion));
    assert!(executor.rebuilt_root_prints_as_authored(root, &assertion));
    let overrides = executor
        .last_proof_term_overrides
        .as_ref()
        .expect("overrides");
    assert!(!overrides.contains_key(&alias));
    assert_eq!(
        overrides.get(&unrelated).map(String::as_str),
        Some("unrelated")
    );
}

#[test]
fn raw_alias_mask_cannot_erase_a_forged_root_override() {
    let (mut executor, assertion, root, _, _) = fixture("(and (>= x 0) (<= 0 x) (= x 0))");
    executor
        .last_proof_term_overrides
        .as_mut()
        .expect("overrides")
        .insert(root, "(and (>= x 0) (<= 0 x) (= x 1))".into());
    let before = executor.last_proof_term_overrides.clone();
    assert!(!executor.try_raw_descendant_spellings(root, &assertion));
    assert_eq!(executor.last_proof_term_overrides, before);
}

#[test]
fn raw_alias_mask_keeps_an_authentic_root_override() {
    let (mut executor, assertion, root, _, unrelated) = fixture("(and (>= x 0) (<= 0 x) (= x 0))");
    let surface = crate::executor::proof_surface_syntax::format_frontend_term(&assertion);
    executor
        .last_proof_term_overrides
        .as_mut()
        .expect("overrides")
        .insert(root, surface.clone());
    assert!(executor.try_raw_descendant_spellings(root, &assertion));
    let overrides = executor
        .last_proof_term_overrides
        .as_ref()
        .expect("overrides");
    assert_eq!(overrides.get(&root), Some(&surface));
    assert_eq!(
        overrides.get(&unrelated).map(String::as_str),
        Some("unrelated")
    );
}

#[test]
fn later_refutation_decline_restores_all_original_overrides() {
    // The Boolean skeleton looks worth trying but is satisfiable. Masking
    // succeeds; constructing a genuine refutation must fail and roll back.
    let (mut executor, assertion, root, _, _) =
        fixture("(and (>= x 0) (<= 0 x) (or (= x 0) (not (= x 0))))");
    let before = executor.last_proof_term_overrides.clone();
    assert!(!executor.rebuilt_root_prints_as_authored(root, &assertion));
    let mut proof = ay_core::Proof::new();
    assert!(!executor.replace_with_exact_authored_fold_identity_refutation(&mut proof));
    assert_eq!(executor.last_proof_term_overrides, before);
    assert!(proof.steps.is_empty());
}

#[test]
fn copied_unrelated_spellings_debit_the_same_query_budget() {
    let (mut executor, assertion, root, _, unrelated) = fixture("(and (>= x 0) (<= 0 x) (= x 0))");
    executor
        .last_proof_term_overrides
        .as_mut()
        .expect("overrides")
        .insert(unrelated, "x".repeat(64 * 1024));
    let before = executor.last_proof_term_overrides.clone();
    let initial = executor.proof_source_work.remaining_for_test();
    assert!(executor.proof_source_work.spend(
        ProofSourcePass::AuthoredFoldIdentityRebuild,
        std::iter::once(&assertion),
    ));
    let local_work = initial - executor.proof_source_work.remaining_for_test();
    let map = before.as_ref().expect("overrides");
    let map_work = override_table_copy_work(map).expect("table cost")
        + override_string_copy_work(map).expect("string cost");
    executor
        .proof_source_work
        .set_remaining_for_test(local_work + map_work - 1);
    assert!(!executor.try_raw_descendant_spellings(root, &assertion));
    assert_eq!(executor.last_proof_term_overrides, before);
    assert!(executor.proof_source_work.remaining_for_test() < map_work - 1);

    executor.proof_source_work.set_remaining_for_test(initial);
    assert!(executor.try_raw_descendant_spellings(root, &assertion));
    assert!(initial - executor.proof_source_work.remaining_for_test() > local_work + map_work);
    assert_eq!(
        executor
            .last_proof_term_overrides
            .as_ref()
            .expect("overrides")
            .get(&unrelated),
        before.as_ref().expect("overrides").get(&unrelated)
    );
}

#[test]
fn oversized_child_batch_is_refused_without_changing_overrides() {
    let (mut executor, assertion, _, _, unrelated) = fixture("(and (>= x 0) (<= 0 x) (= x 0))");
    let root = executor.ctx.terms.mk_app(
        ay_core::Symbol::named("and"),
        vec![unrelated; super::super::MAX_SCANNED_CONJUNCT_NODES + 1],
        Sort::Bool,
    );
    assert!(
        term_child_count(&executor.ctx.terms, root).expect("child arity")
            > super::super::MAX_SCANNED_CONJUNCT_NODES
    );
    let before = executor.last_proof_term_overrides.clone();
    assert!(!executor.try_raw_descendant_spellings(root, &assertion));
    assert_eq!(executor.last_proof_term_overrides, before);
}

#[test]
fn derived_datatype_overlay_is_refused_before_copy_or_charge() {
    let (mut executor, assertion, root, _, _) = fixture("(and (>= x 0) (<= 0 x) (= x 0))");
    assert!(!executor.ctx.has_dt_field_surface_entries());
    let declarations = ay_frontend::parse(
        "(declare-datatypes ((Rec 0)) (((mk (left Int) (right Int))))) (declare-const s Rec)",
    )
    .expect("datatype declarations");
    executor
        .execute_all(&declarations)
        .expect("datatype elaboration");
    assert!(executor.ctx.has_dt_field_surface_entries());
    let before = executor.last_proof_term_overrides.clone();
    let remaining = executor.proof_source_work.remaining_for_test();
    assert!(!executor.try_raw_descendant_spellings(root, &assertion));
    assert_eq!(executor.last_proof_term_overrides, before);
    assert_eq!(executor.proof_source_work.remaining_for_test(), remaining);
}

#[test]
fn explicit_copy_debits_refuse_overflow_without_spending() {
    let (executor, _, _, _, _) = fixture("(and (>= x 0) (<= 0 x) (= x 0))");
    let remaining = executor.proof_source_work.remaining_for_test();
    assert!(!executor
        .proof_source_work
        .spend_canonical_scan_work(usize::MAX));
    assert_eq!(executor.proof_source_work.remaining_for_test(), remaining);
    assert!(executor.proof_source_work.spend_canonical_scan_work(1));
    assert_eq!(
        executor.proof_source_work.remaining_for_test(),
        remaining - 1
    );
}

#[test]
fn sparse_capacity_refuses_before_source_or_value_scans() {
    let (mut executor, assertion, root, alias, unrelated) =
        fixture("(and (>= x 0) (<= 0 x) (= x 0))");
    let overrides = executor
        .last_proof_term_overrides
        .as_mut()
        .expect("overrides");
    overrides.reserve(1 << 17);
    let capacity = overrides.capacity();
    let before = executor.proof_source_work.remaining_for_test();
    assert!(override_table_copy_work(overrides).expect("table cost") > before);
    assert!(!executor.try_raw_descendant_spellings(root, &assertion));
    let overrides = executor
        .last_proof_term_overrides
        .as_mut()
        .expect("overrides");
    assert_eq!(overrides.capacity(), capacity);
    assert_eq!(overrides.len(), 2);
    assert_eq!(overrides.get(&alias).map(String::as_str), Some("(>= x 0)"));
    assert_eq!(
        overrides.get(&unrelated).map(String::as_str),
        Some("unrelated")
    );
    assert_eq!(executor.proof_source_work.remaining_for_test(), before);
    overrides.shrink_to_fit();
    assert!(executor.try_raw_descendant_spellings(root, &assertion));
}

#[test]
fn compact_bitvector_leaf_is_preserved_but_oversized_render_is_refused() {
    // The frontend accepts widths through 1,048,576. Repeating a legal
    // compact literal makes its expanded canonical rendering exceed 8 MiB
    // without the parser rejecting the fixture before it reaches this guard.
    for (width, copies, accepted) in [(32, 1, true), (1_048_576, 9, false)] {
        let equality = format!("(= (_ bv0 {width}) (_ bv0 {width}))");
        let text = format!(
            "(and (>= x 0) (<= 0 x) {})",
            vec![equality; copies].join(" ")
        );
        let (mut executor, assertion, root, _, _) = fixture(&text);
        let FrontendTerm::App(_, conjuncts) = &assertion else {
            panic!("conjunction");
        };
        assert_eq!(conjuncts.len(), copies + 2);
        let FrontendTerm::App(_, operands) = &conjuncts[2] else {
            panic!("equality");
        };
        let literal = executor
            .raw_intern_surface(&operands[0])
            .expect("zero literal");
        let spelling = format!("(_ bv0 {width})");
        executor
            .last_proof_term_overrides
            .as_mut()
            .expect("overrides")
            .insert(literal, spelling.clone());
        let before = executor.last_proof_term_overrides.clone();
        let remaining = executor.proof_source_work.remaining_for_test();
        assert_eq!(
            executor.try_raw_descendant_spellings(root, &assertion),
            accepted
        );
        assert!(executor.proof_source_work.remaining_for_test() < remaining);
        if accepted {
            assert_eq!(
                executor
                    .last_proof_term_overrides
                    .as_ref()
                    .expect("overrides")
                    .get(&literal),
                Some(&spelling)
            );
        } else {
            assert_eq!(executor.last_proof_term_overrides, before);
        }
    }
}

#[test]
fn canonical_preflight_charges_deep_and_shared_dag_refusals() {
    // These are resource-probe inputs, not granted authored proof premises.
    for (depth, shared, accepted) in [
        (4, false, true),
        (300, false, false),
        (4, true, true),
        (20, true, false),
    ] {
        let (mut executor, _, _, _, leaf) = fixture("(and (>= x 0) (<= 0 x) (= x 0))");
        let mut root = leaf;
        for _ in 0..depth {
            root = if shared {
                executor.ctx.terms.mk_app(
                    ay_core::Symbol::named("resource_pair"),
                    vec![root, root],
                    Sort::Bool,
                )
            } else {
                executor.ctx.terms.mk_not_raw(root)
            };
        }
        let before = executor.proof_source_work.remaining_for_test();
        assert_eq!(executor.raw_retry_canonical_work(root).is_some(), accepted);
        assert!(executor.proof_source_work.remaining_for_test() < before);
        if !accepted {
            executor
                .proof_source_work
                .set_remaining_for_test(std::mem::size_of::<TermData>());
            assert!(executor.raw_retry_canonical_work(root).is_none());
            assert_eq!(executor.proof_source_work.remaining_for_test(), 0);
            assert!(executor.raw_retry_canonical_work(root).is_none());
            assert_eq!(executor.proof_source_work.remaining_for_test(), 0);
        }
    }
}

#[test]
fn one_visit_allowance_never_walks_the_rest_of_a_deep_or_shared_graph() {
    for shared in [false, true] {
        let (mut executor, _, _, _, leaf) = fixture("(and (>= x 0) (<= 0 x) (= x 0))");
        let mut root = leaf;
        for _ in 0..300 {
            root = if shared {
                executor.ctx.terms.mk_app(
                    ay_core::Symbol::named("resource_pair"),
                    vec![root, root],
                    Sort::Bool,
                )
            } else {
                executor.ctx.terms.mk_not_raw(root)
            };
        }
        let visit_cost = std::mem::size_of::<TermData>();
        executor
            .proof_source_work
            .set_remaining_for_test(visit_cost);
        let mut charges = Vec::new();
        let (result, visits) =
            canonical_term_work_probe_metered(&executor.ctx.terms, root, |work| {
                let accepted = executor.proof_source_work.spend_canonical_scan_work(work);
                charges.push((work, accepted));
                accepted
            });
        assert!(
            result.is_none(),
            "the child expansion must exhaust this allowance"
        );
        assert_eq!(visits, 1, "only the prepaid root was visited");
        assert_eq!(
            charges.len(),
            2,
            "stop at the first refused child expansion"
        );
        assert_eq!(charges[0], (visit_cost, true));
        assert!(!charges[1].1);
        assert_eq!(executor.proof_source_work.remaining_for_test(), 0);

        charges.clear();
        let (result, visits) =
            canonical_term_work_probe_metered(&executor.ctx.terms, root, |work| {
                let accepted = executor.proof_source_work.spend_canonical_scan_work(work);
                charges.push((work, accepted));
                accepted
            });
        assert!(result.is_none());
        assert_eq!(visits, 0, "an empty allowance cannot inspect the root");
        assert_eq!(charges, [(visit_cost, false)]);
    }
}

#[test]
fn bounded_roundtrip_failure_is_charged_and_sufficient_budget_matches_source() {
    let (mut executor, assertion, root, alias, _) = fixture("(and (>= x 0) (<= 0 x) (= x 0))");
    executor
        .last_proof_term_overrides
        .as_mut()
        .expect("overrides")
        .remove(&alias);
    assert!(executor.rebuilt_root_prints_as_authored(root, &assertion));
    executor.proof_source_work.set_remaining_for_test(16_384);
    assert!(!executor.raw_retry_roundtrip(root, &assertion, 1));
    assert_eq!(executor.proof_source_work.remaining_for_test(), 0);
    executor.proof_source_work.set_remaining_for_test(16_384);
    assert!(executor.raw_retry_roundtrip(root, &assertion, 4_096));
    assert!(executor.proof_source_work.remaining_for_test() < 16_384);
    assert!(executor.proof_source_work.remaining_for_test() > 0);
}

#[test]
fn raw_literal_roundtrip_preserves_value_width_structure_and_budget() {
    let mut executor = Executor::new();
    let commands = ay_frontend::parse("(declare-const p (_ BitVec 2))(assert (= p (_ bv1 2)))")
        .expect("source");
    executor.execute_all(&commands).expect("elaborates");
    let ay_frontend::Command::Assert(assertion) = &commands[1] else {
        panic!("assertion")
    };
    let root = executor.raw_intern_surface(assertion).expect("raw root");
    executor.last_proof_term_overrides = Some(HashMap::default());
    assert!(!executor.rebuilt_root_prints_as_authored(root, assertion));
    assert!(executor.raw_propositional_literal_roundtrip(root, assertion));
    for changed in ["(= p (_ bv2 2))", "(= p (_ bv1 3))", "(= q (_ bv1 2))"] {
        let changed =
            super::super::super::parse_rendered_assertion(changed).expect("changed source");
        assert!(!executor.raw_propositional_literal_roundtrip(root, &changed));
    }
    executor.proof_source_work.set_remaining_for_test(0);
    assert!(!executor.raw_propositional_literal_roundtrip(root, assertion));
    assert_eq!(executor.proof_source_work.remaining_for_test(), 0);
}
