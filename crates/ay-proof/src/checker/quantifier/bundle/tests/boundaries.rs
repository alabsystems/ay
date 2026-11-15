// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn work_used(fixture: &Fixture, roots: &[TermId]) -> usize {
    let mut spent = 0usize;
    fixture
        .authenticate(roots, &mut |work, _| {
            spent += work;
            true
        })
        .expect("valid measured control");
    spent
}

#[test]
fn duplicate_roots_and_assumptions_pay_before_queue_growth() {
    let mut fixture = Fixture::new();
    let root = fixture.terms.true_term();
    let baseline = work_used(&fixture, &[root]);
    let roots = vec![root; 4_096];
    let wide_work = work_used(&fixture, &roots);
    assert!(wide_work >= baseline + roots.len());
    let mut left = baseline + 1_024;
    assert_resource(fixture.authenticate(&roots, &mut |work, _| {
        if work > left {
            return false;
        }
        left -= work;
        true
    }));
    for _ in 0..4_096 {
        fixture.proof.add_assume(root, None);
    }
    assert!(work_used(&fixture, &[]) >= wide_work);
}

#[test]
fn wide_repeated_edges_are_charged_even_when_the_dag_is_tiny() {
    let mut fixture = Fixture::new();
    let root = fixture.terms.true_term();
    let baseline = work_used(&fixture, &[root]);
    let wide = fixture
        .terms
        .mk_app(Symbol::named("wide_problem"), vec![root; 4_096], Sort::Bool);
    assert!(work_used(&fixture, &[wide]) >= baseline + 4_096);
    let mut left = baseline + 1_024;
    assert_resource(fixture.authenticate(&[wide], &mut |work, _| {
        if work > left {
            return false;
        }
        left -= work;
        true
    }));
}

#[test]
fn legacy_and_metered_routes_share_the_existing_queue_cap() {
    let mut fixture = Fixture::new();
    let root = fixture.terms.true_term();
    let roots = vec![root; SKOLEM_TERM_WORK_LIMIT + 1];
    assert_resource(fixture.authenticate(&roots, &mut |_, _| true));
    assert_resource(authenticate_bundle_skolems(
        &fixture.proof,
        &fixture.terms,
        &roots,
        &HashMap::default(),
    ));
    let wide = fixture
        .terms
        .mk_app(Symbol::named("overwide_problem"), roots, Sort::Bool);
    assert_resource(fixture.authenticate(&[wide], &mut |_, _| true));
}

#[test]
fn unused_large_names_are_not_hidden_by_proof_root_reachability() {
    let mut fixture = Fixture::new();
    let baseline = work_used(&fixture, &[]);
    let name = "unused".repeat(16_384);
    fixture.terms.mk_var(&name, Sort::Int);
    assert!(work_used(&fixture, &[]) >= baseline + name.len());
    let mut left = baseline + 1_024;
    assert_resource(fixture.authenticate(&[], &mut |work, _| {
        if work > left {
            return false;
        }
        left -= work;
        true
    }));
}

#[test]
fn missing_source_argument_problem_root_and_descendant_fail_without_indexing() {
    let mut fixture = Fixture::new();
    assert_invalid(
        fixture.authenticate(&[TermId::SENTINEL], &mut |_, _| true),
        "missing term",
    );
    let mut entries = fixture.terms.entries_snapshot();
    let dangling = TermId::new(entries.len() as u32);
    entries.push((TermData::Not(TermId::SENTINEL), Sort::Bool));
    fixture.replace_entries(entries);
    assert_invalid(
        fixture.authenticate(&[dangling], &mut |_, _| true),
        "missing term",
    );
    for change_argument in [false, true] {
        let mut fixture = Fixture::new();
        let ProofStep::Step { clause, args, .. } = &mut fixture.proof.steps[0] else {
            panic!("Skolem fixture");
        };
        if change_argument {
            args[0] = TermId::SENTINEL;
        } else {
            clause[0] = TermId::SENTINEL;
        }
        assert_invalid(fixture.authenticate(&[], &mut |_, _| true), "missing term");
    }
}

#[test]
fn proof_id_conversion_and_private_distinct_work_cap_fail_closed() {
    if let Some(index) = (u32::MAX as usize).checked_add(1) {
        assert_resource(meter::proof_id(index));
    }
    let fixture = Fixture::new();
    let mut work = SKOLEM_TERM_WORK_LIMIT;
    assert_resource(walk::collect_candidate_witnesses(
        &fixture.terms,
        vec![fixture.source],
        &HashMap::default(),
        &mut QuantifierMeter::new(ProofId(0), "sko_forall", &mut work, &mut |_, _| true),
    ));
}

#[test]
fn borrowed_declaration_lookup_prices_sparse_and_deleted_buckets() {
    let fixture = Fixture::new();
    let mut declarations = HashMap::default();
    for index in 0..2_048 {
        declarations.insert(format!("unused_declaration_{index}"), "a constructor");
    }
    let allocation = declarations.allocation_size();
    for index in 1..2_048 {
        declarations.remove(&format!("unused_declaration_{index}"));
    }
    assert_eq!(declarations.len(), 1);
    assert_eq!(declarations.allocation_size(), allocation);
    let mut sparse_work = 0usize;
    authenticate_bundle_skolems_with_progress(
        &fixture.proof,
        &fixture.terms,
        &[],
        &declarations,
        &mut |work, _| {
            sparse_work += work;
            true
        },
    )
    .expect("unrelated declarations remain valid");
    assert!(sparse_work > work_used(&fixture, &[]) + 2_048);
}
