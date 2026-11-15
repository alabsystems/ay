// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

fn trace(fixture: &Fixture) -> Vec<(usize, usize)> {
    let mut charges = Vec::new();
    fixture
        .run(&mut |work, bytes| {
            charges.push((work, bytes));
            true
        })
        .expect("valid fixture");
    charges
}

fn totals(charges: &[(usize, usize)]) -> (usize, usize) {
    charges.iter().fold(
        (0usize, 0usize),
        |(work, bytes), &(next_work, next_bytes)| {
            (
                work.checked_add(next_work).expect("test work"),
                bytes.checked_add(next_bytes).expect("test bytes"),
            )
        },
    )
}

fn spend(remaining: &mut (usize, usize), work: usize, bytes: usize) -> bool {
    match (
        remaining.0.checked_sub(work),
        remaining.1.checked_sub(bytes),
    ) {
        (Some(next_work), Some(next_bytes)) => {
            *remaining = (next_work, next_bytes);
            true
        }
        _ => false,
    }
}

#[test]
fn every_callback_including_final_poll_refuses_without_publishing_success() {
    let fixture = Fixture::new();
    let charges = trace(&fixture);
    assert_eq!(charges.first(), Some(&(0, 0)));
    assert_eq!(charges.last(), Some(&(0, 0)));
    assert!(charges.iter().any(|&(_, bytes)| bytes != 0));
    for stop in 1..=charges.len() {
        let mut calls = 0usize;
        assert_resource(fixture.run(&mut |_, _| {
            calls += 1;
            calls != stop
        }));
        assert_eq!(calls, stop, "callback refusal must propagate immediately");
    }
    fixture
        .compare()
        .expect("immutable source remains reusable");
}

#[test]
fn closure_and_ite_matching_share_exact_cumulative_work_and_bytes() {
    let fixture = Fixture::new();
    let total = totals(&trace(&fixture));
    assert!(total.0 > 0 && total.1 > 0);
    for initial in [
        (0, total.1),
        (total.0 - 1, total.1),
        (total.0, 0),
        (total.0, total.1 - 1),
    ] {
        let mut remaining = initial;
        assert_resource(fixture.run(&mut |work, bytes| spend(&mut remaining, work, bytes)));
    }
    let mut remaining = total;
    let mut progress = |work, bytes| spend(&mut remaining, work, bytes);
    fixture
        .run(&mut progress)
        .expect("exact cumulative allowance");
    assert_resource(fixture.run(&mut progress));
    assert_eq!(remaining, (0, 0));
}

#[test]
fn repeated_assertions_and_conjunction_edges_are_each_priced() {
    for repeated_roots in [true, false] {
        let mut fixture = Fixture::new();
        if !repeated_roots {
            let root = fixture
                .terms
                .mk_app(Symbol::named("and"), [fixture.ite], Sort::Bool);
            fixture.roots = vec![root];
        }
        let baseline = totals(&trace(&fixture)).0;
        if repeated_roots {
            fixture.roots = vec![fixture.ite; 4096];
        } else {
            let root =
                fixture
                    .terms
                    .mk_app(Symbol::named("and"), vec![fixture.ite; 4096], Sort::Bool);
            fixture.roots = vec![root];
        }
        fixture
            .compare()
            .expect("duplicate sources preserve exact closure");
        assert!(totals(&trace(&fixture)).0 >= baseline + 4095);
        let mut remaining = (baseline + 64, usize::MAX);
        assert_resource(fixture.run(&mut |work, bytes| spend(&mut remaining, work, bytes)));
    }
}

#[test]
fn unique_wide_closure_prices_tree_nodes_and_explicit_vector_growth() {
    let mut fixture = Fixture::new();
    let baseline = totals(&trace(&fixture));
    let mut leaves = vec![fixture.ite];
    for index in 0..256 {
        let leaf = fixture
            .terms
            .mk_var(&format!("wide_authored_{index}"), Sort::Bool);
        leaves.push(leaf);
        fixture.proof.add_assume(leaf, None);
    }
    let root = fixture
        .terms
        .mk_app(Symbol::named("and"), leaves, Sort::Bool);
    fixture.roots = vec![root];
    fixture
        .compare()
        .expect("wide authored closure has no new cardinality cap");
    let total = totals(&trace(&fixture));
    assert!(total.0 > baseline.0 && total.1 > baseline.1);
    let mut remaining = (usize::MAX, baseline.1);
    assert_resource(fixture.run(&mut |work, bytes| spend(&mut remaining, work, bytes)));

    let mut values = Vec::<TermId>::new();
    assert_resource(push(&mut values, fixture.ite, &mut |_, bytes| bytes == 0));
    assert!(values.is_empty() && values.capacity() == 0);
    push(&mut values, fixture.ite, &mut |_, _| true).expect("first reservation");
    while values.len() < values.capacity() {
        values.push(fixture.ite);
    }
    let original = values.clone();
    let capacity = values.capacity();
    assert_resource(push(&mut values, fixture.branch, &mut |_, bytes| {
        bytes == 0
    }));
    assert_eq!(values, original);
    assert_eq!(values.capacity(), capacity);
}

#[test]
fn repeated_assumptions_and_other_proof_steps_are_not_free() {
    for assumptions in [true, false] {
        let mut fixture = Fixture::new();
        let baseline = totals(&trace(&fixture)).0;
        for _ in 0..4096 {
            if assumptions {
                fixture.proof.add_assume(fixture.ite, None);
            } else {
                fixture.proof.steps.push(ProofStep::Anchor {
                    end_step: ProofId(0),
                    variables: vec![],
                });
            }
        }
        fixture
            .compare()
            .expect("authorization ignores non-assumption rule meaning");
        assert!(totals(&trace(&fixture)).0 >= baseline + 4096);
        let mut remaining = (baseline + 64, usize::MAX);
        assert_resource(fixture.run(&mut |work, bytes| spend(&mut remaining, work, bytes)));
    }
}

#[test]
fn empty_fragment_still_polls_entry_closure_and_final_boundary() {
    let mut fixture = Fixture::new();
    fixture.proof = Proof::new();
    fixture.roots.clear();
    assert_eq!(trace(&fixture), vec![(0, 0); 3]);
    let mut calls = 0usize;
    assert_resource(fixture.run(&mut |_, _| {
        calls += 1;
        calls < 3
    }));
    assert_eq!(calls, 3);
}
