// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::sync::atomic::{AtomicBool, Ordering};

mod fixtures;
use fixtures::Fixture;

#[test]
fn l1_entry_repairs_exact_parsed_guard_after_full_recorded_preprocessing() {
    let mut fixture = Fixture::parsed();
    let mut proof = fixture.pending();
    fixture
        .executor
        .derive_propagated_value_assumptions(&mut proof, &fixture.originals);
    assert!(
        !proof.steps.contains(&ProofStep::Assume(fixture.guard)),
        "raw entries={:?}; raw rewrites={:?}",
        fixture.executor.propagated_value_provenance.entries,
        fixture.executor.propagated_value_provenance.rewrites,
    );
    fixture.authenticate(&proof);
}

#[test]
fn l1_entry_does_not_license_a_guard_from_missing_original_roots() {
    let mut fixture = Fixture::parsed();
    let original = fixture.pending();
    for roots in [
        fixture.originals[1..].to_vec(),
        fixture.originals[..2].to_vec(),
    ] {
        let mut proof = original.clone();
        fixture
            .executor
            .derive_propagated_value_assumptions(&mut proof, &roots);
        assert_eq!(proof, original);
    }
    let mut proof = original;
    fixture
        .executor
        .derive_propagated_value_assumptions(&mut proof, &fixture.originals);
    fixture.authenticate(&proof);
}

#[test]
fn l1_census_never_descends_or_or_malformed_and_edges() {
    let mut fixture = Fixture::parsed();
    let terms = &mut fixture.executor.ctx.terms;
    let other = terms.mk_var("other", Sort::Bool);
    let root = terms.mk_app(Symbol::named("or"), [fixture.guard, other], Sort::Bool);
    let records = HashMap::from_iter([(root, (root, 1))]);
    let found = and_descendants(terms, &records, &|_, _| true).unwrap();
    assert!(!found.contains(&fixture.guard));
    fixture.executor.propagated_value_provenance.entries.clear();
    fixture.executor.propagated_value_provenance.rewrites =
        vec![crate::preprocess::PropagatedRewriteRecord {
            before: fixture.originals[2],
            after: root,
            stamp: 1,
        }];
    let original = fixture.pending();
    let mut proof = original.clone();
    fixture
        .executor
        .derive_propagated_value_assumptions(&mut proof, &fixture.originals);
    assert_eq!(proof, original);

    let terms = &mut fixture.executor.ctx.terms;
    let bad = terms.mk_int(0.into());
    let malformed = terms.mk_app(Symbol::named("and"), [fixture.guard, bad], Sort::Bool);
    assert!(and_descendants(
        terms,
        &HashMap::from_iter([(malformed, (root, 1))]),
        &|_, _| true,
    )
    .is_err());
    assert!(and_descendants(
        terms,
        &HashMap::from_iter([(TermId(u32::MAX), (root, 1))]),
        &|_, _| true,
    )
    .is_err());
}

#[test]
fn l1_discovery_depth_and_fanout_caps_share_one_census() {
    let mut fixture = Fixture::parsed();
    let terms = &mut fixture.executor.ctx.terms;
    let mut deep = fixture.guard;
    for _ in 0..MAX_AND_DEPTH {
        deep = terms.mk_app(Symbol::named("and"), [deep], Sort::Bool);
    }
    assert!(and_descendants(
        terms,
        &HashMap::from_iter([(deep, (fixture.originals[2], 1))]),
        &|_, _| true,
    )
    .unwrap()
    .contains(&fixture.guard));
    deep = terms.mk_app(Symbol::named("and"), [deep], Sort::Bool);
    assert!(!and_descendants(
        terms,
        &HashMap::from_iter([(deep, (fixture.originals[2], 1))]),
        &|_, _| true,
    )
    .unwrap()
    .contains(&fixture.guard));
    let wide = terms.mk_app(
        Symbol::named("and"),
        vec![fixture.guard; PLAN_NODE_BUDGET],
        Sort::Bool,
    );
    assert!(and_descendants(
        terms,
        &HashMap::from_iter([(wide, (fixture.originals[2], 1))]),
        &|_, _| true,
    )
    .is_err());
    // Both individually fit, but their repeated edges share ONE allowance.
    let marker = terms.mk_var("second_parent_marker", Sort::Bool);
    let first = terms.mk_app(Symbol::named("and"), vec![fixture.guard; 4_000], Sort::Bool);
    let second = terms.mk_app(Symbol::named("and"), vec![marker; 4_000], Sort::Bool);
    for root in [first, second] {
        assert!(and_descendants(
            terms,
            &HashMap::from_iter([(root, (fixture.originals[2], 1))]),
            &|_, _| true,
        )
        .is_ok());
    }
    assert!(and_descendants(
        terms,
        &HashMap::from_iter([
            (first, (fixture.originals[2], 1)),
            (second, (fixture.originals[2], 1)),
        ]),
        &|_, _| true,
    )
    .is_err());
    for after in [deep, wide] {
        fixture.executor.propagated_value_provenance.rewrites =
            vec![crate::preprocess::PropagatedRewriteRecord {
                before: fixture.originals[2],
                after,
                stamp: 1,
            }];
        let original = fixture.pending();
        let mut proof = original.clone();
        fixture
            .executor
            .derive_propagated_value_assumptions(&mut proof, &fixture.originals);
        assert_eq!(proof, original);
    }
}

#[test]
fn l1_local_census_decline_preserves_an_existing_direct_candidate() {
    for many_records in [false, true] {
        let mut fixture = Fixture::parsed();
        let length = fixture
            .executor
            .ctx
            .symbol_info("length")
            .unwrap()
            .term
            .unwrap();
        let index = fixture
            .executor
            .ctx
            .symbol_info("__gpc1")
            .unwrap()
            .term
            .unwrap();
        let before = fixture.executor.ctx.terms.mk_bvult(index, length);
        fixture.originals.push(before);
        fixture.executor.propagated_value_provenance.rewrites.push(
            crate::preprocess::PropagatedRewriteRecord {
                before,
                after: fixture.guard,
                stamp: u32::MAX,
            },
        );
        if many_records {
            while fixture.executor.propagated_value_provenance.rewrites.len() < 4_096 {
                let n = fixture.executor.propagated_value_provenance.rewrites.len();
                let unrelated = fixture
                    .executor
                    .ctx
                    .terms
                    .mk_var(format!("unrelated_after_{n}"), Sort::Bool);
                fixture.executor.propagated_value_provenance.rewrites.push(
                    crate::preprocess::PropagatedRewriteRecord {
                        before,
                        after: unrelated,
                        stamp: 1,
                    },
                );
            }
        } else {
            fixture.executor.propagated_value_provenance.rewrites.push(
                crate::preprocess::PropagatedRewriteRecord {
                    before,
                    after: TermId(u32::MAX),
                    stamp: 1,
                },
            );
        }
        let (records, _) = fixture.executor.propagation_replay_indexes();
        assert_eq!(
            and_descendants(&fixture.executor.ctx.terms, &records, &|_, _| true),
            Err(CensusDecline::BoundedMiss),
        );
        let mut proof = fixture.pending();
        fixture
            .executor
            .derive_propagated_value_assumptions(&mut proof, &fixture.originals);
        fixture.authenticate(&proof);
    }
}

#[test]
fn l1_descendant_repair_refuses_pre_cancel_and_interior_discovery_stop() {
    let mut fixture = Fixture::parsed();
    let interrupt = Arc::new(AtomicBool::new(true));
    fixture.executor.solve_interrupt = Some(Arc::clone(&interrupt));
    let original = fixture.pending();
    let mut proof = original.clone();
    fixture
        .executor
        .derive_propagated_value_assumptions(&mut proof, &fixture.originals);
    assert_eq!(proof, original);
    interrupt.store(false, Ordering::Relaxed);

    // Same entry body, deterministic progress seam: stop AFTER admission and
    // while walking the actual parsed after-roots. A later true response must
    // not turn this incomplete discovery into a publishable proof suffix.
    let calls = Cell::new(0usize);
    fixture
        .executor
        .derive_propagated_value_assumptions_with_candidates(
            &mut proof,
            &fixture.originals,
            &|_, _| {
                let call = calls.get() + 1;
                calls.set(call);
                call != 4
            },
        );
    assert_eq!(calls.get(), 4);
    assert_eq!(proof, original);
    fixture
        .executor
        .derive_propagated_value_assumptions(&mut proof, &fixture.originals);
    fixture.authenticate(&proof);
}
