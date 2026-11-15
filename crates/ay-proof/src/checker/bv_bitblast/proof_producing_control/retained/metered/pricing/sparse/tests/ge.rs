// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn app(terms: &mut TermStore, head: &str, args: &[TermId], sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(head), args, sort)
}

fn ordinary() -> (TermStore, TermId) {
    let (mut terms, read_equal) = fixture(8);
    let word = terms.mk_var("guard-word", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 64);
    let guard = app(&mut terms, "bvuge", &[word, zero], Sort::Bool);
    let negative = terms.mk_not_raw(read_equal);
    let root = app(&mut terms, "and", &[guard, negative], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    (terms, clause)
}

#[test]
fn typed_ge_ordinary_sources_get_complete_prepaid_bounds_for_both_unsigned_heads() {
    let (mut terms, root) = fixture(8);
    let a = terms.mk_var("guard", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 64);
    for head in ["bvuge", "bvule"] {
        let guard = app(&mut terms, head, &[a, zero], Sort::Bool);
        let guarded = app(&mut terms, "and", &[root, guard], Sort::Bool);
        assert!(cost(&terms, guarded).is_some());
    }
    let (terms, clause) = ordinary();
    assert!(cost(&terms, clause).is_some());
    let mut poll = || true;
    Control::new(proof().resolution.deadline.unwrap(), &mut poll)
        .run(|control| {
            assert!(matches!(
                source_route(&terms, &[clause], control)?,
                SourceRoute::Ordinary
            ));
            Ok(())
        })
        .unwrap();
}

#[test]
fn ge_syntax_products_are_prepaid_before_any_expensive_original_matching() {
    let (mut terms, root) = fixture(8);
    let a = terms.mk_var("guard", Sort::bitvec(64));
    let zero = terms.mk_bitvec(0.into(), 64);
    let guard = app(&mut terms, "bvuge", &[a, zero], Sort::Bool);
    let many = app(&mut terms, "and", &[guard; 128], Sort::Bool);
    let all = app(&mut terms, "and", &[many, root], Sort::Bool);
    let clause = terms.mk_not_raw(all);
    let mut positive = 0;
    assert!(plan(&terms, &[clause], &proof(), &mut |work, _| {
        positive += usize::from(work > 0);
        true
    })
    .unwrap()
    .is_none()); // useful original source envelope, never raised
    assert!(positive > 0);
}

#[test]
fn ge_route_census_refusal_is_sticky_for_every_checkpoint_on_the_original_owner() {
    let (terms, clause) = ordinary();
    let mut total = 0;
    assert!(plan(&terms, &[clause], &proof(), &mut |_, _| {
        total += 1;
        true
    })
    .unwrap()
    .is_some());
    for stop in 1..=total {
        let mut calls = 0;
        assert!(matches!(
            plan(&terms, &[clause], &proof(), &mut |_, _| {
                calls += 1;
                calls != stop
            }),
            Err(ProofCheckError::ResourceLimit)
        ));
        assert_eq!(calls, stop);
    }
}

#[test]
fn disjoint_candidate_upper_bound_counts_raw_branch_products_and_caps_257th_header() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::bitvec(64));
    let b = terms.mk_var("b", Sort::bitvec(64));
    let ge = app(&mut terms, "bvuge", &[a, b], Sort::Bool);
    let left = app(&mut terms, "and", &[ge; 16], Sort::Bool);
    let right = app(&mut terms, "and", &[ge; 17], Sort::Bool);
    let pair = app(&mut terms, "or", &[left, right], Sort::Bool);
    let root = app(&mut terms, "and", &[pair], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    assert_eq!(
        crate::checker::bv_bitblast::disjoint::candidate_bound(&terms, &[clause]),
        256
    );
    let root = app(&mut terms, "and", &[ge], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    assert_eq!(
        crate::checker::bv_bitblast::disjoint::candidate_bound(&terms, &[clause]),
        0
    );
}

fn outside(last_offset: u128) -> (TermStore, TermId) {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let array = Sort::array(word.clone(), Sort::bitvec(8));
    let stack = terms.mk_var("stack", word.clone());
    let observe = terms.mk_var("observe", word.clone());
    let size = terms.mk_bitvec(1.into(), 9);
    let offset = terms.mk_bitvec(last_offset.into(), 9);
    let start = app(&mut terms, "bvsub", &[stack, size], word.clone());
    let at = app(&mut terms, "bvadd", &[start, offset], word);
    let guard = app(&mut terms, "bvuge", &[stack, size], Sort::Bool);
    let below = app(&mut terms, "bvult", &[observe, start], Sort::Bool);
    let above = app(&mut terms, "bvuge", &[observe, stack], Sort::Bool);
    let out = app(&mut terms, "or", &[below, above], Sort::Bool);
    let not_out = terms.mk_not_raw(out);
    let base = terms.mk_var("memory", array.clone());
    let value = terms.mk_var("value", Sort::bitvec(8));
    let stored = app(&mut terms, "store", &[base, at, value], array);
    let after = app(&mut terms, "select", &[stored, observe], Sort::bitvec(8));
    let before = app(&mut terms, "select", &[base, observe], Sort::bitvec(8));
    let equal = app(&mut terms, "=", &[after, before], Sort::Bool);
    let property = app(&mut terms, "or", &[not_out, equal], Sort::Bool);
    let negative = terms.mk_not_raw(property);
    let root = app(&mut terms, "and", &[guard, negative], Sort::Bool);
    let clause = terms.mk_not_raw(root);
    (terms, clause)
}

#[test]
fn failed_outside_address_or_write_matching_still_prepays_every_syntactic_target() {
    let (terms, clause) = outside(1); // source syntax matches; write is out-of-frame
    assert!(
        crate::checker::bv_bitblast::proof_producing_control::OutsideFrameShape::recognize(
            &terms,
            &[clause]
        )
        .is_none()
    );
    let mut debits = Vec::new();
    let work = outside_frame::matching_work(&terms, &[clause], usize::MAX, &mut |work, _| {
        debits.push(work);
        true
    })
    .unwrap()
    .unwrap();
    assert_eq!(debits.len(), 1); // syntax P before any target matching
    assert!(work >= debits[0] + 32768 * 256);
    let mut calls = 0;
    assert!(matches!(
        outside_frame::matching_work(&terms, &[clause], usize::MAX, &mut |_, _| {
            calls += 1;
            false
        }),
        Err(ProofCheckError::ResourceLimit)
    ));
    assert_eq!(calls, 1);
}

#[test]
fn outside_route_is_not_reclassified_as_ordinary_by_numeric_cost_eligibility() {
    let (terms, clause) = outside(0);
    // A deliberately large T envelope may decline even this small fixture.
    // Eligibility is not permission to reclassify the original route.
    if let Some(cost) = cost(&terms, clause) {
        assert!(cost.work + cost.name_work < 16 * proof().max_leaf_name_bytes);
    }
    let mut poll = || true;
    Control::new(proof().resolution.deadline.unwrap(), &mut poll)
        .run(|control| {
            assert!(matches!(
                source_route(&terms, &[clause], control)?,
                SourceRoute::Outside(_)
            ));
            Ok(())
        })
        .unwrap();
}

#[test]
fn original_disjoint_candidate_remains_selected_even_when_its_cost_is_affordable() {
    let mut terms = TermStore::new();
    let word = Sort::bitvec(9);
    let a = terms.mk_var("a", word.clone());
    let b = terms.mk_var("b", word.clone());
    let size = terms.mk_bitvec(1.into(), 9);
    let end_a = app(&mut terms, "bvadd", &[a, size], word.clone());
    let end_b = app(&mut terms, "bvadd", &[b, size], word.clone());
    let after_b = app(&mut terms, "bvuge", &[a, end_b], Sort::Bool);
    let after_a = app(&mut terms, "bvuge", &[b, end_a], Sort::Bool);
    let separate = app(&mut terms, "or", &[after_b, after_a], Sort::Bool);
    let bound = terms.mk_bitvec(511.into(), 9);
    let nowrap_a = app(&mut terms, "bvule", &[a, bound], Sort::Bool);
    let nowrap_b = app(&mut terms, "bvule", &[b, bound], Sort::Bool);
    let array = terms.mk_var("memory", Sort::array(word, Sort::bitvec(8)));
    let read = app(&mut terms, "select", &[array, b], Sort::bitvec(8));
    let equal = app(&mut terms, "=", &[read, read], Sort::Bool);
    let negative = terms.mk_not_raw(equal);
    let root = app(
        &mut terms,
        "and",
        &[separate, nowrap_a, nowrap_b, negative],
        Sort::Bool,
    );
    let clause = terms.mk_not_raw(root);
    assert!(cost(&terms, clause).is_some());
    let mut poll = || true;
    Control::new(proof().resolution.deadline.unwrap(), &mut poll)
        .run(|control| {
            assert!(matches!(
                source_route(&terms, &[clause], control)?,
                SourceRoute::Disjoint(_)
            ));
            Ok(())
        })
        .unwrap();
}
