// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn address_fixture(offset: u32) -> (TermStore, TermId, TermId) {
    let mut terms = TermStore::new();
    let base = terms.mk_var("base", Sort::bitvec(64));
    let value = terms.mk_bitvec(offset.into(), 64);
    let address = terms.mk_app(Symbol::named("bvadd"), [base, value], Sort::bitvec(64));
    (terms, base, address)
}

#[test]
fn repeated_sparse_addresses_charge_actual_new_work_and_keep_the_mask() {
    let (terms, base, address) = address_fixture(300);
    let mut lowerer = ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(3));
    let first = lowerer.sparse_address(address, 511, 0).unwrap();
    assert_eq!((first.base, first.offset), (Some(base), 300));
    assert_eq!(lowerer.exact_finite_array_work, 3);
    let warm = lowerer.sparse_address(address, 511, 0).unwrap();
    assert_eq!((warm.base, warm.offset), (Some(base), 300));
    assert_eq!(lowerer.exact_finite_array_work, 4);
    let other_mask = lowerer.sparse_address(address, 255, 0).unwrap();
    assert_eq!((other_mask.base, other_mask.offset), (Some(base), 44));
    assert_eq!(lowerer.exact_finite_array_work, 7);
    lowerer.exact_finite_array_work = super::super::MAX_EXACT_FINITE_ARRAY_WORK - 1;
    lowerer.sparse_address(address, 511, 0).unwrap();
    assert!(lowerer.sparse_address(address, 511, 0).is_err());
    assert!(lowerer.resource_exhausted);
}

#[test]
fn cached_sparse_address_height_cannot_hide_deep_requests() {
    let (terms, _, address) = address_fixture(1);
    let mut lowerer = ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(3));
    lowerer
        .sparse_address(address, u64::MAX as u128, 0)
        .unwrap();
    lowerer
        .sparse_address(address, u64::MAX as u128, MAX_ADDRESS_DEPTH - 1)
        .unwrap();
    let error = lowerer
        .sparse_address(address, u64::MAX as u128, MAX_ADDRESS_DEPTH)
        .err()
        .unwrap();
    assert!(error.contains("depth exceeded"));
    assert!(lowerer.resource_exhausted);
}

#[test]
fn cached_sparse_address_observes_live_stop_and_new_arena_identity() {
    let (terms, _, address) = address_fixture(5);
    let mut stop = || false;
    let mut lowerer = ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(3));
    assert_eq!(
        lowerer
            .sparse_address(address, u128::MAX, 0)
            .unwrap()
            .offset,
        5
    );
    lowerer.keep_going = Some(&mut stop);
    assert!(lowerer.sparse_address(address, u128::MAX, 0).is_err());
    assert!(lowerer.cancelled);
    let (other, _, other_address) = address_fixture(6);
    assert_eq!(
        address, other_address,
        "same numeric TermId in a distinct source arena"
    );
    let mut fresh = ProofProducingLowerer::new(&other, Instant::now() + Duration::from_secs(3));
    assert!(fresh.sparse_addresses.entries.is_empty());
    assert_eq!(
        fresh
            .sparse_address(other_address, u128::MAX, 0)
            .unwrap()
            .offset,
        6
    );
}

#[test]
fn sparse_address_memo_retains_opaque_terms_and_has_a_hard_entry_bound() {
    let mut terms = TermStore::new();
    let base = terms.mk_var("base", Sort::bitvec(64));
    let other = terms.mk_var("other", Sort::bitvec(64));
    let mixed = terms.mk_app(Symbol::named("bvadd"), [base, other], Sort::bitvec(64));
    let variables: Vec<_> = (0..MAX_PROOF_PRODUCING_TERM_NODES)
        .map(|i| terms.mk_var(format!("p{i}"), Sort::bitvec(64)))
        .collect();
    let mut lowerer = ProofProducingLowerer::new(&terms, Instant::now() + Duration::from_secs(3));
    let opaque = lowerer.sparse_address(mixed, u64::MAX as u128, 0).unwrap();
    assert_eq!((opaque.base, opaque.offset), (Some(mixed), 0));
    for &term in &variables[..MAX_PROOF_PRODUCING_TERM_NODES - 3] {
        lowerer.sparse_address(term, u64::MAX as u128, 0).unwrap();
    }
    assert_eq!(
        lowerer.sparse_addresses.entries.len(),
        MAX_PROOF_PRODUCING_TERM_NODES
    );
    assert!(lowerer
        .sparse_address(
            variables[MAX_PROOF_PRODUCING_TERM_NODES - 3],
            u64::MAX as u128,
            0
        )
        .is_err());
    assert_eq!(
        lowerer.sparse_addresses.entries.len(),
        MAX_PROOF_PRODUCING_TERM_NODES
    );
    assert!(lowerer.resource_exhausted);
}
