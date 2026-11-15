// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;

#[test]
fn original_entry_refusal_precedes_even_missing_source_lookup() {
    let f = Fixture::new(8, 24);
    let mut calls = 0;
    let mut progress = |_, _| {
        calls += 1;
        false
    };
    assert_eq!(
        Reference::build(&f.terms, TermId::SENTINEL, &mut progress).err(),
        Some(ReferenceError::Resource)
    );
    assert_eq!(calls, 1);
}

#[test]
fn owned_node_payload_is_admitted_before_the_first_graph_allocation() {
    let f = Fixture::new(8, 24);
    let mut payload_requests = 0;
    let mut progress = |_, bytes| {
        if bytes == 0 {
            true
        } else {
            payload_requests += 1;
            false
        }
    };
    assert_eq!(
        Reference::build(&f.terms, f.source, &mut progress).err(),
        Some(ReferenceError::Resource)
    );
    assert_eq!(payload_requests, 1);
}

#[test]
fn final_success_and_normal_source_refusal_keep_the_original_poll() {
    let f = Fixture::new(8, 24);
    for source in [f.source, TermId::SENTINEL] {
        let mut count = 0;
        let mut progress = |_, _| {
            count += 1;
            true
        };
        let healthy = Reference::build(&f.terms, source, &mut progress);
        drop(healthy);
        drop(progress);
        assert!(count > 1);
        let mut remaining = count - 1;
        let mut progress = |_, _| {
            if remaining == 0 {
                false
            } else {
                remaining -= 1;
                true
            }
        };
        assert_eq!(
            Reference::build(&f.terms, source, &mut progress).err(),
            Some(ReferenceError::Resource)
        );
    }
}

#[test]
fn same_owner_is_retained_for_model_walk_and_refusal_is_local_sticky() {
    let f = Fixture::new(8, 24);
    let live = Cell::new(true);
    let mut progress = |_, _| live.get();
    let mut reference =
        Reference::build(&f.terms, f.source, &mut progress).expect("original owner");
    let inputs = f.assignments(raw(0, 127, 1), raw(1, 127, 1), 0);
    reference.evaluate(&inputs).expect("same owner live");
    live.set(false);
    assert_eq!(
        reference.evaluate(&inputs).err(),
        Some(ReferenceError::Resource)
    );
    live.set(true); // Deliberately hostile callback revival cannot revive this program.
    assert_eq!(
        reference.evaluate(&inputs).err(),
        Some(ReferenceError::Resource)
    );
    // A NEW adapter's sticky transaction state remains the external owner's
    // obligation; this control does not claim cross-adapter refusal closure.
}

#[test]
fn cumulative_original_work_is_never_renewed_between_source_and_graph_steps() {
    let f = Fixture::new(8, 24);
    let mut remaining = 200usize;
    let mut progress = |work, _| {
        if work > remaining {
            false
        } else {
            remaining -= work;
            true
        }
    };
    assert_eq!(
        Reference::build(&f.terms, f.source, &mut progress).err(),
        Some(ReferenceError::Resource)
    );
    assert!(remaining < 200);
}

#[test]
fn hostile_precision_refuses_the_owned_envelope_before_any_graph_allocation() {
    let f = Fixture::new(8, 2_000_000);
    let mut allocations = 0;
    let mut progress = |_, bytes| {
        if bytes > 0 {
            allocations += 1;
        }
        true
    };
    assert_eq!(
        Reference::build(&f.terms, f.source, &mut progress).err(),
        Some(ReferenceError::Resource)
    );
    assert_eq!(
        allocations, 0,
        "local refusal is not a borrowed-owner storage grant"
    );
}

#[test]
fn unsupported_rounding_source_is_checked_before_precision_scaled_storage() {
    let mut f = Fixture::new(8, 2_000_000);
    let TermData::App(_, args) = f.terms.get(f.source) else {
        panic!("mul fixture");
    };
    let args = args.clone();
    let rm = f.terms.mk_app(
        Symbol::named("unknown_actual_rm"),
        [],
        Sort::Uninterpreted("RoundingMode".into()),
    );
    let source = f.terms.mk_app(
        Symbol::named("fp.mul"),
        [rm, args[1], args[2]],
        Sort::FloatingPoint(8, 2_000_000),
    );
    let mut allocations = 0;
    let mut progress = |_, bytes| {
        if bytes > 0 {
            allocations += 1;
        }
        true
    };
    assert_eq!(
        Reference::build(&f.terms, source, &mut progress).err(),
        Some(ReferenceError::Source)
    );
    assert_eq!(allocations, 0);
}
