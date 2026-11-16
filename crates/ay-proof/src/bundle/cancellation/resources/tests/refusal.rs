// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use std::cell::Cell;
use std::panic::{catch_unwind, AssertUnwindSafe};

#[test]
fn every_checkpoint_refuses_stickily_with_fresh_retry() {
    for bundle in [contradiction(false), datatype(), skolem()] {
        let before = serde_json::to_vec(&bundle).unwrap();
        let expected = trace(&bundle);
        for stop in 1..=expected.len() {
            let mut actual = Vec::new();
            let result = re_check_bundle_strict_with_resource_control(&bundle, &mut |w, b| {
                actual.push((w, b));
                actual.len() != stop
            });
            assert_resource(result);
            assert_eq!(actual, expected[..stop]);
        }
        assert_eq!(serde_json::to_vec(&bundle).unwrap(), before);
        assert!(bounded(&bundle, totals(&expected)).is_ok());
    }
}

/// #completed-check-accepted: once the operation has returned, the caller is
/// not consulted again, so a refusal it would give now cannot replace the
/// completed result.
#[test]
fn no_control_poll_follows_a_completed_operation() {
    struct Dropped<'a>(&'a Cell<bool>);
    impl Drop for Dropped<'_> {
        fn drop(&mut self) {
            self.0.set(true);
        }
    }
    let destroyed = Cell::new(false);
    let mut calls = 0;
    let mut progress = |work, bytes| {
        calls += 1;
        assert_eq!((work, bytes), (0, 0));
        !destroyed.get()
    };
    let result = ResourceControl {
        progress: &mut progress,
        refused: false,
    }
    .run(|_| {
        let _temporary = Dropped(&destroyed);
        Ok(17)
    });
    assert!(destroyed.get());
    assert!(matches!(result, Ok(17)));
    assert_eq!(calls, 1);
}

#[test]
fn callback_panic_cannot_be_laundered_by_an_inner_catching_operation() {
    let calls = Cell::new(0);
    let mut progress = |_, _| {
        calls.set(calls.get() + 1);
        assert!(calls.get() != 2, "expected callback panic");
        true
    };
    let result = ResourceControl {
        progress: &mut progress,
        refused: false,
    }
    .run(|progress| {
        assert!(catch_unwind(AssertUnwindSafe(|| progress(1, 1))).is_err());
        assert!(
            !progress(0, 0),
            "the caught panic must leave refusal latched"
        );
        Ok(())
    });
    assert!(matches!(result, Err(ProofCheckError::ResourceLimit)));
    assert_eq!(calls.get(), 2);
    let bundle = contradiction(false);
    assert!(bounded(&bundle, totals(&trace(&bundle))).is_ok());
}

#[test]
fn malformed_proofs_keep_their_errors_and_schema_copy_refusal_precedes_allocation() {
    let base = contradiction(false);
    let mut schema = base.clone();
    schema.schema = "wrong-schema".repeat(4096);
    let mut missing_root = base.clone();
    missing_root.steps[0] = ProofStep::Assume(TermId::SENTINEL);
    let mut wrong_sort = base.clone();
    wrong_sort.term_entries[base.obligation_assertions[0].index()].1 = Sort::Int;
    let mut unauthorized = base.clone();
    unauthorized.obligation_assertions = vec![base.true_term.unwrap()];
    let mut missing_terminal = base.clone();
    missing_terminal.steps.pop();
    let mut trust = base.clone();
    trust.steps.push(ProofStep::Step {
        rule: AletheRule::Trust,
        clause: vec![],
        premises: vec![],
        args: vec![],
    });
    for bundle in [
        schema,
        missing_root,
        wrong_sort,
        unauthorized,
        missing_terminal,
        trust,
    ] {
        let expected = oracle::recheck(&bundle);
        assert!(expected.is_err());
        assert_same(
            expected,
            re_check_bundle_strict_with_resource_control(&bundle, &mut |_, _| true),
        );
        let mut calls = 0;
        assert_resource(re_check_bundle_strict_with_resource_control(
            &bundle,
            &mut |_, _| {
                calls += 1;
                false
            },
        ));
        assert_eq!(calls, 1, "entry refusal precedes schema/proof inspection");
    }
    let mut schema = base;
    schema.schema = "copy-budget".repeat(4096);
    let mut debits = Vec::new();
    assert_resource(re_check_bundle_strict_with_resource_control(
        &schema,
        &mut |w, b| {
            debits.push((w, b));
            b == 0
        },
    ));
    assert_eq!(debits.len(), 3);
    assert_eq!(debits[2].1, schema.schema.len() + PROOF_BUNDLE_SCHEMA.len());
}
