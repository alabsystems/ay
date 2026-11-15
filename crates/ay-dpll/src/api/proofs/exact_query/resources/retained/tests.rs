// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::api::{Logic, Sort};
use ay_proof::RetainedProofTransportLimits;
use std::time::Duration;

mod authority;
mod controls;
mod phases;
mod work;

const BOOLEAN: &str = "(declare-const p Bool) (assert p) (assert (not p))";
const FOLDED: &str = "(declare-const x Int) (assert (and (>= x 0) (not (> x 10)) (> x 10)))";
const PINNED: &str =
    "(declare-const x (_ BitVec 16)) (assert (= x #x9c40)) (assert (<= (* (ubv_to_int x) 2) 65535))";
const DATATYPE: &str =
    "(declare-datatype D ((a) (b))) (declare-const x D) (assert (= x a)) (assert (= x b))";

enum Presentation {
    StrictWire,
    NativeBundle,
}

fn parsed(
    logic: Logic,
    source: &str,
    presentation: Presentation,
) -> (Solver, ExactSmtlibQueryBinding) {
    let mut solver = Solver::try_new(logic).unwrap();
    solver.set_produce_proofs(true);
    if matches!(presentation, Presentation::StrictWire) {
        solver
            .try_set_option(":check-proofs-strict", "true")
            .unwrap();
    }
    let binding = solver
        .parse_smtlib2_with_exact_query_binding(source)
        .unwrap();
    (solver, binding)
}

fn solved(source: &str) -> (Solver, ExactSmtlibQueryBinding) {
    let (mut solver, binding) = parsed(Logic::All, source, Presentation::StrictWire);
    assert!(solver.check_sat().is_unsat());
    (solver, binding)
}

fn deadline() -> Instant {
    Instant::now() + Duration::from_secs(300)
}

fn limits() -> RetainedProofTransportLimits {
    RetainedProofTransportLimits {
        max_json_bytes: 16 * 1024 * 1024,
        max_storage_bytes: 64 * 1024 * 1024,
        max_work: 16 * 1024 * 1024,
    }
}

fn trace(solver: &Solver, binding: &ExactSmtlibQueryBinding) -> Vec<(usize, usize)> {
    let mut charges = Vec::new();
    assert!(solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            binding,
            deadline(),
            &mut |work, bytes| {
                charges.push((work, bytes));
                true
            },
        )
        .unwrap()
        .is_some());
    charges
}

fn totals(charges: &[(usize, usize)]) -> (usize, usize) {
    charges.iter().fold((0usize, 0usize), |(w, b), (dw, db)| {
        (w.checked_add(*dw).unwrap(), b.checked_add(*db).unwrap())
    })
}

#[test]
#[ntest::timeout(60000)]
fn retained_exact_export_preserves_original_assumptions_and_typed_replay() {
    for (logic, source, presentation) in [
        (Logic::All, BOOLEAN, Presentation::StrictWire),
        (Logic::All, FOLDED, Presentation::StrictWire),
        (Logic::QfUfbvlia, PINNED, Presentation::StrictWire),
        (Logic::All, DATATYPE, Presentation::NativeBundle),
    ] {
        let (mut solver, binding) = parsed(logic, source, presentation);
        assert!(solver.check_sat().is_unsat());
        let legacy = solver
            .export_last_unsat_bundle_for_exact_query(&binding)
            .unwrap();
        let original_deadline = deadline();
        let mut ledger = |_, _| true;
        let artifact = solver
            .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
                &binding,
                original_deadline,
                &mut ledger,
            )
            .unwrap()
            .unwrap();
        assert_eq!(artifact.schema(), "ay.proofbundle/v6");
        assert_eq!(
            artifact.obligation_assertions(),
            legacy.obligation_assertions
        );
        let second_consumer = artifact
            .replay_exact_with_resource_control(original_deadline, &mut ledger)
            .unwrap();
        assert!(second_consumer.quality.is_complete());
        assert_eq!(
            second_consumer.assume_terms,
            artifact.obligation_assertions()
        );
        let bytes = artifact
            .encode_with_resource_control(limits(), original_deadline, &mut ledger)
            .unwrap();
        let document: serde_json::Value = serde_json::from_slice(&bytes).unwrap();
        assert_eq!(document["schema"], "ay.proofbundle/v6");
        assert!(document.get("retained").is_some());
        assert_eq!(legacy.schema, "ay.proofbundle/v5");
    }
}

#[test]
fn folded_original_source_ids_are_not_replaced_by_canonical_parse_roots() {
    let (solver, binding) = solved(FOLDED);
    let artifact = solver
        .export_last_unsat_retained_bundle_for_exact_query_with_resource_control(
            &binding,
            deadline(),
            &mut |_, _| true,
        )
        .unwrap()
        .unwrap();
    assert_ne!(
        artifact.obligation_assertions(),
        binding
            .assertions()
            .iter()
            .map(|term| term.id())
            .collect::<Vec<_>>(),
    );
    assert!(!artifact.obligation_assertions().is_empty());
}
