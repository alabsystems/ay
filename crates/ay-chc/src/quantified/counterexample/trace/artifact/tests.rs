// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::counterexample::render_oracle as oracle;

mod fixtures;
mod native;
mod refusal;
mod values;

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

#[test]
fn prepared_wire_retains_exact_source_tree_and_all_assignments_without_sat_authority() {
    let token = CancellationToken::new();
    let (source, trace) = fixtures::scalar(&token);
    let wire = fixtures::wire(&source, &trace, &token);
    assert_eq!(wire.source, source.source_smtlib());
    assert_eq!(wire.functions, "(model)");
    assert_eq!(wire.steps.len(), 3);
    assert_eq!(wire.steps[0].clause_index, wire.steps[1].clause_index);
    assert_eq!(wire.steps[2].premises, vec![0, 1]);
    assert_eq!(
        wire.steps.iter().map(|s| s.bindings.len()).sum::<usize>(),
        4
    );
    let bytes = transport::encode(&wire, &control(&token)).unwrap();
    let parsed: wire::Wire = transport::decode(&bytes, &control(&token)).unwrap();
    let prepared = rebuild::prepare(&source, &parsed, &control(&token)).unwrap();
    assert_eq!(prepared.test_pins(), trace.replay_obligation());
    assert_eq!(oracle::models(prepared.test_pins()), vec![vec![0, 1, 0, 1]]);
    assert_eq!(transport::encode(&parsed, &control(&token)).unwrap(), bytes);
    assert_eq!(
        transport::digest(&bytes, &control(&token)).unwrap().len(),
        64
    );
}

#[test]
fn changed_assignment_with_recomputed_hash_is_data_not_a_replay_permit() {
    let token = CancellationToken::new();
    let (source, mut trace) = fixtures::scalar(&token);
    trace.bindings[0].value = SmtValue::BitVec(1, 2);
    fixtures::repin(&source, &mut trace, &token);
    let wire = fixtures::wire(&source, &trace, &token);
    // This is intentionally coherent attacker-controlled DATA, including a
    // recomputed pin digest. Preparation must not itself mint sealed evidence.
    let prepared = rebuild::prepare(&source, &wire, &control(&token)).unwrap();
    assert_eq!(
        oracle::models(prepared.test_pins()),
        [] as [std::vec::Vec<u64>; 0]
    );
    assert_eq!(prepared.test_pins(), trace.replay_obligation());
}

#[test]
fn bodyless_query_without_locals_roundtrips_without_invented_values() {
    let token = CancellationToken::new();
    let source =
        QuantifiedChcProblem::parse_smtlib("(set-logic HORN) (assert (=> true false)) (check-sat)")
            .unwrap();
    let trace = fixtures::unchecked(&source, vec![0], vec![vec![]], Vec::new(), &token);
    let wire = fixtures::wire(&source, &trace, &token);
    assert!(wire.steps[0].bindings.is_empty());
    let prepared = rebuild::prepare(&source, &wire, &control(&token)).unwrap();
    assert_eq!(
        oracle::models(prepared.test_pins()),
        vec![Vec::<u64>::new()]
    );
}

#[test]
fn caller_source_not_reparsed_wire_controls_binders_and_fixedpoint_provenance() {
    let token = CancellationToken::new();
    let (source, trace) = fixtures::scalar(&token);
    let wire = fixtures::wire(&source, &trace, &token);
    let reparsed = QuantifiedChcProblem::parse_smtlib(&wire.source).unwrap();
    assert_ne!(source.source_smtlib(), reparsed.source_smtlib());
    assert!(rebuild::prepare(&reparsed, &wire, &control(&token)).is_none());
    assert!(rebuild::prepare(&source, &wire, &control(&token)).is_some());
    let fixed = QuantifiedChcProblem::parse_smtlib(
        "(set-logic HORN) (declare-rel Bad ()) (rule Bad) (query Bad)",
    )
    .unwrap();
    assert!(fixed.source_view().is_fixedpoint_format());
    let reparsed = QuantifiedChcProblem::parse_smtlib(fixed.source_smtlib()).unwrap();
    assert!(!reparsed.source_view().is_fixedpoint_format());
    assert_ne!(fixed.source_smtlib(), reparsed.source_smtlib());
}
