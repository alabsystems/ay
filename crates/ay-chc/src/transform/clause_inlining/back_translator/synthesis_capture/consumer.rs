// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::portfolio::PreprocessSummary;
use crate::smt::ScopedSmtDeadline;
use crate::transform::ClauseInliner;
use crate::{CancellationToken, ChcParser, ChcSort};
use sha2::{Digest, Sha256};
use std::time::Duration;

const INPUT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/model_checker_consumer_arith_equal_original.smt2"
));

#[test]
#[ntest::timeout(60000)]
fn original_named_reconstruction_closes_before_legacy_enumeration() {
    assert_eq!(
        format!("{:x}", Sha256::digest(INPUT.as_bytes())),
        "7173c651e75ac70e6770e01b1a910435c430f986742eb5f2dabc0a9d46239e48"
    );
    let _switches = crate::ab_switches::TestOverride::set(Default::default());
    let deadline = Instant::now() + Duration::from_secs(30);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let cancellation = CancellationToken::new();
    let original = ChcParser::parse(INPUT).unwrap();
    let target = original.lookup_predicate("main__bb16").unwrap();
    let sorts = original.get_predicate(target).unwrap().arg_sorts.clone();
    assert_eq!(
        sorts,
        [
            ChcSort::BitVec(32),
            ChcSort::Bool,
            ChcSort::BitVec(32),
            ChcSort::Bool,
            ChcSort::BitVec(32),
            ChcSort::Bool,
            ChcSort::Bool,
        ]
    );
    let summary = PreprocessSummary::build_bv_native_with_limits(
        original,
        false,
        Some(deadline),
        &cancellation,
    )
    .expect("same bounded BV-native preprocessing as the original query");
    assert_eq!(summary.transformed_problem.predicates().len(), 1);
    assert_eq!(summary.transformed_problem.clauses().len(), 8);
    assert_eq!(
        summary.transformed_problem.predicates()[0].name,
        "main__bb11"
    );

    // Materialize the real survivor candidate, not a fabricated invariant.
    // This does not establish that it satisfies the residual query clauses.
    let survivor = ClauseInliner::capture_acyclic_survivor_until(
        &summary.transformed_problem,
        deadline,
        &cancellation,
    )
    .unwrap()
    .unwrap();
    let candidate = survivor
        .materialize_until(deadline, &cancellation)
        .unwrap()
        .unwrap();
    let capture = CaptureGuard::install("main__bb16", deadline);

    // Earlier successful legacy projections remain enabled and consume this
    // SAME deadline. The observer asserts only at the named definition, before
    // its legacy enumeration; no earlier result or failure is replaced/skipped.
    let translated = summary.back_translator.translate_validity(candidate);
    assert!(Instant::now() < deadline, "shared reconstruction deadline");
    let observations = capture.take();
    assert_eq!(observations.len(), 1, "must observe the actual named stage");
    let observation = &observations[0];
    assert!(observation.stage > 0);
    assert_eq!(observation.definitions, 10);
    assert_eq!(observation.clause.body.predicates.len(), 1);
    assert_eq!(
        observation
            .keep
            .iter()
            .map(|var| var.sort.clone())
            .collect::<Vec<_>>(),
        sorts
    );
    assert!(observation.formula.node_count(65_537) <= 65_536);
    let interpretation = translated.get(&target).expect("original named predicate");
    assert!(interpretation
        .formula
        .vars()
        .iter()
        .all(|var| interpretation.vars.contains(var)));
    // Even when this construction regression passes, original-clause model
    // validation and strict replay remain separate, mandatory acceptance gates.
}
