// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact R29 source, observed at the real reconstruction failures. These are
//! construction regressions, not full original-model validation or acceptance.
//! A stopped/declined target is intentionally red, never an accepted Unknown.

use super::*;
use crate::portfolio::PreprocessSummary;
use crate::smt::ScopedSmtDeadline;
use crate::{CancellationToken, ChcParser};
use sha2::{Digest, Sha256};
use std::time::Duration;

const INPUT: &str = include_str!(concat!(
    env!("CARGO_MANIFEST_DIR"),
    "/tests/fixtures/model_checker_consumer_realloc_grow_original.smt2"
));

fn reconstruct_original(target_name: &'static str) {
    let deadline = Instant::now() + Duration::from_secs(20);
    let _deadline = ScopedSmtDeadline::install_until(deadline);
    let cancellation = CancellationToken::new();
    let _switches = crate::ab_switches::TestOverride::set(Default::default());
    assert_eq!(INPUT.len(), 311_060);
    assert_eq!(
        format!("{:x}", Sha256::digest(INPUT.as_bytes())),
        "0930146db6fc0c3e308d87dff805d02e20c4959e3b40c7a3c455e1ab636412d7"
    );
    assert_eq!(
        INPUT
            .lines()
            .filter(|line| line.starts_with("(rule "))
            .count(),
        104
    );
    let original = ChcParser::parse(INPUT).unwrap();
    assert_eq!(original.predicates().len(), 65);
    let target = original.lookup_predicate(target_name).unwrap();
    let original_sorts = original.get_predicate(target).unwrap().arg_sorts.clone();
    let summary = PreprocessSummary::build_bv_native_with_limits(
        original,
        false,
        Some(deadline),
        &cancellation,
    )
    .expect("bounded production BV-native preprocessing of the original R29 query");
    // These are the actual current trace's residual counts. A pipeline change
    // must update this regression deliberately, not fabricate an empty model
    // for a residual problem that still contains predicates or query clauses.
    assert_eq!(summary.transformed_problem.predicates().len(), 0);
    assert_eq!(summary.transformed_problem.clauses().len(), 0);
    let capture = CaptureGuard::install(target_name, deadline);
    let translated = summary
        .back_translator
        .translate_validity(Default::default());
    assert!(
        Instant::now() < deadline,
        "one original reconstruction deadline"
    );
    let observations = capture.take();
    assert!(
        !observations.is_empty(),
        "must observe the actual named stage"
    );
    for observation in &observations {
        assert!(observation.stage > 0);
        assert!(observation.definitions > 0);
        assert_eq!(observation.clause.body.predicates.len(), 1);
        assert!(observation.formula.node_count(65_537) <= 65_536);
    }
    let interpretation = translated.get(&target).expect("original named predicate");
    assert_eq!(
        interpretation
            .vars
            .iter()
            .map(|var| var.sort.clone())
            .collect::<Vec<_>>(),
        original_sorts
    );
    assert!(interpretation
        .formula
        .vars()
        .iter()
        .all(|var| interpretation.vars.contains(var)));
    // Do not infer Safe from this one interpretation or the empty residual:
    // every original clause and all 65 predicate interpretations still require
    // validation, with strict replay under the same original acceptance owner.
}

#[test]
#[ntest::timeout(60000)]
fn original_realloc_bb3_reconstructs_before_legacy_enumeration() {
    reconstruct_original("testcrate_0::chc_std_alloc_realloc_grow_full__bb3");
}

#[test]
#[ntest::timeout(60000)]
fn original_realloc_bb10_reconstructs_before_legacy_enumeration() {
    reconstruct_original("testcrate_0::chc_std_alloc_realloc_grow_full__bb10");
}
