// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::CancellationToken;
use std::time::Duration;

fn fixture(declarations: &str, sort: &str) -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(&format!(
        "(set-logic HORN) {declarations}
         (declare-fun P ({sort}) Bool)
         (assert (forall ((x {sort})) (P x)))
         (assert (forall ((x {sort})) (=> (P x) false))) (check-sat)"
    ))
    .unwrap()
}

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(60), token)
}

#[test]
fn wide_array_state_uses_source_observations_without_widening_the_legacy_spec() {
    let token = CancellationToken::new();
    for width in [65, 72, 128, 136, crate::MAX_BITVECTOR_WIDTH] {
        let problem = fixture("", &format!("(Array (_ BitVec {width}) (_ BitVec 8))"));
        assert_eq!(source(&problem, &control(&token)), Some(Shape::Wide));
        assert_eq!(
            super::super::requires_observations(&problem, &control(&token)),
            Some(true)
        );
        assert!(
            super::super::super::GhostPairSpec::analyze(problem.source_problem(), 1).is_empty()
        );
    }
    for width in [72, 128, 136] {
        let problem = fixture("", &format!("(Array (_ BitVec 64) (_ BitVec {width}))"));
        assert_eq!(source(&problem, &control(&token)), Some(Shape::Wide));
    }
}

#[test]
fn unused_wide_declarations_and_scalar_only_sources_keep_their_existing_route() {
    let token = CancellationToken::new();
    let declarations = "(declare-fun unused ((_ BitVec 136)) (_ BitVec 136))
        (declare-datatype Unused ((mkUnused (table (Array (_ BitVec 136) (_ BitVec 64))))))";
    for sort in ["(_ BitVec 136)", "(Array (_ BitVec 64) (_ BitVec 8))"] {
        let problem = fixture(declarations, sort);
        assert_eq!(source(&problem, &control(&token)), Some(Shape::Flat));
    }
    let narrow = fixture(
        "",
        "(Array (_ BitVec 64) (Array (_ BitVec 64) (_ BitVec 8)))",
    );
    assert_eq!(source(&narrow, &control(&token)), Some(Shape::Composite));
    let wide = fixture(
        "",
        "(Array (_ BitVec 64) (Array (_ BitVec 136) (_ BitVec 8)))",
    );
    assert_eq!(source(&wide, &control(&token)), Some(Shape::Wide));
}

#[test]
fn source_shape_scan_retains_observed_cancellation_and_exhausted_budget() {
    let problem = fixture("", "(Array (_ BitVec 136) (_ BitVec 8))");
    let token = CancellationToken::new();
    let stopped = control(&token);
    token.cancel();
    assert!(source(&problem, &stopped).is_none());
    token.reset();
    assert!(source(&problem, &stopped).is_none());
    assert_eq!(source(&problem, &control(&token)), Some(Shape::Wide));
    let exhausted = control(&token);
    assert!(exhausted.bytes(usize::MAX).is_none());
    assert!(source(&problem, &exhausted).is_none());
}
