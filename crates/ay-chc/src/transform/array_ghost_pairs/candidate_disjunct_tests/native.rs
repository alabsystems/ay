// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original quantified-source acceptance, not candidate-only proof claims.

use super::*;
use crate::quantified::{
    ArrayRange, ArrayRangeValue, ArrayRangeWrite, QuantifiedChcProblem, QuantifiedHornClause,
    UniversalPremise,
};
use ntest::timeout;
use std::time::Duration;

const WALL: Duration = Duration::from_secs(20);
const TERMS: usize = 128 * 1024 * 1024;

fn array() -> ChcSort {
    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)))
}

fn read(name: &str, index: u128) -> ChcExpr {
    ChcExpr::select(
        ChcExpr::var(ChcVar::new(name, array())),
        ChcExpr::BitVec(index, 64),
    )
}

fn fixture(second_expected: u128) -> QuantifiedChcProblem {
    let premise = UniversalPremise::array_range_write(
        ChcVar::new("i", ChcSort::BitVec(64)),
        ArrayRangeWrite {
            destination: ChcVar::new("d", array()),
            result: ChcVar::new("w", array()),
            range: ArrayRange::UnsignedHalfOpen {
                lower: Arc::new(ChcExpr::BitVec(1, 64)),
                upper: Arc::new(ChcExpr::BitVec(3, 64)),
            },
        },
        ArrayRangeValue::Fill(Arc::new(ChcExpr::BitVec(9, 8))),
    )
    .expect("exact typed unsigned partial fill");
    let mut declarations = ChcProblem::new();
    let predicate = declarations.declare_predicate("Written", vec![array()]);
    let w = ChcExpr::var(ChcVar::new("w", array()));
    let fact = HornClause::fact(
        ChcExpr::eq(read("d", 0), ChcExpr::BitVec(7, 8)),
        predicate,
        vec![w.clone()],
    );
    let bad = ChcExpr::Op(
        ChcOp::Or,
        vec![
            Arc::new(ChcExpr::not(ChcExpr::eq(
                read("w", 0),
                ChcExpr::BitVec(7, 8),
            ))),
            Arc::new(ChcExpr::not(ChcExpr::eq(
                read("w", 1),
                ChcExpr::BitVec(second_expected, 8),
            ))),
        ],
    );
    let query = HornClause::query(ClauseBody::new(vec![(predicate, vec![w])], Some(bad)));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(fact, vec![premise]),
            QuantifiedHornClause::new(query, Vec::new()),
        ],
    )
    .expect("full original typed source")
}

#[test]
#[timeout(30000)]
fn partial_fill_or_anchors_seal_and_recheck_every_original_clause_under_one_end() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    let token = CancellationToken::new();
    let source = fixture(9);
    let original = source.source_smtlib().to_owned();
    let certificate = crate::transform::array_ghost_pairs::certify::try_quantified_source(
        &source,
        end,
        &token,
        Some(TERMS),
    )
    .expect("both sufficient anchors must pass complete original certification");
    let obligations = certificate
        .replay_obligations(&source, end, &token)
        .expect("all original clauses");
    assert_eq!(obligations.len(), 2);
    assert_eq!(obligations[0].clause_index, 0);
    assert_eq!(obligations[1].clause_index, 1);
    assert!(obligations[0].smtlib.contains("(forall "));
    assert!(obligations[1].smtlib.contains("(or "));
    assert_eq!(source.source_smtlib(), original);
    assert!(certificate.recheck(&source, end, &token));
    assert!(Instant::now() < end);
}

#[test]
#[timeout(30000)]
fn one_false_or_property_withholds_safe_even_when_the_other_anchor_is_valid() {
    let end = Instant::now() + WALL;
    let _deadline = crate::smt::ScopedSmtDeadline::install_until(end);
    let token = CancellationToken::new();
    let source = fixture(8);
    let source_problem = source.source_problem();
    let proposed = candidates(source_problem, 1).expect("both untrusted proposals");
    assert_eq!(proposed.len(), 2);
    assert!(
        crate::transform::array_ghost_pairs::certify::try_quantified_source(
            &source,
            end,
            &token,
            Some(TERMS)
        )
        .is_none(),
        "a false second conjunct cannot inherit the first anchor's validity"
    );
    assert!(Instant::now() < end);
}
