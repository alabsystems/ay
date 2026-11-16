// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod exact_division_memo;
mod exact_division_withheld;
mod memo;
mod reader;
mod refusal;
mod signed_literal_authority;
mod speculative;

#[test]
fn caught_callback_panic_keeps_this_attempt_refused() {
    use std::panic::{catch_unwind, AssertUnwindSafe};
    let mut calls = 0;
    let result = semantic_control::run(
        &mut |_, _| {
            calls += 1;
            assert_ne!(calls, 2, "injected callback panic");
            true
        },
        |poll| {
            assert!(catch_unwind(AssertUnwindSafe(&mut *poll)).is_err());
            poll()
        },
    );
    assert_eq!(result, Err(ProofCheckError::ResourceLimit));
    assert_eq!(calls, 2, "a caught panic must not resurrect the callback");
}

#[derive(Clone, Copy)]
enum Lane {
    Boolean,
    BitBlast,
    Gate,
}

impl Lane {
    fn kind(self) -> TheoryLemmaKind {
        match self {
            Self::Boolean => TheoryLemmaKind::BoolTautology,
            Self::BitBlast => TheoryLemmaKind::BvBitBlast,
            Self::Gate => TheoryLemmaKind::BvBitBlastGate {
                gate_type: BvGateType::Add,
                width: 1,
            },
        }
    }

    fn run(
        self,
        terms: &TermStore,
        clause: &[TermId],
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Result<(), ProofCheckError> {
        match self {
            Self::Boolean => {
                validate_bool_tautology_with_progress(terms, ProofId(0), clause, progress)
            }
            Self::BitBlast => {
                validate_bv_bitblast_with_progress(terms, ProofId(0), clause, None, progress)
            }
            Self::Gate => validate_bv_bitblast_with_progress(
                terms,
                ProofId(0),
                clause,
                Some((BvGateType::Add, 1)),
                progress,
            ),
        }
    }
}

fn valid(lane: Lane) -> (TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let (left, right) = match lane {
        Lane::Boolean => {
            let p = terms.mk_var("semantic-bool", Sort::Bool);
            let not_p = terms.mk_not_raw(p);
            (p, terms.mk_not_raw(not_p))
        }
        Lane::BitBlast | Lane::Gate => {
            let x = terms.mk_var("semantic-bv", Sort::bitvec(1));
            let zero = terms.mk_bitvec(0.into(), 1);
            let add = terms.mk_app(Symbol::named("bvadd"), [x, zero], Sort::bitvec(1));
            (x, add)
        }
    };
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    (terms, vec![equality])
}

#[test]
fn every_top_level_validator_poll_refuses_terminally_without_memo_publication() {
    for lane in [Lane::Boolean, Lane::BitBlast, Lane::Gate] {
        let (terms, clause) = valid(lane);
        let mut total = 0;
        lane.run(&terms, &clause, &mut |work, bytes| {
            assert_eq!((work, bytes), (0, 0));
            total += 1;
            true
        })
        .unwrap();
        assert!(total > 10, "fixture must enter the bounded evaluator");
        for stop in 1..=total {
            let (fresh, clause) = valid(lane);
            let mut calls = 0;
            let result = lane.run(&fresh, &clause, &mut |work, bytes| {
                assert_eq!((work, bytes), (0, 0));
                calls += 1;
                calls != stop
            });
            assert_eq!(result, Err(ProofCheckError::ResourceLimit));
            assert_eq!(calls, stop, "no callback resurrection after refusal");
            assert!(!fresh.strict_bv_semantics_validated(&clause));
            lane.run(&fresh, &clause, &mut |_, _| true).unwrap();
        }
    }
}

#[test]
fn already_reached_schema_errors_are_not_replaced_by_a_later_poll() {
    for lane in [Lane::Boolean, Lane::BitBlast, Lane::Gate] {
        let (terms, _) = valid(lane);
        let mut terms = terms;
        let non_boolean = terms.mk_var("invalid-top-level", Sort::Int);
        let p = terms.mk_var("no-bv-content", Sort::Bool);
        for clause in [vec![], vec![non_boolean], vec![p]] {
            let mut reached = 0;
            let expected = lane
                .run(&terms, &clause, &mut |_, _| {
                    reached += 1;
                    true
                })
                .unwrap_err();
            assert!(matches!(
                expected,
                ProofCheckError::InvalidTheoryLemma { .. }
            ));
            let mut calls = 0;
            let actual = lane
                .run(&terms, &clause, &mut |_, _| {
                    calls += 1;
                    calls <= reached
                })
                .unwrap_err();
            assert_eq!(actual, expected);
            assert_eq!(calls, reached);
        }
    }
}

#[test]
fn packed_boolean_tautology_paths_keep_inner_cancellation() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("packed-p", Sort::Bool);
    let q = terms.mk_var("packed-q", Sort::Bool);
    let and = terms.mk_app(Symbol::named("and"), [p, q], Sort::Bool);
    let or = terms.mk_app(Symbol::named("or"), [p, q], Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);
    let not_and = terms.mk_not_raw(and);
    let not_or = terms.mk_not_raw(or);
    for clause in [
        vec![p, not_p],
        vec![p, not_and],
        vec![p, q, not_or],
        vec![and, not_p, not_q],
        vec![or, not_q],
    ] {
        let packed = terms.mk_app(Symbol::named("or"), clause.clone(), Sort::Bool);
        for candidate in [clause, vec![packed]] {
            let mut total = 0;
            Lane::Boolean
                .run(&terms, &candidate, &mut |_, _| {
                    total += 1;
                    true
                })
                .unwrap();
            for stop in 1..=total {
                let mut calls = 0;
                let result = Lane::Boolean.run(&terms, &candidate, &mut |_, _| {
                    calls += 1;
                    calls != stop
                });
                assert_eq!(result, Err(ProofCheckError::ResourceLimit));
                assert_eq!(calls, stop);
            }
        }
    }
}
