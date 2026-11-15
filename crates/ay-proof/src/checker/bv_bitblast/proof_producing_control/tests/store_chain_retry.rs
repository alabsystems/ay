// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The ordinary route's one retry: complete-domain scalarization of a
//! small-index read first, store-chain reads only after a counted exhaustion.

#![cfg(test)]

use super::super::ordinary::{attempt_ordinary_refutation, counted_exhaustion};
use super::*;
use crate::checker::bv_bitblast::array_finite::SmallIndexReads;

/// `(= v (select (store ((as const (Array (_ BitVec index) (_ BitVec element)))
/// 0) off v) off))`, and the same read against an unrelated value `w`.
fn read_over_write(index: u32, element: u32) -> (TermStore, TermId, TermId) {
    let mut terms = TermStore::new();
    let sort = Sort::array(Sort::bitvec(index), Sort::bitvec(element));
    let zero = terms.mk_bitvec(0.into(), element);
    let zeros = terms.mk_app(Symbol::named("const-array"), [zero], sort.clone());
    let offset = terms.mk_var("off", Sort::bitvec(index));
    let value = terms.mk_var("v", Sort::bitvec(element));
    let other = terms.mk_var("w", Sort::bitvec(element));
    let stored = terms.mk_app(Symbol::named("store"), [zeros, offset, value], sort);
    let read = terms.mk_app(
        Symbol::named("select"),
        [stored, offset],
        Sort::bitvec(element),
    );
    let identity = terms.mk_app(Symbol::named("="), [value, read], Sort::Bool);
    let near_miss = terms.mk_app(Symbol::named("="), [other, read], Sort::Bool);
    (terms, identity, near_miss)
}

fn attempt(
    terms: &TermStore,
    clause: TermId,
    reads: SmallIndexReads,
) -> Result<(), OrdinaryFailure> {
    let (limits, deadline) = strict_producer_limits();
    attempt_ordinary_refutation(
        terms,
        &[clause],
        &limits,
        deadline,
        &mut || Ok(()),
        Route::default(),
        reads,
    )
}

fn refute(terms: &TermStore, clause: TermId) -> Result<(), Failure> {
    let (limits, deadline) = strict_producer_limits();
    refute_ordinary_clause(
        terms,
        &[clause],
        limits,
        deadline,
        &mut || Ok(()),
        Route::default(),
    )
}

/// The two measured refusals: idx8 overruns the lowering's expression-node
/// bound; idx7/elem32 lowers, then overruns one of the bit-blast producer's
/// counted `proof resource` bounds. Which one moves with the producer's
/// pricing: `preflight construction clauses` until b6021b58e stopped the
/// preflight over-counting, then `resolution hints`, then, since 73810d00d,
/// `resolution proof output bytes`. So this pins only that it is a counted
/// producer resource. Each is exactly one counted exhaustion of a query that
/// scalarized a read, and the store-chain lowering of the same clause is
/// refuted.
#[test]
fn an_exhausted_complete_domain_read_is_refuted_through_its_store_chain() {
    for (index, element, exhausted) in [
        (8, 8, "BvExpr nodes, above limit 4096"),
        (7, 32, "proof resource `"),
    ] {
        let (terms, identity, _) = read_over_write(index, element);
        match attempt(&terms, identity, SmallIndexReads::CompleteDomain) {
            Err(OrdinaryFailure::Exhausted {
                reason,
                scalarized_small_index_reads: true,
            }) => assert!(
                reason.contains(exhausted),
                "idx{index}/elem{element}: unexpected exhaustion {reason}"
            ),
            other => {
                panic!("idx{index}/elem{element}: expected a counted exhaustion, got {other:?}")
            }
        }
        attempt(&terms, identity, SmallIndexReads::StoreChain)
            .unwrap_or_else(|error| panic!("idx{index}/elem{element}: {error:?}"));
        assert_eq!(refute(&terms, identity), Ok(()));
    }
}

/// A satisfiable clause stays rejected after the retry, and its reason keeps
/// both attempts.
#[test]
fn a_satisfiable_read_is_rejected_by_both_attempts() {
    let (terms, _, near_miss) = read_over_write(8, 8);
    match refute(&terms, near_miss) {
        Err(Failure::Rejected(reason)) => {
            assert!(reason.contains("above limit 4096"), "{reason}");
            assert!(
                reason.contains("retried with store-chain array reads"),
                "{reason}"
            );
            assert!(reason.contains("no refutation"), "{reason}");
        }
        other => panic!("expected a rejection, got {other:?}"),
    }
}

/// Where the complete domain is affordable its verdict is final: a satisfiable
/// clause is not retried, and nothing was lowered differently.
#[test]
fn an_affordable_complete_domain_verdict_is_not_retried() {
    let (terms, identity, near_miss) = read_over_write(2, 4);
    assert!(attempt(&terms, identity, SmallIndexReads::CompleteDomain).is_ok());
    match attempt(&terms, near_miss, SmallIndexReads::CompleteDomain) {
        Err(OrdinaryFailure::Final(Failure::Rejected(reason))) => {
            assert!(reason.contains("no refutation"), "{reason}");
        }
        other => panic!("expected a final rejection, got {other:?}"),
    }
    match refute(&terms, near_miss) {
        Err(Failure::Rejected(reason)) => {
            assert!(!reason.contains("retried"), "{reason}");
        }
        other => panic!("expected a rejection, got {other:?}"),
    }
}

/// A cancellation during the first attempt is never retried. The lowering
/// makes its refusal sticky, so the first attempt polls exactly four times
/// (three accepted, the fourth refused); a retry would start a fresh lowering
/// whose first poll is a fifth.
#[test]
fn a_cancelled_first_attempt_is_not_retried() {
    let (terms, identity, _) = read_over_write(8, 8);
    let (limits, deadline) = strict_producer_limits();
    let mut polls = 0_usize;
    let mut refuse_after_three = || {
        polls += 1;
        if polls > 3 {
            Err(ProofCheckError::ResourceLimit)
        } else {
            Ok(())
        }
    };
    let outcome = refute_ordinary_clause(
        &terms,
        &[identity],
        limits,
        deadline,
        &mut refuse_after_three,
        Route::default(),
    );
    assert_eq!(outcome, Err(Failure::Cancelled));
    assert_eq!(polls, 4, "the cancelled first attempt must not be retried");
}

/// Only a COUNTED cap starts the retry. Every wall-clock bound on the route
/// is the one hang guard, so a resource refusal that ended at or after it,
/// or one the producer names as a deadline, is final.
#[test]
fn only_a_counted_cap_before_the_hang_guard_is_retried() {
    let future = Instant::now() + Duration::from_secs(60);
    let past = Instant::now();
    assert!(counted_exhaustion(None, future));
    assert!(counted_exhaustion(
        Some("preflight construction clauses"),
        future
    ));
    assert!(counted_exhaustion(Some("resolution hints"), future));
    for deadline_resource in [
        "resolution proof deadline",
        "absolute proof deadline",
        "expression preflight deadline",
        "proof export deadline",
    ] {
        assert!(
            !counted_exhaustion(Some(deadline_resource), future),
            "{deadline_resource}"
        );
    }
    assert!(!counted_exhaustion(None, past));
    assert!(!counted_exhaustion(
        Some("preflight construction clauses"),
        past
    ));
    match OrdinaryFailure::exhausted("stopped".to_owned(), None, true, past) {
        OrdinaryFailure::Final(Failure::Rejected(reason)) => assert_eq!(reason, "stopped"),
        other => panic!("a stop at the hang guard must be final, got {other:?}"),
    }
    match OrdinaryFailure::exhausted(
        "stopped".to_owned(),
        Some("resolution proof deadline"),
        true,
        future,
    ) {
        OrdinaryFailure::Final(Failure::Rejected(_)) => {}
        other => panic!("a deadline resource must be final, got {other:?}"),
    }
}
