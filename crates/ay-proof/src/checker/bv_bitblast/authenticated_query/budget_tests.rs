// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The authentication lanes are decided by counted caps; running out of them,
//! or being stopped, is a DECLINE and never a veto.

use ay_core::{time::Instant, Sort, Symbol, TermStore};
use std::time::Duration;

use super::{
    authenticate_atom_leaf_bool_bv_unsat_query, authenticate_bool_bv_unsat_query, counted_declines,
    export_refutation, proof_producing_limits, replay_failure, BoolBvUnsatAuthenticationError,
    BvBlastValidateError, BvExpr, BvExprExportError,
};

fn oversized_multiplier_root(terms: &mut TermStore, name: &str) -> ay_core::TermId {
    let bv = terms.mk_var(name, Sort::bitvec(64));
    let mut product = bv;
    // Ten 64-bit multipliers exceed the 100,000-gate bound before any search.
    for _ in 0..10 {
        product = terms.mk_app(Symbol::named("bvmul"), [product, bv], Sort::bitvec(64));
    }
    let reflexive = terms.mk_app(Symbol::named("="), [product, product], Sort::Bool);
    terms.mk_not_raw(reflexive)
}

fn exports() -> usize {
    counted_declines::EXPORTS.with(std::cell::Cell::get)
}

#[test]
fn a_replay_that_ran_out_is_a_decline_and_only_a_rejected_step_is_a_veto() {
    for exhausted in [
        BvBlastValidateError::DeadlineExceeded,
        BvBlastValidateError::Cancelled,
        BvBlastValidateError::WorkOverflow,
        BvBlastValidateError::ResourceLimit {
            resource: "replay work",
            limit: 1,
            actual: 2,
        },
    ] {
        let error = replay_failure(exhausted);
        assert!(
            matches!(error, BoolBvUnsatAuthenticationError::ResourceLimit { .. }),
            "{error:?}"
        );
        assert!(error.is_capability_decline());
    }
    let rejected = replay_failure(BvBlastValidateError::UndefinedVar(7));
    assert!(matches!(
        rejected,
        BoolBvUnsatAuthenticationError::Replay { .. }
    ));
    assert!(
        !rejected.is_capability_decline(),
        "a rejected step still vetoes"
    );
}

/// A query beyond the counted gate budget is declined by that counted cap —
/// named in the reason — with no caller deadline, and identically with a
/// generous one: the wall clock plays no part in the outcome.
#[test]
fn a_counted_exhaustion_declines_the_lane_whatever_the_caller_deadline() {
    let mut terms = TermStore::new();
    let root = oversized_multiplier_root(&mut terms, "auth-budget-mul");
    for caller_deadline in [None, Some(Instant::now() + Duration::from_secs(600))] {
        let Err(error) = authenticate_bool_bv_unsat_query(&terms, &[root], caller_deadline) else {
            panic!("the counted gate budget must refuse this query");
        };
        assert!(error.is_capability_decline(), "{error:?}");
        assert!(
            error.to_string().contains("estimated bit-blast gates"),
            "the counted cap is named: {error}"
        );
    }
}

/// The two lanes lower a pure Bool/BV query identically; the second repeats
/// the first's counted exhaustion instead of paying it again, with the same
/// decline.
#[test]
fn a_counted_exhaustion_is_paid_once_per_lowered_query() {
    let mut terms = TermStore::new();
    let root = oversized_multiplier_root(&mut terms, "auth-once-mul");
    let before = exports();
    let first = authenticate_bool_bv_unsat_query(&terms, &[root], None).map(|_| ());
    assert_eq!(exports(), before + 1);
    let second = authenticate_atom_leaf_bool_bv_unsat_query(&terms, &[root], None).map(|_| ());
    let third = authenticate_bool_bv_unsat_query(&terms, &[root], None).map(|_| ());
    assert_eq!(exports(), before + 1, "no second export of the same query");
    assert_eq!(format!("{first:?}"), format!("{second:?}"));
    assert_eq!(format!("{first:?}"), format!("{third:?}"));
    assert!(first.is_err_and(|error| error.is_capability_decline()));
}

/// A stop by the lane's deadline is never remembered: the same query exports
/// again once the deadline no longer binds.
#[test]
fn a_deadline_stop_is_never_remembered() {
    let [a, b] = ["auth-stop-a", "auth-stop-b"].map(|name| BvExpr::leaf(name, 6));
    let query = BvExpr::not(BvExpr::eq(
        BvExpr::mul(a.clone(), b.clone()),
        BvExpr::mul(b, a),
    ));
    let expired = Instant::now();
    let (limits, _) = proof_producing_limits(Some(expired));
    let before = exports();
    let stopped = export_refutation(&query, &limits, expired);
    assert!(
        matches!(stopped, Err(BvExprExportError::ResourceLimit { .. })),
        "{stopped:?}"
    );
    assert!(counted_declines::remembered(counted_declines::key(&query)).is_none());
    let (limits, deadline) = proof_producing_limits(None);
    let _ = export_refutation(&query, &limits, deadline);
    assert_eq!(
        exports(),
        before + 2,
        "the stop did not stand in for a verdict"
    );
}
