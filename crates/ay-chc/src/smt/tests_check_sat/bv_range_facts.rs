// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included at the original tests_check_sat module location.

// =========================================================================
// FRONT-3 cost lever: fixed-width RANGE-ENDPOINT folds.
//
// The Trust/model-checker-consumer panic-freedom encoding emits each machine-integer
// variable's range as the conjunct PAIR `0 <=u x /\ x <=u UMAX`. On a
// 49-function ny-cert sample, 55 of the 79 dumped unsigned comparisons were
// `0 <=u x` (folded by `mk_bvule`) and 50 were `x <=u UMAX` (which, before
// the range-endpoint rule, did not fold).
//
// MEASURED RESULT, recorded here so nobody re-derives the wrong conclusion:
// the unfolded upper bound already cost ZERO extra bit-blasting clauses even
// when its variable is LIVE in the core (a later preprocessing stage
// discharges it), so the fold is a term-graph normalization, NOT a measured
// solve-time win. These tests are kept as the standing pin for that property:
// verdicts identical (semantics preservation) and zero extra clauses.
//
// `dead_var_range_facts_must_not_demote_sat_to_unknown` is the completeness
// guard that decided the fold's PLACEMENT — see its body.
// =========================================================================

fn bv64(name: &str) -> Arc<ChcExpr> {
    Arc::new(ChcExpr::var(ChcVar::new(name, ChcSort::BitVec(64))))
}

const RANGE_FACT_VARS: [&str; 8] = ["a0", "a1", "a2", "a3", "a4", "a5", "a6", "a7"];

/// `AND_i (a_i <u 10)` over 64-bit vars — every range-fact variable is live.
fn live_bv_core(extra: Option<ChcExpr>) -> ChcExpr {
    let mut conjuncts: Vec<Arc<ChcExpr>> = RANGE_FACT_VARS
        .iter()
        .map(|name| {
            Arc::new(ChcExpr::Op(
                ChcOp::BvULt,
                vec![bv64(name), Arc::new(ChcExpr::BitVec(10, 64))],
            ))
        })
        .collect();
    if let Some(extra) = extra {
        conjuncts.push(Arc::new(extra));
    }
    ChcExpr::Op(ChcOp::And, conjuncts)
}

/// `q /\ AND_i (0 <=u a_i /\ a_i <=u UMAX64)` — the range-fact pairs the
/// panic-freedom encoding attaches to every machine-integer local.
fn with_unsigned_range_facts(q: &ChcExpr) -> ChcExpr {
    let umax = Arc::new(ChcExpr::BitVec(u128::from(u64::MAX), 64));
    let zero = Arc::new(ChcExpr::BitVec(0, 64));
    let mut conjuncts: Vec<Arc<ChcExpr>> = vec![Arc::new(q.clone())];
    for name in RANGE_FACT_VARS {
        conjuncts.push(Arc::new(ChcExpr::Op(
            ChcOp::BvULe,
            vec![Arc::clone(&zero), bv64(name)],
        )));
        conjuncts.push(Arc::new(ChcExpr::Op(
            ChcOp::BvULe,
            vec![bv64(name), Arc::clone(&umax)],
        )));
    }
    ChcExpr::Op(ChcOp::And, conjuncts)
}

#[cfg(test)]
fn clause_cost_of(query: &ChcExpr) -> (SmtResult, usize) {
    let mut ctx = SmtContext::new();
    reset_reuse_counters_for_tests();
    let result = ctx.check_sat(query);
    let clauses = bv_new_clause_count_for_tests();
    eprintln!(
        "[front3-ab] verdict={} bv_new_clauses={clauses}",
        match &result {
            SmtResult::Sat(_) => "Sat",
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) => "Unsat",
            SmtResult::Unknown => "Unknown",
            _ => "other",
        }
    );
    (result, clauses)
}

#[test]
#[serial]
fn live_var_range_facts_are_verdict_neutral_and_clause_free_sat() {
    let core = live_bv_core(None);
    let padded = with_unsigned_range_facts(&core);

    let (bare_result, bare_clauses) = clause_cost_of(&core);
    let (padded_result, padded_clauses) = clause_cost_of(&padded);

    assert!(
        matches!(bare_result, SmtResult::Sat(_)),
        "core must be SAT, got {bare_result:?}",
    );
    assert!(
        matches!(padded_result, SmtResult::Sat(_)),
        "range facts are tautologies: the verdict must be unchanged, got {padded_result:?}",
    );
    assert!(
        bare_clauses > 0,
        "the BV core itself must generate clauses (guards against a vacuous test)",
    );
    assert_eq!(
        padded_clauses, bare_clauses,
        "8 tautological 64-bit upper-bound facts over LIVE variables must cost ZERO extra \
         bit-blasting clauses (bare={bare_clauses}, padded={padded_clauses})",
    );
}

#[test]
#[serial]
fn live_var_range_facts_are_verdict_neutral_and_clause_free_unsat() {
    // `a3 <u 10 /\ 20 <u a3` is unsatisfiable; the range facts must not change
    // that, and must not add clauses.
    let core = live_bv_core(Some(ChcExpr::Op(
        ChcOp::BvULt,
        vec![Arc::new(ChcExpr::BitVec(20, 64)), bv64("a3")],
    )));
    let padded = with_unsigned_range_facts(&core);

    let (bare_result, bare_clauses) = clause_cost_of(&core);
    let (padded_result, padded_clauses) = clause_cost_of(&padded);

    assert!(
        matches!(bare_result, SmtResult::Unsat | SmtResult::UnsatWithCore(_)),
        "core must be UNSAT, got {bare_result:?}",
    );
    assert!(
        matches!(
            padded_result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_)
        ),
        "conjoining tautologies must keep UNSAT UNSAT, got {padded_result:?}",
    );
    assert_eq!(
        padded_clauses, bare_clauses,
        "8 tautological 64-bit upper-bound facts over LIVE variables must cost ZERO extra \
         bit-blasting clauses (bare={bare_clauses}, padded={padded_clauses})",
    );
}

#[test]
#[serial]
fn non_endpoint_bounds_still_cost_and_still_constrain() {
    // Control: a bound that is NOT the width's endpoint must still be encoded
    // and must still be able to flip the verdict. If this ever goes
    // clause-free or verdict-neutral, the fold has over-reached.
    let x = Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8))));
    let core = ChcExpr::Op(
        ChcOp::BvULt,
        vec![Arc::new(ChcExpr::BitVec(200, 8)), Arc::clone(&x)],
    );
    let constrained = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(core.clone()),
            Arc::new(ChcExpr::Op(
                ChcOp::BvULe,
                vec![x, Arc::new(ChcExpr::BitVec(100, 8))],
            )),
        ],
    );

    let (core_result, _) = clause_cost_of(&core);
    let (constrained_result, _) = clause_cost_of(&constrained);

    assert!(
        matches!(core_result, SmtResult::Sat(_)),
        "200 <u x is SAT on its own, got {core_result:?}",
    );
    assert!(
        matches!(
            constrained_result,
            SmtResult::Unsat | SmtResult::UnsatWithCore(_)
        ),
        "a non-endpoint upper bound must still constrain: 200 <u x /\\ x <=u 100 is UNSAT, \
         got {constrained_result:?}",
    );
}

#[test]
#[serial]
fn dead_var_range_facts_must_not_demote_sat_to_unknown() {
    // COMPLETENESS GUARD for the range-endpoint fold. If a variable's ONLY
    // occurrence is its tautological range fact, folding that fact away
    // removes the variable from the solved formula entirely — and the strict
    // SAT-model re-verification then sees an unassigned free variable, whose
    // fail-closed handling demotes Sat to Unknown. A term-level fold is safe
    // here because the ORIGINAL `ChcExpr` still mentions the variable and the
    // model-completion path assigns it; an expression-level fold that drops
    // the conjunct from `top_conjuncts` was measured to demote this to
    // Unknown, which is why it is not applied.
    let core = ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::BvAdd,
            vec![
                Arc::new(ChcExpr::var(ChcVar::new("x", ChcSort::BitVec(8)))),
                Arc::new(ChcExpr::BitVec(1, 8)),
            ],
        ),
        ChcExpr::BitVec(3, 8),
    );
    let padded = with_unsigned_range_facts(&core);

    let (padded_result, _) = clause_cost_of(&padded);
    assert!(
        matches!(padded_result, SmtResult::Sat(_)),
        "range facts over otherwise-dead variables must not cost the SAT verdict, \
         got {padded_result:?}",
    );
}
