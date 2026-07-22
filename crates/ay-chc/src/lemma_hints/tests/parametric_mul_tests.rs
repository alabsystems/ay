// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_parametric_multiplication_provider_extracts_query_guard() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Query:
    // inv(A,B,C) /\ (A >= C) /\ not (B >= 2*C) => false
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);

    let constraint = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(c.clone())),
        ChcExpr::not(ChcExpr::ge(
            ChcExpr::var(b.clone()),
            ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(c.clone())),
        )),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(a), ChcExpr::var(b), ChcExpr::var(c)])],
            Some(constraint),
        ),
        ClauseHead::False,
    ));

    // Define canonical vars for inv.
    let canonical_a = ChcVar::new("a0", ChcSort::Int);
    let canonical_b = ChcVar::new("a1", ChcSort::Int);
    let canonical_c = ChcVar::new("a2", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![canonical_a, canonical_b.clone(), canonical_c.clone()];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ParametricMultiplicationProvider;

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let expected = ChcExpr::ge(
        ChcExpr::var(canonical_b),
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(canonical_c)),
    );

    assert!(
        hints
            .iter()
            .any(|h| h.predicate == inv && h.formula == expected),
        "missing expected hint: {expected:?} in {hints:?}"
    );

    let req_stuck = HintRequest::new(HintStage::Stuck, &problem, &canonical_vars_fn);
    let mut hints_stuck = Vec::new();
    provider.collect(&req_stuck, &mut hints_stuck);
    assert!(hints_stuck.is_empty());
}

#[test]
fn test_parametric_multiplication_provider_emits_phase_difference_hint() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Query (s_multipl_08-style):
    // inv(B,A,C) /\ (A >= C) /\ not (B >= 2*C) => false
    //
    // Expect:
    // - Phase-difference: B >= A + C
    // (Note: offset-equality B = C + A is no longer emitted, see comment in collect())
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);

    let constraint = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(c.clone())),
        ChcExpr::not(ChcExpr::ge(
            ChcExpr::var(b.clone()),
            ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(c.clone())),
        )),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(b), ChcExpr::var(a), ChcExpr::var(c)])],
            Some(constraint),
        ),
        ClauseHead::False,
    ));

    // Define canonical vars for inv (positionally).
    let canonical_b = ChcVar::new("a0", ChcSort::Int);
    let canonical_a = ChcVar::new("a1", ChcSort::Int);
    let canonical_c = ChcVar::new("a2", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![
        canonical_b.clone(),
        canonical_a.clone(),
        canonical_c.clone(),
    ];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ParametricMultiplicationProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let expected_diff = ChcExpr::ge(
        ChcExpr::var(canonical_b),
        ChcExpr::add(ChcExpr::var(canonical_a), ChcExpr::var(canonical_c)),
    );
    // Note: We no longer generate the offset-equality hint (B = C + A) because
    // it is NOT entry-inductive for multi-phase problems where the loop may
    // overshoot the exit condition. See comment in collect() method.

    assert!(
        hints
            .iter()
            .any(|h| h.predicate == inv && h.formula == expected_diff),
        "missing expected phase-difference hint: {expected_diff:?} in {hints:?}"
    );
}

#[test]
fn test_parametric_multiplication_provider_negates_direct_query_guard() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Query:
    // inv(A,B,C) /\ (A >= C) /\ (B < 2*C) => false
    //
    // Suggest not(B < 2*C) i.e. B >= 2*C.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);

    let constraint = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(c.clone())),
        ChcExpr::lt(
            ChcExpr::var(b.clone()),
            ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(c.clone())),
        ),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(a), ChcExpr::var(b), ChcExpr::var(c)])],
            Some(constraint),
        ),
        ClauseHead::False,
    ));

    // Define canonical vars for inv.
    let canonical_a = ChcVar::new("a0", ChcSort::Int);
    let canonical_b = ChcVar::new("a1", ChcSort::Int);
    let canonical_c = ChcVar::new("a2", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![canonical_a, canonical_b.clone(), canonical_c.clone()];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ParametricMultiplicationProvider;

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let expected = ChcExpr::ge(
        ChcExpr::var(canonical_b),
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(canonical_c)),
    );

    assert!(
        hints
            .iter()
            .any(|h| h.predicate == inv && h.formula == expected),
        "missing expected hint: {expected:?} in {hints:?}"
    );

    let req_stuck = HintRequest::new(HintStage::Stuck, &problem, &canonical_vars_fn);
    let mut hints_stuck = Vec::new();
    provider.collect(&req_stuck, &mut hints_stuck);
    assert!(hints_stuck.is_empty());
}

#[test]
fn test_parametric_multiplication_provider_equality_from_not_eq() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // gj2007_m_1-style query:
    // inv5(A, B, C) /\ (>= A (* 5 C)) /\ (not (= B (* 5 C))) => false
    //
    // Expect:
    // - Equality hint: B = 5*C
    // - Also: B >= 5*C, B <= 5*C (decomposed bounds)
    // - Also: A >= 5*C (positive guard)
    let mut problem = ChcProblem::new();
    let inv5 = problem.declare_predicate("inv5", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);

    let constraint = ChcExpr::and(
        ChcExpr::ge(
            ChcExpr::var(a.clone()),
            ChcExpr::mul(ChcExpr::int(5), ChcExpr::var(c.clone())),
        ),
        ChcExpr::not(ChcExpr::eq(
            ChcExpr::var(b.clone()),
            ChcExpr::mul(ChcExpr::int(5), ChcExpr::var(c.clone())),
        )),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv5,
                vec![ChcExpr::var(a), ChcExpr::var(b), ChcExpr::var(c)],
            )],
            Some(constraint),
        ),
        ClauseHead::False,
    ));

    let canonical_a = ChcVar::new("a0", ChcSort::Int);
    let canonical_b = ChcVar::new("a1", ChcSort::Int);
    let canonical_c = ChcVar::new("a2", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![
        canonical_a.clone(),
        canonical_b.clone(),
        canonical_c.clone(),
    ];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv5 {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ParametricMultiplicationProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    // Should have equality hint: B = 5*C
    let eq_hint = ChcExpr::eq(
        ChcExpr::var(canonical_b.clone()),
        ChcExpr::mul(ChcExpr::int(5), ChcExpr::var(canonical_c.clone())),
    );
    assert!(
        hints.iter().any(|h| h.predicate == inv5
            && h.formula == eq_hint
            && h.source == "parametric-mul-eq-v1"),
        "missing equality hint B = 5*C; got: {:?}",
        hints
            .iter()
            .map(|h| (&h.formula, h.source))
            .collect::<Vec<_>>()
    );

    // Should have >= hint: B >= 5*C
    let ge_hint = ChcExpr::ge(
        ChcExpr::var(canonical_b.clone()),
        ChcExpr::mul(ChcExpr::int(5), ChcExpr::var(canonical_c.clone())),
    );
    assert!(
        hints
            .iter()
            .any(|h| h.predicate == inv5 && h.formula == ge_hint),
        "missing ge hint B >= 5*C; got: {:?}",
        hints
            .iter()
            .map(|h| (&h.formula, h.source))
            .collect::<Vec<_>>()
    );

    // Should have <= hint: B <= 5*C
    let le_hint = ChcExpr::le(
        ChcExpr::var(canonical_b),
        ChcExpr::mul(ChcExpr::int(5), ChcExpr::var(canonical_c.clone())),
    );
    assert!(
        hints
            .iter()
            .any(|h| h.predicate == inv5 && h.formula == le_hint),
        "missing le hint B <= 5*C; got: {:?}",
        hints
            .iter()
            .map(|h| (&h.formula, h.source))
            .collect::<Vec<_>>()
    );

    // Should have positive guard hint: A >= 5*C
    let pos_ge_hint = ChcExpr::ge(
        ChcExpr::var(canonical_a),
        ChcExpr::mul(ChcExpr::int(5), ChcExpr::var(canonical_c)),
    );
    assert!(
        hints
            .iter()
            .any(|h| h.predicate == inv5 && h.formula == pos_ge_hint),
        "missing positive guard hint A >= 5*C; got: {:?}",
        hints
            .iter()
            .map(|h| (&h.formula, h.source))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_parametric_multiplication_provider_unit_coefficient_var_var_equality() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // s_multipl_10-style query:
    // inv(A, B, C) /\ (>= A C) /\ (not (= B C)) => false
    //
    // Treat (= B C) as (= B (* 1 C)) and emit equality + decomposed bounds.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);

    let constraint = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(c.clone())),
        ChcExpr::not(ChcExpr::eq(
            ChcExpr::var(b.clone()),
            ChcExpr::var(c.clone()),
        )),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(a), ChcExpr::var(b), ChcExpr::var(c)])],
            Some(constraint),
        ),
        ClauseHead::False,
    ));

    let canonical_a = ChcVar::new("a0", ChcSort::Int);
    let canonical_b = ChcVar::new("a1", ChcSort::Int);
    let canonical_c = ChcVar::new("a2", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![canonical_a, canonical_b.clone(), canonical_c.clone()];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ParametricMultiplicationProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let eq_hint = ChcExpr::eq(
        ChcExpr::var(canonical_b.clone()),
        ChcExpr::var(canonical_c.clone()),
    );
    let ge_hint = ChcExpr::ge(
        ChcExpr::var(canonical_b.clone()),
        ChcExpr::var(canonical_c.clone()),
    );
    let le_hint = ChcExpr::le(ChcExpr::var(canonical_b), ChcExpr::var(canonical_c));

    assert!(
        hints.iter().any(|h| h.predicate == inv
            && h.formula == eq_hint
            && h.source == "parametric-mul-eq-v1"),
        "missing equality hint B = C; got: {:?}",
        hints
            .iter()
            .map(|h| (&h.formula, h.source))
            .collect::<Vec<_>>()
    );
    assert!(
        hints
            .iter()
            .any(|h| h.predicate == inv && h.formula == ge_hint),
        "missing ge hint B >= C; got: {:?}",
        hints
            .iter()
            .map(|h| (&h.formula, h.source))
            .collect::<Vec<_>>()
    );
    assert!(
        hints
            .iter()
            .any(|h| h.predicate == inv && h.formula == le_hint),
        "missing le hint B <= C; got: {:?}",
        hints
            .iter()
            .map(|h| (&h.formula, h.source))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_parametric_multiplication_provider_propagates_multi_phase_predecessors() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Multi-phase chain:
    // FUN -> SAD -> WEE
    //
    // Query on WEE:
    //   WEE(B, A, C) /\ A >= C /\ not (3*C <= B) => false
    // should produce:
    // - WEE: B >= A + 2*C
    // - SAD: B >= A + C
    // - FUN: B >= A
    let mut problem = ChcProblem::new();
    let fun = problem.declare_predicate("FUN", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);
    let sad = problem.declare_predicate("SAD", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);
    let wee = problem.declare_predicate("WEE", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    // Transition FUN -> SAD with phase-exit guard A >= E.
    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                fun,
                vec![
                    ChcExpr::var(b.clone()),
                    ChcExpr::var(a.clone()),
                    ChcExpr::var(e.clone()),
                ],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(c.clone()), ChcExpr::var(b.clone())),
                ChcExpr::and(
                    ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(e.clone())),
                    ChcExpr::eq(ChcExpr::var(d.clone()), ChcExpr::int(0)),
                ),
            )),
        ),
        ClauseHead::Predicate(
            sad,
            vec![
                ChcExpr::var(c.clone()),
                ChcExpr::var(d.clone()),
                ChcExpr::var(e.clone()),
            ],
        ),
    ));

    // Transition SAD -> WEE with phase-exit guard A >= E.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                sad,
                vec![
                    ChcExpr::var(b.clone()),
                    ChcExpr::var(a.clone()),
                    ChcExpr::var(e.clone()),
                ],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(c.clone()), ChcExpr::var(b.clone())),
                ChcExpr::and(
                    ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(e.clone())),
                    ChcExpr::eq(ChcExpr::var(d.clone()), ChcExpr::int(0)),
                ),
            )),
        ),
        ClauseHead::Predicate(
            wee,
            vec![ChcExpr::var(c.clone()), ChcExpr::var(d), ChcExpr::var(e)],
        ),
    ));

    // Query on WEE: WEE(B, A, C) /\ A >= C /\ not (3*C <= B) => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                wee,
                vec![
                    ChcExpr::var(b.clone()),
                    ChcExpr::var(a.clone()),
                    ChcExpr::var(c.clone()),
                ],
            )],
            Some(ChcExpr::and(
                ChcExpr::ge(ChcExpr::var(a), ChcExpr::var(c.clone())),
                ChcExpr::not(ChcExpr::le(
                    ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(c)),
                    ChcExpr::var(b),
                )),
            )),
        ),
        ClauseHead::False,
    ));

    let fun_vars = vec![
        ChcVar::new("f0", ChcSort::Int),
        ChcVar::new("f1", ChcSort::Int),
        ChcVar::new("f2", ChcSort::Int),
    ];
    let sad_vars = vec![
        ChcVar::new("s0", ChcSort::Int),
        ChcVar::new("s1", ChcSort::Int),
        ChcVar::new("s2", ChcSort::Int),
    ];
    let wee_vars = vec![
        ChcVar::new("w0", ChcSort::Int),
        ChcVar::new("w1", ChcSort::Int),
        ChcVar::new("w2", ChcSort::Int),
    ];

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == fun {
            Some(&fun_vars)
        } else if pred == sad {
            Some(&sad_vars)
        } else if pred == wee {
            Some(&wee_vars)
        } else {
            None
        }
    };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let provider = ParametricMultiplicationProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let wee_expected = ChcExpr::ge(
        ChcExpr::var(wee_vars[0].clone()),
        ChcExpr::add(
            ChcExpr::var(wee_vars[1].clone()),
            ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(wee_vars[2].clone())),
        ),
    );
    let sad_expected = ChcExpr::ge(
        ChcExpr::var(sad_vars[0].clone()),
        ChcExpr::add(
            ChcExpr::var(sad_vars[1].clone()),
            ChcExpr::var(sad_vars[2].clone()),
        ),
    );
    let fun_expected = ChcExpr::ge(
        ChcExpr::var(fun_vars[0].clone()),
        ChcExpr::var(fun_vars[1].clone()),
    );

    assert!(
        hints.iter().any(|h| h.predicate == wee
            && h.formula == wee_expected
            && h.source == "parametric-mul-diff-v1"),
        "missing expected WEE phase-difference hint: {wee_expected:?} in {hints:?}"
    );
    assert!(
        hints.iter().any(|h| h.predicate == sad
            && h.formula == sad_expected
            && h.source == "parametric-mul-pred-v1"),
        "missing expected SAD predecessor hint: {sad_expected:?} in {hints:?}"
    );
    assert!(
        hints.iter().any(|h| h.predicate == fun
            && h.formula == fun_expected
            && h.source == "parametric-mul-pred-v1"),
        "missing expected FUN predecessor hint: {fun_expected:?} in {hints:?}"
    );
}

#[test]
fn test_parametric_multiplication_provider_skips_diff_hint_when_a_b_alias_same_canonical() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Query has A and B both in one predicate argument expression, so both map
    // to the same canonical var. We should skip self-difference hints.
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);

    let constraint = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(c.clone())),
        ChcExpr::not(ChcExpr::ge(
            ChcExpr::var(b.clone()),
            ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(c.clone())),
        )),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![
                    ChcExpr::add(ChcExpr::var(a), ChcExpr::var(b)),
                    ChcExpr::var(c),
                ],
            )],
            Some(constraint),
        ),
        ClauseHead::False,
    ));

    let canonical_x = ChcVar::new("a0", ChcSort::Int);
    let canonical_c = ChcVar::new("a1", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![canonical_x.clone(), canonical_c.clone()];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ParametricMultiplicationProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let direct_expected = ChcExpr::ge(
        ChcExpr::var(canonical_x),
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(canonical_c)),
    );
    assert!(
        hints.iter().any(|h| h.predicate == inv
            && h.formula == direct_expected
            && h.source == "parametric-mul-v1"),
        "missing expected direct hint: {direct_expected:?} in {hints:?}"
    );

    assert!(
        hints
            .iter()
            .all(|h| !(h.predicate == inv && h.source == "parametric-mul-diff-v1")),
        "unexpected self-difference hint when A/B alias canonical var: {hints:?}"
    );
}

#[test]
fn test_parametric_multiplication_provider_skips_pred_diff_without_a_guard() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // No A >= C guard in the query: predecessor propagation should emit direct
    // hints only, not a degenerate predecessor diff hint with fallback a_pos=b_pos.
    let mut problem = ChcProblem::new();
    let pre = problem.declare_predicate("pre", vec![ChcSort::Int, ChcSort::Int]);
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    let b = ChcVar::new("B", ChcSort::Int);
    let c = ChcVar::new("C", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pre, vec![ChcExpr::var(b.clone()), ChcExpr::var(c.clone())])],
            None,
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(b.clone()), ChcExpr::var(c.clone())]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(b.clone()), ChcExpr::var(c.clone())])],
            Some(ChcExpr::not(ChcExpr::ge(
                ChcExpr::var(b),
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(c)),
            ))),
        ),
        ClauseHead::False,
    ));

    let pre_vars = vec![
        ChcVar::new("p0", ChcSort::Int),
        ChcVar::new("p1", ChcSort::Int),
    ];
    let inv_vars = vec![
        ChcVar::new("i0", ChcSort::Int),
        ChcVar::new("i1", ChcSort::Int),
    ];

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == pre {
            Some(&pre_vars)
        } else if pred == inv {
            Some(&inv_vars)
        } else {
            None
        }
    };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let provider = ParametricMultiplicationProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let pre_direct_expected = ChcExpr::ge(
        ChcExpr::var(pre_vars[0].clone()),
        ChcExpr::var(pre_vars[1].clone()),
    );
    assert!(
        hints.iter().any(|h| h.predicate == pre
            && h.formula == pre_direct_expected
            && h.source == "parametric-mul-pred-direct-v1"),
        "missing expected predecessor direct hint: {pre_direct_expected:?} in {hints:?}"
    );

    assert!(
        hints
            .iter()
            .all(|h| !(h.predicate == pre && h.source == "parametric-mul-pred-v1")),
        "unexpected predecessor diff hint without A guard: {hints:?}"
    );
}

#[test]
fn test_bounds_extreme_values_no_overflow() {
    use crate::ChcSort;

    let x = ChcVar::new("x", ChcSort::Int);

    // Test: x > i128::MAX-1 should not overflow, gives x >= i128::MAX
    let expr = ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(i128::MAX - 1));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert!(matches!(bounds[0].1, ChcExpr::Int(i128::MAX)));

    // Test: x > i128::MAX should saturate to i128::MAX (not overflow)
    let expr = ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(i128::MAX));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert!(matches!(bounds[0].1, ChcExpr::Int(i128::MAX)));

    // Test: x < i128::MIN+1 should not underflow, gives x <= i128::MIN
    let expr = ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(i128::MIN + 1));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert!(matches!(bounds[0].1, ChcExpr::Int(i128::MIN)));

    // Test: x < i128::MIN should saturate to i128::MIN (not underflow)
    let expr = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(i128::MIN));
    let bounds = BoundsFromInitProvider::extract_bounds(&expr);
    assert_eq!(bounds.len(), 1);
    assert!(matches!(bounds[0].1, ChcExpr::Int(i128::MIN)));
}

#[test]
fn test_expression_head_args_extract_constituent_var_hints() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Create a problem with:
    // predicate inv(x: Int)
    // clause: x >= 0 => inv(x + 1)  -- head arg is expression containing x
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    let constraint = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));

    // Head argument is x + 1 (not a plain variable)
    let head_arg = ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::Predicate(inv, vec![head_arg]),
    ));

    let canonical_vars: Vec<ChcVar> = vec![ChcVar::new("a0", ChcSort::Int)];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    let provider = BoundsFromInitProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    // #2660: With expression head arg handling, x in head arg (x + 1) is
    // recognized as a constituent var, so bounds on x are extracted as hints.
    assert_eq!(
        hints.len(),
        1,
        "Expected 1 hint from constituent var x in expr head arg (x + 1), got {hints:?}"
    );
}
