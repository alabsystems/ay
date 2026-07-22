// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::{ChcSort, ChcVar};

#[test]
fn test_inline_fact_clause() {
    // Init(0) ⇐ true
    // Loop(x) ⇐ Init(x)
    // Query: false ⇐ Loop(z), z > 100
    // After: Query should have no predicates (all inlined)

    let mut problem = ChcProblem::new();
    let init = problem.declare_predicate("Init", vec![ChcSort::Int]);
    let loop_pred = problem.declare_predicate("Loop", vec![ChcSort::Int]);

    // Init(x) ⇐ x = 0
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(init, vec![ChcExpr::var(x)]),
    ));

    // Loop(y) ⇐ Init(y)
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(init, vec![ChcExpr::var(y.clone())])]),
        ClauseHead::Predicate(loop_pred, vec![ChcExpr::var(y)]),
    ));

    // Query: false ⇐ Loop(z), z > 100
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(loop_pred, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(100))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // Both Init and Loop should be inlined since they have unique definitions
    // No intermediate predicates should remain in any clause body
    for clause in result.clauses() {
        for (pred_id, _) in &clause.body.predicates {
            assert_ne!(*pred_id, init, "Init should be inlined");
            assert_ne!(*pred_id, loop_pred, "Loop should be inlined");
        }
    }

    // After full inlining, only the query should remain (with constraint)
    assert_eq!(result.clauses().len(), 1, "Only query should remain");
    assert!(
        result.clauses()[0].is_query(),
        "Remaining clause should be query"
    );
    assert!(
        result.clauses()[0].body.constraint.is_some(),
        "Query should have constraint from inlined definitions"
    );
}

#[test]
fn test_no_inline_recursive() {
    // Loop(x) ⇐ Loop(x-1), x > 0
    // Should NOT inline (self-recursive)

    let mut problem = ChcProblem::new();
    let loop_pred = problem.declare_predicate("Loop", vec![ChcSort::Int]);

    // Loop(x) ⇐ x = 0 (base case)
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(loop_pred, vec![ChcExpr::var(x)]),
    ));

    // Loop(x+1) ⇐ Loop(x), x >= 0
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(loop_pred, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(
            loop_pred,
            vec![ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1))],
        ),
    ));

    // Query
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(loop_pred, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(100))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // Loop should NOT be inlined because it has multiple definitions
    // and one is self-recursive
    let loop_clauses: Vec<_> = result
        .clauses()
        .iter()
        .filter(|c| c.head.predicate_id() == Some(loop_pred))
        .collect();
    assert!(
        loop_clauses.len() >= 2,
        "Loop should not be inlined (has multiple definitions)"
    );
}

#[test]
fn test_multi_def_inlining() {
    // P has 2 definitions and 1 tail use → multi-def inlining expands
    // Q's clause into 2 clauses (one per P definition), eliminating P.
    //
    // Before:
    //   P(x) ⇐ x = 0
    //   P(x) ⇐ x = 1
    //   Q(y) ⇐ P(y)
    //   false ⇐ Q(y), y > 10
    //
    // After multi-def inlining of P:
    //   Q(y) ⇐ (y = 0)     ; from P's first definition
    //   Q(y) ⇐ (y = 1)     ; from P's second definition
    //   false ⇐ Q(y), y > 10

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    // P(x) ⇐ x = 0
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(x) ⇐ x = 1
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));

    // Q(y) ⇐ P(y)
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(y.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));

    // Query
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(y.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(y), ChcExpr::int(10))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // P should be inlined via multi-def expansion (2 defs, 1 tail use).
    // After P is inlined into Q, Q has 2 definitions and 1 tail use,
    // so Q is also eligible for unique-def inlining in the cleanup phase
    // (each Q definition is a fact clause with no body predicates).
    // The result is all predicates eliminated — only queries remain.
    let p_in_body = result
        .clauses()
        .iter()
        .any(|c| c.body.predicates.iter().any(|(id, _)| *id == p));
    assert!(!p_in_body, "P should be inlined via multi-def expansion");

    let q_in_body = result
        .clauses()
        .iter()
        .any(|c| c.body.predicates.iter().any(|(id, _)| *id == q));
    assert!(
        !q_in_body,
        "Q should also be inlined (becomes unique-def fact after P expansion)"
    );

    // Only query clauses should remain
    assert!(
        result.clauses().iter().all(HornClause::is_query),
        "All remaining clauses should be queries"
    );
    assert_eq!(
        result.clauses().len(),
        2,
        "Should have 2 query clauses (one per P definition path)"
    );
}

#[test]
fn equal_cardinality_multi_def_rewrite_invalidates_clause_alignment() {
    // Two definitions and two query uses preserve the total clause count:
    // 4 input clauses -> 4 expanded query clauses. Cardinality therefore
    // cannot tell whether output indices still address input clauses.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    for value in [0, 1] {
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(value))),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
        ));
    }
    for value in [0, 1] {
        let y = ChcVar::new(format!("y_{value}"), ChcSort::Int);
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(p, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(value))),
        )));
    }
    let input_len = problem.clauses().len();

    let (transformed, _, _, traces, output_to_input) =
        ClauseInliner::new().inline_tracked(&problem);
    assert_eq!(transformed.clauses().len(), input_len);
    assert!(
        traces.is_empty(),
        "rewritten clauses must not retain stale traces"
    );
    assert!(
        output_to_input.is_none(),
        "a multi-def rewrite must invalidate index alignment even when clause counts happen to match"
    );
}

#[test]
fn test_break_cycle() {
    // A(x) ⇐ B(x)
    // B(x) ⇐ A(x)
    // Should break cycle and inline at most one

    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("A", vec![ChcSort::Int]);
    let b = problem.declare_predicate("B", vec![ChcSort::Int]);
    let c = problem.declare_predicate("C", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // A(x) ⇐ B(x), x >= 0
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(b, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(a, vec![ChcExpr::var(x.clone())]),
    ));

    // B(x) ⇐ A(x), x < 100
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(a, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(100))),
        ),
        ClauseHead::Predicate(b, vec![ChcExpr::var(x.clone())]),
    ));

    // C(x) ⇐ A(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(a, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(c, vec![ChcExpr::var(x.clone())]),
    ));

    // Query
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        c,
        vec![ChcExpr::var(x)],
    )])));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // The cyclic predicates A and B should not cause infinite loop
    // At least one should remain (cycle is broken)
    let has_a = result
        .clauses()
        .iter()
        .any(|c| c.head.predicate_id() == Some(a));
    let has_b = result
        .clauses()
        .iter()
        .any(|c| c.head.predicate_id() == Some(b));

    // At least one of A or B should still exist (cycle prevents full inlining)
    assert!(
        has_a || has_b,
        "At least one cyclic predicate should remain"
    );
}

/// Tests inlining of predicates with complex head expressions.
///
/// This exercises the code path at lines 422-438 that handles non-variable
/// head arguments (e.g., P(x+1) instead of P(x)).
#[test]
fn test_inline_complex_head_expr() {
    // P(x+1) ⇐ x >= 0    ; defining clause with complex head
    // Q(y) ⇐ P(y)        ; usage
    // false ⇐ Q(z)       ; query
    //
    // After inlining P:
    // Q(y) should become: Q(y) ⇐ (x+1 = y) ∧ (x >= 0)

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // P(x+1) ⇐ x >= 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1))]),
    ));

    // Q(y) ⇐ P(y)
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(y.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y)]),
    ));

    // Query: false ⇐ Q(z), z > 100
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(100))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // P should be inlined (unique non-recursive definition)
    let has_p_in_body = result
        .clauses()
        .iter()
        .any(|c| c.body.predicates.iter().any(|(id, _)| *id == p));
    assert!(!has_p_in_body, "P should be inlined into Q's definition");

    // The defining clause for Q should now have a constraint
    // that captures the complex head expression relationship (x+1 = y)
    let q_def: Vec<_> = result
        .clauses()
        .iter()
        .filter(|c| c.head.predicate_id() == Some(q))
        .collect();

    if !q_def.is_empty() {
        // Q's definition should have been updated with inlined constraint
        let q_clause = q_def[0];
        assert!(
            q_clause.body.constraint.is_some(),
            "Q's definition should have constraint after inlining P"
        );

        // The constraint should include the head expression equality
        let constraint_str = format!("{}", q_clause.body.constraint.as_ref().unwrap());
        // Should contain some form of equality involving the arithmetic expression
        assert!(
            constraint_str.contains("1") || constraint_str.contains("+"),
            "Constraint should capture the x+1 relationship: {constraint_str}"
        );
    }

    // Verify the solver can still process the transformed problem correctly
    // by checking it has valid structure
    assert!(
        !result.clauses().is_empty(),
        "Should have at least one clause"
    );
    let queries: Vec<_> = result.clauses().iter().filter(|c| c.is_query()).collect();
    assert_eq!(queries.len(), 1, "Should have exactly one query");
}

#[test]
fn test_chain_inlining() {
    // Tests that chained definitions are inlined in order:
    // A(x) ⇐ x = 0
    // B(x) ⇐ A(x)
    // C(x) ⇐ B(x)
    // Query: false ⇐ C(x)
    // After: Query should have constraint from A

    let mut problem = ChcProblem::new();
    let a = problem.declare_predicate("A", vec![ChcSort::Int]);
    let b = problem.declare_predicate("B", vec![ChcSort::Int]);
    let c = problem.declare_predicate("C", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // A(x) ⇐ x = 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(a, vec![ChcExpr::var(x.clone())]),
    ));

    // B(x) ⇐ A(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(a, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(b, vec![ChcExpr::var(x.clone())]),
    ));

    // C(x) ⇐ B(x)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(b, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(c, vec![ChcExpr::var(x.clone())]),
    ));

    // Query: false ⇐ C(x)
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        c,
        vec![ChcExpr::var(x)],
    )])));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // All intermediate predicates should be inlined
    // The query should now be a fact (no predicates in body)
    let queries: Vec<_> = result.clauses().iter().filter(|c| c.is_query()).collect();
    assert_eq!(queries.len(), 1, "Should have exactly one query");

    // After full inlining, query body should be empty (a fact)
    assert!(
        queries[0].body.predicates.is_empty(),
        "Query should have no predicates after full chain inlining"
    );
}

/// Regression test for #5295: back-translation must synthesize interpretations
/// for inlined predicates with complex head arguments (e.g., P(x+1)).
///
/// Before fix: synthesize_interpretation returned None for complex heads,
/// causing the predicate's interpretation to be missing from the back-translated
/// model. Portfolio then rejected valid Safe results as "invalid invariant."
#[test]
fn test_back_translate_complex_head_synthesizes_interpretation() {
    use crate::pdr::model::PredicateInterpretation;
    use crate::transform::ValidityWitness;

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // P(x+1) <= x >= 0   (complex head arg)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1))]),
    ));

    // Q(y) <= P(y)
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(y.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y)]),
    ));

    // Query: false <= Q(z), z > 100
    let z = ChcVar::new("z", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(z.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(z), ChcExpr::int(100))),
    )));

    // Transform using the Transformer trait (produces a back-translator)
    let inliner = Box::new(ClauseInliner::new());
    let TransformationResult {
        problem: _transformed,
        back_translator,
    } = inliner.transform(problem);

    // Simulate a solver model with only Q's interpretation (P was inlined)
    let q_var = ChcVar::new("q_arg", ChcSort::Int);
    let q_interp = PredicateInterpretation::new(
        vec![q_var.clone()],
        ChcExpr::ge(ChcExpr::var(q_var), ChcExpr::int(1)),
    );

    let mut model = ValidityWitness::new();
    model.set(q, q_interp);
    // P has NO interpretation — it was inlined away

    // Back-translate: P's interpretation should be synthesized
    let translated = back_translator.translate_validity(model);

    // P must now have an interpretation (the fix for #5295)
    assert!(
        translated.get(&p).is_some(),
        "BUG #5295: back-translator failed to synthesize interpretation for \
         inlined predicate P with complex head arg (x+1)"
    );
}

/// Regression for #425: back-translation after multi-def inlining must
/// existentially eliminate clause-local witness variables when reconstructing
/// the outer predicate from the inlined inner-loop invariant.
#[test]
fn test_back_translate_count_by_2_m_nest_eliminates_clause_local_witnesses() {
    use crate::pdr::{PdrConfig, PdrResult, PdrSolver};
    use crate::ChcParser;
    use ay_core::kani_compat::DetHashSet as FxHashSet;

    let input = include_str!(
        "../../../../../benchmarks/chc-comp/2025/extra-small-lia/count_by_2_m_nest_000.smt2"
    );
    let original = ChcParser::parse(input).expect("benchmark should parse");
    let original_for_verify = original.clone();

    let TransformationResult {
        problem: transformed,
        back_translator,
    } = Box::new(ClauseInliner::new()).transform(original);

    assert_eq!(
        transformed.predicates().len(),
        1,
        "count_by_2_m_nest should inline to a single predicate"
    );

    let mut solver = PdrSolver::new(transformed, PdrConfig::default());
    let model = match solver.solve() {
        PdrResult::Safe(model) => model,
        _ => panic!("inlined count_by_2_m_nest should solve to Safe"),
    };

    let translated = back_translator.translate_validity(model);
    assert_eq!(
        translated.len(),
        original_for_verify.predicates().len(),
        "back-translation should reconstruct all original predicates"
    );

    for (pred_id, interp) in translated.iter() {
        let allowed: FxHashSet<ChcVar> = interp.vars.iter().cloned().collect();
        assert!(
            interp
                .formula
                .vars()
                .into_iter()
                .all(|var| allowed.contains(&var)),
            "back-translated predicate {} still contains clause-local variables: {}",
            pred_id.index(),
            interp.formula
        );
    }

    let mut verifier = PdrSolver::new(original_for_verify, PdrConfig::default());
    assert!(
        verifier.verify_model(&translated),
        "back-translated model for count_by_2_m_nest must validate on the original problem"
    );
}

/// Regression test: 2-predicate chain with 3-arg Post predicate.
/// After inlining, the query constraint should be UNSAT because stored = val
/// from the transition but not(stored = val) from the query.
/// Part of #7897: this case was returning "Trivially unsafe" incorrectly.
#[test]
fn test_inline_multi_arg_chain_soundness() {
    let mut problem = ChcProblem::new();
    let pre = problem.declare_predicate("Pre", vec![ChcSort::Int, ChcSort::Int]);
    let post = problem.declare_predicate("Post", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    // Pre(p, v) <= (p = 0 /\ v >= 0)
    let p = ChcVar::new("p", ChcSort::Int);
    let v = ChcVar::new("v", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(p.clone()), ChcExpr::int(0)),
            ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(pre, vec![ChcExpr::var(p.clone()), ChcExpr::var(v.clone())]),
    ));

    // Post(p2, s, v) <= Pre(p, v) /\ p2 = 1 /\ s = v
    let p2 = ChcVar::new("p2", ChcSort::Int);
    let s = ChcVar::new("s", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pre, vec![ChcExpr::var(p.clone()), ChcExpr::var(v.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(p2.clone()), ChcExpr::int(1)),
                ChcExpr::eq(ChcExpr::var(s.clone()), ChcExpr::var(v.clone())),
            )),
        ),
        ClauseHead::Predicate(
            post,
            vec![
                ChcExpr::var(p2),
                ChcExpr::var(s.clone()),
                ChcExpr::var(v.clone()),
            ],
        ),
    ));

    // false <= Post(px, sx, vx) /\ sx != vx
    let px = ChcVar::new("px", ChcSort::Int);
    let sx = ChcVar::new("sx", ChcSort::Int);
    let vx = ChcVar::new("vx", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(
            post,
            vec![
                ChcExpr::var(px),
                ChcExpr::var(sx.clone()),
                ChcExpr::var(vx.clone()),
            ],
        )],
        Some(ChcExpr::not(ChcExpr::eq(
            ChcExpr::var(sx),
            ChcExpr::var(vx),
        ))),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);

    // After inlining, only the query clause should remain
    assert_eq!(result.clauses().len(), 1, "Only query should remain");
    assert!(
        result.clauses()[0].is_query(),
        "Remaining clause should be query"
    );
    // The remaining clause should have no predicates in the body
    assert!(
        result.clauses()[0].body.predicates.is_empty(),
        "All predicates should be inlined"
    );

    // Print the inlined constraint for debugging
    let constraint = result.clauses()[0]
        .body
        .constraint
        .as_ref()
        .expect("Query should have a constraint after inlining");
    eprintln!("Inlined constraint: {constraint}");

    // CRITICAL: the query constraint should be UNSAT because the chain implies
    // stored = val, but the query asserts not(stored = val).
    // Check with SMT solver.
    use crate::smt::SmtResult;
    let mut smt = result.make_smt_context();
    match smt.check_sat(constraint) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
            // Correct! The constraint should be UNSAT.
        }
        SmtResult::Sat(model) => {
            panic!(
                "BUG: Inlined constraint should be UNSAT but SMT says SAT.\n\
                 Constraint: {constraint}\n\
                 Model: {model:?}\n\
                 This means the inliner lost the 's = v' constraint during inlining."
            );
        }
        SmtResult::Unknown => {
            panic!("SMT returned Unknown for inlined constraint - check SMT solver completeness");
        }
    }
}

/// Test that full preprocessing pipeline produces UNSAT constraint for
/// the multi-arg chain. This catches bugs where DeadParamEliminator or
/// LocalVarEliminator interact with ClauseInliner to lose constraints.
#[test]
fn test_full_preprocess_pipeline_multi_arg_chain() {
    use crate::transform::{DeadParamEliminator, LocalVarEliminator, TransformationPipeline};

    let mut problem = ChcProblem::new();
    let pre = problem.declare_predicate("Pre", vec![ChcSort::Int, ChcSort::Int]);
    let post = problem.declare_predicate("Post", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    // Pre(p, v) <= (p = 0 /\ v >= 0)
    let p = ChcVar::new("p", ChcSort::Int);
    let v = ChcVar::new("v", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(p.clone()), ChcExpr::int(0)),
            ChcExpr::ge(ChcExpr::var(v.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(pre, vec![ChcExpr::var(p.clone()), ChcExpr::var(v.clone())]),
    ));

    // Post(p2, s, v) <= Pre(p, v) /\ p2 = 1 /\ s = v
    let p2 = ChcVar::new("p2", ChcSort::Int);
    let s = ChcVar::new("s", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pre, vec![ChcExpr::var(p.clone()), ChcExpr::var(v.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(p2.clone()), ChcExpr::int(1)),
                ChcExpr::eq(ChcExpr::var(s.clone()), ChcExpr::var(v.clone())),
            )),
        ),
        ClauseHead::Predicate(
            post,
            vec![
                ChcExpr::var(p2),
                ChcExpr::var(s.clone()),
                ChcExpr::var(v.clone()),
            ],
        ),
    ));

    // false <= Post(px, sx, vx) /\ sx != vx
    let px = ChcVar::new("px", ChcSort::Int);
    let sx = ChcVar::new("sx", ChcSort::Int);
    let vx = ChcVar::new("vx", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(
            post,
            vec![
                ChcExpr::var(px),
                ChcExpr::var(sx.clone()),
                ChcExpr::var(vx.clone()),
            ],
        )],
        Some(ChcExpr::not(ChcExpr::eq(
            ChcExpr::var(sx),
            ChcExpr::var(vx),
        ))),
    )));

    // Run the full preprocessing pipeline (same order as PreprocessSummary::build
    // for the LIA case, skipping BV transforms)
    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(DeadParamEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem);
    let preprocessed = result.problem;

    eprintln!("Preprocessed problem:");
    eprintln!("  Clauses: {}", preprocessed.clauses().len());
    eprintln!("  Predicates: {}", preprocessed.predicates().len());
    for (i, clause) in preprocessed.clauses().iter().enumerate() {
        eprintln!(
            "  Clause {i}: body_preds={}, constraint={:?}",
            clause.body.predicates.len(),
            clause.body.constraint.as_ref().map(|c| format!("{c}"))
        );
    }

    // All queries should have UNSAT constraints
    for query in preprocessed.queries() {
        let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        eprintln!("  Query constraint: {constraint}");

        use crate::smt::SmtResult;
        let mut smt = preprocessed.make_smt_context();
        match smt.check_sat(&constraint) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // Correct
            }
            SmtResult::Sat(model) => {
                panic!(
                    "BUG: Preprocessed query constraint should be UNSAT but SMT says SAT.\n\
                     Constraint: {constraint}\n\
                     Model: {model:?}\n\
                     Full preprocessing pipeline lost the 's = v' implication."
                );
            }
            SmtResult::Unknown => {
                panic!("SMT returned Unknown for preprocessed constraint");
            }
        }
    }
}

/// Test that parsing + preprocessing produces UNSAT constraint for the
/// multi-arg chain when loaded from SMT2 format.
/// Part of #7897: the binary returns "unknown" instead of "sat".
#[test]
fn test_parse_preprocess_multi_arg_chain_soundness() {
    use crate::parser::ChcParser;
    use crate::transform::{DeadParamEliminator, LocalVarEliminator, TransformationPipeline};

    let input = r#"
(set-logic HORN)
(declare-fun Pre (Int Int) Bool)
(declare-fun Post (Int Int Int) Bool)

(assert (forall ((p Int) (v Int))
    (=> (and (= p 0) (>= v 0))
        (Pre p v))))

(assert (forall ((p Int) (v Int) (p2 Int) (s Int))
    (=> (and (Pre p v)
             (= p2 1)
             (= s v))
        (Post p2 s v))))

(assert (forall ((px Int) (sx Int) (vx Int))
    (=> (and (Post px sx vx) (not (= sx vx)))
        false)))

(check-sat)
"#;

    let problem = ChcParser::parse(input).expect("parse should succeed");

    eprintln!("Parsed problem:");
    eprintln!("  Predicates: {}", problem.predicates().len());
    eprintln!("  Clauses: {}", problem.clauses().len());
    for (i, clause) in problem.clauses().iter().enumerate() {
        eprintln!(
            "  Clause {i}: head={:?}, body_preds={}, constraint={}",
            clause.head,
            clause.body.predicates.len(),
            clause
                .body
                .constraint
                .as_ref()
                .map_or("None".to_string(), |c| format!("{c}"))
        );
    }

    // Run the same preprocessing pipeline as the portfolio
    let pipeline = TransformationPipeline::new()
        .with(DeadParamEliminator::new())
        .with(LocalVarEliminator::new())
        .with(DeadParamEliminator::new())
        .with(ClauseInliner::new());
    let result = pipeline.transform(problem);
    let preprocessed = result.problem;

    eprintln!("After preprocessing:");
    eprintln!("  Clauses: {}", preprocessed.clauses().len());
    eprintln!("  Predicates: {}", preprocessed.predicates().len());
    for (i, clause) in preprocessed.clauses().iter().enumerate() {
        eprintln!(
            "  Clause {i}: body_preds={}, constraint={}",
            clause.body.predicates.len(),
            clause
                .body
                .constraint
                .as_ref()
                .map_or("None".to_string(), |c| format!("{c}"))
        );
    }

    // After inlining, the query constraint should be UNSAT
    for query in preprocessed.queries() {
        let constraint = query.body.constraint.clone().unwrap_or(ChcExpr::Bool(true));
        eprintln!("Query constraint: {constraint}");

        use crate::smt::SmtResult;
        let mut smt = preprocessed.make_smt_context();
        match smt.check_sat(&constraint) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                // Correct! Chain implies s=v, and query says not(s=v).
            }
            SmtResult::Sat(model) => {
                panic!(
                    "BUG: Parsed+preprocessed constraint should be UNSAT but SMT says SAT.\n\
                     Constraint: {constraint}\n\
                     Model: {model:?}"
                );
            }
            SmtResult::Unknown => {
                panic!("SMT returned Unknown for parsed+preprocessed constraint");
            }
        }
    }
}

/// Regression for #7997: back-translation must handle signed triple-sum patterns
/// where an equality like `C = Add(A, B)` has multiple non-keep variables that
/// need to be solved iteratively.
///
/// Before fix: `solve_local_from_head_equality` only handled single-variable
/// affine RHS (`var + const`). When back-translating from a clause with
/// `C = A + B` where C is keep and A, B are locals, the function returned None,
/// causing the existential projection to fail.
///
/// After fix: `solve_local_from_linear_equality` handles multi-variable linear
/// expressions by extracting one local at a time, allowing iterative elimination.
#[test]
fn test_back_translate_signed_triple_sum_linear_solver() {
    use crate::pdr::model::PredicateInterpretation;
    use crate::transform::ValidityWitness;

    // Construct a problem that produces the signed triple-sum pattern:
    //
    //   Inner(A, B) <= A = 0 /\ B = 0
    //   Inner(A', B') <= Inner(A, B) /\ A' = A + 2 /\ B' = B + 1
    //   Outer(C) <= Inner(A, B) /\ C = A + B
    //   false <= Outer(C) /\ C > 100
    //
    // After inlining Outer, only Inner remains. Back-translating Outer
    // requires solving `C = A + B` where C is keep, A and B are locals
    // from Inner's body arguments.

    let mut problem = ChcProblem::new();
    let inner = problem.declare_predicate("Inner", vec![ChcSort::Int, ChcSort::Int]);
    let outer = problem.declare_predicate("Outer", vec![ChcSort::Int]);

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);

    // Inner(A, B) <= A = 0 /\ B = 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(
            inner,
            vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())],
        ),
    ));

    // Inner(A', B') <= Inner(A, B) /\ A' = A + 2 /\ B' = B + 1
    let a2 = ChcVar::new("A2", ChcSort::Int);
    let b2 = ChcVar::new("B2", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inner,
                vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(a2.clone()),
                    ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::int(2)),
                ),
                ChcExpr::eq(
                    ChcExpr::var(b2.clone()),
                    ChcExpr::add(ChcExpr::var(b.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(inner, vec![ChcExpr::var(a2), ChcExpr::var(b2)]),
    ));

    // Outer(C) <= Inner(A, B) /\ C = A + B   (the signed-sum pattern)
    let c = ChcVar::new("C", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inner,
                vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())],
            )],
            Some(ChcExpr::eq(
                ChcExpr::var(c.clone()),
                ChcExpr::add(ChcExpr::var(a), ChcExpr::var(b)),
            )),
        ),
        ClauseHead::Predicate(outer, vec![ChcExpr::var(c.clone())]),
    ));

    // Query: false <= Outer(C) /\ C > 100
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(outer, vec![ChcExpr::var(c.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(c), ChcExpr::int(100))),
    )));

    // Transform: Outer is a unique-def non-recursive predicate => inlined.
    let inliner = Box::new(ClauseInliner::new());
    let TransformationResult {
        problem: transformed,
        back_translator,
    } = inliner.transform(problem);

    // Outer should be inlined, only Inner should remain.
    let outer_in_body = transformed
        .clauses()
        .iter()
        .any(|c| c.body.predicates.iter().any(|(id, _)| *id == outer));
    assert!(
        !outer_in_body,
        "Outer should be inlined away, leaving only Inner"
    );

    // Simulate a solver model for Inner (e.g., `A >= 0 /\ B >= 0`).
    let inner_var_a = ChcVar::new("inner_a", ChcSort::Int);
    let inner_var_b = ChcVar::new("inner_b", ChcSort::Int);
    let inner_interp = PredicateInterpretation::new(
        vec![inner_var_a.clone(), inner_var_b.clone()],
        ChcExpr::and(
            ChcExpr::ge(ChcExpr::var(inner_var_a), ChcExpr::int(0)),
            ChcExpr::ge(ChcExpr::var(inner_var_b), ChcExpr::int(0)),
        ),
    );

    let mut model = ValidityWitness::new();
    model.set(inner, inner_interp);

    let translated = back_translator.translate_validity(model);

    // Outer must have a synthesized interpretation.
    assert!(
        translated.get(&outer).is_some(),
        "BUG #7997: back-translator failed to synthesize Outer's interpretation \
         when defining clause has `C = A + B` (signed-sum pattern)"
    );

    // The interpretation must be closed (no clause-local variables).
    let outer_interp = translated.get(&outer).unwrap();
    let allowed: ay_core::kani_compat::DetHashSet<ChcVar> =
        outer_interp.vars.iter().cloned().collect();
    assert!(
        outer_interp
            .formula
            .vars()
            .into_iter()
            .all(|var| allowed.contains(&var)),
        "BUG #7997: Outer's back-translated interpretation contains clause-local \
         variables: {} (vars: {:?})",
        outer_interp.formula,
        outer_interp.vars,
    );
}

/// Regression for #7997: back-translation with signed triple-sum (`D = A + B - C`)
/// where the defining clause has THREE local variables from the body predicate.
///
/// Before fix: `solve_local_from_linear_equality` required exactly 1 local across
/// both sides of the equality. With `D = A + B - C` (D=keep, A/B/C=local), it
/// found 3 locals and returned None, falling through to AllSAT+MBP which could
/// fail on complex formulas.
///
/// After fix: the solver picks one local to solve for (e.g., `A = D - B + C`),
/// substitutes it out, then iterates to eliminate remaining locals from other
/// equalities. This reduces the MBP's workload and succeeds on patterns where
/// MBP alone would fail.
#[test]
fn test_back_translate_signed_triple_sum_multi_local_elimination() {
    use crate::pdr::model::PredicateInterpretation;
    use crate::transform::ValidityWitness;

    // Problem structure:
    //   Inner(A, B, C) <= A = 0 /\ B = 0 /\ C = 0
    //   Inner(A', B', C') <= Inner(A, B, C) /\ A' = A + 2 /\ B' = B + 1 /\ C' = C + 1
    //   Outer(D) <= Inner(A, B, C) /\ D = A + B - C   (signed triple-sum)
    //   false <= Outer(D) /\ D > 100
    //
    // After inlining Outer, back-translation must reconstruct Outer's
    // interpretation from Inner's model + the defining clause `D = A + B - C`.

    let mut problem = ChcProblem::new();
    let inner = problem.declare_predicate("Inner", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);
    let outer = problem.declare_predicate("Outer", vec![ChcSort::Int]);

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let c_var = ChcVar::new("C", ChcSort::Int);

    // Inner(A, B, C) <= A = 0 /\ B = 0 /\ C = 0
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::and(
                ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(0)),
                ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::int(0)),
            ),
            ChcExpr::eq(ChcExpr::var(c_var.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(
            inner,
            vec![
                ChcExpr::var(a.clone()),
                ChcExpr::var(b.clone()),
                ChcExpr::var(c_var.clone()),
            ],
        ),
    ));

    // Inner step
    let a2 = ChcVar::new("A2", ChcSort::Int);
    let b2 = ChcVar::new("B2", ChcSort::Int);
    let c2 = ChcVar::new("C2", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inner,
                vec![
                    ChcExpr::var(a.clone()),
                    ChcExpr::var(b.clone()),
                    ChcExpr::var(c_var.clone()),
                ],
            )],
            Some(ChcExpr::and(
                ChcExpr::and(
                    ChcExpr::eq(
                        ChcExpr::var(a2.clone()),
                        ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::int(2)),
                    ),
                    ChcExpr::eq(
                        ChcExpr::var(b2.clone()),
                        ChcExpr::add(ChcExpr::var(b.clone()), ChcExpr::int(1)),
                    ),
                ),
                ChcExpr::eq(
                    ChcExpr::var(c2.clone()),
                    ChcExpr::add(ChcExpr::var(c_var.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(
            inner,
            vec![ChcExpr::var(a2), ChcExpr::var(b2), ChcExpr::var(c2)],
        ),
    ));

    // Outer(D) <= Inner(A, B, C) /\ D = A + B - C  (signed triple-sum)
    let d = ChcVar::new("D", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inner,
                vec![
                    ChcExpr::var(a.clone()),
                    ChcExpr::var(b.clone()),
                    ChcExpr::var(c_var.clone()),
                ],
            )],
            Some(ChcExpr::eq(
                ChcExpr::var(d.clone()),
                ChcExpr::sub(
                    ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
                    ChcExpr::var(c_var.clone()),
                ),
            )),
        ),
        ClauseHead::Predicate(outer, vec![ChcExpr::var(d.clone())]),
    ));

    // Query: false <= Outer(D) /\ D > 100
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(outer, vec![ChcExpr::var(d.clone())])],
        Some(ChcExpr::gt(ChcExpr::var(d), ChcExpr::int(100))),
    )));

    // Transform: inline Outer.
    let inliner = Box::new(ClauseInliner::new());
    let TransformationResult {
        problem: transformed,
        back_translator,
    } = inliner.transform(problem);

    // Outer should be inlined away.
    assert!(
        !transformed
            .clauses()
            .iter()
            .any(|c| c.body.predicates.iter().any(|(id, _)| *id == outer)),
        "Outer should be inlined"
    );

    // Simulate Inner's model: A >= 0 /\ B >= 0 /\ C >= 0 /\ A + B - C = 0
    // (the signed triple-sum invariant).
    let ia = ChcVar::new("ia", ChcSort::Int);
    let ib = ChcVar::new("ib", ChcSort::Int);
    let ic = ChcVar::new("ic", ChcSort::Int);
    let inner_interp = PredicateInterpretation::new(
        vec![ia.clone(), ib.clone(), ic.clone()],
        ChcExpr::and(
            ChcExpr::and(
                ChcExpr::ge(ChcExpr::var(ia.clone()), ChcExpr::int(0)),
                ChcExpr::ge(ChcExpr::var(ib.clone()), ChcExpr::int(0)),
            ),
            ChcExpr::and(
                ChcExpr::ge(ChcExpr::var(ic.clone()), ChcExpr::int(0)),
                ChcExpr::eq(
                    ChcExpr::sub(
                        ChcExpr::add(ChcExpr::var(ia), ChcExpr::var(ib)),
                        ChcExpr::var(ic),
                    ),
                    ChcExpr::int(0),
                ),
            ),
        ),
    );

    let mut model = ValidityWitness::new();
    model.set(inner, inner_interp);

    let translated = back_translator.translate_validity(model);

    // Outer must have a synthesized interpretation.
    assert!(
        translated.get(&outer).is_some(),
        "BUG #7997: back-translator failed to synthesize Outer's interpretation \
         with signed triple-sum defining clause `D = A + B - C`"
    );

    // The interpretation must be closed (no clause-local variables).
    let outer_interp = translated.get(&outer).unwrap();
    let allowed: ay_core::kani_compat::DetHashSet<ChcVar> =
        outer_interp.vars.iter().cloned().collect();
    assert!(
        outer_interp
            .formula
            .vars()
            .into_iter()
            .all(|var| allowed.contains(&var)),
        "BUG #7997: Outer's signed-triple-sum back-translated interpretation \
         contains clause-local variables: {} (vars: {:?})",
        outer_interp.formula,
        outer_interp.vars,
    );
}

/// Soundness regression (rank-6 review finding): a REPEATED head variable in a
/// defining clause (`P(v, v)`) implies a positional equality between the call
/// arguments. The direct-substitution path used to build the duplicate-keyed
/// substitution [(v,a),(v,b)] whose map collapse (last-wins) silently DROPPED
/// `a = b`, weakening the body — a wrong-Unsafe class. Repeated head vars must
/// route through the fresh-vars path, which links repeats via one canonical
/// fresh variable (#7897).
#[test]
fn test_inline_repeated_head_var_preserves_positional_equality() {
    // P(v, v) ⇐ true ; Query: false ⇐ P(a, b), a = 0, b = 1.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let v = ChcVar::new("v", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::var(v.clone()), ChcExpr::var(v)]),
    ));
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())])],
        Some(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(b), ChcExpr::int(1)),
        )),
    )));

    let inliner = ClauseInliner::new();
    let result = inliner.inline(&problem);
    let query = result
        .clauses()
        .iter()
        .find(|c| c.is_query())
        .expect("query clause");
    assert!(
        query.body.predicates.is_empty(),
        "P (unique def) should be inlined"
    );
    let constraint = query.body.constraint.clone().expect("constraint");
    let folded = constraint
        .clone()
        .into_propagate_equalities()
        .simplify_constants();
    assert!(
        matches!(folded, ChcExpr::Bool(false)),
        "query constraint must be UNSAT (positional equality a=b preserved); got {folded:?} from {constraint:?}"
    );
}

/// Rank-6 review second regression: the same repeated-head-var wrong-Unsafe
/// class through the MULTI-DEF path. With TWO defining clauses for `P(v, v)`,
/// the unique-def phase does not fire; the multi-definition phase under the
/// graph-collapse node rule (|in|*|out| <= |in|+|out|, 2*1 <= 2+1) expands the
/// query once per definition via `inline_clause`. Each expansion must route
/// through the fresh-vars path and preserve the positional equality `a = b`,
/// keeping the system UNSAT.
#[test]
fn test_multi_def_graph_collapse_repeated_head_var_preserves_positional_equality() {
    // P(v, v) ⇐ true ; P(w, w) ⇐ w = 5 ; Query: false ⇐ P(a, b), a = 0, b = 1.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let v = ChcVar::new("v", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::var(v.clone()), ChcExpr::var(v)]),
    ));
    let w = ChcVar::new("w", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(w.clone()), ChcExpr::int(5))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(w.clone()), ChcExpr::var(w)]),
    ));
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())])],
        Some(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(a), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(b), ChcExpr::int(1)),
        )),
    )));

    let inliner = ClauseInliner::new().with_graph_collapse_node_rule();
    let result = inliner.inline(&problem);
    let queries: Vec<_> = result.clauses().iter().filter(|c| c.is_query()).collect();
    assert_eq!(
        queries.len(),
        2,
        "multi-def graph collapse must expand the query once per definition; got {:?}",
        result.clauses()
    );
    for query in queries {
        assert!(
            query.body.predicates.is_empty(),
            "P (2 defs, graph-collapse node rule) must be inlined; got {:?}",
            query.body.predicates
        );
        let constraint = query.body.constraint.clone().expect("constraint");
        let folded = constraint
            .clone()
            .into_propagate_equalities()
            .simplify_constants();
        assert!(
            matches!(folded, ChcExpr::Bool(false)),
            "each expanded query must stay UNSAT (positional equality a=b preserved); got {folded:?} from {constraint:?}"
        );
    }
}

/// ADVERSARIAL (b) — #chc25-deriv-expansion. The SMT counterexample kernel must
/// REJECT an expanded derivation chain built from a CORRUPTED composition trace.
/// We inline a linear chain `Init -> Step -> Q` into a composite fact clause,
/// confirm the HONEST expansion certifies on the original clauses, then corrupt
/// an intermediate value in the trace and confirm the replay rejects it (never
/// Valid). This proves derivation-chain expansion cannot manufacture a wrong
/// Unsafe: soundness rests on the kernel gate, not on trusting the trace.
#[test]
fn deriv_expansion_corrupted_trace_rejected_by_kernel() {
    use crate::bmc::{BmcConfig, BmcSolver};
    use crate::pdr::{CexVerificationResult, PdrConfig, PdrSolver};
    use crate::transform::BackTranslator;
    use crate::ChcEngineResult;
    use back_translator::InliningBackTranslator;

    // Init(x) <= x = 0
    // Step(x) <= Init(y) /\ x = y + 1        (Step = Init + 1)
    // Q(x)    <= Step(x)                      (composite: collapses to Q(1) fact)
    // Q(x)    <= Q(x)                         (self-loop keeps Q non-inlinable)
    // false   <= Q(x) /\ x >= 1
    let mut problem = ChcProblem::new();
    let init = problem.declare_predicate("Init", vec![ChcSort::Int]);
    let step = problem.declare_predicate("Step", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(init, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(init, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(x.clone()),
                ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(1)),
            )),
        ),
        ClauseHead::Predicate(step, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(step, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(q, vec![ChcExpr::var(x.clone())])]),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(q, vec![ChcExpr::var(x.clone())])],
        Some(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(1))),
    )));

    let inliner = ClauseInliner::new();
    let (transformed, inlined_defs, new_to_old, traces, _output_to_input) =
        inliner.inline_tracked(&problem);
    assert!(
        !traces.is_empty(),
        "inliner must record a composition trace for the collapsed chain"
    );

    let cfg = BmcConfig::default()
        .with_max_depth(3)
        .with_time_budget(std::time::Duration::from_secs(30));
    let ChcEngineResult::Unsafe(cex) = BmcSolver::new(transformed, cfg).solve() else {
        panic!("inlined composite problem must refute");
    };

    let pdr_cfg = || PdrConfig {
        solve_timeout: Some(std::time::Duration::from_secs(30)),
        ..PdrConfig::default()
    };

    let raw_entries = cex.witness.as_ref().map(|w| w.entries.len()).unwrap_or(0);

    // HONEST expansion certifies on the ORIGINAL clauses.
    let honest = InliningBackTranslator {
        inlined_defs: inlined_defs.clone(),
        new_to_old: new_to_old.clone(),
        composition_traces: traces.clone(),
        output_to_input: None,
        input_problem: None,
    };
    let honest_witness = honest.translate_invalidity(cex.clone());
    // Expansion must actually reconstruct the Init->Step->Q chain (else the
    // test would pass vacuously via the fallback BMC replay).
    let honest_entries = honest_witness
        .witness
        .as_ref()
        .map(|w| w.entries.len())
        .unwrap_or(0);
    assert!(
        honest_entries > raw_entries,
        "honest expansion must add reconstructed entries (raw={raw_entries}, expanded={honest_entries})"
    );
    let mut v_ok = PdrSolver::new(problem.clone(), pdr_cfg());
    assert_eq!(
        v_ok.verify_counterexample(&honest_witness),
        CexVerificationResult::Valid,
        "honest expanded chain must certify on the original clauses"
    );

    // CORRUPT: force the intermediate `Step` value to a wrong constant (999).
    let mut corrupt_traces = traces;
    let mut corrupted = false;
    for trace in corrupt_traces.values_mut() {
        if let Some(s) = trace.steps.get_mut(&step) {
            s.call_args = vec![ChcExpr::int(999)];
            corrupted = true;
        }
    }
    assert!(
        corrupted,
        "trace must contain a Step composition to corrupt"
    );

    let bad = InliningBackTranslator {
        inlined_defs,
        new_to_old,
        composition_traces: corrupt_traces,
        output_to_input: None,
        input_problem: None,
    };
    let bad_witness = bad.translate_invalidity(cex);
    // The corruption still BUILDS a chain (entries added); the rejection below
    // therefore proves the kernel catches a reconstructed-but-wrong chain, not
    // merely a fail-closed no-op.
    let bad_entries = bad_witness
        .witness
        .as_ref()
        .map(|w| w.entries.len())
        .unwrap_or(0);
    assert!(
        bad_entries > raw_entries,
        "corrupted expansion must still build a chain (raw={raw_entries}, bad={bad_entries})"
    );
    let mut v_bad = PdrSolver::new(problem, pdr_cfg());
    assert_ne!(
        v_bad.verify_counterexample(&bad_witness),
        CexVerificationResult::Valid,
        "corrupted-trace expansion (wrong intermediate value) must be REJECTED by the SMT kernel"
    );
}

// ── Ground recovery of inlined linking variables ───────────────────────────
//
// Inlining substitutes a definition into its caller and existentially projects
// the fresh linking variables away, so a ground derivation over the SURVIVING
// clause carries no value for them. Ground back-translation has to put them
// back to rebuild the collapsed chain. These tests pin down that it does so by
// EVALUATION (the recorded defining expressions), and — the part that actually
// guards soundness — that a WRONG intermediate is rejected rather than
// accepted.

/// Build a problem whose middle predicate is inlined through the fresh-variable
/// path, so a linking variable really is created and projected.
///
/// ```text
/// clause 0:  Mid(a, k)   ⇐ k = a + 1                (unique definition)
/// clause 1:  Top(m)      ⇐ Mid(m, j), j > 5         (caller; j is the link)
/// clause 2:  false       ⇐ Top(p), p = 3            (query)
/// ```
///
/// `Mid`'s definition carries a body-local-free but head-argument-fresh shape:
/// the caller passes `j` for the second position, inlining equates a fresh
/// variable to it, and the surviving clause keeps only `m`.
fn linking_var_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let mid = problem.declare_predicate("Mid", vec![ChcSort::Int, ChcSort::Int]);
    let top = problem.declare_predicate("Top", vec![ChcSort::Int]);

    // clause 0: Mid(a, k) ⇐ k = a + 1
    let a = ChcVar::new("a", ChcSort::Int);
    let k = ChcVar::new("k", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            ChcExpr::var(k.clone()),
            ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::int(1)),
        )),
        ClauseHead::Predicate(mid, vec![ChcExpr::var(a), ChcExpr::var(k)]),
    ));

    // clause 1: Top(m) ⇐ Mid(m, j), j > 5
    let m = ChcVar::new("m", ChcSort::Int);
    let j = ChcVar::new("j", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(mid, vec![ChcExpr::var(m.clone()), ChcExpr::var(j.clone())])],
            Some(ChcExpr::gt(ChcExpr::var(j), ChcExpr::int(5))),
        ),
        ClauseHead::Predicate(top, vec![ChcExpr::var(m)]),
    ));

    // clause 2: false ⇐ Top(p), p = 8
    let p = ChcVar::new("p", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(top, vec![ChcExpr::var(p.clone())])],
        Some(ChcExpr::eq(ChcExpr::var(p), ChcExpr::int(8))),
    )));

    problem
}

/// The inliner must RECORD a defining expression for every fresh linking
/// variable it introduces at a head-argument position — that record is what
/// makes recovery an evaluation instead of a solve.
#[test]
fn linking_definitions_are_recorded_for_fresh_head_args() {
    let problem = linking_var_problem();
    let inliner = ClauseInliner::new();
    let (_, _, _, traces, _) = inliner.inline_tracked(&problem);

    let trace = traces
        .values()
        .find(|trace| trace.is_composite())
        .expect("the caller clause must have a composition trace");
    let recorded: usize = trace
        .steps
        .values()
        .map(|step| step.linking_defs.len())
        .sum();
    assert!(
        recorded > 0,
        "inlining introduced fresh linking variables but recorded no defining \
         expressions for them; ground recovery would fall back to an SMT solve"
    );
    // Every recorded definition must be expressed in the CALLER's space, not in
    // the definition's own — otherwise evaluating it in the composite
    // environment is meaningless.
    for step in trace.steps.values() {
        for (var, definition) in &step.linking_defs {
            assert!(
                var.name.contains("__inline_"),
                "recorded a definition for {} which is not a fresh linking variable",
                var.name
            );
            assert!(
                !definition
                    .vars()
                    .iter()
                    .any(|v| v.name.contains("__inline_") && v.name == var.name),
                "linking definition for {} is self-referential",
                var.name
            );
        }
    }
}

/// Build the ground derivation over the INLINED problem that corresponds to
/// `Top` reaching 8: seed the query clause and let ground completion fill in
/// the fresh linking variables inlining introduced.
fn inlined_query_derivation(inlined: &ChcProblem) -> crate::ground_derivation::GroundDerivation {
    use crate::ground_derivation::{
        complete::complete_env_for_clause, GroundDerivation, GroundDerivationStep,
    };
    use crate::smt::SmtValue;

    let query_index = inlined
        .clauses()
        .iter()
        .position(|clause| matches!(clause.head, ClauseHead::False))
        .expect("the inlined problem must still have a query");
    let mut env: FxHashMap<String, SmtValue> = FxHashMap::default();
    env.insert("p".to_string(), SmtValue::Int(8));
    assert!(
        complete_env_for_clause(&inlined.clauses()[query_index], &mut env),
        "could not complete the query environment on the inlined problem"
    );
    GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: query_index,
            env,
            premises: vec![],
        }],
        query_step: 0,
    }
}

/// End to end: a ground derivation over the INLINED problem must expand into
/// one over the INPUT clauses that VALIDATES — with the projected intermediate
/// recovered by evaluation, and with no SMT solve involved.
#[test]
fn ground_back_translation_recovers_the_projected_intermediate() {
    use crate::ground_derivation::validate_ground_derivation;

    let problem = linking_var_problem();
    let inliner = Box::new(ClauseInliner::new());
    let result = inliner.transform(problem.clone());
    let inlined_derivation = inlined_query_derivation(&result.problem);
    // Sanity: the derivation we hand over is valid where it lives.
    validate_ground_derivation(&result.problem, &inlined_derivation)
        .expect("test setup: the input derivation must validate on the inlined problem");

    let expanded = result
        .back_translator
        .translate_ground_derivation(&inlined_derivation)
        .expect(
            "ground back-translation failed to expand the composite step — the \
             projected linking variable was not recovered",
        );

    // The expansion must be a genuine derivation over the ORIGINAL clauses.
    validate_ground_derivation(&problem, &expanded)
        .expect("expanded derivation does not validate on the original clauses");

    // It must actually have rebuilt the collapsed applications rather than
    // passing the composite step through.
    assert!(
        expanded.len() > inlined_derivation.len(),
        "expansion did not reconstruct the inlined steps (len {} vs {})",
        expanded.len(),
        inlined_derivation.len()
    );
    assert!(
        expanded.steps.iter().any(|step| step.clause_index == 0),
        "expanded derivation never applies the inlined definition (clause 0)"
    );
}

/// ANTI-FABRICATION: recovery synthesizes VALUES, and a wrong one must be
/// caught. Corrupting the recovered intermediate has to make the derivation
/// fail ground validation against the original clauses — the guarantee that
/// lets recovery be a heuristic in the first place.
#[test]
fn corrupted_intermediate_is_rejected_by_ground_validation() {
    use crate::ground_derivation::validate_ground_derivation;
    use crate::smt::SmtValue;

    let problem = linking_var_problem();
    let inliner = Box::new(ClauseInliner::new());
    let result = inliner.transform(problem.clone());
    let inlined_derivation = inlined_query_derivation(&result.problem);

    let mut expanded = result
        .back_translator
        .translate_ground_derivation(&inlined_derivation)
        .expect("back-translation should succeed before corruption");
    validate_ground_derivation(&problem, &expanded)
        .expect("the uncorrupted expansion must validate");

    // Corrupt the reconstructed `Mid` application: its definition forces
    // k = a + 1, so bumping the recovered intermediate breaks it. This is
    // exactly the shape a wrong recovery would produce.
    let mid_step = expanded
        .steps
        .iter_mut()
        .find(|step| step.clause_index == 0)
        .expect("expansion must contain the reconstructed definition step");
    let corrupted = match mid_step.env.get("k") {
        Some(SmtValue::Int(value)) => SmtValue::Int(value + 1),
        other => panic!("expected an integer intermediate, found {other:?}"),
    };
    mid_step.env.insert("k".to_string(), corrupted);

    assert!(
        validate_ground_derivation(&problem, &expanded).is_err(),
        "a corrupted intermediate value was ACCEPTED by ground validation — \
         recovery would no longer be safe to treat as a heuristic"
    );
}

fn recovery_trace(
    pred: PredicateId,
    call_args: Vec<ChcExpr>,
    linking_defs: Vec<(ChcVar, ChcExpr)>,
) -> ClauseTrace {
    let def_clause = HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(pred, call_args.clone()),
    );
    let mut trace = ClauseTrace::new(0);
    trace.steps.insert(
        pred,
        CompositionStep {
            inlined_pred: pred,
            call_args,
            def_clause,
            def_input_index: Some(0),
            linking_defs,
            var_renames: Vec::new(),
        },
    );
    trace
}

#[test]
fn linking_definition_recovery_reaches_a_multi_round_fixpoint() {
    use crate::smt::SmtValue;

    let source = ChcVar::new("source", ChcSort::Int);
    let links: Vec<ChcVar> = (1..=6)
        .map(|index| ChcVar::new(format!("link_{index}"), ChcSort::Int))
        .collect();
    // Deliberately reverse the dependency order. A single sweep can recover
    // only `link_1`; every later value requires another round. Six links also
    // guards against the former `steps + 2` bound, which allowed only four
    // rounds for an arbitrary-arity single composition step.
    let definitions = (0..links.len())
        .rev()
        .map(|index| {
            let source_var = if index == 0 {
                source.clone()
            } else {
                links[index - 1].clone()
            };
            (
                links[index].clone(),
                ChcExpr::add(ChcExpr::var(source_var), ChcExpr::int(1)),
            )
        })
        .collect();
    let trace = recovery_trace(
        PredicateId::new(90),
        vec![ChcExpr::var(links[5].clone())],
        definitions,
    );
    let composite = HornClause::query(ClauseBody::constraint(ChcExpr::Bool(true)));
    let mut recovered = FxHashMap::default();
    recovered.insert(source.name, SmtValue::Int(10));

    InliningBackTranslator::recover_linking_defs_ground(&composite, &trace, &mut recovered);
    for (index, link) in links.iter().enumerate() {
        assert_eq!(
            recovered.get(&link.name),
            Some(&SmtValue::Int(11 + index as i128)),
            "link {} was not recovered at the definition fixpoint",
            index + 1
        );
    }
}

#[test]
fn repeated_head_equality_participates_in_the_linking_fixpoint() {
    use crate::smt::SmtValue;

    let first_actual = ChcVar::new("first_actual", ChcSort::Int);
    let second_actual = ChcVar::new("second_actual", ChcSort::Int);
    let canonical = ChcVar::new("shared__inline_test", ChcSort::Int);
    let downstream = ChcVar::new("downstream", ChcSort::Int);
    // This is the trace shape for `P(v, v)`: only the canonical fresh binding
    // is recorded, while the second actual remains linked by the composite
    // equality. Put the downstream definition first so recovery must alternate
    // definition evaluation, clause propagation, then definition evaluation.
    let trace = recovery_trace(
        PredicateId::new(91),
        vec![
            ChcExpr::var(first_actual.clone()),
            ChcExpr::var(second_actual.clone()),
        ],
        vec![
            (
                downstream.clone(),
                ChcExpr::add(ChcExpr::var(second_actual.clone()), ChcExpr::int(1)),
            ),
            (canonical.clone(), ChcExpr::var(first_actual.clone())),
        ],
    );
    let composite = HornClause::query(ClauseBody::constraint(ChcExpr::eq(
        ChcExpr::var(canonical.clone()),
        ChcExpr::var(second_actual.clone()),
    )));
    let mut recovered = FxHashMap::default();
    recovered.insert(first_actual.name, SmtValue::Int(5));

    InliningBackTranslator::recover_linking_defs_ground(&composite, &trace, &mut recovered);
    assert_eq!(recovered.get(&canonical.name), Some(&SmtValue::Int(5)));
    assert_eq!(recovered.get(&second_actual.name), Some(&SmtValue::Int(5)));
    assert_eq!(recovered.get(&downstream.name), Some(&SmtValue::Int(6)));
}

#[test]
fn unconstrained_call_defaults_only_when_absence_is_syntactic() {
    use crate::smt::SmtValue;

    let dead = ChcVar::new("dead_call_argument", ChcSort::Int);
    let mentioned = ChcVar::new("mentioned_call_argument", ChcSort::Int);
    let trace = recovery_trace(
        PredicateId::new(92),
        vec![ChcExpr::var(dead.clone()), ChcExpr::var(mentioned.clone())],
        vec![],
    );
    // `mentioned = mentioned` is intentionally not simplified here: its mere
    // syntactic occurrence is enough to bar the default heuristic.
    let composite = HornClause::query(ClauseBody::constraint(ChcExpr::eq(
        ChcExpr::var(mentioned.clone()),
        ChcExpr::var(mentioned.clone()),
    )));
    let mut recovered = FxHashMap::default();

    InliningBackTranslator::default_unconstrained_call_vars(&composite, &trace, &mut recovered);
    assert_eq!(recovered.get(&dead.name), Some(&SmtValue::Int(0)));
    assert!(
        !recovered.contains_key(&mentioned.name),
        "a variable mentioned by the composite must flow to propagation or the fail-closed solve"
    );
}
