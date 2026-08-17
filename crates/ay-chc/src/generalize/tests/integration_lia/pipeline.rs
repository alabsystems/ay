// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Generalizer-pipeline integration regressions.

use super::*;

// =========================================================================
// GeneralizerPipeline Integration Tests
// =========================================================================

#[test]
fn test_pipeline_runs_multiple_generalizers() {
    let mut pipeline = GeneralizerPipeline::new();
    pipeline.add(Box::new(DropLiteralGeneralizer::new()));
    pipeline.add(Box::new(LiteralWeakeningGeneralizer::new()));

    let mut ts = MockTransitionSystem::new();

    // Lemma: x = 5 AND y = 3
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    let lemma = ChcExpr::and(
        ChcExpr::eq(x.clone(), ChcExpr::int(5)),
        ChcExpr::eq(y, ChcExpr::int(3)),
    );

    // Mark x <= 5 as inductive (after dropping y)
    ts.mark_inductive(&format!("{:?}", ChcExpr::le(x.clone(), ChcExpr::int(5))));
    // Also mark x = 5 alone as inductive
    ts.mark_inductive(&format!("{:?}", ChcExpr::eq(x, ChcExpr::int(5))));

    let _result = pipeline.generalize(&lemma, 1, &mut ts);

    // Pipeline should run both generalizers
    // First DropLiteral drops y, then LiteralWeakening weakens x = 5 to x <= 5
    assert!(ts.queries.borrow().len() >= 2);
}

#[test]
fn test_pipeline_empty_returns_unchanged() {
    let pipeline = GeneralizerPipeline::new();
    let mut ts = MockTransitionSystem::new();

    let lemma = ChcExpr::Bool(true);
    let result = pipeline.generalize(&lemma, 1, &mut ts);

    assert_eq!(result, lemma);
}

#[test]
fn test_pipeline_iterates_to_fixpoint() {
    let mut pipeline = GeneralizerPipeline::new();
    pipeline.add(Box::new(DropLiteralGeneralizer::new()));

    let mut ts = MockTransitionSystem::new();

    // Lemma: a AND b AND c (three conjuncts after flattening)
    let a = ChcExpr::var(ChcVar::new("a", ChcSort::Bool));
    let b = ChcExpr::var(ChcVar::new("b", ChcSort::Bool));
    let c = ChcExpr::var(ChcVar::new("c", ChcSort::Bool));
    let lemma = ChcExpr::and(ChcExpr::and(a.clone(), b), c.clone());

    // DropLiteral extracts conjuncts [a, b, c] and tries dropping each in order:
    // - Try drop a: candidate [b, c]. NOT inductive -> keep a
    // - Try drop b: candidate [a, c]. Inductive -> drop b
    // - Try drop c: candidate [a]. Inductive -> drop c
    // Result: just 'a'
    //
    // Mark states that allow dropping b and c but not a:
    ts.mark_inductive(&format!("{a:?}")); // Final state: just a
    ts.mark_inductive(&format!("{:?}", ChcExpr::and(a.clone(), c))); // After dropping b: [a, c]
                                                                     // DO NOT mark [b, c] as inductive - we want to keep 'a'

    let result = pipeline.generalize(&lemma, 1, &mut ts);

    // Pipeline should iterate until only 'a' remains
    assert_eq!(result, a);
}

#[test]
fn test_pipeline_stops_when_nothing_changes() {
    let mut pipeline = GeneralizerPipeline::new();
    pipeline.add(Box::new(DropLiteralGeneralizer::new()));

    let mut ts = MockTransitionSystem::new();

    // Lemma: x AND y where neither can be dropped alone
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Bool));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Bool));
    let lemma = ChcExpr::and(x, y);

    // Only the full formula is inductive - nothing can be dropped
    ts.mark_inductive(&format!("{lemma:?}"));

    let result = pipeline.generalize(&lemma, 1, &mut ts);

    // Should return unchanged
    assert_eq!(result, lemma);
}
