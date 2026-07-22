// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_ratio_hints_2x_pattern() {
    // Test ratio hints for s_multipl pattern: A' = A + 1, B' = B + 2
    // Expected: 2*A = B (since deltas are 1 and 2)
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    // Init clause: A = 0 /\ B = 0 => inv(A, B)
    let a_var = ChcVar::new("A", ChcSort::Int);
    let b_var = ChcVar::new("B", ChcSort::Int);

    let init_constraint = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(a_var.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(b_var.clone()), ChcExpr::int(0)),
    );
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(init_constraint),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(a_var.clone()), ChcExpr::var(b_var.clone())],
        ),
    ));

    // Self-loop clause: inv(A, B) /\ C = A + 1 /\ D = B + 2 => inv(C, D)
    // Using C/D instead of A_next/B_next to match real benchmark naming (e.g., s_multipl_23)
    let c_var = ChcVar::new("C", ChcSort::Int);
    let d_var = ChcVar::new("D", ChcSort::Int);

    let loop_constraint = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(c_var.clone()),
            ChcExpr::add(ChcExpr::var(a_var.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::eq(
            ChcExpr::var(d_var.clone()),
            ChcExpr::add(ChcExpr::var(b_var.clone()), ChcExpr::int(2)),
        ),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(a_var), ChcExpr::var(b_var)])],
            Some(loop_constraint),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(c_var), ChcExpr::var(d_var)]),
    ));

    // Define canonical vars for inv
    let canonical_a = ChcVar::new("__p0_a0", ChcSort::Int);
    let canonical_b = ChcVar::new("__p0_a1", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![canonical_a, canonical_b];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    let provider = RecurrenceConservedEqualityProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    // Should have at least one ratio hint like 2*A = B
    assert!(!hints.is_empty(), "Expected ratio hints to be generated");

    // Check for the ratio hint: (= (* 2 __p0_a0) __p0_a1)
    let has_ratio_hint = hints.iter().any(|h| {
        let formula_str = format!("{:?}", h.formula);
        // The hint should be 2*a0 = a1 or equivalent
        formula_str.contains("Mul")
            && formula_str.contains("__p0_a0")
            && formula_str.contains("__p0_a1")
    });
    assert!(
        has_ratio_hint,
        "Missing ratio hint 2*A = B. Got hints: {:?}",
        hints
            .iter()
            .map(|h| format!("{:?}", h.formula))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_mod_residue_dillig02_m_pattern() {
    // Test ModResidueHintProvider for dillig02_m pattern: G' = G + 1, H' = ite((mod G 2)=0, ...)
    // Expected: hints for (mod G 2) = 0 and (mod G 2) = 1
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    // Init clause: G = 0 /\ H = 0 => inv(G, H)
    let g_var = ChcVar::new("G", ChcSort::Int);
    let h_var = ChcVar::new("H", ChcSort::Int);

    let init_constraint = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(g_var.clone()), ChcExpr::int(0)),
        ChcExpr::eq(ChcExpr::var(h_var.clone()), ChcExpr::int(0)),
    );
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(init_constraint),
        ClauseHead::Predicate(
            inv,
            vec![ChcExpr::var(g_var.clone()), ChcExpr::var(h_var.clone())],
        ),
    ));

    // Self-loop clause: inv(G, H) /\ G' = G + 1 /\ H' = ite((mod G 2)=0, H+1, H+2) => inv(G', H')
    let g_next = ChcVar::new("G_prime", ChcSort::Int);
    let h_next = ChcVar::new("H_prime", ChcSort::Int);

    // Build: (mod G 2) = 0
    let mod_g_2 = ChcExpr::mod_op(ChcExpr::var(g_var.clone()), ChcExpr::int(2));
    let mod_eq_0 = ChcExpr::eq(mod_g_2, ChcExpr::int(0));

    // Build: ite((mod G 2)=0, H+1, H+2)
    let h_if_even = ChcExpr::add(ChcExpr::var(h_var.clone()), ChcExpr::int(1));
    let h_if_odd = ChcExpr::add(ChcExpr::var(h_var.clone()), ChcExpr::int(2));
    let h_next_expr = ChcExpr::ite(mod_eq_0, h_if_even, h_if_odd);

    let loop_constraint = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::var(g_next.clone()),
            ChcExpr::add(ChcExpr::var(g_var.clone()), ChcExpr::int(1)),
        ),
        ChcExpr::eq(ChcExpr::var(h_next.clone()), h_next_expr),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(g_var), ChcExpr::var(h_var)])],
            Some(loop_constraint),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(g_next), ChcExpr::var(h_next)]),
    ));

    // Define canonical vars for inv
    let canonical_g = ChcVar::new("__p0_a0", ChcSort::Int);
    let canonical_h = ChcVar::new("__p0_a1", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![canonical_g, canonical_h];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    let provider = ModResidueHintProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    // Should have exactly 2 hints: (mod __p0_a0 2) = 0 and (mod __p0_a0 2) = 1
    assert_eq!(
        hints.len(),
        2,
        "Expected exactly 2 mod-residue hints. Got: {:?}",
        hints
            .iter()
            .map(|h| format!("{:?}", h.formula))
            .collect::<Vec<_>>()
    );

    // Check both residues are present
    let has_residue_0 = hints.iter().any(|h| {
        let s = format!("{:?}", h.formula);
        s.contains("Mod") && s.contains("__p0_a0") && s.ends_with("Int(0)])")
    });
    let has_residue_1 = hints.iter().any(|h| {
        let s = format!("{:?}", h.formula);
        s.contains("Mod") && s.contains("__p0_a0") && s.ends_with("Int(1)])")
    });

    assert!(
        has_residue_0,
        "Missing residue 0 hint. Got: {:?}",
        hints
            .iter()
            .map(|h| format!("{:?}", h.formula))
            .collect::<Vec<_>>()
    );
    assert!(
        has_residue_1,
        "Missing residue 1 hint. Got: {:?}",
        hints
            .iter()
            .map(|h| format!("{:?}", h.formula))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_mod_residue_propagates_to_predecessor_on_dillig02_benchmark() {
    let input =
        include_str!("../../../../../benchmarks/chc-comp/2025/extra-small-lia/dillig02_m_000.smt2");
    let problem = crate::ChcParser::parse(input).expect("parse dillig02_m benchmark");

    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "inv")
        .expect("benchmark must declare inv")
        .id;
    let inv1 = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "inv1")
        .expect("benchmark must declare inv1")
        .id;

    let inv_canonical = canonical_vars_for_pred(&problem, inv).expect("canonical vars for inv");
    let inv1_canonical = canonical_vars_for_pred(&problem, inv1).expect("canonical vars for inv1");

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(inv_canonical.as_slice())
        } else if pred == inv1 {
            Some(inv1_canonical.as_slice())
        } else {
            None
        }
    };

    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let provider = ModResidueHintProvider;
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let build_sum = |vars: &[ChcVar]| {
        // Build a flat n-ary Add matching the hint generator's output.
        let args: Vec<Arc<ChcExpr>> = [2usize, 3, 4, 5]
            .into_iter()
            .map(|idx| Arc::new(ChcExpr::var(vars[idx].clone())))
            .collect();
        ChcExpr::Op(crate::ChcOp::Add, args)
    };
    let inv_sum = build_sum(&inv_canonical);
    let inv1_sum = build_sum(&inv1_canonical);

    let expect_residue = |predicate: PredicateId, expr: ChcExpr, residue: i64| {
        let expected = ChcExpr::eq(
            ChcExpr::mod_op(expr, ChcExpr::int(2)),
            ChcExpr::int(residue),
        );
        hints
            .iter()
            .find(|hint| hint.predicate == predicate && hint.formula == expected)
            .cloned()
    };

    assert!(
        expect_residue(inv1, inv1_sum.clone(), 0).is_some(),
        "missing direct inv1 modular hint on dillig02_m: {hints:?}"
    );
    assert!(
        expect_residue(inv1, inv1_sum, 1).is_some(),
        "missing direct inv1 odd-residue hint on dillig02_m: {hints:?}"
    );

    let propagated_even =
        expect_residue(inv, inv_sum.clone(), 0).expect("missing propagated even hint for inv");
    let propagated_odd =
        expect_residue(inv, inv_sum, 1).expect("missing propagated odd hint for inv");

    assert_eq!(
        propagated_even.source, "mod-residue-pred-v1",
        "inv hint should come from predecessor propagation"
    );
    assert_eq!(
        propagated_odd.source, "mod-residue-pred-v1",
        "inv hint should come from predecessor propagation"
    );
}

#[test]
fn test_collect_all_hints_with_extra_hints() {
    use crate::ChcSort;

    // Test that extra runtime hints are merged with static providers
    let problem = ChcProblem::new();
    let vars: Vec<ChcVar> = vec![];
    let vars_ref: &[ChcVar] = &vars;
    let canonical_vars_fn = |_: PredicateId| -> Option<&[ChcVar]> { Some(vars_ref) };
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    // Create extra runtime hints (like from model-checker-consumer loop invariants)
    let extra_hint = LemmaHint::new(
        PredicateId(42),
        ChcExpr::ge(
            ChcExpr::var(ChcVar::new("i", ChcSort::Int)),
            ChcExpr::int(0),
        ),
        50, // Lower priority than built-in providers
        "model-checker-consumer-user-invariant",
    );
    let extra = vec![extra_hint];

    // Collect with extra hints
    let hints = collect_all_hints_with_extra(&req, &extra);

    // Verify extra hint is included
    let found_extra = hints.iter().any(|h| {
        h.predicate == PredicateId(42) && h.source == "model-checker-consumer-user-invariant"
    });
    assert!(
        found_extra,
        "Extra runtime hint should be in collected hints"
    );

    // Verify hints are sorted by priority (extra hint has priority 50, should come first)
    if !hints.is_empty() && hints[0].source == "model-checker-consumer-user-invariant" {
        assert_eq!(hints[0].priority, 50);
    }

    // Verify collect_all_hints_with_extra with empty extras
    let hints_no_extra = collect_all_hints_with_extra(&req, &[]);
    let found_extra_in_no_extra = hints_no_extra.iter().any(|h| {
        h.predicate == PredicateId(42) && h.source == "model-checker-consumer-user-invariant"
    });
    assert!(
        !found_extra_in_no_extra,
        "Extra hint should not appear when not provided"
    );
}

#[test]
fn test_collect_all_hints_with_extra_deduplication() {
    use crate::ChcSort;

    // Test that duplicate hints are deduplicated
    let problem = ChcProblem::new();
    let vars: Vec<ChcVar> = vec![];
    let vars_ref: &[ChcVar] = &vars;
    let canonical_vars_fn = |_: PredicateId| -> Option<&[ChcVar]> { Some(vars_ref) };
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);

    // Create two identical extra hints
    let formula = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::int(0),
    );
    let hint1 = LemmaHint::new(PredicateId(0), formula.clone(), 100, "source1");
    let hint2 = LemmaHint::new(PredicateId(0), formula.clone(), 100, "source2");
    let extra = vec![hint1, hint2];

    let hints = collect_all_hints_with_extra(&req, &extra);

    // Count how many hints have this exact formula for predicate 0
    let count = hints
        .iter()
        .filter(|h| {
            h.predicate == PredicateId(0) && format!("{:?}", h.formula) == format!("{formula:?}")
        })
        .count();

    // Should be deduplicated to 1 (same predicate + formula)
    assert_eq!(count, 1, "Duplicate hints should be deduplicated");
}

// ============================================================================
// ModResidueHintProvider unit tests (extract_mod_terms, contains_next_var, etc.)
// ============================================================================

#[test]
fn test_extract_mod_terms_simple_mod() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(3));
    let terms = ModResidueHintProvider::extract_mod_terms(&expr);
    assert_eq!(terms.len(), 1);
    assert_eq!(terms[0].0, ChcExpr::var(x));
    assert_eq!(terms[0].1, 3);
}

#[test]
fn test_extract_mod_terms_skips_modulus_one() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(1));
    assert!(ModResidueHintProvider::extract_mod_terms(&expr).is_empty());
}

#[test]
fn test_extract_mod_terms_skips_zero_modulus() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(0));
    assert!(ModResidueHintProvider::extract_mod_terms(&expr).is_empty());
}

#[test]
fn test_extract_mod_terms_skips_next_var_dividend() {
    let x_next = ChcVar::new("x_next", ChcSort::Int);
    let expr = ChcExpr::mod_op(ChcExpr::var(x_next), ChcExpr::int(2));
    assert!(ModResidueHintProvider::extract_mod_terms(&expr).is_empty());
}

#[test]
fn test_extract_mod_terms_nested_in_and() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(2)),
            ChcExpr::int(0),
        ),
        ChcExpr::ge(ChcExpr::var(y), ChcExpr::int(0)),
    );
    let terms = ModResidueHintProvider::extract_mod_terms(&expr);
    assert_eq!(terms.len(), 1);
    assert_eq!(terms[0].0, ChcExpr::var(x));
    assert_eq!(terms[0].1, 2);
}

#[test]
fn test_extract_mod_terms_extracts_vars_from_sum_dividend() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let sum = ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::var(b.clone()));
    let expr = ChcExpr::mod_op(sum.clone(), ChcExpr::int(3));
    let terms = ModResidueHintProvider::extract_mod_terms(&expr);
    assert_eq!(terms.len(), 3);
    assert_eq!(terms[0].0, sum);
    assert_eq!(terms[0].1, 3);
    assert!(terms
        .iter()
        .any(|(e, k)| *e == ChcExpr::var(a.clone()) && *k == 3));
    assert!(terms
        .iter()
        .any(|(e, k)| *e == ChcExpr::var(b.clone()) && *k == 3));
}

#[test]
fn test_extract_vars_from_dividend_skips_next_vars() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b_next = ChcVar::new("b_next", ChcSort::Int);
    let mut out = Vec::new();
    let sum = ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::var(b_next));
    ModResidueHintProvider::extract_vars_from_dividend(&sum, 2, &mut out);
    assert_eq!(out.len(), 1);
    assert_eq!(out[0].0, ChcExpr::var(a));
    assert_eq!(out[0].1, 2);
}

#[test]
fn test_extract_divisibility_terms_from_scaled_variable() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(x.clone()));
    let terms = ModResidueHintProvider::extract_divisibility_terms(&expr);
    assert_eq!(terms.len(), 1);
    assert_eq!(terms[0].0, ChcExpr::var(x));
    assert_eq!(terms[0].1, 3);
}

#[test]
fn test_contains_next_var_true() {
    let x_next = ChcVar::new("counter_next", ChcSort::Int);
    assert!(ModResidueHintProvider::contains_next_var(&ChcExpr::var(
        x_next
    )));
}

#[test]
fn test_contains_next_var_false() {
    let x = ChcVar::new("counter", ChcSort::Int);
    assert!(!ModResidueHintProvider::contains_next_var(&ChcExpr::var(x)));
}

#[test]
fn test_contains_next_var_nested() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y_next = ChcVar::new("y_next", ChcSort::Int);
    let expr = ChcExpr::add(ChcExpr::var(x), ChcExpr::var(y_next));
    assert!(ModResidueHintProvider::contains_next_var(&expr));
}

#[test]
fn test_contains_next_var_integer_constant() {
    assert!(!ModResidueHintProvider::contains_next_var(&ChcExpr::int(
        42
    )));
}

#[test]
fn test_extract_mod_terms_multiple_distinct_mods() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(2)),
            ChcExpr::int(0),
        ),
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(y.clone()), ChcExpr::int(3)),
            ChcExpr::int(1),
        ),
    );
    let terms = ModResidueHintProvider::extract_mod_terms(&expr);
    assert!(terms
        .iter()
        .any(|(e, k)| *e == ChcExpr::var(x.clone()) && *k == 2));
    assert!(terms
        .iter()
        .any(|(e, k)| *e == ChcExpr::var(y.clone()) && *k == 3));
}

#[test]
fn test_extract_mod_terms_non_constant_modulus_ignored() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let expr = ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::var(y));
    assert!(ModResidueHintProvider::extract_mod_terms(&expr).is_empty());
}

#[test]
fn test_problem_contains_mod_div_true() {
    use crate::{ClauseBody, ClauseHead, HornClause};
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2)),
                ChcExpr::int(0),
            )),
        ),
        ClauseHead::False,
    ));
    assert!(ModSumHintProvider::problem_contains_mod_div(&problem));
}

#[test]
fn test_problem_contains_mod_div_false() {
    use crate::{ClauseBody, ClauseHead, HornClause};
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));
    assert!(!ModSumHintProvider::problem_contains_mod_div(&problem));
}

// ============================================================================
// ModSumHintProvider tests
// ============================================================================

#[test]
fn test_mod_sum_basic_with_mod_problem() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Problem with mod in constraint and 2 int vars -> should generate sum hints
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Self-loop with mod in constraint
    let constraint = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(constraint),
        ),
        ClauseHead::Predicate(
            inv,
            vec![
                ChcExpr::add(ChcExpr::var(x), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(y), ChcExpr::int(1)),
            ],
        ),
    ));

    let canonical_a = ChcVar::new("a0", ChcSort::Int);
    let canonical_b = ChcVar::new("a1", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![canonical_a.clone(), canonical_b.clone()];
    let canonical_ref: &[ChcVar] = &canonical_vars;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ModSumHintProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    // With 2 int vars and mod in problem, should get pairwise sum mod hints
    assert!(
        !hints.is_empty(),
        "ModSumHintProvider should generate hints for 2+ int vars with mod in problem"
    );

    // All hints should be for predicate inv
    assert!(hints.iter().all(|h| h.predicate == inv));

    // All hints should have source "mod-sum-v1"
    assert!(hints.iter().all(|h| h.source == "mod-sum-v1"));

    // Hints should contain (mod (+ a0 a1) 2) = 0 and (mod (+ a0 a1) 2) = 1
    let sum = ChcExpr::add(ChcExpr::var(canonical_a), ChcExpr::var(canonical_b));
    let expected_0 = ChcExpr::eq(
        ChcExpr::mod_op(sum.clone(), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    let expected_1 = ChcExpr::eq(ChcExpr::mod_op(sum, ChcExpr::int(2)), ChcExpr::int(1));

    assert!(
        hints.iter().any(|h| h.formula == expected_0),
        "Missing (mod (+ a0 a1) 2) = 0 hint. Got: {:?}",
        hints.iter().map(|h| &h.formula).collect::<Vec<_>>()
    );
    assert!(
        hints.iter().any(|h| h.formula == expected_1),
        "Missing (mod (+ a0 a1) 2) = 1 hint. Got: {:?}",
        hints.iter().map(|h| &h.formula).collect::<Vec<_>>()
    );
}

#[test]
fn test_mod_sum_startup_only() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // ModSumHintProvider should only collect at Startup stage
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2)),
                ChcExpr::int(0),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(y), ChcExpr::int(0)]),
    ));

    let canonical_vars: Vec<ChcVar> = vec![
        ChcVar::new("a0", ChcSort::Int),
        ChcVar::new("a1", ChcSort::Int),
    ];
    let canonical_ref: &[ChcVar] = &canonical_vars;
    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ModSumHintProvider;

    // Stuck stage should produce nothing
    let req = HintRequest::new(HintStage::Stuck, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);
    assert!(
        hints.is_empty(),
        "ModSumHintProvider should not produce hints at Stuck stage"
    );
}

#[test]
fn test_mod_sum_no_mod_in_problem() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Problem without any mod/div operations -> no hints
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Only linear arithmetic, no mod/div
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(y), ChcExpr::int(0)]),
    ));

    let canonical_vars: Vec<ChcVar> = vec![
        ChcVar::new("a0", ChcSort::Int),
        ChcVar::new("a1", ChcSort::Int),
    ];
    let canonical_ref: &[ChcVar] = &canonical_vars;
    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ModSumHintProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    assert!(
        hints.is_empty(),
        "ModSumHintProvider should not produce hints when problem has no mod/div"
    );
}

#[test]
fn test_mod_sum_needs_at_least_two_int_vars() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Predicate with only 1 int var -> no sum hints possible
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2)),
                ChcExpr::int(0),
            )),
        ),
        ClauseHead::False,
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

    let provider = ModSumHintProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    assert!(
        hints.is_empty(),
        "ModSumHintProvider should not generate hints with only 1 int var"
    );
}

#[test]
fn test_mod_sum_three_vars_generates_full_sum_hint() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // 3 int vars should generate pairwise sum hints AND full sum hint
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);

    // Need mod/div in the problem for ModSum to activate
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                inv,
                vec![
                    ChcExpr::var(x.clone()),
                    ChcExpr::var(y.clone()),
                    ChcExpr::var(z.clone()),
                ],
            )],
            Some(ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2)),
                ChcExpr::int(0),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(y), ChcExpr::var(z), ChcExpr::int(0)]),
    ));

    let a0 = ChcVar::new("a0", ChcSort::Int);
    let a1 = ChcVar::new("a1", ChcSort::Int);
    let a2 = ChcVar::new("a2", ChcSort::Int);
    let canonical_vars: Vec<ChcVar> = vec![a0.clone(), a1.clone(), a2.clone()];
    let canonical_ref: &[ChcVar] = &canonical_vars;
    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ModSumHintProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    assert!(!hints.is_empty(), "Should generate hints with 3 int vars");

    // Should have full sum hint: (mod (+ a0 a1 a2) 2) = 0 and = 1
    let full_sum = ChcExpr::add(
        ChcExpr::add(ChcExpr::var(a0), ChcExpr::var(a1)),
        ChcExpr::var(a2),
    );
    let full_sum_mod_0 = ChcExpr::eq(
        ChcExpr::mod_op(full_sum.clone(), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    let full_sum_mod_1 = ChcExpr::eq(ChcExpr::mod_op(full_sum, ChcExpr::int(2)), ChcExpr::int(1));

    assert!(
        hints.iter().any(|h| h.formula == full_sum_mod_0),
        "Missing full sum mod 2 = 0 hint. Got: {:?}",
        hints.iter().map(|h| &h.formula).collect::<Vec<_>>()
    );
    assert!(
        hints.iter().any(|h| h.formula == full_sum_mod_1),
        "Missing full sum mod 2 = 1 hint. Got: {:?}",
        hints.iter().map(|h| &h.formula).collect::<Vec<_>>()
    );
}

#[test]
fn test_mod_residue_no_self_loop_produces_nothing() {
    // ModResidueHintProvider requires self-loop clauses to fire
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("p", vec![ChcSort::Int]);
    let q = problem.declare_predicate("q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);

    // p(x) /\ (mod x 2) = 0 => q(x)  -- not a self-loop
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(2)),
                ChcExpr::int(0),
            )),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x)]),
    ));

    let canonical_vars: Vec<ChcVar> = vec![ChcVar::new("a0", ChcSort::Int)];
    let canonical_ref: &[ChcVar] = &canonical_vars;
    let canonical_vars_fn = |_: PredicateId| -> Option<&[ChcVar]> { Some(canonical_ref) };

    let provider = ModResidueHintProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    assert!(
        hints.is_empty(),
        "ModResidueHintProvider should not fire for non-self-loop clauses"
    );
}

#[test]
fn test_mod_residue_stuck_stage_allows_higher_modulus() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // ModResidueHintProvider allows modulus up to 4 at Startup, up to 8 at Stuck
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let x_next = ChcVar::new("X_prime", ChcSort::Int);

    // Self-loop: inv(x) /\ (mod x 6) = 0 /\ x_next = x + 1 => inv(x_next)
    let constraint = ChcExpr::and(
        ChcExpr::eq(
            ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(6)),
            ChcExpr::int(0),
        ),
        ChcExpr::eq(
            ChcExpr::var(x_next.clone()),
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ),
    );

    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x)])], Some(constraint)),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x_next)]),
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

    let provider = ModResidueHintProvider;

    // At Startup (max_enum=4), modulus 6 should be skipped
    let req_startup = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints_startup = Vec::new();
    provider.collect(&req_startup, &mut hints_startup);
    assert!(
        hints_startup.is_empty(),
        "Modulus 6 should be skipped at Startup (max_enum=4)"
    );

    // At Stuck (max_enum=8), modulus 6 should produce 6 residue hints
    let req_stuck = HintRequest::new(HintStage::Stuck, &problem, &canonical_vars_fn);
    let mut hints_stuck = Vec::new();
    provider.collect(&req_stuck, &mut hints_stuck);
    assert_eq!(
        hints_stuck.len(),
        6,
        "Modulus 6 at Stuck stage should produce 6 residue hints (0..5). Got: {:?}",
        hints_stuck
            .iter()
            .map(|h| format!("{:?}", h.formula))
            .collect::<Vec<_>>()
    );
}

#[test]
fn test_mod_residue_emits_divisibility_hint_from_scaled_head_arg() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(inv, vec![ChcExpr::mul(ChcExpr::int(3), ChcExpr::var(x))]),
    ));

    let canonical_x = ChcVar::new("a0", ChcSort::Int);
    let canonical_vars = vec![canonical_x.clone()];
    let canonical_ref: &[ChcVar] = &canonical_vars;
    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ModResidueHintProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let expected = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(canonical_x), ChcExpr::int(3)),
        ChcExpr::int(0),
    );
    assert!(
        hints
            .iter()
            .any(|hint| hint.predicate == inv && hint.formula == expected),
        "missing divisibility hint from scaled head arg: {hints:?}"
    );
}

#[test]
fn test_mod_residue_propagates_clause_local_sum_definition_to_predecessor() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    let mut problem = ChcProblem::new();
    let pre = problem.declare_predicate("pre", vec![ChcSort::Int, ChcSort::Int]);
    let loop_pred = problem.declare_predicate("loop", vec![ChcSort::Int]);

    let x = ChcVar::new("X", ChcSort::Int);
    let y = ChcVar::new("Y", ChcSort::Int);
    let g = ChcVar::new("G", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(pre, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::var(g.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            )),
        ),
        ClauseHead::Predicate(loop_pred, vec![ChcExpr::var(g)]),
    ));

    let z = ChcVar::new("Z", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(loop_pred, vec![ChcExpr::var(z.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(z.clone()), ChcExpr::int(2)),
                ChcExpr::int(0),
            )),
        ),
        ClauseHead::Predicate(loop_pred, vec![ChcExpr::var(z)]),
    ));

    let pre_a0 = ChcVar::new("__p0_a0", ChcSort::Int);
    let pre_a1 = ChcVar::new("__p0_a1", ChcSort::Int);
    let loop_a0 = ChcVar::new("__p1_a0", ChcSort::Int);
    let pre_canonical = vec![pre_a0.clone(), pre_a1.clone()];
    let loop_canonical = vec![loop_a0];
    let pre_ref: &[ChcVar] = &pre_canonical;
    let loop_ref: &[ChcVar] = &loop_canonical;

    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == pre {
            Some(pre_ref)
        } else if pred == loop_pred {
            Some(loop_ref)
        } else {
            None
        }
    };

    let provider = ModResidueHintProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    let expected_even = ChcExpr::eq(
        ChcExpr::mod_op(
            ChcExpr::add(ChcExpr::var(pre_a0.clone()), ChcExpr::var(pre_a1.clone())),
            ChcExpr::int(2),
        ),
        ChcExpr::int(0),
    );
    let expected_odd = ChcExpr::eq(
        ChcExpr::mod_op(
            ChcExpr::add(ChcExpr::var(pre_a0), ChcExpr::var(pre_a1)),
            ChcExpr::int(2),
        ),
        ChcExpr::int(1),
    );

    assert!(
        hints.iter().any(|hint| {
            hint.predicate == pre
                && hint.source == "mod-residue-pred-v1"
                && hint.formula == expected_even
        }),
        "missing propagated even predecessor hint through clause-local sum: {hints:?}"
    );
    assert!(
        hints.iter().any(|hint| {
            hint.predicate == pre
                && hint.source == "mod-residue-pred-v1"
                && hint.formula == expected_odd
        }),
        "missing propagated odd predecessor hint through clause-local sum: {hints:?}"
    );
}

#[test]
fn test_mod_sum_skips_bool_vars() {
    use crate::{ChcSort, ClauseBody, ClauseHead, HornClause};

    // Predicate with 1 Int and 1 Bool var -> only 1 int var -> no sum hints
    let mut problem = ChcProblem::new();
    let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Bool]);

    let x = ChcVar::new("x", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Bool);

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(inv, vec![ChcExpr::var(x.clone()), ChcExpr::var(b.clone())])],
            Some(ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2)),
                ChcExpr::int(0),
            )),
        ),
        ClauseHead::Predicate(inv, vec![ChcExpr::int(0), ChcExpr::var(b)]),
    ));

    let canonical_vars: Vec<ChcVar> = vec![
        ChcVar::new("a0", ChcSort::Int),
        ChcVar::new("a1", ChcSort::Bool),
    ];
    let canonical_ref: &[ChcVar] = &canonical_vars;
    let canonical_vars_fn = |pred: PredicateId| -> Option<&[ChcVar]> {
        if pred == inv {
            Some(canonical_ref)
        } else {
            None
        }
    };

    let provider = ModSumHintProvider;
    let req = HintRequest::new(HintStage::Startup, &problem, &canonical_vars_fn);
    let mut hints = Vec::new();
    provider.collect(&req, &mut hints);

    assert!(
        hints.is_empty(),
        "ModSumHintProvider should skip Bool vars, only 1 Int var remaining"
    );
}
