// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::cancellation::CancellationToken;
use std::fmt;
use std::sync::Arc;

fn integer(name: &str) -> ChcExpr {
    ChcExpr::var(ChcVar::new(name, ChcSort::Int))
}

#[test]
fn complete_keys_keep_commutative_identity_and_distinct_variables() {
    let budget = SynthesisBudget::unbounded();
    let left = ChcExpr::add(integer("left"), integer("right"));
    let swapped = ChcExpr::add(integer("right"), integer("left"));
    assert_eq!(
        validation_expr_key_checked(&left, &budget).unwrap(),
        validation_expr_key_checked(&swapped, &budget).unwrap()
    );
    assert_ne!(
        validation_expr_key_checked(&integer("left"), &budget).unwrap(),
        validation_expr_key_checked(&integer("right"), &budget).unwrap()
    );
    let boolean_int = |name| {
        ChcExpr::Op(
            ChcOp::Ite,
            vec![
                Arc::new(ChcExpr::var(ChcVar::new(name, ChcSort::Bool))),
                Arc::new(ChcExpr::Int(1)),
                Arc::new(ChcExpr::Int(0)),
            ],
        )
    };
    let independent = ChcExpr::and(
        ChcExpr::eq(boolean_int("left"), ChcExpr::Int(0)),
        ChcExpr::eq(boolean_int("right"), ChcExpr::Int(1)),
    );
    assert!(!validation_formula_proves_unsat_checked(&independent, &budget).unwrap());
}

#[test]
fn interrupted_debug_buffer_is_not_a_key() {
    struct CancelDuringKey(CancellationToken);
    impl fmt::Debug for CancelDuringKey {
        fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
            formatter.write_str("shared-prefix")?;
            self.0.cancel();
            formatter.write_str("-different-suffix")
        }
    }
    let token = CancellationToken::new();
    let budget = SynthesisBudget::new(None, Some(token.clone()));
    assert_eq!(
        budget::debug_key(&CancelDuringKey(token), &budget),
        Err(budget::ValidationStopped)
    );
}

#[test]
fn expression_rewrites_discard_partial_results_on_stop() {
    let expr = ChcExpr::Op(
        ChcOp::Add,
        (0..128)
            .map(|index| Arc::new(integer(&format!("x{index}"))))
            .collect(),
    );
    let mut visits = 0;
    assert!(expr
        .simplify_constants_checked(|| {
            visits += 1;
            visits >= 8
        })
        .is_none());
    assert!(visits >= 8);
    let substitutions = (0..128)
        .map(|index| {
            (
                ChcVar::new(format!("x{index}"), ChcSort::Int),
                ChcExpr::Int(index),
            )
        })
        .collect::<Vec<_>>();
    let mut visits = 0;
    assert!(expr
        .substitute_checked(&substitutions[..1], || {
            visits += 1;
            visits >= 8
        })
        .is_none());
    assert!(visits >= 8);
    let complete = expr.substitute_checked(&substitutions, || false).unwrap();
    assert_eq!(complete, expr.substitute(&substitutions));
    assert_eq!(
        ChcExpr::add(ChcExpr::Int(2), ChcExpr::Int(3)).simplify_constants_checked(|| false),
        Some(ChcExpr::Int(5))
    );
}

#[test]
fn cancellation_is_distinct_from_a_proved_contradiction() {
    let formula = ChcExpr::and(
        ChcExpr::eq(integer("x"), ChcExpr::Int(0)),
        ChcExpr::ne(integer("x"), ChcExpr::Int(0)),
    );
    assert!(
        validation_formula_proves_unsat_checked(&formula, &SynthesisBudget::unbounded()).unwrap()
    );
    let token = CancellationToken::new();
    token.cancel();
    let budget = SynthesisBudget::new(None, Some(token));
    assert_eq!(
        validation_formula_proves_unsat_checked(&formula, &budget),
        Err(budget::ValidationStopped)
    );
}

#[test]
fn elapsed_deadline_returns_no_canonical_expression() {
    let budget = SynthesisBudget::new(Some(Instant::now()), None);
    assert_eq!(
        canonical_validation_expr_checked(&integer("x"), &budget),
        Err(budget::ValidationStopped)
    );
}

#[test]
fn completed_operation_cannot_publish_after_cancellation() {
    let token = CancellationToken::new();
    let budget = SynthesisBudget::new(None, Some(token.clone()));
    assert_eq!(
        budget::run(&budget, || {
            token.cancel();
            Ok(true)
        }),
        Err(budget::ValidationStopped)
    );
}

#[test]
fn final_validation_checks_budget_even_without_another_clause() {
    let problem = ChcProblem::new();
    let model = InvariantModel::new();
    let token = CancellationToken::new();
    token.cancel();
    let budget = SynthesisBudget::new(None, Some(token));
    let mut smt = problem.make_smt_context();
    let mut stats = AlgebraicValidationStats::default();
    assert_eq!(
        validate_model_with_smt_and_stats(&problem, &model, false, &budget, &mut smt, &mut stats),
        AlgebraicValidationResult::DeadlineExceeded
    );
    assert_eq!(stats.lra_affine_original_clause_validation_successes, 0);
    assert_eq!(stats.lra_affine_original_clause_validation_unknowns, 1);
}

#[test]
fn alias_rewrite_has_fixed_roots_and_stops_mid_chain() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    let body = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(z.clone()), ChcExpr::var(y.clone())),
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::var(x.clone())),
    );
    let actual = validation_alias_substitution_checked(&body, &SynthesisBudget::unbounded())
        .unwrap()
        .into_iter()
        .map(|(var, value)| (var.name, value))
        .collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(actual.len(), 2);
    assert_eq!(actual["y"], ChcExpr::var(x.clone()));
    assert_eq!(actual["z"], ChcExpr::var(x.clone()));
    assert!(validation_alias_substitution_checked(
        &body,
        &SynthesisBudget::cancelling_after_polls(8)
    )
    .is_err());
    let vars = (0..32)
        .map(|index| ChcVar::new(format!("v{index}"), ChcSort::Int))
        .collect::<Vec<_>>();
    let mut parents = FxHashMap::default();
    for pair in vars.windows(2) {
        parents.insert(pair[0].clone(), pair[1].clone());
    }
    parents.insert(vars[31].clone(), vars[31].clone());
    assert!(validation_alias_find_checked(
        &mut parents,
        &vars[0],
        &SynthesisBudget::cancelling_after_polls(8)
    )
    .is_err());
}

#[test]
fn linear_rewrite_has_fixed_values_and_stops_mid_pass() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let body = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(a), ChcExpr::Int(5)),
        ChcExpr::eq(ChcExpr::var(b), ChcExpr::add(integer("a"), ChcExpr::Int(7))),
    );
    let actual =
        validation_body_linear_substitution_checked(&body, &[], &SynthesisBudget::unbounded())
            .unwrap()
            .into_iter()
            .map(|(var, value)| (var.name, value))
            .collect::<std::collections::BTreeMap<_, _>>();
    assert_eq!(actual["a"], ChcExpr::Int(5));
    assert_eq!(actual["b"], ChcExpr::Int(12));
    assert!(validation_body_linear_substitution_checked(
        &body,
        &[],
        &SynthesisBudget::cancelling_after_polls(10)
    )
    .is_err());
    let residue = ChcExpr::eq(
        ChcExpr::Op(
            ChcOp::Mod,
            vec![
                Arc::new(ChcExpr::add(integer("x"), ChcExpr::Int(1))),
                Arc::new(ChcExpr::Int(4)),
            ],
        ),
        ChcExpr::Int(2),
    );
    let result =
        validation_linear_mod_residue_atom_checked(&residue, &SynthesisBudget::unbounded())
            .unwrap()
            .unwrap();
    assert_eq!(result.modulus, 4);
    assert_eq!(result.residue, 2);
    assert_eq!(result.expr.constant, 1);
    assert_eq!(result.expr.coeffs["x"], 1);
    assert!(validation_linear_mod_residue_atom_checked(
        &residue,
        &SynthesisBudget::cancelling_after_polls(4)
    )
    .is_err());
}

#[test]
fn conjunction_rewrite_keeps_fixed_output_and_discards_stopped_scan() {
    let boolean = |name: &str| ChcExpr::var(ChcVar::new(name, ChcSort::Bool));
    let nested = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::Op(
                ChcOp::And,
                vec![Arc::new(boolean("a")), Arc::new(ChcExpr::Bool(true))],
            )),
            Arc::new(boolean("b")),
        ],
    );
    assert_eq!(
        nested.simplify_constants_checked(|| false),
        Some(ChcExpr::Op(
            ChcOp::And,
            vec![Arc::new(boolean("a")), Arc::new(boolean("b"))]
        ))
    );
    let args = (0..32)
        .map(|index| Arc::new(boolean(&format!("p{index}"))))
        .chain((0..32).map(|index| Arc::new(ChcExpr::not(boolean(&format!("q{index}"))))))
        .collect();
    let comparison = ChcExpr::Op(ChcOp::And, args);
    let mut polls = 0;
    assert!(comparison
        .simplify_constants_checked(|| {
            polls += 1;
            polls >= 400
        })
        .is_none());
    assert!(polls >= 400);
    assert_eq!(
        comparison.simplify_constants_checked(|| false),
        Some(comparison.clone())
    );
}

#[test]
fn contradiction_pair_scan_distinguishes_stop_from_false() {
    let boolean = |name: &str| ChcExpr::var(ChcVar::new(name, ChcSort::Bool));
    let negatives = (0..32).map(|index| {
        Arc::new(ChcExpr::not(ChcExpr::or(
            boolean(&format!("q{index}")),
            boolean(&format!("r{index}")),
        )))
    });
    let positives = (0..32).map(|index| Arc::new(boolean(&format!("p{index}"))));
    let formula = ChcExpr::Op(ChcOp::And, negatives.chain(positives).collect());
    assert_eq!(
        is_trivial_contradiction_checked(&formula, || false),
        Some(false)
    );
    let mut polls = 0;
    assert_eq!(
        is_trivial_contradiction_checked(&formula, || {
            polls += 1;
            polls >= 200
        }),
        None
    );
    assert_eq!(polls, 200);
    let contradictory = ChcExpr::and(boolean("x"), ChcExpr::not(boolean("x")));
    assert_eq!(
        is_trivial_contradiction_checked(&contradictory, || false),
        Some(true)
    );
}

#[test]
fn linear_extraction_has_exact_coefficients_and_cancels_inside_map_copy() {
    let expr = ChcExpr::add(
        ChcExpr::mul(ChcExpr::Int(3), integer("x")),
        ChcExpr::sub(integer("y"), ChcExpr::Int(5)),
    );
    let linear = validation_linear_expr(&expr, &SynthesisBudget::unbounded())
        .unwrap()
        .unwrap();
    assert_eq!(linear.constant, -5);
    assert_eq!(linear.coeffs.len(), 2);
    assert_eq!(linear.coeffs["x"], 3);
    assert_eq!(linear.coeffs["y"], 1);
    let wide = ChcExpr::Op(
        ChcOp::Add,
        (0..128)
            .map(|i| Arc::new(integer(&format!("x{i}"))))
            .collect(),
    );
    assert!(validation_linear_expr(&wide, &SynthesisBudget::cancelling_after_polls(80)).is_err());
    let complete = validation_linear_expr(&wide, &SynthesisBudget::unbounded())
        .unwrap()
        .unwrap();
    assert_eq!(complete.coeffs.len(), 128);
    assert_eq!(complete.constant, 0);
    assert!(complete
        .coeffs
        .values()
        .all(|coefficient| *coefficient == 1));
}

#[test]
fn equality_span_checks_each_search_branch_without_publishing_a_partial_answer() {
    let budget = SynthesisBudget::unbounded();
    let x = validation_linear_expr(&integer("x"), &budget)
        .unwrap()
        .unwrap();
    let twice_x = validation_linear_expr(&ChcExpr::mul(ChcExpr::Int(2), integer("x")), &budget)
        .unwrap()
        .unwrap();
    assert!(validation_linear_expr_in_equality_span_bounded(&twice_x, &[x], &budget).unwrap());
    let target = validation_linear_expr(&integer("outside"), &budget)
        .unwrap()
        .unwrap();
    let equalities = (0..6)
        .map(|i| {
            validation_linear_expr(&integer(&format!("e{i}")), &budget)
                .unwrap()
                .unwrap()
        })
        .collect::<Vec<_>>();
    assert!(validation_linear_expr_in_equality_span_bounded(
        &target,
        &equalities,
        &SynthesisBudget::cancelling_after_polls(100)
    )
    .is_err());
    assert!(
        !validation_linear_expr_in_equality_span_bounded(&target, &equalities[..1], &budget)
            .unwrap()
    );
}

#[test]
fn residue_rounds_keep_exact_fixed_point_and_distinguish_abort_from_contradiction() {
    let residue = |name| {
        ChcExpr::Op(
            ChcOp::Mod,
            vec![Arc::new(integer(name)), Arc::new(ChcExpr::Int(4))],
        )
    };
    let conjuncts = vec![
        ChcExpr::eq(residue("x"), ChcExpr::Int(1)),
        ChcExpr::eq(integer("y"), ChcExpr::add(integer("x"), ChcExpr::Int(2))),
    ];
    let result = collect_validation_mod_residues(&conjuncts, &SynthesisBudget::unbounded())
        .unwrap()
        .unwrap();
    assert_eq!(result["x"], (4, 1));
    assert_eq!(result["y"], (4, 3));
    assert!(collect_validation_mod_residues(
        &conjuncts,
        &SynthesisBudget::cancelling_after_polls(30)
    )
    .is_err());
    let contradiction = vec![
        ChcExpr::eq(residue("x"), ChcExpr::Int(1)),
        ChcExpr::eq(residue("x"), ChcExpr::Int(2)),
    ];
    assert!(
        collect_validation_mod_residues(&contradiction, &SynthesisBudget::unbounded())
            .unwrap()
            .is_none()
    );
}

#[test]
fn parallel_substitution_and_resource_fallbacks_have_fixed_expected_expressions() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let input = ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::var(y.clone()));
    let substitution = [(x, ChcExpr::var(y.clone())), (y, ChcExpr::Int(7))];
    assert_eq!(
        input.substitute_checked(&substitution, || false),
        Some(ChcExpr::add(integer("y"), ChcExpr::Int(7)))
    );
    assert_eq!(
        input.substitute_at_node_limit(&substitution, 0),
        Some(input.clone())
    );
    let folded = ChcExpr::add(ChcExpr::Int(2), ChcExpr::Int(3));
    assert_eq!(
        folded.simplify_constants_checked(|| false),
        Some(ChcExpr::Int(5))
    );
    assert_eq!(folded.simplify_constants_at_node_limit(0), Some(folded));
    let mut deep = integer("x");
    for _ in 0..=MAX_EXPR_RECURSION_DEPTH {
        deep = ChcExpr::FuncApp("keep".into(), ChcSort::Int, vec![Arc::new(deep)]);
    }
    let substitution = [(ChcVar::new("x", ChcSort::Int), ChcExpr::Int(7))];
    assert_eq!(
        deep.substitute_checked(&substitution, || false),
        Some(deep.clone())
    );
    assert_eq!(
        deep.simplify_constants_checked(|| false),
        Some(deep.clone())
    );
    let conjunction = ChcExpr::Op(
        ChcOp::And,
        vec![
            Arc::new(ChcExpr::Bool(true)),
            Arc::new(ChcExpr::Bool(false)),
        ],
    );
    assert_eq!(
        conjunction.conjuncts_checked(|| false).unwrap(),
        vec![&ChcExpr::Bool(true), &ChcExpr::Bool(false)]
    );
}

mod rewriter_stop;
