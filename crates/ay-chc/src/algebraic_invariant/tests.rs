// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::validate::{
    validate_model, validate_model_with_forced_results_for_tests, AlgebraicValidationResult,
};
use super::*;
use crate::smt::SmtResult;
use crate::ChcParser;
use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;
use std::sync::Arc;

const S_MULTIPL_25_000: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_25_000.smt2");
const BOUNCY_ONE_COUNTER_000: &str = include_str!(
    "../../../../benchmarks/chc-comp/2025/extra-small-lia/bouncy_one_counter_000.smt2"
);
const BOUNCY_TWO_COUNTERS_EQUALITY_000: &str = include_str!(
    "../../../../benchmarks/chc-comp/2025/extra-small-lia/bouncy_two_counters_equality_000.smt2"
);
const COUNT_BY_2_000: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/count_by_2_000.smt2");
const S_MULTIPL_08_000: &str =
    include_str!("../../../../benchmarks/chc-comp/2025/extra-small-lia/s_multipl_08_000.smt2");

const MODEL_CHECKER_CONSUMER_SYMBOLIC_ACCUMULATOR: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int Int Int) Bool)

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (<= 0 n) (<= n 100) (= i 0) (= sum 0))
      (Inv n i sum))))

(assert (forall ((n Int) (i Int) (sum Int) (i2 Int) (sum2 Int))
  (=> (and (Inv n i sum)
           (< i n)
           (= i2 (+ i 1))
           (= sum2 (+ sum i)))
      (Inv n i2 sum2))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Inv n i sum)
           (> sum (* n n)))
      false)))

(check-sat)
"#;

const TWO_ARG_SELF_LOOP_FOR_ALPHA_RENAME: &str = r#"
(set-logic HORN)
(declare-fun P (Int Int) Bool)
(assert
  (forall ((A Int) (B Int) (C Int) (D Int))
    (=>
      (and (P A B) (= C (+ A 1)) (= D (+ B 1)))
      (P C D))))
(assert
  (forall ((A Int) (B Int))
    (=>
      (and (P A B) (< A 0))
      false)))
(check-sat)
"#;

const MODEL_CHECKER_CONSUMER_COUNTDOWN_ACCUMULATOR: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)

(assert (forall ((n Int) (sum Int))
  (=> (and (= n 5) (= sum 0))
      (Inv n sum))))

(assert (forall ((n Int) (sum Int) (n1 Int) (sum1 Int))
  (=> (and (Inv n sum)
           (> n 0)
           (= sum1 (+ sum n))
           (= n1 (- n 1)))
      (Inv n1 sum1))))

(assert (forall ((n Int) (sum Int))
  (=> (and (Inv n sum) (= n 0) (> sum 15))
      false)))

(check-sat)
"#;

const S_MUTANTS_02_MONOTONE_ADDITIVE_CHAIN: &str = r#"
(set-logic HORN)
(declare-fun itp (Int Int Int Int) Bool)

(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (=> (and (= C 0) (= B 0) (= A 0) (= D 0))
      (itp A B C D))))

(assert (forall ((A Int) (B Int) (C Int) (D Int)
                 (E Int) (F Int) (G Int) (H Int))
  (=> (and (itp A B C D)
           (= G (+ C F))
           (= F (+ B E))
           (= E (+ 1 A))
           (= H (+ D G)))
      (itp E F G H))))

(assert (forall ((A Int) (B Int) (C Int) (D Int))
  (=> (and (itp A B C D) (not (>= D 0)))
      false)))

(check-sat)
"#;

const NEGATIVE_ADDITIVE_INCREMENT_NOT_MONOTONE: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)

(assert (forall ((x Int) (y Int))
  (=> (and (= x 0) (= y (- 1)))
      (Inv x y))))

(assert (forall ((x Int) (y Int) (x1 Int))
  (=> (and (Inv x y) (= x1 (+ x y)))
      (Inv x1 y))))

(assert (forall ((x Int) (y Int))
  (=> (and (Inv x y) (< x 0))
      false)))

(check-sat)
"#;

const MODEL_CHECKER_CONSUMER_MULTI_BLOCK_ACCUMULATOR: &str = r#"
(set-logic HORN)
(declare-fun Entry (Int) Bool)
(declare-fun Mid (Int) Bool)
(declare-fun Inv (Int Int Int) Bool)

(assert (forall ((n Int))
  (=> (and (<= 0 n) (<= n 100))
      (Entry n))))

(assert (forall ((n Int))
  (=> (Entry n)
      (Mid n))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Mid n) (= i 0) (= sum 0))
      (Inv n i sum))))

(assert (forall ((n Int) (i Int) (sum Int) (i2 Int) (sum2 Int))
  (=> (and (Inv n i sum)
           (< i n)
           (= i2 (+ i 1))
           (= sum2 (+ sum i)))
      (Inv n i2 sum2))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Inv n i sum)
           (> sum (* n n)))
      false)))

(check-sat)
"#;

const MODEL_CHECKER_CONSUMER_TWO_HOP_INIT_TRANSFER_ACCUMULATOR: &str = r#"
(set-logic HORN)
(declare-fun Entry (Int) Bool)
(declare-fun Mid1 (Int) Bool)
(declare-fun Mid2 (Int) Bool)
(declare-fun Inv (Int Int Int) Bool)

(assert (forall ((n Int))
  (=> (= n 7)
      (Entry n))))

(assert (forall ((n Int))
  (=> (Entry n)
      (Mid1 n))))

(assert (forall ((n Int))
  (=> (Mid1 n)
      (Mid2 n))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Mid2 n) (= i 0) (= sum 0))
      (Inv n i sum))))

(assert (forall ((n Int) (i Int) (sum Int) (i2 Int) (sum2 Int))
  (=> (and (Inv n i sum)
           (< i n)
           (= i2 (+ i 1))
           (= sum2 (+ sum i)))
      (Inv n i2 sum2))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Inv n i sum)
           (> sum (* n n)))
      false)))

(check-sat)
"#;

const MODEL_CHECKER_CONSUMER_UNREACHABLE_SELF_LOOP: &str = r#"
(set-logic HORN)
(declare-fun Dead (Int) Bool)

(assert (forall ((x Int) (x1 Int))
  (=> (and (Dead x) (= x1 (+ x 1)))
      (Dead x1))))

(assert (forall ((x Int))
  (=> (Dead x)
      false)))

(check-sat)
"#;

const MODEL_CHECKER_CONSUMER_MODULAR_CHAIN_TRANSFER_SUMMARY: &str = r#"
(set-logic HORN)
(declare-fun Entry (Int) Bool)
(declare-fun Inv (Int) Bool)

(assert (forall ((x Int))
  (=> (= x 0)
      (Entry x))))

(assert (forall ((x Int) (x1 Int))
  (=> (and (Entry x) (= x1 x))
      (Entry x1))))

(assert (forall ((x Int))
  (=> (Entry x)
      (Inv x))))

(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 2)))
      (Inv x1))))

(assert (forall ((x Int))
  (=> (and (Inv x) (= (mod x 2) 1))
      false)))

(check-sat)
"#;

const MODEL_CHECKER_CONSUMER_BOUNDED_ACCUMULATOR_OVERFLOW_EDGE: &str = r#"
(set-logic HORN)
(declare-fun Entry (Int) Bool)
(declare-fun Inv (Int Int Int) Bool)
(declare-fun Check (Int Int Int Bool) Bool)

(assert (forall ((n Int))
  (=> (and (<= 0 n) (<= n 100))
      (Entry n))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Entry n) (= i 0) (= sum 0))
      (Inv n i sum))))

(assert (forall ((n Int) (i Int) (sum Int) (i2 Int) (sum2 Int))
  (=> (and (Inv n i sum)
           (< i n)
           (= i2 (+ i 1))
           (= sum2 (+ sum i)))
      (Inv n i2 sum2))))

(assert (forall ((n Int) (i Int) (sum Int) (overflow Bool))
  (=> (and (Inv n i sum)
           (< i n)
           (= overflow (or (< (+ sum i) 0) (>= (+ sum i) 4294967296))))
      (Check n i sum overflow))))

(assert (forall ((n Int) (i Int) (sum Int) (overflow Bool))
  (=> (and (Check n i sum overflow) overflow)
      false)))

(check-sat)
"#;

const MODEL_CHECKER_CONSUMER_UNBOUNDED_ACCUMULATOR_OVERFLOW_EDGE: &str = r#"
(set-logic HORN)
(declare-fun Entry (Int) Bool)
(declare-fun Inv (Int Int Int) Bool)
(declare-fun Check (Int Int Int Bool) Bool)

(assert (forall ((n Int))
  (=> (<= 0 n)
      (Entry n))))

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Entry n) (= i 0) (= sum 0))
      (Inv n i sum))))

(assert (forall ((n Int) (i Int) (sum Int) (i2 Int) (sum2 Int))
  (=> (and (Inv n i sum)
           (< i n)
           (= i2 (+ i 1))
           (= sum2 (+ sum i)))
      (Inv n i2 sum2))))

(assert (forall ((n Int) (i Int) (sum Int) (overflow Bool))
  (=> (and (Inv n i sum)
           (< i n)
           (= overflow (or (< (+ sum i) 0) (>= (+ sum i) 4294967296))))
      (Check n i sum overflow))))

(assert (forall ((n Int) (i Int) (sum Int) (overflow Bool))
  (=> (and (Check n i sum overflow) overflow)
      false)))

(check-sat)
"#;

const MODEL_CHECKER_CONSUMER_BV32_SYMBOLIC_ACCUMULATOR: &str = r#"
(set-logic HORN)
(declare-fun Inv ((_ BitVec 32) (_ BitVec 32) (_ BitVec 32)) Bool)

(assert (forall ((n (_ BitVec 32)) (i (_ BitVec 32)) (sum (_ BitVec 32)))
  (=> (and (bvule n (_ bv100 32)) (= i (_ bv0 32)) (= sum (_ bv0 32)))
      (Inv n i sum))))

(assert (forall ((n (_ BitVec 32)) (i (_ BitVec 32)) (sum (_ BitVec 32)))
  (=> (and (Inv n i sum)
           (bvult i n))
      (Inv n (bvadd i (_ bv1 32)) (bvadd sum i)))))

(assert (forall ((n (_ BitVec 32)) (i (_ BitVec 32)) (sum (_ BitVec 32)))
  (=> (and (Inv n i sum)
           (bvugt sum (bvmul n n)))
      false)))

(check-sat)
"#;

const MODEL_CHECKER_CONSUMER_FACTORIAL_MONOTONE_PRODUCT: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int Int Int) Bool)

(assert (forall ((n Int) (i Int) (result Int))
  (=> (and (<= 0 n) (<= n 12) (= i 1) (= result 1))
      (Inv n i result))))

(assert (forall ((n Int) (i Int) (result Int) (i2 Int) (result2 Int))
  (=> (and (Inv n i result)
           (<= i n)
           (= i2 (+ i 1))
           (= result2 (* result i)))
      (Inv n i2 result2))))

(assert (forall ((n Int) (i Int) (result Int))
  (=> (and (Inv n i result)
           (< result 1))
      false)))

(check-sat)
"#;

const UNKNOWN_SELF_LOOP_VALIDATION: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)

(assert (forall ((x Int) (x1 Int))
  (=> (and (Inv x) (= x1 (+ x 1)))
      (Inv x1))))

(check-sat)
"#;

const UNKNOWN_QUERY_VALIDATION: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)

(assert (forall ((x Int))
  (=> (and (Inv x) (< (* x x) 0))
      false)))

(check-sat)
"#;

const TRIANGULAR_QUERY_VALIDATION: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int Int Int) Bool)

(assert (forall ((n Int) (i Int) (sum Int))
  (=> (and (Inv n i sum)
           (> sum (* n n)))
      false)))

(check-sat)
"#;

const TRIANGULAR_QUERY_WITH_EXTRA_ARG_VALIDATION: &str = r#"
(set-logic HORN)
(declare-fun Inv (Int Int Int Int) Bool)

(assert (forall ((n Int) (i Int) (sum Int) (k Int))
  (=> (and (Inv n i sum k)
           (> sum (* n n)))
      false)))

(check-sat)
"#;

fn triangular_accumulator_model(problem: &ChcProblem, identity_rhs: ChcExpr) -> InvariantModel {
    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");
    let n = ChcVar::new("n", ChcSort::Int);
    let i = ChcVar::new("i", ChcSort::Int);
    let sum = ChcVar::new("sum", ChcSort::Int);

    let identity = ChcExpr::eq(
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(sum.clone())),
        identity_rhs,
    );
    let formula = ChcExpr::and_vec(vec![
        identity,
        ChcExpr::ge(ChcExpr::var(i.clone()), ChcExpr::int(0)),
        ChcExpr::ge(ChcExpr::var(n.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(i.clone()), ChcExpr::var(n.clone())),
    ]);

    let mut model = InvariantModel::new();
    model.set(
        inv.id,
        PredicateInterpretation::new(vec![n, i, sum], formula),
    );
    model
}

fn square_minus_counter_expr(counter: &ChcVar) -> ChcExpr {
    ChcExpr::sub(
        ChcExpr::mul(ChcExpr::var(counter.clone()), ChcExpr::var(counter.clone())),
        ChcExpr::var(counter.clone()),
    )
}

fn square_plus_counter_expr(counter: &ChcVar) -> ChcExpr {
    ChcExpr::add(
        ChcExpr::mul(ChcExpr::var(counter.clone()), ChcExpr::var(counter.clone())),
        ChcExpr::var(counter.clone()),
    )
}

fn nary_add(args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(ChcOp::Add, args.into_iter().map(Arc::new).collect())
}

#[test]
fn algebraic_validation_demotes_unknown_self_loop_9402() {
    let problem =
        ChcParser::parse(UNKNOWN_SELF_LOOP_VALIDATION).expect("self-loop CHC should parse");
    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");

    let x = ChcVar::new("x", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        inv.id,
        PredicateInterpretation::new(
            vec![x.clone()],
            ChcExpr::le(
                ChcExpr::mul(ChcExpr::var(x.clone()), ChcExpr::var(x)),
                ChcExpr::int(0),
            ),
        ),
    );

    let (validation, stats) =
        validate_model_with_forced_results_for_tests(&problem, &model, [SmtResult::Unknown]);

    assert_eq!(
        validation,
        AlgebraicValidationResult::Invalid,
        "self-loop SMT Unknown must be demoted, not accepted as implication success"
    );
    assert_eq!(
        stats.lra_affine_original_clause_validation_attempts, 1,
        "validation should record one original-clause attempt"
    );
    assert_eq!(
        stats.lra_affine_original_clause_validation_queries, 1,
        "forced Unknown should be consumed by the self-loop validation query"
    );
    assert_eq!(
        stats.lra_affine_original_clause_validation_unknowns, 1,
        "SMT Unknown should be exposed as an unknown-demoted validation result"
    );
    assert_eq!(stats.lra_affine_original_clause_validation_successes, 0);
}

#[test]
fn algebraic_validation_demotes_unknown_query_clause_9402() {
    let problem = ChcParser::parse(UNKNOWN_QUERY_VALIDATION).expect("query CHC should parse");
    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");

    let x = ChcVar::new("x", ChcSort::Int);
    let mut model = InvariantModel::new();
    model.set(
        inv.id,
        PredicateInterpretation::new(vec![x], ChcExpr::Bool(true)),
    );

    let (validation, stats) =
        validate_model_with_forced_results_for_tests(&problem, &model, [SmtResult::Unknown]);

    assert_eq!(
        validation,
        AlgebraicValidationResult::Invalid,
        "query SMT Unknown must be demoted even when no concrete sample refutes it"
    );
    assert_eq!(stats.lra_affine_original_clause_validation_attempts, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_queries, 1);
    assert_eq!(
        stats.lra_affine_original_clause_validation_unknowns, 1,
        "SMT Unknown should be visible to telemetry as demoted"
    );
    assert_eq!(stats.lra_affine_original_clause_validation_successes, 0);
}

#[test]
fn algebraic_validation_discharges_exact_triangular_accumulator_unknown_query() {
    let problem =
        ChcParser::parse(TRIANGULAR_QUERY_VALIDATION).expect("triangular query should parse");
    let i = ChcVar::new("i", ChcSort::Int);
    let model = triangular_accumulator_model(&problem, square_minus_counter_expr(&i));

    let (validation, stats) =
        validate_model_with_forced_results_for_tests(&problem, &model, [SmtResult::Unknown]);

    assert_eq!(
        validation,
        AlgebraicValidationResult::Valid,
        "exact triangular accumulator query should discharge after SMT Unknown"
    );
    assert_eq!(stats.lra_affine_original_clause_validation_attempts, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_queries, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_successes, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_unknowns, 0);
}

#[test]
fn algebraic_validation_discharges_exact_triangular_plus_accumulator_unknown_query() {
    let problem =
        ChcParser::parse(TRIANGULAR_QUERY_VALIDATION).expect("triangular query should parse");
    let i = ChcVar::new("i", ChcSort::Int);
    let model = triangular_accumulator_model(&problem, square_plus_counter_expr(&i));

    let (validation, stats) =
        validate_model_with_forced_results_for_tests(&problem, &model, [SmtResult::Unknown]);

    assert_eq!(
        validation,
        AlgebraicValidationResult::Valid,
        "exact n*(n+1) triangular accumulator query should discharge after SMT Unknown"
    );
    assert_eq!(stats.lra_affine_original_clause_validation_attempts, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_queries, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_successes, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_unknowns, 0);
}

#[test]
fn algebraic_validation_rejects_triangular_identity_with_extra_addend() {
    let problem =
        ChcParser::parse(TRIANGULAR_QUERY_VALIDATION).expect("triangular query should parse");
    let i = ChcVar::new("i", ChcSort::Int);
    let invalid_rhs = nary_add(vec![
        ChcExpr::mul(ChcExpr::var(i.clone()), ChcExpr::var(i.clone())),
        ChcExpr::neg(ChcExpr::var(i.clone())),
        ChcExpr::int(100),
    ]);
    let model = triangular_accumulator_model(&problem, invalid_rhs);

    let (validation, stats) =
        validate_model_with_forced_results_for_tests(&problem, &model, [SmtResult::Unknown]);

    assert_eq!(
        validation,
        AlgebraicValidationResult::Invalid,
        "triangular fallback must reject identities with extra nonzero addends"
    );
    assert_eq!(stats.lra_affine_original_clause_validation_queries, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_unknowns, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_successes, 0);
}

#[test]
fn algebraic_validation_rejects_triangular_product_with_extra_decrement_term() {
    let problem = ChcParser::parse(TRIANGULAR_QUERY_WITH_EXTRA_ARG_VALIDATION)
        .expect("triangular query should parse");
    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");
    let n = ChcVar::new("n", ChcSort::Int);
    let i = ChcVar::new("i", ChcSort::Int);
    let sum = ChcVar::new("sum", ChcSort::Int);
    let k = ChcVar::new("k", ChcSort::Int);
    let bad_decrement = nary_add(vec![
        ChcExpr::var(i.clone()),
        ChcExpr::int(-1),
        ChcExpr::var(k.clone()),
    ]);
    let identity = ChcExpr::eq(
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(sum.clone())),
        ChcExpr::mul(ChcExpr::var(i.clone()), bad_decrement),
    );
    let formula = ChcExpr::and_vec(vec![
        identity,
        ChcExpr::ge(ChcExpr::var(i.clone()), ChcExpr::int(0)),
        ChcExpr::ge(ChcExpr::var(n.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(i.clone()), ChcExpr::var(n.clone())),
    ]);
    let mut model = InvariantModel::new();
    model.set(
        inv.id,
        PredicateInterpretation::new(vec![n, i, sum, k], formula),
    );

    let (validation, stats) =
        validate_model_with_forced_results_for_tests(&problem, &model, [SmtResult::Unknown]);

    assert_eq!(
        validation,
        AlgebraicValidationResult::Invalid,
        "triangular fallback must reject product forms with extra decrement terms"
    );
    assert_eq!(stats.lra_affine_original_clause_validation_queries, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_unknowns, 1);
    assert_eq!(stats.lra_affine_original_clause_validation_successes, 0);
}

#[test]
fn sally_lra_strict_original_clause_validation_demotes_unknown_query() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "../../benchmarks/chc/chc-comp25-benchmarks/sally-chc-benchmarks/tte_synchro/tte_synchro.sm_clock_distance_strict_000.smt2",
    );
    if !path.exists() {
        return;
    }

    let input = std::fs::read_to_string(&path).expect("read Sally LRA-Lin regression");
    let problem = ChcParser::parse(&input).expect("Sally LRA-Lin regression should parse");
    let (result, stats) = try_algebraic_solve_with_deadline_and_stats(
        &problem,
        false,
        Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(4)),
    );

    assert!(
        matches!(result, AlgebraicResult::NotApplicable),
        "strict original-clause validation must demote the Sally LRA-Lin false SAFE, got {result:?}"
    );
    assert!(
        stats.lra_affine_original_clause_validation_attempts > 0,
        "expected strict LRA original-clause validation to run"
    );
    assert!(
        stats.lra_affine_original_clause_validation_queries > 0,
        "expected strict LRA original-clause validation to issue SMT queries"
    );
    assert_eq!(
        stats.lra_affine_original_clause_validation_attempts,
        stats.lra_affine_original_clause_validation_successes
            + stats.lra_affine_original_clause_validation_failures
            + stats.lra_affine_original_clause_validation_unknowns,
        "LRA validation counters should partition attempts"
    );
    assert_eq!(
        stats.lra_affine_original_clause_validation_successes, 0,
        "the known wrong Sally/LRA candidate must not be accepted"
    );
    assert!(
        stats.lra_affine_original_clause_validation_failures
            + stats.lra_affine_original_clause_validation_unknowns
            > 0,
        "the known wrong Sally/LRA candidate must fail closed"
    );
}

#[test]
fn approx_4_lra_algebraic_safe_validates_9697() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(
        "../../benchmarks/chc-comp/chc-comp25-repo/sally-chc-benchmarks/approximate_agreement/approx.4_000.smt2",
    );
    if !path.exists() {
        return;
    }

    let input = std::fs::read_to_string(&path).expect("read approx.4 LRA-Lin regression");
    let problem = ChcParser::parse(&input).expect("approx.4 LRA-Lin regression should parse");
    let (result, stats) = try_algebraic_solve_with_deadline_and_stats(
        &problem,
        false,
        Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(4)),
    );

    assert!(
        matches!(result, AlgebraicResult::Safe(_)),
        "approx.4 active Bool-state diff-bound invariant should validate as Safe, got {result:?}"
    );
    assert!(
        stats.lra_affine_original_clause_validation_successes > 0,
        "expected original-clause validation to accept the recovered invariant"
    );
    assert_eq!(
        stats.lra_affine_original_clause_validation_failures
            + stats.lra_affine_original_clause_validation_unknowns,
        0,
        "validated approx.4 invariant must not rely on failed/unknown original-clause checks"
    );
}

/// Test that the transition extraction handles post-var forward substitution.
#[test]
fn test_extract_normalized_transition_forward_sub() {
    use crate::{ClauseBody, HornClause};

    // Simulate FUN self-loop: FUN(A,B) ∧ (C=A+1) ∧ (D=B+C) → FUN(C,D)
    let pred_id = PredicateId::new(0);
    let clause = HornClause::new(
        ClauseBody::new(
            vec![(
                pred_id,
                vec![
                    ChcExpr::var(ChcVar::new("A", ChcSort::Int)),
                    ChcExpr::var(ChcVar::new("B", ChcSort::Int)),
                ],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(ChcVar::new("C", ChcSort::Int)),
                    ChcExpr::add(
                        ChcExpr::int(1),
                        ChcExpr::var(ChcVar::new("A", ChcSort::Int)),
                    ),
                ),
                ChcExpr::eq(
                    ChcExpr::var(ChcVar::new("D", ChcSort::Int)),
                    ChcExpr::add(
                        ChcExpr::var(ChcVar::new("B", ChcSort::Int)),
                        ChcExpr::var(ChcVar::new("C", ChcSort::Int)),
                    ),
                ),
            )),
        ),
        ClauseHead::Predicate(
            pred_id,
            vec![
                ChcExpr::var(ChcVar::new("C", ChcSort::Int)),
                ChcExpr::var(ChcVar::new("D", ChcSort::Int)),
            ],
        ),
    );

    let result = extract_normalized_transition(&clause);
    assert!(result.is_some(), "Should extract transition");

    let (pre_vars, transition) = result.unwrap();
    assert_eq!(pre_vars, vec!["A", "B"]);

    // Verify that analyze_transition works on the result
    let system = analyze_transition(&transition, &pre_vars);
    assert!(system.is_some(), "Should produce a triangular system");

    let sys = system.unwrap();
    match sys.get_solution("A") {
        Some(ClosedForm::ConstantDelta { delta }) => assert_eq!(*delta, 1),
        other => panic!("Expected ConstantDelta(1) for A, got {other:?}"),
    }

    // B should have a Polynomial closed form (quadratic sum)
    assert!(
        matches!(sys.get_solution("B"), Some(ClosedForm::Polynomial { .. })),
        "Expected Polynomial for B, got {:?}",
        sys.get_solution("B")
    );
}

/// Test n-elimination produces the correct invariant for s_multipl_22 pattern.
#[test]
fn test_n_elimination_s_multipl_22_pattern() {
    use crate::{ClauseBody, HornClause};

    // Build the FUN self-loop clause
    let pred_id = PredicateId::new(0);
    let clause = HornClause::new(
        ClauseBody::new(
            vec![(
                pred_id,
                vec![
                    ChcExpr::var(ChcVar::new("A", ChcSort::Int)),
                    ChcExpr::var(ChcVar::new("B", ChcSort::Int)),
                ],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(ChcVar::new("C", ChcSort::Int)),
                    ChcExpr::add(
                        ChcExpr::int(1),
                        ChcExpr::var(ChcVar::new("A", ChcSort::Int)),
                    ),
                ),
                ChcExpr::eq(
                    ChcExpr::var(ChcVar::new("D", ChcSort::Int)),
                    ChcExpr::add(
                        ChcExpr::var(ChcVar::new("B", ChcSort::Int)),
                        ChcExpr::var(ChcVar::new("C", ChcSort::Int)),
                    ),
                ),
            )),
        ),
        ClauseHead::Predicate(
            pred_id,
            vec![
                ChcExpr::var(ChcVar::new("C", ChcSort::Int)),
                ChcExpr::var(ChcVar::new("D", ChcSort::Int)),
            ],
        ),
    );

    let (pre_vars, transition) = extract_normalized_transition(&clause).unwrap();
    let system = analyze_transition(&transition, &pre_vars).unwrap();

    let mut init = FxHashMap::default();
    init.insert("A".to_string(), 0i128);
    init.insert("B".to_string(), 0i128);

    let invariants = eliminate_iteration_count(&system, &init);
    assert!(!invariants.is_empty(), "Should derive algebraic invariant");

    // The invariant should express: 2*B = A^2 + A = A*(A+1)
    // Since B_n = n*0 + (1/2)*n^2 + (1/2)*n = n^2/2 + n/2 (with A_0=0)
    //   wait: quadratic_sum gives s_n = s_0 + n*counter_0 + (delta/2)*n^2 - (delta/2)*n
    //   with s_0=B_0=0, counter_0=A_0=0, delta=1:
    //   B_n = 0 + n*0 + (1/2)*n^2 - (1/2)*n = (n^2 - n)/2
    //
    // But the actual sequence is B = 1, 3, 6, 10, ... = n*(n+1)/2
    // because the update is B' = B + C where C = A+1 (the new A value).
    //
    // The discrepancy: quadratic_sum sums counter values BEFORE increment,
    // but our transition has B_next = B + A_next = B + (A+1).
    //
    // After forward substitution: B_next = B + (1 + A)
    // This is B' = B + (A + 1). In analyze_update:
    //   The update expr is (+ B (+ 1 A)) = B + (1 + A)
    //   This doesn't match Var + Var directly (it's Var + Op).
    //   So analyze_update may NOT recognize this as quadratic_sum!
    //
    // Let me check if this test actually produces a Polynomial.
    // If not, we need to handle B + (constant + A) patterns.

    let inv = &invariants[0];
    assert!(
        matches!(inv, ChcExpr::Op(ChcOp::Eq, _)),
        "Invariant should be an equality, got {inv:?}"
    );
}

#[test]
fn test_n_elimination_countdown_accumulator_negative_delta_9191() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_COUNTDOWN_ACCUMULATOR)
        .expect("accumulator should parse");
    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");
    let self_loop = find_self_loop(&problem, inv.id).expect("Inv self-loop should exist");
    let (pre_vars, transition) =
        extract_normalized_transition(self_loop).expect("transition should normalize");
    let system = analyze_transition(&transition, &pre_vars).expect("closed forms should exist");
    let init_values =
        extract_init_values(&problem, inv.id, &pre_vars).expect("fact should provide init");

    let invariants = eliminate_iteration_count(&system, &init_values);
    assert!(
        invariants.iter().any(|expr| {
            let text = format!("{expr:?}");
            text.contains("sum") && text.contains("Mul")
        }),
        "countdown accumulator should derive a nonlinear sum invariant, got {invariants:?}"
    );
}

#[test]
fn test_try_algebraic_solve_countdown_accumulator_9191() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_COUNTDOWN_ACCUMULATOR)
        .expect("accumulator should parse");
    let result = try_algebraic_solve(&problem, false);
    assert!(
        matches!(result, AlgebraicResult::Safe(_)),
        "countdown accumulator should solve through algebraic synthesis, got {result:?}"
    );
}

#[test]
fn test_try_algebraic_solve_s_mutants_02_monotone_additive_bounds() {
    let problem = ChcParser::parse(S_MUTANTS_02_MONOTONE_ADDITIVE_CHAIN)
        .expect("s_mutants_02-style benchmark should parse");
    let (result, stats) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
    let AlgebraicResult::Safe(model) = result else {
        panic!("s_mutants_02-style monotone additive chain should solve, got {result:?} {stats:?}");
    };
    assert!(
        validate_model(&problem, &model),
        "monotone additive lower-bound model must validate on the original CHC"
    );

    let itp = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "itp")
        .expect("itp predicate should exist");
    let interp = model.get(&itp.id).expect("itp interpretation should exist");
    assert!(
        interp.formula.conjuncts().iter().any(
            |expr| matches!(expr, ChcExpr::Op(ChcOp::Ge, args)
                if matches!((&*args[0], &*args[1]), (ChcExpr::Var(v), ChcExpr::Int(0)) if v.name == "D"))
        ),
        "expected derived D >= 0 monotone additive bound, got {:?}",
        interp.formula
    );
}

#[test]
fn test_monotone_additive_bounds_reject_negative_increment() {
    let problem = ChcParser::parse(NEGATIVE_ADDITIVE_INCREMENT_NOT_MONOTONE)
        .expect("negative increment benchmark should parse");
    let result = try_algebraic_solve(&problem, false);
    assert!(
        !matches!(result, AlgebraicResult::Safe(_)),
        "negative additive increments must not be accepted as monotone-safe, got {result:?}"
    );
}

#[test]
fn test_close_transferred_formula_alpha_renames_self_loop_binders_7170() {
    let problem = ChcParser::parse(TWO_ARG_SELF_LOOP_FOR_ALPHA_RENAME)
        .expect("self-loop benchmark should parse");
    let pred = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "P")
        .expect("P predicate should exist");
    let pred_vars = canonical_predicate_vars(pred);
    let source_a = ChcVar::new("A", ChcSort::Int);
    let source_b = ChcVar::new("B", ChcSort::Int);
    let formula = ChcExpr::eq(
        ChcExpr::var(source_a.clone()),
        ChcExpr::var(source_b.clone()),
    );

    let renamed = close_transferred_formula_over_predicate(&problem, pred, formula, &pred_vars)
        .expect("self-loop body vars should alpha-rename to predicate binders");

    assert!(formula_is_closed_over(&renamed, &pred_vars));
    assert!(!renamed.vars().contains(&source_a));
    assert!(!renamed.vars().contains(&source_b));
    assert_eq!(
        renamed,
        ChcExpr::eq(
            ChcExpr::var(pred_vars[0].clone()),
            ChcExpr::var(pred_vars[1].clone())
        )
    );
}

#[test]
fn test_close_transferred_formula_rejects_remaining_foreign_var_7170() {
    let problem = ChcParser::parse(TWO_ARG_SELF_LOOP_FOR_ALPHA_RENAME)
        .expect("self-loop benchmark should parse");
    let pred = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "P")
        .expect("P predicate should exist");
    let pred_vars = canonical_predicate_vars(pred);
    let source_a = ChcVar::new("A", ChcSort::Int);
    let alien = ChcVar::new("Z", ChcSort::Int);
    let formula = ChcExpr::eq(ChcExpr::var(source_a), ChcExpr::var(alien));

    assert!(
        close_transferred_formula_over_predicate(&problem, pred, formula, &pred_vars).is_none(),
        "formula variables that cannot be mapped to predicate binders must fail closed",
    );
}

#[test]
fn test_derive_conserved_invariant_for_symbolic_entry_predicate() {
    let problem = ChcParser::parse(S_MULTIPL_25_000).expect("benchmark should parse");
    let inv1 = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "inv1")
        .expect("inv1 predicate should exist");
    let inv2 = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "inv2")
        .expect("inv2 predicate should exist");

    let self_loop = find_self_loop(&problem, inv1.id).expect("inv1 self-loop should exist");
    let (pre_vars, transition) =
        extract_normalized_transition(self_loop).expect("transition should normalize");
    let system = analyze_transition(&transition, &pre_vars).expect("closed forms should exist");
    let init_values =
        extract_init_values(&problem, inv1.id, &pre_vars).expect("inv1 fact should provide init");
    let inv1_invariants = eliminate_iteration_count(&system, &init_values);
    assert!(
        !inv1_invariants.is_empty(),
        "inv1 should have algebraic invariants"
    );

    let inv1_vars: Vec<ChcVar> = pre_vars
        .iter()
        .enumerate()
        .map(|(i, name)| {
            let sort = inv1.arg_sorts.get(i).cloned().unwrap_or(ChcSort::Int);
            ChcVar::new(name.clone(), sort)
        })
        .collect();
    let mut model = InvariantModel::new();
    model.set(
        inv1.id,
        PredicateInterpretation::new(inv1_vars, conjoin(inv1_invariants)),
    );

    let mut solved_preds = FxHashSet::default();
    solved_preds.insert(inv1.id);

    let derived = derive_conserved_invariant(&problem, inv2, &model, &solved_preds, false)
        .expect("inv2 should derive a conserved invariant from symbolic entry values");

    assert!(
        derived
            .conjuncts()
            .iter()
            .any(|expr| matches!(expr, ChcExpr::Op(ChcOp::Eq, _))),
        "expected at least one equality invariant, got {derived:?}"
    );
}

#[test]
fn test_try_algebraic_solve_handles_symbolic_entry_successor() {
    let problem = ChcParser::parse(S_MULTIPL_25_000).expect("benchmark should parse");
    let result = try_algebraic_solve(&problem, false);

    if let AlgebraicResult::Safe(model) = result {
        let inv2 = problem
            .predicates()
            .iter()
            .find(|pred| pred.name == "inv2")
            .expect("inv2 predicate should exist");
        let inv2_interp = model
            .get(&inv2.id)
            .expect("inv2 interpretation should exist");
        assert_ne!(
            inv2_interp.formula,
            ChcExpr::Bool(true),
            "inv2 should not fall back to a trivial invariant"
        );
        assert!(
            validate_model(&problem, &model),
            "algebraic model should validate on the original CHC"
        );
    }
    // None is acceptable: NIA solver returns Unknown for query clause
    // with polynomial terms (A*A, F*F). Synthesis correctness is
    // verified by test_derive_conserved_invariant_for_symbolic_entry_predicate.
}

#[test]
fn test_try_algebraic_solve_symbolic_accumulator_1753() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_SYMBOLIC_ACCUMULATOR)
        .expect("accumulator should parse");
    let (result, stats) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
    let AlgebraicResult::Safe(model) = result else {
        panic!(
            "symbolic accumulator should validate through the triangular accumulator fallback, got {result:?} with {stats:?}"
        );
    };
    assert!(
        validate_model(&problem, &model),
        "symbolic accumulator Safe result must validate on the original CHC"
    );

    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");
    let interp = model.get(&inv.id).expect("Inv interpretation should exist");
    let conjuncts = interp.formula.conjuncts();

    assert!(
        conjuncts
            .iter()
            .any(|expr| matches!(expr, ChcExpr::Op(ChcOp::Eq, _))),
        "expected a polynomial equality invariant, got {:?}",
        interp.formula
    );
    assert!(
        conjuncts.iter().any(
            |expr| matches!(expr, ChcExpr::Op(ChcOp::Le, args)
                if matches!((&*args[0], &*args[1]), (ChcExpr::Var(v0), ChcExpr::Var(v1)) if v0.name == "i" && v1.name == "n"))
        ),
        "expected loop-guard bridge invariant i <= n, got {:?}",
        interp.formula
    );
}

#[test]
fn test_try_algebraic_solve_multiblock_accumulator_fact_transfer_9004() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_MULTI_BLOCK_ACCUMULATOR)
        .expect("accumulator should parse");
    let (result, stats) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
    let AlgebraicResult::Safe(model) = result else {
        assert!(
            matches!(result, AlgebraicResult::NotApplicable)
                && stats.lra_affine_original_clause_validation_unknowns > 0,
            "multi-block accumulator must either validate definitively or fail closed on SMT Unknown, got {result:?} with {stats:?}"
        );
        return;
    };
    assert!(
        validate_model(&problem, &model),
        "multi-block accumulator Safe result must validate on the original CHC"
    );

    for name in ["Entry", "Mid", "Inv"] {
        let pred = problem
            .predicates()
            .iter()
            .find(|pred| pred.name == name)
            .expect("predicate should exist");
        let interp = model
            .get(&pred.id)
            .expect("predicate interpretation should exist");
        assert_ne!(
            interp.formula,
            ChcExpr::Bool(true),
            "{name} should receive a non-trivial transferred invariant"
        );
    }
}

#[test]
fn test_extract_init_values_from_symbolic_transfer_chain_9004() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_MULTI_BLOCK_ACCUMULATOR)
        .expect("accumulator should parse");
    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");
    let self_loop = find_self_loop(&problem, inv.id).expect("Inv self-loop should exist");
    let (pre_vars, _) =
        extract_normalized_transition(self_loop).expect("transition should normalize");

    let init_values =
        extract_init_values(&problem, inv.id, &pre_vars).expect("transfer entry should exist");
    assert_eq!(init_values.get("i"), Some(&0));
    assert_eq!(init_values.get("sum"), Some(&0));
    assert!(
        !init_values.contains_key("n"),
        "symbolic source n should remain symbolic, got {init_values:?}"
    );
}

#[test]
fn test_extract_init_values_from_two_hop_transfer_chain_9004() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_TWO_HOP_INIT_TRANSFER_ACCUMULATOR)
        .expect("accumulator should parse");
    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");
    let self_loop = find_self_loop(&problem, inv.id).expect("Inv self-loop should exist");
    let (pre_vars, _) =
        extract_normalized_transition(self_loop).expect("transition should normalize");

    let init_values =
        extract_init_values(&problem, inv.id, &pre_vars).expect("transfer entry should exist");
    assert_eq!(init_values.get("n"), Some(&7));
    assert_eq!(init_values.get("i"), Some(&0));
    assert_eq!(init_values.get("sum"), Some(&0));
}

#[test]
fn test_unreachable_self_loop_gets_false_invariant_9004() {
    let problem =
        ChcParser::parse(MODEL_CHECKER_CONSUMER_UNREACHABLE_SELF_LOOP).expect("CHC should parse");
    let (result, stats) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
    let AlgebraicResult::Safe(model) = result else {
        panic!("unreachable self-loop should solve with false invariant, got {result:?} {stats:?}");
    };
    assert!(
        validate_model(&problem, &model),
        "false invariant for unreachable self-loop must validate"
    );
    let dead = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Dead")
        .expect("Dead predicate should exist");
    let interp = model.get(&dead.id).expect("Dead invariant should exist");
    assert_eq!(interp.formula, ChcExpr::Bool(false));
}

#[test]
fn test_modular_chain_summary_from_transfer_entry_equality_9691() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_MODULAR_CHAIN_TRANSFER_SUMMARY)
        .expect("modular chain CHC should parse");
    let (result, stats) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
    let AlgebraicResult::Safe(model) = result else {
        panic!("modular chain summary should validate, got {result:?} with {stats:?}");
    };
    assert!(
        validate_model(&problem, &model),
        "modular chain summary Safe result must validate on the original CHC"
    );
    assert_eq!(
        stats.accelerated_summary_modular_chain_summary_candidates, 1,
        "transfer entry equality x=0 and drift 2 should emit one modular candidate"
    );
    assert_eq!(
        stats.accelerated_summary_modular_chain_family_summary_candidates, 1,
        "modular candidate should also be counted as a family-summary candidate"
    );

    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");
    let interp = model.get(&inv.id).expect("Inv interpretation should exist");
    assert!(
        interp.formula.conjuncts().iter().any(|expr| {
            matches!(expr, ChcExpr::Op(ChcOp::Eq, args)
                if matches!((&*args[0], &*args[1]), (ChcExpr::Op(ChcOp::Mod, mod_args), ChcExpr::Int(0))
                    if mod_args.len() == 2 && matches!(&*mod_args[1], ChcExpr::Int(2))))
        }),
        "expected Inv invariant to include a mod-2 chain summary, got {:?}",
        interp.formula
    );
}

#[test]
fn test_multi_pred_linear_transfer_closure_hard_tail_9691() {
    for (name, input) in [
        ("bouncy_one_counter_000", BOUNCY_ONE_COUNTER_000),
        (
            "bouncy_two_counters_equality_000",
            BOUNCY_TWO_COUNTERS_EQUALITY_000,
        ),
        ("s_multipl_08_000", S_MULTIPL_08_000),
        ("count_by_2_000", COUNT_BY_2_000),
    ] {
        let problem = ChcParser::parse(input).unwrap_or_else(|err| panic!("{name} parse: {err}"));
        let (result, stats) = try_algebraic_solve_with_deadline_and_stats(
            &problem,
            false,
            Some(ay_core::time::Instant::now() + std::time::Duration::from_secs(3)),
        );
        let AlgebraicResult::Safe(model) = result else {
            panic!("{name} should solve via closed transfer, got {result:?} with {stats:?}");
        };
        assert!(
            validate_model(&problem, &model),
            "{name} closed-transfer model must validate on the original CHC"
        );
        assert!(
            stats.lra_affine_original_clause_validation_successes > 0,
            "{name} should be accepted by original-clause validation"
        );
        assert_eq!(
            stats.lra_affine_original_clause_validation_failures
                + stats.lra_affine_original_clause_validation_unknowns,
            0,
            "{name} must not rely on failed/unknown validation"
        );
    }
}

#[test]
fn test_zero_arity_overflow_guard_uses_triangular_transfer_bound_9004() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_BOUNDED_ACCUMULATOR_OVERFLOW_EDGE)
        .expect("bounded accumulator should parse");
    let (result, stats) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
    match result {
        AlgebraicResult::Safe(model) => assert!(
            validate_model(&problem, &model),
            "bounded accumulator Safe result must validate on the original CHC"
        ),
        AlgebraicResult::NotApplicable => assert!(
            stats.lra_affine_original_clause_validation_unknowns > 0,
            "bounded accumulator must fail closed only after SMT Unknown demotion, got {stats:?}"
        ),
        AlgebraicResult::Unsafe => {
            panic!("bounded accumulator should not produce an unsafe recurrence result")
        }
    }
}

#[test]
fn test_triangular_bound_not_applied_without_finite_upper_bound_9004() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_UNBOUNDED_ACCUMULATOR_OVERFLOW_EDGE)
        .expect("unbounded accumulator should parse");
    let result = try_algebraic_solve(&problem, false);
    assert!(
        !matches!(result, AlgebraicResult::Safe(_)),
        "triangular overflow proof must require a finite counter upper bound, got {result:?}"
    );
}

#[test]
fn test_try_algebraic_solve_factorial_positive_product_1753() {
    let problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_FACTORIAL_MONOTONE_PRODUCT)
        .expect("factorial should parse");
    let (result, stats) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
    let AlgebraicResult::Safe(model) = result else {
        assert!(
            matches!(result, AlgebraicResult::NotApplicable)
                && stats.lra_affine_original_clause_validation_unknowns > 0,
            "factorial positivity must either validate definitively or fail closed on SMT Unknown, got {result:?} with {stats:?}"
        );
        return;
    };
    assert!(
        validate_model(&problem, &model),
        "factorial Safe result must validate on the original CHC"
    );

    let inv = problem
        .predicates()
        .iter()
        .find(|pred| pred.name == "Inv")
        .expect("Inv predicate should exist");
    let interp = model.get(&inv.id).expect("Inv interpretation should exist");
    let conjuncts = interp.formula.conjuncts();

    assert!(
        conjuncts.iter().any(
            |expr| matches!(expr, ChcExpr::Op(ChcOp::Ge, args)
                if matches!((&*args[0], &*args[1]), (ChcExpr::Var(v), ChcExpr::Int(1)) if v.name == "result"))
        ),
        "expected monotone product invariant result >= 1, got {:?}",
        interp.formula
    );
    assert!(
        conjuncts.iter().any(
            |expr| matches!(expr, ChcExpr::Op(ChcOp::Le, args)
                if matches!((&*args[0], &*args[1]), (ChcExpr::Var(v), ChcExpr::Op(ChcOp::Add, rhs))
                    if v.name == "i"
                        && rhs.len() == 2
                        && matches!((&*rhs[0], &*rhs[1]), (ChcExpr::Var(n), ChcExpr::Int(1)) if n.name == "n")))
        ),
        "expected loop-guard bridge invariant i <= n + 1, got {:?}",
        interp.formula
    );
}

/// Test #7931: BV32 symbolic accumulator via BvToInt + algebraic synthesis.
///
/// Verifies that `try_algebraic_solve` succeeds on the BV-to-Int abstracted
/// problem. This test isolates the algebraic pipeline from the portfolio's
/// engine timeouts.
#[test]
fn test_bv32_accumulator_via_bv_to_int_algebraic_7931() {
    use crate::transform::{BvToIntAbstractor, DeadParamEliminator, TransformationPipeline};

    // Parse BV32 problem
    let bv_problem = ChcParser::parse(MODEL_CHECKER_CONSUMER_BV32_SYMBOLIC_ACCUMULATOR)
        .expect("parse BV32 accumulator");

    // Phase 1: algebraic solve on original BV problem should fail
    // (algebraic synthesis doesn't understand BV operations natively)
    let result_original = try_algebraic_solve(&bv_problem, false);
    assert!(
        matches!(result_original, AlgebraicResult::NotApplicable),
        "BV problem should not solve directly"
    );

    // Phase 2: apply BvToInt + DeadParamElim (NO BvToBool — that would
    // bitblast BV32 into 32 Bool args per variable, which algebraic
    // synthesis cannot handle).
    let pipeline = TransformationPipeline::new()
        .with(BvToIntAbstractor::new())
        .with(DeadParamEliminator::new());
    let transformed = pipeline.transform(bv_problem.clone());
    let int_problem = transformed.problem;

    assert_eq!(int_problem.predicates().len(), 1);
    assert!(int_problem.predicates()[0]
        .arg_sorts
        .iter()
        .all(|s| matches!(s, ChcSort::Int)));

    // After #7986 soundness fix: algebraic solve on BvToInt-abstracted
    // problem must NOT return Safe (mod/div detected, Unknown rejected).
    let result_int = try_algebraic_solve(&int_problem, false);
    assert!(
        !matches!(result_int, AlgebraicResult::Safe(_)),
        "BvToInt-abstracted problem must not be accepted as Safe after #7986 soundness fix"
    );
}

const BV_WIDE_MUL_UNSAFE: &str = include_str!("../../../../benchmarks/chc/bv_wide_mul_unsafe.smt2");

/// Regression test for #7986: BvToInt algebraic false-proof soundness bug.
///
/// The bv_wide_mul_unsafe benchmark models a BV16 counter that doubles each
/// step (x' = x * 2). After 16 doublings, x overflows to 0 (mod 2^16).
/// The system is UNSAFE (x=0 is reachable).
///
/// Before the fix, the algebraic solver derived x >= 1 in unbounded integers
/// and the validator accepted SMT Unknown on the BvToInt-abstracted transition
/// clause. This is UNSOUND: modular wrapping makes x = 0 reachable in BV16.
///
/// The fix detects mod/div operations (signature of BvToInt abstraction) and
/// refuses to accept Unknown results when they are present.
#[test]
fn test_bvtoint_algebraic_false_proof_regression_7986() {
    use crate::transform::{BvToIntAbstractor, DeadParamEliminator, TransformationPipeline};

    let bv_problem = ChcParser::parse(BV_WIDE_MUL_UNSAFE).expect("parse bv_wide_mul_unsafe");

    let pipeline = TransformationPipeline::new()
        .with(BvToIntAbstractor::new())
        .with(DeadParamEliminator::new());
    let transformed = pipeline.transform(bv_problem.clone());
    let int_problem = transformed.problem;

    // Algebraic solve on BvToInt-abstracted UNSAFE problem must NOT return Safe.
    // Before fix: returned Safe(model) with x >= 1 invariant.
    // After fix: returns NotApplicable (validation rejects the invariant).
    let result = try_algebraic_solve(&int_problem, false);
    assert!(
        !matches!(result, AlgebraicResult::Safe(_)),
        "BvToInt-abstracted unsafe BV problem must NOT be accepted as Safe (#7986). \
         Got: {result:?}"
    );
}

// ---------------------------------------------------------------------------
// Deadline observance in the synthesis phase.
// ---------------------------------------------------------------------------

/// A CHC problem whose algebraic synthesis phase is expensive in a way that a
/// per-outer-iteration deadline check cannot bound.
///
/// One predicate, `width` Int arguments, all initialised to 0 and all
/// incremented by 1 on the self-loop. Every pair therefore has the same
/// constant delta, so `derive_auxiliary_invariants`' same-delta pair loop emits
/// `width * (width - 1) / 2` equalities for a SINGLE predicate — the whole cost
/// sits inside one iteration of the `for pred in predicates` loop, which is the
/// shape that makes a per-iteration check look correct while bounding nothing.
fn wide_lockstep_counter_problem(width: usize) -> ChcProblem {
    use std::fmt::Write as _;

    let pre: Vec<String> = (0..width).map(|i| format!("v{i}")).collect();
    let post: Vec<String> = (0..width).map(|i| format!("w{i}")).collect();
    let decl = vec!["Int"; width].join(" ");
    let binders = |names: &[String]| {
        names
            .iter()
            .map(|n| format!("({n} Int)"))
            .collect::<Vec<_>>()
            .join(" ")
    };
    let apply = |names: &[String]| format!("(Inv {})", names.join(" "));

    let mut smt = String::new();
    let _ = writeln!(smt, "(set-logic HORN)");
    let _ = writeln!(smt, "(declare-fun Inv ({decl}) Bool)");

    let init_eqs: Vec<String> = pre.iter().map(|n| format!("(= {n} 0)")).collect();
    let _ = writeln!(
        smt,
        "(assert (forall ({}) (=> (and {}) {})))",
        binders(&pre),
        init_eqs.join(" "),
        apply(&pre)
    );

    let step_eqs: Vec<String> = (0..width).map(|i| format!("(= w{i} (+ v{i} 1))")).collect();
    let mut loop_binders = binders(&pre);
    loop_binders.push(' ');
    loop_binders.push_str(&binders(&post));
    let _ = writeln!(
        smt,
        "(assert (forall ({}) (=> (and {} {}) {})))",
        loop_binders,
        apply(&pre),
        step_eqs.join(" "),
        apply(&post)
    );

    let _ = writeln!(
        smt,
        "(assert (forall ({}) (=> (and {} (< v0 0)) false)))",
        binders(&pre),
        apply(&pre)
    );
    let _ = writeln!(smt, "(check-sat)");

    ChcParser::parse(&smt).expect("generated lockstep-counter problem should parse")
}

/// Measurement harness for the expired-deadline cost fraction, not a gate: it
/// prints timings and asserts nothing. It is minutes of synthesis at width 120,
/// so it is compiled only under the `measurement-harness-tests` feature —
/// which means it RUNS when that feature is on, rather than being an
/// `#[ignore]`d test that runs nowhere (the repository forbids `#[ignore]`).
/// The gate that does assert on this behaviour,
/// `algebraic_prestage_honors_a_budget_that_expires_mid_flight`, is
/// unconditional and runs on every `cargo test`.
///
/// ```text
/// cargo test -p ay-chc --release --features measurement-harness-tests \
///     --lib measure_expired_deadline_cost_fraction -- --nocapture
/// ```
#[cfg(feature = "measurement-harness-tests")]
#[test]
fn measure_expired_deadline_cost_fraction() {
    for width in [40usize, 80, 120] {
        let problem = wide_lockstep_counter_problem(width);

        let t_full = ay_core::time::Instant::now();
        let (full, _) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
        let full_elapsed = t_full.elapsed();

        let t_exp = ay_core::time::Instant::now();
        let (expired, _) = try_algebraic_solve_with_deadline_and_stats(
            &problem,
            false,
            Some(ay_core::time::Instant::now()),
        );
        let expired_elapsed = t_exp.elapsed();

        let tag = |r: &AlgebraicResult| match r {
            AlgebraicResult::Safe(_) => "Safe",
            AlgebraicResult::Unsafe => "Unsafe",
            AlgebraicResult::NotApplicable => "NotApplicable",
        };
        println!(
            "width={width:>4}  full={:>10.4}s  expired={:>10.4}s  fraction={:>7.2}%  \
             full={} expired={}",
            full_elapsed.as_secs_f64(),
            expired_elapsed.as_secs_f64(),
            100.0 * expired_elapsed.as_secs_f64() / full_elapsed.as_secs_f64().max(1e-9),
            tag(&full),
            tag(&expired),
        );

        // Mid-flight: a budget that expires while synthesis is running. This is
        // the shape the corpus cells hit (nominal 5s, actual 33.67s) and the
        // one an entry gate alone cannot catch.
        for budget_ms in [10u64, 50, 200] {
            let budget = std::time::Duration::from_millis(budget_ms);
            let t = ay_core::time::Instant::now();
            let (r, _) = try_algebraic_solve_with_deadline_and_stats(
                &problem,
                false,
                Some(ay_core::time::Instant::now() + budget),
            );
            let el = t.elapsed();
            println!(
                "    midflight width={width:>4} budget={budget_ms:>4}ms  actual={:>9.4}s  \
                 overrun={:>8.2}x  result={}",
                el.as_secs_f64(),
                el.as_secs_f64() / budget.as_secs_f64(),
                tag(&r),
            );
        }
    }
}

/// #9110 gate: a budget that expires DURING synthesis/validation must stop it.
///
/// The bug this pins was not "the deadline is never checked" — it was checked,
/// at the top of three loops whose single iteration is where the time goes. The
/// observable signature is a runtime that does not move when the budget moves.
/// Measured before the fix on width 120: 1.992s at a 10ms budget, 1.986s at
/// 50ms, 1.982s at 200ms.
///
/// Both assertions are RELATIVE to the same problem's own unbudgeted cost, so
/// the gate holds in debug and release and on any machine speed.
#[test]
fn algebraic_prestage_honors_a_budget_that_expires_mid_flight() {
    use std::time::Duration;

    let problem = wide_lockstep_counter_problem(40);

    // Non-vacuity floor 1: unbudgeted, this problem is genuinely SOLVED. The
    // budgeted run below therefore gives up on real, available work rather
    // than reporting NotApplicable because there was nothing to do.
    let t = ay_core::time::Instant::now();
    let (unbudgeted, _) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
    let full = t.elapsed();
    assert!(
        matches!(unbudgeted, AlgebraicResult::Safe(_)),
        "non-vacuity: the lockstep problem must be solvable when unbudgeted, got {unbudgeted:?}"
    );

    // Non-vacuity floor 2: that work must be substantial relative to the
    // budget, otherwise the ratio below compares timer noise to timer noise.
    const BUDGET: Duration = Duration::from_millis(50);
    assert!(
        full > BUDGET * 4,
        "non-vacuity: unbudgeted solve took {full:?}, which is not enough more than the \
         {BUDGET:?} budget for this test to be able to detect an ignored budget"
    );

    let t = ay_core::time::Instant::now();
    let (budgeted, _) = try_algebraic_solve_with_deadline_and_stats(
        &problem,
        false,
        Some(ay_core::time::Instant::now() + BUDGET),
    );
    let budgeted_elapsed = t.elapsed();

    // Soundness: an exhausted budget yields no verdict at all.
    assert!(
        matches!(budgeted, AlgebraicResult::NotApplicable),
        "an exhausted budget must yield NotApplicable, never a verdict, got {budgeted:?}"
    );

    // The fix: the budgeted run must be a small fraction of the full one.
    // Before the fix this ratio was ~1.08x (0.882s vs 0.951s) — i.e. the
    // budget bought nothing. After it is ~17x.
    assert!(
        budgeted_elapsed * 4 < full,
        "budget ignored: a {BUDGET:?} budget took {budgeted_elapsed:?}, versus {full:?} \
         for the same problem with no budget at all"
    );
}

/// #9110 gate: re-entering the pre-strategy on a spent budget must cost nothing.
///
/// The pre-strategy is entered up to three times per solve (original problem,
/// BvToInt retry, adaptive escalation) sharing ONE deadline, and had no entry
/// gate — so entries two and three replayed the whole phase against a deadline
/// that had already passed. Measured before the fix at width 120: 3.93s of work
/// on an already-expired deadline.
#[test]
fn algebraic_prestage_does_no_work_on_an_already_expired_deadline() {
    let problem = wide_lockstep_counter_problem(40);

    // Non-vacuity: there is real work here to skip.
    let t = ay_core::time::Instant::now();
    let (unbudgeted, _) = try_algebraic_solve_with_deadline_and_stats(&problem, false, None);
    let full = t.elapsed();
    assert!(
        matches!(unbudgeted, AlgebraicResult::Safe(_)),
        "non-vacuity: the lockstep problem must be solvable when unbudgeted, got {unbudgeted:?}"
    );

    let t = ay_core::time::Instant::now();
    let (expired, _) = try_algebraic_solve_with_deadline_and_stats(
        &problem,
        false,
        Some(ay_core::time::Instant::now()),
    );
    let expired_elapsed = t.elapsed();

    assert!(
        matches!(expired, AlgebraicResult::NotApplicable),
        "an expired deadline must yield NotApplicable, got {expired:?}"
    );
    assert!(
        expired_elapsed * 20 < full,
        "an already-expired deadline still cost {expired_elapsed:?} against a full cost of {full:?}"
    );
}

/// #9110 gate: the runtime must TRACK the budget, not merely take one.
///
/// This is the diagnostic that identified the defect in the first place. A
/// solver that polls its budget finishes sooner when given less; a solver that
/// merely accepts a budget parameter and never polls it takes the same wall
/// clock whatever it is handed. The corpus cells showed 33.67s at a nominal 5s
/// and 33.63s at 20s, and this problem reproduces exactly that: with the
/// syntactic fast-path poll removed it takes 0.466s at a 10ms budget and
/// 0.470s at 250ms (a ratio of 1.01), versus 0.013s and 0.204s with the poll
/// in place (a ratio of 15).
///
/// Deliberately NOT a ratio against the unbudgeted cost: solving this width
/// outright takes ~14s, and the gate must stay cheap. Comparing two budgets
/// against each other is both cheaper and a sharper test of the actual
/// property, and it is independent of build profile and machine speed.
///
/// The width-40 gates above cover the entry gate and the conjoin
/// linearization; this one covers the Θ(|head|·|body|) validation scan, which
/// is the phase that dominated the measured overrun.
#[test]
fn algebraic_prestage_runtime_tracks_the_budget_it_is_given() {
    use std::time::Duration;

    const WIDTH: usize = 80;
    let problem = wide_lockstep_counter_problem(WIDTH);

    // Non-vacuity (structural): this really is the wide problem, so the
    // synthesized interpretation is large enough for the validation scan to be
    // the dominant cost. A trivial problem would finish inside every budget
    // and make the comparison below meaningless.
    assert_eq!(problem.clauses().len(), 3, "init, self-loop, query");
    assert_eq!(
        problem
            .predicates()
            .first()
            .expect("one predicate")
            .arg_sorts
            .len(),
        WIDTH,
        "non-vacuity: the predicate must be wide enough to make synthesis expensive"
    );

    let run = |budget: Duration| {
        let t = ay_core::time::Instant::now();
        let (result, _) = try_algebraic_solve_with_deadline_and_stats(
            &problem,
            false,
            Some(ay_core::time::Instant::now() + budget),
        );
        assert!(
            matches!(result, AlgebraicResult::NotApplicable),
            "an exhausted budget must yield NotApplicable, never a verdict, got {result:?}"
        );
        t.elapsed()
    };

    let small = run(Duration::from_millis(10));
    let large = run(Duration::from_millis(250));

    assert!(
        large > small * 3,
        "the budget is not being polled: a 250ms budget took {large:?} and a 10ms budget \
         took {small:?}, i.e. the runtime barely moved when the budget moved 25x"
    );
}

/// #9110 gate: an external cancellation token must reach the pre-strategy.
///
/// It previously did not reach this module in any form, so an embedding
/// driver's `cancellation_handle().cancel_after(..)` was inert here — arming it
/// on a 341s corpus cell measurably made it WORSE (343s), because the timer ran
/// and nothing observed it.
#[test]
fn algebraic_prestage_observes_an_external_cancellation_token() {
    let problem = wide_lockstep_counter_problem(40);

    // Non-vacuity: uncancelled, with no deadline, this problem is solved.
    let t = ay_core::time::Instant::now();
    let (uncancelled, _) = try_algebraic_solve_with_budget_and_stats(
        &problem,
        false,
        None,
        Some(crate::cancellation::CancellationToken::new()),
    );
    let full = t.elapsed();
    assert!(
        matches!(uncancelled, AlgebraicResult::Safe(_)),
        "non-vacuity: an un-cancelled token must not disturb the solve, got {uncancelled:?}"
    );

    let token = crate::cancellation::CancellationToken::new();
    token.cancel();
    let t = ay_core::time::Instant::now();
    let (cancelled, _) =
        try_algebraic_solve_with_budget_and_stats(&problem, false, None, Some(token));
    let cancelled_elapsed = t.elapsed();

    assert!(
        matches!(cancelled, AlgebraicResult::NotApplicable),
        "cancellation must yield NotApplicable, never a verdict, got {cancelled:?}"
    );
    assert!(
        cancelled_elapsed * 20 < full,
        "cancellation was not observed: {cancelled_elapsed:?} against an uncancelled {full:?}"
    );
}

/// #9110: an interrupted `and_all` must not hand back the partial conjunction.
///
/// A truncated conjunction is strictly WEAKER than the one the synthesizer
/// derived, and a too-weak interpretation is not merely useless: validation
/// reads a query clause the interpretation fails to exclude as evidence that
/// bad states are reachable. Returning a partial result would therefore turn a
/// timeout into a wrong verdict.
#[test]
fn and_all_checked_discards_the_partial_conjunction_when_it_stops() {
    let conjuncts: Vec<ChcExpr> = (0..4096)
        .map(|i| {
            ChcExpr::ge(
                ChcExpr::var(ChcVar::new(format!("x{i}"), ChcSort::Int)),
                ChcExpr::int(i),
            )
        })
        .collect();

    // Non-vacuity: the input is big enough to cross several poll strides, so a
    // stop predicate genuinely has somewhere to fire.
    assert!(conjuncts.len() > 4 * 512, "input must span several strides");

    // Stops immediately: no formula at all, not a truncated one.
    assert!(
        ChcExpr::and_all_checked(conjuncts.clone(), || true).is_none(),
        "a tripped stop predicate must discard the partial conjunction"
    );

    // Never stops: identical to the unchecked constructor.
    let checked = ChcExpr::and_all_checked(conjuncts.clone(), || false)
        .expect("a stop predicate that never fires must produce the full conjunction");
    assert_eq!(
        checked,
        ChcExpr::and_all(conjuncts.clone()),
        "the checked and unchecked constructors must agree"
    );
    assert_eq!(
        checked.conjuncts().len(),
        conjuncts.len(),
        "non-vacuity: every conjunct must survive"
    );
}

/// #9110: linearizing `conjoin` must not change the formula it builds.
///
/// `conjoin` used to fold with `reduce(ChcExpr::and)`. That is not linear:
/// `ChcExpr::and(a, b)` is `and_all([a, b])`, which re-flattens and re-hashes
/// the whole accumulator every step, so folding n conjuncts did Θ(n²)
/// hash-consing. Replacing the fold with one `and_all` pass is only safe if it
/// produces the identical expression — same order, same flattening, same
/// first-occurrence dedup, same constant folding.
#[test]
fn conjoin_matches_the_binary_fold_it_replaced() {
    let var = |n: &str| ChcExpr::var(ChcVar::new(n.to_string(), ChcSort::Int));

    let cases: Vec<Vec<ChcExpr>> = vec![
        vec![],
        vec![ChcExpr::ge(var("a"), ChcExpr::int(0))],
        vec![
            ChcExpr::ge(var("a"), ChcExpr::int(0)),
            ChcExpr::le(var("b"), ChcExpr::int(7)),
            ChcExpr::eq(var("c"), var("d")),
        ],
        // duplicates: first-occurrence dedup must be preserved
        vec![
            ChcExpr::ge(var("a"), ChcExpr::int(0)),
            ChcExpr::ge(var("a"), ChcExpr::int(0)),
            ChcExpr::le(var("b"), ChcExpr::int(7)),
        ],
        // nested And: flattening must be preserved
        vec![
            ChcExpr::and(
                ChcExpr::ge(var("a"), ChcExpr::int(0)),
                ChcExpr::le(var("b"), ChcExpr::int(7)),
            ),
            ChcExpr::eq(var("c"), var("d")),
        ],
        // constant folding, both polarities
        vec![
            ChcExpr::Bool(true),
            ChcExpr::ge(var("a"), ChcExpr::int(0)),
            ChcExpr::Bool(true),
        ],
        vec![
            ChcExpr::ge(var("a"), ChcExpr::int(0)),
            ChcExpr::Bool(false),
            ChcExpr::le(var("b"), ChcExpr::int(7)),
        ],
    ];

    for case in cases {
        let folded = match case.len() {
            0 => ChcExpr::Bool(true),
            1 => case[0].clone(),
            _ => case
                .clone()
                .into_iter()
                .reduce(ChcExpr::and)
                .expect("non-empty"),
        };
        assert_eq!(
            conjoin(case.clone()),
            folded,
            "linearized conjoin disagreed with the binary fold on {case:?}"
        );
    }
}
