// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::pdr::config::PdrConfig;
use crate::pdr::frame::Lemma;
use crate::ChcParser;
use crate::{ChcProblem, ClauseBody, ClauseHead, HornClause};

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

#[test]
fn array_scalarized_model_translates_select_argument_back_to_original_signature() {
    let bv64 = ChcSort::BitVec(64);
    let bv8 = ChcSort::BitVec(8);
    let arr_sort = ChcSort::Array(Box::new(bv64.clone()), Box::new(bv8.clone()));
    let mut problem = ChcProblem::new();
    let pred = problem.declare_predicate("inv", vec![arr_sort.clone(), bv64.clone()]);

    let m = ChcVar::new("m", arr_sort);
    let cnt = ChcVar::new("cnt", bv64);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                pred,
                vec![ChcExpr::var(m.clone()), ChcExpr::var(cnt.clone())],
            )],
            Some(ChcExpr::eq(
                ChcExpr::select(ChcExpr::var(m), ChcExpr::BitVec(0, 64)),
                ChcExpr::BitVec(255, 8),
            )),
        ),
        ClauseHead::False,
    ));

    let solver = PdrSolver::new(problem, PdrConfig::default());
    let sel_var = ChcVar::new("m__sel_bv0_64", bv8.clone());
    let cnt_var = ChcVar::new("__p0_a1", ChcSort::BitVec(64));
    let mut model = InvariantModel::new();
    model.set(
        pred,
        PredicateInterpretation::new(
            vec![sel_var.clone(), cnt_var],
            ChcExpr::eq(ChcExpr::var(sel_var), ChcExpr::BitVec(255, 8)),
        ),
    );

    let translated = solver
        .try_translate_array_scalarized_model(model)
        .expect("model should backtranslate");
    let interp = translated.get(&pred).expect("translated predicate model");
    assert_eq!(interp.vars.len(), 2);
    assert!(matches!(interp.vars[0].sort, ChcSort::Array(_, _)));
    assert_eq!(
        interp.formula,
        ChcExpr::eq(
            ChcExpr::select(
                ChcExpr::var(ChcVar::new(
                    "__p0_a0",
                    ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)))
                )),
                ChcExpr::BitVec(0, 64)
            ),
            ChcExpr::BitVec(255, 8)
        )
    );
    assert!(
        !interp
            .formula
            .vars()
            .iter()
            .any(|var| var.name.contains("__sel_")),
        "translated model must not retain scalarized select vars: {}",
        interp.formula
    );
}

// ── filter_non_canonical_conjuncts ──────────────────────────────────

#[test]
fn filter_non_canonical_removes_witness_conjunct() {
    let a0 = int_var("a0");
    let witness = int_var("_parity_w_a0_2");

    // a0 >= 0 AND a0 = 2 * _parity_w_a0_2 + 1
    let canonical_conj = ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(0));
    let witness_conj = ChcExpr::eq(
        ChcExpr::var(a0.clone()),
        ChcExpr::add(
            ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(witness)),
            ChcExpr::Int(1),
        ),
    );
    let formula = ChcExpr::and(canonical_conj.clone(), witness_conj);

    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0]);

    // Should keep only the canonical conjunct
    let conjuncts = result.collect_conjuncts();
    assert_eq!(conjuncts.len(), 1);
    assert_eq!(conjuncts[0], canonical_conj);
}

#[test]
fn filter_non_canonical_keeps_all_canonical() {
    let a0 = int_var("a0");
    let a1 = int_var("a1");

    let c1 = ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(0));
    let c2 = ChcExpr::le(ChcExpr::var(a1.clone()), ChcExpr::int(10));
    let formula = ChcExpr::and(c1, c2);

    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0, a1]);
    let conjuncts = result.collect_conjuncts();
    assert_eq!(conjuncts.len(), 2);
}

#[test]
fn filter_non_canonical_all_non_canonical_returns_true() {
    let w1 = int_var("_parity_w_a0_2");
    let w2 = int_var("_parity_w_a1_3");
    let a0 = int_var("a0");

    let c1 = ChcExpr::ge(ChcExpr::var(w1), ChcExpr::int(0));
    let c2 = ChcExpr::le(ChcExpr::var(w2), ChcExpr::int(5));
    let formula = ChcExpr::and(c1, c2);

    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0]);
    assert!(matches!(result, ChcExpr::Bool(true)));
}

#[test]
fn filter_non_canonical_true_unchanged() {
    let a0 = int_var("a0");
    let formula = ChcExpr::Bool(true);
    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0]);
    assert!(matches!(result, ChcExpr::Bool(true)));
}

/// Single conjunct with non-canonical var should be filtered to true.
#[test]
fn filter_non_canonical_single_conjunct_with_witness_filtered() {
    let witness = int_var("_parity_w_a0_2");
    let a0 = int_var("a0");

    // Single conjunct referencing non-canonical variable
    let formula = ChcExpr::eq(
        ChcExpr::var(a0.clone()),
        ChcExpr::mul(ChcExpr::Int(2), ChcExpr::var(witness)),
    );

    let result = PdrSolver::filter_non_canonical_conjuncts(&formula, &[a0]);

    // Must filter to true since the only conjunct has non-canonical vars
    assert!(
        matches!(result, ChcExpr::Bool(true)),
        "Single non-canonical conjunct should be filtered: {result}"
    );
}

// ── query relevance ─────────────────────────────────────────────────

#[test]
fn query_relevant_predicates_are_backward_slice_from_false_heads() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun r (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (p x) (q x))))
(assert (forall ((x Int)) (=> (and (r x) (> x 10)) false)))
(check-sat)
"#;

    let solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let p = solver.problem.lookup_predicate("p").unwrap();
    let q = solver.problem.lookup_predicate("q").unwrap();
    let r = solver.problem.lookup_predicate("r").unwrap();

    let relevant = solver.query_relevant_predicates();
    assert!(
        relevant.contains(&r),
        "query predecessor should be relevant"
    );
    assert!(
        !relevant.contains(&p) && !relevant.contains(&q),
        "unrelated p -> q component should not be query-relevant: {relevant:?}"
    );
}

#[test]
fn frame_model_interprets_query_irrelevant_predicates_as_true() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)
(declare-fun r (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (= x 0) (r x))))
(assert (forall ((x Int)) (=> (p x) (q x))))
(assert (forall ((x Int)) (=> (and (r x) (> x 10)) false)))
(check-sat)
"#;

    let mut solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let q = solver.problem.lookup_predicate("q").unwrap();
    let q_var = solver.canonical_vars(q).unwrap()[0].clone();
    let q_lemma = ChcExpr::ge(ChcExpr::var(q_var), ChcExpr::int(0));
    solver.frames[1].add_lemma(Lemma::new(q, q_lemma, 1));

    let r = solver.problem.lookup_predicate("r").unwrap();
    let r_var = solver.canonical_vars(r).unwrap()[0].clone();
    let r_lemma = ChcExpr::le(ChcExpr::var(r_var), ChcExpr::int(10));
    solver.frames[1].add_lemma(Lemma::new(r, r_lemma.clone(), 1));

    let model = solver.build_model_from_frame(1);
    let q_formula = &model.get(&q).expect("q interpretation").formula;
    assert!(
        matches!(q_formula, ChcExpr::Bool(true)),
        "query-irrelevant q should be true, got {q_formula}"
    );

    let r_formula = &model.get(&r).expect("r interpretation").formula;
    assert_eq!(
        r_formula, &r_lemma,
        "query-relevant r should retain its frame lemma"
    );
}

#[test]
fn frame_model_interprets_unreachable_query_predicate_as_false() {
    let smt2 = r#"
(set-logic HORN)
(declare-rel error ())
(query error)
"#;

    let solver = PdrSolver::new(ChcParser::parse(smt2).unwrap(), PdrConfig::default());
    let error = solver.problem.lookup_predicate("error").unwrap();

    let model = solver.build_model_from_frame(1);
    let error_formula = &model.get(&error).expect("error interpretation").formula;
    assert!(
        matches!(error_formula, ChcExpr::Bool(false)),
        "unreachable query predicate should be false, got {error_formula}"
    );
}

// ── propagate_tight_bound_constants ─────────────────────────────────

#[test]
fn tight_bounds_produces_equality() {
    let a0 = int_var("a0");

    // a0 >= 5 AND a0 <= 5
    let formula = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(5)),
        ChcExpr::le(ChcExpr::var(a0), ChcExpr::int(5)),
    );

    let result = PdrSolver::propagate_tight_bound_constants(&formula);

    // Should contain a0 = 5
    let conjuncts = result.collect_conjuncts();
    let has_equality = conjuncts.iter().any(|c| {
        matches!(c, ChcExpr::Op(ChcOp::Eq, args)
            if args.len() == 2
            && matches!(args[0].as_ref(), ChcExpr::Var(v) if v.name == "a0")
            && matches!(args[1].as_ref(), ChcExpr::Int(5)))
    });
    assert!(has_equality, "Expected a0 = 5 in result: {result}");
}

#[test]
fn tight_bounds_all_constants_not_true() {
    let a0 = int_var("a0");
    let a1 = int_var("a1");

    // a0 >= 0 AND a0 <= 0 AND a1 >= 0 AND a1 <= 0
    let formula = ChcExpr::and_all(vec![
        ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(a0), ChcExpr::int(0)),
        ChcExpr::ge(ChcExpr::var(a1.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(a1), ChcExpr::int(0)),
    ]);

    let result = PdrSolver::propagate_tight_bound_constants(&formula);

    // Must NOT simplify to true — must preserve equalities
    assert!(
        !matches!(result, ChcExpr::Bool(true)),
        "tight bounds lost information: {result}"
    );

    // Should contain a0 = 0 AND a1 = 0
    let vars_in_result = result.vars();
    assert!(
        vars_in_result.iter().any(|v| v.name == "a0"),
        "a0 missing from result: {result}"
    );
    assert!(
        vars_in_result.iter().any(|v| v.name == "a1"),
        "a1 missing from result: {result}"
    );
}

#[test]
fn tight_bounds_preserves_remainder() {
    let a0 = int_var("a0");
    let a1 = int_var("a1");

    // a0 >= 3 AND a0 <= 3 AND a1 >= 0
    let formula = ChcExpr::and_all(vec![
        ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(3)),
        ChcExpr::le(ChcExpr::var(a0), ChcExpr::int(3)),
        ChcExpr::ge(ChcExpr::var(a1), ChcExpr::int(0)),
    ]);

    let result = PdrSolver::propagate_tight_bound_constants(&formula);

    // Should contain both a0 = 3 AND a1 >= 0 (or a1 >= 0 with a0 substituted)
    assert!(
        !matches!(result, ChcExpr::Bool(true)),
        "Should not be trivially true: {result}"
    );
    let conjuncts = result.collect_conjuncts();
    assert!(
        conjuncts.len() >= 2,
        "Expected at least 2 conjuncts (equality + remainder), got {}: {result}",
        conjuncts.len()
    );
}

#[test]
fn tight_bounds_no_bounds_unchanged() {
    let a0 = int_var("a0");

    // a0 >= 0 (no tight bounds)
    let formula = ChcExpr::ge(ChcExpr::var(a0), ChcExpr::int(0));
    let result = PdrSolver::propagate_tight_bound_constants(&formula);
    assert_eq!(result, formula);
}

#[test]
fn tight_bounds_non_matching_bounds_unchanged() {
    let a0 = int_var("a0");

    // a0 >= 0 AND a0 <= 10 (not tight)
    let formula = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a0.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(a0), ChcExpr::int(10)),
    );
    let original = formula.clone();
    let result = PdrSolver::propagate_tight_bound_constants(&formula);
    assert_eq!(result, original);
}
