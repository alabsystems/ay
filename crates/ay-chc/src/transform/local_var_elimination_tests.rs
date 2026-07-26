// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::ChcSort;

#[test]
fn get_linear_coefficient_sub_overflow_returns_none() {
    let x = ChcVar::new("x", ChcSort::Int);
    let lhs = ChcExpr::mul(ChcExpr::Int(i128::MAX), ChcExpr::var(x.clone()));
    let rhs = ChcExpr::neg(ChcExpr::var(x.clone()));
    let expr = ChcExpr::sub(lhs, rhs);
    assert_eq!(get_linear_coefficient(&expr, &x), None);
}

#[test]
fn get_linear_coefficient_neg_overflow_returns_none() {
    let x = ChcVar::new("x", ChcSort::Int);
    let inner = ChcExpr::mul(ChcExpr::Int(i128::MIN), ChcExpr::var(x.clone()));
    let expr = ChcExpr::neg(inner);
    assert_eq!(get_linear_coefficient(&expr, &x), None);
}

#[test]
fn eliminates_nonempty_huge_abi_style_interval() {
    use num_bigint::BigInt;

    let x = ChcVar::new("x", ChcSort::Int);
    let uint256_max: BigInt = (BigInt::from(1_u8) << 256) - 1_u8;
    let constraint = ChcExpr::and_all([
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::from_bigint(uint256_max)),
    ]);

    assert_eq!(
        LocalVarEliminator::new().try_eliminate_var(&constraint, &x),
        Some(ChcExpr::Bool(true))
    );
}

#[test]
fn eliminates_nonempty_strict_integer_interval() {
    let x = ChcVar::new("x", ChcSort::Int);
    let constraint = ChcExpr::and_all([
        ChcExpr::lt(ChcExpr::int(10), ChcExpr::var(x.clone())),
        ChcExpr::gt(ChcExpr::int(12), ChcExpr::var(x.clone())),
    ]);

    assert_eq!(
        LocalVarEliminator::new().try_eliminate_var(&constraint, &x),
        Some(ChcExpr::Bool(true))
    );
}

#[test]
fn contradictory_strict_integer_interval_becomes_false() {
    let x = ChcVar::new("x", ChcSort::Int);
    let constraint = ChcExpr::and_all([
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(11)),
    ]);

    assert_eq!(
        LocalVarEliminator::new().try_eliminate_var(&constraint, &x),
        Some(ChcExpr::Bool(false))
    );
}

#[test]
fn non_bound_occurrence_prevents_constant_interval_elimination() {
    let x = ChcVar::new("x", ChcSort::Int);
    let constraint = ChcExpr::and_all([
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        ChcExpr::eq(
            ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ChcExpr::int(7),
        ),
    ]);

    assert_eq!(
        LocalVarEliminator::new().try_eliminate_var(&constraint, &x),
        None
    );
}

// Moved from tests/chc_regression_1615.rs — uses LocalVarEliminator (no longer pub)

fn parse_problem(smt: &str) -> ChcProblem {
    use crate::parser::ChcParser;
    let problem =
        ChcParser::parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT2:\n{smt}"));
    problem
        .validate()
        .unwrap_or_else(|err| panic!("CHC validation failed: {err}\nSMT2:\n{smt}"));
    problem
}

const DTUC_000: &str = r#"(set-logic HORN)
(declare-fun |FUN| ( Int Int Int Int ) Bool)
(declare-fun |SAD| ( Int Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (and (= A 0) (= C 0))) (FUN A B C D))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) (=> (and (FUN A D B F) (and (= C (+ 1 A)) (not (<= F A)) (= E (+ 1 B)))) (FUN C D E F))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) (=> (and (FUN B A D E) (and (= B E) (= C E))) (SAD B C D E))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) ) (=> (and (SAD C B A F) (and (= D (+ (- 1) B)) (not (<= B 0)) (= E (+ (- 1) A)))) (SAD C D E F))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (SAD A C D B) (and (not (<= C 0)) (<= D 0))) false)))
(check-sat)
"#;

const S_MUTANTS_16_M_000: &str = r#"(set-logic HORN)
(declare-fun |itp| ( Int Int Int ) Bool)
(declare-fun |itp1| ( Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) ) (=> (and (and (= A 0) (not (<= 5 C)) (not (<= C 0)) (= B (* 3 C)))) (itp A B C))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) (=> (and (itp A B E) (and (= C (+ 1 A)) (not (<= 100 A)) (= D (+ 1 B)))) (itp C D E))))
(assert (forall ( (A Int) (B Int) (C Int) ) (=> (and (itp A B C) (<= 100 A)) (itp1 A B C))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) ) (=> (and (itp1 A B E) (and (= C (+ 1 A)) (not (<= 120 A)) (= D (+ 1 B)))) (itp1 C D E))))
(assert (forall ( (A Int) (B Int) (C Int) ) (=> (and (itp1 B C A) (and (or (not (<= C 132)) (not (>= C 3))) (<= 120 B))) false)))
(check-sat)
"#;

const THREE_DOTS_MOVING_2_000: &str = r#"(set-logic HORN)
(declare-fun |inv| ( Int Int Int Int ) Bool)
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (and (>= D (+ B (* (- 1) C))) (>= D (+ B (* (- 1) A))) (not (<= B A)) (>= D (+ C (* (- 2) A) B)))) (inv A B C D))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) (E Int) (F Int) (G Int) ) (=> (and (inv B C F A) (let ((a!1 (and (= D (ite (<= B F) (+ 1 B) (+ (- 1) B))) (= E D) (= B C)))) (let ((a!2 (or (and (= D B) (= E (+ (- 1) C)) (not (= B C))) a!1))) (and (= G (+ (- 1) A)) a!2 (not (= C F)))))) (inv D E F G))))
(assert (forall ( (A Int) (B Int) (C Int) (D Int) ) (=> (and (inv A B C D) (and (<= D 0) (not (= B C)))) false)))
(check-sat)
"#;

#[test]
fn test_local_var_elimination_dtuc() {
    let problem = parse_problem(DTUC_000);
    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);
    result.validate().unwrap();
    assert!(result.clauses().len() <= problem.clauses().len());
    assert_eq!(problem.predicates().len(), result.predicates().len());
}

#[test]
fn test_local_var_elimination_s_mutants() {
    let problem = parse_problem(S_MUTANTS_16_M_000);
    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);
    result.validate().unwrap();
    assert!(result.clauses().len() <= problem.clauses().len());
    assert_eq!(problem.predicates().len(), result.predicates().len());
}

#[test]
fn test_local_var_elimination_three_dots() {
    let problem = parse_problem(THREE_DOTS_MOVING_2_000);
    let eliminator = LocalVarEliminator::new();
    let result = eliminator.eliminate(&problem);
    result.validate().unwrap();
    assert!(result.clauses().len() <= problem.clauses().len());
    assert_eq!(problem.predicates().len(), result.predicates().len());
}

#[test]
fn ground_backtranslation_tracks_indices_after_dropping_false_clause() {
    use crate::ground_derivation::{
        validate_ground_derivation, GroundDerivation, GroundDerivationStep,
    };
    use crate::transform::Transformer;
    use crate::ClauseHead;
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    let mut input = ChcProblem::new();
    let p = input.declare_predicate("P", vec![]);
    let local = ChcVar::new("local", ChcSort::Int);
    input.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(local.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(local), ChcExpr::int(1)),
        )),
        ClauseHead::Predicate(p, vec![]),
    ));
    input.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![]),
    ));
    input.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![],
    )])));
    assert_eq!(
        input.clauses().len(),
        3,
        "the contradictory local clause must survive construction"
    );
    assert_eq!(input.clauses()[0].head.predicate_id(), Some(p));
    assert_eq!(input.clauses()[1].head.predicate_id(), Some(p));
    assert!(input.clauses()[2].is_query());

    let transformed = Box::new(LocalVarEliminator::new()).transform(input.clone());
    assert_eq!(transformed.problem.clauses().len(), 2);
    assert_eq!(
        transformed.problem.clauses()[0].head.predicate_id(),
        Some(p)
    );
    assert!(transformed.problem.clauses()[1].is_query());
    let output_proof = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: FxHashMap::default(),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: FxHashMap::default(),
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    validate_ground_derivation(&transformed.problem, &output_proof)
        .expect("setup: transformed proof must validate");

    let translated = transformed
        .back_translator
        .translate_ground_derivation(&output_proof)
        .expect("surviving clauses must map across the dropped false prefix");
    validate_ground_derivation(&input, &translated)
        .expect("translated proof must validate on the input clauses");
    assert_eq!(translated.steps[0].clause_index, 1);
    assert_eq!(translated.steps[1].clause_index, 2);
}

#[test]
fn ground_backtranslation_recovers_projected_one_sided_integer_bound() {
    use crate::ground_derivation::{
        validate_ground_derivation, GroundDerivation, GroundDerivationStep,
    };
    use crate::transform::Transformer;
    use crate::ClauseHead;
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    // The local is absent from every predicate argument, so LVE projects its
    // satisfiable one-sided bound and turns this into an unconditional fact.
    // Ground replay must reconstruct a value satisfying the richer input
    // clause instead of assigning Int's zero default.
    let mut input = ChcProblem::new();
    let p = input.declare_predicate("P", vec![]);
    let local = ChcVar::new("P1__inline_1168__inline_1226", ChcSort::Int);
    input.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::ge(ChcExpr::var(local.clone()), ChcExpr::int(4))),
        ClauseHead::Predicate(p, vec![]),
    ));
    input.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![],
    )])));

    let transformed = Box::new(LocalVarEliminator::new()).transform(input.clone());
    assert_eq!(transformed.problem.clauses().len(), 2);
    assert!(
        transformed.problem.clauses()[0].body.constraint.is_none(),
        "LVE should project the satisfiable one-sided local bound"
    );
    let output_proof = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: FxHashMap::default(),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: FxHashMap::default(),
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    validate_ground_derivation(&transformed.problem, &output_proof)
        .expect("setup: projected proof must validate");

    let translated = transformed
        .back_translator
        .translate_ground_derivation(&output_proof)
        .expect("the projected lower-bound local must be reconstructible");
    validate_ground_derivation(&input, &translated)
        .expect("translated proof must validate on the input clauses");
    assert!(
        matches!(
            translated.steps[0].env.get(&local.name),
            Some(crate::smt::SmtValue::Int(value)) if *value >= 4
        ),
        "replayed local must satisfy its original lower bound, got {:?}",
        translated.steps[0].env.get(&local.name)
    );
}

#[test]
fn ground_backtranslation_recovers_projected_affine_array_bound_without_smt() {
    use crate::ground_derivation::{
        validate_ground_derivation, GroundDerivation, GroundDerivationStep,
    };
    use crate::smt::SmtValue;
    use crate::transform::Transformer;
    use crate::ClauseHead;
    use ay_core::kani_compat::DetHashMap as FxHashMap;

    let array_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let mut input = ChcProblem::new();
    let p = input.declare_predicate("P", vec![array_sort.clone()]);
    let table = ChcVar::new("table", array_sort);
    let local = ChcVar::new("local", ChcSort::Int);
    input.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(p, vec![ChcExpr::const_array(ChcSort::Int, ChcExpr::int(3))]),
    ));
    input.add_clause(HornClause::query(ClauseBody::new(
        vec![(p, vec![ChcExpr::var(table.clone())])],
        Some(ChcExpr::le(
            ChcExpr::int(0),
            ChcExpr::add(
                ChcExpr::select(ChcExpr::var(table.clone()), ChcExpr::int(0)),
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(local.clone())),
            ),
        )),
    )));

    let transformed = Box::new(LocalVarEliminator::new()).transform(input.clone());
    assert!(
        transformed.problem.clauses()[1]
            .body
            .constraint
            .as_ref()
            .is_none_or(|constraint| constraint == &ChcExpr::Bool(true)),
        "LVE should project the satisfiable affine local bound"
    );
    let table_value = SmtValue::ConstArray(Box::new(SmtValue::Int(3)));
    let output_proof = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: FxHashMap::default(),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: FxHashMap::from_iter([(table.name.clone(), table_value)]),
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    validate_ground_derivation(&transformed.problem, &output_proof)
        .expect("setup: transformed affine proof must validate");

    let translated = transformed
        .back_translator
        .translate_ground_derivation(&output_proof)
        .expect("the projected affine local must be reconstructed");
    validate_ground_derivation(&input, &translated)
        .expect("translated affine proof must validate on the input clauses");
    assert_eq!(
        translated.steps[1].env.get(&local.name),
        Some(&SmtValue::Int(-1)),
        "completion should choose ceil(-3/2) directly"
    );
}

#[test]
fn ground_backtranslation_recovers_eleven_bounded_integer_alias_pairs() {
    use crate::ground_derivation::{
        validate_ground_derivation, GroundDerivation, GroundDerivationStep,
    };
    use crate::smt::SmtValue;
    use crate::transform::Transformer;
    use ay_core::kani_compat::DetHashMap as FxHashMap;
    use num_bigint::BigInt;

    // Solidity's decode/slice query clauses contain eleven disjoint pairs of
    // this exact form. LVE projects both names, but replay must treat `x = y`
    // as one bounded integer rather than asking the mixed array/LIA solver to
    // rediscover all 22 values at once.
    let mut conjuncts = Vec::new();
    let mut pairs = Vec::new();
    let uint256_max: BigInt = (BigInt::from(1_u8) << 256) - 1_u8;
    for index in 0..11_i128 {
        let x = ChcVar::new(format!("bounded_{index}"), ChcSort::Int);
        let y = ChcVar::new(format!("alias_{index}"), ChcSort::Int);
        let lower = if index == 10 { 4 } else { 0 };
        conjuncts.push(ChcExpr::eq(
            ChcExpr::var(x.clone()),
            ChcExpr::var(y.clone()),
        ));
        conjuncts.push(ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(lower)));
        if index != 10 {
            conjuncts.push(ChcExpr::le(
                ChcExpr::var(x.clone()),
                ChcExpr::from_bigint(uint256_max.clone()),
            ));
        }
        pairs.push((x, y, lower));
    }

    let mut input = ChcProblem::new();
    input.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::and_all(
        conjuncts,
    ))));
    let transformed = Box::new(LocalVarEliminator::new()).transform(input.clone());
    assert_eq!(transformed.problem.clauses().len(), 1);
    assert!(
        transformed.problem.clauses()[0].body.constraint.is_none(),
        "all eleven satisfiable local alias pairs should be projected"
    );

    let output_proof = GroundDerivation {
        steps: vec![GroundDerivationStep {
            clause_index: 0,
            env: FxHashMap::default(),
            premises: vec![],
        }],
        query_step: 0,
    };
    validate_ground_derivation(&transformed.problem, &output_proof)
        .expect("setup: projected alias-pair proof must validate");
    let translated = transformed
        .back_translator
        .translate_ground_derivation(&output_proof)
        .expect("all bounded alias classes must reconstruct deterministically");
    validate_ground_derivation(&input, &translated)
        .expect("translated alias-pair proof must validate on the input clause");

    for (x, y, lower) in pairs {
        assert_eq!(
            translated.steps[0].env.get(&x.name),
            Some(&SmtValue::Int(lower))
        );
        assert_eq!(
            translated.steps[0].env.get(&y.name),
            Some(&SmtValue::Int(lower))
        );
    }
}
