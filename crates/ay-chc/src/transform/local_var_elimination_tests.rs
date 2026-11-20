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

    assert_eq!(eliminate_single(&constraint, &x), Some(ChcExpr::Bool(true)));
}

#[test]
fn eliminates_nonempty_strict_integer_interval() {
    let x = ChcVar::new("x", ChcSort::Int);
    let constraint = ChcExpr::and_all([
        ChcExpr::lt(ChcExpr::int(10), ChcExpr::var(x.clone())),
        ChcExpr::gt(ChcExpr::int(12), ChcExpr::var(x.clone())),
    ]);

    assert_eq!(eliminate_single(&constraint, &x), Some(ChcExpr::Bool(true)));
}

#[test]
fn contradictory_strict_integer_interval_becomes_false() {
    let x = ChcVar::new("x", ChcSort::Int);
    let constraint = ChcExpr::and_all([
        ChcExpr::gt(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        ChcExpr::lt(ChcExpr::var(x.clone()), ChcExpr::int(11)),
    ]);

    assert_eq!(
        eliminate_single(&constraint, &x),
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

    assert_eq!(eliminate_single(&constraint, &x), None);
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

// ---------------------------------------------------------------------------
// Reference: the per-variable algorithm before the occurrence index. Every
// step re-flattens the whole constraint, recomputes every conjunct's variable
// set and rebuilds the conjunction with `and_all`. Kept verbatim as the
// differential oracle for `eliminate_locals`.
// ---------------------------------------------------------------------------

fn reference_eliminate_in_clause(clause: &HornClause) -> (HornClause, usize) {
    let constraint = match &clause.body.constraint {
        Some(c) => c,
        None => return (clause.clone(), 0),
    };

    let shared_vars = collect_shared_vars(clause);
    let constraint_vars: FxHashSet<_> = constraint.vars().into_iter().collect();
    let local_vars: Vec<_> = constraint_vars
        .iter()
        .filter(|v| !shared_vars.contains(*v))
        .cloned()
        .collect();
    if local_vars.is_empty() {
        return (clause.clone(), 0);
    }

    let mut current_constraint = constraint.clone();
    let mut eliminated = 0;
    for var in &local_vars {
        if let Some(simplified) = reference_try_eliminate_var(&current_constraint, var) {
            current_constraint = simplified;
            eliminated += 1;
        }
    }
    if eliminated == 0 {
        return (clause.clone(), 0);
    }

    let final_constraint = current_constraint.simplify_array_ops().simplify_constants();
    let new_body = ClauseBody::new(
        clause.body.predicates.clone(),
        Some(final_constraint).filter(|c| !matches!(c, ChcExpr::Bool(true))),
    );
    (HornClause::new(new_body, clause.head.clone()), eliminated)
}

fn reference_try_eliminate_var(constraint: &ChcExpr, var: &ChcVar) -> Option<ChcExpr> {
    if let Some(result) = reference_try_equality_substitution(constraint, var) {
        return Some(result);
    }
    if let Some(result) = reference_try_constant_interval_elimination(constraint, var) {
        return Some(result);
    }
    reference_try_one_sided_bound_elimination(constraint, var)
}

fn reference_conjuncts(constraint: &ChcExpr) -> Vec<ChcExpr> {
    let mut c = constraint.collect_conjuncts();
    c.retain(|x| !matches!(x, ChcExpr::Bool(true)));
    c
}

fn reference_conjunct_mentions_var(conj: &ChcExpr, var: &ChcVar) -> bool {
    conj.vars().contains(var)
}

fn reference_try_equality_substitution(constraint: &ChcExpr, var: &ChcVar) -> Option<ChcExpr> {
    let conjuncts = reference_conjuncts(constraint);
    for (i, conj) in conjuncts.iter().enumerate() {
        if let Some(replacement) = extract_equality_for_var(conj, var) {
            let subst = vec![(var.clone(), replacement)];
            let other: Vec<ChcExpr> = conjuncts
                .iter()
                .enumerate()
                .filter(|(j, _)| *j != i)
                .map(|(_, c)| c.substitute(&subst))
                .collect();
            return Some(ChcExpr::and_all(other));
        }
    }
    None
}

fn reference_try_constant_interval_elimination(
    constraint: &ChcExpr,
    var: &ChcVar,
) -> Option<ChcExpr> {
    if !matches!(&var.sort, ChcSort::Int) {
        return None;
    }

    let conjuncts = reference_conjuncts(constraint);
    let mut lower: Option<num_bigint::BigInt> = None;
    let mut upper: Option<num_bigint::BigInt> = None;
    let mut found_bound = false;

    for conj in &conjuncts {
        if !reference_conjunct_mentions_var(conj, var) {
            continue;
        }
        found_bound = true;
        match classify_constant_int_bound(conj, var)? {
            ConstantIntBound::Lower(value) => {
                lower = Some(match lower.take() {
                    Some(current) => current.max(value),
                    None => value,
                });
            }
            ConstantIntBound::Upper(value) => {
                upper = Some(match upper.take() {
                    Some(current) => current.min(value),
                    None => value,
                });
            }
        }
    }

    if !found_bound {
        return None;
    }
    if matches!((lower, upper), (Some(lower), Some(upper)) if lower > upper) {
        return Some(ChcExpr::Bool(false));
    }

    Some(ChcExpr::and_all(
        conjuncts
            .into_iter()
            .filter(|conj| !reference_conjunct_mentions_var(conj, var)),
    ))
}

fn reference_try_one_sided_bound_elimination(
    constraint: &ChcExpr,
    var: &ChcVar,
) -> Option<ChcExpr> {
    let conjuncts = reference_conjuncts(constraint);
    let mut has_lower = false;
    let mut has_upper = false;
    let mut all_bounds = true;

    for conj in &conjuncts {
        if !reference_conjunct_mentions_var(conj, var) {
            continue;
        }
        match classify_bound(conj, var) {
            BoundType::Lower => has_lower = true,
            BoundType::Upper => has_upper = true,
            BoundType::NotBound => {
                all_bounds = false;
                break;
            }
        }
    }
    if !all_bounds || (has_lower && has_upper) {
        return None;
    }
    Some(ChcExpr::and_all(
        conjuncts
            .into_iter()
            .filter(|c| !reference_conjunct_mentions_var(c, var)),
    ))
}

/// Eliminate one variable with the occurrence-index algorithm, checked
/// against the reference rule application.
fn eliminate_single(constraint: &ChcExpr, var: &ChcVar) -> Option<ChcExpr> {
    let result = eliminate_locals(constraint, std::slice::from_ref(var)).map(|(c, _)| c);
    assert_eq!(result, reference_try_eliminate_var(constraint, var));
    result
}

// ---------------------------------------------------------------------------
// Differential test: occurrence index vs reference on random clauses.
// ---------------------------------------------------------------------------

/// SplitMix64: a deterministic, dependency-free generator for test inputs.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9E37_79B9_7F4A_7C15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xBF58_476D_1CE4_E5B9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94D0_49BB_1331_11EB);
        z ^ (z >> 31)
    }

    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }

    fn small_int(&mut self) -> ChcExpr {
        ChcExpr::int(self.below(9) as i64 - 4)
    }
}

fn bv_op(op: ChcOp, a: ChcExpr, b: ChcExpr) -> ChcExpr {
    ChcExpr::Op(op, vec![std::sync::Arc::new(a), std::sync::Arc::new(b)])
}

struct RandomClauseVars {
    ints: Vec<ChcVar>,
    bvs: Vec<ChcVar>,
    bools: Vec<ChcVar>,
    s0: ChcVar,
    s1: ChcVar,
    sb: ChcVar,
}

impl RandomClauseVars {
    fn new() -> Self {
        Self {
            ints: (0..6)
                .map(|i| ChcVar::new(format!("x{i}"), ChcSort::Int))
                .collect(),
            bvs: (0..4)
                .map(|i| ChcVar::new(format!("b{i}"), ChcSort::BitVec(8)))
                .collect(),
            bools: (0..2)
                .map(|i| ChcVar::new(format!("p{i}"), ChcSort::Bool))
                .collect(),
            s0: ChcVar::new("s0", ChcSort::Int),
            s1: ChcVar::new("s1", ChcSort::Int),
            sb: ChcVar::new("sb", ChcSort::BitVec(8)),
        }
    }
}

fn random_conjunct(rng: &mut SplitMix64, v: &RandomClauseVars, earlier: &[ChcExpr]) -> ChcExpr {
    let x = |rng: &mut SplitMix64| ChcExpr::var(v.ints[rng.below(v.ints.len())].clone());
    let b = |rng: &mut SplitMix64| ChcExpr::var(v.bvs[rng.below(v.bvs.len())].clone());
    let p = |rng: &mut SplitMix64| ChcExpr::var(v.bools[rng.below(v.bools.len())].clone());
    let s0 = ChcExpr::var(v.s0.clone());
    let s1 = ChcExpr::var(v.s1.clone());
    let sb = ChcExpr::var(v.sb.clone());
    let swap = |rng: &mut SplitMix64, a: ChcExpr, b: ChcExpr| {
        if rng.below(2) == 0 {
            (a, b)
        } else {
            (b, a)
        }
    };
    let cmp = |rng: &mut SplitMix64, a: ChcExpr, b: ChcExpr| match rng.below(4) {
        0 => ChcExpr::le(a, b),
        1 => ChcExpr::lt(a, b),
        2 => ChcExpr::ge(a, b),
        _ => ChcExpr::gt(a, b),
    };
    match rng.below(20) {
        // Equality chain x_{i+1} = x_i + 1.
        0..=3 => {
            let i = rng.below(v.ints.len() - 1);
            let next = ChcExpr::var(v.ints[i + 1].clone());
            let step = ChcExpr::add(ChcExpr::var(v.ints[i].clone()), ChcExpr::int(1));
            let (l, r) = swap(rng, next, step);
            ChcExpr::eq(l, r)
        }
        // Definition by a shared or local term.
        4 => {
            let lhs = x(rng);
            let rhs = if rng.below(2) == 0 {
                ChcExpr::add(s0, rng.small_int())
            } else {
                ChcExpr::add(x(rng), s1)
            };
            let (l, r) = swap(rng, lhs, rhs);
            ChcExpr::eq(l, r)
        }
        // Constant interval bounds.
        5..=7 => {
            let (var, bound) = (x(rng), rng.small_int());
            let (l, r) = swap(rng, var, bound);
            cmp(rng, l, r)
        }
        // Linear (one-sided) bounds, possibly over shared variables.
        8..=9 => {
            let lhs = match rng.below(3) {
                0 => ChcExpr::add(ChcExpr::mul(ChcExpr::int(2), x(rng)), s0),
                1 => ChcExpr::sub(x(rng), x(rng)),
                _ => ChcExpr::neg(x(rng)),
            };
            let rhs = if rng.below(2) == 0 {
                s1
            } else {
                rng.small_int()
            };
            let (l, r) = swap(rng, lhs, rhs);
            cmp(rng, l, r)
        }
        // Non-bound occurrences.
        10 => ChcExpr::not(ChcExpr::eq(x(rng), s0)),
        11 => ChcExpr::eq(ChcExpr::add(x(rng), x(rng)), s1),
        // Bit-vector chain and relations.
        12 => {
            let i = rng.below(v.bvs.len() - 1);
            let next = ChcExpr::var(v.bvs[i + 1].clone());
            let step = bv_op(
                ChcOp::BvAdd,
                ChcExpr::var(v.bvs[i].clone()),
                ChcExpr::BitVec(1, 8),
            );
            let (l, r) = swap(rng, next, step);
            ChcExpr::eq(l, r)
        }
        13 => match rng.below(3) {
            0 => ChcExpr::bv_ule(b(rng), sb),
            1 => {
                let var = b(rng);
                let (l, r) = swap(rng, var, sb);
                ChcExpr::eq(l, r)
            }
            _ => ChcExpr::eq(sb, bv_op(ChcOp::BvAdd, b(rng), b(rng))),
        },
        // Boolean locals: a substitution can split a conjunct into several.
        14 => p(rng),
        15 => {
            let def = match rng.below(4) {
                0 => ChcExpr::and_all([
                    ChcExpr::ge(x(rng), ChcExpr::int(0)),
                    ChcExpr::le(x(rng), s0),
                ]),
                1 => ChcExpr::ge(x(rng), s1),
                2 => ChcExpr::Bool(rng.below(4) != 0),
                _ => ChcExpr::not(p(rng)),
            };
            let var = p(rng);
            let (l, r) = swap(rng, var, def);
            ChcExpr::eq(l, r)
        }
        16 => ChcExpr::not(p(rng)),
        // Shared-only conjunct.
        17 => ChcExpr::le(s0, ChcExpr::add(s1, rng.small_int())),
        // Repeated conjunct.
        18 if !earlier.is_empty() => earlier[rng.below(earlier.len())].clone(),
        _ => {
            if rng.below(30) == 0 {
                ChcExpr::Bool(false)
            } else {
                ChcExpr::eq(x(rng), x(rng))
            }
        }
    }
}

fn random_clause(
    rng: &mut SplitMix64,
    v: &RandomClauseVars,
    p: crate::PredicateId,
    q: crate::PredicateId,
) -> HornClause {
    use crate::ClauseHead;

    let len = 2 + rng.below(12);
    let mut conjuncts: Vec<ChcExpr> = Vec::with_capacity(len);
    for _ in 0..len {
        let conj = random_conjunct(rng, v, &conjuncts);
        conjuncts.push(conj);
    }
    // `and_vec` keeps repeated conjuncts, like a constraint straight from a
    // transform that did not go through `and_all`.
    let constraint = ChcExpr::and_vec(conjuncts);
    // Sometimes a local-looking variable is shared through the head.
    let head_int = if rng.below(3) == 0 {
        ChcExpr::var(v.ints[rng.below(v.ints.len())].clone())
    } else {
        ChcExpr::var(v.s0.clone())
    };
    let body = ClauseBody::new(
        vec![(
            p,
            vec![
                ChcExpr::var(v.s0.clone()),
                ChcExpr::var(v.s1.clone()),
                ChcExpr::var(v.sb.clone()),
            ],
        )],
        Some(constraint),
    );
    let head = if rng.below(4) == 0 {
        ClauseHead::False
    } else {
        ClauseHead::Predicate(q, vec![head_int, ChcExpr::var(v.sb.clone())])
    };
    HornClause::new(body, head)
}

#[test]
#[ntest::timeout(120_000)]
fn occurrence_index_matches_reference_on_random_clauses() {
    use crate::smt::{SmtContext, SmtResult};

    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int, ChcSort::BitVec(8)]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::BitVec(8)]);
    let vars = RandomClauseVars::new();
    let eliminator = LocalVarEliminator::new();
    let mut rng = SplitMix64(0x5EED_1A7E_0CC0_u64);

    let mut identical = 0usize;
    let mut proved_equivalent = 0usize;
    let mut total_eliminated = 0usize;
    let mut contradictions = 0usize;
    const CLAUSES: usize = 3000;
    for round in 0..CLAUSES {
        let clause = random_clause(&mut rng, &vars, p, q);
        let (expected, expected_count) = reference_eliminate_in_clause(&clause);
        let (actual, actual_count) = eliminator.eliminate_in_clause(&clause);
        assert_eq!(
            actual_count, expected_count,
            "round {round}: eliminated-variable count differs for {clause:?}"
        );
        assert_eq!(actual.body.predicates, expected.body.predicates);
        total_eliminated += actual_count;
        if is_trivially_false(&expected) {
            contradictions += 1;
        }
        if actual.body.constraint == expected.body.constraint {
            identical += 1;
            continue;
        }
        let truth = |c: &Option<ChcExpr>| c.clone().unwrap_or(ChcExpr::Bool(true));
        let (old, new) = (
            truth(&expected.body.constraint),
            truth(&actual.body.constraint),
        );
        let differ = ChcExpr::not(ChcExpr::eq(old.clone(), new.clone()));
        let mut smt = SmtContext::new();
        match smt.check_sat(&differ) {
            SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {
                proved_equivalent += 1;
            }
            other => panic!(
                "round {round}: projections differ ({other:?})\nclause: {clause:?}\n\
                 reference: {old}\noccurrence index: {new}"
            ),
        }
    }
    eprintln!(
        "local-var-elim differential: {CLAUSES} clauses, {total_eliminated} vars eliminated, \
         {contradictions} contradictions, {identical} identical, {proved_equivalent} proved equivalent"
    );
    assert!(
        total_eliminated > CLAUSES,
        "generator must exercise elimination"
    );
    assert!(
        contradictions > 0,
        "generator must exercise the false collapse"
    );
}

/// 5,000 equality-defined locals plus 5,000 unrelated conjuncts. The
/// reference re-derives all 10,000 conjuncts' variable sets and rebuilds the
/// conjunction for every local (quadratic: minutes); the occurrence index
/// touches only the conjuncts that mention each local. (Each local is defined
/// from a head variable: a single chain `x_{i+1} = x_i + 1` grows terms past
/// the depth `substitute` reaches in some elimination orders, where keeping
/// the definition is the sound outcome.)
#[test]
#[ntest::timeout(5_000)]
fn many_defined_locals_with_many_unrelated_conjuncts_scale() {
    use crate::ClauseHead;

    const N: usize = 5_000;
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int, ChcSort::Int]);
    let s = ChcVar::new("s", ChcSort::Int);
    let t = ChcVar::new("t", ChcSort::Int);
    let u = ChcVar::new("u", ChcSort::Int);
    let x: Vec<ChcVar> = (0..N)
        .map(|i| ChcVar::new(format!("x{i}"), ChcSort::Int))
        .collect();

    let chain: Vec<ChcExpr> = (0..N)
        .map(|i| {
            ChcExpr::eq(
                ChcExpr::var(x[i].clone()),
                ChcExpr::add(ChcExpr::var(s.clone()), ChcExpr::int(i as i64)),
            )
        })
        .collect();
    let unrelated: Vec<ChcExpr> = (0..N)
        .map(|k| {
            ChcExpr::le(
                ChcExpr::add(ChcExpr::var(t.clone()), ChcExpr::int(k as i64)),
                ChcExpr::var(u.clone()),
            )
        })
        .collect();
    // Interleave so every chain conjunct sits among unrelated ones.
    let mut conjuncts = Vec::with_capacity(2 * N);
    for (c, w) in chain.into_iter().zip(unrelated.iter().cloned()) {
        conjuncts.push(c);
        conjuncts.push(w);
    }
    let args = vec![ChcExpr::var(s), ChcExpr::var(t), ChcExpr::var(u)];
    let clause = HornClause::new(
        ClauseBody::new(vec![(p, args.clone())], Some(ChcExpr::and_vec(conjuncts))),
        ClauseHead::Predicate(p, args),
    );

    let (result, eliminated) = LocalVarEliminator::new().eliminate_in_clause(&clause);
    assert_eq!(eliminated, N, "every chain local is defined by an equality");
    let expected = ChcExpr::and_all(unrelated)
        .simplify_array_ops()
        .simplify_constants();
    assert_eq!(result.body.constraint, Some(expected));
}

/// `vars()` stops at `MAX_EXPR_RECURSION_DEPTH` but `substitute` still
/// replaces a variable there. A local at depth exactly 500 in one conjunct
/// must still receive the substitution when its defining equation is dropped,
/// or the projection gains a spurious model: `x = 5 /\ T(x) < 5` with
/// `T(x) = x + 0 + ... + 0` is unsatisfiable.
#[test]
fn equality_substitution_reaches_a_variable_below_the_vars_depth_cutoff() {
    use crate::ClauseHead;
    let x = ChcVar::new("x", ChcSort::Int);
    for depth_of_x in [400usize, 499, 500, 501, 502] {
        let mut t = ChcExpr::var(x.clone());
        // The `<` is at depth 1 and `x` sits `depth_of_x` levels below the root.
        for _ in 0..depth_of_x - 1 {
            t = ChcExpr::add(t, ChcExpr::int(0));
        }
        let constraint = ChcExpr::and_vec(vec![
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5)),
            ChcExpr::lt(t, ChcExpr::int(5)),
        ]);
        let clause = HornClause::new(ClauseBody::new(vec![], Some(constraint)), ClauseHead::False);
        let (new, _) = LocalVarEliminator::new().eliminate_in_clause(&clause);
        // Either the substitution reached `x` and the clause became `false`,
        // or `x` was not eliminated and its definition is still there; never
        // a constraint where `x` is free with its definition dropped.
        let kept_x = new
            .body
            .constraint
            .as_ref()
            .is_some_and(|c| exact_vars(c).contains(&x));
        assert!(
            is_trivially_false(&new) || kept_x,
            "x at depth {depth_of_x}: definition dropped with x left free"
        );
        if depth_of_x < 498 {
            assert!(is_trivially_false(&new), "a reachable x is substituted");
        }
    }
}

/// A conjunct inside an `and` nested deeper than `collect_conjuncts` flattens
/// must still be seen by every rule: here the bounds `x >= 0` and `x <= -1`
/// contradict, but the second sits under a 1,100-deep `and` chain.
#[test]
fn deeply_nested_and_is_flattened_for_every_rule() {
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let s = ChcVar::new("s", ChcSort::Int);
    let mut lump = ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(-1));
    for i in (0..1_100i64).rev() {
        lump = ChcExpr::Op(
            ChcOp::And,
            vec![
                std::sync::Arc::new(ChcExpr::ge(ChcExpr::var(s.clone()), ChcExpr::int(i))),
                std::sync::Arc::new(lump),
            ],
        );
    }
    let constraint = ChcExpr::and_vec(vec![
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(1)),
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        lump,
    ]);
    for order in [vec![y.clone(), x.clone()], vec![x.clone(), y.clone()]] {
        let (result, _) =
            eliminate_locals(&constraint, &order).expect("both locals are eliminable");
        assert_eq!(result, ChcExpr::Bool(false), "order {order:?}");
    }
}
