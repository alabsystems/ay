// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_is_trivial_contradiction_le_and_ge_is_not_contradiction() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    let expr = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::ge(ChcExpr::var(a), ChcExpr::var(b)),
    );

    assert!(!cube::is_trivial_contradiction(&expr));
}

#[test]
fn test_point_values_satisfy_cube_handles_simple_bounds() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let x = ChcVar::new("x", ChcSort::Int);
    let cube = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(10)),
    );

    let mut values: FxHashMap<String, SmtValue> = FxHashMap::default();
    values.insert("x".to_string(), SmtValue::Int(5));
    assert!(solver.point_values_satisfy_cube(&cube, &values));

    values.insert("x".to_string(), SmtValue::Int(11));
    assert!(!solver.point_values_satisfy_cube(&cube, &values));
}

#[test]
fn test_point_values_satisfy_cube_swaps_constant_on_lhs() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    let x = ChcVar::new("x", ChcSort::Int);
    // (<= 10 x)  <=>  (>= x 10)
    let cube = ChcExpr::le(ChcExpr::int(10), ChcExpr::var(x));

    let mut values: FxHashMap<String, SmtValue> = FxHashMap::default();
    values.insert("x".to_string(), SmtValue::Int(11));
    assert!(solver.point_values_satisfy_cube(&cube, &values));

    values.insert("x".to_string(), SmtValue::Int(9));
    assert!(!solver.point_values_satisfy_cube(&cube, &values));
}

#[test]
fn test_is_trivial_contradiction_le_and_gt_is_contradiction() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    let expr = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::gt(ChcExpr::var(a), ChcExpr::var(b)),
    );

    assert!(cube::is_trivial_contradiction(&expr));
}

#[test]
fn test_is_trivial_contradiction_le_ge_and_not_eq_is_contradiction() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    let expr = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
            ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ),
        ChcExpr::not(ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b))),
    );

    assert!(cube::is_trivial_contradiction(&expr));
}

#[test]
fn test_is_trivial_contradiction_reversed_order_is_handled() {
    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);

    let not_contradiction = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::gt(ChcExpr::var(b.clone()), ChcExpr::var(a.clone())),
    );
    assert!(!cube::is_trivial_contradiction(&not_contradiction));

    let contradiction = ChcExpr::and(
        ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::lt(ChcExpr::var(b), ChcExpr::var(a)),
    );
    assert!(cube::is_trivial_contradiction(&contradiction));
}

#[test]
fn test_is_trivial_contradiction_detects_negated_or_covering_fact_9185() {
    let x = ChcVar::new("x", ChcSort::BitVec(32));
    let fact = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(1, 32));
    let bad_state = ChcExpr::not(ChcExpr::or(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 32)),
        fact.clone(),
    ));
    let expr = ChcExpr::and(fact, bad_state);

    assert!(cube::is_trivial_contradiction(&expr));
}

#[test]
fn test_is_trivial_contradiction_detects_negated_and_already_entailed_9185() {
    let x = ChcVar::new("x", ChcSort::BitVec(32));
    let y = ChcVar::new("y", ChcSort::BitVec(32));
    let fact_x = ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, 32));
    let fact_y = ChcExpr::eq(ChcExpr::var(y), ChcExpr::BitVec(8, 32));
    let expr = ChcExpr::and_all([
        fact_x.clone(),
        fact_y.clone(),
        ChcExpr::not(ChcExpr::and(fact_x, fact_y)),
    ]);

    assert!(cube::is_trivial_contradiction(&expr));
}

#[test]
fn pdr_applies_user_hints_as_lemmas() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))

(assert
  (forall ((x Int) (x_next Int))
(=>
  (and (inv x) (= x_next (+ x 1)) (< x 5))
  (inv x_next)
)
  )
)

(assert (forall ((x Int)) (=> (and (inv x) (< x (- 123))) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.predicates()[0].id;
    let canonical_vars = solver.canonical_vars(pred_id).unwrap();
    let x = canonical_vars[0].clone();

    // Use a weak-but-inductive hint that isn't produced by built-in hint providers
    // (init bounds would yield x >= 0, but not x >= -123).
    let hint_formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(-123));
    solver.config.user_hints = vec![LemmaHint::new(pred_id, hint_formula.clone(), 0, "user")];

    assert!(
        !solver.frames[1].contains_lemma(pred_id, &hint_formula),
        "test setup: hint unexpectedly already present"
    );

    solver.apply_lemma_hints(HintStage::Startup);

    assert!(
        solver
            .frames
            .iter()
            .any(|f| f.contains_lemma(pred_id, &hint_formula)),
        "expected user hint to be added as a lemma"
    );
}

#[test]
fn pdr_applies_conjunctive_user_hints_when_individual_hints_fail_self_inductive() {
    // Regression test: some hint sets are jointly self-inductive even when each hint
    // fails `is_self_inductive_blocking` in isolation. In these cases we should
    // retry validation on the conjunction.
    //
    // Construction:
    // - Hint A: x >= 0
    // - Hint B: y = 0
    // - From x>=0 alone: unreachable states with y=1 can decrement x below 0.
    // - From y=0 alone: unreachable states with x<0 can flip y to 1.
    // - From (x>=0 ∧ y=0): both counterexample branches are pruned, making the
    //   conjunction self-inductive.
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int Int) Bool)

(assert (forall ((x Int) (y Int)) (=> (and (= x 0) (= y 0)) (inv x y))))

; y = 0, x >= 0  -> x' = x + 1, y' = 0
(assert
  (forall ((x Int) (y Int) (x2 Int) (y2 Int))
(=>
  (and (inv x y) (= y 0) (>= x 0) (= x2 (+ x 1)) (= y2 0))
  (inv x2 y2)
)
  )
)

; y = 0, x < 0  -> x' = x - 1, y' = 1   (breaks y=0 unless x>=0 is assumed)
(assert
  (forall ((x Int) (y Int) (x2 Int) (y2 Int))
(=>
  (and (inv x y) (= y 0) (< x 0) (= x2 (- x 1)) (= y2 1))
  (inv x2 y2)
)
  )
)

; y = 1, x >= 0 -> x' = x - 1, y' = 0   (breaks x>=0 unless y=0 is assumed)
(assert
  (forall ((x Int) (y Int) (x2 Int) (y2 Int))
(=>
  (and (inv x y) (= y 1) (>= x 0) (= x2 (- x 1)) (= y2 0))
  (inv x2 y2)
)
  )
)

; y = 1, x < 0  -> x' = x + 1, y' = 1
(assert
  (forall ((x Int) (y Int) (x2 Int) (y2 Int))
(=>
  (and (inv x y) (= y 1) (< x 0) (= x2 (+ x 1)) (= y2 1))
  (inv x2 y2)
)
  )
)

; No safety query needed: we only test hint injection.
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let canonical_vars = solver.canonical_vars(pred_id).unwrap();
    let x = canonical_vars[0].clone();
    let y = canonical_vars[1].clone();

    let hint_x_ge_0 = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0));
    let hint_y_eq_0 = ChcExpr::eq(ChcExpr::var(y), ChcExpr::int(0));
    solver.config.user_hints = vec![
        LemmaHint::new(pred_id, hint_x_ge_0.clone(), 0, "test-conj"),
        LemmaHint::new(pred_id, hint_y_eq_0.clone(), 0, "test-conj"),
    ];

    let mut expected_conjuncts = vec![hint_x_ge_0, hint_y_eq_0];
    expected_conjuncts.sort();
    let expected = ChcExpr::and_vec(expected_conjuncts);

    assert!(
        solver
            .frames
            .iter()
            .all(|f| !f.contains_lemma(pred_id, &expected)),
        "test setup: conjunction unexpectedly already present"
    );

    // Use a stage with no built-in providers for this problem shape, so the test isolates
    // the user-hint logic (bounds-from-init + recurrence only run at Startup).
    solver.apply_lemma_hints(HintStage::Stuck);

    assert!(
        solver
            .frames
            .iter()
            .any(|f| f.contains_lemma(pred_id, &expected)),
        "expected conjunction hint to be added as a lemma"
    );
}

#[test]
fn pdr_solve_applies_user_hints_as_lemmas() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))

(assert
  (forall ((x Int) (x_next Int))
(=>
  (and (inv x) (= x_next (+ x 1)) (< x 5))
  (inv x_next)
)
  )
)

(assert (forall ((x Int)) (=> (and (inv x) (< x (- 123))) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_id = solver.problem.predicates()[0].id;
    let canonical_vars = solver.canonical_vars(pred_id).unwrap();
    let x = canonical_vars[0].clone();
    let hint_formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(-123));
    solver.config.user_hints = vec![LemmaHint::new(pred_id, hint_formula.clone(), 0, "user")];

    assert!(
        !solver.frames[1].contains_lemma(pred_id, &hint_formula),
        "test setup: hint unexpectedly already present"
    );

    // Call apply_lemma_hints directly because solve() may prove safety via
    // discovery before reaching the hint application code (the problem is
    // trivially safe: x starts at 0, increments to 5, query is x < -123).
    solver.apply_lemma_hints(crate::lemma_hints::HintStage::Startup);

    assert!(
        solver
            .frames
            .iter()
            .any(|f| f.contains_lemma(pred_id, &hint_formula)),
        "expected user hint to be applied as a lemma"
    );

    // Also verify solve() produces Safe
    let result = solver.solve();
    assert!(
        matches!(result, crate::pdr::PdrResult::Safe(_)),
        "expected Safe result"
    );
}

/// Multi-BB while loop where the loop closes through a second relation:
/// `head` has NO self-loop clause (cycle is head -> body -> head).
/// Safe: x starts at 2 and only increments, query is x < 2.
const MULTI_BB_LOOP_SAFE_SMT2: &str = r#"
(set-logic HORN)

(declare-fun head (Int) Bool)
(declare-fun body (Int) Bool)

(assert (forall ((x Int)) (=> (= x 2) (head x))))
(assert (forall ((x Int)) (=> (and (head x) (< x 10)) (body x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (body x) (= x2 (+ x 1))) (head x2))))
(assert (forall ((x Int)) (=> (and (head x) (< x 2)) false)))

(check-sat)
"#;

#[test]
fn pdr_admits_relative_induction_hint_on_loop_head_without_self_loop() {
    // model-checker-consumer wishlist item 6: user loop invariants forwarded as hints were
    // rejected with "not self-inductive" when establishment flows in from a
    // DIFFERENT BB relation. `head` has no self-loop clause, so
    // is_self_inductive_blocking rejects any hint for it VACUOUSLY (#8578
    // anti-vacuous guard). The hint x >= 2 is preserved by the incoming edges
    // (relative induction) and must be admitted via the is_entry_inductive
    // fallthrough.
    let problem = ChcParser::parse(MULTI_BB_LOOP_SAFE_SMT2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let head_id = solver.problem.get_predicate_by_name("head").unwrap().id;
    let canonical_vars = solver.canonical_vars(head_id).unwrap();
    let x = canonical_vars[0].clone();
    let hint_formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(2));

    // Pre-fix rejection path: no self-loop clause => vacuous self-inductive
    // rejection (this is exactly the "rejected: not self-inductive" symptom).
    assert!(
        !solver.predicate_has_self_loop_clause(head_id),
        "test setup: head must have no self-loop clause"
    );
    let blocking = ChcExpr::not(hint_formula.clone());
    assert!(
        !solver.is_self_inductive_blocking_uncached(&blocking, head_id),
        "test setup: self-inductive check must reject vacuously (no self-loop)"
    );

    solver.config.user_hints = vec![LemmaHint::new(head_id, hint_formula.clone(), 0, "user")];
    solver.apply_lemma_hints(HintStage::Startup);

    assert!(
        solver
            .frames
            .iter()
            .any(|f| f.contains_lemma(head_id, &hint_formula)),
        "expected relative-induction hint to be admitted as a lemma"
    );

    // The admitted lemma must carry the relative_induction_only origin tag so
    // strict verification-skip paths (individually_inductive, #5877) can
    // exclude it independently of the #8578 anti-vacuous oracle guard.
    let tagged = solver.frames.iter().any(|f| {
        f.lemmas.iter().any(|l| {
            l.predicate == head_id && l.formula == hint_formula && l.relative_induction_only
        })
    });
    assert!(
        tagged,
        "admitted hint must be tagged relative_induction_only"
    );

    // End-to-end: the problem is safe and must stay provable with the hint.
    let result = solver.solve();
    assert!(
        matches!(result, crate::pdr::PdrResult::Safe(_)),
        "expected Safe result, got {result:?}"
    );
}

#[test]
fn relative_induction_hint_lemma_is_excluded_from_individually_inductive_treatment() {
    // #5877 guard verification: a hint admitted under relative (entry)
    // induction only must NOT be admissible by the strict per-lemma oracles
    // that safety_proof_inductive.rs recomputes before granting the
    // individually_inductive whole-model verification skip. Both oracles must
    // reject the lemma (anti-vacuous #8578 guard: no self-loop clause), and
    // the admitted lemma additionally carries the relative_induction_only tag
    // which short-circuits those recomputations explicitly.
    let problem = ChcParser::parse(MULTI_BB_LOOP_SAFE_SMT2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let head_id = solver.problem.get_predicate_by_name("head").unwrap().id;
    let canonical_vars = solver.canonical_vars(head_id).unwrap();
    let x = canonical_vars[0].clone();
    let hint_formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(2));

    solver.config.user_hints = vec![LemmaHint::new(head_id, hint_formula.clone(), 0, "user")];
    solver.apply_lemma_hints(HintStage::Startup);

    let admitted: Vec<_> = solver
        .frames
        .iter()
        .flat_map(|f| f.lemmas.iter())
        .filter(|l| l.predicate == head_id && l.formula == hint_formula)
        .collect();
    assert!(
        !admitted.is_empty(),
        "test setup: hint must be admitted (covered by the admission test)"
    );
    assert!(
        admitted.iter().all(|l| l.relative_induction_only),
        "every admitted copy must be tagged relative_induction_only"
    );

    // The strict recomputation path (safety_proof_inductive.rs) admits a lemma
    // into individually_inductive treatment only when a self-inductiveness
    // oracle accepts it. Both must reject this lemma: head has no self-loop
    // clause, so self-inductiveness is vacuous and unproven.
    let blocking = ChcExpr::not(hint_formula.clone());
    assert!(
        !solver.is_strictly_self_inductive_blocking(&blocking, head_id),
        "strict self-inductive oracle must reject the entry-only hint lemma"
    );
    assert!(
        !solver.is_self_inductive_blocking(&blocking, head_id),
        "frame-strengthened self-inductive oracle must reject the entry-only hint lemma"
    );
}

#[test]
fn pdr_poisoned_relative_induction_hint_cannot_force_false_safe() {
    // A poisoned (NON-invariant) hint on a no-self-loop loop head must not
    // produce a false Safe. The loop DECREMENTS x from 2, so head reaches
    // x = -1 and the query fires: the correct verdict is Unsafe. The hint
    // x >= 2 does hold at 1-step reachability (it may legitimately be
    // admitted as a low-level frame lemma), but it is NOT an invariant;
    // deeper frames and final model verification must still surface the
    // counterexample.
    let smt2 = r#"
(set-logic HORN)

(declare-fun head (Int) Bool)
(declare-fun body (Int) Bool)

(assert (forall ((x Int)) (=> (= x 2) (head x))))
(assert (forall ((x Int)) (=> (and (head x) (> x (- 10))) (body x))))
(assert (forall ((x Int) (x2 Int)) (=> (and (body x) (= x2 (- x 1))) (head x2))))
(assert (forall ((x Int)) (=> (and (head x) (< x 0)) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let head_id = solver.problem.get_predicate_by_name("head").unwrap().id;
    let canonical_vars = solver.canonical_vars(head_id).unwrap();
    let x = canonical_vars[0].clone();
    let hint_formula = ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(2));
    solver.config.user_hints = vec![LemmaHint::new(head_id, hint_formula, 0, "poisoned")];

    let result = solver.solve();
    assert!(
        matches!(result, crate::pdr::PdrResult::Unsafe(_)),
        "poisoned hint must not flip an Unsafe problem, got {result:?}"
    );
}
