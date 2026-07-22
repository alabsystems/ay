// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for proof-obligation blocking and lemma generalization.

use super::super::*;
use super::bool_normalization::{denormalize_int_to_bool, normalize_bool_to_int};

mod may_pob;
mod source_regression_tests;

fn unit_test_config() -> PdrConfig {
    PdrConfig {
        verbose: false,
        use_interpolation: false,
        use_mbp: false,
        use_must_summaries: false,
        use_level_priority: false,
        use_mixed_summaries: false,
        use_convex_closure: false,
        use_restarts: false,
        use_pob_push: false,
        ..Default::default()
    }
}

fn run_cluster_generalization_via_production_path(
    solver: &mut PdrSolver,
    predicate: PredicateId,
    level: usize,
    blocking_formula: &ChcExpr,
    pob_state: &ChcExpr,
) -> ChcExpr {
    let mut pob = ProofObligation::new(predicate, pob_state.clone(), level);
    solver.try_global_generalization(blocking_formula, &mut pob, false)
}

#[test]
fn generalize_blocking_formula_discovers_disjunctive_affine_invariant_from_anchor() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((a Int) (b Int))
  (=> (and (= a 0) (= b 0)) (Inv a b))))
(assert (forall ((a Int) (b Int) (a2 Int) (b2 Int))
  (=> (and (Inv a b) (= a2 (+ a 1)) (= b2 (+ b 2))) (Inv a2 b2))))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut config = unit_test_config();
    config.use_relational_equality = false;
    config.use_init_bound_weakening = false;
    config.use_range_weakening = false;
    config.use_farkas_combination = false;
    let mut solver = PdrSolver::new(problem, config);

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let vars = solver.canonical_vars(inv).unwrap().to_vec();
    let anchor = solver
        .normalize_affine_equality_for_target(
            inv,
            &ChcExpr::eq(
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(vars[0].clone())),
                ChcExpr::var(vars[1].clone()),
            ),
        )
        .expect("normalize affine anchor");
    solver.add_lemma_to_frame(Lemma::new(inv, anchor.clone(), 1), 1);

    let blocked_state = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::int(1)),
        ChcExpr::eq(ChcExpr::var(vars[1].clone()), ChcExpr::int(1)),
    );

    let generalized = solver.generalize_blocking_formula(&blocked_state, inv, 1);

    let lhs = match &anchor {
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => match args[1].as_ref() {
            ChcExpr::Int(0) => args[0].as_ref().clone(),
            _ => panic!("expected normalized affine anchor, got {anchor}"),
        },
        _ => panic!("expected equality anchor, got {anchor}"),
    };
    let expected = ChcExpr::and(
        ChcExpr::not(ChcExpr::eq(lhs.clone(), ChcExpr::int(-1))),
        ChcExpr::not(ChcExpr::eq(lhs, ChcExpr::int(0))),
    );

    assert_eq!(
        generalized, expected,
        "expected adjacent disjunctive affine blocking formula"
    );
}

#[test]
fn block_obligation_mbp_predecessor_mentions_all_canonical_vars() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int) (y Int) (z Int))
(=> (and (Inv x)
         (= y (+ x 1))
         (or (= z 0) (= z 1))
         (> y 0))
    (Inv y))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 2)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut config = unit_test_config();
    config.use_mbp = true;
    let mut solver = PdrSolver::new(problem, config);

    // Use level 2 so predecessor extraction takes the prev_level > 0 path.
    solver.frames.push(Frame::new());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_x = solver.canonical_vars(inv).unwrap()[0].clone();
    let bad_state = ChcExpr::gt(ChcExpr::var(canon_x), ChcExpr::int(2));
    let mut pob = ProofObligation::new(inv, bad_state.clone(), 2);

    let reachable = match solver.block_obligation_with_local_blocked(&mut pob, &[], &[]) {
        BlockResult::Reachable(pred) => pred,
        BlockResult::Blocked(_) => panic!("expected Reachable predecessor, got Blocked"),
        BlockResult::AlreadyBlocked => {
            panic!("expected Reachable predecessor, got AlreadyBlocked")
        }
        BlockResult::Unknown => panic!("expected Reachable predecessor, got Unknown"),
    };

    let clause = solver
        .problem
        .clauses_defining(inv)
        .find(|c| !c.body.predicates.is_empty())
        .expect("expected transition clause");
    let (body_pred, body_args) = &clause.body.predicates[0];
    let head_args = match &clause.head {
        crate::ClauseHead::Predicate(_, args) => args.as_slice(),
        crate::ClauseHead::False => panic!("expected predicate head"),
    };
    let state_on_head = solver
        .apply_to_args(inv, &bad_state, head_args)
        .expect("state should map to head args");
    let base = ChcExpr::and(
        clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true)),
        state_on_head,
    );
    let frame_constraint = solver.frames[1]
        .get_predicate_constraint(*body_pred)
        .unwrap_or(ChcExpr::Bool(true));
    let frame_on_body = solver
        .apply_to_args(*body_pred, &frame_constraint, body_args)
        .expect("frame constraint should map to body args");
    let query = solver.bound_int_vars(ChcExpr::and_all([
        base,
        frame_on_body,
        ChcExpr::Bool(true), // no local unknown-predecessor exclusions in this test
    ]));

    let mbp_cube = solver
        .cube_from_model_mbp(*body_pred, body_args, &query, &reachable.smt_model)
        .expect("MBP cube should be extractable");
    let canon_vars = solver.canonical_vars(inv).unwrap();

    assert!(
        !cube::is_point_cube_for_vars(&mbp_cube, canon_vars),
        "test setup must produce a non-point MBP cube"
    );
    // After #2918: the ground-POB override uses a variable-presence check
    // instead of is_point_cube_for_vars. Since cube_from_model_mbp augments
    // unconstrained vars (#2481), all canonical vars are present in the MBP
    // cube, so the override does NOT fire. The predecessor keeps the MBP
    // generalization (may contain inequalities, not just equalities).
    let state_vars = reachable.state.vars();
    assert!(
        canon_vars
            .iter()
            .all(|cv| state_vars.iter().any(|v| v.name == cv.name)),
        "returned predecessor must mention all canonical vars (variable-presence check)"
    );
}

#[test]
fn block_obligation_level0_returns_reachable_for_sat_fact() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, unit_test_config());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_x = solver.canonical_vars(inv).unwrap()[0].clone();

    let state = ChcExpr::eq(ChcExpr::var(canon_x), ChcExpr::int(0));
    let mut pob = ProofObligation::new(inv, state.clone(), 0);

    match solver.block_obligation_with_local_blocked(&mut pob, &[], &[]) {
        BlockResult::Reachable(pred) => {
            assert_eq!(pred.predicate, inv);
            assert_eq!(pred.clause_index, 0);
            assert_eq!(pred.state, state);
        }
        _ => panic!("expected Reachable"),
    }
}

#[test]
fn block_obligation_array_level0_fact_reuses_head_fact_session() {
    // Symbolic array access (variable index) resists scalarization (#d29877046 fix).
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv ((Array Int Int) Int) Bool)
(assert
  (forall ((v (Array Int Int)) (k Int))
    (=>
      (and
        (= k 0)
        (= (select v k) 0))
      (Inv v k))))
(assert
  (forall ((v (Array Int Int)) (k Int))
    (=>
      (and (Inv v k) (< (select v k) 0))
      false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, unit_test_config());
    assert!(
        solver.uses_arrays,
        "symbolic select must survive scalarization"
    );
    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon = solver.canonical_vars(inv).unwrap();
    let state = ChcExpr::eq(
        ChcExpr::select(
            ChcExpr::var(canon[0].clone()),
            ChcExpr::var(canon[1].clone()),
        ),
        ChcExpr::int(0),
    );
    let session_key = ArraySessionKey::HeadFact { clause_index: 0 };

    let mut pob = ProofObligation::new(inv, state.clone(), 0);
    let first = solver.block_obligation_with_local_blocked(&mut pob, &[], &[]);
    assert!(
        matches!(first, BlockResult::Reachable(_)),
        "expected level-0 array fact predecessor"
    );
    assert_eq!(solver.array_clause_sessions.len(), 1);
    assert_eq!(
        solver
            .array_clause_sessions
            .get(&session_key)
            .unwrap()
            .query_count(),
        1
    );

    let mut pob_again = ProofObligation::new(inv, state, 0);
    let second = solver.block_obligation_with_local_blocked(&mut pob_again, &[], &[]);
    assert!(
        matches!(second, BlockResult::Reachable(_)),
        "expected repeated level-0 array fact predecessor"
    );
    assert_eq!(solver.array_clause_sessions.len(), 1);
    assert_eq!(
        solver
            .array_clause_sessions
            .get(&session_key)
            .unwrap()
            .query_count(),
        2
    );
}

#[test]
fn block_obligation_array_prev_level0_reuses_prev_level_init_session() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv ((Array Int Bool) Int) Bool)
(assert
  (forall ((v (Array Int Bool)) (c Int))
    (=>
      (and (= c 0) (= v ((as const (Array Int Bool)) false)))
      (Inv v c))))
(assert
  (forall ((v (Array Int Bool)) (c Int) (v2 (Array Int Bool)) (c2 Int))
    (=>
      (and
        (Inv v c)
        (= v2 (store v c true))
        (= c2 (+ c 1))
        (<= c 10))
      (Inv v2 c2))))
(assert
  (forall ((v (Array Int Bool)) (c Int))
    (=>
      (and (Inv v c) (< c 0))
      false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, unit_test_config());
    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_c = solver.canonical_vars(inv).unwrap()[1].clone();
    let state = ChcExpr::eq(ChcExpr::var(canon_c), ChcExpr::int(1));
    let session_key = ArraySessionKey::PrevLevelInit {
        clause_index: 1,
        fact_index: 0,
    };

    let mut pob = ProofObligation::new(inv, state.clone(), 1);
    let first = solver.block_obligation_with_local_blocked(&mut pob, &[], &[]);
    assert!(
        matches!(first, BlockResult::Reachable(_)),
        "expected prev_level=0 array predecessor"
    );
    assert_eq!(
        solver
            .array_clause_sessions
            .get(&session_key)
            .unwrap()
            .query_count(),
        1
    );

    let mut pob_again = ProofObligation::new(inv, state, 1);
    let second = solver.block_obligation_with_local_blocked(&mut pob_again, &[], &[]);
    assert!(
        matches!(second, BlockResult::Reachable(_)),
        "expected repeated prev_level=0 array predecessor"
    );
    assert_eq!(
        solver
            .array_clause_sessions
            .get(&session_key)
            .unwrap()
            .query_count(),
        2
    );
}

#[test]
fn block_obligation_array_prev_level_positive_reuses_single_body_session() {
    // Symbolic array access (variable index) resists scalarization (#e4df2cc74 fix).
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv ((Array Int Int) Int) Bool)
(assert
  (forall ((v (Array Int Int)) (k Int))
    (=>
      (and (= k 0) (= (select v k) 0))
      (Inv v k))))
(assert
  (forall ((v (Array Int Int)) (k Int) (v2 (Array Int Int)) (k2 Int))
    (=>
      (and
        (Inv v k)
        (= v2 (store v k (+ (select v k) 1)))
        (= k2 (+ k 1))
        (<= k 10))
      (Inv v2 k2))))
(assert
  (forall ((v (Array Int Int)) (k Int))
    (=>
      (and (Inv v k) (< (select v k) 0))
      false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, unit_test_config());
    assert!(
        solver.uses_arrays,
        "symbolic selects must resist scalarization"
    );
    solver.frames.push(Frame::new());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon = solver.canonical_vars(inv).unwrap();
    // State with array ops triggers the array session path (contains_array_ops).
    let state = ChcExpr::eq(
        ChcExpr::select(
            ChcExpr::var(canon[0].clone()),
            ChcExpr::var(canon[1].clone()),
        ),
        ChcExpr::int(1),
    );
    let session_key = ArraySessionKey::SingleBody { clause_index: 1 };

    let mut pob = ProofObligation::new(inv, state.clone(), 2);
    let first = solver.block_obligation_with_local_blocked(&mut pob, &[], &[]);
    assert!(
        matches!(first, BlockResult::Reachable(_)),
        "expected prev_level>0 array predecessor"
    );
    assert_eq!(
        solver
            .array_clause_sessions
            .get(&session_key)
            .unwrap()
            .query_count(),
        1
    );

    let mut pob_again = ProofObligation::new(inv, state, 2);
    let second = solver.block_obligation_with_local_blocked(&mut pob_again, &[], &[]);
    assert!(
        matches!(second, BlockResult::Reachable(_)),
        "expected repeated prev_level>0 array predecessor"
    );
    assert_eq!(
        solver
            .array_clause_sessions
            .get(&session_key)
            .unwrap()
            .query_count(),
        2
    );
}

#[test]
fn block_obligation_returns_already_blocked_when_frame_constraint_unsat() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, unit_test_config());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_x = solver.canonical_vars(inv).unwrap()[0].clone();

    let frame_lemma = Lemma::new(
        inv,
        ChcExpr::le(ChcExpr::var(canon_x.clone()), ChcExpr::int(0)),
        1,
    );
    solver.add_lemma(frame_lemma, 1);

    let state = ChcExpr::gt(ChcExpr::var(canon_x), ChcExpr::int(0));
    let mut pob = ProofObligation::new(inv, state, 1);

    match solver.block_obligation_with_local_blocked(&mut pob, &[], &[]) {
        BlockResult::AlreadyBlocked => {}
        _ => panic!("expected AlreadyBlocked"),
    }
}

#[test]
fn block_obligation_returns_already_blocked_from_relational_invariant() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((a Int) (b Int)) (=> (and (= a 0) (= b 0)) (Inv a b))))
(assert (forall ((a Int) (b Int)) (=> (and (Inv a b) (> a 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, unit_test_config());

    // Ensure pob.level=2 exists while keeping frame[2] empty, so the
    // level-local already-blocked SMT check does not apply.
    solver.frames.push(Frame::new());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_vars = solver.canonical_vars(inv).unwrap();
    let a = canon_vars[0].clone();
    let b = canon_vars[1].clone();

    solver.add_lemma(
        Lemma::new(
            inv,
            ChcExpr::le(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
            1,
        ),
        1,
    );

    // bad_state: (a >= b) ∧ ¬(a = b)  ⇒  (a > b), which contradicts (a <= b).
    let bad_state = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(a.clone()), ChcExpr::var(b.clone())),
        ChcExpr::not(ChcExpr::eq(ChcExpr::var(a), ChcExpr::var(b))),
    );
    let mut pob = ProofObligation::new(inv, bad_state, 2);

    match solver.block_obligation_with_local_blocked(&mut pob, &[], &[]) {
        BlockResult::AlreadyBlocked => {}
        _ => panic!("expected AlreadyBlocked"),
    }
}

#[test]
fn block_obligation_returns_already_blocked_from_parity_invariant() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (Inv x))))
(assert (forall ((x Int)) (=> (and (Inv x) (> x 0)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, unit_test_config());

    // Ensure pob.level=2 exists while keeping frame[2] empty, so the
    // level-local already-blocked SMT check does not apply.
    solver.frames.push(Frame::new());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_x = solver.canonical_vars(inv).unwrap()[0].clone();

    let mod_expr = ChcExpr::mod_op(ChcExpr::var(canon_x), ChcExpr::int(6));
    solver.add_lemma(
        Lemma::new(inv, ChcExpr::eq(mod_expr.clone(), ChcExpr::int(0)), 1),
        1,
    );

    let bad_state = ChcExpr::not(ChcExpr::eq(mod_expr, ChcExpr::int(0)));
    let mut pob = ProofObligation::new(inv, bad_state, 2);

    match solver.block_obligation_with_local_blocked(&mut pob, &[], &[]) {
        BlockResult::AlreadyBlocked => {}
        _ => panic!("expected AlreadyBlocked"),
    }
}

#[test]
fn block_obligation_preserves_mbp_generalization_with_var_presence_check() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun P (Int) Bool)
(declare-fun Q (Int) Bool)
(assert (forall ((x Int)) (=> (= x 5) (P x))))
(assert
  (forall ((x Int) (y Int))
(=> (and (P x) (= x (+ y 1)) (> y 0))
    (Q x))))
(assert (forall ((x Int)) (=> (and (Q x) (> x 100)) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut config = unit_test_config();
    config.use_mbp = true;
    let mut solver = PdrSolver::new(problem, config);

    // Force the non-level-0 predecessor path.
    solver.frames.push(Frame::new());
    solver.frames.push(Frame::new());

    let p = solver.problem.get_predicate_by_name("P").unwrap().id;
    let q = solver.problem.get_predicate_by_name("Q").unwrap().id;
    let qx = solver.canonical_vars(q).unwrap()[0].clone();
    let pob_state = ChcExpr::gt(ChcExpr::var(qx), ChcExpr::int(1));
    let mut pob = ProofObligation::new(q, pob_state.clone(), 2);

    let predecessor = match solver.block_obligation_with_local_blocked(&mut pob, &[], &[]) {
        BlockResult::Reachable(pred) => pred,
        _ => panic!("expected Reachable predecessor"),
    };

    assert_eq!(predecessor.predicate, p);

    // cube_from_model_mbp augments unconstrained canonical vars with model
    // values (#2481), so all canonical vars should appear in the predecessor
    // state. Inequalities are allowed (MBP generalization is preserved).
    let canonical_vars = solver.canonical_vars(p).unwrap().to_vec();
    let state_vars = predecessor.state.vars();
    assert!(
        canonical_vars
            .iter()
            .all(|cv| state_vars.iter().any(|v| v.name == cv.name)),
        "MBP augmentation should produce predecessor mentioning all canonical vars"
    );

    let clause = &solver.problem.clauses()[predecessor.clause_index];
    let head_args = match &clause.head {
        crate::ClauseHead::Predicate(_, args) => args.as_slice(),
        crate::ClauseHead::False => panic!("Q clause should have a predicate head"),
    };
    let state_on_head = solver
        .apply_to_args(q, &pob_state, head_args)
        .expect("state should apply to clause head args");
    let clause_constraint = clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));
    let guarded = solver.clause_guarded_constraint(q, predecessor.clause_index, head_args, 2);
    let base = ChcExpr::and_all([clause_constraint, state_on_head, guarded]);

    let (body_pred, body_args) = &clause.body.predicates[0];
    let frame_constraint = solver.frames[1]
        .get_predicate_constraint(*body_pred)
        .unwrap_or(ChcExpr::Bool(true));
    let frame_on_body = solver
        .apply_to_args(*body_pred, &frame_constraint, body_args)
        .expect("frame constraint should apply to body args");
    let query_for_cube =
        solver.bound_int_vars(ChcExpr::and_all([base, frame_on_body, ChcExpr::Bool(true)]));

    // After #2481 augmentation + #2918 variable-presence check, the
    // blocking path keeps the MBP cube (augmented with equalities for any
    // unconstrained canonical vars) rather than falling back to a full
    // point cube. Verify that the point-cube extractor still works as a
    // valid alternative extraction path.
    let point_cube = solver
        .cube_from_model_or_constraints(
            *body_pred,
            body_args,
            &query_for_cube,
            &predecessor.smt_model,
        )
        .expect("point-cube extraction should succeed");
    let point_vars = point_cube.vars();
    assert!(
        canonical_vars
            .iter()
            .all(|cv| point_vars.iter().any(|v| v.name == cv.name)),
        "point cube must mention all canonical vars"
    );
}

#[test]
fn block_obligation_preserves_soundness_for_mixed_sat_no_cube_and_unsat_clauses() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun A (Int Real) Bool)
(declare-fun B (Int Real) Bool)

; Fact for A.
(assert (forall ((x Int) (r Real))
  (=> (= x 0)
  (A x r))))

; Clause 1: SAT predecessor candidate for B.
(assert (forall ((x Int) (r Real) (x1 Int) (r1 Real))
  (=> (and (A x r)
       (= x1 (+ x 1))
       (= r1 r))
  (B x1 r1))))

; Clause 2: UNSAT predecessor candidate under the A fact constraint.
(assert (forall ((x Int) (r Real) (x1 Int) (r1 Real))
  (=> (and (A x r)
       (= x1 (+ x 2))
       (= r1 r))
  (B x1 r1))))

; Safety query on B.
(assert (forall ((x Int) (r Real))
  (=> (and (B x r) (= x 1))
  false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, unit_test_config());
    let b = solver.problem.get_predicate_by_name("B").unwrap().id;
    let bx = solver.canonical_vars(b).unwrap()[0].clone();
    let mut pob = ProofObligation::new(b, ChcExpr::eq(ChcExpr::var(bx), ChcExpr::int(1)), 1);

    match solver.block_obligation_with_local_blocked(&mut pob, &[], &[]) {
        // Conservative path: a SAT-no-cube predecessor was seen, so we avoid
        // creating a blocking lemma.
        BlockResult::Unknown => {
            assert!(
                solver.telemetry.sat_no_cube_events > 0,
                "expected SAT-no-cube telemetry when returning Unknown"
            );
        }
        // Also sound: cube extraction succeeded on a SAT predecessor.
        BlockResult::Reachable(_) => {}
        BlockResult::Blocked(_) => {
            panic!("mixed SAT-no-cube/UNSAT predecessor clauses must not produce Blocked")
        }
        BlockResult::AlreadyBlocked => {
            panic!("unexpected AlreadyBlocked in isolated soundness test setup")
        }
    }
}

#[test]
fn minimize_projection_model_prefers_smallest_sat_integer_candidate() {
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(1)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(5)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(5));

    let mut smt = SmtContext::new();
    let minimized = PdrSolver::minimize_projection_model_with_context(
        &mut smt,
        std::slice::from_ref(&x),
        &query,
        model,
    );

    assert_eq!(minimized.get("x"), Some(&SmtValue::Int(1)));
}

#[test]
fn minimize_projection_model_respects_positive_lower_bound() {
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(5));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(50));

    let mut smt = SmtContext::new();
    let minimized = PdrSolver::minimize_projection_model_with_context(
        &mut smt,
        std::slice::from_ref(&x),
        &query,
        model,
    );

    assert_eq!(minimized.get("x"), Some(&SmtValue::Int(5)));
}

#[test]
fn minimize_projection_model_respects_negative_upper_bound() {
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::and(
        ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(-20)),
        ChcExpr::le(ChcExpr::var(x.clone()), ChcExpr::int(-3)),
    );

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(-20));

    let mut smt = SmtContext::new();
    let minimized = PdrSolver::minimize_projection_model_with_context(
        &mut smt,
        std::slice::from_ref(&x),
        &query,
        model,
    );

    assert_eq!(minimized.get("x"), Some(&SmtValue::Int(-3)));
}

#[test]
fn minimize_projection_model_respects_equality_constraint() {
    let x = ChcVar::new("x", ChcSort::Int);
    let query = ChcExpr::eq(ChcExpr::int(42), ChcExpr::var(x.clone()));

    let mut model = FxHashMap::default();
    model.insert("x".to_string(), SmtValue::Int(100));

    let mut smt = SmtContext::new();
    let minimized = PdrSolver::minimize_projection_model_with_context(
        &mut smt,
        std::slice::from_ref(&x),
        &query,
        model,
    );

    assert_eq!(minimized.get("x"), Some(&SmtValue::Int(42)));
}

#[test]
fn minimize_projection_model_prefers_false_for_boolean_projection_var() {
    let b = ChcVar::new("b", ChcSort::Bool);
    let query = ChcExpr::not(ChcExpr::var(b.clone()));

    let mut model = FxHashMap::default();
    model.insert("b".to_string(), SmtValue::Bool(true));

    let mut smt = SmtContext::new();
    let minimized = PdrSolver::minimize_projection_model_with_context(
        &mut smt,
        std::slice::from_ref(&b),
        &query,
        model,
    );

    assert_eq!(minimized.get("b"), Some(&SmtValue::Bool(false)));
}

/// Verify that range-weakening skips variables with no init bounds (#3020).
///
/// When `init_values` lacks an entry for a variable, the old code defaulted
/// `init_max`/`init_min` to 0, potentially expanding or contracting the
/// binary search range. The fix skips range-weakening entirely for such
/// variables, preserving the original equality conjunct.
#[test]
fn generalize_preserves_equality_for_unknown_init_bounds() {
    // Inv(x, y) where fact constrains only x (y has no init bounds).
    let smt2 = r#"
(set-logic HORN)
(declare-fun Inv (Int Int) Bool)
(assert (forall ((x Int) (y Int)) (=> (= x 0) (Inv x y))))
(assert (forall ((x Int) (y Int) (x1 Int) (y1 Int))
(=> (and (Inv x y) (= x1 (+ x 1)) (= y1 y))
    (Inv x1 y1))))
(assert (forall ((x Int) (y Int)) (=> (and (Inv x y) (> x 5)) false)))
(check-sat)
"#;
    let problem = ChcParser::parse(smt2).unwrap();
    let mut config = unit_test_config();
    config.use_range_weakening = true;

    let mut solver = PdrSolver::new(problem, config);
    // Need at least 2 frames for generalization to run
    solver.frames.push(Frame::new());

    let inv = solver.problem.get_predicate_by_name("Inv").unwrap().id;
    let canon_vars = solver.canonical_vars(inv).unwrap().to_vec();

    // Verify test precondition: y (second canonical var) has no init bounds
    let init_values = solver.get_init_values(inv);
    let y_var = &canon_vars[1];
    assert!(
        !init_values.contains_key(&y_var.name),
        "test setup: y should have no init bounds (fact constrains only x)"
    );

    // Build a blocking formula with equalities for both x and y
    let x_var = &canon_vars[0];
    let state = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x_var.clone()), ChcExpr::int(3)),
        ChcExpr::eq(ChcExpr::var(y_var.clone()), ChcExpr::int(42)),
    );

    let generalized = solver.generalize_blocking_formula(&state, inv, 2);

    // The y = 42 equality should survive generalization because y has no
    // init bounds and range-weakening skips unknown-bound variables.
    // (x = 3 may or may not be weakened depending on monotonicity analysis.)
    let gen_str = format!("{generalized}");
    assert!(
        gen_str.contains("42"),
        "y = 42 should survive generalization (no init bounds → skip range-weakening), got: {gen_str}"
    );
}

#[test]
fn block_obligation_uses_cluster_min_max_generalization_for_non_init_predicate() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int)) (=> (A x) (B x))))
(assert (forall ((x Int)) (=> (and (B x) (= x 100)) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut config = unit_test_config();
    config.use_convex_closure = true;

    let mut solver = PdrSolver::new(problem, config);
    let b = solver.problem.get_predicate_by_name("B").unwrap().id;
    let x = solver.canonical_vars(b).unwrap()[0].clone();

    for value in [-1, -2] {
        let point_cube = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(value));
        solver
            .caches
            .cluster_store
            .add_blocking_cube(b, &point_cube, 1)
            .expect("cluster seed should be recorded");
    }

    let original_point = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(-3));
    let generalized = run_cluster_generalization_via_production_path(
        &mut solver,
        b,
        1,
        &original_point,
        &original_point,
    );

    assert_eq!(
        generalized,
        ChcExpr::le(ChcExpr::var(x), ChcExpr::int(-1)),
        "expected seeded equality cluster to widen B(-3) to x <= -1"
    );
}

#[test]
fn block_obligation_cluster_generalization_respects_convex_closure_gate() {
    let smt2 = r#"
(set-logic HORN)
(declare-fun A (Int) Bool)
(declare-fun B (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (A x))))
(assert (forall ((x Int)) (=> (A x) (B x))))
(assert (forall ((x Int)) (=> (and (B x) (= x 100)) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut config = unit_test_config();
    config.use_convex_closure = false;

    let mut solver = PdrSolver::new(problem, config);
    let b = solver.problem.get_predicate_by_name("B").unwrap().id;
    let x = solver.canonical_vars(b).unwrap()[0].clone();

    for value in [-1, -2] {
        let point_cube = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(value));
        solver
            .caches
            .cluster_store
            .add_blocking_cube(b, &point_cube, 1)
            .expect("cluster seed should be recorded");
    }

    let original_point = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(-3));
    let generalized = run_cluster_generalization_via_production_path(
        &mut solver,
        b,
        1,
        &original_point,
        &original_point,
    );

    assert_eq!(
        generalized, original_point,
        "test helper must follow production convex-closure gating"
    );
}

// ---- Bool-to-Int normalization / denormalization tests (#5877) ----

#[test]
fn normalize_eq_true_converts_bool_var_to_ge_int_1() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Bool(true));
    let (normalized, bool_vars) = normalize_bool_to_int(&[expr]);
    assert_eq!(normalized.len(), 1);
    assert!(bool_vars.contains("x"));
    let expected = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    assert_eq!(normalized[0], expected);
}

#[test]
fn normalize_eq_false_converts_bool_var_to_le_int_0() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Bool(false));
    let (normalized, bool_vars) = normalize_bool_to_int(&[expr]);
    assert_eq!(normalized.len(), 1);
    assert!(bool_vars.contains("x"));
    let expected = ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(0),
    );
    assert_eq!(normalized[0], expected);
}

#[test]
fn normalize_not_bool_var_converts_to_le_int_0() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let expr = ChcExpr::not(ChcExpr::var(x));
    let (normalized, bool_vars) = normalize_bool_to_int(&[expr]);
    assert_eq!(normalized.len(), 1);
    assert!(bool_vars.contains("x"));
    let expected = ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(0),
    );
    assert_eq!(normalized[0], expected);
}

#[test]
fn normalize_bare_bool_var_converts_to_ge_int_1() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let expr = ChcExpr::var(x);
    let (normalized, bool_vars) = normalize_bool_to_int(&[expr]);
    assert_eq!(normalized.len(), 1);
    assert!(bool_vars.contains("x"));
    let expected = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    assert_eq!(normalized[0], expected);
}

#[test]
fn normalize_not_eq_true_converts_to_le_int_0() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let expr = ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::Bool(true)));
    let (normalized, bool_vars) = normalize_bool_to_int(&[expr]);
    assert_eq!(normalized.len(), 1);
    assert!(bool_vars.contains("x"));
    let expected = ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(0),
    );
    assert_eq!(normalized[0], expected);
}

#[test]
fn normalize_not_eq_false_converts_to_ge_int_1() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let expr = ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::Bool(false)));
    let (normalized, bool_vars) = normalize_bool_to_int(&[expr]);
    assert_eq!(normalized.len(), 1);
    assert!(bool_vars.contains("x"));
    let expected = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    assert_eq!(normalized[0], expected);
}

#[test]
fn normalize_bool_equality_converts_both_to_int() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let y = ChcVar::new("y", ChcSort::Bool);
    let expr = ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(y));
    let (normalized, bool_vars) = normalize_bool_to_int(&[expr]);
    assert_eq!(normalized.len(), 1);
    assert!(bool_vars.contains("x"));
    assert!(bool_vars.contains("y"));
    let expected = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
    );
    assert_eq!(normalized[0], expected);
}

#[test]
fn normalize_int_expr_passes_through() {
    let x = ChcVar::new("x", ChcSort::Int);
    let expr = ChcExpr::ge(ChcExpr::var(x), ChcExpr::Int(5));
    let (normalized, bool_vars) = normalize_bool_to_int(&[expr.clone()]);
    assert_eq!(normalized.len(), 1);
    assert!(bool_vars.is_empty());
    assert_eq!(normalized[0], expr);
}

#[test]
fn denormalize_ge_1_converts_back_to_bool_var() {
    let mut bool_vars = FxHashSet::default();
    bool_vars.insert("x".to_string());
    let expr = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    let result = denormalize_int_to_bool(&expr, &bool_vars);
    assert_eq!(result, ChcExpr::var(ChcVar::new("x", ChcSort::Bool)));
}

#[test]
fn denormalize_le_0_converts_back_to_not_bool_var() {
    let mut bool_vars = FxHashSet::default();
    bool_vars.insert("x".to_string());
    let expr = ChcExpr::le(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(0),
    );
    let result = denormalize_int_to_bool(&expr, &bool_vars);
    assert_eq!(
        result,
        ChcExpr::not(ChcExpr::var(ChcVar::new("x", ChcSort::Bool)))
    );
}

#[test]
fn denormalize_eq_both_bool_restores_sort() {
    let mut bool_vars = FxHashSet::default();
    bool_vars.insert("x".to_string());
    bool_vars.insert("y".to_string());
    let expr = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
    );
    let result = denormalize_int_to_bool(&expr, &bool_vars);
    let expected = ChcExpr::eq(
        ChcExpr::var(ChcVar::new("x", ChcSort::Bool)),
        ChcExpr::var(ChcVar::new("y", ChcSort::Bool)),
    );
    assert_eq!(result, expected);
}

#[test]
fn denormalize_non_bool_int_var_passes_through() {
    let bool_vars = FxHashSet::default(); // no bool vars
    let expr = ChcExpr::ge(
        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
        ChcExpr::Int(1),
    );
    let result = denormalize_int_to_bool(&expr, &bool_vars);
    assert_eq!(result, expr);
}

#[test]
fn normalize_denormalize_roundtrip_eq_true() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let original = ChcExpr::eq(ChcExpr::var(x), ChcExpr::Bool(true));
    let (normalized, bool_vars) = normalize_bool_to_int(&[original]);
    let denormalized = denormalize_int_to_bool(&normalized[0], &bool_vars);
    // (= x true) normalizes to (>= x_int 1), denormalizes to bare x (Bool)
    // This is semantically equivalent but not structurally identical.
    assert_eq!(
        denormalized,
        ChcExpr::var(ChcVar::new("x", ChcSort::Bool)),
        "roundtrip should produce bare Bool var (semantically equivalent to (= x true))"
    );
}

#[test]
fn normalize_denormalize_roundtrip_not_var() {
    let x = ChcVar::new("x", ChcSort::Bool);
    let original = ChcExpr::not(ChcExpr::var(x));
    let (normalized, bool_vars) = normalize_bool_to_int(&[original.clone()]);
    let denormalized = denormalize_int_to_bool(&normalized[0], &bool_vars);
    assert_eq!(denormalized, original, "roundtrip should preserve (not x)");
}

#[test]
fn denormalize_recurses_into_and() {
    let mut bool_vars = FxHashSet::default();
    bool_vars.insert("x".to_string());
    bool_vars.insert("y".to_string());
    let expr = ChcExpr::and(
        ChcExpr::ge(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::Int(1),
        ),
        ChcExpr::le(
            ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
            ChcExpr::Int(0),
        ),
    );
    let result = denormalize_int_to_bool(&expr, &bool_vars);
    let expected = ChcExpr::and(
        ChcExpr::var(ChcVar::new("x", ChcSort::Bool)),
        ChcExpr::not(ChcExpr::var(ChcVar::new("y", ChcSort::Bool))),
    );
    assert_eq!(result, expected);
}
