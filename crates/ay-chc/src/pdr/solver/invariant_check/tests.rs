// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::unwrap_used)]
use super::*;
use crate::pdr::model::{InvariantModel, PredicateInterpretation};
use crate::pdr::PdrConfig;
use crate::{ChcExpr, ChcParser, ChcSort, ChcVar};

fn int_var(name: &str) -> ChcVar {
    ChcVar::new(name, ChcSort::Int)
}

fn var(name: &str) -> ChcExpr {
    ChcExpr::var(int_var(name))
}

#[test]
fn is_discovered_invariant_relational_le() {
    let formula = ChcExpr::le(var("a"), var("b"));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_relational_ge() {
    let formula = ChcExpr::ge(var("a"), var("b"));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_relational_lt() {
    let formula = ChcExpr::lt(var("a"), var("b"));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_relational_gt() {
    let formula = ChcExpr::gt(var("a"), var("b"));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_bound_var_ge_const() {
    let formula = ChcExpr::ge(var("a"), ChcExpr::int(0));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_bound_const_le_var() {
    let formula = ChcExpr::le(ChcExpr::int(0), var("a"));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_bound_var_le_const() {
    let formula = ChcExpr::le(var("x"), ChcExpr::int(128));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_bound_gt_negative() {
    let formula = ChcExpr::gt(var("x"), ChcExpr::int(-5));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_parity_mod_eq() {
    let mod_expr = ChcExpr::mod_op(var("a"), ChcExpr::int(2));
    let formula = ChcExpr::eq(mod_expr, ChcExpr::int(0));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_parity_eq_mod_reversed() {
    let mod_expr = ChcExpr::mod_op(var("a"), ChcExpr::int(3));
    let formula = ChcExpr::eq(ChcExpr::int(1), mod_expr);
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_sum_eq_var() {
    let sum = ChcExpr::add(var("a"), var("b"));
    let formula = ChcExpr::eq(sum, var("c"));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_var_eq_sum() {
    let sum = ChcExpr::add(var("a"), var("b"));
    let formula = ChcExpr::eq(var("c"), sum);
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_triple_sum_eq_var() {
    let sum_ab = ChcExpr::add(var("a"), var("b"));
    let sum_abc = ChcExpr::add(sum_ab, var("c"));
    let formula = ChcExpr::eq(sum_abc, var("d"));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_rejects_bool_true() {
    assert!(!PdrSolver::is_discovered_invariant(&ChcExpr::Bool(true)));
}

#[test]
fn is_discovered_invariant_rejects_bool_false() {
    assert!(!PdrSolver::is_discovered_invariant(&ChcExpr::Bool(false)));
}

#[test]
fn is_discovered_invariant_rejects_negation() {
    let inner = ChcExpr::le(var("a"), var("b"));
    let formula = ChcExpr::not(inner);
    assert!(!PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_rejects_conjunction() {
    let a_ge_0 = ChcExpr::ge(var("a"), ChcExpr::int(0));
    let b_ge_0 = ChcExpr::ge(var("b"), ChcExpr::int(0));
    let formula = ChcExpr::and(a_ge_0, b_ge_0);
    assert!(!PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_accepts_eq_two_vars() {
    let formula = ChcExpr::eq(var("a"), var("b"));
    assert!(PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_rejects_eq_two_consts() {
    let formula = ChcExpr::eq(ChcExpr::int(1), ChcExpr::int(2));
    assert!(!PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_rejects_le_two_consts() {
    let formula = ChcExpr::le(ChcExpr::int(1), ChcExpr::int(2));
    assert!(!PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_rejects_sum_eq_const() {
    let sum = ChcExpr::add(var("a"), var("b"));
    let formula = ChcExpr::eq(sum, ChcExpr::int(5));
    assert!(!PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn is_discovered_invariant_rejects_var_eq_const() {
    let formula = ChcExpr::eq(var("a"), ChcExpr::int(5));
    assert!(!PdrSolver::is_discovered_invariant(&formula));
}

#[test]
fn inductive_subset_rejects_init_invalid_single_predicate_lemma() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)

(assert
  (forall ((x Int))
    (=>
      (= x 1)
      (inv x))))

(assert
  (forall ((x Int) (xp Int))
    (=>
      (and (inv x) (= xp (+ x 1)))
      (inv xp))))

(assert
  (forall ((x Int))
    (=>
      (and (inv x) (< x 1))
      false)))

(check-sat)
"#,
    )
    .expect("safe increment benchmark should parse");

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .get_predicate_by_name("inv")
        .expect("predicate should exist")
        .id;
    let x = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")[0]
        .clone();

    // x >= 2 is self-inductive for x' = x + 1 and blocks the error x < 1,
    // but it is false at the initial state x = 1 and must not be accepted
    // by the inductive-subset fast path.
    solver.frames[1].add_lemma(Lemma::new(
        pred,
        ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(2)),
        1,
    ));

    let queries: Vec<_> = solver
        .problem
        .clauses()
        .iter()
        .filter(|c| c.is_query())
        .cloned()
        .collect();
    let frame_model = solver.build_model_from_frame(1);

    match solver.try_inductive_subset_model(&queries, frame_model) {
        super::safety_proof_inductive::InductiveSubsetOutcome::Proven(model) => {
            assert!(
                solver.verify_model(&model),
                "inductive-subset must not accept an init-invalid model"
            );
        }
        super::safety_proof_inductive::InductiveSubsetOutcome::Cascade(_)
        | super::safety_proof_inductive::InductiveSubsetOutcome::Insufficient => {}
    }
}

fn simple_model_for_first_predicate(solver: &PdrSolver) -> InvariantModel {
    let pred = solver.problem.predicates()[0].id;
    let vars = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")
        .to_vec();
    let mut model = InvariantModel::new();
    model.set(
        pred,
        PredicateInterpretation::new(vars, ChcExpr::Bool(true)),
    );
    model
}

#[test]
fn reverify_non_strict_single_predicate_bv_inductive_subset_candidate_issue_7964() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)

(assert
  (forall ((x (_ BitVec 8)))
    (=>
      (= x #x00)
      (inv x))))

(assert
  (forall ((x (_ BitVec 8)))
    (=>
      (and (inv x) (= x #xff))
      false)))

(check-sat)
"#,
    )
    .expect("single-predicate BV benchmark should parse");

    let solver = PdrSolver::new(problem, PdrConfig::default());
    let model = simple_model_for_first_predicate(&solver);

    assert!(
        solver.must_reverify_bv_single_predicate_inductive_subset_candidate(&model),
        "native-BV single-predicate non-strict candidates must go through the verification cascade"
    );
}

#[test]
fn single_predicate_bv_non_strict_inductive_subset_routes_to_cascade_issue_7964() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)

(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=>
      (and (= x #x00) (= y #x00))
      (inv x y))))

(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (xp (_ BitVec 8)) (yp (_ BitVec 8)))
    (=>
      (and (inv x y)
           (= xp (bvadd x y))
           (= yp y))
      (inv xp yp))))

(assert
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=>
      (and (inv x y) (= x #x01))
      false)))

(check-sat)
"#,
    )
    .expect("single-predicate BV benchmark should parse");

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .get_predicate_by_name("inv")
        .expect("predicate should exist")
        .id;
    let vars = solver
        .canonical_vars(pred)
        .expect("predicate should have canonical vars")
        .to_vec();
    let x = vars[0].clone();
    let y = vars[1].clone();

    // Frame[1] contains one algebraically verified lemma that by itself does
    // not block the query, plus a non-strict inductive lemma that needs the
    // algebraic context. A third non-inductive lemma forces the path through
    // the inductive-subset branch instead of the all-inductive branch.
    solver.frames[1].add_lemma(
        Lemma::new(
            pred,
            ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::BitVec(0, 8)),
            1,
        )
        .with_algebraically_verified(true),
    );
    solver.frames[1].add_lemma(Lemma::new(
        pred,
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::BitVec(0, 8)),
        1,
    ));
    solver.frames[1].add_lemma(Lemma::new(
        pred,
        ChcExpr::eq(ChcExpr::var(x), ChcExpr::BitVec(1, 8)),
        1,
    ));

    let queries: Vec<_> = solver
        .problem
        .clauses()
        .iter()
        .filter(|c| c.is_query())
        .cloned()
        .collect();
    let frame_model = solver.build_model_from_frame(1);

    match solver.try_inductive_subset_model(&queries, frame_model) {
        super::safety_proof_inductive::InductiveSubsetOutcome::Cascade(_) => {}
        super::safety_proof_inductive::InductiveSubsetOutcome::Proven(model) => {
            panic!(
                "non-strict single-predicate BV inductive subset must not be exposed as Proven, got {:?}",
                model
            );
        }
        super::safety_proof_inductive::InductiveSubsetOutcome::Insufficient => {
            panic!("single-predicate BV inductive subset should still return a model for cascade")
        }
    }
}

#[test]
fn reverify_non_strict_bitblasted_single_predicate_bv_candidate_issue_7964() {
    let problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv (Bool Bool Bool) Bool)

(assert
  (forall ((a0 Bool) (a1 Bool) (c Bool))
    (=>
      (and (= a0 false) (= a1 false) (= c true))
      (inv a0 a1 c))))

(assert
  (forall ((a0 Bool) (a1 Bool) (c Bool))
    (=>
      (and (inv a0 a1 c) (= a0 false) (= a1 false) (= c true))
      false)))

(check-sat)
"#,
    )
    .expect("bit-blasted single-predicate benchmark should parse");

    let config = PdrConfig {
        bv_bit_groups: vec![(0, 2)],
        ..PdrConfig::default()
    };
    let solver = PdrSolver::new(problem, config);
    let model = simple_model_for_first_predicate(&solver);

    // #7964: BvToBool-expanded problems have has_bv_sorts()=false, so
    // must_reverify only triggers for native BV. BvToBool transitions are
    // fully expanded to Boolean logic, making frame-relative self-inductive
    // models reliable.
    assert!(
        !solver.must_reverify_bv_single_predicate_inductive_subset_candidate(&model),
        "BvToBool-expanded single-predicate candidates should NOT force cascade (#7964)"
    );
}

#[test]
fn keep_direct_accept_for_strict_or_non_bv_candidates_issue_7964() {
    let bv_problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)

(assert
  (forall ((x (_ BitVec 8)))
    (=>
      (= x #x00)
      (inv x))))

(assert
  (forall ((x (_ BitVec 8)))
    (=>
      (and (inv x) (= x #xff))
      false)))

(check-sat)
"#,
    )
    .expect("single-predicate BV benchmark should parse");
    let bv_solver = PdrSolver::new(bv_problem, PdrConfig::default());
    let mut strict_model = simple_model_for_first_predicate(&bv_solver);
    strict_model.individually_inductive = true;
    assert!(
        !bv_solver.must_reverify_bv_single_predicate_inductive_subset_candidate(&strict_model),
        "strictly-inductive BV candidates can still use the direct-accept path"
    );

    let int_problem = ChcParser::parse(
        r#"
(set-logic HORN)
(declare-fun inv (Int) Bool)

(assert
  (forall ((x Int))
    (=>
      (= x 0)
      (inv x))))

(assert
  (forall ((x Int))
    (=>
      (and (inv x) (= x 1))
      false)))

(check-sat)
"#,
    )
    .expect("single-predicate Int benchmark should parse");
    let int_solver = PdrSolver::new(int_problem, PdrConfig::default());
    let int_model = simple_model_for_first_predicate(&int_solver);
    assert!(
        !int_solver.must_reverify_bv_single_predicate_inductive_subset_candidate(&int_model),
        "non-BV candidates should keep the existing direct-accept behavior"
    );
}

#[test]
fn safety_proof_routes_bv_inductive_subset_candidates_through_cascade_issue_7964() {
    let src = include_str!("safety_proof.rs");
    let branch_start = src
        .find("InductiveSubsetOutcome::Proven(m) => {")
        .expect("safety_proof.rs should handle inductive-subset Proven results");
    let branch = &src[branch_start..];
    let branch_end = branch
        .find("InductiveSubsetOutcome::Insufficient => {")
        .unwrap_or(branch.len());
    let proven_branch = &branch[..branch_end];

    assert!(
        proven_branch
            .contains("self.must_reverify_bv_single_predicate_inductive_subset_candidate(&m)"),
        "BV single-predicate inductive-subset candidates must be gated by the reverify helper"
    );
    assert!(
        proven_branch.contains("return self.try_model_verification_cascade(m);"),
        "BV single-predicate inductive-subset candidates must route through the verification cascade"
    );
}
