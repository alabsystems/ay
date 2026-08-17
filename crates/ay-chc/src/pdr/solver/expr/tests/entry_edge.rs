// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Tests for sample_entry_edge_models (#2079)

use super::*;

#[test]
fn sample_entry_edge_models_basic_two_predicate_chain() {
    // Test basic entry-edge sampling with a P -> Q transition.
    // P is initialized, Q is derived from P.
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)
(declare-fun |Q| ( Int ) Bool)

; Fact: x = 0 => P(x)
(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (P x)
)
  )
)

; Trans: P(x) /\ x < 10 => Q(x)
(assert
  (forall ( (x Int) )
(=>
  (and (P x) (< x 10))
  (Q x)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse two-pred chain fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_p = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;
    let pred_q = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "Q")
        .expect("missing Q")
        .id;

    // sample_entry_edge_models uses frame constraints for body predicates, not fact clauses.
    // Constrain P to x = 0 to get a deterministic entry-edge sample.
    let p_vars = solver
        .canonical_vars(pred_p)
        .expect("canonical vars for P")
        .to_vec();
    let formula = ChcExpr::eq(ChcExpr::var(p_vars[0].clone()), ChcExpr::int(0));
    let lemma = Lemma::new(pred_p, formula, 1);
    solver.add_lemma(lemma, 1);

    // Sample from entry edges (P -> Q transitions)
    let models = solver.sample_entry_edge_models(pred_q, 1, 3);

    // Q(x) where x satisfies P(x) /\ x < 10, so Q's arg is 0 (from x=0)
    assert!(
        !models.is_empty(),
        "expected at least one entry-edge sample for Q"
    );

    let canon_vars = solver
        .canonical_vars(pred_q)
        .expect("canonical vars for Q")
        .to_vec();
    let x_name = &canon_vars[0].name;

    // The entry edge maps x -> x where x=0, so Q's var should be 0.
    assert!(
        models.iter().any(|m| m.get(x_name).copied() == Some(0)),
        "expected entry-edge sample with canonical var = 0, got {models:?}"
    );
}

#[test]
fn sample_entry_edge_models_with_constant_head_args() {
    // Test entry-edge sampling when head has constant arguments.
    // Q(C, 0, C) pattern where C is a head variable.
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)
(declare-fun |Q| ( Int Int Int ) Bool)

; Fact: x = 5 => P(x)
(assert
  (forall ( (x Int) )
(=>
  (= x 5)
  (P x)
)
  )
)

; Trans: P(x) => Q(x, 0, x)
; Head has constant 0 in middle position
(assert
  (forall ( (x Int) )
(=>
  (P x)
  (Q x 0 x)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse constant head args fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_p = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;
    let pred_q = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "Q")
        .expect("missing Q")
        .id;

    // Constrain P to x = 5 via a frame lemma to get deterministic entry-edge samples.
    // Note: sample_entry_edge_models does not directly use fact clauses.
    let p_vars = solver
        .canonical_vars(pred_p)
        .expect("canonical vars for P")
        .to_vec();
    let formula = ChcExpr::eq(ChcExpr::var(p_vars[0].clone()), ChcExpr::int(5));
    let lemma = Lemma::new(pred_p, formula, 1);
    solver.add_lemma(lemma, 1);

    let models = solver.sample_entry_edge_models(pred_q, 1, 3);

    assert!(
        !models.is_empty(),
        "expected at least one entry-edge sample for Q with constant head args"
    );

    let canon_vars = solver
        .canonical_vars(pred_q)
        .expect("canonical vars for Q")
        .to_vec();

    // Check that the constant argument (position 1, value 0) is captured
    let var1_name = &canon_vars[1].name;
    assert!(
        models.iter().any(|m| m.get(var1_name).copied() == Some(0)),
        "expected constant head arg (0) to be captured in sample, got {models:?}"
    );

    // First and third args should both be 5 (from P(x) where x=5)
    let var0_name = &canon_vars[0].name;
    let var2_name = &canon_vars[2].name;
    assert!(
        models
            .iter()
            .any(|m| m.get(var0_name).copied() == Some(5) && m.get(var2_name).copied() == Some(5)),
        "expected first and third args to be 5, got {models:?}"
    );
}

#[test]
fn sample_entry_edge_models_with_expr_head_args() {
    // Test entry-edge sampling when head args are expressions (not just variables/constants).
    // This exercises the `canon_i = head_arg_i` binding used to extract canonical values.
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)
(declare-fun |Q| ( Int ) Bool)

; Fact: x = 5 => P(x)
(assert
  (forall ( (x Int) )
(=>
  (= x 5)
  (P x)
)
  )
)

; Trans: P(x) => Q(x + 1)
(assert
  (forall ( (x Int) )
(=>
  (P x)
  (Q (+ x 1))
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse expr head args fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_q = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "Q")
        .expect("missing Q")
        .id;

    let models = solver.sample_entry_edge_models(pred_q, 1, 3);
    assert!(
        !models.is_empty(),
        "expected at least one entry-edge sample for Q with expr head args"
    );

    let canon_vars = solver
        .canonical_vars(pred_q)
        .expect("canonical vars for Q")
        .to_vec();
    let x_name = &canon_vars[0].name;

    assert!(
        models.iter().any(|m| m.get(x_name).copied() == Some(6)),
        "expected entry-edge sample Q(x) to have x=6 from Q(x+1) with x=5, got {models:?}"
    );
}

#[test]
fn sample_entry_edge_models_recurses_through_derived_predicates() {
    // Test entry-edge sampling through a derived predicate chain:
    // P (facts) -> Q (derived) -> R (derived).
    //
    // Without recursive entry-edge sampling, sampling for R can degenerate to unconstrained
    // SMT guesses because Q has no facts and no must-summaries initially.
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)
(declare-fun |Q| ( Int ) Bool)
(declare-fun |R| ( Int ) Bool)

; Fact: x = 5 => P(x)
(assert
  (forall ( (x Int) )
(=>
  (= x 5)
  (P x)
)
  )
)

; P(x) => Q(x + 1)  (so reachable Q is 6)
(assert
  (forall ( (x Int) )
(=>
  (P x)
  (Q (+ x 1))
)
  )
)

; Q(y) => R(y + 1)  (so reachable R is 7)
(assert
  (forall ( (y Int) )
(=>
  (Q y)
  (R (+ y 1))
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse derived chain fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_r = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "R")
        .expect("missing R")
        .id;

    let models = solver.sample_entry_edge_models(pred_r, 1, 3);
    assert!(
        !models.is_empty(),
        "expected at least one entry-edge sample for R via derived chain"
    );

    let canon_vars = solver
        .canonical_vars(pred_r)
        .expect("canonical vars for R")
        .to_vec();
    let x_name = &canon_vars[0].name;

    assert!(
        models.iter().any(|m| m.get(x_name).copied() == Some(7)),
        "expected entry-edge sample R(x) to have x=7 from chain P(5)->Q(6)->R(7), got {models:?}"
    );
}

#[test]
fn sample_entry_edge_models_uses_body_forward_simulation_for_guarded_entry() {
    // Test that entry-edge sampling can reach guarded entry conditions by forward-simulating
    // the body predicate, even when the body already has must-summary samples.
    //
    // Shape:
    //   P(x, y) facts: x >= 0, y = x
    //   P self-loop: x > 0 => P(x-1, y)   (y preserved, x decrements to 0)
    //   Entry edge: P(0, y) => Q(y)
    //
    // Reachable entry states into Q include y > 0 (e.g., start at x=y=1, step to x=0,y=1).
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int Int ) Bool)
(declare-fun |Q| ( Int ) Bool)

; Facts: y = x, x >= 0
(assert
  (forall ( (x Int) (y Int) )
(=>
  (and (>= x 0) (= y x))
  (P x y)
)
  )
)

; Self-loop: while x > 0, decrement x (preserve y)
(assert
  (forall ( (x Int) (y Int) (x2 Int) (y2 Int) )
(=>
  (and
    (P x y)
    (and (not (<= x 0)) (= x2 (+ (- 1) x)) (= y2 y))
  )
  (P x2 y2)
)
  )
)

; Entry into Q at x = 0
(assert
  (forall ( (x Int) (y Int) )
(=>
  (and (P x y) (= x 0))
  (Q y)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse guarded-entry fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_p = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;
    let pred_q = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "Q")
        .expect("missing Q")
        .id;

    // Sanity-check sampling for the body predicate: we should be able to sample x=y=1 from
    // facts, and forward-simulate to reach x=0,y=1.
    let p_vars = solver
        .canonical_vars(pred_p)
        .expect("canonical vars for P")
        .to_vec();
    let p_x = &p_vars[0].name;
    let p_y = &p_vars[1].name;
    let p_fact_count = solver
        .problem
        .facts()
        .filter(|f| f.head.predicate_id() == Some(pred_p))
        .count();
    let init_models = solver.sample_init_models(pred_p, 5);
    assert!(
        init_models.iter().any(|m| m.get(p_x).copied() == Some(1) && m.get(p_y).copied() == Some(1)),
        "expected init samples for P to include x=y=1; facts_for_P={p_fact_count}, got {init_models:?}"
    );
    let forward = solver.simulate_forward_samples_from_init_samples(pred_p, &init_models, 5);
    assert!(
        forward
            .iter()
            .any(|m| m.get(p_x).copied() == Some(0) && m.get(p_y).copied() == Some(1)),
        "expected forward simulation to include P(x=0,y=1), got {forward:?}"
    );

    let models = solver.sample_entry_edge_models(pred_q, 1, 5);
    assert!(
        !models.is_empty(),
        "expected at least one entry-edge sample for Q via forward simulation"
    );

    let canon_vars = solver
        .canonical_vars(pred_q)
        .expect("canonical vars for Q")
        .to_vec();
    let x_name = &canon_vars[0].name;

    assert!(
        models.iter().any(|m| m.get(x_name).copied() == Some(1)),
        "expected entry-edge sample Q(x) to include x=1 reachable via P(1,1)->P(0,1), got {models:?}"
    );
}

mod boundary_conditions;
