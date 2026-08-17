// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Entry-edge sampling boundary-condition regressions.

use super::*;

#[test]
fn sample_entry_edge_models_empty_when_no_incoming_transitions() {
    // Test that sample_entry_edge_models returns empty when predicate has no
    // incoming inter-predicate transitions (only fact clauses).
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)

; Fact only - no incoming transitions from other predicates
(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (P x)
)
  )
)

; Self-loop only
(assert
  (forall ( (x Int) )
(=>
  (and (P x) (< x 10))
  (P (+ x 1))
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse no incoming transitions fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred_p = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "P")
        .expect("missing P")
        .id;

    // P has only fact clauses and self-loops, no incoming inter-pred transitions
    let models = solver.sample_entry_edge_models(pred_p, 0, 3);

    assert!(
        models.is_empty(),
        "expected empty result for predicate with no incoming transitions, got {models:?}"
    );
}

#[test]
fn sample_entry_edge_models_uses_frame_constraints() {
    // Test that frame constraints from body predicates are applied.
    // P(x) at level 1 has constraint x >= 0, Q derived from P should respect this.
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

; Trans: P(x) => Q(x)
(assert
  (forall ( (x Int) )
(=>
  (P x)
  (Q x)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse frame constraints fixture");
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

    // Add a frame constraint for P: x >= 0
    let p_vars = solver.canonical_vars(pred_p).expect("vars for P").to_vec();
    let formula = ChcExpr::ge(ChcExpr::var(p_vars[0].clone()), ChcExpr::int(0));
    let lemma = Lemma::new(pred_p, formula, 1);
    solver.add_lemma(lemma, 1);

    // Sample entry edges for Q at level 1
    let models = solver.sample_entry_edge_models(pred_q, 1, 5);

    // All samples should have x >= 0 due to frame constraint on P
    let q_vars = solver.canonical_vars(pred_q).expect("vars for Q").to_vec();
    let x_name = &q_vars[0].name;

    for model in &models {
        if let Some(&val) = model.get(x_name) {
            assert!(
                val >= 0,
                "expected all samples to satisfy frame constraint x >= 0, got x = {val}"
            );
        }
    }
}
