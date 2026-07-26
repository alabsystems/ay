// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn try_weaken_interpolant_equalities_handles_deep_and_tree() {
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)

(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (P x)
)
  )
)

(assert
  (forall ( (x Int) )
(=>
  (and
    (P x)
    (>= x 100)
  )
  false
)
  )
)

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("parse deep-weakening fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let x = ChcVar::new("x", ChcSort::Int);
    let mut deep = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0));
    for bound in 1..=5000 {
        // Construct the pathological left spine directly. Canonical `and`
        // flattens in production; distinct atoms prevent canonical
        // deduplication when the weakening result is rebuilt.
        let atom = ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(bound));
        deep = ChcExpr::Op(
            crate::ChcOp::And,
            vec![std::sync::Arc::new(deep), std::sync::Arc::new(atom)],
        );
    }

    let bad_state = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0));
    let weakened = solver.try_weaken_interpolant_equalities(&deep, &bad_state);
    assert!(
        matches!(weakened, ChcExpr::Op(ChcOp::And, _)),
        "deep and-tree should remain an and-tree without stack overflow"
    );
}

#[test]
fn try_weaken_interpolant_equalities_weakens_shallow_equality() {
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)

(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (P x)
)
  )
)

(assert
  (forall ( (x Int) )
(=>
  (and
    (P x)
    (>= x 100)
  )
  false
)
  )
)

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("parse shallow-weakening fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let x = ChcVar::new("x", ChcSort::Int);
    let interpolant = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    let bad_state = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0));

    let weakened = solver.try_weaken_interpolant_equalities(&interpolant, &bad_state);
    assert_eq!(
        weakened,
        ChcExpr::ge(
            ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
            ChcExpr::int(0)
        )
    );
}

#[test]
fn try_weaken_interpolant_equalities_respects_depth_limit() {
    let input = r#"
(set-logic HORN)

(declare-fun |P| ( Int ) Bool)

(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (P x)
)
  )
)

(assert
  (forall ( (x Int) )
(=>
  (and
    (P x)
    (>= x 100)
  )
  false
)
  )
)

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("parse deep-depth fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let mut deep = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0));
    for _ in 0..(crate::expr::MAX_EXPR_RECURSION_DEPTH + 16) {
        let guard = ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0));
        deep = ChcExpr::Op(ChcOp::And, vec![Arc::new(guard), Arc::new(deep)]);
    }

    let bad_state = ChcExpr::lt(ChcExpr::var(x), ChcExpr::int(0));
    let weakened = solver.try_weaken_interpolant_equalities(&deep, &bad_state);
    assert_eq!(
        weakened, deep,
        "deep interpolants beyond recursion limit should remain unchanged"
    );
}
