// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn sample_divisibility_discovery_rejects_non_inductive_mod_invariant() {
    // Regression for #2437: sample-based modular discovery must not bypass
    // parity-preservation checks on +1 transitions.
    let input = r#"
(set-logic HORN)

(declare-fun |Inv| ( Int ) Bool)

(assert
  (forall ( (x Int) )
(=>
  (= x 2)
  (Inv x)
)
  )
)

(assert
  (forall ( (x Int) (x_next Int) )
(=>
  (and (Inv x) (= x_next (+ x 1)))
  (Inv x_next)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse parity regression fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "Inv")
        .expect("missing Inv")
        .id;
    let int_vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for Inv")
        .to_vec();
    assert_eq!(int_vars.len(), 1, "expected one integer argument");

    // These samples imply x mod 4 = 2, but x' = x + 1 does not preserve it.
    let var_name = int_vars[0].name.clone();
    let mut m1 = FxHashMap::default();
    m1.insert(var_name.clone(), 2);
    let mut m2 = FxHashMap::default();
    m2.insert(var_name, 6);
    let models = vec![m1, m2];

    solver.discover_divisibility_invariants_from_samples(pred, &int_vars, &models);

    let mod4_eq_2 = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(int_vars[0].clone()), ChcExpr::int(4)),
        ChcExpr::int(2),
    );
    assert!(
        !solver.frames[1].contains_lemma(pred, &mod4_eq_2),
        "non-inductive x mod 4 = 2 must not be inserted for x' = x + 1"
    );
}

#[test]
fn sample_divisibility_discovery_accepts_inductive_mod_invariant() {
    // Positive counterpart to the rejection test above (#2520).
    // x starts at 0, x' = x + 2 preserves x mod 2 = 0.
    // Samples {0, 4} should discover x mod 2 = 0 and insert it.
    let input = r#"
(set-logic HORN)

(declare-fun |Inv| ( Int ) Bool)

(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (Inv x)
)
  )
)

(assert
  (forall ( (x Int) (x_next Int) )
(=>
  (and (Inv x) (= x_next (+ x 2)))
  (Inv x_next)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse parity fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "Inv")
        .expect("missing Inv")
        .id;
    let int_vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for Inv")
        .to_vec();
    assert_eq!(int_vars.len(), 1, "expected one integer argument");

    // Samples: all even numbers — consistent with x mod 2 = 0
    let var_name = int_vars[0].name.clone();
    let mut m1 = FxHashMap::default();
    m1.insert(var_name.clone(), 0);
    let mut m2 = FxHashMap::default();
    m2.insert(var_name, 4);
    let models = vec![m1, m2];

    solver.discover_divisibility_invariants_from_samples(pred, &int_vars, &models);

    let mod2_eq_0 = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(int_vars[0].clone()), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    assert!(
        solver.frames[1].contains_lemma(pred, &mod2_eq_0),
        "inductive x mod 2 = 0 must be inserted for x' = x + 2"
    );
}

fn make_filter_fixture_solver() -> PdrSolver {
    let input = r#"
(set-logic HORN)

(declare-fun |Inv| ( Int ) Bool)

(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (Inv x)
)
  )
)

(check-sat)
(exit)
"#;
    let problem = ChcParser::parse(input).expect("parse filter fixture");
    PdrSolver::new(problem, PdrConfig::default())
}

#[test]
fn filter_f1_for_affine_check_keeps_supported_shapes_only() {
    let solver = make_filter_fixture_solver();
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    let f1 = ChcExpr::and(
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
            ChcExpr::ge(ChcExpr::var(x.clone()), ChcExpr::int(0)),
        ),
        ChcExpr::and(
            ChcExpr::eq(
                ChcExpr::mod_op(ChcExpr::var(x.clone()), ChcExpr::int(2)),
                ChcExpr::int(0),
            ),
            ChcExpr::and(
                ChcExpr::or(
                    ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(1)),
                ),
                ChcExpr::not(ChcExpr::eq(ChcExpr::var(x), ChcExpr::var(y))),
            ),
        ),
    );

    let filtered = solver
        .filter_f1_for_affine_check(&f1)
        .expect("expected at least one relevant conjunct");
    let conjuncts = filtered.collect_conjuncts();

    assert_eq!(conjuncts.len(), 3, "expected eq/bound/not-eq only");
    assert!(conjuncts.iter().all(|c| !c.contains_mod()));
    assert!(conjuncts
        .iter()
        .all(|c| !matches!(c, ChcExpr::Op(ChcOp::Or, _))));
    assert!(
        conjuncts
            .iter()
            .any(|c| matches!(c, ChcExpr::Op(ChcOp::Eq, _))),
        "expected an equality conjunct"
    );
    assert!(
        conjuncts
            .iter()
            .any(|c| matches!(c, ChcExpr::Op(ChcOp::Ge, _))),
        "expected a bound conjunct"
    );
    assert!(
        conjuncts.iter().any(|c| matches!(
            c,
            ChcExpr::Op(ChcOp::Not, args)
                if args.len() == 1 && matches!(args[0].as_ref(), ChcExpr::Op(ChcOp::Eq, _))
        )),
        "expected negated-equality conjunct to be kept"
    );
}

#[test]
fn filter_f1_for_affine_check_caps_context_to_ten() {
    let solver = make_filter_fixture_solver();
    let x = ChcVar::new("x", ChcSort::Int);
    let f1 = (0..12)
        .map(|i| ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(i)))
        .reduce(ChcExpr::and)
        .expect("non-empty conjunct set");

    let filtered = solver
        .filter_f1_for_affine_check(&f1)
        .expect("expected filtered context");
    let conjuncts = filtered.collect_conjuncts();

    assert_eq!(
        conjuncts.len(),
        10,
        "filter must cap affine-check context at 10 lemmas"
    );
}

#[test]
fn sample_divisibility_discovery_falls_back_to_single_var_patterns() {
    // x preserves evenness, y toggles parity; x+y does not have fixed parity.
    // Discovery should still learn x mod 2 = 0 from single-variable patterns.
    let input = r#"
(set-logic HORN)

(declare-fun |Inv| ( Int Int ) Bool)

(assert
  (forall ( (x Int) (y Int) )
(=>
  (and (= x 0) (= y 0))
  (Inv x y)
)
  )
)

(assert
  (forall ( (x Int) (y Int) (x_next Int) (y_next Int) )
(=>
  (and (Inv x y) (= x_next (+ x 2)) (= y_next (+ y 1)))
  (Inv x_next y_next)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse two-var parity fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "Inv")
        .expect("missing Inv")
        .id;
    let int_vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for Inv")
        .to_vec();
    assert_eq!(int_vars.len(), 2, "expected two integer arguments");

    let x_name = int_vars[0].name.clone();
    let y_name = int_vars[1].name.clone();
    let mut m1 = FxHashMap::default();
    m1.insert(x_name.clone(), 0);
    m1.insert(y_name.clone(), 0);
    let mut m2 = FxHashMap::default();
    m2.insert(x_name, 4);
    m2.insert(y_name, 1);
    let models = vec![m1, m2];

    solver.discover_divisibility_invariants_from_samples(pred, &int_vars, &models);

    let x_mod2_eq_0 = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(int_vars[0].clone()), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    let y_mod2_eq_0 = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(int_vars[1].clone()), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    assert!(
        solver.frames[1].contains_lemma(pred, &x_mod2_eq_0),
        "x mod 2 = 0 should be learned even when no stable pair-sum pattern exists"
    );
    assert!(
        !solver.frames[1].contains_lemma(pred, &y_mod2_eq_0),
        "y mod 2 = 0 should not be learned when y parity is mixed"
    );
}

#[test]
fn sample_divisibility_discovery_filters_redundant_modulus_constraints() {
    // Samples imply both x mod 2 = 0 and x mod 4 = 0, but mod 4 is redundant.
    let input = r#"
(set-logic HORN)

(declare-fun |Inv| ( Int ) Bool)

(assert
  (forall ( (x Int) )
(=>
  (= x 0)
  (Inv x)
)
  )
)

(assert
  (forall ( (x Int) (x_next Int) )
(=>
  (and (Inv x) (= x_next (+ x 4)))
  (Inv x_next)
)
  )
)

(check-sat)
(exit)
"#;

    let problem = ChcParser::parse(input).expect("parse redundant-mod fixture");
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver
        .problem
        .predicates()
        .iter()
        .find(|p| p.name == "Inv")
        .expect("missing Inv")
        .id;
    let int_vars = solver
        .canonical_vars(pred)
        .expect("canonical vars for Inv")
        .to_vec();
    assert_eq!(int_vars.len(), 1, "expected one integer argument");

    let var_name = int_vars[0].name.clone();
    let mut m1 = FxHashMap::default();
    m1.insert(var_name.clone(), 0);
    let mut m2 = FxHashMap::default();
    m2.insert(var_name, 4);
    let models = vec![m1, m2];

    solver.discover_divisibility_invariants_from_samples(pred, &int_vars, &models);

    let mod2_eq_0 = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(int_vars[0].clone()), ChcExpr::int(2)),
        ChcExpr::int(0),
    );
    let mod4_eq_0 = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(int_vars[0].clone()), ChcExpr::int(4)),
        ChcExpr::int(0),
    );

    assert!(
        solver.frames[1].contains_lemma(pred, &mod2_eq_0),
        "expected base mod-2 invariant to be inserted"
    );
    assert!(
        !solver.frames[1].contains_lemma(pred, &mod4_eq_0),
        "redundant mod-4 invariant should be filtered out"
    );
}
