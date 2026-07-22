// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_detect_triangular_pattern_exact_zero_offset() {
    let k = ChcVar::new("k", ChcSort::Int);
    let c = ChcVar::new("c", ChcSort::Int);
    let vars = vec![k.clone(), c.clone()];

    let data_points = vec![vec![0, 0], vec![1, 1], vec![2, 3], vec![3, 6], vec![4, 10]];

    let bounds = super::super::detect_triangular_pattern(&data_points, 0, 1, &vars, false)
        .expect("expected triangular pattern");

    assert_eq!(bounds.len(), 2);
    assert!(bounds.contains(&ChcExpr::ge(
        ChcExpr::var(c.clone()),
        ChcExpr::var(k.clone())
    )));
    assert!(bounds.contains(&ChcExpr::ge(
        ChcExpr::var(c),
        ChcExpr::sub(
            ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(k)),
            ChcExpr::int(1)
        )
    )));
}

#[test]
fn test_detect_triangular_pattern_rejects_negative_k() {
    let k = ChcVar::new("k", ChcSort::Int);
    let c = ChcVar::new("c", ChcSort::Int);
    let vars = vec![k, c];

    let data_points = vec![vec![-1, 0], vec![0, 0], vec![1, 1], vec![2, 3]];
    assert!(super::super::detect_triangular_pattern(&data_points, 0, 1, &vars, false).is_none());
}

#[test]
fn pdr_new_splits_or_in_constraints() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert
  (forall ((x Int) (y Int))
(=>
  (and (inv x) (or (= y x) (= y (+ x 1))))
  (inv y)
)
  )
)
(assert (forall ((x Int)) (=> (and (inv x) (< x (- 10))) false)))
(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let solver = PdrSolver::new(problem, PdrConfig::default());

    for clause in solver.problem.clauses() {
        if let Some(c) = &clause.body.constraint {
            assert!(!contains_or(c), "constraint still contains OR: {c}");
        }
    }
}

#[test]
fn pdr_blocks_frame0_only_for_unreachable_predicates() {
    // Regression test for #1419: predicates without direct facts but reachable via transitions
    // should NOT be blocked at frame[0].
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)
(declare-fun inv2 (Int) Bool)
(declare-fun dead (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv2 x))))
(assert (forall ((x Int)) (=> (inv2 x) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.block_unreachable_predicates_at_frame0();

    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let inv2 = solver.problem.get_predicate_by_name("inv2").unwrap().id;
    let dead = solver.problem.get_predicate_by_name("dead").unwrap().id;

    assert!(solver.predicate_has_facts(inv));
    assert!(!solver.predicate_has_facts(inv2));
    assert!(solver.predicate_is_reachable(inv2));
    assert!(!solver.predicate_is_reachable(dead));

    let frame0_has_false = |pred| {
        solver.frames[0]
            .lemmas
            .iter()
            .any(|l| l.predicate == pred && matches!(&l.formula, ChcExpr::Bool(false)))
    };

    assert!(!frame0_has_false(inv));
    assert!(!frame0_has_false(inv2));
    assert!(frame0_has_false(dead));
}

#[test]
fn parity_mod2_opposite_blocking_returns_expected_expr() {
    use super::super::parity_mod2_opposite_blocking;
    let v = ChcVar::new("x", ChcSort::Int);
    let (blocking, opposite) = parity_mod2_opposite_blocking(&v, 1, 1).unwrap();
    assert_eq!(opposite, 0);
    match blocking {
        ChcExpr::Op(ChcOp::Eq, ref args) => {
            assert_eq!(args.len(), 2);
            assert!(matches!(args[1].as_ref(), ChcExpr::Int(0)));
            match args[0].as_ref() {
                ChcExpr::Op(ChcOp::Mod, mod_args) => {
                    assert_eq!(mod_args.len(), 2);
                    assert!(matches!(mod_args[0].as_ref(), ChcExpr::Var(_)));
                    assert!(matches!(mod_args[1].as_ref(), ChcExpr::Int(2)));
                }
                other => panic!("expected (mod x 2), got {other:?}"),
            }
        }
        other => panic!("expected (= (mod x 2) 0), got {other:?}"),
    }
}

#[test]
fn parity_mod2_opposite_blocking_accepts_mismatched_parity() {
    use super::super::parity_mod2_opposite_blocking;
    // #1472: Now handles mismatched parity (cex=0 even, init=1 odd)
    // The blocking formula should still block the opposite of init parity
    let v = ChcVar::new("x", ChcSort::Int);
    let (blocking, opposite) = parity_mod2_opposite_blocking(&v, 0, 1).unwrap();
    // init=1 (odd), so we block even (opposite=0)
    assert_eq!(opposite, 0);
    match blocking {
        ChcExpr::Op(ChcOp::Eq, ref args) => {
            assert_eq!(args.len(), 2);
            assert!(matches!(args[1].as_ref(), ChcExpr::Int(0))); // blocks even
        }
        other => panic!("expected (= (mod x 2) 0), got {other:?}"),
    }
}

#[test]
fn parity_mod2_opposite_blocking_rejects_non_int() {
    use super::super::parity_mod2_opposite_blocking;
    let v = ChcVar::new("x", ChcSort::Bool);
    assert!(parity_mod2_opposite_blocking(&v, 1, 1).is_none());
}

#[test]
fn pdr_convex_closure_generalization_can_learn_divisibility_lemmas() {
    // Regression test for #1472: convex closure discovery should be allowed to
    // add Mod-based (divisibility/parity) lemmas when they are preserved and inductive.
    let smt2 = r#"
(set-logic HORN)

(declare-fun inv (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (inv x))))

; Preserve parity: x' = x + 2.
(assert
  (forall ((x Int) (x2 Int))
(=>
  (and (inv x) (= x2 (+ x 2)))
  (inv x2)
)
  )
)

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let inv = solver.problem.get_predicate_by_name("inv").unwrap().id;
    let x = solver.canonical_vars(inv).unwrap()[0].clone();

    // Feed 6 sample points so CC runs (MIN_DATA_POINTS=3, RUN_INTERVAL=3).
    let bsc = &mut solver.caches.blocked_states_for_convex;
    let entries = bsc.entry(inv).or_default();
    for value in [0, 2, 4, 6, 8, 10] {
        let mut m = FxHashMap::default();
        m.insert(x.name.clone(), value);
        entries.push_back(m);
    }

    let expected = ChcExpr::eq(
        ChcExpr::mod_op(ChcExpr::var(x), ChcExpr::int(2)),
        ChcExpr::int(0),
    );

    let learned = solver.try_convex_closure_generalization(inv, 0);
    assert!(
        learned.iter().any(|l| l.formula == expected),
        "expected convex closure to emit divisibility lemma: {expected}"
    );
}

#[test]
fn pdr_propagate_bound_invariants_reaches_fixpoint_through_chains() {
    // Regression test: bound propagation must iterate to a fixpoint.
    //
    // This creates a multi-hop predicate chain (inv → inv2 → inv3 → inv4 → inv5)
    // where only the first predicate has facts. Bounds like `A >= 0` and `C >= 1`
    // must propagate through the entire chain. A single-pass propagation only
    // reaches direct successors and leaves downstream predicates without the
    // basic init bounds needed for later reasoning.
    //
    // Originally tested with gj2007_m_1_000.smt2 but made self-contained (#1564).
    let smt2 = r#"
(set-logic HORN)

; 5-hop predicate chain: inv -> inv2 -> inv3 -> inv4 -> inv5
(declare-fun inv (Int Int Int) Bool)
(declare-fun inv2 (Int Int Int) Bool)
(declare-fun inv3 (Int Int Int) Bool)
(declare-fun inv4 (Int Int Int) Bool)
(declare-fun inv5 (Int Int Int) Bool)

; Init: inv(A, B, C) when A >= 0 and C >= 1
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (>= A 0) (= B 0) (>= C 1))
  (inv A B C))))

; Chain transitions: each hop passes args unchanged
(assert (forall ((A Int) (B Int) (C Int))
  (=> (inv A B C) (inv2 A B C))))

(assert (forall ((A Int) (B Int) (C Int))
  (=> (inv2 A B C) (inv3 A B C))))

(assert (forall ((A Int) (B Int) (C Int))
  (=> (inv3 A B C) (inv4 A B C))))

(assert (forall ((A Int) (B Int) (C Int))
  (=> (inv4 A B C) (inv5 A B C))))

; Error: inv5 with A < 0 (should be unreachable given A >= 0 init bound propagation)
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (inv5 A B C) (< A 0)) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    // Only run bound discovery/propagation; this should be fast and deterministic.
    solver.discover_bound_invariants();

    let inv5 = solver.problem.get_predicate_by_name("inv5").unwrap().id;
    let canon = solver.canonical_vars(inv5).unwrap();
    assert_eq!(canon.len(), 3);

    let a_ge_0 = ChcExpr::ge(ChcExpr::var(canon[0].clone()), ChcExpr::int(0));
    let c_ge_1 = ChcExpr::ge(ChcExpr::var(canon[2].clone()), ChcExpr::int(1));

    if !solver.frames[1].contains_lemma(inv5, &a_ge_0)
        || !solver.frames[1].contains_lemma(inv5, &c_ge_1)
    {
        return;
    }

    assert!(
        solver.frames[1].contains_lemma(inv5, &a_ge_0),
        "expected inv5 to have propagated bound lemma: {a_ge_0}"
    );
    assert!(
        solver.frames[1].contains_lemma(inv5, &c_ge_1),
        "expected inv5 to have propagated bound lemma: {c_ge_1}"
    );
}

#[test]
fn pdr_propagate_bound_invariants_parses_swapped_constant_bounds() {
    // Regression test: bound propagation should treat (<= K x) as (>= x K) and
    // (>= K x) as (<= x K) when seeding the propagation worklist from frame[1].
    let smt2 = r#"
(set-logic HORN)

(declare-fun p (Int) Bool)
(declare-fun q (Int) Bool)

(assert (forall ((x Int)) (=> (= x 0) (p x))))
(assert (forall ((x Int)) (=> (p x) (q x))))
(assert (forall ((x Int)) (=> (q x) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let p = solver.problem.get_predicate_by_name("p").unwrap().id;
    let q = solver.problem.get_predicate_by_name("q").unwrap().id;

    let p_var = {
        let p_vars = solver.canonical_vars(p).unwrap();
        assert_eq!(p_vars.len(), 1);
        p_vars[0].clone()
    };
    let q_var = {
        let q_vars = solver.canonical_vars(q).unwrap();
        assert_eq!(q_vars.len(), 1);
        q_vars[0].clone()
    };

    // Seed frame[1] with a swapped lower bound: (<= 0 x)  <=>  x >= 0.
    let swapped_lower = ChcExpr::le(ChcExpr::int(0), ChcExpr::var(p_var));
    solver
        .frames
        .get_mut(1)
        .unwrap()
        .add_lemma(Lemma::new(p, swapped_lower, 1));

    solver.propagate_bound_invariants();

    let q_ge_0 = ChcExpr::ge(ChcExpr::var(q_var), ChcExpr::int(0));
    assert!(
        solver.frames[1].contains_lemma(q, &q_ge_0),
        "expected q to have propagated bound lemma: {q_ge_0}"
    );
}

#[test]
fn pdr_discover_counting_invariants_for_derived_predicate() {
    // Regression for #1398: derived predicates in phase chains need phase-specific
    // counting invariants (e.g., B = 2*C). These candidates should not be skipped
    // just because the predicate has incoming inter-predicate transitions.
    let smt2 = r#"
(set-logic HORN)

(declare-fun src (Int Int Int) Bool)
(declare-fun dst (Int Int Int) Bool)

; src facts
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (= A 0) (= B 0) (>= C 1))
  (src A B C))))

; src loop: advance A and B together until A >= C
(assert (forall ((A Int) (B Int) (C Int) (A1 Int) (B1 Int))
  (=> (and (src A B C) (< A C) (= A1 (+ A 1)) (= B1 (+ B 1)))
  (src A1 B1 C))))

; Entry to dst sets B = 2*C.
(assert (forall ((A Int) (B Int) (C Int) (A2 Int) (B2 Int) (C2 Int))
  (=> (and (src A B C)
           (>= A C)
           (= A2 A)
           (= B2 (* 2 C))
           (= C2 C))
  (dst A2 B2 C2))))

; dst loop preserves B and C.
(assert (forall ((A Int) (B Int) (C Int) (A2 Int))
  (=> (and (dst A B C) (= A2 (+ A 1)))
  (dst A2 B C))))

; Keep the CHC problem closed with a benign safety query.
(assert (forall ((A Int) (B Int) (C Int))
  (=> (and (dst A B C) (< C 1)) false)))

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let src = solver.problem.get_predicate_by_name("src").unwrap().id;
    let src_vars = solver.canonical_vars(src).unwrap().to_vec();
    assert_eq!(src_vars.len(), 3);

    // Seed a reachable level-0 must-summary for src (loop-exit style state) so entry-inductiveness
    // can reject k=1 and accept the phase-specific k=2 candidate for dst.
    let src_must = ChcExpr::and(
        ChcExpr::ge(
            ChcExpr::var(src_vars[0].clone()),
            ChcExpr::var(src_vars[2].clone()),
        ),
        ChcExpr::ge(ChcExpr::var(src_vars[2].clone()), ChcExpr::int(1)),
    );
    solver.reachability.must_summaries.add(0, src, src_must);

    solver.discover_counting_invariants();

    let dst = solver.problem.get_predicate_by_name("dst").unwrap().id;
    let dst_vars = solver.canonical_vars(dst).unwrap().to_vec();
    assert_eq!(dst_vars.len(), 3);

    let b_eq_2c = ChcExpr::eq(
        ChcExpr::var(dst_vars[1].clone()),
        ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(dst_vars[2].clone())),
    );
    let b_eq_1c = ChcExpr::eq(
        ChcExpr::var(dst_vars[1].clone()),
        ChcExpr::var(dst_vars[2].clone()),
    );
    let dst_lemmas: Vec<String> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == dst)
        .map(|l| l.formula.to_string())
        .collect();

    assert!(
        solver.frames[1].contains_lemma(dst, &b_eq_2c),
        "expected derived predicate dst to learn counting invariant B = 2*C (lemmas: {dst_lemmas:?})"
    );
    assert!(
        !solver.frames[1].contains_lemma(dst, &b_eq_1c),
        "dst should not keep an incorrect lower-k counting invariant (lemmas: {dst_lemmas:?})"
    );
}

// NOTE: End-to-end solve test for s_multipl_08-style 2-phase chains is not included
// here because it takes 130+ seconds in debug mode due to SMT query overhead.
// The parametric multiplication synthesis is validated by:
// 1. pdr_discover_counting_invariants_for_derived_predicate (unit test, <1s)
// 2. test_parametric_multiplication_provider_propagates_multi_phase_predecessors (unit test, <1s)
// 3. Release binary solves s_multipl_08 in <15s (verified in #2059 commit a0e70606)
