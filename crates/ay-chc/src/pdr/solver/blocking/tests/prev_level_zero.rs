// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Level-1 obligations whose predecessor is an init state
//! (`check_prev_level_zero_predecessor`): the fact clause is conjoined with
//! the transition clause, so its locals must be renamed apart first.
//! Clause-local names are unique only within one clause, and translated
//! benchmarks reuse `A`, `B`, ... in every clause with different roles.

use super::super::super::*;

/// The fact and the transition clause both bind `a` and `b`, in swapped
/// roles. `B(1, 5)` is the image of the only init state `B(0, 5)`.
const SWAPPED_LOCAL_NAMES: &str = r#"
(set-logic HORN)
(declare-fun B (Int Int) Bool)
(assert (forall ((a Int) (b Int)) (=> (and (= a 0) (= b 5)) (B a b))))
(assert (forall ((b Int) (a Int) (c Int))
  (=> (and (B b a) (= c (+ b 1))) (B c a))))
(check-sat)
"#;

/// sally/vmt shape: the fact binds `x` as Bool, the transition binds `x` as
/// its Int head slot. One step from init (`a = 0`) gives `x = 2`.
const SAME_NAME_OTHER_SORT: &str = r#"
(set-logic HORN)
(declare-fun B (Int Bool) Bool)
(assert (forall ((y Int) (x Bool)) (=> (and (= y 0) x) (B y x))))
(assert (forall ((a Int) (p Bool) (x Int) (q Bool))
  (=> (and (B a p) (> x (+ a 1)) (< x (+ a 3)) (= q p)) (B x q))))
(check-sat)
"#;

#[test]
fn prev_level_zero_predecessor_renames_fact_locals_apart() {
    // Unrenamed, the query read the fact's `a = 0, b = 5` and the init match
    // `b = a, a = b` over ONE pair of symbols, which is UNSAT, so the solver
    // tried to block a state one transition from init (the inductiveness
    // check then refused the lemma and the obligation came back Unknown).
    let problem = ChcParser::parse(SWAPPED_LOCAL_NAMES).unwrap();
    let mut solver = PdrSolver::new(problem, super::unit_test_config());
    let b = solver.problem.get_predicate_by_name("B").unwrap().id;
    let b0 = solver.canonical_vars(b).unwrap()[0].clone();
    let mut pob = ProofObligation::new(b, ChcExpr::eq(ChcExpr::var(b0), ChcExpr::int(1)), 1);

    match solver.block_obligation_with_local_blocked(&mut pob, &[], &[]) {
        BlockResult::Reachable(pred) => assert_eq!(pred.predicate, b),
        BlockResult::Blocked(_) => {
            panic!("a state one transition from init must not be blocked at level 1")
        }
        BlockResult::AlreadyBlocked => {
            panic!("unexpected AlreadyBlocked: no lemmas were added")
        }
        BlockResult::MustReachable(_) => panic!("reach facts belong to the nonlinear lane"),
        BlockResult::Unknown => panic!(
            "expected the init predecessor, got Unknown (fact locals captured by \
             the transition clause's names)"
        ),
    }
}

#[test]
fn prev_level_zero_interpolation_keeps_fact_locals_out_of_head_slots() {
    // The level-0 predecessor check is UNSAT, so with interpolation on its
    // A-side is translated to canonical names by variable name. Unrenamed, the
    // fact's `x: Bool` was renamed onto the Int slot `__p0_a0` (debug
    // tripwire in `substitute_name_map`).
    let problem = ChcParser::parse(SAME_NAME_OTHER_SORT).unwrap();
    let mut config = super::unit_test_config();
    config.use_interpolation = true;
    let mut solver = PdrSolver::new(problem, config);
    let b = solver.problem.get_predicate_by_name("B").unwrap().id;
    let b0 = solver.canonical_vars(b).unwrap()[0].clone();
    let mut pob = ProofObligation::new(b, ChcExpr::eq(ChcExpr::var(b0), ChcExpr::int(1)), 1);

    let result = solver.block_obligation_with_local_blocked(&mut pob, &[], &[]);
    assert!(
        !matches!(result, BlockResult::Reachable(_)),
        "x = 1 is not reachable in one step: the only successor of init has x = 2"
    );
}

const GENERATED_NAME_COLLISION: &str = r#"
(set-logic HORN)
(declare-fun B (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (B x))))
(assert (forall ((a Int) (__lvl0_fact_0_x Int))
  (=> (and (B a) (= __lvl0_fact_0_x (+ a 1)) (>= __lvl0_fact_0_x 1))
      (B __lvl0_fact_0_x))))
(check-sat)
"#;

const GENERATED_NAME_OTHER_SORT: &str = r#"
(set-logic HORN)
(declare-fun B (Int Bool) Bool)
(assert (forall ((n Int) (x Bool)) (=> (and (= n 0) x) (B n x))))
(assert (forall ((a Int) (p Bool) (__lvl0_fact_0_x Int) (q Bool))
  (=> (and (B a p) (= __lvl0_fact_0_x (+ a 1)) (>= __lvl0_fact_0_x 1) (= q p))
      (B __lvl0_fact_0_x q))))
(check-sat)
"#;

fn assert_generated_name_shape(problem: &crate::ChcProblem, fact_sort: ChcSort) {
    // A sole successor equality is normalized into a functional head by the
    // parser, removing the colliding name. The extra bound keeps that binder
    // live, without changing the init-to-1 witness. Check before AND after
    // solver construction so neither preprocessing phase can erase coverage.
    assert_eq!(problem.clauses().len(), 2);
    let fact = &problem.clauses()[0];
    assert!(fact.is_fact());
    let fact_var = ChcVar::new("x", fact_sort);
    assert!(fact
        .body
        .constraint
        .as_ref()
        .unwrap()
        .vars()
        .contains(&fact_var));
    let crate::ClauseHead::Predicate(_, fact_args) = &fact.head else {
        panic!("expected fact predicate head");
    };
    assert!(fact_args.iter().any(|arg| arg.vars().contains(&fact_var)));
    let transition = &problem.clauses()[1];
    assert_eq!(transition.body.predicates.len(), 1);
    let successor = ChcVar::new("__lvl0_fact_0_x", ChcSort::Int);
    assert!(transition
        .body
        .constraint
        .as_ref()
        .unwrap()
        .vars()
        .contains(&successor));
    let crate::ClauseHead::Predicate(_, head_args) = &transition.head else {
        panic!("expected transition predicate head");
    };
    assert_eq!(head_args.first(), Some(&ChcExpr::var(successor)));
}

#[test]
fn prev_level_zero_generated_names_avoid_same_and_other_sort_binders() {
    for (source, fact_sort) in [
        (GENERATED_NAME_COLLISION, ChcSort::Int),
        (GENERATED_NAME_OTHER_SORT, ChcSort::Bool),
    ] {
        let problem = ChcParser::parse(source).unwrap();
        assert_generated_name_shape(&problem, fact_sort.clone());
        let mut solver = PdrSolver::new(problem, super::unit_test_config());
        assert_generated_name_shape(&solver.problem, fact_sort);
        let b = solver.problem.get_predicate_by_name("B").unwrap().id;
        let b0 = solver.canonical_vars(b).unwrap()[0].clone();
        let mut pob = ProofObligation::new(b, ChcExpr::eq(ChcExpr::var(b0), ChcExpr::int(1)), 1);
        match solver.check_predecessor_reachability(&mut pob, &[]) {
            Err(BlockResult::Reachable(pred)) => {
                assert_eq!(pred.predicate, b);
                assert_eq!(pred.clause_index, 1, "must use the transition/fact join");
            }
            _ => panic!("the actual init predecessor must be found, not Unknown or blocked"),
        }
    }
}

#[test]
fn prev_level_zero_query_only_capture_is_terminal_unknown() {
    // Only the fresh name differs: an unrelated query local must still reach
    // the actual transition/fact join, not return a vacuous generic Unknown.
    for (query_name, collides) in [("__lvl0_fact_0_x_2", false), ("__lvl0_fact_0_x_1", true)] {
        let problem = ChcParser::parse(GENERATED_NAME_COLLISION).unwrap();
        assert_generated_name_shape(&problem, ChcSort::Int);
        let mut solver = PdrSolver::new(problem, super::unit_test_config());
        assert_generated_name_shape(&solver.problem, ChcSort::Int);
        let b = solver.problem.get_predicate_by_name("B").unwrap().id;
        let b0 = solver.canonical_vars(b).unwrap()[0].clone();
        let state = ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(b0), ChcExpr::int(1)),
            ChcExpr::eq(
                ChcExpr::var(ChcVar::new(query_name, ChcSort::Int)),
                ChcExpr::int(0),
            ),
        );
        let mut pob = ProofObligation::new(b, state, 1);
        match solver.check_predecessor_reachability(&mut pob, &[]) {
            Err(BlockResult::Unknown) if collides => {}
            Err(BlockResult::Reachable(pred)) if !collides => {
                assert_eq!(pred.predicate, b);
                assert_eq!(pred.clause_index, 1);
            }
            _ => panic!("unexpected predecessor result for query local {query_name}"),
        }
    }
}

#[test]
fn generated_fact_name_collision_keeps_true_counterexample_checkable() {
    let source =
        GENERATED_NAME_COLLISION.replace("(check-sat)", "(assert (=> (B 1) false))\n(check-sat)");
    let problem = ChcParser::parse(&source).unwrap();
    let mut config = super::unit_test_config();
    config.preserve_original_clauses = true;
    let mut solver = PdrSolver::new(problem, config);
    let PdrResult::Unsafe(cex) = solver.solve() else {
        panic!("the original source reaches the error after one transition");
    };
    assert_eq!(
        solver.verify_counterexample(&cex),
        crate::pdr::CexVerificationResult::Valid
    );
}

#[test]
fn prev_level_zero_other_sort_generated_name_stays_out_of_interpolation_slots() {
    // The reachable other-sort query cannot tell prefix renaming from fresh
    // renaming: a Bool and an Int local of one spelling are distinct `ChcVar`s
    // there. The UNSAT interpolation A-side is translated by NAME, so the
    // prefix-renamed fact `x: Bool` (`__lvl0_fact_0_x`) was mapped onto the
    // transition's Int head slot `__p0_a0` (debug tripwire in
    // `substitute_name_map`). B(5) is not one step from init (only B(1) is).
    let problem = ChcParser::parse(GENERATED_NAME_OTHER_SORT).unwrap();
    assert_generated_name_shape(&problem, ChcSort::Bool);
    let mut config = super::unit_test_config();
    config.use_interpolation = true;
    let mut solver = PdrSolver::new(problem, config);
    assert_generated_name_shape(&solver.problem, ChcSort::Bool);
    let b = solver.problem.get_predicate_by_name("B").unwrap().id;
    let b0 = solver.canonical_vars(b).unwrap()[0].clone();
    let mut pob = ProofObligation::new(b, ChcExpr::eq(ChcExpr::var(b0), ChcExpr::int(5)), 1);
    assert!(
        matches!(
            solver.block_obligation_with_local_blocked(&mut pob, &[], &[]),
            BlockResult::Blocked(_)
        ),
        "B(5) must be blocked at level 1 through the interpolating level-zero join"
    );
}
