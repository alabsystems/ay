// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn pdr_entry_value_fallback_uses_relaxed_context_after_unknown_full_check() {
    let problem = ChcParser::parse(SIMPLE_ENTRY_TIMEOUT_SMT2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let src = solver.problem.lookup_predicate("SRC").unwrap();
    let dst = solver.problem.lookup_predicate("DST").unwrap();
    let entry_clause = solver
        .problem
        .clauses_defining(dst)
        .find(|c| c.body.predicates.len() == 1 && c.body.predicates[0].0 == src)
        .cloned()
        .expect("expected SRC->DST transition");
    let edge_constraint = entry_clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));

    // Add a huge unsafe (ITE-heavy) source lemma so full context SAT check
    // deterministically returns Unknown; relaxed context drops it.
    let x = ChcVar::new("x", ChcSort::Int);
    let huge_unsafe = make_exponential_unsafe_ite(&x, 21);
    solver.frames[1].add_lemma(Lemma::new(src, huge_unsafe.clone(), 1));

    // Sanity check this setup really drives Unknown on the full context.
    let full_constraint = ChcExpr::and(huge_unsafe, edge_constraint);
    solver.smt.reset();
    let full_result = solver
        .smt
        .check_sat_with_timeout(&full_constraint, std::time::Duration::from_millis(100));
    assert!(
        matches!(full_result, SmtResult::Unknown),
        "expected full entry context to return Unknown for this test setup, got {full_result:?}"
    );

    let entry_values = solver.compute_entry_values_from_transition(&entry_clause, src, dst);
    let dst_var = solver.canonical_vars(dst).unwrap()[0].clone();
    let dst_bounds = entry_values
        .get(&dst_var.name)
        .expect("expected relaxed fallback to infer DST entry value");

    assert_eq!(
        (dst_bounds.min, dst_bounds.max),
        (7, 7),
        "expected relaxed fallback to preserve y=7 entry inference after full-context Unknown"
    );
}

#[test]
fn pdr_entry_value_repeated_unknown_degrades_to_no_inference() {
    let problem = ChcParser::parse(SIMPLE_ENTRY_TIMEOUT_SMT2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let src = solver.problem.lookup_predicate("SRC").unwrap();
    let dst = solver.problem.lookup_predicate("DST").unwrap();
    let entry_clause = solver
        .problem
        .clauses_defining(dst)
        .find(|c| c.body.predicates.len() == 1 && c.body.predicates[0].0 == src)
        .cloned()
        .expect("expected SRC->DST transition");
    // Add a huge safe (non-ITE) lemma so the full and relaxed contexts are
    // realistic, then FORCE every SAT check to Unknown. The previous version
    // relied on a wall-clock race (a 2^21-node repeated conjunction under a
    // 100ms timeout), but the shared-subtree formula is genuinely satisfiable
    // and a fast enough check_sat can legitimately DECIDE it within budget,
    // making the test flaky. Forcing Unknown pins the intent deterministically:
    // when both the full and relaxed checks return Unknown, inference must be
    // skipped conservatively. The forced queue survives `smt.reset()` (see
    // `SmtContext::reset`), covering the reset inside each inference check:
    // full + relaxed per call, two calls.
    let x = ChcVar::new("x", ChcSort::Int);
    let huge_safe = make_exponential_conjunction(&x, 21);
    solver.frames[1].add_lemma(Lemma::new(src, huge_safe, 1));
    for _ in 0..4 {
        solver
            .smt
            .push_forced_check_sat_result_for_tests(SmtResult::Unknown);
    }

    let first = solver.compute_entry_values_from_transition(&entry_clause, src, dst);
    let second = solver.compute_entry_values_from_transition(&entry_clause, src, dst);

    assert!(
        first.is_empty(),
        "expected no entry-value inference when full/relaxed checks are Unknown (first run), got {first:?}"
    );
    assert!(
        second.is_empty(),
        "expected repeated Unknown checks to continue yielding no inference, got {second:?}"
    );
}

#[test]
fn pdr_discovers_equality_invariants_from_fact_constants() {
    let smt2 = r#"
(set-logic HORN)

(declare-fun P ( Int Int ) Bool)

(assert
  (forall ( (x Int) (y Int) )
(=>
  (and (= x 0) (= y 0))
  (P x y)
)
  )
)

(check-sat)
"#;

    let problem = ChcParser::parse(smt2).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    solver.discover_equality_invariants();

    let p = solver.problem.lookup_predicate("P").unwrap();
    let vars = solver.canonical_vars(p).unwrap();
    assert_eq!(vars.len(), 2);

    let expected = ChcExpr::eq(ChcExpr::var(vars[0].clone()), ChcExpr::var(vars[1].clone()));

    if !solver.frames[1].contains_lemma(p, &expected) {
        let mut p_lemmas: Vec<String> = solver.frames[1]
            .lemmas
            .iter()
            .filter(|l| l.predicate == p)
            .map(|l| l.formula.to_string())
            .collect();
        p_lemmas.sort();

        eprintln!("optional equality invariant not discovered: {expected}; P lemmas: {p_lemmas:?}");
        return;
    }
}

// Tests for is_point_cube_for_vars with union-find grounding (#755)

#[test]
fn test_is_point_cube_var_eq_constant_is_grounded() {
    // x = 5 should ground x
    let x = ChcVar::new("x", ChcSort::Int);
    let cube = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(5));
    assert!(cube::is_point_cube_for_vars(&cube, &[x]));
}

#[test]
fn test_is_point_cube_var_eq_var_not_grounded() {
    // x = y without any constant does NOT ground either
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let cube = ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone()));
    // Neither x nor y is grounded to a constant
    assert!(!cube::is_point_cube_for_vars(
        &cube,
        std::slice::from_ref(&x)
    ));
    assert!(!cube::is_point_cube_for_vars(
        &cube,
        std::slice::from_ref(&y)
    ));
    assert!(!cube::is_point_cube_for_vars(&cube, &[x, y]));
}

#[test]
fn test_is_point_cube_transitive_grounding() {
    // x = y AND y = 5 should ground both x and y through transitivity
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let cube = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(5)),
    );
    assert!(cube::is_point_cube_for_vars(
        &cube,
        std::slice::from_ref(&x)
    ));
    assert!(cube::is_point_cube_for_vars(
        &cube,
        std::slice::from_ref(&y)
    ));
    assert!(cube::is_point_cube_for_vars(&cube, &[x, y]));
}

#[test]
fn test_is_point_cube_chain_grounding() {
    // x = y AND y = z AND z = 10 should ground all three
    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    let cube = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::var(z.clone())),
            ChcExpr::eq(ChcExpr::var(z.clone()), ChcExpr::int(10)),
        ),
    );
    assert!(cube::is_point_cube_for_vars(
        &cube,
        &[x.clone(), y.clone(), z.clone()]
    ));

    // Without the z = 10, none are grounded
    let cube_no_const = ChcExpr::and(
        ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::var(y.clone())),
        ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::var(z.clone())),
    );
    assert!(!cube::is_point_cube_for_vars(&cube_no_const, &[x, y, z]));
}

#[test]
fn test_safety_path_point_blocking_accepts_relative_induction() {
    let input = r#"
(set-logic HORN)
(declare-rel Inv (Int))
(declare-var x Int)

(rule (=> (= x 0) (Inv x)))
(rule (=> (Inv x) (Inv (+ x 1))))
(query (and (Inv x) (= x (- 1))))
"#;

    let problem = ChcParser::parse(input).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());

    let pred = solver.problem.lookup_predicate("Inv").unwrap();
    let x = solver.canonical_vars(pred).unwrap()[0].clone();
    let point = ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(-1));

    // The lemma ¬(x = -1) is not self-inductive due to unreachable predecessors (x = -2).
    assert!(!solver.is_self_inductive_blocking(&point, pred));
    // But it is inductive relative to level 1 (init facts).
    assert!(solver.is_inductive_blocking(&point, pred, 1));

    // Safety-path point blocking should accept relative induction (#831).
    assert!(solver.is_safety_path_point_blocking_acceptable(&point, pred, 1));
}

#[test]
fn test_n1_per_clause_interpolation_translates_to_canonical_vars() {
    let input = r#"
(set-logic HORN)
(declare-rel Inv (Int))
(declare-var x Int)

(rule (=> (= x 0) (Inv x)))
(query (and (Inv x) (= x 1)))
"#;

    let problem = ChcParser::parse(input).unwrap();
    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let pred = solver.problem.lookup_predicate("Inv").unwrap();
    let canon = solver.canonical_vars(pred).unwrap()[0].clone();

    let bad_state = ChcExpr::ge(ChcExpr::var(canon.clone()), ChcExpr::int(1));
    let local_arg = ChcVar::new("A", ChcSort::Int);
    let clause_constraint = ChcExpr::le(ChcExpr::var(local_arg.clone()), ChcExpr::int(0));
    let clause_data = vec![(vec![ChcExpr::var(local_arg.clone())], clause_constraint)];

    let interpolant = solver
        .try_n1_per_clause_interpolation(&clause_data, &bad_state, pred)
        .expect("expected per-clause interpolant")
        .expr;
    let names: Vec<String> = interpolant.vars().into_iter().map(|v| v.name).collect();
    assert!(
        names.iter().all(|n| n == &canon.name),
        "expected only canonical vars; got {names:?} in {interpolant}"
    );
    assert!(
        !names.iter().any(|n| n == &local_arg.name),
        "unexpected local var in interpolant: {interpolant}"
    );

    let combined = ChcExpr::and(interpolant, bad_state);
    let mut smt = SmtContext::new();
    match smt.check_sat(&combined) {
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_) => {}
        SmtResult::Sat(model) => panic!("expected UNSAT, got SAT model {model:?}"),
        SmtResult::Unknown => panic!("expected UNSAT, got Unknown"),
    }
}
