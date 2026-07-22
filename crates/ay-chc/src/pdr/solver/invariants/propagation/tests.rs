// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::pdr::{frame::Lemma, PdrConfig, PdrSolver};
use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
use ay_core::time::Instant;

/// Regression test for #2191: propagation should handle constant head args.
///
/// Problem structure:
/// - P(A, B) has invariant A <= B
/// - Clause: P(X, Y) /\ X >= 0 => Q(0, Y)  (constant head arg X=0)
///
/// Expected: The invariant A <= B from P should propagate to Q.
/// Since A maps to constant 0 in Q, and B maps to arg1 of Q,
/// the propagated invariant should be "0 <= arg1" which simplifies to "arg1 >= 0".
#[test]
fn test_propagation_with_constant_body_arg() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::Int]);

    let a = ChcVar::new("A", ChcSort::Int);
    let b = ChcVar::new("B", ChcSort::Int);
    let x = ChcVar::new("X", ChcSort::Int);
    let y = ChcVar::new("Y", ChcSort::Int);

    // Init: A = 0 /\ B = 0 => P(A, B)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(p, vec![ChcExpr::var(a), ChcExpr::var(b)]),
    ));

    // Transition P → Q with constant head arg:
    // P(X, Y) /\ X >= 0 => Q(0, Y)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(
            q,
            vec![
                ChcExpr::int(0), // constant head arg
                ChcExpr::var(y),
            ],
        ),
    ));

    // Query: Q(D, E) /\ E < 0 => false
    let d = ChcVar::new("D", ChcSort::Int);
    let e = ChcVar::new("E", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(d), ChcExpr::var(e.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(e), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let solver = PdrSolver::new(problem, config);

    // Run propagation and check it finds candidates
    let candidates = solver.build_propagation_candidates(p);
    assert!(
        !candidates.is_empty(),
        "should find propagation candidates from P to Q"
    );

    // Verify at least one candidate has constant head arg
    let has_constant_head = candidates.iter().any(|c| {
        solver
            .propagation_candidate_components(p, c)
            .is_some_and(|(_, head_args, _)| {
                head_args.iter().any(|arg| matches!(arg, ChcExpr::Int(_)))
            })
    });
    assert!(
        has_constant_head,
        "should have candidate with constant head arg"
    );
}

/// Regression for #1402: propagate invariants through affine head definitions.
///
/// Pattern:
/// - Source lemma on P: x = y
/// - Cross-predicate clause: P(x, y) /\ u = x + 1 /\ v = y + 1 => Q(u, v)
///
/// The propagated clause-guarded lemma for Q should rewrite the source
/// variables through the affine head equalities instead of bailing out when
/// the head arguments are clause-local vars with linear definitions.
#[test]
fn test_propagation_through_affine_head_equalities() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let u = ChcVar::new("u", ChcSort::Int);
    let v = ChcVar::new("v", ChcSort::Int);
    let bad_u = ChcVar::new("bad_u", ChcSort::Int);
    let bad_v = ChcVar::new("bad_v", ChcSort::Int);

    // Keep Q fact-free so propagated invariants land in clause-guarded storage.
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(y.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone()), ChcExpr::var(y.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(x), ChcExpr::var(y)])],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(u.clone()),
                    ChcExpr::add(
                        ChcExpr::var(ChcVar::new("x", ChcSort::Int)),
                        ChcExpr::int(1),
                    ),
                ),
                ChcExpr::eq(
                    ChcExpr::var(v.clone()),
                    ChcExpr::add(
                        ChcExpr::var(ChcVar::new("y", ChcSort::Int)),
                        ChcExpr::int(1),
                    ),
                ),
            )),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(u), ChcExpr::var(v)]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(bad_u), ChcExpr::var(bad_v)])],
            Some(ChcExpr::Bool(true)),
        ),
        ClauseHead::False,
    ));

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let p_vars = solver.canonical_vars(p).unwrap().to_vec();
    let q_vars = solver.canonical_vars(q).unwrap().to_vec();

    let source_eq = ChcExpr::eq(
        ChcExpr::var(p_vars[0].clone()),
        ChcExpr::var(p_vars[1].clone()),
    );
    solver.frames[1].add_lemma(Lemma::new(p, source_eq, 1));

    let added = solver.propagate_frame1_invariants_to_users();
    assert!(
        added >= 1,
        "expected affine P -> Q propagation to add a guarded lemma"
    );

    let q_clause_index = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, clause)| {
            clause.head.predicate_id() == Some(q)
                && clause.body.predicates.iter().any(|(pred, _)| *pred == p)
        })
        .map(|(idx, _)| idx)
        .expect("expected P -> Q clause");

    let propagated = solver
        .caches
        .clause_guarded_lemmas
        .get(&(q, q_clause_index))
        .expect("expected clause-guarded lemma for Q");

    let expected_shifted = ChcExpr::eq(
        ChcExpr::sub(ChcExpr::var(q_vars[0].clone()), ChcExpr::int(1)),
        ChcExpr::sub(ChcExpr::var(q_vars[1].clone()), ChcExpr::int(1)),
    )
    .simplify_constants();
    let expected_direct = ChcExpr::eq(
        ChcExpr::var(q_vars[0].clone()),
        ChcExpr::var(q_vars[1].clone()),
    );

    assert!(
        propagated.iter().any(|(formula, _)| {
            formula == &expected_shifted
                || formula == &expected_direct
                || formula
                    .vars()
                    .into_iter()
                    .all(|var| q_vars.iter().any(|qv| qv.name == var.name))
        }),
        "expected propagated lemma over Q vars only; got {propagated:?}"
    );
}

#[test]
fn test_transition_affine_hints_promote_source_affine_equality_to_target() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::Int]);

    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let p_a_next = ChcVar::new("p_a_next", ChcSort::Int);
    let p_b_next = ChcVar::new("p_b_next", ChcSort::Int);
    let q_u = ChcVar::new("q_u", ChcSort::Int);
    let q_v = ChcVar::new("q_v", ChcSort::Int);
    let q_u_next = ChcVar::new("q_u_next", ChcSort::Int);
    let q_v_next = ChcVar::new("q_v_next", ChcSort::Int);
    let bad_u = ChcVar::new("bad_u", ChcSort::Int);
    let bad_v = ChcVar::new("bad_v", ChcSort::Int);

    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(p, vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())]),
    ));

    // P self-loop: preserves 2*a = b.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(p_a_next.clone()),
                    ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::int(1)),
                ),
                ChcExpr::eq(
                    ChcExpr::var(p_b_next.clone()),
                    ChcExpr::add(ChcExpr::var(b.clone()), ChcExpr::int(2)),
                ),
            )),
        ),
        ClauseHead::Predicate(
            p,
            vec![
                ChcExpr::var(p_a_next.clone()),
                ChcExpr::var(p_b_next.clone()),
            ],
        ),
    ));

    // Cross-predicate transition: rewrite the same affine step into Q's namespace.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(q_u.clone()),
                    ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::int(1)),
                ),
                ChcExpr::eq(
                    ChcExpr::var(q_v.clone()),
                    ChcExpr::add(ChcExpr::var(b.clone()), ChcExpr::int(2)),
                ),
            )),
        ),
        ClauseHead::Predicate(
            q,
            vec![ChcExpr::var(q_u.clone()), ChcExpr::var(q_v.clone())],
        ),
    ));

    // Q self-loop: preserves 2*u = v once established at entry.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                q,
                vec![ChcExpr::var(q_u.clone()), ChcExpr::var(q_v.clone())],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(q_u_next.clone()),
                    ChcExpr::add(ChcExpr::var(q_u), ChcExpr::int(1)),
                ),
                ChcExpr::eq(
                    ChcExpr::var(q_v_next.clone()),
                    ChcExpr::add(ChcExpr::var(q_v), ChcExpr::int(2)),
                ),
            )),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(q_u_next), ChcExpr::var(q_v_next)]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(bad_u), ChcExpr::var(bad_v.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(bad_v), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let p_vars = solver.canonical_vars(p).unwrap().to_vec();
    let q_vars = solver.canonical_vars(q).unwrap().to_vec();
    let source_expected = solver
        .normalize_affine_equality_for_target(
            p,
            &ChcExpr::eq(
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(p_vars[0].clone())),
                ChcExpr::var(p_vars[1].clone()),
            ),
        )
        .expect("normalize source affine equality");
    solver.frames[1].add_lemma(Lemma::new(p, source_expected.clone(), 1));

    let target_expected = solver
        .normalize_affine_equality_for_target(
            q,
            &ChcExpr::eq(
                ChcExpr::mul(ChcExpr::int(2), ChcExpr::var(q_vars[0].clone())),
                ChcExpr::var(q_vars[1].clone()),
            ),
        )
        .expect("normalize target affine equality");

    let hints = solver.collect_affine_equality_propagation_hints();
    assert!(
        hints
            .iter()
            .any(|hint| hint.predicate == q && hint.formula == target_expected),
        "expected transition-derived affine hint for Q, got {hints:?}"
    );

    let added = solver.apply_affine_equality_propagation_hints();
    assert!(
        added >= 1,
        "expected at least one applied affine propagation hint"
    );
    assert!(
        solver.frames[1].contains_lemma(q, &target_expected),
        "expected target affine hint to become a frame lemma"
    );
}

#[test]
fn test_transition_affine_hints_promote_source_bound_to_target() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int, ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int, ChcSort::Int]);

    let a = ChcVar::new("a", ChcSort::Int);
    let b = ChcVar::new("b", ChcSort::Int);
    let q_u = ChcVar::new("q_u", ChcSort::Int);
    let q_v = ChcVar::new("q_v", ChcSort::Int);
    let q_u_next = ChcVar::new("q_u_next", ChcSort::Int);
    let q_v_next = ChcVar::new("q_v_next", ChcSort::Int);
    let bad_u = ChcVar::new("bad_u", ChcSort::Int);
    let bad_v = ChcVar::new("bad_v", ChcSort::Int);

    // P is initialized with a-b >= 1000.
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(a.clone()), ChcExpr::int(1000)),
            ChcExpr::eq(ChcExpr::var(b.clone()), ChcExpr::int(0)),
        )),
        ClauseHead::Predicate(p, vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())]),
    ));

    // Cross-predicate transition preserves the source difference through affine head args.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![ChcExpr::var(a.clone()), ChcExpr::var(b.clone())])],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(q_u.clone()),
                    ChcExpr::add(ChcExpr::var(a.clone()), ChcExpr::int(1)),
                ),
                ChcExpr::eq(
                    ChcExpr::var(q_v.clone()),
                    ChcExpr::add(ChcExpr::var(b.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(
            q,
            vec![ChcExpr::var(q_u.clone()), ChcExpr::var(q_v.clone())],
        ),
    ));

    // Q self-loop preserves u-v, making the propagated range fact inductive.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                q,
                vec![ChcExpr::var(q_u.clone()), ChcExpr::var(q_v.clone())],
            )],
            Some(ChcExpr::and(
                ChcExpr::eq(
                    ChcExpr::var(q_u_next.clone()),
                    ChcExpr::add(ChcExpr::var(q_u), ChcExpr::int(1)),
                ),
                ChcExpr::eq(
                    ChcExpr::var(q_v_next.clone()),
                    ChcExpr::add(ChcExpr::var(q_v), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(q_u_next), ChcExpr::var(q_v_next)]),
    ));

    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                q,
                vec![ChcExpr::var(bad_u.clone()), ChcExpr::var(bad_v.clone())],
            )],
            Some(ChcExpr::lt(
                ChcExpr::sub(ChcExpr::var(bad_u), ChcExpr::var(bad_v)),
                ChcExpr::int(1000),
            )),
        ),
        ClauseHead::False,
    ));

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    let p_vars = solver.canonical_vars(p).unwrap().to_vec();
    let q_vars = solver.canonical_vars(q).unwrap().to_vec();
    let source_bound = ChcExpr::ge(
        ChcExpr::sub(
            ChcExpr::var(p_vars[0].clone()),
            ChcExpr::var(p_vars[1].clone()),
        ),
        ChcExpr::int(1000),
    );
    solver.frames[1].add_lemma(Lemma::new(p, source_bound, 1));

    let target_expected = ChcExpr::ge(
        ChcExpr::add(
            ChcExpr::var(q_vars[0].clone()),
            ChcExpr::neg(ChcExpr::var(q_vars[1].clone())),
        ),
        ChcExpr::int(1000),
    )
    .simplify_constants();

    let hints = solver.collect_affine_equality_propagation_hints();
    assert!(
        hints
            .iter()
            .any(|hint| hint.predicate == q && hint.formula == target_expected),
        "expected transition-derived affine bound hint for Q, got {hints:?}"
    );

    let added = solver.apply_affine_equality_propagation_hints();
    assert!(
        added >= 1,
        "expected at least one applied affine bound propagation hint"
    );
    assert!(
        solver.frames[1].contains_lemma(q, &target_expected),
        "expected target affine bound hint to become a frame lemma"
    );
}

#[test]
fn benchmark_dense_candidate_index_lookup() {
    const PREDICATE_COUNT: usize = 24;
    const LOOKUP_ROUNDS: usize = 400;

    let mut problem = ChcProblem::new();
    let predicates: Vec<_> = (0..PREDICATE_COUNT)
        .map(|i| problem.declare_predicate(format!("P{i}"), vec![ChcSort::Int, ChcSort::Int]))
        .collect();

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let y_constraint = y.clone();
    let x_expr = ChcExpr::var(x);
    let y_expr = ChcExpr::var(y);

    // Dense transition graph: every predicate flows to every other predicate.
    for &source in &predicates {
        for &target in &predicates {
            if source == target {
                continue;
            }
            problem.add_clause(HornClause::new(
                ClauseBody::new(vec![(source, vec![x_expr.clone(), y_expr.clone()])], None),
                ClauseHead::Predicate(target, vec![x_expr.clone(), y_expr.clone()]),
            ));
        }
    }
    // Ensure at least one query exists in the generated problem.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(
                *predicates.last().expect("non-empty predicates"),
                vec![x_expr, y_expr],
            )],
            Some(ChcExpr::lt(ChcExpr::var(y_constraint), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let solver = PdrSolver::new(problem, PdrConfig::default());

    let start_scan = Instant::now();
    let mut scan_total = 0usize;
    for _ in 0..LOOKUP_ROUNDS {
        for &source in &predicates {
            scan_total += solver.build_propagation_candidates(source).len();
        }
    }
    let scan_elapsed = start_scan.elapsed();

    let candidate_index = solver.build_propagation_candidate_index();
    let start_index = Instant::now();
    let mut index_total = 0usize;
    for _ in 0..LOOKUP_ROUNDS {
        for &source in &predicates {
            index_total += candidate_index.get(&source).map_or(0, Vec::len);
        }
    }
    let index_elapsed = start_index.elapsed();

    assert_eq!(
        scan_total, index_total,
        "indexed lookup and scan path must produce identical candidate counts"
    );

    let speedup = if index_elapsed.is_zero() {
        f64::INFINITY
    } else {
        scan_elapsed.as_secs_f64() / index_elapsed.as_secs_f64()
    };
    eprintln!(
        "#2429 dense candidate lookup timing: scan={scan_elapsed:?}, indexed={index_elapsed:?}, speedup={speedup:.2}x"
    );
}

/// Regression test for #2560: when an existing propagated lemma's max_level is
/// bumped, transitive clause-guarded copies must also be bumped.
///
/// Scenario:
/// - Initial propagation at frame[1]: P -> Q -> R stores max_level=1 for Q and R.
/// - Later P is re-propagated at a higher level (simulating push to higher frame).
/// - Q's existing copy gets level-bumped. R must also be bumped transitively.
#[test]
fn test_transitive_clause_guarded_max_level_bump_propagates_to_downstream_users() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let r = problem.declare_predicate("R", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // P(x) => Q(x)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(x.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x)]),
    ));
    // Q(y) => R(y)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![ChcExpr::var(y.clone())])], None),
        ClauseHead::Predicate(r, vec![ChcExpr::var(y)]),
    ));

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    // Seed frame[1] with a source lemma for P in canonical namespace.
    let p_var = solver
        .canonical_vars(p)
        .expect("P should have canonical vars")[0]
        .clone();
    let source_formula = ChcExpr::ge(ChcExpr::var(p_var), ChcExpr::int(0));
    solver.frames[1].add_lemma(Lemma::new(p, source_formula.clone(), 1));

    // Initial startup propagation runs at target_level=1.
    let initial_added = solver.propagate_frame1_invariants_to_users();
    assert!(
        initial_added >= 2,
        "expected P->Q and Q->R propagated lemmas"
    );

    let q_clause_index = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, clause)| {
            clause.head.predicate_id() == Some(q)
                && clause.body.predicates.iter().any(|(pred, _)| *pred == p)
        })
        .map(|(i, _)| i)
        .expect("expected clause P -> Q");
    let r_clause_index = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, clause)| {
            clause.head.predicate_id() == Some(r)
                && clause.body.predicates.iter().any(|(pred, _)| *pred == q)
        })
        .map(|(i, _)| i)
        .expect("expected clause Q -> R");

    let cgl = &solver.caches.clause_guarded_lemmas;
    let q_levels_before: Vec<usize> = cgl
        .get(&(q, q_clause_index))
        .expect("expected clause-guarded lemma for Q")
        .iter()
        .map(|(_, level)| *level)
        .collect();
    let r_levels_before: Vec<usize> = cgl
        .get(&(r, r_clause_index))
        .expect("expected clause-guarded lemma for R")
        .iter()
        .map(|(_, level)| *level)
        .collect();
    assert!(
        q_levels_before.iter().all(|&level| level == 1),
        "Q lemmas should start at level 1, got {q_levels_before:?}"
    );
    assert!(
        r_levels_before.iter().all(|&level| level == 1),
        "R lemmas should start at level 1, got {r_levels_before:?}"
    );

    // Make frame 3 available so propagate_lemma_to_users(level=2) uses target_level=3.
    while solver.frames.len() < 4 {
        solver.frames.push(crate::pdr::frame::Frame::new());
    }

    // Re-propagate source at a higher level. Existing Q lemma is level-bumped.
    // #2560 fix: Q must be re-enqueued so downstream R also gets level-bumped.
    let bumped_added = solver.propagate_lemma_to_users(p, &source_formula, 2);
    assert_eq!(
        bumped_added, 0,
        "re-propagation should level-bump existing lemmas, not create new formulas"
    );

    let cgl = &solver.caches.clause_guarded_lemmas;
    let q_levels_after: Vec<usize> = cgl
        .get(&(q, q_clause_index))
        .expect("expected clause-guarded lemma for Q after bump")
        .iter()
        .map(|(_, level)| *level)
        .collect();
    let r_levels_after: Vec<usize> = cgl
        .get(&(r, r_clause_index))
        .expect("expected clause-guarded lemma for R after bump")
        .iter()
        .map(|(_, level)| *level)
        .collect();

    assert!(
        q_levels_after.iter().all(|&level| level == 3),
        "Q lemmas should be bumped to level 3, got {q_levels_after:?}"
    );
    assert!(
        r_levels_after.iter().all(|&level| level == 3),
        "R lemmas should be bumped transitively to level 3, got {r_levels_after:?}"
    );
}

/// Fixture-backed regression for #2560.
///
/// Uses an embedded CHC benchmark (`tests/embedded/issue_2560_transitive_chain_000.smt2`)
/// with a transitive user chain P -> Q -> R.
/// The test verifies the same level-bump path as the unit fixture:
/// 1) startup propagation stores Q/R clause-guarded copies at level 1,
/// 2) re-propagating P at a higher level bumps Q to level 3,
/// 3) downstream R is also bumped to level 3 transitively.
#[test]
fn test_transitive_clause_guarded_max_level_bump_on_embedded_benchmark() {
    let input = include_str!(concat!(
        env!("CARGO_MANIFEST_DIR"),
        "/tests/embedded/issue_2560_transitive_chain_000.smt2"
    ));
    let problem = crate::ChcParser::parse(input).expect("parse issue_2560_transitive_chain_000");

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    let p = solver
        .problem
        .lookup_predicate("P")
        .expect("missing P predicate in fixture");
    let q = solver
        .problem
        .lookup_predicate("Q")
        .expect("missing Q predicate in fixture");
    let r = solver
        .problem
        .lookup_predicate("R")
        .expect("missing R predicate in fixture");

    let p_var = solver
        .canonical_vars(p)
        .expect("P should have canonical vars")[0]
        .clone();
    let source_formula = ChcExpr::ge(ChcExpr::var(p_var), ChcExpr::int(0));
    solver.frames[1].add_lemma(Lemma::new(p, source_formula.clone(), 1));

    let initial_added = solver.propagate_frame1_invariants_to_users();
    assert!(
        initial_added >= 2,
        "expected at least P->Q and Q->R propagated lemmas"
    );

    let q_clause_index = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, clause)| {
            clause.head.predicate_id() == Some(q)
                && clause.body.predicates.iter().any(|(pred, _)| *pred == p)
        })
        .map(|(i, _)| i)
        .expect("expected P -> Q clause in fixture");
    let r_clause_index = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, clause)| {
            clause.head.predicate_id() == Some(r)
                && clause.body.predicates.iter().any(|(pred, _)| *pred == q)
        })
        .map(|(i, _)| i)
        .expect("expected Q -> R clause in fixture");

    let cgl = &solver.caches.clause_guarded_lemmas;
    let q_levels_before: Vec<usize> = cgl
        .get(&(q, q_clause_index))
        .expect("expected clause-guarded lemma for Q")
        .iter()
        .map(|(_, level)| *level)
        .collect();
    let r_levels_before: Vec<usize> = cgl
        .get(&(r, r_clause_index))
        .expect("expected clause-guarded lemma for R")
        .iter()
        .map(|(_, level)| *level)
        .collect();
    assert!(
        q_levels_before.iter().all(|&level| level == 1),
        "Q lemmas should start at level 1, got {q_levels_before:?}"
    );
    assert!(
        r_levels_before.iter().all(|&level| level == 1),
        "R lemmas should start at level 1, got {r_levels_before:?}"
    );

    while solver.frames.len() < 4 {
        solver.frames.push(crate::pdr::frame::Frame::new());
    }

    let bumped_added = solver.propagate_lemma_to_users(p, &source_formula, 2);
    assert_eq!(
        bumped_added, 0,
        "re-propagation should bump existing max levels, not add new formulas"
    );

    let cgl = &solver.caches.clause_guarded_lemmas;
    let q_levels_after: Vec<usize> = cgl
        .get(&(q, q_clause_index))
        .expect("expected clause-guarded lemma for Q after bump")
        .iter()
        .map(|(_, level)| *level)
        .collect();
    let r_levels_after: Vec<usize> = cgl
        .get(&(r, r_clause_index))
        .expect("expected clause-guarded lemma for R after bump")
        .iter()
        .map(|(_, level)| *level)
        .collect();

    assert!(
        q_levels_after.iter().all(|&level| level == 3),
        "Q lemmas should be bumped to level 3, got {q_levels_after:?}"
    );
    assert!(
        r_levels_after.iter().all(|&level| level == 3),
        "R lemmas should be bumped transitively to level 3, got {r_levels_after:?}"
    );
}

/// Regression test for #2807: clause-guarded propagation stores lemmas indexed
/// by (target_pred, clause_index) and `clause_guarded_constraint` returns them
/// only when queried with the matching clause_index.
///
/// Verifies:
/// 1. Propagated lemma appears under the correct clause index.
/// 2. A different clause index for the same predicate returns no constraint.
/// 3. The translated lemma only contains target-namespace variables.
#[test]
fn test_clause_guarded_constraint_scoped_to_source_clause() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Init: x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));

    // Clause 1 (transition P → Q): P(y) => Q(y)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(y.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));

    // Clause 2 (self-loop on Q): Q(y) /\ y < 100 => Q(y)
    // This clause should NOT receive clause-guarded lemmas from P→Q.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y.clone()), ChcExpr::int(100))),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));

    // Query: Q(y) /\ y < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    // Seed frame[1] with a source lemma for P.
    let p_var = solver
        .canonical_vars(p)
        .expect("P should have canonical vars")[0]
        .clone();
    let source_formula = ChcExpr::ge(ChcExpr::var(p_var), ChcExpr::int(0));
    solver.frames[1].add_lemma(Lemma::new(p, source_formula, 1));

    // Run propagation.
    let added = solver.propagate_frame1_invariants_to_users();
    assert!(added >= 1, "expected at least one propagated lemma P→Q");

    // Find the clause index for the P→Q transition.
    let p_to_q_clause = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, c)| {
            c.head.predicate_id() == Some(q) && c.body.predicates.iter().any(|(bp, _)| *bp == p)
        })
        .map(|(i, _)| i)
        .expect("expected P→Q clause");

    // Find the clause index for Q's self-loop.
    let q_self_loop_clause = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, c)| {
            c.head.predicate_id() == Some(q) && c.body.predicates.iter().any(|(bp, _)| *bp == q)
        })
        .map(|(i, _)| i)
        .expect("expected Q self-loop clause");

    let q_var = solver
        .canonical_vars(q)
        .expect("Q should have canonical vars")[0]
        .clone();
    let q_head_args = vec![ChcExpr::var(q_var)];

    // 1. Clause-guarded constraint for P→Q clause should be non-trivial.
    let guarded_p_to_q = solver.clause_guarded_constraint(q, p_to_q_clause, &q_head_args, 1);
    assert_ne!(
        guarded_p_to_q,
        ChcExpr::Bool(true),
        "P→Q clause should have a non-trivial clause-guarded constraint for Q"
    );

    // 2. Self-loop clause should NOT have clause-guarded constraints from P→Q.
    let guarded_self_loop =
        solver.clause_guarded_constraint(q, q_self_loop_clause, &q_head_args, 1);
    assert_eq!(
        guarded_self_loop,
        ChcExpr::Bool(true),
        "Q self-loop clause should NOT have clause-guarded constraints from P→Q"
    );

    // 3. Verify all clause-guarded lemmas for Q use only Q's canonical variables.
    let q_vars = solver
        .canonical_vars(q)
        .expect("Q should have canonical vars");
    for ((pred, _clause_idx), lemmas) in &solver.caches.clause_guarded_lemmas {
        if *pred != q {
            continue;
        }
        for (formula, _level) in lemmas {
            for v in formula.vars() {
                assert!(
                    q_vars.iter().any(|qv| qv.name == v.name),
                    "clause-guarded lemma {} for Q contains variable {} \
                     outside Q's canonical namespace {:?}",
                    formula,
                    v.name,
                    q_vars.iter().map(|v| &v.name).collect::<Vec<_>>()
                );
            }
        }
    }
}

/// Regression test for #2807: init-valid propagated lemma correctly enters
/// both clause-guarded store and frames, with proper variable namespace.
///
/// Verifies that when a propagated lemma is init-valid for the target
/// predicate, it is stored in both locations and all variables in the stored
/// lemma belong to the target's canonical namespace.
#[test]
fn test_init_valid_propagated_lemma_enters_both_stores() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Init: x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x.clone())]),
    ));

    // P(y) => Q(y)  (identity transfer)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(y.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));

    // Init: x = 0 => Q(x)  (Q also inits at 0)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(q, vec![ChcExpr::var(x)]),
    ));

    // Q self-loop that preserves q >= 0: Q(y) /\ y >= 0 => Q(y + 1)
    let y_plus_1 = ChcExpr::add(ChcExpr::var(y.clone()), ChcExpr::int(1));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::ge(ChcExpr::var(y.clone()), ChcExpr::int(0))),
        ),
        ClauseHead::Predicate(q, vec![y_plus_1]),
    ));

    // Query: Q(y) /\ y < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    // Seed P with invariant "x >= 0" — init-valid and self-inductive for Q
    // (Q inits at 0, and Q's self-loop only fires when y >= 0).
    let p_var = solver
        .canonical_vars(p)
        .expect("P should have canonical vars")[0]
        .clone();
    let source_formula = ChcExpr::ge(ChcExpr::var(p_var), ChcExpr::int(0));
    solver.frames[1].add_lemma(Lemma::new(p, source_formula, 1));

    let added = solver.propagate_frame1_invariants_to_users();
    assert!(added >= 1, "expected at least one propagated lemma P→Q");

    // Verify clause-guarded store has the lemma.
    let p_to_q_clause = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, c)| {
            c.head.predicate_id() == Some(q) && c.body.predicates.iter().any(|(bp, _)| *bp == p)
        })
        .map(|(i, _)| i)
        .expect("expected P→Q clause");

    let q_var = solver
        .canonical_vars(q)
        .expect("Q should have canonical vars")[0]
        .clone();
    let q_head_args = vec![ChcExpr::var(q_var)];

    let guarded = solver.clause_guarded_constraint(q, p_to_q_clause, &q_head_args, 1);
    assert_ne!(
        guarded,
        ChcExpr::Bool(true),
        "clause-guarded store should contain the propagated lemma"
    );

    // Verify frame also has the lemma (init-valid propagated lemma enters frames).
    let q_frame_lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == q)
        .collect();
    assert!(
        !q_frame_lemmas.is_empty(),
        "init-valid propagated lemma should also be in Q's frame"
    );

    // Verify all lemmas for Q in frames use only Q's canonical variables.
    let q_vars = solver
        .canonical_vars(q)
        .expect("Q should have canonical vars");
    for lemma in &q_frame_lemmas {
        for v in lemma.formula.vars() {
            assert!(
                q_vars.iter().any(|qv| qv.name == v.name),
                "frame lemma {} for Q contains variable {} outside Q's namespace",
                lemma.formula,
                v.name,
            );
        }
    }
}

/// Regression for #1402: predicates connected by a reversible var-to-var
/// mapping should receive regular discovered-invariant propagation, not just a
/// clause-guarded copy on the direct user edge.
#[test]
fn test_shared_variable_pattern_promotes_related_predicate_invariant() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);
    let z = ChcVar::new("z", ChcSort::Int);
    let q_next = ChcVar::new("q_next", ChcSort::Int);

    // Init: x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));

    // Identity transport in both directions establishes a shared predicate pattern.
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(y.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(q, vec![ChcExpr::var(z.clone())])], None),
        ClauseHead::Predicate(p, vec![ChcExpr::var(z.clone())]),
    ));

    // Q self-loop preserves x >= 0 once learned.
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(z.clone())])],
            Some(ChcExpr::and(
                ChcExpr::ge(ChcExpr::var(z.clone()), ChcExpr::int(0)),
                ChcExpr::eq(
                    ChcExpr::var(q_next.clone()),
                    ChcExpr::add(ChcExpr::var(z.clone()), ChcExpr::int(1)),
                ),
            )),
        ),
        ClauseHead::Predicate(q, vec![ChcExpr::var(q_next)]),
    ));

    // Query: Q(x) /\ x < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(z.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(z), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let mut solver = PdrSolver::new(problem, PdrConfig::default());
    assert!(
        !solver.predicate_has_facts(q),
        "Q should stay fact-free in this regression"
    );

    let p_var = solver
        .canonical_vars(p)
        .expect("P should have canonical vars")[0]
        .clone();
    let q_var = solver
        .canonical_vars(q)
        .expect("Q should have canonical vars")[0]
        .clone();

    let p_ge_0 = ChcExpr::ge(ChcExpr::var(p_var), ChcExpr::int(0));
    let q_ge_0 = ChcExpr::ge(ChcExpr::var(q_var), ChcExpr::int(0));
    solver.frames[1].add_lemma(Lemma::new(p, p_ge_0, 1));

    let added = solver.propagate_frame1_invariants_to_users();
    assert!(
        added >= 2,
        "expected clause-guarded transport plus related-predicate propagation"
    );
    assert!(
        solver.frames[1].contains_lemma(q, &q_ge_0),
        "reversible shared-variable pattern should promote Q >= 0 into frame[1]"
    );
}

/// Regression test for #1398: propagated lemmas for predicates without direct
/// fact clauses must stay clause-scoped and must not be promoted into frames.
#[test]
fn test_no_fact_target_keeps_propagated_lemma_clause_scoped() {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    let q = problem.declare_predicate("Q", vec![ChcSort::Int]);

    let x = ChcVar::new("x", ChcSort::Int);
    let y = ChcVar::new("y", ChcSort::Int);

    // Init: x = 0 => P(x)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
    ));

    // Transition-only target: P(y) => Q(y)
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![ChcExpr::var(y.clone())])], None),
        ClauseHead::Predicate(q, vec![ChcExpr::var(y.clone())]),
    ));

    // Query: Q(y) /\ y < 0 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(q, vec![ChcExpr::var(y.clone())])],
            Some(ChcExpr::lt(ChcExpr::var(y), ChcExpr::int(0))),
        ),
        ClauseHead::False,
    ));

    let config = PdrConfig {
        verbose: false,
        ..PdrConfig::default()
    };
    let mut solver = PdrSolver::new(problem, config);

    assert!(
        solver.predicate_has_facts(p),
        "P should have a direct fact clause"
    );
    assert!(
        !solver.predicate_has_facts(q),
        "Q should be transition-only in this regression fixture"
    );

    let p_var = solver
        .canonical_vars(p)
        .expect("P should have canonical vars")[0]
        .clone();
    solver.frames[1].add_lemma(Lemma::new(
        p,
        ChcExpr::ge(ChcExpr::var(p_var), ChcExpr::int(0)),
        1,
    ));

    let added = solver.propagate_frame1_invariants_to_users();
    assert!(added >= 1, "expected at least one propagated lemma P→Q");

    let p_to_q_clause = solver
        .problem
        .clauses()
        .iter()
        .enumerate()
        .find(|(_, c)| {
            c.head.predicate_id() == Some(q) && c.body.predicates.iter().any(|(bp, _)| *bp == p)
        })
        .map(|(i, _)| i)
        .expect("expected P→Q clause");

    let q_var = solver
        .canonical_vars(q)
        .expect("Q should have canonical vars")[0]
        .clone();
    let q_head_args = vec![ChcExpr::var(q_var)];

    let guarded = solver.clause_guarded_constraint(q, p_to_q_clause, &q_head_args, 1);
    assert_ne!(
        guarded,
        ChcExpr::Bool(true),
        "transition-only target should keep the propagated lemma in clause-guarded storage"
    );

    let q_frame_lemmas: Vec<_> = solver.frames[1]
        .lemmas
        .iter()
        .filter(|l| l.predicate == q)
        .collect();
    assert!(
        q_frame_lemmas.is_empty(),
        "transition-only target should not receive propagated lemmas in its frame"
    );
}
