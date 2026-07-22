#![allow(clippy::unwrap_used)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

mod ite_split_tests {
    use super::*;

    #[test]
    fn split_boolean_ite_in_transition_constraint() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

        let a = ChcVar::new("A", ChcSort::Int);
        let b = ChcVar::new("B", ChcSort::Int);
        let c = ChcVar::new("C", ChcSort::Int);
        let d = ChcVar::new("D", ChcSort::Int);

        // inv(A,B) /\ (= C (+ 1 A)) /\ (ite (<= C 50) (= D B) (= D (+ 1 B))) => inv(C,D)
        let constraint = ChcExpr::and(
            ChcExpr::eq(
                ChcExpr::var(c.clone()),
                ChcExpr::add(ChcExpr::int(1), ChcExpr::var(a.clone())),
            ),
            ChcExpr::ite(
                ChcExpr::le(ChcExpr::var(c.clone()), ChcExpr::int(50)),
                ChcExpr::eq(ChcExpr::var(d.clone()), ChcExpr::var(b.clone())),
                ChcExpr::eq(
                    ChcExpr::var(d.clone()),
                    ChcExpr::add(ChcExpr::int(1), ChcExpr::var(b.clone())),
                ),
            ),
        );

        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(a), ChcExpr::var(b)])],
                Some(constraint),
            ),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(c), ChcExpr::var(d)]),
        ));

        let before = problem.clauses().len();
        problem.try_split_ites_in_clauses(8, false);
        let after = problem.clauses().len();

        assert!(after > before, "expected ite splitting to add clauses");
        for clause in problem.clauses() {
            if let Some(c) = &clause.body.constraint {
                assert!(!c.contains_ite(), "constraint still contains ite: {c}");
            }
        }
    }

    #[test]
    fn split_arithmetic_ite_in_transition_constraint() {
        // Tests splitting of arithmetic ITE (dillig12 pattern):
        // (= I (ite (= J 1) (+ E F) E))
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

        let e = ChcVar::new("E", ChcSort::Int);
        let f = ChcVar::new("F", ChcSort::Int);
        let i = ChcVar::new("I", ChcSort::Int);
        let j = ChcVar::new("J", ChcSort::Int);

        // inv(E,F) /\ (= I (ite (= J 1) (+ E F) E)) => inv(I,F)
        // This is an arithmetic ITE: the result is Int, not Bool
        let constraint = ChcExpr::eq(
            ChcExpr::var(i.clone()),
            ChcExpr::ite(
                ChcExpr::eq(ChcExpr::var(j), ChcExpr::int(1)),
                ChcExpr::add(ChcExpr::var(e.clone()), ChcExpr::var(f.clone())),
                ChcExpr::var(e.clone()),
            ),
        );

        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(e), ChcExpr::var(f.clone())])],
                Some(constraint),
            ),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(i), ChcExpr::var(f)]),
        ));

        let before = problem.clauses().len();
        problem.try_split_ites_in_clauses(8, false);
        let after = problem.clauses().len();

        assert!(
            after > before,
            "expected arithmetic ite splitting to add clauses"
        );
        for clause in problem.clauses() {
            if let Some(c) = &clause.body.constraint {
                assert!(!c.contains_ite(), "constraint still contains ite: {c}");
            }
        }
    }
}

mod phase_bounded_tests {
    use super::*;

    /// Build a phased-execution CHC problem (mimicking model-checker-consumer patterns).
    ///
    /// Single predicate with `num_phases` transitions:
    ///   phase 0 -> 1 -> 2 -> ... -> (num_phases - 1)
    /// Predicate: Inv(phase: Int, x: Int)
    /// Fact: phase=0, x=init_x
    /// Transitions: phase=k /\ ... => Inv(k+1, ...)
    /// Query: phase=max_phase /\ NOT(safety_cond)
    fn build_phased_problem(num_phases: usize) -> ChcProblem {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int, ChcSort::Int]);

        let phase = ChcVar::new("phase", ChcSort::Int);
        let x = ChcVar::new("x", ChcSort::Int);
        let phase1 = ChcVar::new("phase1", ChcSort::Int);
        let x1 = ChcVar::new("x1", ChcSort::Int);

        // Fact: phase=0, x=10
        let fact_constraint = ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(phase.clone()), ChcExpr::int(0)),
            ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(10)),
        );
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(fact_constraint),
            ClauseHead::Predicate(
                inv,
                vec![ChcExpr::var(phase.clone()), ChcExpr::var(x.clone())],
            ),
        ));

        // Transitions: phase=k => Inv(k+1, x+1)
        for k in 0..(num_phases as i64) {
            let constraint = ChcExpr::Op(
                ChcOp::And,
                vec![
                    Arc::new(ChcExpr::eq(ChcExpr::var(phase.clone()), ChcExpr::int(k))),
                    Arc::new(ChcExpr::eq(
                        ChcExpr::var(phase1.clone()),
                        ChcExpr::int(k + 1),
                    )),
                    Arc::new(ChcExpr::eq(
                        ChcExpr::var(x1.clone()),
                        ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                    )),
                ],
            );
            problem.add_clause(HornClause::new(
                ClauseBody::new(
                    vec![(
                        inv,
                        vec![ChcExpr::var(phase.clone()), ChcExpr::var(x.clone())],
                    )],
                    Some(constraint),
                ),
                ClauseHead::Predicate(
                    inv,
                    vec![ChcExpr::var(phase1.clone()), ChcExpr::var(x1.clone())],
                ),
            ));
        }

        // Query: phase=num_phases /\ x != (10 + num_phases)
        let expected_x = 10 + num_phases as i64;
        let query_constraint = ChcExpr::and(
            ChcExpr::eq(ChcExpr::var(phase.clone()), ChcExpr::int(num_phases as i64)),
            ChcExpr::Op(
                ChcOp::Not,
                vec![Arc::new(ChcExpr::eq(
                    ChcExpr::var(x.clone()),
                    ChcExpr::int(expected_x),
                ))],
            ),
        );
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(phase), ChcExpr::var(x)])],
                Some(query_constraint),
            ),
            ClauseHead::False,
        ));

        problem
    }

    #[test]
    fn test_phase_bounded_detection_three_phases() {
        let problem = build_phased_problem(3);
        let depth = problem.detect_phase_bounded_depth();
        // 3 transitions: 0->1, 1->2, 2->3, max_phase=3, depth=4
        assert_eq!(depth, Some(4));
    }

    #[test]
    fn test_phase_bounded_detection_five_phases() {
        let problem = build_phased_problem(5);
        let depth = problem.detect_phase_bounded_depth();
        // 5 transitions: 0->1->2->3->4->5, max_phase=5, depth=6
        assert_eq!(depth, Some(6));
    }

    #[test]
    fn test_no_phase_bounded_for_simple_loop() {
        // A standard simple loop problem is NOT phase-bounded:
        // Inv(x) /\ x < 100 /\ x' = x+1 => Inv(x')
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("Inv", vec![ChcSort::Int]);

        let x = ChcVar::new("x", ChcSort::Int);
        let x1 = ChcVar::new("x1", ChcSort::Int);

        // Fact: x=0
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));

        // Single transition: Inv(x) /\ x < 100 /\ x1 = x+1 => Inv(x1)
        let constraint = ChcExpr::and(
            ChcExpr::Op(
                ChcOp::Lt,
                vec![
                    Arc::new(ChcExpr::var(x.clone())),
                    Arc::new(ChcExpr::int(100)),
                ],
            ),
            ChcExpr::eq(
                ChcExpr::var(x1.clone()),
                ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
            ),
        );
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(inv, vec![ChcExpr::var(x.clone())])], Some(constraint)),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x1)]),
        ));

        // Query
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::Op(
                    ChcOp::Lt,
                    vec![Arc::new(ChcExpr::var(x)), Arc::new(ChcExpr::int(0))],
                )),
            ),
            ClauseHead::False,
        ));

        // Only 1 transition -> not phase-bounded (needs >= 2)
        let depth = problem.detect_phase_bounded_depth();
        assert_eq!(depth, None);
    }

    #[test]
    fn test_no_phase_bounded_for_multi_predicate() {
        // Multi-predicate problems should return None
        let mut problem = ChcProblem::new();
        let _p1 = problem.declare_predicate("P1", vec![ChcSort::Int]);
        let _p2 = problem.declare_predicate("P2", vec![ChcSort::Int]);

        let depth = problem.detect_phase_bounded_depth();
        assert_eq!(depth, None);
    }
}

mod dependency_graph_tests {
    use super::*;

    #[test]
    fn test_has_cycles_false_for_acyclic_chain_8663() {
        let mut problem = ChcProblem::new();
        let p0 = problem.declare_predicate("P0", vec![ChcSort::Int]);
        let p1 = problem.declare_predicate("P1", vec![ChcSort::Int]);
        let p2 = problem.declare_predicate("P2", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(p0, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p0, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(p1, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p1, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(p2, vec![ChcExpr::var(x)]),
        ));

        assert!(!problem.has_cycles());
        assert!(problem.topological_order().is_some());
    }

    #[test]
    fn test_has_cycles_true_for_self_loop_8663() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
        ));

        assert!(problem.has_cycles());
        assert!(problem.topological_order().is_none());
    }

    #[test]
    fn test_has_cycles_true_for_mutual_cycle_8663() {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let q = problem.declare_predicate("Q", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(p, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(q, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::predicates_only(vec![(q, vec![ChcExpr::var(x.clone())])]),
            ClauseHead::Predicate(p, vec![ChcExpr::var(x)]),
        ));

        assert!(problem.has_cycles());
        assert!(problem.topological_order().is_none());
    }
}

mod or_split_tests {
    use super::*;

    fn contains_or(expr: &ChcExpr) -> bool {
        match expr {
            ChcExpr::Op(ChcOp::Or, _) => true,
            ChcExpr::Op(_, args) => args.iter().any(|a| contains_or(a.as_ref())),
            ChcExpr::PredicateApp(_, _, args) => args.iter().any(|a| contains_or(a.as_ref())),
            _ => false,
        }
    }

    #[test]
    fn split_or_in_transition_constraint() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);

        let a = ChcVar::new("A", ChcSort::Int);
        let b = ChcVar::new("B", ChcSort::Int);
        let c = ChcVar::new("C", ChcSort::Int);
        let d = ChcVar::new("D", ChcSort::Int);

        // inv(A,B) /\ (= C (+ 1 A)) /\ (or (= D B) (= D (+ 1 B))) => inv(C,D)
        let constraint = ChcExpr::and(
            ChcExpr::eq(
                ChcExpr::var(c.clone()),
                ChcExpr::add(ChcExpr::int(1), ChcExpr::var(a.clone())),
            ),
            ChcExpr::or(
                ChcExpr::eq(ChcExpr::var(d.clone()), ChcExpr::var(b.clone())),
                ChcExpr::eq(
                    ChcExpr::var(d.clone()),
                    ChcExpr::add(ChcExpr::int(1), ChcExpr::var(b.clone())),
                ),
            ),
        );

        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(a), ChcExpr::var(b)])],
                Some(constraint),
            ),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(c), ChcExpr::var(d)]),
        ));

        let before = problem.clauses().len();
        problem.try_split_ors_in_clauses(8, false);
        let after = problem.clauses().len();

        assert!(after > before, "expected OR splitting to add clauses");
        for clause in problem.clauses() {
            if let Some(c) = &clause.body.constraint {
                assert!(!contains_or(c), "constraint still contains or: {c}");
            }
        }
    }
}

mod clause_simplification_tests {
    use super::*;

    #[test]
    fn false_body_transition_and_query_are_pruned_but_query_is_remembered_for_validation() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("inv", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::Bool(false)),
            ),
            ClauseHead::Predicate(inv, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(inv, vec![ChcExpr::var(x)])],
                Some(ChcExpr::Bool(false)),
            ),
            ClauseHead::False,
        ));

        assert!(problem.clauses().is_empty());
        assert_eq!(problem.queries().count(), 0);
        assert_eq!(problem.pruned_false_queries, 1);
        problem
            .validate()
            .expect("pruned false query should validate");
    }
}
