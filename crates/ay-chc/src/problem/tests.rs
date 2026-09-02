#![allow(clippy::unwrap_used)]
// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn datatype_feature_detection_ignores_unused_declaration_prelude() {
    let problem = crate::parser::ChcParser::parse(
        r#"
(set-logic HORN)
(declare-datatype Box ((box (box-value Int))))
(declare-fun P (Int) Bool)
(assert (P 0))
(assert (forall ((x Int)) (=> (P x) false)))
(check-sat)
"#,
    )
    .unwrap();

    assert!(!problem.datatype_defs().is_empty());
    assert!(!problem.has_datatype_sorts());
    assert!(!problem.uses_datatype_features());
}

#[test]
fn datatype_feature_detection_includes_constraint_only_locals() {
    let problem = crate::parser::ChcParser::parse(
        r#"
(set-logic HORN)
(declare-datatype Box ((box (box-value Int))))
(declare-fun P (Int) Bool)
(assert (forall ((left Box) (right Box) (x Int))
  (=> (= left right) (P x))))
(assert (forall ((x Int)) (=> (P x) false)))
(check-sat)
"#,
    )
    .unwrap();

    assert!(
        !problem.has_datatype_sorts(),
        "all predicate arguments in this regression are scalar"
    );
    assert!(
        problem.uses_datatype_features(),
        "datatype locals in a clause constraint must admit the datatype refutation lane"
    );
}

#[test]
fn datatype_feature_detection_includes_typed_local_without_registry() {
    let constructors = std::sync::Arc::new(vec![crate::ChcDtConstructor {
        name: "typed-box".to_string(),
        selectors: vec![crate::ChcDtSelector {
            name: "typed-box-value".to_string(),
            sort: ChcSort::Int,
        }],
    }]);
    let datatype = ChcSort::Datatype {
        name: "TypedBox".to_string(),
        constructors,
    };
    let left = ChcVar::new("left-box", datatype.clone());
    let right = ChcVar::new("right-box", datatype);
    let mut problem = ChcProblem::new();
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::eq(
        ChcExpr::var(left),
        ChcExpr::var(right),
    ))));

    assert!(problem.datatype_defs().is_empty());
    assert!(problem.uses_datatype_features());
}

#[test]
fn query_obligations_unfold_markers_and_prune_unrelated_properties() {
    let mut problem = ChcProblem::new();
    let root_0 = problem.declare_predicate("root_0", vec![]);
    let root_1 = problem.declare_predicate("root_1", vec![]);
    let error_p0 = problem.declare_predicate("error_p0", vec![]);
    let error_p1 = problem.declare_predicate("error_p1", vec![]);
    let error = problem.declare_predicate("error", vec![]);

    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(root_0, vec![]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(root_1, vec![]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(root_0, vec![])]),
        ClauseHead::Predicate(error_p0, vec![]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(root_1, vec![])]),
        ClauseHead::Predicate(error_p1, vec![]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(error_p0, vec![])]),
        ClauseHead::Predicate(error, vec![]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::predicates_only(vec![(error_p1, vec![])]),
        ClauseHead::Predicate(error, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        error,
        vec![],
    )])));

    let obligations = problem
        .query_obligations()
        .expect("valid query problem should split");
    assert_eq!(obligations.len(), 2);
    assert_eq!(obligations[0].id().label(), "error_p0");
    assert_eq!(obligations[1].id().label(), "error_p1");

    for (obligation, selected, rejected) in [
        (&obligations[0], error_p0, error_p1),
        (&obligations[1], error_p1, error_p0),
    ] {
        assert_eq!(obligation.problem().queries().count(), 1);
        assert!(obligation.problem().validate().is_ok());
        assert_eq!(
            obligation.id().content_sha256(),
            obligation.problem().normalized_input_sha256()
        );
        assert!(obligation
            .problem()
            .clauses_defining(selected)
            .next()
            .is_some());
        assert!(
            obligation
                .problem()
                .clauses_defining(rejected)
                .next()
                .is_none(),
            "the unrelated property's definitions must be removed"
        );
        assert!(
            obligation
                .problem()
                .clauses_defining(error)
                .next()
                .is_none(),
            "the aggregate marker is downstream of the selected direct query"
        );
    }
}

#[test]
fn constrained_nullary_query_is_not_unfolded_without_alpha_renaming() {
    let mut problem = ChcProblem::new();
    let marker = problem.declare_predicate("error", vec![]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(ChcExpr::var(x.clone()), ChcExpr::int(0))),
        ClauseHead::Predicate(marker, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::new(
        vec![(marker, vec![])],
        Some(ChcExpr::eq(ChcExpr::var(x), ChcExpr::int(1))),
    )));

    let obligations = problem
        .query_obligations()
        .expect("valid constrained query should remain direct");
    assert_eq!(obligations.len(), 1);
    assert_eq!(obligations[0].id().defining_clause_index(), None);
    assert_eq!(obligations[0].problem().queries().count(), 1);
}

#[test]
fn query_obligations_distinguish_no_query_invalid_and_vacuously_pruned() {
    assert!(matches!(
        ChcProblem::new().query_obligations(),
        Err(crate::ChcError::NoQuery)
    ));

    let mut invalid = ChcProblem::new();
    let unary = invalid.declare_predicate("unary", vec![ChcSort::Int]);
    invalid.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        unary,
        vec![],
    )])));
    assert!(matches!(
        invalid.query_obligations(),
        Err(crate::ChcError::ArityMismatch {
            expected: 1,
            actual: 0,
            ..
        })
    ));

    let mut vacuous = ChcProblem::new();
    vacuous.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::Bool(
        false,
    ))));
    assert!(vacuous.validate().is_ok());
    assert!(vacuous
        .query_obligations()
        .expect("a remembered false query is valid and vacuously safe")
        .is_empty());
}

#[test]
fn constraint_only_query_drops_all_unrelated_definitions() {
    let mut problem = ChcProblem::new();
    let unrelated = problem.declare_predicate("unrelated", vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(unrelated, vec![]),
    ));

    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::query(ClauseBody::constraint(ChcExpr::eq(
        ChcExpr::var(x),
        ChcExpr::int(0),
    ))));

    let obligations = problem
        .query_obligations()
        .expect("constraint-only query should be independently solvable");
    assert_eq!(obligations.len(), 1);
    let obligation = &obligations[0];
    assert_eq!(obligation.problem().clauses().len(), 1);
    assert_eq!(obligation.problem().queries().count(), 1);
    assert!(obligation
        .problem()
        .clauses_defining(unrelated)
        .next()
        .is_none());
    assert_eq!(
        obligation.id().content_sha256(),
        obligation.problem().normalized_input_sha256()
    );
    assert_eq!(obligation.id().content_sha256().len(), 64);
    assert!(obligation
        .id()
        .content_sha256()
        .bytes()
        .all(|byte| byte.is_ascii_hexdigit() && !byte.is_ascii_uppercase()));
}

#[test]
fn query_obligations_reject_relation_hidden_in_constraint() {
    let mut problem = ChcProblem::new();
    let reachable = problem.declare_predicate("reachable", vec![]);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(reachable, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::constraint(
        ChcExpr::predicate_app("reachable", reachable, vec![]),
    )));

    let error = problem
        .query_obligations()
        .expect_err("a relation hidden in a theory constraint is not a valid Horn problem");
    assert!(
        matches!(error, crate::ChcError::Verification(_)),
        "hidden relation must fail closed before slicing, got {error}"
    );
    assert!(
        error.to_string().contains("ClauseBody::predicates"),
        "error must explain the canonical Horn representation: {error}"
    );
}

#[test]
fn validation_rejects_conflicting_typed_uf_signatures_across_clauses() {
    let mut problem = ChcProblem::new();
    let reachable = problem.declare_predicate("reachable", vec![]);
    for argument in [ChcExpr::Int(0), ChcExpr::Bool(false)] {
        let application = ChcExpr::FuncApp(
            "f".to_string(),
            ChcSort::Int,
            vec![std::sync::Arc::new(argument)],
        );
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::eq(application, ChcExpr::Int(0))),
            ClauseHead::Predicate(reachable, vec![]),
        ));
    }
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        reachable,
        vec![],
    )])));

    let error = problem
        .validate()
        .expect_err("ordinary UFs cannot be overloaded across disjoint clauses");
    assert!(
        matches!(error, crate::ChcError::Verification(_)),
        "signature conflict must be a typed validation failure: {error}"
    );
    assert!(error.to_string().contains("conflicting signatures"));
}

fn typed_function_problem(
    name: &str,
    return_sort: ChcSort,
    argument_sorts: Vec<ChcSort>,
    datatype_anchor: Option<ChcSort>,
) -> ChcProblem {
    let mut problem = ChcProblem::new();
    if let Some(sort) = datatype_anchor {
        problem.declare_predicate("datatype_anchor", vec![sort]);
    }
    let reachable = problem.declare_predicate("reachable", vec![]);
    let arguments = argument_sorts
        .into_iter()
        .enumerate()
        .map(|(index, sort)| ChcExpr::var(ChcVar::new(format!("arg_{index}"), sort)))
        .map(Arc::new)
        .collect();
    let result_sort = return_sort.clone();
    let application = ChcExpr::FuncApp(name.to_string(), return_sort, arguments);
    let constraint = if application.sort() == ChcSort::Bool {
        application
    } else {
        ChcExpr::eq(
            application,
            ChcExpr::var(ChcVar::new("function_result", result_sort)),
        )
    };
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(constraint),
        ClauseHead::Predicate(reachable, vec![]),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        reachable,
        vec![],
    )])));
    problem
}

fn validation_box_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "ValidationBox".to_string(),
        constructors: Arc::new(vec![crate::ChcDtConstructor {
            name: "mkValidationBox".to_string(),
            selectors: vec![crate::ChcDtSelector {
                name: "validationPayload".to_string(),
                sort: ChcSort::Int,
            }],
        }]),
    }
}

#[test]
fn validation_rejects_non_scalar_typed_ordinary_uf_signatures() {
    let datatype = validation_box_sort();
    let array = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Bool));
    let uninterpreted = ChcSort::Uninterpreted("OpaqueValidationSort".to_string());
    let cases = [
        ("array-argument", ChcSort::Int, vec![array.clone()]),
        ("datatype-argument", ChcSort::Int, vec![datatype.clone()]),
        (
            "uninterpreted-argument",
            ChcSort::Int,
            vec![uninterpreted.clone()],
        ),
        ("array-return", array, vec![ChcSort::Int]),
        ("datatype-return", datatype, vec![ChcSort::Int]),
        ("uninterpreted-return", uninterpreted, vec![ChcSort::Int]),
    ];

    for (name, return_sort, argument_sorts) in cases {
        let error = typed_function_problem(name, return_sort, argument_sorts, None)
            .validate()
            .expect_err("typed ordinary UFs must stay within the scalar backend contract");
        assert!(
            error.to_string().contains("non-scalar"),
            "{name} must report the scalar-UF boundary: {error}"
        );
    }
}

#[test]
fn validation_rejects_typed_ordinary_uf_namespace_collisions() {
    let mut predicate_collision =
        typed_function_problem("claimed_relation", ChcSort::Int, vec![ChcSort::Int], None);
    predicate_collision.declare_predicate("claimed_relation", vec![ChcSort::Int]);
    let error = predicate_collision
        .validate()
        .expect_err("ordinary UF must not reuse a predicate name");
    assert!(error.to_string().contains("predicate name"));

    let datatype = validation_box_sort();
    for (name, return_sort) in [
        ("mkValidationBox", ChcSort::Int),
        ("validationPayload", ChcSort::Int),
        ("is-mkValidationBox", ChcSort::Bool),
    ] {
        let error = typed_function_problem(
            name,
            return_sort,
            vec![ChcSort::Int],
            Some(datatype.clone()),
        )
        .validate()
        .expect_err("ordinary UF must not reuse a datatype term symbol");
        assert!(
            error
                .to_string()
                .contains("datatype constructor, selector, or tester"),
            "{name} collision must identify the datatype namespace: {error}"
        );
    }

    for builtin in ["to_real", "select", "bvadd"] {
        let error = typed_function_problem(builtin, ChcSort::Int, vec![ChcSort::Int], None)
            .validate()
            .expect_err("ordinary UF must not reuse a reserved SMT builtin");
        assert!(
            error.to_string().contains("reserved SMT builtin"),
            "{builtin} collision must identify the builtin namespace: {error}"
        );
    }
}

#[test]
fn validation_accepts_scalar_typed_bool_uf_and_exact_intrinsics() {
    typed_function_problem(
        "typed_bool_uf",
        ChcSort::Bool,
        vec![
            ChcSort::Bool,
            ChcSort::Int,
            ChcSort::Real,
            ChcSort::BitVec(17),
        ],
        None,
    )
    .validate()
    .expect("typed Bool-return ordinary UF with scalar arguments is supported");

    typed_function_problem("to_real", ChcSort::Real, vec![ChcSort::Int], None)
        .validate()
        .expect("the exact typed to_real intrinsic is not an ordinary UF collision");
}

#[test]
fn validation_accepts_exact_typed_datatype_members() {
    let datatype = validation_box_sort();
    let payload = ChcExpr::var(ChcVar::new("payload", ChcSort::Int));
    let constructor = ChcExpr::FuncApp(
        "mkValidationBox".to_string(),
        datatype.clone(),
        vec![Arc::new(payload.clone())],
    );
    let selector = ChcExpr::FuncApp(
        "validationPayload".to_string(),
        ChcSort::Int,
        vec![Arc::new(constructor.clone())],
    );
    let tester = ChcExpr::FuncApp(
        "is-mkValidationBox".to_string(),
        ChcSort::Bool,
        vec![Arc::new(constructor)],
    );

    let mut problem = ChcProblem::new();
    let reachable = problem.declare_predicate("reachable", vec![datatype]);
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::and(ChcExpr::eq(selector, payload), tester)),
        ClauseHead::Predicate(
            reachable,
            vec![ChcExpr::var(ChcVar::new("state", validation_box_sort()))],
        ),
    ));
    problem.add_clause(HornClause::query(ClauseBody::predicates_only(vec![(
        reachable,
        vec![ChcExpr::var(ChcVar::new(
            "query_state",
            validation_box_sort(),
        ))],
    )])));
    problem
        .validate()
        .expect("exact constructor, selector, and tester applications remain datatype terms");
}

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

mod dead_end_cone_tests {
    use super::*;

    /// Non-tautological self-loop `p(x) /\ (y = x + 1) => p(y)`.
    fn self_loop_clause(p: PredicateId, x: &ChcVar, y: &ChcVar) -> HornClause {
        HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::eq(
                    ChcExpr::var(y.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                )),
            ),
            ClauseHead::Predicate(p, vec![ChcExpr::var(y.clone())]),
        )
    }

    /// Build: p0 -> p1 -> err (query), plus a dead-end `dead` with a
    /// non-tautological self-loop reached only from p1 (`p1 -> dead`, no path
    /// dead ~> err). The sole cycle is the dead-end self-loop.
    fn build_acyclic_modulo_dead_end() -> (ChcProblem, PredicateId) {
        let mut problem = ChcProblem::new();
        let p0 = problem.declare_predicate("p0", vec![ChcSort::Int]);
        let p1 = problem.declare_predicate("p1", vec![ChcSort::Int]);
        let err = problem.declare_predicate("err", vec![]);
        let dead = problem.declare_predicate("dead", vec![ChcSort::Int]);

        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);

        // Fact: => p0(x)
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![], None),
            ClauseHead::Predicate(p0, vec![ChcExpr::var(x.clone())]),
        ));
        // p0(x) => p1(x)
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p0, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(p1, vec![ChcExpr::var(x.clone())]),
        ));
        // p1(x) => err
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p1, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(err, vec![]),
        ));
        // p1(x) => dead(x)   (enters the dead-end region)
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p1, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(dead, vec![ChcExpr::var(x.clone())]),
        ));
        // dead(x) /\ (y = x+1) => dead(y)   (the sole cycle, off the query cone)
        problem.add_clause(self_loop_clause(dead, &x, &y));
        // Query: err => false
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(err, vec![])],
            None,
        )));

        (problem, dead)
    }

    #[test]
    fn cone_excludes_dead_end_predicate() {
        let (problem, dead) = build_acyclic_modulo_dead_end();
        let cone = problem
            .query_cone_of_influence()
            .expect("explicit query seeds the cone");
        assert_eq!(cone.len(), 3, "cone should be {{p0, p1, err}}");
        assert!(
            !cone.contains(&dead),
            "dead-end predicate must be out of cone"
        );
    }

    #[test]
    fn strips_dead_end_self_loop_and_becomes_acyclic() {
        let (mut problem, dead) = build_acyclic_modulo_dead_end();
        assert!(
            problem.has_cycles(),
            "dead-end self-loop makes the full graph cyclic"
        );
        let before = problem.clauses().len();

        assert!(
            problem.strip_dead_end_cycle_predicates(),
            "the dead-end self-loop should be stripped"
        );

        assert_eq!(
            problem.clauses().len(),
            before - 2,
            "the p1->dead and dead->dead clauses should be removed"
        );
        assert_eq!(
            problem.clauses_defining(dead).count(),
            0,
            "no clause should still define the dead-end predicate"
        );
        assert!(
            !problem.has_cycles(),
            "after stripping the dead-end cycle the problem is acyclic"
        );
        // The query is preserved so the verdict is still well-defined.
        assert_eq!(problem.queries().count(), 1);
    }

    #[test]
    fn does_not_strip_when_cycle_is_on_the_query_cone() {
        // Same skeleton, but the cycle is a self-loop on p1, which IS on the
        // path to the query: PDR is genuinely required, so nothing is stripped.
        let mut problem = ChcProblem::new();
        let p0 = problem.declare_predicate("p0", vec![ChcSort::Int]);
        let p1 = problem.declare_predicate("p1", vec![ChcSort::Int]);
        let err = problem.declare_predicate("err", vec![]);

        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![], None),
            ClauseHead::Predicate(p0, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p0, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(p1, vec![ChcExpr::var(x.clone())]),
        ));
        // p1 self-loop (on the query cone) — a genuine cycle.
        problem.add_clause(self_loop_clause(p1, &x, &y));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p1, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(err, vec![]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(err, vec![])],
            None,
        )));

        let before = problem.clauses().len();
        assert!(
            !problem.strip_dead_end_cycle_predicates(),
            "a cycle on the query cone must not be stripped"
        );
        assert_eq!(problem.clauses().len(), before, "no clause removed");
    }

    #[test]
    fn does_not_strip_a_dead_end_that_is_already_acyclic() {
        // A dead-end predicate with NO cycle: stripping would change nothing an
        // engine cares about for acyclicity, so we deliberately leave it be
        // (keeps every non-target problem byte-identical).
        let mut problem = ChcProblem::new();
        let p0 = problem.declare_predicate("p0", vec![ChcSort::Int]);
        let err = problem.declare_predicate("err", vec![]);
        let dead = problem.declare_predicate("dead", vec![ChcSort::Int]);

        let x = ChcVar::new("x", ChcSort::Int);

        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![], None),
            ClauseHead::Predicate(p0, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p0, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(err, vec![]),
        ));
        // acyclic dead-end: p0 -> dead, no self-loop.
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![(p0, vec![ChcExpr::var(x.clone())])], None),
            ClauseHead::Predicate(dead, vec![ChcExpr::var(x.clone())]),
        ));
        problem.add_clause(HornClause::query(ClauseBody::new(
            vec![(err, vec![])],
            None,
        )));

        let before = problem.clauses().len();
        assert!(!problem.has_cycles());
        assert!(
            !problem.strip_dead_end_cycle_predicates(),
            "no cycle to remove -> no strip"
        );
        assert_eq!(problem.clauses().len(), before);
    }

    #[test]
    fn no_query_returns_none_cone_and_no_strip() {
        let mut problem = ChcProblem::new();
        let p0 = problem.declare_predicate("p0", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        problem.add_clause(HornClause::new(
            ClauseBody::new(vec![], None),
            ClauseHead::Predicate(p0, vec![ChcExpr::var(x)]),
        ));
        assert!(problem.query_cone_of_influence().is_none());
        assert!(!problem.strip_dead_end_cycle_predicates());
    }
}
