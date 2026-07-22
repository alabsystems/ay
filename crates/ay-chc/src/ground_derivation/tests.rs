// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the pure-ground derivation validator.
//!
//! The validator is the trust anchor for ground-witness back-translation, so
//! the tests are written adversarially: every structural escape hatch a
//! fabricated derivation could use (self-justification, padding, argument
//! disagreement, non-ground values, wrong clause) must be a rejection.

use super::*;
use crate::clause::{ClauseBody, ClauseHead};
use crate::{ChcDtConstructor, ChcDtSelector, ChcSort, ChcVar, PredicateId};
use std::sync::Arc;

fn var(name: &str) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, ChcSort::Int))
}

fn env(pairs: &[(&str, i128)]) -> FxHashMap<String, SmtValue> {
    let mut map = FxHashMap::default();
    for (name, value) in pairs {
        map.insert((*name).to_string(), SmtValue::Int(*value));
    }
    map
}

/// `P(0).  P(x) => P(x + 1).  P(x) /\ x >= 2 => false.`
///
/// UNSAFE: `P(0), P(1), P(2)` then the query.
fn counting_problem() -> ChcProblem {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("P", vec![ChcSort::Int]);
    // clause 0: fact P(0)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(var("x"), ChcExpr::Int(0))),
        ClauseHead::Predicate(p, vec![var("x")]),
    ));
    // clause 1: P(x) /\ y = x + 1 => P(y)
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("x")])],
            Some(ChcExpr::eq(
                var("y"),
                ChcExpr::add(var("x"), ChcExpr::Int(1)),
            )),
        ),
        ClauseHead::Predicate(p, vec![var("y")]),
    ));
    // clause 2: P(x) /\ x >= 2 => false
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("x")])],
            Some(ChcExpr::ge(var("x"), ChcExpr::Int(2))),
        ),
        ClauseHead::False,
    ));
    problem
}

fn counting_derivation() -> GroundDerivation {
    GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: env(&[("x", 0)]),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: env(&[("x", 0), ("y", 1)]),
                premises: vec![0],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: env(&[("x", 1), ("y", 2)]),
                premises: vec![1],
            },
            GroundDerivationStep {
                clause_index: 2,
                env: env(&[("x", 2)]),
                premises: vec![2],
            },
        ],
        query_step: 3,
    }
}

#[test]
fn ground_derivation_validates_a_real_counterexample() {
    let problem = counting_problem();
    assert_eq!(
        validate_ground_derivation(&problem, &counting_derivation()),
        Ok(())
    );
}

#[test]
fn ground_derivation_rejects_argument_disagreement() {
    // The middle step claims to consume `P(0)` but binds `x = 1`: the body
    // argument no longer matches the premise's head argument.
    let problem = counting_problem();
    let mut derivation = counting_derivation();
    derivation.steps[1].env = env(&[("x", 1), ("y", 2)]);
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::ArgumentMismatch {
            step: 1,
            position: 0,
            argument: 0,
        })
    );
}

#[test]
fn ground_derivation_rejects_violated_constraint() {
    // Jump straight from `P(0)` to the query: the query guard `x >= 2` is
    // concretely false.
    let problem = counting_problem();
    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: env(&[("x", 0)]),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 2,
                env: env(&[("x", 0)]),
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::ConstraintFalse { step: 1 })
    );
}

#[test]
fn ground_derivation_rejects_unbound_variable() {
    // `y` is missing from the step environment, so the transition constraint
    // cannot be decided. Fail closed rather than assume.
    let problem = counting_problem();
    let mut derivation = counting_derivation();
    derivation.steps[1].env = env(&[("x", 0)]);
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::ConstraintNotGround { step: 1 })
    );
}

#[test]
fn ground_derivation_rejects_opaque_placeholder_values() {
    // An `Opaque` model placeholder is not a value: two unrelated placeholders
    // would otherwise compare equal and "justify" a step.
    let problem = counting_problem();
    let mut derivation = counting_derivation();
    derivation.steps[1]
        .env
        .insert("y".to_string(), SmtValue::Opaque("@x7".to_string()));
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::ConstraintNotGround { step: 1 })
    );
}

#[test]
fn ground_derivation_rejects_self_justifying_step() {
    // The classic adversarial witness: a step that premises itself. Strictly
    // backwards premise indices make this structurally impossible.
    let problem = counting_problem();
    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 1,
                env: env(&[("x", 5), ("y", 5)]),
                premises: vec![0],
            },
            GroundDerivationStep {
                clause_index: 2,
                env: env(&[("x", 5)]),
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::PremiseNotWellFounded {
            step: 0,
            premise: 0,
        })
    );
}

#[test]
fn ground_derivation_rejects_missing_premise_for_body_predicate() {
    // A step that fires a transition clause with no premise at all would
    // "derive" `P` out of nothing.
    let problem = counting_problem();
    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 1,
                env: env(&[("x", 1), ("y", 2)]),
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 2,
                env: env(&[("x", 2)]),
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::PremiseArityMismatch {
            step: 0,
            expected: 1,
            found: 0,
        })
    );
}

#[test]
fn ground_derivation_rejects_non_query_root() {
    let problem = counting_problem();
    let mut derivation = counting_derivation();
    derivation.query_step = 2;
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::RootNotQuery { step: 2 })
    );
}

#[test]
fn ground_derivation_rejects_padding_steps() {
    let problem = counting_problem();
    let mut derivation = counting_derivation();
    derivation.steps.push(GroundDerivationStep {
        clause_index: 0,
        env: env(&[("x", 0)]),
        premises: vec![],
    });
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::UnreachableStep { step: 4 })
    );
}

#[test]
fn ground_derivation_rejects_out_of_range_clause() {
    let problem = counting_problem();
    let mut derivation = counting_derivation();
    derivation.steps[0].clause_index = 99;
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::ClauseOutOfRange {
            step: 0,
            clause_index: 99,
        })
    );
}

/// ANTI-FABRICATION: the same derivation shape replayed against a problem whose
/// error is genuinely unreachable must be rejected. This is the miniature of
/// the synthetic SAFE analogue regression test.
#[test]
fn ground_derivation_rejects_derivation_from_a_different_problem() {
    // Same predicate/clause layout, but the query demands `x >= 100`, which the
    // three-step derivation never reaches.
    let mut safe = ChcProblem::new();
    let p = safe.declare_predicate("P", vec![ChcSort::Int]);
    safe.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(var("x"), ChcExpr::Int(0))),
        ClauseHead::Predicate(p, vec![var("x")]),
    ));
    safe.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("x")])],
            Some(ChcExpr::eq(
                var("y"),
                ChcExpr::add(var("x"), ChcExpr::Int(1)),
            )),
        ),
        ClauseHead::Predicate(p, vec![var("y")]),
    ));
    safe.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("x")])],
            Some(ChcExpr::ge(var("x"), ChcExpr::Int(100))),
        ),
        ClauseHead::False,
    ));
    assert_eq!(
        validate_ground_derivation(&safe, &counting_derivation()),
        Err(GroundDerivationError::ConstraintFalse { step: 3 })
    );
}

#[test]
fn ground_derivation_validates_array_and_datatype_values() {
    // Ground evaluation must decide array reads and datatype selectors, which
    // is exactly what the ground-table concretizer and the DT flattener need
    // when they re-materialize erased values.
    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let p = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let table = ChcExpr::Var(ChcVar::new("T", arr_sort));
    // (select T 3) = 7 => Q(7)
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            var("v"),
            ChcExpr::select(table.clone(), ChcExpr::Int(3)),
        )),
        ClauseHead::Predicate(p, vec![var("v")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("v")])],
            Some(ChcExpr::eq(var("v"), ChcExpr::Int(7))),
        ),
        ClauseHead::False,
    ));

    let mut fact_env = env(&[("v", 7)]);
    fact_env.insert(
        "T".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(3), SmtValue::Int(7))],
        },
    );
    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: fact_env,
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: env(&[("v", 7)]),
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    assert_eq!(validate_ground_derivation(&problem, &derivation), Ok(()));
}

#[test]
fn ground_derivation_rejects_wrong_pin_value() {
    // The same shape with the pin map claiming a different value at index 3:
    // the fact constraint now forces `v = 5` while the query needs `v = 7`.
    let mut problem = ChcProblem::new();
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let p = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let table = ChcExpr::Var(ChcVar::new("T", arr_sort));
    problem.add_clause(HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(
            var("v"),
            ChcExpr::select(table.clone(), ChcExpr::Int(3)),
        )),
        ClauseHead::Predicate(p, vec![var("v")]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("v")])],
            Some(ChcExpr::eq(var("v"), ChcExpr::Int(7))),
        ),
        ClauseHead::False,
    ));

    let mut fact_env = env(&[("v", 7)]);
    fact_env.insert(
        "T".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![(SmtValue::Int(3), SmtValue::Int(5))],
        },
    );
    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: fact_env,
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: env(&[("v", 7)]),
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    assert_eq!(
        validate_ground_derivation(&problem, &derivation),
        Err(GroundDerivationError::ConstraintFalse { step: 0 })
    );
}

#[test]
fn completion_decomposes_a_known_datatype_constructor_into_fields() {
    let pair_sort = ChcSort::Datatype {
        name: "Pair".to_string(),
        constructors: Arc::new(vec![ChcDtConstructor {
            name: "mk-pair".to_string(),
            selectors: vec![
                ChcDtSelector {
                    name: "left".to_string(),
                    sort: ChcSort::Int,
                },
                ChcDtSelector {
                    name: "right".to_string(),
                    sort: ChcSort::Int,
                },
            ],
        }]),
    };
    let pair = ChcVar::new("pair", pair_sort.clone());
    let left = ChcVar::new("left", ChcSort::Int);
    let right = ChcVar::new("right", ChcSort::Int);
    let rebuilt = ChcExpr::FuncApp(
        "mk-pair".to_string(),
        pair_sort,
        vec![
            Arc::new(ChcExpr::var(left.clone())),
            Arc::new(ChcExpr::var(right.clone())),
        ],
    );
    let clause = HornClause::query(ClauseBody::constraint(ChcExpr::eq(
        ChcExpr::var(pair.clone()),
        rebuilt,
    )));
    let mut completed = FxHashMap::default();
    completed.insert(
        pair.name,
        SmtValue::Datatype(
            "mk-pair".to_string(),
            vec![SmtValue::Int(17), SmtValue::Int(23)],
        ),
    );

    assert!(complete::complete_env_for_clause(&clause, &mut completed));
    assert_eq!(completed.get(&left.name), Some(&SmtValue::Int(17)));
    assert_eq!(completed.get(&right.name), Some(&SmtValue::Int(23)));
    assert_eq!(
        eval_ground(&clause.body.constraint.unwrap(), &completed),
        Some(SmtValue::Bool(true))
    );
}

#[test]
fn completion_does_not_decompose_a_different_constructor() {
    let option_sort = ChcSort::Datatype {
        name: "OptionInt".to_string(),
        constructors: Arc::new(vec![
            ChcDtConstructor {
                name: "none".to_string(),
                selectors: vec![],
            },
            ChcDtConstructor {
                name: "some".to_string(),
                selectors: vec![ChcDtSelector {
                    name: "value".to_string(),
                    sort: ChcSort::Int,
                }],
            },
        ]),
    };
    let option = ChcVar::new("option", option_sort.clone());
    let value = ChcVar::new("value", ChcSort::Int);
    let some = ChcExpr::FuncApp(
        "some".to_string(),
        option_sort,
        vec![Arc::new(ChcExpr::var(value.clone()))],
    );
    let clause = HornClause::query(ClauseBody::constraint(ChcExpr::eq(
        ChcExpr::var(option.clone()),
        some,
    )));
    let mut propagated = FxHashMap::default();
    propagated.insert(option.name, SmtValue::Datatype("none".to_string(), vec![]));

    complete::propagate_env_for_clause(&clause, &mut propagated);
    assert!(
        !propagated.contains_key(&value.name),
        "constructor injectivity must not cross constructor tags"
    );
}

#[test]
fn premise_seeding_evaluates_the_premise_head_argument() {
    let p = PredicateId::new(0);
    let head_source = ChcVar::new("head_source", ChcSort::Int);
    let premise = HornClause::new(
        ClauseBody::constraint(ChcExpr::Bool(true)),
        ClauseHead::Predicate(
            p,
            vec![ChcExpr::add(
                ChcExpr::var(head_source.clone()),
                ChcExpr::int(1),
            )],
        ),
    );
    let consumed = ChcVar::new("consumed", ChcSort::Int);
    let consumer = HornClause::query(ClauseBody::predicates_only(vec![(
        p,
        vec![ChcExpr::var(consumed.clone())],
    )]));
    let clauses = vec![premise, consumer.clone()];
    let steps = vec![GroundDerivationStep {
        clause_index: 0,
        env: env(&[("head_source", 40)]),
        premises: vec![],
    }];
    let mut seeded = FxHashMap::default();

    complete::seed_env_from_premises(&consumer, &[0], &steps, &clauses, &mut seeded);
    assert_eq!(seeded.get(&consumed.name), Some(&SmtValue::Int(41)));

    // A value already fixed by the consumer's own evidence has precedence;
    // final validation, rather than this heuristic, reports any disagreement.
    seeded.insert(consumed.name.clone(), SmtValue::Int(99));
    complete::seed_env_from_premises(&consumer, &[0], &steps, &clauses, &mut seeded);
    assert_eq!(seeded.get(&consumed.name), Some(&SmtValue::Int(99)));
}

#[test]
fn debug_render_truncation_is_unicode_boundary_safe() {
    // Byte offset 220 is inside this four-byte code point. The former
    // `&rendered[..220]` diagnostic path panicked on this exact shape.
    let rendered = format!("{}💥suffix", "a".repeat(219));
    let truncated = truncate_debug_expr(rendered);
    assert!(truncated.ends_with('…'));
    assert_eq!(truncated, format!("{}…", "a".repeat(219)));
    assert!(truncated.len() <= 222); // 219-byte payload plus the 3-byte ellipsis.
}

#[test]
fn ground_derivation_len_and_is_empty_track_the_step_list() {
    assert!(GroundDerivation::default().is_empty());
    assert_eq!(GroundDerivation::default().len(), 0);
    let derivation = counting_derivation();
    assert!(!derivation.is_empty());
    assert_eq!(derivation.len(), 4);
}

// ==========================================================================
// Witness carrying and ground completion (#item4-ground-witness-backtranslation)
//
// These pin the SOUNDNESS claim that makes carrying a transformed-search model
// down into the original-clause expansion acceptable: a carried value is
// SYNTHESIS, never evidence. It is written into an environment that
// `validate_ground_derivation` then re-evaluates in full against the ORIGINAL
// clauses, so a wrong carried value can only be REJECTED.
// ==========================================================================

/// `Option Int`, the two-constructor shape the archetype's tester-only
/// existentials have.
fn option_int_sort() -> ChcSort {
    ChcSort::Datatype {
        name: "OptionInt".to_string(),
        constructors: std::sync::Arc::new(vec![
            crate::ChcDtConstructor {
                name: "none".to_string(),
                selectors: vec![],
            },
            crate::ChcDtConstructor {
                name: "some".to_string(),
                selectors: vec![crate::ChcDtSelector {
                    name: "val".to_string(),
                    sort: ChcSort::Int,
                }],
            },
        ]),
    }
}

fn is_some(expr: ChcExpr) -> ChcExpr {
    ChcExpr::FuncApp(
        "is-some".to_string(),
        ChcSort::Bool,
        vec![std::sync::Arc::new(expr)],
    )
}

/// A clause whose variable `c` is an existential constrained ONLY through a
/// tester — no equality determines it and no premise pins it. This is the exact
/// shape that made the iterator_count expansion fail: completion had to invent
/// a value, and the sort default (`none`, the nullary constructor) falsified
/// the tester.
fn tester_only_clause() -> (ChcProblem, HornClause) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("R", vec![ChcSort::Bool]);
    let cell = ChcExpr::Var(ChcVar::new("c", option_int_sort()));
    // out = is-some(c)  =>  R(out)
    let clause = HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(var("out"), is_some(cell))),
        ClauseHead::Predicate(p, vec![var("out")]),
    );
    problem.add_clause(clause.clone());
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("out")])],
            Some(ChcExpr::eq(var("out"), ChcExpr::Bool(true))),
        ),
        ClauseHead::False,
    ));
    (problem, clause)
}

/// The same shape with the ITE condition guarded by a SECOND unconstrained
/// existential. This is the case Part 1 exists for and Part 2 provably cannot
/// reach: at normalization time `k` is still unbound, so the ITE does not
/// resolve, so the tester's subject is the ITE term rather than `c` and the
/// tester rule correctly abstains. Only a carried witness completes it.
fn witness_only_clause() -> (ChcProblem, HornClause) {
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("R", vec![ChcSort::Bool]);
    let cell = ChcExpr::Var(ChcVar::new("c", option_int_sort()));
    let none = ChcExpr::FuncApp("none".to_string(), option_int_sort(), vec![]);
    let selected = ChcExpr::Op(
        crate::ChcOp::Ite,
        vec![
            std::sync::Arc::new(ChcExpr::gt(var("k"), ChcExpr::Int(100))),
            std::sync::Arc::new(cell),
            std::sync::Arc::new(none),
        ],
    );
    let clause = HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(var("out"), is_some(selected))),
        ClauseHead::Predicate(p, vec![var("out")]),
    );
    problem.add_clause(clause.clone());
    problem.add_clause(HornClause::new(
        ClauseBody::new(
            vec![(p, vec![var("out")])],
            Some(ChcExpr::eq(var("out"), ChcExpr::Bool(true))),
        ),
        ClauseHead::False,
    ));
    (problem, clause)
}

#[test]
fn carried_witness_completes_what_ground_completion_cannot() {
    // THE COMPLETENESS CLAIM. The derivation needs `out = true`, which needs
    // the ITE to select `c` and `c` to be a `some`. Nothing DETERMINES either
    // `k` or `c`, and the tester rule cannot fire because the ITE is unresolved
    // while `k` is unbound — so unaided completion defaults `k = 0`, the ITE
    // selects `none`, and the constraint reads false. The carried witness is
    // the only thing that closes it.
    let (problem, clause) = witness_only_clause();

    let mut plain = FxHashMap::default();
    plain.insert("out".to_string(), SmtValue::Bool(true));
    assert!(complete::complete_env_for_clause(&clause, &mut plain));
    assert_eq!(
        eval_ground_pub(clause.body.constraint.as_ref().expect("constraint"), &plain),
        Some(SmtValue::Bool(false)),
        "unaided completion should falsify this clause — that is the gap"
    );

    let mut carried = FxHashMap::default();
    carried.insert("out".to_string(), SmtValue::Bool(true));
    let mut witness = FxHashMap::default();
    witness.insert("k".to_string(), SmtValue::Int(200));
    witness.insert(
        "c".to_string(),
        SmtValue::Datatype("some".to_string(), vec![SmtValue::Int(4)]),
    );
    assert!(complete::complete_env_for_clause_with_fallback(
        &clause,
        &mut carried,
        &witness
    ));
    assert_eq!(
        eval_ground_pub(
            clause.body.constraint.as_ref().expect("constraint"),
            &carried
        ),
        Some(SmtValue::Bool(true)),
        "the carried witness must satisfy the clause the search satisfied"
    );

    let derivation = |fact_env: FxHashMap<String, SmtValue>| GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: fact_env,
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: {
                    let mut e = FxHashMap::default();
                    e.insert("out".to_string(), SmtValue::Bool(true));
                    e
                },
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    assert_eq!(
        validate_ground_derivation(&problem, &derivation(carried)),
        Ok(())
    );
    assert!(
        validate_ground_derivation(&problem, &derivation(plain)).is_err(),
        "the sort-defaulted environment must NOT validate — that is the gap the \
         carried witness closes"
    );
}

#[test]
fn carried_witness_wins_over_a_synthesized_tag() {
    // Where the tester rule CAN fire, the carried value still takes precedence:
    // it is the instantiation the search actually used, and the synthesized tag
    // only fills its fields with defaults.
    let (_, clause) = tester_only_clause();

    let mut carried = FxHashMap::default();
    carried.insert("out".to_string(), SmtValue::Bool(true));
    let mut witness = FxHashMap::default();
    witness.insert(
        "c".to_string(),
        SmtValue::Datatype("some".to_string(), vec![SmtValue::Int(4)]),
    );
    assert!(complete::complete_env_for_clause_with_fallback(
        &clause,
        &mut carried,
        &witness
    ));
    assert_eq!(
        carried.get("c"),
        Some(&SmtValue::Datatype(
            "some".to_string(),
            vec![SmtValue::Int(4)]
        )),
        "the carried witness must win over a synthesized tag"
    );
}

#[test]
fn a_wrong_carried_witness_is_rejected_by_ground_validation() {
    // THE LOAD-BEARING ANTI-FABRICATION TEST. A carried value's provenance is
    // an OVER-APPROXIMATING transformed problem, so it can be wrong — the
    // corrupted-rename case, a stale column read, a truncated flattening. When
    // it is, completion happily writes it, and validation must still reject.
    let (problem, clause) = tester_only_clause();

    let mut carried = FxHashMap::default();
    carried.insert("out".to_string(), SmtValue::Bool(true));
    let mut wrong_witness = FxHashMap::default();
    // `none` is well-sorted and concrete, so every guard admits it — and it
    // makes `is-some(c)` false while the derivation claims `out = true`.
    wrong_witness.insert(
        "c".to_string(),
        SmtValue::Datatype("none".to_string(), vec![]),
    );
    assert!(complete::complete_env_for_clause_with_fallback(
        &clause,
        &mut carried,
        &wrong_witness
    ));
    assert_eq!(
        carried.get("c"),
        Some(&SmtValue::Datatype("none".to_string(), vec![])),
        "completion does not screen the witness — validation is the anchor"
    );

    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: carried,
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: {
                    let mut e = FxHashMap::default();
                    e.insert("out".to_string(), SmtValue::Bool(true));
                    e
                },
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    assert!(
        validate_ground_derivation(&problem, &derivation).is_err(),
        "a WRONG carried witness was accepted — the acceptance anchor is broken"
    );
}

#[test]
fn a_mis_sorted_carried_witness_is_ignored_rather_than_written() {
    // A witness entry whose sort does not match the variable (a stale value
    // from a truncated flattening) must not be written where a differently
    // sorted value belongs; the slot falls back to the previous behavior.
    let (_, clause) = tester_only_clause();
    let mut carried = FxHashMap::default();
    carried.insert("out".to_string(), SmtValue::Bool(true));
    let mut bad_sort = FxHashMap::default();
    bad_sort.insert("c".to_string(), SmtValue::Int(9));
    assert!(complete::complete_env_for_clause_with_fallback(
        &clause,
        &mut carried,
        &bad_sort
    ));
    assert!(
        !matches!(carried.get("c"), Some(SmtValue::Int(_))),
        "a mis-sorted witness must be ignored, not written"
    );
}

#[test]
fn tester_driven_completion_recovers_the_forced_constructor() {
    // With no witness at all, the clause still FORCES `is-some(c)` once
    // `out = true` is known. Instantiating the demanded tag is the unique
    // choice the conjunct admits, so completion should find it unaided.
    let (problem, clause) = tester_only_clause();
    let mut e = FxHashMap::default();
    e.insert("out".to_string(), SmtValue::Bool(true));
    assert!(complete::complete_env_for_clause_with_fallback(
        &clause,
        &mut e,
        &FxHashMap::default()
    ));
    assert!(
        matches!(e.get("c"), Some(SmtValue::Datatype(ctor, _)) if ctor == "some"),
        "tester-driven completion should have instantiated `some`, got {:?}",
        e.get("c")
    );

    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: e,
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: {
                    let mut q = FxHashMap::default();
                    q.insert("out".to_string(), SmtValue::Bool(true));
                    q
                },
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    assert_eq!(validate_ground_derivation(&problem, &derivation), Ok(()));
}

#[test]
fn tester_driven_completion_cannot_manufacture_a_witness_for_a_contradiction() {
    // ANTI-FABRICATION. A clause demanding BOTH `is-some(c)` and `is-none(c)`
    // is unsatisfiable. Tester-driven completion must abstain rather than pick
    // a tag, and the resulting step must NOT validate. This is the guard that
    // stops the rule from turning "the clause says something impossible" into
    // "here is a witness for it".
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("R", vec![ChcSort::Bool]);
    let cell = ChcExpr::Var(ChcVar::new("c", option_int_sort()));
    let is_none = ChcExpr::FuncApp(
        "is-none".to_string(),
        ChcSort::Bool,
        vec![std::sync::Arc::new(cell.clone())],
    );
    let clause = HornClause::new(
        ClauseBody::constraint(ChcExpr::and(is_some(cell), is_none)),
        ClauseHead::Predicate(p, vec![var("out")]),
    );
    problem.add_clause(clause.clone());
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(p, vec![var("out")])], None),
        ClauseHead::False,
    ));

    let mut e = FxHashMap::default();
    e.insert("out".to_string(), SmtValue::Bool(true));
    // Completion may still make the environment total (via a sort default);
    // what must NOT happen is the derivation being accepted.
    complete::complete_env_for_clause_with_fallback(&clause, &mut e, &FxHashMap::default());
    let derivation = GroundDerivation {
        steps: vec![
            GroundDerivationStep {
                clause_index: 0,
                env: e,
                premises: vec![],
            },
            GroundDerivationStep {
                clause_index: 1,
                env: {
                    let mut q = FxHashMap::default();
                    q.insert("out".to_string(), SmtValue::Bool(true));
                    q
                },
                premises: vec![0],
            },
        ],
        query_step: 1,
    };
    assert!(
        validate_ground_derivation(&problem, &derivation).is_err(),
        "a contradictory clause was given a witness — tester completion fabricated"
    );
}

#[test]
fn determined_ite_normalization_exposes_the_tester_subject() {
    // The archetype's real shape: the tester's argument is an ITE, so the
    // subject is invisible until the (already determined) condition resolves.
    // `out = is-some(ite (b) c none)` with `b = true` must complete `c` to a
    // `some`, and with `b = false` must NOT — the ITE then selects `none` and
    // the clause is unsatisfiable for `out = true`.
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("R", vec![ChcSort::Bool]);
    let cell = ChcExpr::Var(ChcVar::new("c", option_int_sort()));
    let none = ChcExpr::FuncApp("none".to_string(), option_int_sort(), vec![]);
    let selected = ChcExpr::Op(
        crate::ChcOp::Ite,
        vec![
            std::sync::Arc::new(var("b")),
            std::sync::Arc::new(cell),
            std::sync::Arc::new(none),
        ],
    );
    let clause = HornClause::new(
        ClauseBody::constraint(ChcExpr::eq(var("out"), is_some(selected))),
        ClauseHead::Predicate(p, vec![var("out"), var("b")]),
    );
    problem.add_clause(clause.clone());

    let mut taken = FxHashMap::default();
    taken.insert("out".to_string(), SmtValue::Bool(true));
    taken.insert("b".to_string(), SmtValue::Bool(true));
    assert!(complete::complete_env_for_clause_with_fallback(
        &clause,
        &mut taken,
        &FxHashMap::default()
    ));
    assert!(
        matches!(taken.get("c"), Some(SmtValue::Datatype(ctor, _)) if ctor == "some"),
        "ITE normalization should have exposed `c` as the tester subject, got {:?}",
        taken.get("c")
    );
    assert_eq!(
        eval_ground_pub(clause.body.constraint.as_ref().expect("constraint"), &taken),
        Some(SmtValue::Bool(true))
    );

    // The other branch: the ITE selects `none`, so no value of `c` can make the
    // constraint hold. Completion must not pretend otherwise.
    let mut skipped = FxHashMap::default();
    skipped.insert("out".to_string(), SmtValue::Bool(true));
    skipped.insert("b".to_string(), SmtValue::Bool(false));
    complete::complete_env_for_clause_with_fallback(&clause, &mut skipped, &FxHashMap::default());
    assert_eq!(
        eval_ground_pub(
            clause.body.constraint.as_ref().expect("constraint"),
            &skipped
        ),
        Some(SmtValue::Bool(false)),
        "the unsatisfiable branch must evaluate FALSE, not be papered over"
    );
}

#[test]
fn ground_pins_refine_a_stale_carried_table() {
    // The array analogue of a stale carried value. The concretizer replaced
    // this clause's reads by their values, leaving the table unconstrained in
    // the transformed problem, so the model assigned it an empty map over the
    // sort default. The ORIGINAL clause still carries the pins, which entail
    // the table's contents exactly — so completion must refine the stale value
    // rather than trust it.
    let arr_sort = ChcSort::Array(Box::new(ChcSort::Int), Box::new(ChcSort::Int));
    let mut problem = ChcProblem::new();
    let p = problem.declare_predicate("Q", vec![ChcSort::Int]);
    let table = ChcExpr::Var(ChcVar::new("T", arr_sort));
    let clause = HornClause::new(
        ClauseBody::constraint(ChcExpr::and(
            ChcExpr::eq(
                ChcExpr::select(table.clone(), ChcExpr::Int(2)),
                ChcExpr::Int(1),
            ),
            ChcExpr::eq(var("v"), ChcExpr::Int(1)),
        )),
        ClauseHead::Predicate(p, vec![var("v")]),
    );
    problem.add_clause(clause.clone());

    let mut stale = FxHashMap::default();
    stale.insert(
        "T".to_string(),
        SmtValue::ArrayMap {
            default: Box::new(SmtValue::Int(0)),
            entries: vec![],
        },
    );
    assert!(complete::complete_env_for_clause(&clause, &mut stale));
    assert_eq!(
        eval_ground_pub(clause.body.constraint.as_ref().expect("constraint"), &stale),
        Some(SmtValue::Bool(true)),
        "the clause's own ground pin must win over a stale carried table"
    );

    // A table that already AGREES with every pin is left untouched, so nothing
    // that validates today changes.
    let agreeing = SmtValue::ArrayMap {
        default: Box::new(SmtValue::Int(0)),
        entries: vec![(SmtValue::Int(2), SmtValue::Int(1))],
    };
    let mut kept = FxHashMap::default();
    kept.insert("T".to_string(), agreeing.clone());
    assert!(complete::complete_env_for_clause(&clause, &mut kept));
    assert_eq!(kept.get("T"), Some(&agreeing));
}
