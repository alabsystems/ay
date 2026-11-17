// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::acceptance_inventory::r34::tests::{fixture, original};
use ay_chc::{ChcExpr, ChcParser, ChcSort, ChcVar, ClauseHead, PdrConfig};
use std::collections::btree_map::Entry;
use std::time::Duration;

fn inspect(archive: &R34Archive, case: R34Witness) -> R34WitnessBinding {
    let guard = original();
    let mut config = PdrConfig::production(false).with_memory_budget(Some(64 * 1024 * 1024));
    config.solve_timeout = Some(Duration::from_secs(15));
    let owner = ExternalInvariantValidationOwner::capture(&guard, &config);
    let binding = archive.inspect_witness(case, &owner).unwrap();
    assert!(binding
        .blockers
        .contains(&R34WitnessBlocker::MissingOriginalRemainingBudget));
    assert!(!binding.solver_invoked && !binding.promotable_for_ask_closure);
    binding
}

fn aggregate(archive: &R34Archive) -> ChcProblem {
    let mut problem = capture::parse_source(archive, &archive.capture.sources["static"]).unwrap();
    problem.expand_nullary_fail_queries(false);
    problem
}

fn simple() -> ChcProblem {
    ChcParser::parse(
        "(set-logic HORN) (declare-rel p (Int))
        (declare-var x Int) (rule (p x)) (rule (=> (p x) false))",
    )
    .unwrap()
}

#[test]
fn both_real_constructor_invocations_bind_unique_fact_and_complete_v1_query() {
    let archive = fixture();
    for case in [R34Witness::Static0001, R34Witness::Static0003] {
        let binding = inspect(&archive, case);
        assert_eq!(binding.predecessor_fact_indices, vec![0]);
        assert!(binding.historical_query_authenticated);
        assert_eq!(binding.datatype_definitions, 7);
        assert!(binding.current_query_sha256.is_some());
        assert!(!binding
            .blockers
            .contains(&R34WitnessBlocker::MissingPredecessorFactRecipe));
        assert!(!binding.blockers.iter().any(|b| matches!(
            b,
            R34WitnessBlocker::ReconstructionError { .. } | R34WitnessBlocker::OwnerRefused { .. }
        )));
        // The capture's `{formula:?}` digest predates 98d0c3224, which prints
        // a datatype sort's constructors as an interned identity, so the
        // current format stays a visible migration. In the historical format
        // it matches the recipe and not the bare constraint (test below).
        assert!(binding
            .blockers
            .iter()
            .any(|b| matches!(b, R34WitnessBlocker::FormulaDebugIdentity { .. })));
    }
}

#[test]
fn actual_constructor_recipe_contains_every_typed_predecessor_equality() {
    let archive = fixture();
    let problem = aggregate(&archive);
    let facts::Recipe::Ready {
        formula,
        predecessors,
    } = facts::reconstruct(&problem, 14, &mut || true).unwrap()
    else {
        panic!("recipe")
    };
    assert_eq!(predecessors, vec![0]);
    let clause = &problem.clauses()[14];
    let fact = &problem.clauses()[0];
    let ClauseHead::Predicate(_, args) = &fact.head else {
        panic!("fact")
    };
    assert_eq!(clause.body.predicates.len(), 1);
    assert_eq!(args.len(), 26);
    let mut exact: Vec<_> = fact.body.constraint.iter().cloned().collect();
    exact.extend(
        clause.body.predicates[0]
            .1
            .iter()
            .zip(args)
            .map(|(left, right)| ChcExpr::eq(left.clone(), right.clone())),
    );
    exact.extend(clause.body.constraint.iter().cloned());
    assert_eq!(formula, ChcExpr::and_all(exact));
    // The consumer's constraint query over this formula is, byte for byte,
    // the archived v1 witness query.
    let mut query = ChcProblem::new();
    for (name, constructors) in problem.datatype_defs() {
        query.add_datatype_def(name.clone(), constructors.clone());
    }
    query.add_clause(HornClause::query(ClauseBody::constraint(formula)));
    assert_eq!(
        query
            .normalized_input_v1_with_progress(&mut || true)
            .unwrap(),
        include_str!("../../fixtures/static-0001.normalized")
    );
}

#[test]
fn archived_witness_byte_or_digest_mutation_cannot_authenticate() {
    for mutate_bytes in [true, false] {
        let mut archive = fixture();
        if mutate_bytes {
            let witness = &archive.capture.witnesses[0];
            let path = format!(
                "{}/{}",
                archive.capture.sources["static"].base,
                capture::string(&witness.record["constraint_query"], "file").unwrap()
            );
            archive.files.get_mut(&path).unwrap().push(b' ');
        } else {
            archive.capture.witnesses[0].record["constraint_query"]["normalized_input_sha256"] =
                "0".repeat(64).into();
        }
        let binding = inspect(&archive, R34Witness::Static0001);
        assert!(!binding.historical_query_authenticated);
        assert!(binding.current_query_sha256.is_none());
        assert!(binding
            .blockers
            .iter()
            .any(|b| matches!(b, R34WitnessBlocker::ReconstructionError { .. })));
    }
}

#[test]
fn source_byte_mutation_cannot_be_hidden_by_matching_witness_bytes() {
    let mut archive = fixture();
    let source = &archive.capture.sources["static"];
    let path = format!(
        "{}/{}",
        source.base,
        capture::string(&source.source, "file").unwrap()
    );
    archive.files.get_mut(&path).unwrap().push(b' ');
    let binding = inspect(&archive, R34Witness::Static0001);
    assert!(!binding.historical_query_authenticated);
    assert!(binding.current_query_sha256.is_none());
    assert!(binding.blockers.iter().any(|b| matches!(b,
        R34WitnessBlocker::ReconstructionError { reason } if reason.contains("source bytes identity"))));
}

#[test]
fn wrong_clause_or_aggregate_recipe_never_uses_a_hash_alias() {
    for change_index in [true, false] {
        let mut archive = fixture();
        if change_index {
            archive.capture.witnesses[0].record["clause_index"] = 0.into();
        } else {
            archive
                .capture
                .sources
                .get_mut("static")
                .unwrap()
                .aggregate_problem["passes"]["transforms"]["enabled"] = true.into();
        }
        let binding = inspect(&archive, R34Witness::Static0001);
        assert!(binding.current_query_sha256.is_none());
        assert!(!binding.historical_query_authenticated);
    }
}

#[test]
fn ambiguous_recursive_later_or_missing_source_fact_refuses() {
    for variant in 0..4 {
        let mut problem = simple();
        match variant {
            0 => problem.add_clause(problem.clauses()[0].clone()),
            1 => problem.clauses_mut()[0].body = problem.clauses()[1].body.clone(),
            2 => problem.clauses_mut().swap(0, 1),
            _ => problem.clauses_mut()[0].head = ClauseHead::False,
        }
        let index = if variant == 2 { 0 } else { 1 };
        assert!(
            matches!(
                facts::reconstruct(&problem, index, &mut || true).unwrap(),
                facts::Recipe::Missing
            ),
            "variant {variant}"
        );
    }
}

#[test]
fn malformed_argument_arity_and_same_name_wrong_sort_refuse() {
    for wrong_sort in [false, true] {
        let mut problem = simple();
        let args = &mut problem.clauses_mut()[1].body.predicates[0].1;
        if wrong_sort {
            args[0] = ChcExpr::var(ChcVar::new("x", ChcSort::Bool));
        } else {
            args.clear();
        }
        assert!(matches!(
            facts::reconstruct(&problem, 1, &mut || true).unwrap(),
            facts::Recipe::Missing
        ));
    }
}

#[test]
fn ordered_predicate_arguments_are_not_name_projected_or_dropped() {
    let mut problem = ChcParser::parse(
        "(set-logic HORN) (declare-rel p (Int Int))
        (declare-var x Int) (declare-var y Int) (rule (p x y))
        (rule (=> (p y x) false))",
    )
    .unwrap();
    let facts::Recipe::Ready { formula, .. } =
        facts::reconstruct(&problem, 1, &mut || true).unwrap()
    else {
        panic!("recipe")
    };
    let x = ChcExpr::var(ChcVar::new("x", ChcSort::Int));
    let y = ChcExpr::var(ChcVar::new("y", ChcSort::Int));
    assert_eq!(
        formula,
        ChcExpr::and_all([
            ChcExpr::eq(y.clone(), x.clone()),
            ChcExpr::eq(x.clone(), y.clone())
        ])
    );
    problem.clauses_mut()[1].body.predicates[0].1.swap(0, 1);
    let facts::Recipe::Ready {
        formula: changed, ..
    } = facts::reconstruct(&problem, 1, &mut || true).unwrap()
    else {
        panic!("recipe")
    };
    assert_ne!(formula, changed);
}

#[test]
fn every_recipe_poll_refuses_immediately_without_an_extra_callback() {
    let problem = aggregate(&fixture());
    let mut total = 0;
    assert!(matches!(
        facts::reconstruct(&problem, 14, &mut || {
            total += 1;
            true
        })
        .unwrap(),
        facts::Recipe::Ready { .. }
    ));
    assert!(total > 26);
    for stop in 1..=total {
        let mut polls = 0;
        let result = facts::reconstruct(&problem, 14, &mut || {
            polls += 1;
            assert!(polls <= stop, "callback after refusal");
            polls != stop
        })
        .unwrap();
        assert!(matches!(result, facts::Recipe::Stopped));
        assert_eq!(polls, stop);
    }
}

/// `{formula:?}` as printed by the capture's AY revision (48c98a43d): before
/// 98d0c3224 a datatype sort printed its constructor list, not its interned
/// content identity. Every other derived `Debug` is unchanged; an identity
/// this walk did not map panics instead of being skipped.
fn historical_debug(formula: &ChcExpr) -> String {
    fn sorts(sort: &ChcSort, lists: &mut std::collections::BTreeMap<String, String>) {
        match sort {
            ChcSort::Datatype { constructors, .. } => {
                let identity = format!("{constructors:?}");
                if let Entry::Vacant(entry) = lists.entry(identity) {
                    entry.insert(format!("{:?}", **constructors));
                    for selector in constructors.iter().flat_map(|c| &c.selectors) {
                        sorts(&selector.sort, lists);
                    }
                }
            }
            ChcSort::Array(key, value) => {
                sorts(key, lists);
                sorts(value, lists);
            }
            _ => {}
        }
    }
    fn exprs(expr: &ChcExpr, lists: &mut std::collections::BTreeMap<String, String>) {
        sorts(&expr.sort(), lists);
        match expr {
            ChcExpr::Var(var) => sorts(&var.sort, lists),
            ChcExpr::FuncApp(_, sort, args) => {
                sorts(sort, lists);
                for arg in args {
                    exprs(arg, lists);
                }
            }
            ChcExpr::Op(_, args) | ChcExpr::PredicateApp(_, _, args) => {
                for arg in args {
                    exprs(arg, lists);
                }
            }
            _ => {}
        }
    }
    fn expand(text: &str, lists: &std::collections::BTreeMap<String, String>) -> String {
        let mut out = String::new();
        let mut rest = text;
        while let Some(start) = rest.find("ChcDtConstructors(@") {
            let end = start + rest[start..].find(')').unwrap() + 1;
            out.push_str(&rest[..start]);
            out.push_str(&expand(&lists[&rest[start..end]], lists));
            rest = &rest[end..];
        }
        out.push_str(rest);
        out
    }
    let mut lists = std::collections::BTreeMap::new();
    exprs(formula, &mut lists);
    expand(&format!("{formula:?}"), &lists)
}

#[test]
fn captured_formula_debug_digest_authenticates_the_recipe_not_the_bare_constraint() {
    let archive = fixture();
    let problem = aggregate(&archive);
    let facts::Recipe::Ready { formula, .. } =
        facts::reconstruct(&problem, 14, &mut || true).unwrap()
    else {
        panic!("recipe")
    };
    // Counterfactual: the bare clause14 constraint the original code refused
    // to substitute. Its complete v1 query bytes are identical (all 26
    // predecessor equalities are reflexive and simplify away), so only the
    // archived formula digest tells the two apart.
    let bare = ChcExpr::and_all(problem.clauses()[14].body.constraint.iter().cloned());
    let mut query = ChcProblem::new();
    for (name, constructors) in problem.datatype_defs() {
        query.add_datatype_def(name.clone(), constructors.clone());
    }
    query.add_clause(HornClause::query(ClauseBody::constraint(bare.clone())));
    assert_eq!(
        query
            .normalized_input_v1_with_progress(&mut || true)
            .unwrap(),
        include_str!("../../fixtures/static-0001.normalized")
    );
    for witness in &archive.capture.witnesses[..2] {
        let captured = capture::string(&witness.record, "formula_debug_sha256").unwrap();
        assert_eq!(
            capture::digest(historical_debug(&formula).as_bytes()),
            captured
        );
        assert_ne!(
            capture::digest(historical_debug(&bare).as_bytes()),
            captured
        );
    }
}
