// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Datatype sorts in the identity: by reference, linear, injective, versioned.
#![cfg(test)]

use super::*;
use crate::{ChcDtConstructor, ChcDtConstructors, ChcDtSelector, ChcVar, ClauseBody};

fn datatype(name: &str, constructor: &str, fields: Vec<(String, ChcSort)>) -> ChcSort {
    ChcSort::Datatype {
        name: name.to_string(),
        constructors: ChcDtConstructors::new(vec![ChcDtConstructor {
            name: constructor.to_string(),
            selectors: fields
                .into_iter()
                .map(|(name, sort)| ChcDtSelector { name, sort })
                .collect(),
        }]),
    }
}

/// `D0 = leaf`, `Dk = { ak: D(k-1), bk: D(k-1) }`: `O(k)` type text and `2^k`
/// leaves. `rename` renames the datatype at one level.
fn struct_dag(k: usize, leaf: ChcSort, rename: Option<usize>) -> ChcSort {
    let mut sort = leaf;
    for level in 1..=k {
        let name = if rename == Some(level) {
            format!("Renamed{level}")
        } else {
            format!("D{level}")
        };
        sort = datatype(
            &name,
            &format!("mk{level}"),
            vec![
                (format!("a{level}"), sort.clone()),
                (format!("b{level}"), sort),
            ],
        );
    }
    sort
}

fn dag(k: usize) -> ChcSort {
    struct_dag(k, ChcSort::BitVec(32), None)
}

/// model-checker-consumer's measured shape: one predicate over `Dk`, one fact, one query.
fn single_variable_problem(sort: ChcSort) -> ChcProblem {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("bb0", vec![sort.clone()]);
    let x = ChcVar::new("x", sort);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(predicate, vec![ChcExpr::var(x.clone())]),
    ));
    problem.add_clause(HornClause::new(
        ClauseBody::new(vec![(predicate, vec![ChcExpr::var(x)])], None),
        ClauseHead::False,
    ));
    problem
}

fn definition_lines(text: &str) -> usize {
    text.lines()
        .filter(|line| line.starts_with("constructors @"))
        .count()
}

#[test]
fn k_nested_struct_identity_grows_linearly_in_k() {
    // Inline spelling grew 4x per k += 2 (8.4 MB for one variable at k = 16).
    // By reference, each level adds one definition line, and at k = 48 the
    // tree expansion (2^48 leaves) is never walked.
    let sizes: Vec<usize> = (1..=48)
        .map(|k| input(&single_variable_problem(dag(k))).len())
        .collect();
    for k in 2..=48 {
        let step = sizes[k - 1] - sizes[k - 2];
        assert!(step <= 300, "k={k}: identity grew by {step} bytes");
    }
    assert!(sizes[47] <= sizes[0] + 47 * 300);
    for k in [1, 16, 48] {
        let problem = single_variable_problem(dag(k));
        let text = input(&problem);
        assert!(text
            .starts_with("ay.chc.normalized-input/v2\nfixedpoint=false\ndatatype-constructors\n"));
        // Each level's constructor list is defined exactly once.
        assert_eq!(definition_lines(&text), k, "k={k}");
        assert_oracle(&problem);
    }
}

#[test]
fn hashing_the_identity_polls_linearly_in_k() {
    // Every node and byte chunk of the identity reaches a poll, so the poll
    // count measures the identity's work.
    let polls = |k: usize| {
        let mut calls = 0usize;
        normalized_chc_input_sha256_with_progress(&single_variable_problem(dag(k)), &mut || {
            calls += 1;
            true
        })
        .expect("unlimited");
        calls
    };
    let (at_16, at_32, at_48) = (polls(16), polls(32), polls(48));
    assert_eq!(at_48 - at_32, at_32 - at_16);
}

#[test]
fn equal_problems_built_independently_have_one_identity() {
    let first = single_variable_problem(dag(12));
    let second = single_variable_problem(dag(12));
    assert_eq!(input(&first), input(&second));
    assert_eq!(input_hash(&first), input_hash(&second));
    assert_eq!(ordered_hash(&first), ordered_hash(&second));
}

#[test]
fn every_nested_difference_changes_both_identities() {
    let base = single_variable_problem(dag(10));
    let variants = [
        ("leaf width", struct_dag(10, ChcSort::BitVec(31), None)),
        ("leaf sort", struct_dag(10, ChcSort::Int, None)),
        (
            "inner datatype name",
            struct_dag(10, ChcSort::BitVec(32), Some(3)),
        ),
        (
            "outer datatype name",
            struct_dag(10, ChcSort::BitVec(32), Some(10)),
        ),
        ("one level fewer", dag(9)),
        (
            "uninterpreted with the same name",
            ChcSort::Uninterpreted("D10".to_string()),
        ),
        (
            "same name, other definition",
            datatype("D10", "mk10", vec![("a10".to_string(), dag(9))]),
        ),
        (
            "selector renamed under the same names",
            datatype(
                "D10",
                "mk10",
                vec![("a10".to_string(), dag(9)), ("c10".to_string(), dag(9))],
            ),
        ),
    ];
    let mut inputs = vec![("base", input_hash(&base), ordered_hash(&base))];
    for (label, sort) in variants {
        let problem = single_variable_problem(sort);
        assert_oracle(&problem);
        inputs.push((label, input_hash(&problem), ordered_hash(&problem)));
    }
    for (i, (left, left_input, left_ordered)) in inputs.iter().enumerate() {
        for (right, right_input, right_ordered) in &inputs[i + 1..] {
            assert_ne!(left_input, right_input, "{left} vs {right}");
            assert_ne!(left_ordered, right_ordered, "{left} vs {right}");
        }
    }
}

#[test]
fn input_without_datatype_sorts_keeps_v1_and_its_bytes() {
    let mut problem = ChcProblem::new();
    let predicate = problem.declare_predicate("P", vec![ChcSort::Int]);
    let x = ChcVar::new("x", ChcSort::Int);
    problem.add_clause(HornClause::new(
        ClauseBody::empty(),
        ClauseHead::Predicate(predicate, vec![ChcExpr::var(x)]),
    ));
    // A registry entry whose selectors are all scalar references no
    // datatype sort, so the spelling is unchanged.
    problem.add_datatype_def(
        "Box".to_string(),
        vec![("mk".to_string(), vec![("v".to_string(), ChcSort::Int)])],
    );
    let text = input(&problem);
    assert_eq!(
        text,
        "ay.chc.normalized-input/v1\nfixedpoint=false\ndatatypes\n\
         datatype \"Box\"=\"mk\"(\"v\":Int)\nactions\npredicates\n\
         predicate p0 name=\"P\" args=[Int]\nclauses\n\
         clause action=none body=[] constraint=true head=p0(var:\"x\":Int)\n"
    );
    assert_eq!(
        crate::normalized_chc_input_schema_of(&text),
        Some(crate::NORMALIZED_CHC_INPUT_SCHEMA)
    );
    assert_oracle(&problem);
}

#[test]
fn a_datatype_anywhere_in_the_input_selects_the_v2_normalized_input() {
    let leaf = datatype("Leaf", "leaf", Vec::new());
    // Only in the registry's selector sorts. (The clause-sequence overlay
    // spells clauses and predicate signatures only, so it stays v1 here.)
    let mut registry_only = ChcProblem::new();
    registry_only.add_datatype_def(
        "Box".to_string(),
        vec![("mk".to_string(), vec![("v".to_string(), leaf.clone())])],
    );
    let text = input(&registry_only);
    assert_eq!(
        crate::normalized_chc_input_schema_of(&text),
        Some(crate::NORMALIZED_CHC_INPUT_DATATYPE_REFERENCE_SCHEMA)
    );
    assert_eq!(definition_lines(&text), 1);
    assert_oracle(&registry_only);
    // Only inside an array sort in a clause constraint.
    let mut nested = ChcProblem::new();
    push_raw(
        &mut nested,
        HornClause::query(ClauseBody::constraint(ChcExpr::FuncApp(
            "inspect".to_string(),
            ChcSort::Bool,
            vec![Arc::new(ChcExpr::var(ChcVar::new(
                "cells",
                ChcSort::Array(Box::new(ChcSort::Int), Box::new(leaf)),
            )))],
        ))),
    );
    assert!(input(&nested).starts_with("ay.chc.normalized-input/v2\n"));
    assert_oracle(&nested);
}

#[test]
fn a_standalone_sort_spells_its_reference() {
    let d3 = dag(3);
    let ChcSort::Datatype { constructors, .. } = &d3 else {
        unreachable!()
    };
    assert_eq!(
        super::super::sort(&d3),
        format!("Datatype(\"D3\";@{})", constructors.id())
    );
}
