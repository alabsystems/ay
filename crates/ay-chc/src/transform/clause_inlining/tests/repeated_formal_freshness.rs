// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Synthetic RefCell-style positional regressions, not retained producer VCs.
//!
//! The array between repeated scalar positions models the relevant source
//! shape. Bool indices make all array interpretations exhaustively enumerable;
//! this is not a claim that the retained RefCell VC uses Bool-indexed arrays.

#![cfg(test)]

use super::*;
use crate::pdr::model::PredicateInterpretation;
use crate::transform::ValidityWitness;
use crate::SmtValue;

mod evaluation;
mod fixtures;

fn reconstruct(original: &ChcProblem, predicate: PredicateId) -> PredicateInterpretation {
    original.validate().expect("well-typed original source");
    let TransformationResult {
        problem: transformed,
        back_translator,
    } = Box::new(ClauseInliner::new()).transform(original.clone());
    transformed
        .validate()
        .expect("well-typed transformed source");
    assert!(
        transformed.predicates().is_empty(),
        "P must actually be inlined"
    );
    for clause in transformed.clauses() {
        assert!(clause.is_query());
        assert_eq!(
            clause.body.predicates,
            [] as [(PredicateId, Vec<ChcExpr>); 0]
        );
        let folded = clause
            .body
            .constraint
            .clone()
            .unwrap_or(ChcExpr::Bool(true))
            // Bool/array var=var aliases need the general alias pass;
            // into_propagate_equalities alone only propagates Int constants.
            .propagate_constants()
            .into_propagate_equalities()
            .simplify_constants();
        assert_eq!(
            folded,
            ChcExpr::Bool(false),
            "empty model must satisfy every residual query"
        );
    }
    // This empty witness is a model of the transformed source, established
    // above; it is not an arbitrary interpretation passed to a private helper.
    let translated = back_translator.translate_validity(ValidityWitness::new());
    assert_eq!(translated.len(), original.predicates().len());
    let interpretation = translated
        .get(&predicate)
        .expect("restore original predicate ID");
    let source = original.get_predicate(predicate).unwrap();
    assert_eq!(
        interpretation
            .vars
            .iter()
            .map(|var| var.sort.clone())
            .collect::<Vec<_>>(),
        source.arg_sorts
    );
    let names: FxHashSet<_> = interpretation
        .vars
        .iter()
        .map(|var| var.name.as_str())
        .collect();
    assert_eq!(
        names.len(),
        interpretation.vars.len(),
        "each position needs its own name"
    );
    let allowed: FxHashSet<_> = interpretation.vars.iter().cloned().collect();
    assert!(
        interpretation
            .formula
            .vars()
            .iter()
            .all(|var| allowed.contains(var)),
        "no clause-local witness may escape"
    );
    interpretation.clone()
}

#[test]
fn later_head_name_cannot_capture_a_repeated_formal_across_an_array_column() {
    let (original, predicate) = fixtures::head_collision();
    let interpretation = reconstruct(&original, predicate);
    let mut accepted = 0;
    for mask in 0_u8..32 {
        let at_false = mask & 1 != 0;
        let at_true = mask & 2 != 0;
        let first = mask & 4 != 0;
        let repeated = mask & 8 != 0;
        let last = mask & 16 != 0;
        let expected = first == repeated && !last && at_false == first;
        let actual = evaluation::apply(
            &interpretation,
            &[
                SmtValue::Bool(first),
                evaluation::array(at_false, at_true),
                SmtValue::Bool(repeated),
                SmtValue::Bool(last),
            ],
        );
        assert_eq!(actual, expected, "head-collision tuple {mask:05b}");
        accepted += usize::from(actual);
    }
    assert_eq!(accepted, 4);
    // Both sides of the old positional alias: it discarded this valid tuple
    // and admitted the following unequal first/repeated arguments.
    assert!(evaluation::apply(
        &interpretation,
        &[
            SmtValue::Bool(true),
            evaluation::array(true, false),
            SmtValue::Bool(true),
            SmtValue::Bool(false),
        ]
    ));
    assert!(!evaluation::apply(
        &interpretation,
        &[
            SmtValue::Bool(false),
            evaluation::array(false, false),
            SmtValue::Bool(true),
            SmtValue::Bool(false),
        ]
    ));
}

#[test]
fn clause_local_dedup_name_remains_existential_in_the_reconstructed_witness() {
    let (original, predicate) = fixtures::body_collision();
    let interpretation = reconstruct(&original, predicate);
    let mut accepted = 0;
    for mask in 0_u8..16 {
        let at_false = mask & 1 != 0;
        let at_true = mask & 2 != 0;
        let first = mask & 4 != 0;
        let repeated = mask & 8 != 0;
        // Existential local z satisfies z=!first and z=true. It must not
        // become the repeated head position merely because its name collides.
        let expected = !first && first == repeated && !at_false;
        let actual = evaluation::apply(
            &interpretation,
            &[
                SmtValue::Bool(first),
                evaluation::array(at_false, at_true),
                SmtValue::Bool(repeated),
            ],
        );
        assert_eq!(actual, expected, "body-collision tuple {mask:04b}");
        accepted += usize::from(actual);
    }
    assert_eq!(
        accepted, 2,
        "projection must retain the two genuine source tuples"
    );
    assert!(evaluation::apply(
        &interpretation,
        &[
            SmtValue::Bool(false),
            evaluation::array(false, true),
            SmtValue::Bool(false),
        ]
    ));
    assert!(!evaluation::apply(
        &interpretation,
        &[
            SmtValue::Bool(false),
            evaluation::array(false, true),
            SmtValue::Bool(true),
        ]
    ));
}
