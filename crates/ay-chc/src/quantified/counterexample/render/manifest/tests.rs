// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::quantified::QuantifiedHornClause;
use crate::{CancellationToken, ChcOp, ChcProblem, ChcSort, ClauseBody};
use ay_core::time::Instant;
use std::sync::Arc;
use std::time::Duration;

fn variable(name: &str, sort: ChcSort) -> ChcExpr {
    ChcExpr::Var(ChcVar::new(name, sort))
}

fn operation(op: ChcOp, args: Vec<ChcExpr>) -> ChcExpr {
    ChcExpr::Op(op, args.into_iter().map(Arc::new).collect())
}

fn premise() -> UniversalPremise {
    let i = ChcVar::new("i", ChcSort::BitVec(2));
    let reserved = ChcVar::new("ay_qcex_0", ChcSort::BitVec(2));
    UniversalPremise::with_binders(
        vec![i.clone(), reserved.clone()],
        operation(
            ChcOp::Implies,
            vec![
                operation(ChcOp::Eq, vec![ChcExpr::Var(i), ChcExpr::Var(reserved)]),
                variable("matrix", ChcSort::Bool),
            ],
        ),
    )
    .unwrap()
}

fn source() -> QuantifiedChcProblem {
    let mut declarations = ChcProblem::new();
    let p = declarations.declare_predicate("P", vec![ChcSort::BitVec(2)]);
    let x = variable("x", ChcSort::BitVec(2));
    let y = variable("y", ChcSort::BitVec(2));
    QuantifiedChcProblem::new(
        declarations,
        vec![
            QuantifiedHornClause::new(
                HornClause::fact(variable("i", ChcSort::Bool), p, vec![x.clone()]),
                vec![premise()],
            ),
            QuantifiedHornClause::new(
                HornClause::query(ClauseBody::new(
                    vec![(p, vec![x]), (p, vec![y])],
                    Some(variable("i", ChcSort::Bool)),
                )),
                vec![premise()],
            ),
        ],
    )
    .unwrap()
}

fn control(token: &CancellationToken) -> SourceControl<'_> {
    SourceControl::new(Instant::now() + Duration::from_secs(30), token)
}

fn rendered<'a>(source: &'a QuantifiedChcProblem, token: &CancellationToken) -> Rendered<'a> {
    render_with_bindings(
        source,
        &[0, 0, 1],
        &[vec![], vec![], vec![0, 1]],
        &control(token),
    )
    .unwrap()
}

#[test]
fn every_occurrence_keeps_exact_free_local_membership_and_independent_symbols() {
    let source = source();
    let token = CancellationToken::new();
    let result = rendered(&source, &token);
    let actual: Vec<_> = result
        .bindings
        .iter()
        .map(|binding| (binding.occurrence, binding.variable.name.as_str()))
        .collect();
    assert_eq!(
        actual,
        vec![
            (0, "i"),
            (0, "matrix"),
            (0, "x"),
            (1, "i"),
            (1, "matrix"),
            (1, "x"),
            (2, "i"),
            (2, "matrix"),
            (2, "x"),
            (2, "y"),
        ]
    );
    let ClauseHead::Predicate(_, args) = &source.source_problem().clauses()[0].head else {
        panic!("source fact");
    };
    let ChcExpr::Var(original_x) = &args[0] else {
        panic!("source formal");
    };
    assert!(std::ptr::eq(result.bindings[2].variable, original_x));
    assert!(std::ptr::eq(result.bindings[5].variable, original_x));
    for (index, binding) in result.bindings.iter().enumerate() {
        assert_eq!(binding.symbol, format!("ay_qcex_{}", index + 1));
        assert_eq!(
            result
                .obligation
                .matches(&format!("(declare-const {} ", binding.symbol))
                .count(),
            1,
        );
    }
    assert_eq!(result.obligation.matches("(declare-const ").count(), 10);
}

#[test]
fn lexical_binders_are_not_assignments_but_same_named_outer_values_remain() {
    let source = source();
    let token = CancellationToken::new();
    let result = rendered(&source, &token);
    assert!(result.bindings.iter().all(|binding| {
        binding.variable.name != "ay_qcex_0"
            && (binding.variable.name != "i" || binding.variable.sort == ChcSort::Bool)
    }));
    assert_eq!(
        result
            .bindings
            .iter()
            .filter(|binding| binding.variable.name == "i")
            .count(),
        3
    );
    assert_eq!(
        result
            .bindings
            .iter()
            .filter(|binding| binding.variable.name == "matrix")
            .count(),
        3
    );
    assert_eq!(
        result
            .obligation
            .matches("(forall ((i (_ BitVec 2))(ay_qcex_0 (_ BitVec 2)))")
            .count(),
        3,
    );
}

#[test]
fn manifest_and_ordinary_rendering_have_identical_bytes_and_terminal_controls() {
    let source = source();
    let token = CancellationToken::new();
    let result = rendered(&source, &token);
    assert_eq!(
        result.obligation,
        render_derivation(
            &source,
            &[0, 0, 1],
            &[vec![], vec![], vec![0, 1]],
            &control(&token)
        )
        .unwrap(),
    );
    let stopped = control(&token);
    token.cancel();
    assert!(
        render_with_bindings(&source, &[0, 0, 1], &[vec![], vec![], vec![0, 1]], &stopped).is_err()
    );
    token.reset();
    assert!(
        render_with_bindings(&source, &[0, 0, 1], &[vec![], vec![], vec![0, 1]], &stopped).is_err()
    );
    assert_eq!(rendered(&source, &token).bindings.len(), 10);
}

#[test]
fn flattening_moves_spelling_and_prepays_exact_binding_storage() {
    let token = CancellationToken::new();
    let variable = ChcVar::new("local", ChcSort::Bool);
    let charge = 128 + std::mem::size_of::<Binding<'_>>();
    for allowance in [charge - 1, charge] {
        let control = control(&token);
        control.bytes(64 * 1024 * 1024 - allowance).unwrap();
        let symbol = String::from("ay_qcex_7");
        let allocation = symbol.as_ptr();
        let result = retain(
            String::new(),
            vec![Scope {
                variables: vec![(&variable, symbol)],
            }],
            0..0,
            &control,
        );
        if allowance == charge {
            let result = result.unwrap();
            assert_eq!(result.bindings.len(), 1);
            assert_eq!(result.bindings[0].symbol.as_ptr(), allocation);
            assert!(control.poll().is_some());
        } else {
            assert!(result.is_err());
            assert!(control.poll().is_none());
        }
    }
}

#[test]
fn function_free_source_keeps_an_empty_structural_declaration_interval() {
    let source = source();
    let token = CancellationToken::new();
    let result = rendered(&source, &token);
    assert!(result.function_declarations.is_empty());
    assert!(result.obligation[result.function_declarations.end..].starts_with("(declare-const "));
}
