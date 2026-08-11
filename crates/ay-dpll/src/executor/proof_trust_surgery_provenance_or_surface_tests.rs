// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Surface-shape policy tests for provenance-authenticated OR repair.

use ay_frontend::command::{Sort as FrontendSort, Term as FrontendTerm};

use super::super::proof_trust_surgery_provenance::{
    surface_arithmetic_ite_matches, surface_or_decomposition_matches,
};
use super::{declare_fixture_const, Executor};

#[test]
fn or_unit_surface_gate_rejects_implication_and_nested_or() {
    let mut executor = Executor::new();
    let a = declare_fixture_const(
        &mut executor,
        "surface_a",
        FrontendSort::Simple("Bool".to_string()),
    );
    let b = declare_fixture_const(
        &mut executor,
        "surface_b",
        FrontendSort::Simple("Bool".to_string()),
    );
    let c = declare_fixture_const(
        &mut executor,
        "surface_c",
        FrontendSort::Simple("Bool".to_string()),
    );
    let canonical = executor.ctx.terms.mk_or(vec![a, b, c]);
    let ay_core::TermData::App(_, disjuncts) = executor.ctx.terms.get(canonical).clone() else {
        panic!("fixture OR must remain an application");
    };
    let implication = FrontendTerm::App(
        "=>".to_string(),
        vec![
            FrontendTerm::Symbol("surface_a".to_string()),
            FrontendTerm::Symbol("surface_b".to_string()),
        ],
    );
    let implication_canonical = executor
        .ctx
        .elaborate_surface_subterm(&implication)
        .expect("implication fixture elaborates");
    let ay_core::TermData::App(_, implication_disjuncts) =
        executor.ctx.terms.get(implication_canonical).clone()
    else {
        panic!("implication must elaborate to an OR");
    };
    let nested = FrontendTerm::App(
        "or".to_string(),
        vec![
            FrontendTerm::Symbol("surface_a".to_string()),
            FrontendTerm::App(
                "or".to_string(),
                vec![
                    FrontendTerm::Symbol("surface_b".to_string()),
                    FrontendTerm::Symbol("surface_c".to_string()),
                ],
            ),
        ],
    );
    let let_operand = FrontendTerm::App(
        "or".to_string(),
        vec![
            FrontendTerm::Let(
                vec![(
                    "z".to_string(),
                    FrontendTerm::Symbol("surface_a".to_string()),
                )],
                Box::new(FrontendTerm::Symbol("z".to_string())),
            ),
            FrontendTerm::Symbol("surface_b".to_string()),
        ],
    );
    let binary = executor.ctx.terms.mk_or(vec![a, b]);
    let ay_core::TermData::App(_, binary_disjuncts) = executor.ctx.terms.get(binary).clone() else {
        panic!("binary OR fixture must remain an application");
    };
    assert!(!surface_or_decomposition_matches(
        &mut executor.ctx,
        &implication,
        &implication_disjuncts,
    ));
    assert!(!surface_or_decomposition_matches(
        &mut executor.ctx,
        &nested,
        &disjuncts,
    ));
    assert!(!surface_or_decomposition_matches(
        &mut executor.ctx,
        &let_operand,
        &binary_disjuncts,
    ));
}

#[test]
fn arithmetic_ite_surface_gate_rejects_let_condition() {
    let mut executor = Executor::new();
    let _p = declare_fixture_const(
        &mut executor,
        "ite_surface_p",
        FrontendSort::Simple("Bool".to_string()),
    );
    let _x = declare_fixture_const(
        &mut executor,
        "ite_surface_x",
        FrontendSort::Simple("Int".to_string()),
    );
    let _y = declare_fixture_const(
        &mut executor,
        "ite_surface_y",
        FrontendSort::Simple("Int".to_string()),
    );
    let parsed = FrontendTerm::App(
        "ite".to_string(),
        vec![
            FrontendTerm::Let(
                vec![(
                    "z".to_string(),
                    FrontendTerm::Symbol("ite_surface_p".to_string()),
                )],
                Box::new(FrontendTerm::Symbol("z".to_string())),
            ),
            FrontendTerm::App(
                "<".to_string(),
                vec![
                    FrontendTerm::Symbol("ite_surface_x".to_string()),
                    FrontendTerm::Symbol("ite_surface_y".to_string()),
                ],
            ),
            FrontendTerm::App(
                "<".to_string(),
                vec![
                    FrontendTerm::Symbol("ite_surface_y".to_string()),
                    FrontendTerm::Symbol("ite_surface_x".to_string()),
                ],
            ),
        ],
    );
    let canonical = executor
        .ctx
        .elaborate_surface_subterm(&parsed)
        .expect("ITE fixture elaborates");
    let ay_core::TermData::Ite(cond, then_term, else_term) = *executor.ctx.terms.get(canonical)
    else {
        panic!("fixture must remain an ITE");
    };
    assert!(!surface_arithmetic_ite_matches(
        &mut executor.ctx,
        &parsed,
        &[cond, then_term, else_term],
    ));
}
