// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact authority tests for raw arithmetic defining-equality aliases.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{Sort, Symbol, TermId};
use ay_frontend::command::{
    Command, Constant as FrontendConstant, Sort as FrontendSort, Term as FrontendTerm,
};

use super::ProvenanceSurfaceAudit;
use crate::executor::Executor;

fn declare(executor: &mut Executor, name: &str, sort: &str) -> TermId {
    executor
        .ctx
        .process_command(&Command::DeclareConst(
            name.to_string(),
            FrontendSort::Simple(sort.to_string()),
        ))
        .expect("fixture declaration succeeds");
    executor
        .ctx
        .elaborate_surface_subterm(&FrontendTerm::Symbol(name.to_string()))
        .expect("declared fixture symbol elaborates")
}

fn symbol(name: &str) -> FrontendTerm {
    FrontendTerm::Symbol(name.to_string())
}

fn numeral(value: &str) -> FrontendTerm {
    FrontendTerm::Const(FrontendConstant::Numeral(value.to_string()))
}

fn app(head: &str, operands: Vec<FrontendTerm>) -> FrontendTerm {
    FrontendTerm::App(head.to_string(), operands)
}

fn assert_arithmetic_alias_rejected(
    executor: &mut Executor,
    canonical: TermId,
    parsed: FrontendTerm,
    alias: TermId,
) {
    let originals = vec![(canonical, parsed)];
    let mut ordinary = ProvenanceSurfaceAudit::default();
    assert!(ordinary.require_original_alias_only(&mut executor.ctx, &originals, canonical, alias,));
    let mut arithmetic = ProvenanceSurfaceAudit::default();
    assert!(!arithmetic.require_original_arithmetic_alias_only(
        &mut executor.ctx,
        &originals,
        canonical,
        alias,
    ));
}

#[test]
fn exact_numeric_defining_alias_upgrades_to_a_farkas_operand() {
    let mut executor = Executor::new();
    for name in ["alias_i", "alias_j", "alias_e", "alias_f"] {
        let _ = declare(&mut executor, name, "Int");
    }
    let parsed = app(
        "=",
        vec![
            symbol("alias_i"),
            app(
                "ite",
                vec![
                    app("=", vec![symbol("alias_j"), numeral("1")]),
                    app("+", vec![symbol("alias_e"), symbol("alias_f")]),
                    symbol("alias_e"),
                ],
            ),
        ],
    );
    let canonical = executor
        .ctx
        .elaborate_surface_subterm(&parsed)
        .expect("defining equality elaborates");
    let alias = executor
        .raw_intern_surface(&parsed)
        .expect("binder-free defining equality raw-interns");
    assert_ne!(canonical, alias, "the fixture must exercise a fresh alias");
    let originals = vec![(canonical, parsed.clone())];
    let mut active = HashMap::default();
    assert!(
        crate::executor::proof_surface_syntax::collect_surface_term_overrides(
            &mut executor.ctx,
            canonical,
            &parsed,
            &mut active,
        )
    );

    let mut ordinary = ProvenanceSurfaceAudit::default();
    assert!(ordinary.require_original_alias_only(&mut executor.ctx, &originals, canonical, alias,));
    ordinary.protect_farkas_operand(&mut executor.ctx.terms, alias);
    let mut ordinary_active = active.clone();
    assert!(ordinary.merge_into(&mut ordinary_active));
    assert!(!ordinary.validate_effective(&executor.ctx.terms, &ordinary_active));

    let mut arithmetic = ProvenanceSurfaceAudit::default();
    assert!(arithmetic.require_original_alias_only(
        &mut executor.ctx,
        &originals,
        canonical,
        alias,
    ));
    assert!(arithmetic.require_original_arithmetic_alias_only(
        &mut executor.ctx,
        &originals,
        canonical,
        alias,
    ));
    arithmetic.protect_farkas_operand(&mut executor.ctx.terms, alias);
    assert!(arithmetic.merge_into(&mut active));
    assert!(arithmetic.validate_effective(&executor.ctx.terms, &active));
}

#[test]
fn arithmetic_alias_upgrade_is_idempotent_at_the_term_cap() {
    let mut executor = Executor::new();
    for name in ["alias_cap_i", "alias_cap_k", "alias_cap_j", "alias_cap_e"] {
        let _ = declare(&mut executor, name, "Int");
    }
    let defining = |left: &str| {
        app(
            "=",
            vec![
                symbol(left),
                app(
                    "ite",
                    vec![
                        app("=", vec![symbol("alias_cap_j"), numeral("1")]),
                        app("+", vec![symbol("alias_cap_e"), numeral("1")]),
                        symbol("alias_cap_e"),
                    ],
                ),
            ],
        )
    };
    let first = defining("alias_cap_i");
    let second = defining("alias_cap_k");
    let first_canonical = executor
        .ctx
        .elaborate_surface_subterm(&first)
        .expect("first defining equality elaborates");
    let second_canonical = executor
        .ctx
        .elaborate_surface_subterm(&second)
        .expect("second defining equality elaborates");
    let first_alias = executor
        .raw_intern_surface(&first)
        .expect("first defining equality raw-interns");
    let second_alias = executor
        .raw_intern_surface(&second)
        .expect("second defining equality raw-interns");
    let originals = vec![(first_canonical, first), (second_canonical, second)];

    let mut audit = ProvenanceSurfaceAudit::default();
    assert!(audit.require_original_alias_only(
        &mut executor.ctx,
        &originals,
        first_canonical,
        first_alias,
    ));
    assert!(audit.require_original_arithmetic_alias_only(
        &mut executor.ctx,
        &originals,
        first_canonical,
        first_alias,
    ));
    let mut filler = u32::MAX;
    while audit.arithmetic_requirements.len() < super::MAX_AUDITED_TERMS {
        audit.arithmetic_requirements.insert(TermId(filler));
        filler -= 1;
    }
    let at_cap = audit.arithmetic_requirements.len();
    assert!(audit.require_original_arithmetic_alias_only(
        &mut executor.ctx,
        &originals,
        first_canonical,
        first_alias,
    ));
    assert_eq!(audit.arithmetic_requirements.len(), at_cap);
    assert!(!audit.require_original_arithmetic_alias_only(
        &mut executor.ctx,
        &originals,
        second_canonical,
        second_alias,
    ));
    assert!(audit.overflowed);
    assert!(audit.aliases.contains(&second_alias));
    assert!(!audit.arithmetic_requirements.contains(&second_alias));
    assert_eq!(audit.arithmetic_requirements.len(), at_cap);
}

#[test]
fn arithmetic_alias_rejects_boolean_and_non_linear_equalities() {
    let mut executor = Executor::new();
    let i = declare(&mut executor, "alias_bad_i", "Int");
    let e = declare(&mut executor, "alias_bad_e", "Int");
    let f = declare(&mut executor, "alias_bad_f", "Int");

    let bool_equality = app(
        "=",
        vec![
            app("<", vec![symbol("alias_bad_i"), numeral("0")]),
            FrontendTerm::Const(FrontendConstant::True),
        ],
    );
    let bool_canonical = executor
        .ctx
        .elaborate_surface_subterm(&bool_equality)
        .expect("Boolean equality elaborates");
    let bool_alias = executor
        .raw_intern_surface(&bool_equality)
        .expect("Boolean equality raw-interns");
    assert_arithmetic_alias_rejected(&mut executor, bool_canonical, bool_equality, bool_alias);

    let nonlinear = app(
        "=",
        vec![
            symbol("alias_bad_i"),
            app(
                "*",
                vec![numeral("0"), symbol("alias_bad_e"), symbol("alias_bad_f")],
            ),
        ],
    );
    let nonlinear_canonical = executor
        .ctx
        .elaborate_surface_subterm(&nonlinear)
        .expect("nonlinear equality elaborates");
    let nonlinear_alias = executor
        .raw_intern_surface(&nonlinear)
        .expect("binder-free nonlinear equality raw-interns");
    assert_ne!(nonlinear_canonical, nonlinear_alias);
    assert_arithmetic_alias_rejected(
        &mut executor,
        nonlinear_canonical,
        nonlinear,
        nonlinear_alias,
    );

    assert_eq!(*executor.ctx.terms.sort(i), Sort::Int);
    assert_eq!(*executor.ctx.terms.sort(e), Sort::Int);
    assert_eq!(*executor.ctx.terms.sort(f), Sort::Int);
}

#[test]
fn arithmetic_alias_rejects_hidden_reordered_and_negated_sources() {
    let mut executor = Executor::new();
    let i = declare(&mut executor, "alias_shape_i", "Int");
    let e = declare(&mut executor, "alias_shape_e", "Int");
    let f = declare(&mut executor, "alias_shape_f", "Int");
    let _condition = declare(&mut executor, "alias_shape_condition", "Bool");

    let hidden = app(
        "=",
        vec![
            symbol("alias_shape_i"),
            FrontendTerm::Let(
                vec![("z".to_string(), symbol("alias_shape_e"))],
                Box::new(symbol("z")),
            ),
        ],
    );
    let hidden_canonical = executor
        .ctx
        .elaborate_surface_subterm(&hidden)
        .expect("let-hidden equality elaborates");
    let hidden_alias = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [i, f], Sort::Bool);
    assert_arithmetic_alias_rejected(&mut executor, hidden_canonical, hidden, hidden_alias);

    let ordered = app(
        "=",
        vec![
            symbol("alias_shape_i"),
            app(
                "ite",
                vec![
                    symbol("alias_shape_condition"),
                    symbol("alias_shape_e"),
                    symbol("alias_shape_f"),
                ],
            ),
        ],
    );
    let ordered_canonical = executor
        .ctx
        .elaborate_surface_subterm(&ordered)
        .expect("ITE equality elaborates");
    let right = executor
        .ctx
        .elaborate_surface_subterm(&app(
            "ite",
            vec![
                symbol("alias_shape_condition"),
                symbol("alias_shape_e"),
                symbol("alias_shape_f"),
            ],
        ))
        .expect("ITE side elaborates");
    let reordered_alias = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [right, i], Sort::Bool);
    assert_arithmetic_alias_rejected(&mut executor, ordered_canonical, ordered, reordered_alias);

    let negated = app(
        "not",
        vec![app(
            "=",
            vec![symbol("alias_shape_i"), symbol("alias_shape_e")],
        )],
    );
    let negated_canonical = executor
        .ctx
        .elaborate_surface_subterm(&negated)
        .expect("negated equality elaborates");
    let positive_alias = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [i, e], Sort::Bool);
    let originals = vec![(negated_canonical, negated)];
    let mut arithmetic = ProvenanceSurfaceAudit::default();
    assert!(!arithmetic.require_original_arithmetic_alias_only(
        &mut executor.ctx,
        &originals,
        negated_canonical,
        positive_alias,
    ));
}
