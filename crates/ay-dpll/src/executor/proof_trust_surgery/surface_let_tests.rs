// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for surface reconstruction and authored proof plans.

use super::*;

use ay_frontend::command::Index as FrontendIndex;
use ay_frontend::parse;

#[path = "surface_let_tests/fixtures.rs"]
mod fixtures;
use fixtures::{
    assert_legacy_ite_scan_preflight_rejects_excess_arity,
    assert_native_ematching_body_preflight_rejects_excess_depth, authored_array_ite_fixture,
    normalized_authored_or_fixture,
};

#[test]
fn expansion_descends_into_structured_indexed_terms() {
    let zero = FrontendTerm::IndexedApp(
        "bv0".to_string(),
        vec![FrontendIndex::Numeral("8".to_string())],
        Vec::new(),
    );
    let term = FrontendTerm::Let(
        vec![("x".to_string(), zero.clone())],
        Box::new(FrontendTerm::App(
            "=".to_string(),
            vec![
                FrontendTerm::Symbol("x".to_string()),
                FrontendTerm::IndexedApp(
                    "bv1".to_string(),
                    vec![FrontendIndex::Numeral("8".to_string())],
                    Vec::new(),
                ),
            ],
        )),
    );
    let expanded = expand_surface_lets(&term, &std::collections::HashMap::new())
        .expect("binder-free indexed term expands");
    assert!(matches!(
        expanded,
        FrontendTerm::App(ref op, ref args)
            if op == "=" && args.first() == Some(&zero)
    ));
}

#[test]
fn raw_intern_accepts_structured_decimal_bitvector_literal() {
    let mut executor = Executor::new();
    let literal = FrontendTerm::IndexedApp(
        "bv3".to_string(),
        vec![FrontendIndex::Numeral("4".to_string())],
        Vec::new(),
    );
    let raw = executor
        .raw_intern_surface(&literal)
        .expect("structured decimal bitvector literal interns");
    assert_eq!(executor.ctx.terms.sort(raw), &Sort::bitvec(4));

    let ordinary = FrontendTerm::Symbol("(_ bv3 4)".to_string());
    assert!(executor.raw_intern_surface(&ordinary).is_none());

    let character = FrontendTerm::IndexedApp(
        "Char".to_string(),
        vec![FrontendIndex::Numeral("65".to_string())],
        Vec::new(),
    );
    assert!(executor.raw_intern_surface(&character).is_none());
}

#[test]
fn raw_intern_preserves_a_folded_ite_source() {
    use ay_frontend::command::Constant as SurfaceConstant;

    let mut executor = Executor::new();
    let surface = FrontendTerm::App(
        "ite".to_string(),
        vec![
            FrontendTerm::Const(SurfaceConstant::True),
            FrontendTerm::Const(SurfaceConstant::Numeral("1".to_string())),
            FrontendTerm::Const(SurfaceConstant::Numeral("2".to_string())),
        ],
    );
    let canonical = executor
        .ctx
        .elaborate_surface_subterm(&surface)
        .expect("ground ite elaborates");
    let raw = executor
        .raw_intern_surface(&surface)
        .expect("ground ite raw-interns");

    assert_ne!(raw, canonical, "raw source must not inherit ite folding");
    assert!(matches!(
        executor.ctx.terms.get(raw),
        TermData::Ite(condition, then_term, else_term)
            if executor.ctx.terms.is_true(*condition)
                && then_term != else_term
    ));
}

#[test]
fn raw_intern_preserves_private_identity_for_declared_builtin_spellings() {
    use ay_frontend::command::Constant as SurfaceConstant;

    let cases = [
        (
            "(declare-fun = (Int Int) Bool)",
            "=",
            vec![
                FrontendTerm::Const(SurfaceConstant::Numeral("0".to_string())),
                FrontendTerm::Const(SurfaceConstant::Numeral("1".to_string())),
            ],
        ),
        (
            "(declare-fun rem (Int Int) Int)",
            "rem",
            vec![
                FrontendTerm::Const(SurfaceConstant::Numeral("5".to_string())),
                FrontendTerm::Const(SurfaceConstant::Numeral("2".to_string())),
            ],
        ),
        (
            "(declare-fun to_int (Real) Int)",
            "to_int",
            vec![FrontendTerm::Const(SurfaceConstant::Decimal(
                "1.5".to_string(),
            ))],
        ),
    ];

    for (declaration, head, args) in cases {
        let mut executor = Executor::new();
        let commands = parse(declaration).expect("declaration parses");
        executor
            .execute_all(&commands)
            .expect("declaration executes");

        let surface = FrontendTerm::App(head.to_string(), args);
        let elaborated = executor
            .ctx
            .elaborate_surface_subterm(&surface)
            .expect("declared application elaborates");
        let raw = executor
            .raw_intern_surface(&surface)
            .expect("declared application raw-interns");
        let expected_identity = executor
            .ctx
            .symbol_iter()
            .find(|(surface, _)| surface.as_str() == head)
            .map(|(surface, info)| executor.ctx.symbol_identity_name(surface, info))
            .expect("declaration remains live");

        assert_ne!(
            expected_identity, head,
            "builtin-colliding declarations require a private identity"
        );
        assert!(matches!(
            executor.ctx.terms.get(elaborated),
            TermData::App(Symbol::Named(identity), _) if identity == expected_identity
        ));
        assert!(matches!(
            executor.ctx.terms.get(raw),
            TermData::App(Symbol::Named(identity), _) if identity == expected_identity
        ));
    }
}

#[test]
fn raw_ematching_forall_preserves_private_declaration_identity() {
    use ay_frontend::command::Constant as SurfaceConstant;

    let mut executor = Executor::new();
    let commands = parse(
        "(declare-fun rem (Int Int) Int)\n\
         (assert (forall ((x Int)) (= (rem x 2) 0)))",
    )
    .expect("quantified private-UF fixture parses");
    let ay_frontend::Command::Assert(parsed_forall) = &commands[1] else {
        panic!("fixture must contain an asserted forall");
    };
    let parsed_forall = parsed_forall.clone();
    executor
        .execute_all(&commands)
        .expect("quantified private-UF fixture executes");

    let canonical_forall = executor.ctx.assertions[0];
    let private_identity = executor
        .ctx
        .symbol_iter()
        .find(|(surface, _)| surface.as_str() == "rem")
        .map(|(surface, info)| executor.ctx.symbol_identity_name(surface, info).to_string())
        .expect("rem declaration remains live");
    assert_ne!(private_identity, "rem");

    let five = executor.ctx.terms.mk_int(5.into());
    let ground_surface = FrontendTerm::App(
        "=".to_string(),
        vec![
            FrontendTerm::App(
                "rem".to_string(),
                vec![
                    FrontendTerm::Const(SurfaceConstant::Numeral("5".to_string())),
                    FrontendTerm::Const(SurfaceConstant::Numeral("2".to_string())),
                ],
            ),
            FrontendTerm::Const(SurfaceConstant::Numeral("0".to_string())),
        ],
    );
    let ground_instance = executor
        .raw_intern_surface(&ground_surface)
        .expect("authenticated ground instance raw-interns");
    let rebuilt = executor
        .build_raw_ematching_forall_source(
            canonical_forall,
            &parsed_forall,
            &[five],
            ground_instance,
        )
        .expect("binder lifting preserves the authenticated private head");

    let TermData::Forall(_, raw_body, _) = executor.ctx.terms.get(rebuilt).clone() else {
        panic!("proof repair must rebuild a forall");
    };
    let mut pending = vec![raw_body];
    let mut found_private_head = false;
    while let Some(term) = pending.pop() {
        if matches!(
            executor.ctx.terms.get(term),
            TermData::App(Symbol::Named(identity), _) if identity == &private_identity
        ) {
            found_private_head = true;
            break;
        }
        pending.extend(executor.ctx.terms.children(term));
    }
    assert!(
        found_private_head,
        "rebuilt quantified proof source lost private declaration identity"
    );
}

#[test]
fn rebuilt_private_equality_does_not_authorize_canonical_builtin_collision() {
    let mut executor = Executor::new();
    let commands = parse(
        "(declare-fun = (Int Int) Bool)\n\
         (assert (= 0 1))",
    )
    .expect("fixture parses");
    executor.execute_all(&commands).expect("fixture executes");

    // The rebuild captures both the canonical authored root and any raw
    // source reconstruction that proof surgery may assume.
    executor.rebuild_trust_leaf_proof_from_original_assertions(&mut Proof::new());
    let private_equality = executor
        .last_proof_rebuild_originals
        .iter()
        .copied()
        .find(|&term| {
            matches!(
                executor.ctx.terms.get(term),
                TermData::App(Symbol::Named(identity), _)
                    if identity != "="
                        && executor.ctx.dt_surface_name(identity) == Some("=")
            )
        })
        .expect("rebuilt authored premise retains the private declaration identity");
    let args = match executor.ctx.terms.get(private_equality).clone() {
        TermData::App(_, args) => args,
        _ => unreachable!("matched an application above"),
    };
    let canonical_builtin = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), args, Sort::Bool);
    assert!(!executor
        .problem_assertions_for_strict_proof()
        .contains(&canonical_builtin));

    // Source spelling alone must not authorize the canonical builtin: the
    // problem asserted a free UF application instead. Assumption authority
    // is validated before terminal-proof shape, so this minimal proof
    // isolates the exact scope decision under test.
    let mut forged = Proof::new();
    forged.add_assume(canonical_builtin, None);
    assert!(matches!(
        executor.check_proof_strict_with_datatypes(&forged),
        Err(ay_proof::ProofCheckError::UnauthorizedAssumption {
            term,
            ..
        }) if term == canonical_builtin
    ));
}

#[test]
fn normalized_authored_implication_derives_exact_packed_or() {
    let (mut executor, originals, target, _) = normalized_authored_or_fixture();
    let plan = executor
        .plan_normalized_authored_or(&[target], &originals)
        .expect("the authenticated implication must align with the packed proof target");
    assert!(matches!(
        executor.ctx.terms.get(plan.source_or),
        TermData::App(Symbol::Named(name), _) if name == "or"
    ));
    assert_eq!(
        plan.literals
            .iter()
            .filter(|literal| literal.bridge_atom.is_some())
            .count(),
        1,
        "only the negated strict comparison may need normalization"
    );

    let mut proof = Proof::new();
    let source = proof.add_assume(plan.source_or, None);
    let unit = executor
        .emit_normalized_authored_or(&mut proof, &plan, source)
        .expect("the planned implication/or bridge emits");
    assert!(matches!(
        &proof.steps[unit.0 as usize],
        ProofStep::Step {
            clause,
            rule: AletheRule::Contraction,
            ..
        } if clause.as_slice() == [target]
    ));
    let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &executor.ctx.terms,
        None,
        None,
        &[plan.source_or],
    )
    .expect("every implication, arithmetic, packing, and resolution step replays");
    assert_eq!(authenticated.clause(unit), Some([target].as_slice()));
    assert_eq!(
        ay_proof::terminal_trust_report(&proof).trust_rule_on_path,
        0
    );
}

#[test]
fn normalized_authored_implication_refuses_forged_guard_or_equality() {
    let (mut executor, originals, target, z) = normalized_authored_or_fixture();
    let TermData::App(Symbol::Named(name), disjuncts) = executor.ctx.terms.get(target).clone()
    else {
        panic!("fixture target must be a packed or")
    };
    assert_eq!(name, "or");
    let eq_pos = disjuncts
        .iter()
        .position(|&term| decode_binary_equality(&executor.ctx.terms, term).is_some())
        .expect("target contains its raw equality");
    let guard_pos = disjuncts
        .iter()
        .position(|&term| {
            matches!(
                executor.ctx.terms.get(term),
                TermData::App(Symbol::Named(op), args) if op == "<=" && args.len() == 2
            )
        })
        .expect("target contains its normalized guard");

    let (eq_lhs, _) = decode_binary_equality(&executor.ctx.terms, disjuncts[eq_pos])
        .expect("equality position was checked");
    let wrong_equality = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [eq_lhs, z], Sort::Bool);
    let guard_args = match executor.ctx.terms.get(disjuncts[guard_pos]).clone() {
        TermData::App(_, args) => args,
        _ => unreachable!("guard position was checked"),
    };
    let one = executor.ctx.terms.mk_int(1.into());
    let wrong_guard =
        executor
            .ctx
            .terms
            .mk_app(Symbol::named("<="), [guard_args[0], one], Sort::Bool);

    for (label, position, replacement) in [
        ("equality", eq_pos, wrong_equality),
        ("guard", guard_pos, wrong_guard),
    ] {
        let mut forged_disjuncts = disjuncts.clone();
        forged_disjuncts[position] = replacement;
        let forged = executor
            .ctx
            .terms
            .mk_app(Symbol::named("or"), forged_disjuncts, Sort::Bool);
        assert!(
            executor
                .plan_normalized_authored_or(&[forged], &originals)
                .is_none(),
            "a forged {label} must not align with the authenticated source"
        );
    }
}

#[test]
fn authored_array_ite_derives_packed_unit_from_row_chain() {
    let (mut executor, originals, target, _) = authored_array_ite_fixture();
    let plan = executor
        .plan_authored_array_ite(&[target], &originals)
        .expect("the exact authored equality and guard must certify the array ITE");
    assert_eq!(
        ay_proof::recognize_array_theory_lemma(&executor.ctx.terms, &plan.congruence_clause,),
        Some(TheoryLemmaKind::ArrayRowChain)
    );
    assert_eq!(
        ay_proof::recognize_array_select_store(&executor.ctx.terms, &plan.row1_clause),
        Some(true)
    );

    let mut proof = Proof::new();
    let equality_assume = proof.add_assume(plan.array_equality, None);
    let guard_assume = proof.add_assume(plan.guard_source, None);
    let unit = executor
        .emit_authored_array_ite(&mut proof, &plan, equality_assume, guard_assume)
        .expect("the checked ROW/ITE/OR derivation emits");
    let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context(
        &proof,
        &executor.ctx.terms,
        None,
        None,
        &[plan.array_equality, plan.guard_source],
    )
    .expect("every ROW, ITE, OR, and resolution step replays");
    assert_eq!(authenticated.clause(unit), Some([target].as_slice()));
    assert_eq!(
        ay_proof::terminal_trust_report(&proof).trust_rule_on_path,
        0
    );
}

#[test]
fn authored_array_ite_refuses_forged_then_branch() {
    let (mut executor, originals, target, wrong) = authored_array_ite_fixture();
    assert!(
        executor
            .plan_authored_array_ite(&[target], &originals[..1])
            .is_none(),
        "the array equality alone must not authorize the ITE guard"
    );
    assert!(
        executor
            .plan_authored_array_ite(&[target], &originals[1..])
            .is_none(),
        "the guard alone must not authorize the array equality"
    );
    let TermData::App(Symbol::Named(op), disjuncts) = executor.ctx.terms.get(target).clone() else {
        panic!("fixture target must be an or")
    };
    assert_eq!(op, "or");
    let ite_position = disjuncts
        .iter()
        .position(|&term| matches!(executor.ctx.terms.get(term), TermData::Ite(..)))
        .expect("fixture target contains its ITE");
    let TermData::Ite(guard, _, else_branch) =
        executor.ctx.terms.get(disjuncts[ite_position]).clone()
    else {
        unreachable!("ITE position was checked")
    };
    let read = match executor.ctx.terms.get(else_branch).clone() {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => args[1],
        _ => panic!("fixture else branch is an equality"),
    };
    let forged_then = executor
        .ctx
        .terms
        .mk_app(Symbol::named("="), [wrong, read], Sort::Bool);
    let forged_ite = executor.ctx.terms.mk_ite(guard, forged_then, else_branch);
    let mut forged_disjuncts = disjuncts;
    forged_disjuncts[ite_position] = forged_ite;
    let forged = executor
        .ctx
        .terms
        .mk_app(Symbol::named("or"), forged_disjuncts, Sort::Bool);
    assert!(
        executor
            .plan_authored_array_ite(&[forged], &originals)
            .is_none(),
        "a forged then branch must not pass the strict ROW matcher"
    );
}

#[test]
fn native_ematching_body_preflight_rejects_excess_depth() {
    assert_native_ematching_body_preflight_rejects_excess_depth();
}

#[test]
fn legacy_ite_scan_preflight_rejects_excess_arity() {
    assert_legacy_ite_scan_preflight_rejects_excess_arity();
}
