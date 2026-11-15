// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{
    try_export_alethe_with_problem_scope_and_overrides,
    try_export_alethe_with_problem_scope_overrides_and_budget, AlethePrintError,
};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId, TermStore};

fn raw_equality(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}

#[test]
fn surface_symm_collapsed_to_identical_literal_prints_weakening() {
    let mut terms = TermStore::new();
    let u = terms.mk_var("u", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let premise = raw_equality(&mut terms, u, x);
    let conclusion = raw_equality(&mut terms, x, u);
    let mut overrides = DetHashMap::default();
    overrides.insert(premise, "(= x u)".to_string());

    let mut proof = Proof::new();
    let assumed = proof.add_assume(premise, None);
    proof.add_rule_step(AletheRule::Symm, vec![conclusion], vec![assumed], vec![]);

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[premise],
        Some(&overrides),
    )
    .expect("an identical printed clause is an exact weakening");
    assert!(
        output.contains("(step t1 (cl (= x u)) :rule weakening :premises (t0))"),
        "{output}"
    );
    assert!(!output.contains(":rule symm"), "{output}");
}

#[test]
fn surface_symm_exact_string_and_quoted_symbol_reversal_stays_symm() {
    let mut terms = TermStore::new();
    let symbol = terms.mk_var("x y", Sort::String);
    let string = terms.mk_string("a\"b".to_string());
    let premise = raw_equality(&mut terms, symbol, string);
    let conclusion = raw_equality(&mut terms, string, symbol);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(premise, None);
    proof.add_rule_step(AletheRule::Symm, vec![conclusion], vec![assumed], vec![]);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[premise], None)
            .expect("an exact printed reversal must remain symm");
    assert!(
        output.contains(r#"(step t1 (cl (= "a""b" |x y|)) :rule symm :premises (t0))"#),
        "{output}"
    );
    assert!(!output.contains(":rule weakening"), "{output}");
}

/// D7 (2026-09-22): a Z3-escaped quoted symbol renders in AY's lossless
/// escape spelling, and the surface verdict discloses that pinned Carcara
/// rejects that spelling — the document is no longer refused at the printer.
#[test]
fn surface_symm_renders_z3_escaped_quoted_symbol_and_discloses_unsupported_surface() {
    let mut terms = TermStore::new();
    let symbol = terms.mk_var("x|y", Sort::String);
    let string = terms.mk_string("a\"b".to_string());
    let premise = raw_equality(&mut terms, symbol, string);
    let conclusion = raw_equality(&mut terms, string, symbol);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(premise, None);
    proof.add_rule_step(AletheRule::Symm, vec![conclusion], vec![assumed], vec![]);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[premise], None)
            .expect("an escaped quoted symbol renders in the lossless AY spelling");
    assert!(
        output.contains(r#"(step t1 (cl (= "a""b" |x\|y|)) :rule symm :premises (t0))"#),
        "{output}"
    );
    let surface = crate::carcara_proof_surface(&proof, &terms, None);
    assert!(
        surface
            .unsupported_reason()
            .is_some_and(|reason| reason.contains("symbol `x|y`")),
        "{surface}"
    );
}

#[test]
fn surface_symm_negated_reversal_prints_not_symm() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = raw_equality(&mut terms, x, y);
    let reversed = raw_equality(&mut terms, y, x);
    let premise = terms.mk_not_raw(equality);
    let conclusion = terms.mk_not_raw(reversed);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(premise, None);
    proof.add_rule_step(AletheRule::Symm, vec![conclusion], vec![assumed], vec![]);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[premise], None)
            .expect("a negated equality reversal has the dedicated not_symm rule");
    assert!(
        output.contains("(step t1 (cl (not (= y x))) :rule not_symm :premises (t0))"),
        "{output}"
    );
    assert!(!output.contains(":rule symm"), "{output}");
}

#[test]
fn surface_symm_rejects_non_reversed_or_annotated_printed_steps() {
    let mut terms = TermStore::new();
    let u = terms.mk_var("u", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let premise = raw_equality(&mut terms, u, x);
    let conclusion = raw_equality(&mut terms, x, u);
    let mut overrides = DetHashMap::default();
    overrides.insert(premise, "(= u u)".to_string());

    let mut malformed = Proof::new();
    let assumed = malformed.add_assume(premise, None);
    malformed.add_rule_step(AletheRule::Symm, vec![conclusion], vec![assumed], vec![]);
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &malformed,
        &terms,
        &[premise],
        Some(&overrides),
    )
    .expect_err("a non-reversed printed symm must fail closed");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { ref reason, .. }
            if reason.contains("neither identical to nor the exact reverse")),
        "{error}"
    );

    let mut annotated = Proof::new();
    let assumed = annotated.add_assume(premise, None);
    annotated.add_rule_step(AletheRule::Symm, vec![conclusion], vec![assumed], vec![u]);
    let error =
        try_export_alethe_with_problem_scope_and_overrides(&annotated, &terms, &[premise], None)
            .expect_err("symm proof arguments are not part of the certified contract");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { ref reason, .. }
            if reason.contains("does not accept proof arguments")),
        "{error}"
    );
}

#[test]
fn surface_symm_rejects_native_invalid_identity_before_weakening() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = raw_equality(&mut terms, x, y);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(equality, None);
    proof.add_rule_step(AletheRule::Symm, vec![equality], vec![assumed], vec![]);

    let error =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[equality], None)
            .expect_err("native-invalid symm must not be laundered into weakening");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { ref reason, .. }
            if reason.contains("native symm shape is invalid")),
        "{error}"
    );
}

#[test]
fn surface_symm_budget_reports_only_fully_rendered_steps() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let premise = raw_equality(&mut terms, x, y);
    let conclusion = raw_equality(&mut terms, y, x);
    let mut proof = Proof::new();
    let assumed = proof.add_assume(premise, None);
    proof.add_rule_step(AletheRule::Symm, vec![conclusion], vec![assumed], vec![]);

    let error = try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        &terms,
        &[premise],
        None,
        Some(50),
    )
    .expect_err("the symmetry parse must exhaust this focused budget");
    assert!(
        matches!(
            error,
            AlethePrintError::EmissionBudgetExhausted {
                steps_rendered: 1,
                ..
            }
        ),
        "{error}"
    );
}

/// `(= (= a b) (= b a))` as the strict checker's `eq_symmetric` conclusion.
fn eq_symmetric_conclusion(terms: &mut TermStore, a: TermId, b: TermId) -> (TermId, TermId) {
    let forward = raw_equality(terms, a, b);
    let backward = raw_equality(terms, b, a);
    (forward, raw_equality(terms, forward, backward))
}

fn export_eq_symmetric(
    terms: &TermStore,
    conclusion: TermId,
    overrides: Option<&DetHashMap<TermId, String>>,
) -> Result<String, AlethePrintError> {
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::EqSymmetric, vec![conclusion], vec![], vec![]);
    // The conclusion stands in for a problem assertion that declares its
    // symbols; the proof itself may not introduce declarations.
    try_export_alethe_with_problem_scope_and_overrides(&proof, terms, &[conclusion], overrides)
}

/// a7_int_neg_unsat: the authored `(= (g (- 5)) 0)` rides the canonical
/// `(= 0 (g (- 5)))` document-wide, so the checked reversal printed with two
/// identical sides and pinned carcara refused `eq_symmetric` ("expected terms
/// to be equal"). Identical printed sides are an instance of `refl`.
#[test]
fn surface_eq_symmetric_collapsed_by_an_authored_override_prints_refl() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let zero = terms.mk_int(0.into());
    let (canonical, conclusion) = eq_symmetric_conclusion(&mut terms, zero, x);
    let mut overrides = DetHashMap::default();
    overrides.insert(canonical, "(= x 0)".to_string());
    let output = export_eq_symmetric(&terms, conclusion, Some(&overrides))
        .expect("an identity is a refl instance");
    assert!(
        output.contains("(step t0 (cl (= (= x 0) (= x 0))) :rule refl)"),
        "{output}"
    );
    assert!(!output.contains(":rule eq_symmetric"), "{output}");
}

#[test]
fn surface_eq_symmetric_exact_reversal_stays_byte_identical() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let (_, conclusion) = eq_symmetric_conclusion(&mut terms, x, y);
    let output = export_eq_symmetric(&terms, conclusion, None).expect("an exact reversal");
    assert!(
        output.contains("(step t0 (cl (= (= x y) (= y x))) :rule eq_symmetric)"),
        "{output}"
    );
}

/// Negative twins of the new `refl` acceptance: a printed pair that is
/// neither a reversal nor an identity, and a native step the strict checker
/// would refuse even though its print is an identity, both fail closed.
#[test]
fn surface_eq_symmetric_refuses_corrupted_or_native_invalid_steps() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let (forward, conclusion) = eq_symmetric_conclusion(&mut terms, x, y);
    let mut overrides = DetHashMap::default();
    overrides.insert(forward, "(= x x)".to_string());
    let error = export_eq_symmetric(&terms, conclusion, Some(&overrides))
        .expect_err("a corrupted printed operand must fail closed");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { ref reason, .. }
            if reason.contains("neither an exact reversal nor an identity")),
        "{error}"
    );

    let identity = raw_equality(&mut terms, forward, forward);
    let error = export_eq_symmetric(&terms, identity, None)
        .expect_err("native-invalid eq_symmetric must not be laundered into refl");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { ref reason, .. }
            if reason.contains("native eq_symmetric shape is invalid")),
        "{error}"
    );
}
