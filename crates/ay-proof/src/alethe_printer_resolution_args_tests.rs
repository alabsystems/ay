// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use crate::{
    try_export_alethe, try_export_alethe_with_problem_scope_and_overrides,
    try_export_alethe_with_problem_scope_overrides_and_budget, AlethePrintError,
};
use ay_core::kani_compat::DetHashMap;
use ay_core::{AletheRule, Proof, Sort, Symbol, TermId, TermStore};

#[test]
fn generic_resolution_export_rejects_malformed_argument_count() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(x, None);
        let h2 = proof.add_assume(not_x, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![x]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("one pivot without its polarity must fail closed");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("requires 2 pivot/polarity arguments, found 1")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_non_boolean_polarity() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);
    let one = terms.mk_int(1.into());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(x, None);
        let h2 = proof.add_assume(not_x, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![x, one]);

        let error =
            try_export_alethe(&proof, &terms).expect_err("a non-Boolean polarity must fail closed");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("polarity for link 0 must be true or false")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_accepts_complete_nary_annotations() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let first = proof.add_theory_lemma("test", vec![a, b]);
        let second = proof.add_theory_lemma("test", vec![not_b]);
        let third = proof.add_theory_lemma("test", vec![not_a]);
        proof.add_rule_step(
            rule,
            Vec::new(),
            vec![first, second, third],
            vec![b, yes, a, yes],
        );

        let output = try_export_alethe(&proof, &terms)
            .expect("one pivot/polarity pair per link must export");
        assert!(output.contains(":args (b true a true)"), "{output}");
    }
}

#[test]
fn generic_resolution_export_rejects_surface_changed_polarity() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(yes, "(= p p)".to_string());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(p, None);
        let h2 = proof.add_assume(not_p, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![p, yes]);

        let error = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[p, not_p],
            Some(&overrides),
        )
        .expect_err("a Boolean constant printed as an equality must fail closed");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("effective surface overrides are active")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_surface_changed_pivot_depth() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(p, "(not (not p))".to_string());
    overrides.insert(not_p, "(not p)".to_string());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(p, None);
        let h2 = proof.add_assume(not_p, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![p, yes]);

        let error = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[p, not_p],
            Some(&overrides),
        )
        .expect_err("a surface pivot with a different exact negation depth must fail closed");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("effective surface overrides are active")
            ),
            "{error}"
        );
    }
}

#[test]
fn annotated_resolution_override_gate_does_not_render_huge_canonical_term() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let wide = terms.mk_app(Symbol::Named("or".to_string()), vec![p; 8_192], Sort::Bool);
    let not_wide = terms.mk_not_raw(wide);
    let yes = terms.mk_bool(true);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(wide, "p".to_string());
    overrides.insert(not_wide, "(not p)".to_string());

    let mut proof = Proof::new();
    let h1 = proof.add_assume(wide, None);
    let h2 = proof.add_assume(not_wide, None);
    proof.add_rule_step(
        AletheRule::Resolution,
        Vec::new(),
        vec![h1, h2],
        vec![wide, yes],
    );

    let error = try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        &terms,
        &[wide, not_wide],
        Some(&overrides),
        Some(64),
    )
    .expect_err("annotated resolution with any active override must fail in constant time");
    assert!(
        matches!(
            error,
            AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                if reason.contains("effective surface overrides are active")
        ),
        "{error}"
    );
}

#[test]
fn generic_resolution_export_rejects_repeated_directed_pivot() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let left = proof.add_theory_lemma("test", vec![p]);
        let right = proof.add_theory_lemma("test", vec![not_p, not_p]);
        proof.add_rule_step(rule, Vec::new(), vec![left, right], vec![p, yes]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("a duplicate next-premise pivot must not be erased only internally");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("premise 1 contains a duplicate literal")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_duplicate_in_first_premise() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let left = proof.add_theory_lemma("test", vec![p, p]);
        let right = proof.add_theory_lemma("test", vec![not_p]);
        proof.add_rule_step(rule, vec![p], vec![left, right], vec![p, yes]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("an explicit resolution first premise must be duplicate-free");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("first premise contains a duplicate literal")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_duplicate_in_conclusion() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let left = proof.add_theory_lemma("test", vec![p, q]);
        let right = proof.add_theory_lemma("test", vec![not_p]);
        proof.add_rule_step(rule, vec![q, q], vec![left, right], vec![p, yes]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("an explicit resolution conclusion must be duplicate-free");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("conclusion contains a duplicate literal")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_export_rejects_cross_premise_residual_collision() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let yes = terms.mk_bool(true);

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let left = proof.add_theory_lemma("test", vec![p, q]);
        let right = proof.add_theory_lemma("test", vec![not_p, q]);
        proof.add_rule_step(rule, vec![q], vec![left, right], vec![p, yes]);

        let error = try_export_alethe(&proof, &terms)
            .expect_err("an explicit resolution must retain both residual occurrences");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { ref reason, .. }
                    if reason.contains("residual for link 0 contains a duplicate literal")
            ),
            "{error}"
        );
    }
}

#[test]
fn generic_resolution_keeps_certified_distinct_bridge() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = terms.mk_eq(x, y);
    let disequality = terms.mk_not_raw(equality);
    let no = terms.mk_bool(false);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(disequality, "(distinct x y)".to_string());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(disequality, None);
        let h2 = proof.add_assume(equality, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], vec![equality, no]);

        let output = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[disequality, equality],
            Some(&overrides),
        )
        .expect("the exact unit distinct/equality bridge remains supported");
        assert!(output.contains(":rule distinct_elim"), "{output}");
    }
}

#[test]
fn argument_free_resolution_keeps_surface_override_path() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(p, "(not (not p))".to_string());
    overrides.insert(not_p, "(not p)".to_string());

    for rule in [AletheRule::Resolution, AletheRule::ThResolution] {
        let mut proof = Proof::new();
        let h1 = proof.add_assume(p, None);
        let h2 = proof.add_assume(not_p, None);
        proof.add_rule_step(rule, Vec::new(), vec![h1, h2], Vec::new());

        let output = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[p, not_p],
            Some(&overrides),
        )
        .expect("argument-free resolution retains its existing inferred-pivot path");
        assert!(!output.contains(":args"), "{output}");
    }
}
