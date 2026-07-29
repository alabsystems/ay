// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{string_literal, AletheRule, Sort};

// Note: quote_symbol tests are in ay-core::smtlib

#[test]
fn test_empty_proof() {
    let proof = Proof::new();
    let terms = TermStore::new();
    let output = export_alethe(&proof, &terms);
    assert_eq!(output, "");
}

#[test]
fn test_assume_step() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(x, None);

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains("(declare-fun x () Bool)"),
        "Missing declaration for x: {output}"
    );
    assert!(output.contains("(assume t0 x)"), "Missing assume: {output}");
}

#[test]
fn test_step_with_premises() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(x, None);
    let h2 = proof.add_assume(not_x, None);
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![], // empty clause = contradiction
        vec![h1, h2],
        vec![x], // pivot
    );

    let output = export_alethe(&proof, &terms);
    // Declaration preamble + 3 proof steps
    assert!(
        output.contains("(declare-fun x () Bool)"),
        "Missing declaration: {output}"
    );
    assert!(
        output.contains("(assume t0 x)"),
        "Missing assume h1: {output}"
    );
    assert!(
        output.contains("(assume t1 (not x))"),
        "Missing assume h2: {output}"
    );
    assert!(
        output.contains(":rule resolution"),
        "Missing resolution: {output}"
    );
    assert!(
        output.contains(":premises (t0 t1)"),
        "Missing premises: {output}"
    );
}

#[test]
fn test_theory_lemma_generic() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq = terms.mk_eq(a, b);

    let mut proof = Proof::new();
    proof.add_theory_lemma("EUF", vec![eq]);

    let output = export_alethe(&proof, &terms);
    // Generic lemmas use "trust" rule
    assert!(output.contains(":rule trust"));
    assert!(output.contains("(= a b)"));
}

#[test]
fn test_theory_lemma_with_kind() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);

    // Build transitivity clause: (not (= a b)) OR (not (= b c)) OR (= a c)
    let eq_ab = terms.mk_eq(a, b);
    let eq_bc = terms.mk_eq(b, c);
    let eq_ac = terms.mk_eq(a, c);
    let not_eq_ab = terms.mk_not(eq_ab);
    let not_eq_bc = terms.mk_not(eq_bc);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "EUF",
        vec![not_eq_ab, not_eq_bc, eq_ac],
        TheoryLemmaKind::EufTransitive,
    );

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains(":rule eq_transitive"),
        "Expected eq_transitive rule, got: {output}"
    );
}

#[test]
fn test_theory_lemma_la_generic_with_farkas() {
    use ay_core::FarkasAnnotation;
    use num_rational::Rational64;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(5)));
    let ten = terms.mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(
        10,
    )));

    // x <= 5
    let x_le_5 = terms.mk_le(x, five);
    // x >= 10 (negated as x < 10)
    let x_ge_10 = terms.mk_ge(x, ten);

    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_x_le_5, not_x_ge_10],
        FarkasAnnotation::new(vec![Rational64::from(1), Rational64::from(1)]),
    );

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains(":rule la_generic"),
        "Expected la_generic rule, got: {output}"
    );
    assert!(
        output.contains(":args (1 1)"),
        "Expected :args (1 1), got: {output}"
    );
}

#[test]
fn test_theory_lemma_la_generic_fractional_farkas() {
    use ay_core::FarkasAnnotation;
    use num_rational::Rational64;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let five = terms.mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(5)));
    let ten = terms.mk_rational(num_rational::BigRational::from(num_bigint::BigInt::from(
        10,
    )));

    let x_le_5 = terms.mk_le(x, five);
    let x_ge_10 = terms.mk_ge(x, ten);

    let not_x_le_5 = terms.mk_not(x_le_5);
    let not_x_ge_10 = terms.mk_not(x_ge_10);

    let mut proof = Proof::new();
    // Use fractional coefficients: 1/2 and 3/4
    proof.add_theory_lemma_with_farkas(
        "LRA",
        vec![not_x_le_5, not_x_ge_10],
        FarkasAnnotation::new(vec![Rational64::new(1, 2), Rational64::new(3, 4)]),
    );

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains(":rule la_generic"),
        "Expected la_generic rule, got: {output}"
    );
    // Fractional coefficients must use Real literals for Carcara: (/ 1.0 2.0)
    assert!(
        output.contains("(/ 1.0 2.0)"),
        "Expected (/ 1.0 2.0) for 1/2, got: {output}"
    );
    assert!(
        output.contains("(/ 3.0 4.0)"),
        "Expected (/ 3.0 4.0) for 3/4, got: {output}"
    );
}

#[test]
fn test_format_rational() {
    let mut terms = TermStore::new();
    let rat = terms.mk_rational(num_rational::BigRational::new(1.into(), 2.into()));

    let printer = AlethePrinter::new(&terms);
    let output = printer.format_term(rat);
    assert_eq!(output, "(/ 1.0 2.0)");
}

#[test]
fn test_format_negative_rational() {
    let mut terms = TermStore::new();
    let rat = terms.mk_rational(num_rational::BigRational::new((-3).into(), 4.into()));

    let printer = AlethePrinter::new(&terms);
    let output = printer.format_term(rat);
    assert_eq!(output, "(- (/ 3.0 4.0))");
}

#[test]
fn test_format_bitvector() {
    let mut terms = TermStore::new();
    let bv = terms.mk_bitvec(5.into(), 4);

    let printer = AlethePrinter::new(&terms);
    let output = printer.format_term(bv);
    assert_eq!(output, "#b0101");
}

#[test]
fn test_format_string_constant_uses_canonical_smtlib_literal() {
    let value = r#"say "hi" at C:\tmp"#;
    let mut terms = TermStore::new();
    let string = terms.mk_string(value.to_string());

    let printer = AlethePrinter::new(&terms);
    let output = printer.format_term(string);

    assert_eq!(output, string_literal(value));
    assert_eq!(output, r#""say ""hi"" at C:\tmp""#);
    assert!(
        !output.contains("\\\""),
        "Alethe string output must use doubled quotes, not backslash quotes: {output}"
    );
}

#[test]
fn test_export_alethe_with_problem_scope_declares_auxiliary_symbols_only() {
    let mut terms = TermStore::new();
    let user_a = terms.mk_var("a", Sort::Int);
    let user_b = terms.mk_var("b", Sort::Int);
    let mod_q = terms.mk_var("_mod_q_2", Sort::Int);
    let mod_r = terms.mk_var("_mod_r_3", Sort::Int);
    let sk = terms.mk_var("__ay_ext_diff_1_2", Sort::Int);

    let user_eq = terms.mk_eq(user_a, user_b);
    let q_eq = terms.mk_eq(mod_q, user_a);
    let r_eq = terms.mk_eq(mod_r, user_b);
    let sk_eq = terms.mk_eq(sk, user_a);

    let mut proof = Proof::new();
    proof.add_assume(q_eq, None);
    proof.add_assume(r_eq, None);
    proof.add_assume(sk_eq, None);

    let output = export_alethe_with_problem_scope(&proof, &terms, &[user_eq]);
    assert!(output.contains("(declare-fun _mod_q_2 () Int)"), "{output}");
    assert!(output.contains("(declare-fun _mod_r_3 () Int)"), "{output}");
    assert!(
        output.contains("(declare-fun __ay_ext_diff_1_2 () Int)"),
        "{output}"
    );
    assert!(!output.contains("(declare-fun a () Int)"), "{output}");
    assert!(!output.contains("(declare-fun b () Int)"), "{output}");
}

#[test]
fn test_export_alethe_with_problem_scope_ignores_bound_auxiliary_names() {
    let mut terms = TermStore::new();
    let aux_name = "_mod_q_2".to_string();
    let aux = terms.mk_var(aux_name.clone(), Sort::Int);
    let body = terms.mk_eq(aux, aux);
    let quantified = terms.mk_forall(vec![(aux_name, Sort::Int)], body);

    let mut proof = Proof::new();
    proof.add_assume(quantified, None);

    let output = export_alethe_with_problem_scope(&proof, &terms, &[]);
    assert!(
        !output.contains("(declare-fun _mod_q_2 () Int)"),
        "bound quantifier variable must not be declared as a free symbol: {output}"
    );
}

#[test]
fn test_skolem_variables_declared() {
    let mut terms = TermStore::new();
    // User-declared variable
    let x = terms.mk_var("x", Sort::Int);
    // Skolem variables (mk_fresh_var, not registered in names map)
    let q = terms.mk_fresh_var("_mod_q", Sort::Int);
    let r = terms.mk_fresh_var("_mod_r", Sort::Int);

    // Build a clause referencing all three variables
    let eq_xq = terms.mk_eq(x, q);
    let eq_xr = terms.mk_eq(x, r);

    let mut proof = Proof::new();
    proof.add_theory_lemma("LIA", vec![eq_xq, eq_xr]);

    let output = export_alethe(&proof, &terms);
    assert!(
        output.contains("(declare-fun x () Int)"),
        "Missing declaration for user var x: {output}"
    );
    assert!(
        output.contains("(declare-fun _mod_q_"),
        "Missing declaration for Skolem _mod_q_*: {output}"
    );
    assert!(
        output.contains("(declare-fun _mod_r_"),
        "Missing declaration for Skolem _mod_r_*: {output}"
    );
    // Declarations must appear before proof steps
    let decl_pos = output.find("(declare-fun").unwrap();
    let step_pos = output.find("(step").unwrap();
    assert!(decl_pos < step_pos, "Declarations must precede proof steps");
}

#[test]
fn test_declarations_sorted_by_name() {
    let mut terms = TermStore::new();
    let b = terms.mk_var("b", Sort::Bool);
    let a = terms.mk_var("a", Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(b, None);
    proof.add_assume(a, None);

    let output = export_alethe(&proof, &terms);
    let a_pos = output.find("(declare-fun a").unwrap();
    let b_pos = output.find("(declare-fun b").unwrap();
    assert!(a_pos < b_pos, "Declarations must be sorted by name");
}

// ---------------------------------------------------------------------------
// #8821: Fail-loud on missing FarkasAnnotation.
//
// Prior to #8821, the printer silently rewrote LraFarkas/LiaGeneric steps
// that were missing a FarkasAnnotation into `:rule trust`. The #8759
// terminal-trust detector walks ProofStep::TheoryLemma.kind, not the
// emitted text — so `kind.is_trust()` returned false (the kind was still
// LraFarkas/LiaGeneric), and the downgrade went undetected. These tests
// lock in the fail-loud contract.
// ---------------------------------------------------------------------------

#[test]
fn test_try_export_alethe_fails_on_missing_lra_farkas_annotation() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let eq = terms.mk_eq(x, y);

    let mut proof = Proof::new();
    // Construct an LraFarkas step with no Farkas annotation. We bypass
    // `add_theory_lemma_with_farkas` (which requires coefficients) and go
    // through the raw `add_step` path because the bug we are fixing
    // concerns exactly this shape of step: an arithmetic theory lemma
    // whose kind says "la_generic" but whose annotation is missing.
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![eq],
        farkas: None,
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });

    let result = try_export_alethe(&proof, &terms);
    match result {
        Err(AlethePrintError::MissingFarkasAnnotation {
            theory,
            rule,
            kind,
            step,
        }) => {
            assert_eq!(theory, "LRA", "theory name must round-trip");
            assert_eq!(rule, "la_generic", "expected rule name");
            assert_eq!(kind, "LraFarkas", "expected kind discriminant");
            assert_eq!(step, 0, "offending step must be identified");
        }
        other => panic!("expected MissingFarkasAnnotation error, got: {other:?}"),
    }
}

#[test]
fn test_try_export_alethe_fails_on_missing_lia_generic_annotation() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let eq = terms.mk_eq(a, b);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![eq],
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });

    match try_export_alethe(&proof, &terms) {
        Err(AlethePrintError::MissingFarkasAnnotation { rule, kind, .. }) => {
            assert_eq!(rule, "lia_generic");
            assert_eq!(kind, "LiaGeneric");
        }
        other => panic!("expected MissingFarkasAnnotation error, got: {other:?}"),
    }
}

#[test]
fn test_try_export_alethe_fails_closed_on_array_extensionality() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("a", array_sort.clone());
    let b = terms.mk_var("b", array_sort);
    let k = terms.mk_var("__ext_diff_1_2", Sort::Int);
    let eq_ab = terms.mk_eq(a, b);
    let sel_a = terms.mk_select(a, k);
    let sel_b = terms.mk_select(b, k);
    let sel_eq = terms.mk_eq(sel_a, sel_b);
    let not_sel_eq = terms.mk_not(sel_eq);
    let ext_clause = terms.mk_or(vec![eq_ab, not_sel_eq]);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause: vec![ext_clause],
        farkas: None,
        kind: TheoryLemmaKind::ArrayExtensionality,
        lia: None,
    });

    assert!(matches!(
        try_export_alethe(&proof, &terms),
        Err(AlethePrintError::UnsupportedArrayExtensionality { id }) if id == ProofId(0)
    ));

    let output = export_alethe(&proof, &terms);
    assert!(
        !output.contains(":rule extensionality"),
        "unsupported external rule must never be emitted: {output}"
    );
    assert!(
        output.contains("UNVERIFIABLE PROOF") && output.contains("(error"),
        "infallible export must fail loudly: {output}"
    );
}

#[test]
fn test_export_alethe_never_emits_silent_trust_for_lra_farkas() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let eq = terms.mk_eq(x, y);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LRA".to_string(),
        clause: vec![eq],
        farkas: None,
        kind: TheoryLemmaKind::LraFarkas,
        lia: None,
    });

    // The infallible path MUST NOT emit a `(step ... :rule trust ...)`
    // command — that was exactly the silent-downgrade path #8821 closes.
    // Instead it emits a loudly marked unverifiable document.
    let output = export_alethe(&proof, &terms);
    assert!(
        !output.contains("(step"),
        "export_alethe must not emit any (step ...) commands when rendering fails; got:\n{output}"
    );
    assert!(
        output.contains("UNVERIFIABLE PROOF"),
        "export_alethe must emit an UNVERIFIABLE PROOF marker; got:\n{output}"
    );
    assert!(
        output.contains("(error"),
        "unverifiable output must be an (error ...) S-expression that downstream checkers will reject; got:\n{output}"
    );
    // The only `trust` string permitted in this output is the explanatory
    // comment that *no* trust fallback will be written. A downstream
    // Carcara run will encounter `(error ...)` first and refuse the file,
    // but we still assert the stronger invariant: no emitted proof step
    // bears the trust rule.
}

#[test]
fn test_export_alethe_with_problem_scope_fails_loud_on_missing_farkas() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let y = terms.mk_var("y", Sort::Real);
    let eq = terms.mk_eq(x, y);

    let mut proof = Proof::new();
    proof.add_step(ProofStep::TheoryLemma {
        theory: "LIA".to_string(),
        clause: vec![eq],
        farkas: None,
        kind: TheoryLemmaKind::LiaGeneric,
        lia: None,
    });

    let output = export_alethe_with_problem_scope(&proof, &terms, &[]);
    assert!(
        !output.contains("(step"),
        "emitted a (step ...) on unverifiable path: {output}"
    );
    assert!(
        output.contains("UNVERIFIABLE PROOF"),
        "missing UNVERIFIABLE marker: {output}"
    );
    assert!(
        output.contains("(error"),
        "missing (error ...) sentinel: {output}"
    );
}

#[test]
fn test_try_export_alethe_generic_trust_is_still_allowed() {
    // TheoryLemmaKind::Generic is the explicit "we know this is trust"
    // kind — the #8759 detector recognizes it via `kind.is_trust()`. The
    // printer should continue to emit those faithfully so the detector
    // can flag them. Only the *silent* downgrade from LraFarkas/LiaGeneric
    // is forbidden.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq = terms.mk_eq(x, y);

    let mut proof = Proof::new();
    proof.add_theory_lemma("EUF", vec![eq]); // default kind = Generic

    let output = try_export_alethe(&proof, &terms)
        .expect("Generic kind is a first-class :rule trust, not a silent downgrade");
    assert!(
        output.contains(":rule trust"),
        "Generic kind should still emit trust: {output}"
    );
}

// NOTE: Carcara integration tests deleted - required external carcara tool (#596)
// Deleted tests: test_carcara_verification, test_carcara_eq_transitive,
// test_carcara_eq_congruent, test_carcara_la_generic
// Run carcara tests manually with: cargo install carcara && CARCARA_PATH=carcara cargo test

/// An or_pos/or_neg tautology whose or-term carries a surface-syntax
/// override `(=> A B)` must print as the spec-correct implies_* rule with
/// the implication's literal order — carcara parses the printed override
/// back as an implication, and or_pos over an implication is invalid Alethe.
#[test]
fn test_or_pos_with_implies_override_resugars_to_implies_pos() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofStep, TermData};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a".to_string(), Sort::Bool);
    let b = terms.mk_var("b".to_string(), Sort::Bool);
    let imp = terms.mk_implies(a, b); // internally (or (not a) b) (possibly reordered)
    let not_imp = terms.mk_not_raw(imp);
    let (d0, d1) = match terms.get(imp) {
        TermData::App(_, args) => (args[0], args[1]),
        other => panic!("expected desugared or app, got {other:?}"),
    };

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(imp, "(=> a b)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    // or_pos: (cl (not s) d0 d1) with s printed as (=> a b).
    let step = ProofStep::Step {
        rule: AletheRule::OrPos(0),
        clause: vec![not_imp, d0, d1],
        premises: vec![],
        args: vec![imp],
    };
    let printed = printer.format_step(&step, ProofId(3)).unwrap();
    assert_eq!(
        printed,
        "(step t3 (cl (not (=> a b)) (not a) b) :rule implies_pos)"
    );

    // or_neg over the consequent: (cl s (not b)) -> implies_neg2.
    let not_b = terms.mk_not_raw(b);
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let step = ProofStep::Step {
        rule: AletheRule::OrNeg,
        clause: vec![imp, not_b],
        premises: vec![],
        args: vec![imp],
    };
    let printed = printer.format_step(&step, ProofId(4)).unwrap();
    assert_eq!(
        printed,
        "(step t4 (cl (=> a b) (not b)) :rule implies_neg2)"
    );
}

/// or_neg over a NEGATED disjunct: the traced clause literal is the
/// double-negation-stripped inner term, but strict Alethe concludes
/// `(cl (or ...) (not (not a)))`. The printer must emit the honest
/// double-negated or_neg (with its position arg), a `not_not` bridge
/// step, and a resolution restoring the traced clause under the step's
/// own id.
#[test]
fn test_or_neg_infers_position_arg_for_negated_disjunct() {
    use ay_core::{ProofStep, TermData};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a".to_string(), Sort::Bool);
    let b = terms.mk_var("b".to_string(), Sort::Bool);
    let not_a = terms.mk_not(a);
    let or_term = terms.mk_or(vec![b, not_a]);
    let pos = match terms.get(or_term) {
        TermData::App(_, args) => args.iter().position(|&d| d == not_a).unwrap(),
        other => panic!("expected or app, got {other:?}"),
    };

    let printer = AlethePrinter::new(&terms);
    let step = ProofStep::Step {
        rule: AletheRule::OrNeg,
        clause: vec![or_term, a],
        premises: vec![],
        args: vec![or_term],
    };
    let printed = printer.format_step(&step, ProofId(7)).unwrap();
    assert_eq!(
        printed,
        format!(
            "(step t7a (cl (or b (not a)) (not (not a))) :rule or_neg :args ({pos}))\n\
             (step t7b0 (cl (not (not (not a))) a) :rule not_not)\n\
             (step t7 (cl (or b (not a)) a) :rule resolution :premises (t7a t7b0))"
        )
    );
}

#[test]
fn args_free_and_neg_bridges_compact_double_negation() {
    use ay_core::{ProofStep, Symbol};

    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let not_p = terms.mk_not_raw(p);
    let le = terms.mk_app(Symbol::named("<="), [x, y], Sort::Bool);
    let not_le = terms.mk_not_raw(le);
    let source = terms.mk_app(Symbol::named("and"), [not_p, le], Sort::Bool);
    let step = ProofStep::Step {
        rule: AletheRule::AndNeg,
        clause: vec![source, p, not_le],
        premises: vec![],
        args: vec![],
    };

    let printer = AlethePrinter::new(&terms);
    let printed = printer.format_step(&step, ProofId(5)).unwrap();
    assert!(printed.contains("(step t5a"), "{printed}");
    assert!(printed.contains(":rule and_neg"), "{printed}");
    assert!(printed.contains("(step t5b0"), "{printed}");
    assert!(printed.contains(":rule not_not"), "{printed}");
    assert!(
        printed.contains("(step t5 (cl (and (not p) (<= x y)) p (not (<= x y))) :rule resolution"),
        "{printed}"
    );
}

#[test]
fn problem_scoped_export_rejects_reachable_transformed_assume() {
    let mut terms = TermStore::new();
    let authored = terms.mk_var("authored", Sort::Bool);
    let transformed = terms.mk_var("preprocessed", Sort::Bool);
    let not_transformed = terms.mk_not_raw(transformed);

    let mut proof = Proof::new();
    let transformed_id = proof.add_assume(transformed, None);
    let negated_id = proof.add_assume(not_transformed, None);
    proof.add_resolution(vec![], transformed, transformed_id, negated_id);

    let err = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[authored, not_transformed],
        None,
    )
    .expect_err("a load-bearing transformed conjunction must not be exportable");
    assert!(matches!(err, AlethePrintError::NonProblemAssume { term, .. } if term == transformed));
}

#[test]
fn certified_skolem_step_expands_to_choice_anchor_without_free_witness() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let p_i = terms.mk_app(Symbol::named("P"), [i], Sort::Bool);
    let q_i = terms.mk_app(Symbol::named("Q"), [i], Sort::Bool);
    let not_p_i = terms.mk_not_raw(p_i);
    let body = terms.mk_app(Symbol::named("or"), [not_p_i, q_i], Sort::Bool);
    let quantified = terms.mk_forall(vec![("i".to_string(), Sort::Int)], body);

    let witness = terms.mk_var("sk!i_printer", Sort::Int);
    terms.mark_skolem_symbol("sk!i_printer");
    let p_w = terms.mk_app(Symbol::named("P"), [witness], Sort::Bool);
    let q_w = terms.mk_app(Symbol::named("Q"), [witness], Sort::Bool);
    let not_p_w = terms.mk_not_raw(p_w);
    let instance = terms.mk_app(Symbol::named("or"), [not_p_w, q_w], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(body, "(=> (P i) (Q i))".to_string());
    overrides.insert(
        quantified,
        "(forall ((i Int)) (=> (P i) (Q i)))".to_string(),
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified],
        Some(&overrides),
    )
    .expect("certified Skolem expansion must render");
    assert!(
        output.contains(
            "(anchor :step t0 :args ((:= (i Int) (choice ((i Int)) (not (=> (P i) (Q i)))))))"
        ),
        "{output}"
    );
    assert!(
        output.contains("(step t0.t1 (cl (= (=> (P i) (Q i)) (=> (P (choice"),
        "{output}"
    );
    assert!(output.contains(":rule sko_forall"), "{output}");
    assert!(!output.contains("declare-fun sk!i_printer"), "{output}");
    assert!(!output.contains(":rule trust"), "{output}");
}

/// A quantified implication with a conjunction antecedent is internally a
/// flattened n-ary or. Every command in the expanded `sko_forall` must still
/// use the authored implication identity, and its `or_neg` tautologies must
/// be rebuilt from spec-valid implication/conjunction rules.
#[test]
fn certified_skolem_flattened_implication_has_one_surface_identity() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let p_i = terms.mk_app(Symbol::named("P"), [i], Sort::Bool);
    let q_i = terms.mk_app(Symbol::named("Q"), [i], Sort::Bool);
    let r_i = terms.mk_app(Symbol::named("R"), [i], Sort::Bool);
    let not_p_i = terms.mk_not_raw(p_i);
    let not_q_i = terms.mk_not_raw(q_i);
    let body = terms.mk_app(Symbol::named("or"), [not_p_i, not_q_i, r_i], Sort::Bool);
    let quantified = terms.mk_forall(vec![("i".to_string(), Sort::Int)], body);

    let witness = terms.mk_var("sk!i_flat_printer", Sort::Int);
    terms.mark_skolem_symbol("sk!i_flat_printer");
    let p_w = terms.mk_app(Symbol::named("P"), [witness], Sort::Bool);
    let q_w = terms.mk_app(Symbol::named("Q"), [witness], Sort::Bool);
    let r_w = terms.mk_app(Symbol::named("R"), [witness], Sort::Bool);
    let not_p_w = terms.mk_not_raw(p_w);
    let not_q_w = terms.mk_not_raw(q_w);
    let not_r_w = terms.mk_not_raw(r_w);
    let instance = terms.mk_app(Symbol::named("or"), [not_p_w, not_q_w, r_w], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);
    proof.add_rule_step(
        AletheRule::OrNeg,
        vec![instance, p_w],
        vec![],
        vec![instance],
    );
    proof.add_rule_step(
        AletheRule::OrNeg,
        vec![instance, q_w],
        vec![],
        vec![instance],
    );
    proof.add_rule_step(
        AletheRule::OrNeg,
        vec![instance, not_r_w],
        vec![],
        vec![instance],
    );

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(body, "(=> (and (P i) (Q i)) (R i))".to_string());
    overrides.insert(p_i, "(P i)".to_string());
    overrides.insert(q_i, "(Q i)".to_string());
    overrides.insert(r_i, "(R i)".to_string());
    overrides.insert(
        quantified,
        "(forall ((i Int)) (=> (and (P i) (Q i)) (R i)))".to_string(),
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[quantified],
        Some(&overrides),
    )
    .expect("flattened implication Skolem proof must render");
    assert!(
        output.contains("(choice ((i Int)) (not (=> (and (P i) (Q i)) (R i))))"),
        "{output}"
    );
    assert!(
        output.contains("(step t0.t1 (cl (= (=> (and (P i) (Q i)) (R i)) (=> (and"),
        "{output}"
    );
    assert!(output.contains("(step t1.imp"), "{output}");
    assert!(output.contains(":rule implies_neg1"), "{output}");
    assert!(output.contains(":rule and_pos :args (0)"), "{output}");
    assert!(output.contains(":rule and_pos :args (1)"), "{output}");
    assert!(output.contains(":rule implies_neg2"), "{output}");
    assert!(!output.contains("(choice ((i Int)) (not (or"), "{output}");
    assert!(!output.contains(":rule or_neg"), "{output}");
    assert!(
        !output.contains("declare-fun sk!i_flat_printer"),
        "{output}"
    );
    assert!(!output.contains(":rule trust"), "{output}");
}

/// An or_pos step over an or-term whose surface override reorders the
/// disjuncts must print the disjunct literals in the PRINTED operand order
/// (carcara checks or_pos literals against the printed or-term's own
/// argument order).
#[test]
fn test_or_pos_reorders_literals_to_surface_operand_order() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofStep, TermData};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a".to_string(), Sort::Bool);
    let b = terms.mk_var("b".to_string(), Sort::Bool);
    let not_a = terms.mk_not(a);
    let or_term = terms.mk_or(vec![not_a, b]); // canonicalizes to (or b (not a))
    let not_or = terms.mk_not_raw(or_term);
    let (d0, d1) = match terms.get(or_term) {
        TermData::App(_, args) => (args[0], args[1]),
        other => panic!("expected or app, got {other:?}"),
    };
    assert_eq!((d0, d1), (b, not_a), "test requires canonical reorder");

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(or_term, "(or (not a) b)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let step = ProofStep::Step {
        rule: AletheRule::OrPos(0),
        clause: vec![not_or, d0, d1],
        premises: vec![],
        args: vec![or_term],
    };
    let printed = printer.format_step(&step, ProofId(4)).unwrap();
    assert_eq!(
        printed,
        "(step t4 (cl (not (or (not a) b)) (not a) b) :rule or_pos)"
    );
}

/// A xor_neg tautology whose xor-term's surface override swaps the operands
/// must print as the sibling spec variant over the printed operand order,
/// with `not_not` bridges for double-negation-stripped literals.
#[test]
fn test_xor_neg_swaps_variant_for_surface_operand_order() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofStep, TermData};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a".to_string(), Sort::Bool);
    let b = terms.mk_var("b".to_string(), Sort::Bool);
    let not_a = terms.mk_not(a);
    let xor_term = terms.mk_xor(not_a, b);
    let TermData::App(_, xargs) = terms.get(xor_term) else {
        panic!("expected xor app");
    };
    // Internal operand order (canonicalized); traced clause literals are the
    // double-negation-stripped forms the Tseitin tracer produces:
    // xor_neg1 over internal ops (x0, x1) is (cl s x0 (not x1)).
    let (x0, x1) = (xargs[0], xargs[1]);
    let neg_x1 = terms.mk_not(x1); // strips when x1 is a negation
    let clause = vec![xor_term, x0, neg_x1];

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(xor_term, "(xor (not a) b)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let step = ProofStep::Step {
        rule: AletheRule::XorNeg1,
        clause,
        premises: vec![],
        args: vec![xor_term],
    };
    let printed = printer.format_step(&step, ProofId(9)).unwrap();
    // Every literal of the final step must match the traced clause exactly,
    // and the tautology step must use printed-operand spec shape.
    assert!(
        printed.contains(":rule not_not")
            && printed.contains(":rule resolution :premises (t9a")
            && printed.starts_with("(step t9a (cl (xor (not a) b) "),
        "expected honest spec tautology + not_not bridge + resolution: {printed}"
    );
}

/// A surface `>=` override on one side of a canonical `<=` congruence must
/// not turn the printed `cong` into a different-operator application. Prove
/// the surface/canonical comparison identity, apply canonical congruence, and
/// compose the two equalities.
#[test]
fn test_cong_with_surface_order_reversal_uses_canonical_bridge() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq_xy = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let lower_x = terms.mk_app(Symbol::named("<="), [k, x], Sort::Bool);
    let lower_y = terms.mk_app(Symbol::named("<="), [k, y], Sort::Bool);
    let comparison_eq = terms.mk_app(Symbol::named("="), [lower_x, lower_y], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(eq_xy, None);
    proof.add_rule_step(AletheRule::Cong, vec![comparison_eq], vec![premise], vec![]);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(lower_x, "(>= x k)".to_string());
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[eq_xy],
        Some(&overrides),
    )
    .expect("exact order reversal has a certified congruence bridge");

    assert!(
        output.contains(
            "(step t1.norm (cl (= (>= x k) (<= k x))) :rule comp_simplify)\n\
             (step t1.cong (cl (= (<= k x) (<= k y))) :rule cong :premises (t0))\n\
             (step t1 (cl (= (>= x k) (<= k y))) :rule trans :premises (t1.norm t1.cong))"
        ),
        "{output}"
    );
}

/// The congruence bridge must not infer an equivalence for a merely similar
/// override: strict `>` is not the same comparison as canonical `<=`.
#[test]
fn test_cong_bridge_rejects_non_equivalent_surface_order() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq_xy = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let lower_x = terms.mk_app(Symbol::named("<="), [k, x], Sort::Bool);
    let lower_y = terms.mk_app(Symbol::named("<="), [k, y], Sort::Bool);
    let comparison_eq = terms.mk_app(Symbol::named("="), [lower_x, lower_y], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(eq_xy, None);
    proof.add_rule_step(AletheRule::Cong, vec![comparison_eq], vec![premise], vec![]);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(lower_x, "(> x k)".to_string());
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[eq_xy],
        Some(&overrides),
    )
    .expect_err("an unrelated order override must fail closed");
    assert!(
        matches!(error, AlethePrintError::InvalidCongruenceStep { .. }),
        "{error}"
    );
}

#[test]
fn test_eq_congruent_bridge_repairs_exact_multiplication_operand_swap() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let c = terms.mk_var("c", Sort::Int);
    let s = terms.mk_var("s", Sort::Int);
    let sixteen = terms.mk_int(16.into());
    let seven = terms.mk_int(7.into());
    let mul = terms.mk_app(Symbol::named("*"), [c, sixteen], Sort::Int);
    let left = terms.mk_app(Symbol::named("+"), [mul, s], Sort::Int);
    let right = terms.mk_app(Symbol::named("+"), [mul, seven], Sort::Int);
    let mul_refl = terms.mk_app(Symbol::named("="), [mul, mul], Sort::Bool);
    let s_eq_seven = terms.mk_app(Symbol::named("="), [s, seven], Sort::Bool);
    let conclusion = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let not_mul_refl = terms.mk_not_raw(mul_refl);
    let not_s_eq_seven = terms.mk_not_raw(s_eq_seven);

    let mut proof = Proof::new();
    proof.add_rule_step(
        AletheRule::EqCongruent,
        vec![not_mul_refl, not_s_eq_seven, conclusion],
        Vec::new(),
        Vec::new(),
    );
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(left, "(+ (* 16 c) s)".to_string());

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], Some(&overrides))
            .expect("exact multiplication swap has an ACI congruence bridge");
    assert!(
        output.contains("(step t0.ac (cl (= (* 16 c) (* c 16))) :rule aci_simp)"),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.eqc (cl (not (= (* 16 c) (* c 16))) \
             (not (= s 7)) (= (+ (* 16 c) s) (+ (* c 16) 7))) \
             :rule eq_congruent)"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0 (cl (not (= (* c 16) (* c 16))) (not (= s 7)) \
             (= (+ (* 16 c) s) (+ (* c 16) 7))) \
             :rule resolution :premises (t0.eqc t0.acw))"
        ),
        "{output}"
    );
}

#[test]
fn test_surface_distinct_resolution_mismatch_fails_closed() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);

    let mut proof = Proof::new();
    let distinct_assume = proof.add_assume(disequality, None);
    let equality_assume = proof.add_assume(equality, None);
    proof.add_resolution(Vec::new(), equality, distinct_assume, equality_assume);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(disequality, "(distinct (ite true x w) y)".to_string());
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[disequality, equality],
        Some(&overrides),
    )
    .expect_err("a surface pivot with different operands must not fall through");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error}"
    );
}

#[test]
fn test_surface_distinct_non_unit_resolution_mismatch_fails_closed() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let p = terms.mk_var("p", Sort::Bool);
    let q = terms.mk_var("q", Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let disequality = terms.mk_not_raw(equality);

    let mut proof = Proof::new();
    let distinct_clause = proof.add_theory_lemma("test", vec![disequality, p]);
    let equality_clause = proof.add_theory_lemma("test", vec![equality, q]);
    proof.add_resolution(vec![p, q], equality, distinct_clause, equality_clause);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(disequality, "(distinct x y)".to_string());
    let error =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], Some(&overrides))
            .expect_err("a non-unit distinct/equality surface pivot must not fall through");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error}"
    );

    let mut generic_proof = Proof::new();
    let distinct_clause = generic_proof.add_theory_lemma("test", vec![disequality, p]);
    let equality_clause = generic_proof.add_theory_lemma("test", vec![equality, q]);
    generic_proof.add_rule_step(
        AletheRule::ThResolution,
        vec![p, q],
        vec![distinct_clause, equality_clause],
        vec![equality],
    );
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &generic_proof,
        &terms,
        &[],
        Some(&overrides),
    )
    .expect_err("a generic non-unit distinct/equality surface pivot must not fall through");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error}"
    );
}

#[test]
fn test_surface_distinct_over_canonical_and_pos_fails_closed() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let z = terms.mk_var("z", Sort::Int);
    let eq_xy = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let eq_xz = terms.mk_app(Symbol::named("="), [x, z], Sort::Bool);
    let neq_xy = terms.mk_not_raw(eq_xy);
    let neq_xz = terms.mk_not_raw(eq_xz);
    let conjunction = terms.mk_app(Symbol::named("and"), [neq_xy, neq_xz], Sort::Bool);
    let not_conjunction = terms.mk_not_raw(conjunction);
    let step = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: vec![not_conjunction, neq_xy],
        premises: Vec::new(),
        args: vec![conjunction],
    };
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(conjunction, "(distinct (ite true x w) y z)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let error = printer
        .format_step(&step, ProofId(0))
        .expect_err("and_pos over a printed distinct term must fail closed");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error}"
    );
}

#[test]
fn test_array_row1_uses_checked_arrays_idx_rule() {
    use ay_core::{ArraySort, Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int))),
    );
    let index = terms.mk_var("i", Sort::Int);
    let value = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(array, index, value);
    let select = terms.mk_app(Symbol::named("select"), [store, index], Sort::Int);
    let row = terms.mk_app(Symbol::named("="), [select, value], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "array",
        vec![row],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    );
    let output = try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], None)
        .expect("unit ROW1 has a checked external rule");
    assert!(
        output.contains("(step t0 (cl (= (select (store a i v) i) v)) :rule arrays_idx)"),
        "{output}"
    );
    assert!(!output.contains("read_over_write_pos"), "{output}");
}

#[test]
fn test_array_conditional_reversed_row1_uses_congruence_subproof() {
    use ay_core::{ArraySort, Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int))),
    );
    let store_index = terms.mk_var("i", Sort::Int);
    let read_index = terms.mk_var("j", Sort::Int);
    let value = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(array, store_index, value);
    let select = terms.mk_app(Symbol::named("select"), [store, read_index], Sort::Int);
    let reversed_row = terms.mk_app(Symbol::named("="), [value, select], Sort::Bool);
    let index_eq = terms.mk_app(Symbol::named("="), [store_index, read_index], Sort::Bool);
    let guard = terms.mk_not_raw(index_eq);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "array",
        vec![guard, reversed_row],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    );
    let output = try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], None)
        .expect("conditional reversed ROW1 has a checked external subproof");

    assert!(output.contains("(anchor :step t0)"), "{output}");
    assert!(output.contains("(assume t0.h (= i j))"), "{output}");
    assert!(
        output.contains("(step t0.idx (cl (= (select (store a i v) i) v)) :rule arrays_idx)"),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.cong (cl (= (select (store a i v) i) \
             (select (store a i v) j))) :rule cong :premises (t0.h))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.base (cl (= (select (store a i v) j) v)) \
             :rule trans :premises (t0.congs t0.idx))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.row (cl (= v (select (store a i v) j))) \
             :rule symm :premises (t0.base))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0 (cl (not (= i j)) (= v (select (store a i v) j))) \
             :rule subproof :discharge (t0.h))"
        ),
        "{output}"
    );
}

#[test]
fn test_array_packed_conditional_row1_bridges_decimal_store_value() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ArraySort, Symbol, TheoryLemmaKind};
    use num_rational::BigRational;

    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Real))),
    );
    let store_index = terms.mk_var("i", Sort::Int);
    let read_index = terms.mk_int(0.into());
    let value = terms.mk_rational(BigRational::new(3.into(), 2.into()));
    let store = terms.mk_store(array, store_index, value);
    let select = terms.mk_app(Symbol::named("select"), [store, read_index], Sort::Real);
    let reversed_row = terms.mk_app(Symbol::named("="), [value, select], Sort::Bool);
    let index_eq = terms.mk_app(Symbol::named("="), [store_index, read_index], Sort::Bool);
    let guard = terms.mk_not_raw(index_eq);
    let packed = terms.mk_app(Symbol::named("or"), [guard, reversed_row], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "array",
        vec![packed],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    );
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(select, "(select (store a i 1.5) 0)".to_string());
    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], Some(&overrides))
            .expect("packed conditional ROW1 preserves its unit or-term");

    assert!(
        output.contains("(step t0.val (cl (= 1.5 (/ 3.0 2.0))) :rule la_generic :args (1))"),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.flat (cl (not (= i 0)) \
             (= (/ 3.0 2.0) (select (store a i 1.5) 0))) \
             :rule subproof :discharge (t0.h))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0 (cl (or (not (= i 0)) \
             (= (/ 3.0 2.0) (select (store a i 1.5) 0)))) \
             :rule resolution :premises (t0.r0 t0.o1))"
        ),
        "{output}"
    );
}

#[test]
fn test_array_row1_rejects_inequivalent_numeric_store_override() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ArraySort, Symbol, TheoryLemmaKind};
    use num_rational::BigRational;

    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Real))),
    );
    let index = terms.mk_var("i", Sort::Int);
    let value = terms.mk_rational(BigRational::new(3.into(), 2.into()));
    let store = terms.mk_store(array, index, value);
    let select = terms.mk_app(Symbol::named("select"), [store, index], Sort::Real);
    let row = terms.mk_app(Symbol::named("="), [select, value], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "array",
        vec![row],
        TheoryLemmaKind::ArraySelectStore { index_eq: true },
    );
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(select, "(select (store a i 999.0) i)".to_string());
    let error =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], Some(&overrides))
            .expect_err("an inequivalent numeric store override must fail closed");
    assert!(
        matches!(error, AlethePrintError::InvalidArrayStep { .. }),
        "{error}"
    );
}

#[test]
fn test_array_printer_empty_row_shapes_fail_closed_without_panic() {
    use ay_core::{Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let empty_or = terms.mk_app(Symbol::named("or"), Vec::<TermId>::new(), Sort::Bool);
    for clause in [Vec::new(), vec![empty_or]] {
        let mut proof = Proof::new();
        proof.add_theory_lemma_with_kind(
            "array",
            clause,
            TheoryLemmaKind::ArraySelectStore { index_eq: true },
        );
        let error = try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], None)
            .expect_err("empty ROW shape must fail closed");
        assert!(
            matches!(error, AlethePrintError::InvalidArrayStep { .. }),
            "{error}"
        );
    }
}

#[test]
fn test_array_row2_uses_checked_arrays_row_subproof() {
    use ay_core::{ArraySort, Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int))),
    );
    let store_index = terms.mk_var("i", Sort::Int);
    let read_index = terms.mk_var("j", Sort::Int);
    let value = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(array, store_index, value);
    let stored_select = terms.mk_app(Symbol::named("select"), [store, read_index], Sort::Int);
    let base_select = terms.mk_app(Symbol::named("select"), [array, read_index], Sort::Int);
    let row = terms.mk_app(Symbol::named("="), [stored_select, base_select], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("="), [store_index, read_index], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "array",
        vec![guard, row],
        TheoryLemmaKind::ArraySelectStore { index_eq: false },
    );
    let output = try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], None)
        .expect("guarded ROW2 has a checked external subproof");
    assert!(output.contains("(anchor :step t0.sp)"), "{output}");
    assert!(output.contains("(assume t0.h (not (= i j)))"), "{output}");
    assert!(
        output.contains(
            "(step t0.row (cl (= (select (store a i v) j) (select a j))) \
             :rule arrays_row :premises (t0.h))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.sp (cl (not (not (= i j))) \
             (= (select (store a i v) j) (select a j))) \
             :rule subproof :discharge (t0.h))"
        ),
        "{output}"
    );
    assert!(
        output.contains("(step t0.nn (cl (not (not (not (= i j)))) (= i j)) :rule not_not)"),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0 (cl (= i j) (= (select (store a i v) j) (select a j))) \
             :rule resolution :premises (t0.sp t0.nn))"
        ),
        "{output}"
    );
    assert!(!output.contains("read_over_write_neg"), "{output}");
}

/// Sub-schema (A) of `ArrayRowChain`: the walk over
/// `(select (store (store (store a i1 e1) i2 e2) i3 e3) i1)` must lower to one
/// `arrays_row` per SKIPPED store plus a terminating `arrays_idx`, all inside a
/// subproof whose assumptions are the negations of the clause's own index
/// guards — never the unknown `read_over_write_chain` rule name.
#[test]
fn test_array_row_chain_eval_lowers_to_arrays_row_and_idx() {
    use ay_core::{ArraySort, Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int))),
    );
    let i1 = terms.mk_var("i1", Sort::Int);
    let i2 = terms.mk_var("i2", Sort::Int);
    let i3 = terms.mk_var("i3", Sort::Int);
    let e1 = terms.mk_var("e1", Sort::Int);
    let e2 = terms.mk_var("e2", Sort::Int);
    let e3 = terms.mk_var("e3", Sort::Int);
    let s1 = terms.mk_store(array, i1, e1);
    let s2 = terms.mk_store(s1, i2, e2);
    let s3 = terms.mk_store(s2, i3, e3);
    let select = terms.mk_app(Symbol::named("select"), [s3, i1], Sort::Int);
    let row = terms.mk_app(Symbol::named("="), [select, e1], Sort::Bool);
    let g2 = terms.mk_app(Symbol::named("="), [i1, i2], Sort::Bool);
    let g3 = terms.mk_app(Symbol::named("="), [i1, i3], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("array", vec![g2, g3, row], TheoryLemmaKind::ArrayRowChain);
    let output = try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], None)
        .expect("row-chain evaluation has a checked external derivation");

    assert!(!output.contains("read_over_write_chain"), "{output}");
    assert!(output.contains("(anchor :step t0.sp)"), "{output}");
    // The outermost store is skipped first, so its guard is assumed first.
    assert!(
        output.contains("(assume t0.h0 (not (= i1 i3)))"),
        "{output}"
    );
    assert!(
        output.contains("(assume t0.h1 (not (= i1 i2)))"),
        "{output}"
    );
    // `arrays_row` demands `(not (= store_index read_index))`, the mirror of
    // the clause's own `(= i1 i3)` spelling: bridged with `not_symm`.
    assert!(
        output.contains("(step t0.s0 (cl (not (= i3 i1))) :rule not_symm :premises (t0.h0))"),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.p0 (cl (= (select (store (store (store a i1 e1) i2 e2) i3 e3) i1) \
             (select (store (store a i1 e1) i2 e2) i1))) :rule arrays_row :premises (t0.s0))"
        ),
        "{output}"
    );
    assert!(
        output.contains("(step t0.pidx (cl (= (select (store a i1 e1) i1) e1)) :rule arrays_idx)"),
        "{output}"
    );
    assert!(
        output.contains(":rule trans :premises (t0.p0 t0.p1 t0.pidx)"),
        "{output}"
    );
    // The closing resolution reproduces the ORIGINAL clause byte-for-byte, so
    // every downstream premise reference is unaffected.
    assert!(
        output.contains(
            "(step t0 (cl (= i1 i2) (= i1 i3) \
             (= (select (store (store (store a i1 e1) i2 e2) i3 e3) i1) e1)) \
             :rule resolution :premises (t0.sp t0.nn0 t0.nn1))"
        ),
        "{output}"
    );
}

/// Sub-schema (B) of `ArrayRowChain`: the two walks are transported across the
/// assumed array equality with `cong`, and the packed unit `or` is restored
/// with one `or_neg` per disjunct.
#[test]
fn test_array_row_chain_under_array_equality_uses_cong() {
    use ay_core::{ArraySort, Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort);
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let store = terms.mk_store(b, i, v);
    let array_eq = terms.mk_app(Symbol::named("="), [a, store], Sort::Bool);
    let premise = terms.mk_not_raw(array_eq);
    let select = terms.mk_app(Symbol::named("select"), [a, i], Sort::Int);
    let row = terms.mk_app(Symbol::named("="), [v, select], Sort::Bool);
    let packed = terms.mk_app(Symbol::named("or"), [premise, row], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("array", vec![packed], TheoryLemmaKind::ArrayRowChain);
    let output = try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], None)
        .expect("row chain under an array equality has a checked external derivation");

    assert!(!output.contains("read_over_write_chain"), "{output}");
    assert!(
        output.contains("(assume t0.h0 (= a (store b i v)))"),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.cong (cl (= (select a i) (select (store b i v) i))) \
             :rule cong :premises (t0.h0))"
        ),
        "{output}"
    );
    assert!(
        output.contains("(step t0.ridx (cl (= (select (store b i v) i) v)) :rule arrays_idx)"),
        "{output}"
    );
    // No guards to discharge: `resolution` would have a single premise, so the
    // subproof clause is re-ordered into the original literal order instead.
    assert!(
        output.contains(
            "(step t0.flat (cl (not (= a (store b i v))) (= v (select a i))) \
             :rule reordering :premises (t0.sp))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.o0 (cl (or (not (= a (store b i v))) (= v (select a i))) \
             (not (not (= a (store b i v))))) :rule or_neg :args (0))"
        ),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0 (cl (or (not (= a (store b i v))) (= v (select a i)))) \
             :rule resolution :premises (t0.flat t0.o0 t0.o1))"
        ),
        "{output}"
    );
}

/// Fail-closed: when a surface override re-spells the `store` node so the
/// printed text is no longer the compositional rendering of the certified
/// term, the printer must NOT reconstruct a derivation from those strings. It
/// keeps the honest (externally uncheckable) `read_over_write_chain` name.
#[test]
fn test_array_row_chain_non_compositional_surface_falls_back() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ArraySort, Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int))),
    );
    let i1 = terms.mk_var("i1", Sort::Int);
    let i2 = terms.mk_var("i2", Sort::Int);
    let e1 = terms.mk_var("e1", Sort::Int);
    let e2 = terms.mk_var("e2", Sort::Int);
    let s1 = terms.mk_store(array, i1, e1);
    let s2 = terms.mk_store(s1, i2, e2);
    let select = terms.mk_app(Symbol::named("select"), [s2, i1], Sort::Int);
    let row = terms.mk_app(Symbol::named("="), [select, e1], Sort::Bool);
    let guard = terms.mk_app(Symbol::named("="), [i1, i2], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("array", vec![guard, row], TheoryLemmaKind::ArrayRowChain);

    // The inner store prints under a `let` abbreviation, so `(store …)` at the
    // outer node no longer splits into the separately printed inner array.
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(
        s2,
        "(let ((?v_0 (store a i1 e1))) (store ?v_0 i2 e2))".to_string(),
    );
    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[], Some(&overrides))
            .expect("fallback emission still produces a document");
    assert!(output.contains(":rule read_over_write_chain"), "{output}");
    assert!(!output.contains("arrays_row"), "{output}");
    assert!(!output.contains("arrays_idx"), "{output}");
}

/// #A2b synthesized-default emission budget: an exhausted work budget must
/// surface as a typed `EmissionBudgetExhausted` error (the caller degrades to
/// the honest "no proof certificate emitted" warning), while `None` keeps
/// the export unbudgeted and byte-identical to the unbudgeted API.
#[test]
fn test_emission_work_budget_exhaustion_and_unbudgeted_parity() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(x, None);
    let h2 = proof.add_assume(not_x, None);
    proof.add_rule_step(AletheRule::Resolution, vec![], vec![h1, h2], vec![x]);

    // Budget of 0 units: the very first rendered step exceeds it.
    let err = try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        &terms,
        &[x, not_x],
        None,
        Some(0),
    )
    .expect_err("zero budget must exhaust");
    assert!(
        matches!(
            err,
            AlethePrintError::EmissionBudgetExhausted { budget: 0, .. }
        ),
        "expected EmissionBudgetExhausted: {err}"
    );

    // Unbudgeted (None) and generously budgeted exports are byte-identical
    // to the pre-existing unbudgeted API.
    let unbudgeted =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[x, not_x], None)
            .expect("unbudgeted export");
    let generous = try_export_alethe_with_problem_scope_overrides_and_budget(
        &proof,
        &terms,
        &[x, not_x],
        None,
        Some(1_000_000),
    )
    .expect("generous budget export");
    assert_eq!(unbudgeted, generous);
    assert!(unbudgeted.contains("(assume t0 x)"));
}

// ---------------------------------------------------------------------------
// #A9 — ad-hoc overloading must make the emitter DECLINE, never abort.
//
// SMT-LIB 2.6 §4.2.3 lets independent datatypes reuse a constructor name and
// §3.6.4 `(as f σ)` disambiguates the overload, so
// `(declare-datatypes ((A 0) (B 0)) (((e) (f)) ((e) (g))))` is well-formed
// input that AY solves. The proof-variable collector used to enforce
// one-sort-per-SURFACE-NAME with a `debug_assert_eq!`, aborting the process
// (exit 101) AFTER the correct verdict had been printed. Alethe preambles are
// a flat, non-overloaded `(declare-fun <name> () <sort>)` namespace, so the
// right behaviour is a typed refusal that leaves the verdict intact.
// ---------------------------------------------------------------------------

/// Two same-named symbols at different sorts, as ad-hoc overloading produces.
fn overloaded_symbol_proof() -> (Proof, TermStore, Vec<TermId>) {
    let mut terms = TermStore::new();
    let sort_a = Sort::Uninterpreted("A".to_string());
    let sort_b = Sort::Uninterpreted("B".to_string());
    // `(as e A)` / `(as e B)`: one surface name, two sorts.
    let e_a = terms.mk_fresh_named_var("e", sort_a.clone());
    let f_a = terms.mk_fresh_named_var("f", sort_a);
    let e_b = terms.mk_fresh_named_var("e", sort_b.clone());
    let g_b = terms.mk_fresh_named_var("g", sort_b);
    let eq_a = terms.mk_eq(e_a, f_a);
    let eq_b = terms.mk_eq(e_b, g_b);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(eq_a, None);
    let h2 = proof.add_assume(eq_b, None);
    proof.add_rule_step(AletheRule::Resolution, vec![], vec![h1, h2], vec![eq_a]);
    (proof, terms, vec![eq_a, eq_b])
}

#[test]
fn overloaded_symbol_declines_instead_of_panicking_plain_export() {
    let (proof, terms, _) = overloaded_symbol_proof();

    let err = try_export_alethe(&proof, &terms)
        .expect_err("a symbol at two sorts has no faithful Alethe preamble");
    match err {
        AlethePrintError::AmbiguousSymbolSort {
            ref name,
            ref first,
            ref second,
        } => {
            assert_eq!(name, "e");
            assert_ne!(first, second, "the reported sorts must differ");
        }
        other => panic!("expected AmbiguousSymbolSort, got {other:?}"),
    }

    // The infallible wrapper must degrade loudly, not abort the process.
    let rendered = export_alethe(&proof, &terms);
    assert!(
        rendered.contains("UNVERIFIABLE PROOF"),
        "infallible export must emit the loud degrade marker: {rendered}"
    );
}

#[test]
fn overloaded_symbol_declines_instead_of_panicking_problem_scope_export() {
    // This is the exact path that aborted with exit 101: the auxiliary
    // declaration collector walks BOTH the proof roots and the problem
    // assertions through `collect_free_vars_in_term`.
    let (proof, terms, assertions) = overloaded_symbol_proof();

    let err = try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &assertions, None)
        .expect_err("problem-scope export must decline on an overloaded symbol");
    assert!(
        matches!(err, AlethePrintError::AmbiguousSymbolSort { .. }),
        "expected AmbiguousSymbolSort, got {err:?}"
    );

    let rendered = export_alethe_with_problem_scope(&proof, &terms, &assertions);
    assert!(
        rendered.contains("UNVERIFIABLE PROOF"),
        "infallible problem-scope export must degrade loudly: {rendered}"
    );
}

#[test]
fn distinct_symbols_at_distinct_sorts_still_export() {
    // The refusal must key on a NAME CLASH, not on the mere presence of
    // several sorts: differently-named symbols at different sorts, and the
    // same symbol repeated at the SAME sort, both remain exportable.
    let mut terms = TermStore::new();
    let sort_a = Sort::Uninterpreted("A".to_string());
    let sort_b = Sort::Uninterpreted("B".to_string());
    let p = terms.mk_fresh_named_var("p", sort_a.clone());
    let q = terms.mk_fresh_named_var("q", sort_a);
    let r = terms.mk_fresh_named_var("r", sort_b.clone());
    let s = terms.mk_fresh_named_var("s", sort_b);
    let eq_a = terms.mk_eq(p, q);
    let eq_b = terms.mk_eq(r, s);
    // Same name, SAME sort — legal and unambiguous.
    let p_again = terms.mk_fresh_named_var("p", Sort::Uninterpreted("A".to_string()));
    let eq_again = terms.mk_eq(p_again, q);

    let mut proof = Proof::new();
    let h1 = proof.add_assume(eq_a, None);
    let h2 = proof.add_assume(eq_b, None);
    let h3 = proof.add_assume(eq_again, None);
    proof.add_rule_step(AletheRule::Resolution, vec![], vec![h1, h2, h3], vec![eq_a]);

    let output = try_export_alethe(&proof, &terms).expect("no name clash — must export");
    assert!(output.contains("(declare-fun p () A)"), "{output}");
    assert!(output.contains("(declare-fun r () B)"), "{output}");
}
