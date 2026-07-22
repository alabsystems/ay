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
    let sk = terms.mk_var("__ext_diff_1_2", Sort::Int);

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
        output.contains("(declare-fun __ext_diff_1_2 () Int)"),
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
