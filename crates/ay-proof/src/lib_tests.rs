// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use ay_core::{string_literal, AletheRule, Sort};

#[path = "alethe_printer_bare_step_rule_tests.rs"]
mod alethe_printer_bare_step_rule_tests;
#[path = "alethe_printer_resolution_args_tests.rs"]
mod alethe_printer_resolution_args_tests;
#[path = "alethe_printer_surface_and_pos_tests.rs"]
mod alethe_printer_surface_and_pos_tests;
#[path = "alethe_printer_surface_symm_tests.rs"]
mod alethe_printer_surface_symm_tests;

/// A problem scope covering every term the proof mentions.
///
/// The tests that use this are STEP-RENDERING tests: they assert on `(step
/// ...)` text and say nothing about the declaration preamble. They used to
/// pass `&[]` as `problem_assertions`, which put every symbol *outside*
/// problem scope — and the exporter then opened the document with a
/// `(declare-fun ...)` preamble that carcara rejects at line 0 (S2), so the
/// text they asserted on could never have been checked by anything.
///
/// The exporter now DECLINES instead of emitting that preamble, so these
/// tests must supply a scope that actually covers their symbols. The step
/// rendering under test is unaffected.
///
/// Do NOT use this in a test whose subject is the assume-authority boundary
/// (`validate_reachable_assumes_in_problem_scope`): folding every assume into
/// the scope makes that check vacuous.
fn scope_covering_proof(proof: &Proof) -> Vec<TermId> {
    let mut scope = Vec::new();
    for step in &proof.steps {
        match step {
            ProofStep::Assume(term) => scope.push(*term),
            ProofStep::Resolution { clause, pivot, .. } => {
                scope.extend(clause.iter().copied());
                scope.push(*pivot);
            }
            ProofStep::TheoryLemma { clause, .. } => scope.extend(clause.iter().copied()),
            ProofStep::Step { clause, args, .. } => {
                scope.extend(clause.iter().copied());
                scope.extend(args.iter().copied());
            }
            _ => {}
        }
    }
    scope
}

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
    let yes = terms.mk_bool(true);
    proof.add_rule_step(
        AletheRule::Resolution,
        vec![], // empty clause = contradiction
        vec![h1, h2],
        vec![x, yes], // pivot and polarity
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
    // Generic lemmas are internally the "trust" kind, but `trust` is not an
    // Alethe rule — emitting it made carcara reject the whole document as
    // `invalid`. On the wire they are the spec's `hole`, which checks as
    // *holey*; `TheoryLemmaKind::Generic.is_trust()` is unchanged, so the
    // #8759 detector still sees the step.
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule trust"), "{output}");
    assert!(output.contains("(= a b)"));
}

#[test]
fn datatype_enum_pigeonhole_keeps_native_identity_but_prints_hole() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let sort = Sort::Uninterpreted("FiniteEnum".to_string());
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort);
    let equality = terms.mk_eq(a, b);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "DT",
        vec![equality],
        TheoryLemmaKind::DatatypeEnumPigeonhole,
    );

    let output = export_alethe(&proof, &terms);
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule dt_enum_pigeonhole"), "{output}");
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
fn bv_bitblast_bvand_commutativity_exports_exact_aci_simp() {
    use ay_core::{Symbol, TheoryLemmaKind};

    for width in [32, 64] {
        let mut terms = TermStore::new();
        let sort = Sort::bitvec(width);
        let a = terms.mk_var("a", sort.clone());
        let b = terms.mk_var("b", sort.clone());
        let and_ab = terms.mk_app(Symbol::named("bvand"), [a, b], sort.clone());
        let and_ba = terms.mk_app(Symbol::named("bvand"), [b, a], sort);
        let equality = terms.mk_app(Symbol::named("="), [and_ab, and_ba], Sort::Bool);
        assert!(
            recognize_bv_bitblast(&terms, &[equality]),
            "{width}-bit bvand commutativity must have a checked LRAT refutation"
        );

        let mut proof = Proof::new();
        proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
        let output = export_alethe(&proof, &terms);
        assert!(output.contains(":rule aci_simp"), "{output}");
        assert!(!output.contains(":rule hole"), "{output}");
    }
}

#[test]
fn bv_bitblast_aci_simp_export_fails_closed_on_near_misses_and_surface_drift() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let bv32 = Sort::bitvec(32);
    let a = terms.mk_var("a", bv32.clone());
    let b = terms.mk_var("b", bv32.clone());
    let c = terms.mk_var("c", bv32.clone());
    let and_ab = terms.mk_app(Symbol::named("bvand"), [a, b], bv32.clone());
    let and_ba = terms.mk_app(Symbol::named("bvand"), [b, a], bv32.clone());

    let cases = [
        // Swapping a non-commutative operator cannot be printed as ACI.
        (
            terms.mk_app(Symbol::named("bvsub"), [a, b], bv32.clone()),
            terms.mk_app(Symbol::named("bvsub"), [b, a], bv32.clone()),
        ),
        // A near-swap with one unrelated operand is also outside the lane.
        (
            and_ab,
            terms.mk_app(Symbol::named("bvand"), [b, c], bv32.clone()),
        ),
    ];
    for (left, right) in cases {
        let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
        let mut proof = Proof::new();
        proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
        let output = export_alethe(&proof, &terms);
        assert!(output.contains(":rule hole"), "{output}");
        assert!(!output.contains(":rule aci_simp"), "{output}");
    }

    // The lowering is also gated on the exact bytes the external checker sees.
    // A surface override that breaks the swap must retain the honest hole.
    let equality = terms.mk_app(Symbol::named("="), [and_ab, and_ba], Sort::Bool);
    let step = ProofStep::TheoryLemma {
        theory: "bv".to_string(),
        clause: vec![equality],
        farkas: None,
        kind: TheoryLemmaKind::BvBitBlast,
        lia: None,
    };
    let mut overrides = DetHashMap::default();
    overrides.insert(and_ab, "(bvand a c)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
    let output = printer.format_step(&step, ProofId(0)).unwrap();
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule aci_simp"), "{output}");
}

/// The endpoint lane (`executor/proof/authored_linear.rs`) closes two
/// authored equalities that pin one opaque term to two different bit-vector
/// CONSTANTS with the unit lemma `(cl (not (= c d)))`. Carcara has no rule for
/// AY's monolithic bit-blasting, but `(= c d)` is a GROUND term its own
/// `evaluate` reduces to `false`, so the lemma exports as a checked
/// `evaluate` + `equiv_pos2` + `false` derivation instead of a hole.
#[test]
fn bv_bitblast_constant_disequality_exports_checked_evaluate() {
    use ay_core::{Symbol, TheoryLemmaKind};
    use num_bigint::BigInt;

    for width in [1_u32, 8, 32] {
        let mut terms = TermStore::new();
        // Width 1 has to work too, so the two values are 1 and 0.
        let one = terms.mk_bitvec(BigInt::from(1), width);
        let zero = terms.mk_bitvec(BigInt::from(0), width);
        let equality = terms.mk_app(Symbol::named("="), [one, zero], Sort::Bool);
        let disequality = terms.mk_not_raw(equality);
        assert!(
            recognize_bv_bitblast(&terms, &[disequality]),
            "{width}-bit constant mismatch must be re-derived by AY's own checker"
        );

        let mut proof = Proof::new();
        proof.add_theory_lemma_with_kind("bv", vec![disequality], TheoryLemmaKind::BvBitBlast);
        let output = export_alethe(&proof, &terms);
        assert!(output.contains(":rule evaluate"), "{output}");
        assert!(output.contains(":rule equiv_pos2"), "{output}");
        assert!(output.contains(":rule false"), "{output}");
        assert!(!output.contains(":rule hole"), "{output}");
        assert!(!output.contains(":rule bv_bitblast"), "{output}");
    }
}

/// `promote_bv_identity_collapse` reconstructs an authored bit-vector identity
/// as a `BvBitBlast` unit lemma. For the bit-wise idempotency shapes that
/// lemma is EXACTLY reconstructible from Carcara's per-operator bit-blasting
/// suite, so it exports as `bitblast_and`/`bitblast_or` + `bitblast_var` +
/// per-bit `and_simplify`/`or_simplify` + `cong`/`trans`/`symm`.
#[test]
fn bv_bitblast_idempotent_gate_exports_per_operator_bitblast() {
    use ay_core::{Symbol, TheoryLemmaKind};

    for (operator, simplify) in [("bvand", "and_simplify"), ("bvor", "or_simplify")] {
        for width in [1_u32, 4, 8] {
            for reversed in [false, true] {
                let mut terms = TermStore::new();
                let sort = Sort::bitvec(width);
                let a = terms.mk_var("a", sort.clone());
                let gate = terms.mk_app(Symbol::named(operator), [a, a], sort);
                let (left, right) = if reversed { (a, gate) } else { (gate, a) };
                let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
                assert!(
                    recognize_bv_bitblast(&terms, &[equality]),
                    "{width}-bit {operator} idempotency must be re-derived by AY's own checker"
                );

                let mut proof = Proof::new();
                proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
                let output = export_alethe(&proof, &terms);
                let blast_rule = format!(":rule bitblast_{}", &operator[2..]);
                assert!(output.contains(&blast_rule), "{output}");
                assert!(output.contains(":rule bitblast_var"), "{output}");
                assert!(output.contains(&format!(":rule {simplify}")), "{output}");
                assert!(output.contains(":rule cong"), "{output}");
                assert!(!output.contains(":rule hole"), "{output}");
                // Exactly one per-bit discharge per bit, and no extra steps:
                // a lowering that quietly skipped a bit would still contain
                // every rule name asserted above.
                assert_eq!(
                    output.matches(":rule ").count(),
                    // bb + var + one simplify per bit + cong + lhs + rhs (+ symm)
                    6 + width as usize + usize::from(reversed),
                    "{output}"
                );
            }
        }
    }
}

/// The NESTED per-operator case: `(bvnot (bvnot t)) = t` needs `bitblast_not`
/// twice with a `cong` bridge, because a `bitblast_*` rule relates exactly ONE
/// word-level operator to a `@bbterm`.
#[test]
fn bv_bitblast_double_negation_exports_nested_per_operator_bitblast() {
    use ay_core::{Symbol, TheoryLemmaKind};

    for width in [1_u32, 2, 8] {
        for reversed in [false, true] {
            let mut terms = TermStore::new();
            let sort = Sort::bitvec(width);
            let a = terms.mk_var("a", sort.clone());
            let once = terms.mk_app(Symbol::named("bvnot"), [a], sort.clone());
            let twice = terms.mk_app(Symbol::named("bvnot"), [once], sort);
            let (left, right) = if reversed { (a, twice) } else { (twice, a) };
            let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
            assert!(
                recognize_bv_bitblast(&terms, &[equality]),
                "{width}-bit double negation must be re-derived by AY's own checker"
            );

            let mut proof = Proof::new();
            proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
            let output = export_alethe(&proof, &terms);
            assert_eq!(output.matches(":rule bitblast_not").count(), 2, "{output}");
            assert!(output.contains(":rule bitblast_var"), "{output}");
            assert!(output.contains(":rule not_simplify"), "{output}");
            assert!(!output.contains(":rule hole"), "{output}");
            assert_eq!(
                output.matches(":rule ").count(),
                // in + lift + out + one not_simplify per bit + cong + var + rhs
                // + trans (+ symm)
                7 + width as usize + usize::from(reversed),
                "{output}"
            );
        }
    }
}

/// Both bit-vector lowerings must decline — keeping the honest `hole` — on
/// every clause AY may carry under the same coarse kind that is NOT an
/// instance of the Carcara rules they emit.
#[test]
fn bv_bitblast_carcara_lowerings_fail_closed_on_near_misses_and_surface_drift() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{Symbol, TheoryLemmaKind};
    use num_bigint::BigInt;

    let mut terms = TermStore::new();
    let bv8 = Sort::bitvec(8);
    let a = terms.mk_var("a", bv8.clone());
    let b = terms.mk_var("b", bv8.clone());
    let one = terms.mk_bitvec(BigInt::from(1), 8);
    let five = terms.mk_bitvec(BigInt::from(5), 8);
    let and_aa = terms.mk_app(Symbol::named("bvand"), [a, a], bv8.clone());
    let or_aa = terms.mk_app(Symbol::named("bvor"), [a, a], bv8.clone());
    let and_ab = terms.mk_app(Symbol::named("bvand"), [a, b], bv8.clone());
    let xor_aa = terms.mk_app(Symbol::named("bvxor"), [a, a], bv8.clone());
    let not_a = terms.mk_app(Symbol::named("bvnot"), [a], bv8.clone());
    let not_not_a = terms.mk_app(Symbol::named("bvnot"), [not_a], bv8.clone());
    let neg_a = terms.mk_app(Symbol::named("bvneg"), [a], bv8.clone());
    let not_neg_a = terms.mk_app(Symbol::named("bvnot"), [neg_a], bv8.clone());
    let zero = terms.mk_bitvec(BigInt::from(0), 8);
    let add_a_one = terms.mk_app(Symbol::named("bvadd"), [a, one], bv8.clone());
    // A width the per-bit expansion refuses to unroll.
    let bv65 = Sort::bitvec(65);
    let wide = terms.mk_var("wide", bv65.clone());
    let and_wide = terms.mk_app(Symbol::named("bvand"), [wide, wide], bv65);

    let equal_constants = terms.mk_app(Symbol::named("="), [five, five], Sort::Bool);
    let non_constant = terms.mk_app(Symbol::named("="), [add_a_one, five], Sort::Bool);
    let near_misses = [
        // Two EQUAL constants: `evaluate` would reduce the equality to `true`.
        terms.mk_not_raw(equal_constants),
        // One side is not a constant: outside the ground-evaluation lane.
        terms.mk_not_raw(non_constant),
        // Distinct operands: not an idempotency.
        terms.mk_app(Symbol::named("="), [and_ab, a], Sort::Bool),
        // Right side is not the repeated operand.
        terms.mk_app(Symbol::named("="), [or_aa, b], Sort::Bool),
        // `bvxor` self-cancellation needs `(xor p p) = false`, which no
        // Carcara rule proves in one step.
        terms.mk_app(Symbol::named("="), [xor_aa, zero], Sort::Bool),
        // Over the per-bit unrolling cap.
        terms.mk_app(Symbol::named("="), [and_wide, wide], Sort::Bool),
        // A SINGLE `bvnot` is not a double negation.
        terms.mk_app(Symbol::named("="), [not_a, a], Sort::Bool),
        // A mixed nest: the inner operator is not the one being cancelled.
        terms.mk_app(Symbol::named("="), [not_neg_a, a], Sort::Bool),
        // A double negation of the WRONG operand.
        terms.mk_app(Symbol::named("="), [not_not_a, b], Sort::Bool),
    ];
    for literal in near_misses {
        let mut proof = Proof::new();
        proof.add_theory_lemma_with_kind("bv", vec![literal], TheoryLemmaKind::BvBitBlast);
        let output = export_alethe(&proof, &terms);
        assert!(output.contains(":rule hole"), "{output}");
        assert!(!output.contains(":rule evaluate"), "{output}");
        assert!(!output.contains(":rule bitblast_"), "{output}");
    }

    // A two-literal clause is not a unit lemma in either lane.
    let idempotency = terms.mk_app(Symbol::named("="), [and_aa, a], Sort::Bool);
    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "bv",
        vec![idempotency, non_constant],
        TheoryLemmaKind::BvBitBlast,
    );
    let output = export_alethe(&proof, &terms);
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule bitblast_"), "{output}");

    // Both lowerings read the BYTES the external checker parses. A surface
    // override that breaks the printed operand identity, or that re-spells a
    // constant as something that is not a bit-vector literal, must decline.
    let five_ne_one = terms.mk_app(Symbol::named("="), [five, one], Sort::Bool);
    let constant_disequality = terms.mk_not_raw(five_ne_one);
    let drift: [(TermId, TermId, &str); 2] = [
        (idempotency, and_aa, "(bvand a b)"),
        (constant_disequality, five, "a"),
    ];
    for (literal, overridden, spelling) in drift {
        let step = ProofStep::TheoryLemma {
            theory: "bv".to_string(),
            clause: vec![literal],
            farkas: None,
            kind: TheoryLemmaKind::BvBitBlast,
            lia: None,
        };
        let mut overrides = DetHashMap::default();
        overrides.insert(overridden, spelling.to_string());
        let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));
        let output = printer.format_step(&step, ProofId(0)).unwrap();
        assert!(output.contains(":rule hole"), "{output}");
        assert!(!output.contains(":rule evaluate"), "{output}");
        assert!(!output.contains(":rule bitblast_"), "{output}");
    }
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

/// S2: a proof free in symbols the problem does not declare is UNRENDERABLE.
///
/// This test previously asserted the opposite — that the exporter opens the
/// document with `(declare-fun _mod_q_2 () Int)` and friends. MEASURED against
/// carcara 1.1.0: an Alethe PROOF document admits no declaration command at
/// any position, so every such document died at
/// `parser error: unexpected token: 'declare-fun' (on line 0, column 1)`
/// before a single rule was checked. The preamble was not a partial fix; it
/// was what made the artifact uncheckable.
#[test]
fn test_export_alethe_with_problem_scope_declines_on_undeclarable_symbols() {
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

    let error =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[user_eq], None)
            .expect_err("symbols outside problem scope have no Alethe declaration form");
    let AlethePrintError::UndeclarableProofSymbols { count, ref names } = error else {
        panic!("expected UndeclarableProofSymbols, got {error}");
    };
    // Exactly the three out-of-scope symbols. `a` and `b` are declared by the
    // problem file, so they are not what blocked the export and the count
    // pins that they were not counted.
    assert_eq!(count, 3, "{error}");
    for aux in ["_mod_q_2", "_mod_r_3", "__ay_ext_diff_1_2"] {
        assert!(names.contains(aux), "{error}");
    }

    // The infallible wrapper must not paper over it with a document either:
    // whatever it returns, it must carry no declaration command and no step.
    let rendered = export_alethe_with_problem_scope(&proof, &terms, &[user_eq]);
    assert!(rendered.contains("UNVERIFIABLE PROOF"), "{rendered}");
    assert!(!rendered.contains("(declare-"), "{rendered}");
    assert!(!rendered.contains("(step "), "{rendered}");
}

/// The fail-closed decline must survive the STREAMING export too: the CLI
/// writes `<input>.alethe` through the budgeted `..._to` sink, and a partial
/// prefix followed by an error is exactly the artifact this class is about.
#[test]
fn test_streaming_export_declines_before_writing_any_bytes() {
    let mut terms = TermStore::new();
    let user_a = terms.mk_var("a", Sort::Int);
    let aux = terms.mk_var("__ay_ext_diff!69", Sort::Int);
    let user_eq = terms.mk_eq(user_a, user_a);
    let aux_eq = terms.mk_eq(aux, user_a);

    let mut proof = Proof::new();
    proof.add_theory_lemma("EUF", vec![aux_eq]);

    let mut sink: Vec<u8> = Vec::new();
    let err = try_export_alethe_with_problem_scope_overrides_and_budget_to(
        &mut sink,
        &proof,
        &terms,
        &[user_eq],
        None,
        None,
    )
    .expect_err("an undeclarable witness must decline");
    assert!(
        matches!(
            err,
            AletheStreamError::Print(AlethePrintError::UndeclarableProofSymbols { .. })
        ),
        "{err}"
    );
    assert!(
        sink.is_empty(),
        "declined export wrote {} bytes: {}",
        sink.len(),
        String::from_utf8_lossy(&sink)
    );
}

/// The positive direction of S2: a document the exporter DOES produce must
/// carry no declaration command anywhere.
///
/// The decline above only covers symbols the collector reports. This pins the
/// stronger, checker-facing invariant on the success path — carcara rejects
/// `(declare-fun` / `(declare-const` / `(declare-sort` / `(set-logic` at ANY
/// position, so one such line makes an otherwise-checkable document
/// uncheckable.
#[test]
fn test_successful_problem_scope_export_emits_no_declaration_command() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Bool);
    let not_x = terms.mk_not(x);

    let mut proof = Proof::new();
    let a0 = proof.add_assume(x, None);
    let a1 = proof.add_assume(not_x, None);
    proof.add_resolution(Vec::new(), x, a0, a1);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[x, not_x], None)
            .expect("all symbols are in problem scope");
    assert!(output.contains("(assume t0 x)"), "{output}");
    for forbidden in ["(declare-", "(set-", "(define-sort", "(check-sat"] {
        assert!(
            !output.contains(forbidden),
            "emitted document contains `{forbidden}`, which no Alethe proof parser accepts:\n{output}"
        );
    }
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

/// Every proof-free symbol outside the problem scope must be REPORTED,
/// whatever it is named — the collector must not silently drop families.
///
/// The collector used to see only names matching six hard-coded prefixes
/// (`_mod_`, `_div_`, `__ay_`, `_sk_`, `sk_`, `skolem`). Internal symbols in
/// any other family fell through, and the resulting document did not parse.
/// Reproduced on QF_DT/20230720-blocksworld, where the eager datatype engine's
/// field-split symbols reach the proof and carcara reports
/// `identifier 's_tmp___!left' is not defined` before checking any rule.
///
/// The obligation is unchanged; only its discharge moved. Declaring the symbol
/// was never a discharge (S2: carcara rejects the declaration itself), so the
/// exporter now names it in a fail-closed decline.
#[test]
fn test_problem_scope_reports_internal_symbols_outside_the_prefix_allowlist() {
    let mut terms = TermStore::new();
    let user = terms.mk_var("s_", Sort::Int);
    let other = terms.mk_var("t_", Sort::Int);
    // A field-split symbol as the frontend mints them for a datatype-sorted
    // constant (`declarations.rs`, `format!("{name}!{sel_name}")`): no
    // recognizable prefix, and absent from the problem scope.
    let field = terms.mk_var("s_tmp___!left", Sort::Int);
    // NOTE: must be `(= s_ t_)`, not `(= s_ s_)` — the term store folds a
    // reflexive equality to `true`, which would leave the problem scope EMPTY
    // and make the second assertion below vacuous.
    let user_goal = terms.mk_eq(user, other);
    let split_eq = terms.mk_eq(field, user);

    let mut proof = Proof::new();
    proof.add_assume(split_eq, None);

    let error =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[user_goal], None)
            .expect_err("an out-of-scope field-split symbol is unrenderable");
    let AlethePrintError::UndeclarableProofSymbols { count, ref names } = error else {
        panic!("expected UndeclarableProofSymbols, got {error}");
    };
    assert_eq!(
        count, 1,
        "the collector must SEE the prefix-less symbol, not drop it: {error}"
    );
    assert!(names.contains("s_tmp___!left"), "{error}");
    // A problem-scope symbol is declared by the problem file and must never be
    // the reason an export declines.
    assert!(!names.contains("t_"), "{error}");
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
fn test_export_alethe_lowers_array_extensionality_to_arrays_ext() {
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

    let output = try_export_alethe(&proof, &terms).expect("one-level extensionality is lowerable");
    // The AY-private rule name must never reach an external checker.
    assert!(
        !output.contains(":rule extensionality"),
        "unsupported external rule must never be emitted: {output}"
    );
    assert!(
        output.contains(":rule arrays_ext"),
        "extensionality must lower to Carcara's checked rule: {output}"
    );
    // The witness is rendered as Carcara's own epsilon term at EVERY
    // occurrence, so it is neither declared nor mentioned as a constant.
    let choice = "(choice ((x Int)) (or (= a b) (not (= (select a x) (select b x)))))";
    assert!(output.contains(choice), "missing epsilon witness: {output}");
    assert!(
        !output.contains("__ext_diff_1_2"),
        "witness constant survived the substitution: {output}"
    );
    assert!(
        !output.contains("(declare-fun __ext_diff_1_2"),
        "substituted witness must not be declared: {output}"
    );
    assert!(
        output.contains(&format!(
            "(step t0 (cl (or (= a b) (not (= (select a {choice}) (select b {choice}))))) \
             :rule resolution :premises (t0.r0 t0.o1))"
        )) || output.contains("(step t0 (cl (or (= a b)"),
        "final clause must keep AY's packed-or shape: {output}"
    );
}

#[test]
fn test_try_export_alethe_fails_closed_on_unrecognized_array_extensionality() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let a = terms.mk_var("a", array_sort.clone());
    let b = terms.mk_var("b", array_sort);
    let k = terms.mk_var("__ext_diff_1_2", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    // Two DIFFERENT read indices: not an extensionality clause at all, so no
    // `arrays_ext` instance justifies it and the export must refuse.
    let eq_ab = terms.mk_eq(a, b);
    let sel_a = terms.mk_select(a, k);
    let sel_b = terms.mk_select(b, j);
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
        !output.contains(":rule extensionality") && !output.contains(":rule arrays_ext"),
        "unjustified extensionality must never be emitted: {output}"
    );
    assert!(
        output.contains("UNVERIFIABLE PROOF") && output.contains("(error"),
        "infallible export must fail loudly: {output}"
    );
}

#[test]
fn test_array_extensionality_refuses_capture_prone_witness() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let array_sort = Sort::array(Sort::Int, Sort::Int);
    // A problem constant literally named `x` would be CAPTURED by the binder
    // Carcara hard-codes in its epsilon term, so the lemma must fail closed.
    let x = terms.mk_var("x", Sort::Int);
    let base = terms.mk_var("base", array_sort.clone());
    let value = terms.mk_var("v", Sort::Int);
    let a = terms.mk_store(base, x, value);
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

    let output = export_alethe_with_problem_scope(&proof, &terms, &scope_covering_proof(&proof));
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
        .expect("Generic kind is a first-class unproved step, not a silent downgrade");
    // Still a first-class, detector-visible unproved step — but written with
    // the rule name the checker actually implements.
    assert!(
        output.contains(":rule hole"),
        "Generic kind should still emit an honest hole: {output}"
    );
    assert!(
        !output.contains(":rule trust"),
        "must not emit a rule name no Alethe checker implements: {output}"
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

/// An internal `or` decomposition over a premise that prints as an authored
/// right-associated implication cannot remain `:rule or`: the external rule
/// sees an implication, not AY's flattened canonical or-term. Rebuild the
/// exact flat clause with one premiseless `implies_pos` per binary link and a
/// single n-ary resolution whose command retains the traced step id.
#[test]
fn test_or_decomposition_with_nested_implies_override_resugars_to_resolution_chain() {
    use ay_core::kani_compat::DetHashMap;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let inner = terms.mk_implies(b, c);
    let source = terms.mk_implies(a, inner);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(source, "(=> a (=> b c))".to_string());

    let mut proof = Proof::new();
    let premise = proof.add_assume(source, None);
    // Deliberately use a different order from the authored implication. The
    // bridge's multiset gate permits only reordering, and its final resolution
    // must reproduce this exact traced clause under t1.
    proof.add_rule_step(AletheRule::Or, vec![c, not_b, not_a], vec![premise], vec![]);

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[source],
        Some(&overrides),
    )
    .expect("the implication decomposition must render through stock Alethe rules");
    assert!(output.contains("(assume t0 (=> a (=> b c)))"), "{output}");
    assert!(
        output.contains(
            "(step t1.imp0 (cl (not (=> a (=> b c))) (not a) (=> b c)) :rule implies_pos)\n\
             (step t1.imp1 (cl (not (=> b c)) (not b) c) :rule implies_pos)\n\
             (step t1 (cl c (not b) (not a)) :rule resolution :premises (t0 t1.imp0 t1.imp1))"
        ),
        "{output}"
    );
    assert_eq!(output.matches(":rule implies_pos").count(), 2, "{output}");
    assert!(!output.contains("(step t1 (cl c (not b) (not a)) :rule or"));
}

/// The bridge is not a general implication/or equivalence rewrite. A traced
/// clause that differs from the assumed canonical or-term must miss the
/// internal TermId multiset gate and fail loudly instead of shipping an `or`
/// rule over a printed implication premise.
#[test]
fn test_implies_decomposition_declines_a_different_internal_clause() {
    use ay_core::kani_compat::DetHashMap;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let not_b = terms.mk_not(b);
    let inner = terms.mk_implies(b, c);
    let source = terms.mk_implies(a, inner);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(source, "(=> a (=> b c))".to_string());

    let mut proof = Proof::new();
    let premise = proof.add_assume(source, None);
    proof.add_rule_step(AletheRule::Or, vec![c, not_b, d], vec![premise], vec![]);
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[source, d],
        Some(&overrides),
    )
    .expect_err("a mismatched implication decomposition must fail loudly");
    assert!(
        matches!(
            error,
            AlethePrintError::InvalidSurfaceStep { id: ProofId(1), .. }
        ),
        "{error}"
    );
}

/// Same-arity forged surface literals and a shorter binary implication both
/// fail the printed-literal/arity gates. Neither may be force-fitted to the
/// valid internal decomposition merely because the root prints with `=>`.
#[test]
fn test_implies_decomposition_declines_printed_literal_or_arity_mismatch() {
    use ay_core::kani_compat::DetHashMap;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let d = terms.mk_var("d", Sort::Bool);
    let not_a = terms.mk_not(a);
    let not_b = terms.mk_not(b);
    let inner = terms.mk_implies(b, c);
    let source = terms.mk_implies(a, inner);

    for surface in ["(=> a (=> d c))", "(=> a c)", "(=> a (=> b c d))"] {
        let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
        overrides.insert(source, surface.to_string());

        let mut proof = Proof::new();
        let premise = proof.add_assume(source, None);
        proof.add_rule_step(AletheRule::Or, vec![c, not_b, not_a], vec![premise], vec![]);
        let error = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &[source, d],
            Some(&overrides),
        )
        .expect_err("a malformed implication decomposition must fail loudly");
        assert!(
            matches!(
                error,
                AlethePrintError::InvalidSurfaceStep { id: ProofId(1), .. }
            ),
            "surface {surface} produced the wrong error: {error}"
        );
    }
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
        &scope_covering_proof(&proof),
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
        &scope_covering_proof(&proof),
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

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
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
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect_err("a non-unit distinct/equality surface pivot must not fall through");
    assert!(
        matches!(error, AlethePrintError::InvalidSurfaceStep { .. }),
        "{error}"
    );

    let mut generic_proof = Proof::new();
    let distinct_clause = generic_proof.add_theory_lemma("test", vec![disequality, p]);
    let equality_clause = generic_proof.add_theory_lemma("test", vec![equality, q]);
    let yes = terms.mk_bool(true);
    generic_proof.add_rule_step(
        AletheRule::ThResolution,
        vec![p, q],
        vec![distinct_clause, equality_clause],
        vec![equality, yes],
    );
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &generic_proof,
        &terms,
        &scope_covering_proof(&generic_proof),
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
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
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
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
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
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
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
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
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
        let error = try_export_alethe_with_problem_scope_and_overrides(
            &proof,
            &terms,
            &scope_covering_proof(&proof),
            None,
        )
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
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
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
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
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
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
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
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect("fallback emission still produces a document");
    // The point of the fallback is that it must NOT claim a real array rule it
    // cannot justify. `read_over_write_chain` is AY's kind name and not an
    // Alethe rule either, so the wire form is the honest `hole`.
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule read_over_write_chain"), "{output}");
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
    proof.add_rule_step(AletheRule::Resolution, vec![], vec![h1, h2], Vec::new());

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
    proof.add_rule_step(AletheRule::Resolution, vec![], vec![h1, h2], Vec::new());
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
    proof.add_rule_step(AletheRule::Resolution, vec![], vec![h1, h2, h3], Vec::new());

    let output = try_export_alethe(&proof, &terms).expect("no name clash — must export");
    assert!(output.contains("(declare-fun p () A)"), "{output}");
    assert!(output.contains("(declare-fun r () B)"), "{output}");
}

// ---------------------------------------------------------------------------
// Printed-shape gate repairs (D1 / D1b)
//
// A census over 167 non-datatype `:status unsat` instances found 36 INVALID
// Alethe proofs; the largest class — 23 instances across QF_UFLIA (10),
// QF_ALIA (4), QF_IDL (4), QF_LIA (2), QF_UFIDL (2) and ALIA (1) — is an
// `and_pos` step whose `(not (and ...))` gate literal ships as its De Morgan
// surface form, because two blockers defeat the printed-shape guard:
//
//   (A) the printed root is `(let ...)`, so `split_application(s, "and")`
//       fails at its `strip_prefix("and")`;
//   (B) the printed root is a left-nested BINARY `and` while `mk_and` flattens
//       internally, so the printed arity (2) never equals the internal
//       conjunct count (58).
//
// ... and its mirror image D1b, an `or_pos` whose printed gate is a nested
// binary `or` ("expected 6 terms in 'or' term, got 2") — a shape that had NO
// guard at all and shipped broken silently.
// ---------------------------------------------------------------------------

/// (A) A `let`-rooted surface override is bridged at the `assume`: the assume
/// keeps the problem's spelling under a DERIVED id and the ORIGINAL id carries
/// the eliminated form, so no downstream premise reference moves. Here the
/// authored spelling survives elimination unchanged, so the equivalence is a
/// genuine `refl`/`let` derivation with no trust hole.
#[test]
fn test_let_rooted_assume_bridges_to_a_certified_and_pos_gate() {
    use ay_core::kani_compat::DetHashMap;

    let mut terms = TermStore::new();
    let p = terms.mk_var("p".to_string(), Sort::Bool);
    let q = terms.mk_var("q".to_string(), Sort::Bool);
    let r = terms.mk_var("r".to_string(), Sort::Bool);
    let and_term = terms.mk_and(vec![p, q, r]);
    // AY's mk_not De Morganizes: this is the gate literal the clausifier stores.
    let demorgan = terms.mk_not(and_term);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(and_term, "(let ((?v_0 q)) (and p ?v_0 r))".to_string());

    let mut proof = Proof::new();
    proof.add_assume(and_term, None);
    proof.add_rule_step(
        AletheRule::AndPos(0),
        vec![demorgan, p],
        vec![],
        vec![and_term],
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[and_term],
        Some(&overrides),
    )
    .expect("let-bridged assume must render");

    // The assume still matches the problem premise verbatim, under `t0.a`.
    assert!(
        output.contains("(assume t0.a (let ((?v_0 q)) (and p ?v_0 r)))"),
        "{output}"
    );
    // Certified arm: anchor + refl + `let` with NO `:premises` (carcara rejects
    // a premise on an already-normal binding: "expected 0 premises, got 1").
    assert!(
        output.contains("(anchor :step t0.l :args ((:= ?v_0 q)))"),
        "{output}"
    );
    assert!(
        output.contains("(step t0.l.t1 (cl (= (and p ?v_0 r) (and p q r))) :rule refl)"),
        "{output}"
    );
    assert!(output.contains(":rule let)"), "{output}");
    assert!(!output.contains(":rule let :premises"), "{output}");
    assert!(!output.contains(":rule hole"), "{output}");
    // The ORIGINAL id concludes the eliminated unit clause.
    assert!(
        output.contains("(step t0 (cl (and p q r)) :rule resolution :premises (t0.e t0.l t0.a))"),
        "{output}"
    );
    // ... and the gate is now the spec-shaped `(not (and ...))`, not the or-form.
    assert!(
        output.contains("(step t1 (cl (not (and p q r)) p) :rule and_pos :args (0))"),
        "{output}"
    );
    assert!(!output.contains("(or (not p)"), "{output}");
}

/// The same bridge when the authored spelling does NOT survive elimination
/// (AY normalizes commutative arguments and arithmetic): the single
/// let-elimination equivalence degrades to a visible, countable `hole` instead
/// of shipping an invalid proof. Everything downstream still gets the spec
/// shape.
#[test]
fn test_let_rooted_assume_falls_back_to_a_single_hole_when_normalization_diverges() {
    use ay_core::kani_compat::DetHashMap;

    let mut terms = TermStore::new();
    let p = terms.mk_var("p".to_string(), Sort::Bool);
    let q = terms.mk_var("q".to_string(), Sort::Bool);
    let r = terms.mk_var("r".to_string(), Sort::Bool);
    let and_term = terms.mk_and(vec![p, q, r]);
    let demorgan = terms.mk_not(and_term);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    // Authored operand order differs from AY's canonical order.
    overrides.insert(and_term, "(let ((?v_0 q)) (and ?v_0 p r))".to_string());

    let mut proof = Proof::new();
    proof.add_assume(and_term, None);
    proof.add_rule_step(
        AletheRule::AndPos(0),
        vec![demorgan, p],
        vec![],
        vec![and_term],
    );

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[and_term],
        Some(&overrides),
    )
    .expect("let-bridged assume must render");

    assert!(
        output.contains("(assume t0.a (let ((?v_0 q)) (and ?v_0 p r)))"),
        "{output}"
    );
    assert!(
        output.contains(
            "(step t0.l (cl (= (let ((?v_0 q)) (and ?v_0 p r)) (and p q r))) :rule hole)"
        ),
        "{output}"
    );
    // Exactly ONE hole: the let-elimination equivalence, nothing else.
    assert_eq!(output.matches(":rule hole").count(), 1, "{output}");
    assert!(
        output.contains("(step t1 (cl (not (and p q r)) p) :rule and_pos :args (0))"),
        "{output}"
    );
}

/// (B) A printed LEFT-NESTED binary `and` over a flattened internal term is
/// decomposed by the shared printed-nesting navigator: one genuine `and_pos`
/// per printed node, resolved into the traced clause. The printed ROOT is
/// untouched, so the resolution that consumes this gate against the assume is
/// unaffected.
#[test]
fn test_nested_binary_and_gate_is_navigated_not_mis_indexed() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, ProofStep};

    let mut terms = TermStore::new();
    let p = terms.mk_var("p".to_string(), Sort::Bool);
    let q = terms.mk_var("q".to_string(), Sort::Bool);
    let r = terms.mk_var("r".to_string(), Sort::Bool);
    let and_term = terms.mk_and(vec![p, q, r]);
    let demorgan = terms.mk_not(and_term);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(and_term, "(and (and p q) r)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let step = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: vec![demorgan, p],
        premises: vec![],
        args: vec![and_term],
    };
    let printed = printer.format_step(&step, ProofId(1)).unwrap();
    assert_eq!(
        printed,
        "(step t1.g0 (cl (not (and (and p q) r)) (and p q)) :rule and_pos :args (0))\n\
         (step t1.g1 (cl (not (and p q)) p) :rule and_pos :args (0))\n\
         (step t1 (cl (not (and (and p q) r)) p) :rule resolution :premises (t1.g0 t1.g1))"
    );
}

/// (B') A FLAT printed `and` whose authored operand order diverges from AY's
/// TermId-sorted internal conjunct vector: the wire index misses, but the
/// extracted conjunct IS a unique printed operand, so the gate is re-slotted
/// to the printed index — a pure printing-index correction, exact by
/// construction.
#[test]
fn test_flat_reordered_and_gate_is_reslotted_to_the_printed_index() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, ProofStep};

    let mut terms = TermStore::new();
    let p = terms.mk_var("p".to_string(), Sort::Bool);
    let q = terms.mk_var("q".to_string(), Sort::Bool);
    let r = terms.mk_var("r".to_string(), Sort::Bool);
    let and_term = terms.mk_and(vec![p, q, r]);
    let demorgan = terms.mk_not(and_term);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    // Authored operand order: `p` sits at printed index 1, not 0.
    overrides.insert(and_term, "(and r p q)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let step = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: vec![demorgan, p],
        premises: vec![],
        args: vec![and_term],
    };
    let printed = printer.format_step(&step, ProofId(1)).unwrap();
    assert_eq!(
        printed,
        "(step t1 (cl (not (and r p q)) p) :rule and_pos :args (1))"
    );
}

/// The flat re-slot declines on a DUPLICATED printed spelling — ambiguity
/// must never pick an index — and the step still fails loud downstream.
#[test]
fn test_flat_reslot_declines_on_duplicate_printed_operand() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, ProofStep};

    let mut terms = TermStore::new();
    let p = terms.mk_var("p".to_string(), Sort::Bool);
    let q = terms.mk_var("q".to_string(), Sort::Bool);
    let r = terms.mk_var("r".to_string(), Sort::Bool);
    let and_term = terms.mk_and(vec![p, q, r]);
    let demorgan = terms.mk_not(and_term);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    // `p` occurs twice in the printed spelling: no unique printed index.
    overrides.insert(and_term, "(and q p p)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let step = ProofStep::Step {
        rule: AletheRule::AndPos(0),
        clause: vec![demorgan, p],
        premises: vec![],
        args: vec![and_term],
    };
    let err = printer
        .format_step(&step, ProofId(1))
        .expect_err("a duplicated printed operand must not be re-slotted");
    assert!(
        format!("{err}").contains("and_pos"),
        "unexpected error: {err}"
    );
}

/// D1b: a printed NESTED binary `or` gate over a flattened internal or-term.
/// carcara compares the gate's top-level arity against the clause tail length,
/// so the re-nested surface spelling must be decomposed the same way.
#[test]
fn test_nested_binary_or_gate_is_decomposed_per_printed_node() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, ProofStep};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a".to_string(), Sort::Bool);
    let b = terms.mk_var("b".to_string(), Sort::Bool);
    let c = terms.mk_var("c".to_string(), Sort::Bool);
    let or_term = terms.mk_or(vec![a, b, c]);
    let not_or = terms.mk_not_raw(or_term);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(or_term, "(or (or a b) c)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let step = ProofStep::Step {
        rule: AletheRule::OrPos(0),
        clause: vec![not_or, a, b, c],
        premises: vec![],
        args: vec![or_term],
    };
    let printed = printer.format_step(&step, ProofId(1)).unwrap();
    assert_eq!(
        printed,
        "(step t1.g0 (cl (not (or (or a b) c)) (or a b) c) :rule or_pos)\n\
         (step t1.g1 (cl (not (or a b)) a b) :rule or_pos)\n\
         (step t1 (cl (not (or (or a b) c)) a b c) :rule resolution :premises (t1.g0 t1.g1))"
    );
}

/// FAIL LOUD. When the printed shape holds neither the conjunct nor a
/// navigable path to it, no `:args (i)` is safe: the step must NOT ship. A
/// wrong proof is worse than no proof, so the printer raises and the caller's
/// unverifiable-proof path fires.
#[test]
fn test_unnavigable_and_pos_gate_fails_loud_instead_of_shipping_a_wrong_index() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, ProofStep};

    let mut terms = TermStore::new();
    let p = terms.mk_var("p".to_string(), Sort::Bool);
    let q = terms.mk_var("q".to_string(), Sort::Bool);
    let r = terms.mk_var("r".to_string(), Sort::Bool);
    let and_term = terms.mk_and(vec![p, q, r]);
    let demorgan = terms.mk_not(and_term);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    // The printed root mentions `q`, but `q` itself prints as `qq`, so no
    // printed operand anywhere in the nesting is the extracted conjunct.
    overrides.insert(and_term, "(and p q r)".to_string());
    overrides.insert(q, "qq".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let step = ProofStep::Step {
        rule: AletheRule::AndPos(1),
        clause: vec![demorgan, q],
        premises: vec![],
        args: vec![and_term],
    };
    let err = printer
        .format_step(&step, ProofId(1))
        .expect_err("an unnavigable and_pos gate must not ship");
    assert!(
        format!("{err}").contains("and_pos"),
        "unexpected error: {err}"
    );
}

/// The same guard on the `or_pos` side, which previously had none at all: a
/// printed gate whose arity cannot reproduce the traced clause tail raises
/// instead of emitting the arity error carcara reports as `invalid`.
#[test]
fn test_or_pos_gate_arity_mismatch_fails_loud() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::{ProofId, ProofStep};

    let mut terms = TermStore::new();
    let a = terms.mk_var("a".to_string(), Sort::Bool);
    let b = terms.mk_var("b".to_string(), Sort::Bool);
    let c = terms.mk_var("c".to_string(), Sort::Bool);
    let or_term = terms.mk_or(vec![a, b, c]);
    let not_or = terms.mk_not_raw(or_term);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    // Printed arity 2 against a 3-literal clause tail: exactly the
    // "expected N terms in 'or' term, got 2" rejection.
    overrides.insert(or_term, "(or a b)".to_string());
    let printer = AlethePrinter::new_with_overrides(&terms, Some(&overrides));

    let step = ProofStep::Step {
        rule: AletheRule::OrPos(0),
        clause: vec![not_or, a, b, c],
        premises: vec![],
        args: vec![or_term],
    };
    let err = printer
        .format_step(&step, ProofId(1))
        .expect_err("an or_pos gate whose printed arity is wrong must not ship");
    assert!(
        format!("{err}").contains("or_pos"),
        "unexpected error: {err}"
    );
}

// ---------------------------------------------------------------------------
// Skolem CONSTANTS are DEFINED as the Hilbert `choice` they denote — never
// declared, and never guessed at (`TermStore::register_skolem_choice`,
// `AlethePrinter::skolem_choice_definitions`).
//
// MEASURED on carcara 1.1.0: its proof grammar admits only `assume`, `step`,
// `anchor` and `define-fun`, so a `(declare-fun ...)` ANYWHERE in the document
// is `parser error: unexpected token: 'declare-fun' (on line 0, column 1)` and
// nothing is checked. That is how the ALIA/piVC and QF_ALIA/ios exemplars
// failed. It is also the wrong statement: `sk` is not an arbitrary fresh
// constant, it is `εx. B`, and only `∃x. B ⟺ B[x := εx. B]` licenses the
// substitution the proof performs.
//
// The contract every test below pins: DEFINE what has provenance, DECLINE the
// rest. There is no declaration fallback, because falling back to a
// declaration is precisely what makes the artifact unparseable.

#[test]
fn skolem_constant_is_defined_as_its_choice_term_not_declared() {
    use ay_core::{SkolemChoice, Symbol};

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
    let quantified = terms.mk_exists(vec![("x".to_string(), Sort::Int)], body);
    let witness = terms.mk_var("sk!x_1", Sort::Int);
    terms.mark_skolem_symbol("sk!x_1");
    terms.register_skolem_choice(
        witness,
        SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Int,
            body,
        },
    );
    let instance = terms.mk_app(Symbol::named("P"), [witness], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_assume(quantified, None);
    proof.add_rule_step(AletheRule::Hole, vec![instance], vec![], vec![]);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[quantified], None)
            .expect("export must succeed");
    assert!(
        output.contains("(define-fun sk!x_1 () Int (choice ((x Int)) (P x)))"),
        "{output}"
    );
    assert!(
        !output.contains("(declare-"),
        "a declared witness states something the proof cannot justify, and makes \
         the document unparseable: {output}"
    );
}

#[test]
fn skolem_definitions_are_emitted_in_mint_order_so_a_body_may_name_an_earlier_one() {
    use ay_core::{SkolemChoice, Symbol};

    // `exists x. exists y. R(x, y)`: the inner witness is minted second and its
    // choice body mentions the outer one. Name order is the REVERSE of mint
    // order here, so a preamble sorted by name would forward-reference.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let inner_body = terms.mk_app(Symbol::named("R"), [x, y], Sort::Bool);
    let inner = terms.mk_exists(vec![("y".to_string(), Sort::Int)], inner_body);
    let outer = terms.mk_exists(vec![("x".to_string(), Sort::Int)], inner);

    let outer_witness = terms.mk_var("sk!zz_outer", Sort::Int);
    terms.mark_skolem_symbol("sk!zz_outer");
    terms.register_skolem_choice(
        outer_witness,
        SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Int,
            body: inner,
        },
    );
    let inner_after = terms.mk_app(Symbol::named("R"), [outer_witness, y], Sort::Bool);
    let inner_witness = terms.mk_var("sk!aa_inner", Sort::Int);
    terms.mark_skolem_symbol("sk!aa_inner");
    terms.register_skolem_choice(
        inner_witness,
        SkolemChoice {
            binder: "y".to_string(),
            sort: Sort::Int,
            body: inner_after,
        },
    );
    let instance = terms.mk_app(
        Symbol::named("R"),
        [outer_witness, inner_witness],
        Sort::Bool,
    );

    let mut proof = Proof::new();
    proof.add_assume(outer, None);
    proof.add_rule_step(AletheRule::Hole, vec![instance], vec![], vec![]);

    let output = try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[outer], None)
        .expect("export must succeed");
    let outer_at = output
        .find("(define-fun sk!zz_outer ")
        .unwrap_or_else(|| panic!("outer witness must be defined: {output}"));
    let inner_at = output
        .find("(define-fun sk!aa_inner ")
        .unwrap_or_else(|| panic!("inner witness must be defined: {output}"));
    assert!(
        outer_at < inner_at,
        "a definition must precede every definition that names it: {output}"
    );
    assert!(
        output.contains("(define-fun sk!aa_inner () Int (choice ((y Int)) (R sk!zz_outer y)))"),
        "{output}"
    );
}

/// REWRITTEN from `skolem_definition_is_withheld_when_its_body_names_an_unresolvable_symbol`,
/// which asserted that the export falls back to `(declare-fun sk!x_ghost () Int)`.
///
/// That "fail-closed" path was fail-OPEN against the real checker: MEASURED,
/// a declaration command anywhere makes the document `invalid` at line 0, so
/// the fallback produced an artifact strictly worse than no artifact. The
/// correct contract is to DECLINE.
#[test]
fn an_unresolvable_choice_body_declines_instead_of_falling_back_to_a_declaration() {
    use ay_core::{SkolemChoice, Symbol};

    // The choice body mentions `ghost`, which the PROBLEM does not declare and
    // no earlier definition introduces. Emitting the definition would spell a
    // symbol the checker cannot resolve.
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let ghost = terms.mk_var("ghost", Sort::Int);
    let body = terms.mk_app(Symbol::named("R"), [x, ghost], Sort::Bool);
    let witness = terms.mk_var("sk!x_ghost", Sort::Int);
    terms.mark_skolem_symbol("sk!x_ghost");
    terms.register_skolem_choice(
        witness,
        SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Int,
            body,
        },
    );
    let declared = terms.mk_var("k", Sort::Int);
    let instance = terms.mk_app(Symbol::named("R"), [witness, declared], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Hole, vec![instance], vec![], vec![]);

    let problem = terms.mk_app(Symbol::named("R"), [declared, declared], Sort::Bool);
    let error =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[problem], None)
            .expect_err("an unresolvable choice body has no correct rendering");
    let AlethePrintError::UndeclarableProofSymbols { count, ref names } = error else {
        panic!("expected UndeclarableProofSymbols, got {error}");
    };
    assert_eq!(count, 1, "{error}");
    assert!(names.contains("sk!x_ghost"), "{error}");

    // And the infallible wrapper must not paper over it with a declaration.
    let rendered = export_alethe_with_problem_scope(&proof, &terms, &[problem]);
    assert!(!rendered.contains("(declare-"), "{rendered}");
    assert!(!rendered.contains("define-fun sk!x_ghost"), "{rendered}");
}

#[test]
fn a_witness_inlined_by_a_certified_skolem_step_is_neither_declared_nor_defined() {
    use ay_core::{SkolemChoice, Symbol};

    // `sko_forall` already resugars this witness to an inline `choice` at every
    // occurrence, so it is not a free symbol of the document. Defining it too
    // would be a second, redundant spelling of the same term — and declining
    // would throw away a document that is already correct.
    let mut terms = TermStore::new();
    let i = terms.mk_var("i", Sort::Int);
    let p_i = terms.mk_app(Symbol::named("P"), [i], Sort::Bool);
    let quantified = terms.mk_forall(vec![("i".to_string(), Sort::Int)], p_i);
    let witness = terms.mk_var("sk!i_dual", Sort::Int);
    terms.mark_skolem_symbol("sk!i_dual");
    let not_p_i = terms.mk_not_raw(p_i);
    terms.register_skolem_choice(
        witness,
        SkolemChoice {
            binder: "i".to_string(),
            sort: Sort::Int,
            body: not_p_i,
        },
    );
    let instance = terms.mk_app(Symbol::named("P"), [witness], Sort::Bool);
    let equality = terms.mk_app(Symbol::named("="), [quantified, instance], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Skolem, vec![equality], vec![], vec![witness]);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[quantified], None)
            .expect("a fully resugared witness needs no preamble at all");
    assert!(!output.contains("declare-fun sk!i_dual"), "{output}");
    assert!(!output.contains("define-fun sk!i_dual"), "{output}");
    assert!(output.contains(":rule sko_forall"), "{output}");
}

/// REWRITTEN from `an_auxiliary_symbol_without_choice_provenance_still_gets_a_declaration`.
///
/// "Still gets a declaration" encoded the fail-OPEN behaviour as correct. A
/// symbol with no recorded defining term has no `define-fun` form either, so
/// the only honest outcomes are "resugar it" or "decline" — and this symbol is
/// neither resugared nor definable.
#[test]
fn an_auxiliary_symbol_without_choice_provenance_declines_rather_than_declaring() {
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let aux = terms.mk_var("_mod_q_7", Sort::Int);
    let k = terms.mk_var("k", Sort::Int);
    let claim = terms.mk_app(Symbol::named("R"), [aux, k], Sort::Bool);
    let problem = terms.mk_app(Symbol::named("R"), [k, k], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Hole, vec![claim], vec![], vec![]);

    let error =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[problem], None)
            .expect_err("a symbol with no defining term cannot be introduced at all");
    let AlethePrintError::UndeclarableProofSymbols { count, ref names } = error else {
        panic!("expected UndeclarableProofSymbols, got {error}");
    };
    assert_eq!(count, 1, "{error}");
    assert!(names.contains("_mod_q_7"), "{error}");
}

/// REWRITTEN from `skolem_definition_is_withheld_when_the_binder_name_is_a_problem_symbol`,
/// which asserted a `(declare-fun sk!x_shadow () Int)` fallback.
///
/// Withholding the definition is still right — the binder is printed by NAME,
/// so a problem symbol spelled the same way would be CAPTURED by it — but the
/// consequence of withholding is a DECLINE, not a declaration.
#[test]
fn a_capturing_binder_declines_instead_of_falling_back_to_a_declaration() {
    use ay_core::{SkolemChoice, Symbol};

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
    let witness = terms.mk_var("sk!x_shadow", Sort::Int);
    terms.mark_skolem_symbol("sk!x_shadow");
    terms.register_skolem_choice(
        witness,
        SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Int,
            body,
        },
    );
    let instance = terms.mk_app(Symbol::named("P"), [witness], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Hole, vec![instance], vec![], vec![]);

    // The PROBLEM declares its own `x` — the same spelling as the binder.
    let problem = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
    let error =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[problem], None)
            .expect_err("a binder that would capture a problem symbol must not be emitted");
    let AlethePrintError::UndeclarableProofSymbols { ref names, .. } = error else {
        panic!("expected UndeclarableProofSymbols, got {error}");
    };
    assert!(names.contains("sk!x_shadow"), "{error}");
}

/// (E) `define-fun` is a MACRO and identical bodies COLLAPSE.
///
/// MEASURED on carcara 1.1.0 with a two-line preamble
/// `(define-fun sk1 () U (choice ((x U)) true))` /
/// `(define-fun sk2 () U (choice ((x U)) true))`: the step
/// `(step t2 (cl (= sk1 sk2)) :rule refl)` CHECKS and the document is `valid`
/// — two distinct Skolem constants proved equal. Give them different bodies
/// and the same step is rejected (`reflexivity failed`), so the shared body is
/// the whole cause. Alpha-renaming the binder does not save it either:
/// `(choice ((x U)) true)` and `(choice ((y U)) true)` also collapse.
///
/// So a definition must carry the witness's OWN defining predicate, and two
/// witnesses must never end up with the same one. Here both witnesses were
/// minted for bodies that render identically, so NEITHER may be defined.
#[test]
fn two_skolems_with_the_same_choice_body_are_never_both_defined() {
    use ay_core::{SkolemChoice, Symbol};

    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    // Two bodies that are alpha-variants: `(P x)` under binder `x`, and
    // `(P y)` under binder `y`. Distinct TermIds, identical after the binder
    // is normalized away — exactly the shape carcara identifies.
    let body_x = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
    let body_y = terms.mk_app(Symbol::named("P"), [y], Sort::Bool);

    let first = terms.mk_var("sk!a_1", Sort::Int);
    terms.mark_skolem_symbol("sk!a_1");
    terms.register_skolem_choice(
        first,
        SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Int,
            body: body_x,
        },
    );
    let second = terms.mk_var("sk!b_2", Sort::Int);
    terms.mark_skolem_symbol("sk!b_2");
    terms.register_skolem_choice(
        second,
        SkolemChoice {
            binder: "y".to_string(),
            sort: Sort::Int,
            body: body_y,
        },
    );
    let claim = terms.mk_app(Symbol::named("R"), [first, second], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Hole, vec![claim], vec![], vec![]);

    // The problem must APPLY `P`, or the definitions would be withheld for the
    // unrelated reason that `P` does not resolve — and this test would pass
    // without the collapse guard existing at all.
    let problem_r = terms.mk_app(Symbol::named("R"), [k, k], Sort::Bool);
    let problem_p = terms.mk_app(Symbol::named("P"), [k], Sort::Bool);
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[problem_r, problem_p],
        None,
    )
    .expect_err("two witnesses sharing a body must not both be defined");
    let AlethePrintError::UndeclarableProofSymbols { count, ref names } = error else {
        panic!("expected UndeclarableProofSymbols, got {error}");
    };
    assert_eq!(
        count, 2,
        "BOTH witnesses must be withheld — defining either one alone would still \
         be correct, but defining both identifies them: {error}"
    );
    assert!(
        names.contains("sk!a_1") && names.contains("sk!b_2"),
        "{error}"
    );
}

/// The control for the collapse guard: DIFFERENT bodies must still be defined.
/// A guard that withheld everything would also "pass" the test above.
#[test]
fn two_skolems_with_different_choice_bodies_are_both_defined() {
    use ay_core::{SkolemChoice, Symbol};

    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let body_p = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
    let body_q = terms.mk_app(Symbol::named("Q"), [x], Sort::Bool);

    let first = terms.mk_var("sk!a_1", Sort::Int);
    terms.mark_skolem_symbol("sk!a_1");
    terms.register_skolem_choice(
        first,
        SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Int,
            body: body_p,
        },
    );
    let second = terms.mk_var("sk!b_2", Sort::Int);
    terms.mark_skolem_symbol("sk!b_2");
    terms.register_skolem_choice(
        second,
        SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Int,
            body: body_q,
        },
    );
    let claim = terms.mk_app(Symbol::named("R"), [first, second], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Hole, vec![claim], vec![], vec![]);

    // `P` and `Q` must be applied by the problem, or the preamble check would
    // withhold both definitions for an unrelated reason.
    let problem_r = terms.mk_app(Symbol::named("R"), [k, k], Sort::Bool);
    let problem_p = terms.mk_app(Symbol::named("P"), [k], Sort::Bool);
    let problem_q = terms.mk_app(Symbol::named("Q"), [k], Sort::Bool);
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &[problem_r, problem_p, problem_q],
        None,
    )
    .expect("distinct bodies are independently definable");
    assert!(
        output.contains("(define-fun sk!a_1 () Int (choice ((x Int)) (P x)))"),
        "{output}"
    );
    assert!(
        output.contains("(define-fun sk!b_2 () Int (choice ((x Int)) (Q x)))"),
        "{output}"
    );
    assert!(!output.contains("(declare-"), "{output}");
}

/// (D) The preamble invariant is checked on the TEXT, not claimed about terms.
///
/// The term-level guard walks `Var` nodes only, so an application HEAD is
/// invisible to it: a body `(choice ((x Int)) (P x))` whose `P` the problem
/// never applies passes every term-level test and then ships a definition
/// carcara rejects with `identifier 'P' is not defined`.
///
/// Re-parsing the emitted preamble with AY's own Alethe parser catches it, and
/// the export declines. This test is the difference between the two: the ONLY
/// thing separating it from `..._is_defined_as_its_choice_term_not_declared`
/// is that the problem here does not mention `P`.
#[test]
fn a_definition_body_naming_an_unresolvable_function_declines() {
    use ay_core::{SkolemChoice, Symbol};

    let mut terms = TermStore::new();
    let k = terms.mk_var("k", Sort::Int);
    let x = terms.mk_var("x", Sort::Int);
    let body = terms.mk_app(Symbol::named("P"), [x], Sort::Bool);
    let witness = terms.mk_var("sk!x_1", Sort::Int);
    terms.mark_skolem_symbol("sk!x_1");
    terms.register_skolem_choice(
        witness,
        SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Int,
            body,
        },
    );
    let claim = terms.mk_app(Symbol::named("R"), [witness, k], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Hole, vec![claim], vec![], vec![]);

    // The problem applies `R`, never `P`. Every free VARIABLE of the body
    // (just the binder) resolves, so only a check of the emitted text can
    // catch this.
    let problem = terms.mk_app(Symbol::named("R"), [k, k], Sort::Bool);
    let error =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[problem], None)
            .expect_err("a body naming an unresolvable function must not ship");
    let AlethePrintError::UndeclarableProofSymbols { ref names, .. } = error else {
        panic!("expected UndeclarableProofSymbols, got {error}");
    };
    assert!(names.contains("sk!x_1"), "{error}");
}

// ---------------------------------------------------------------------------
// carcara's `or` rule is POSITIONAL (`or_conclusion_in_premise_order`).
//
// MEASURED on carcara 1.1.0 with problem `(assert (or a b))`:
//   premise `(or a b)`, conclusion `(cl b a)`
//     -> checking failed on step 't1' with rule 'or':
//        expected terms to be equal: 'a' and 'b'          => invalid
//   premise `(or a b)`, conclusion `(cl a b)`             => accepted
// It does not flatten either: a nested or-term gives
//   "expected 2 terms in clause, got 3".
//
// AY's internal clause is a SET, so its order is whatever order the solver
// built it in. Reordering the RENDERED clause is sound (an Alethe clause IS a
// disjunction) and is the whole fix. This is what
// QF_IDL/DTP/DTP_k2_n35_c210_s12 failed on:
//   checking failed on step 't173516' with rule 'or':
//   expected terms to be equal: '(<= 12 (+ x33 (- x8)))' and
//   '(<= 40 (+ x26 (- x27)))'

#[test]
fn or_step_conclusion_is_reordered_into_the_premise_disjunct_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let or_term = terms.mk_or(vec![a, b]);

    let mut proof = Proof::new();
    let premise = proof.add_assume(or_term, None);
    // The internal clause is the REVERSE permutation of the premise's
    // disjuncts — exactly the shape carcara rejects.
    proof.add_rule_step(AletheRule::Or, vec![b, a], vec![premise], vec![]);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[or_term], None)
            .expect("export must succeed");
    assert!(
        output.contains("(step t1 (cl a b) :rule or :premises (t0))"),
        "the conclusion must be re-slotted into premise order: {output}"
    );
    assert!(
        !output.contains("(cl b a)"),
        "the rejected order must not survive: {output}"
    );
}

#[test]
fn an_already_ordered_or_step_is_left_byte_identical() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let or_term = terms.mk_or(vec![a, b]);

    let mut proof = Proof::new();
    let premise = proof.add_assume(or_term, None);
    proof.add_rule_step(AletheRule::Or, vec![a, b], vec![premise], vec![]);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[or_term], None)
            .expect("export must succeed");
    assert!(
        output.contains("(step t1 (cl a b) :rule or :premises (t0))"),
        "{output}"
    );
}

/// Fail-closed direction: a clause that is NOT a permutation of the premise's
/// disjuncts must be rendered exactly as it was, not force-fitted.
///
/// Re-slotting here would silently replace a literal, which is a wrong proof
/// rather than a rejected one.
#[test]
fn a_non_permuted_or_clause_is_not_re_slotted() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    let c = terms.mk_var("c", Sort::Bool);
    let or_term = terms.mk_or(vec![a, b]);

    let mut proof = Proof::new();
    let premise = proof.add_assume(or_term, None);
    // `c` is not among the premise's disjuncts.
    proof.add_rule_step(AletheRule::Or, vec![c, a], vec![premise], vec![]);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[or_term, c], None)
            .expect("export must succeed");
    assert!(
        output.contains("(step t1 (cl c a) :rule or :premises (t0))"),
        "a clause with an unmatched literal must be left alone: {output}"
    );
}

/// A repeated disjunct must consume a distinct clause position per occurrence,
/// so a multiset — not a set — is what gets matched.
///
/// Built with `mk_app` rather than `mk_or`, because `mk_or` normalizes a
/// duplicated disjunct away and the shape under test would not survive.
#[test]
fn or_reordering_matches_repeated_disjuncts_as_a_multiset() {
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Bool);
    let b = terms.mk_var("b", Sort::Bool);
    // `(or b a b)`: `b` twice.
    let or_term = terms.mk_app(Symbol::named("or"), [b, a, b], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(or_term, None);
    proof.add_rule_step(AletheRule::Or, vec![a, b, b], vec![premise], vec![]);

    let output =
        try_export_alethe_with_problem_scope_and_overrides(&proof, &terms, &[or_term], None)
            .expect("export must succeed");
    assert!(
        output.contains("(step t1 (cl b a b) :rule or :premises (t0))"),
        "{output}"
    );
}

// ---------------------------------------------------------------------------
// A `cong` whose PRINTED operands cannot be checked must DECLINE
// (`surface_cong_has_uncheckable_operands`).
//
// MEASURED on carcara 1.1.0 with premise `(= x y)`:
//   (= (g x) (f y))  -> functions don't match: 'g' and 'f'
//   (= zzz (f y))    -> term is not an application or operation: 'zzz'
//   (= zzz x)        -> term is not an application or operation: 'zzz'
// all `invalid`.
//
// There is no honest repair. Emitting
//   (step t1.s (cl (= (g x) (f x))) :rule hole)
//   (step t1.c (cl (= (f x) (f y))) :rule cong :premises (t0))
//   (step t1   (cl (= (g x) (f y))) :rule trans :premises (t1.s t1.c))
// would turn `invalid` into `holey` while proving NOTHING about the two terms
// — a hole proves anything. A holey verdict bought that way HIDES the defect,
// which is worse than reporting it. This is the same dishonesty as the
// `(cl false) :rule trust` stub the campaign removed.
//
// QF_LIA/.../SmallOperatingSystem-PT-MT8192DC2048/RC-12 is the live instance:
//   checking failed on step 't12' with rule 'cong':
//   operators don't match: 'and' and '<='

#[test]
fn a_cong_whose_printed_operands_have_different_heads_declines() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq_xy = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let f_x = terms.mk_app(Symbol::named("f"), [x], Sort::Int);
    let f_y = terms.mk_app(Symbol::named("f"), [y], Sort::Int);
    let conclusion = terms.mk_app(Symbol::named("="), [f_x, f_y], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(eq_xy, None);
    proof.add_rule_step(AletheRule::Cong, vec![conclusion], vec![premise], vec![]);

    // Elaboration simplified an authored `(g x)` down to `(f x)`; the surface
    // override prints the authored spelling back, so the step equates a `g`
    // application with an `f` application.
    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(f_x, "(g x)".to_string());
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect_err("a printed congruence with different heads must fail closed");
    let AlethePrintError::InvalidCongruenceStep { ref reason, .. } = error else {
        panic!("expected InvalidCongruenceStep, got {error}");
    };
    assert!(
        reason.contains("different operators"),
        "unexpected reason: {reason}"
    );
}

/// The BARE-ATOM case. A sibling guard that required BOTH sides to be
/// applications let this through to the default rendering, which shipped
/// `(step t1 (cl (= zzz (f y))) :rule cong :premises (t0))` — MEASURED
/// `invalid`. An operand that is not a printed application fails the rule
/// whatever the other side is.
#[test]
fn a_cong_whose_printed_operand_is_a_bare_atom_declines() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq_xy = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let f_x = terms.mk_app(Symbol::named("f"), [x], Sort::Int);
    let f_y = terms.mk_app(Symbol::named("f"), [y], Sort::Int);
    let conclusion = terms.mk_app(Symbol::named("="), [f_x, f_y], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(eq_xy, None);
    proof.add_rule_step(AletheRule::Cong, vec![conclusion], vec![premise], vec![]);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(f_x, "zzz".to_string());
    let error = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    )
    .expect_err("a bare-atom congruence operand must fail closed");
    let AlethePrintError::InvalidCongruenceStep { ref reason, .. } = error else {
        panic!("expected InvalidCongruenceStep, got {error}");
    };
    assert!(
        reason.contains("not a printed application"),
        "unexpected reason: {reason}"
    );
}

/// The guard must NOT manufacture a `hole`-plus-`trans` bridge for the shape it
/// declines. A holey verdict bought with an unjustified hole hides the defect.
#[test]
fn the_declined_cong_shape_never_becomes_a_hole_bridge() {
    use ay_core::kani_compat::DetHashMap;
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq_xy = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let f_x = terms.mk_app(Symbol::named("f"), [x], Sort::Int);
    let f_y = terms.mk_app(Symbol::named("f"), [y], Sort::Int);
    let conclusion = terms.mk_app(Symbol::named("="), [f_x, f_y], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(eq_xy, None);
    proof.add_rule_step(AletheRule::Cong, vec![conclusion], vec![premise], vec![]);

    let mut overrides: DetHashMap<TermId, String> = DetHashMap::default();
    overrides.insert(f_x, "(g x)".to_string());
    let rendered = export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        Some(&overrides),
    );
    assert!(rendered.contains("UNVERIFIABLE PROOF"), "{rendered}");
    assert!(
        !rendered.contains(":rule hole"),
        "declining must not be converted into a manufactured hole: {rendered}"
    );
    assert!(
        !rendered.contains(":rule trans"),
        "declining must not be converted into a manufactured trans bridge: {rendered}"
    );
    assert!(!rendered.contains("(step "), "{rendered}");
}

/// The control: an ordinary same-operator congruence still renders. A guard
/// that declined everything would also "pass" the tests above.
#[test]
fn an_ordinary_same_operator_cong_still_renders() {
    use ay_core::Symbol;

    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let eq_xy = terms.mk_app(Symbol::named("="), [x, y], Sort::Bool);
    let f_x = terms.mk_app(Symbol::named("f"), [x], Sort::Int);
    let f_y = terms.mk_app(Symbol::named("f"), [y], Sort::Int);
    let conclusion = terms.mk_app(Symbol::named("="), [f_x, f_y], Sort::Bool);

    let mut proof = Proof::new();
    let premise = proof.add_assume(eq_xy, None);
    proof.add_rule_step(AletheRule::Cong, vec![conclusion], vec![premise], vec![]);

    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
    .expect("a same-operator congruence is exactly what `cong` checks");
    assert!(
        output.contains("(step t1 (cl (= (f x) (f y))) :rule cong :premises (t0))"),
        "{output}"
    );
}

/// Build the store-permutation clause
/// `(cl (= i j) (= (store (store a i v) j w) (store (store a j w) i v)))`,
/// optionally with the index equality spelled the other way round.
fn store_permutation_clause(terms: &mut TermStore, reversed_index_equality: bool) -> Vec<TermId> {
    use ay_core::{ArraySort, Symbol};

    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int))),
    );
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left_inner = terms.mk_store(array, i, v);
    let left = terms.mk_store(left_inner, j, w);
    let right_inner = terms.mk_store(array, j, w);
    let right = terms.mk_store(right_inner, i, v);
    let index_equality = if reversed_index_equality {
        terms.mk_app(Symbol::named("="), [j, i], Sort::Bool)
    } else {
        terms.mk_app(Symbol::named("="), [i, j], Sort::Bool)
    };
    let array_equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    vec![index_equality, array_equality]
}

fn export_store_permutation(clause: Vec<TermId>, terms: &TermStore) -> String {
    use ay_core::TheoryLemmaKind;

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind("array", clause, TheoryLemmaKind::ArrayStorePermutation);
    try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        terms,
        &scope_covering_proof(&proof),
        None,
    )
    .expect("a store-permutation lemma always renders (derived, or as an honest hole)")
}

/// Carcara has no `store_permutation` rule, so the lemma is DERIVED from its
/// `arrays_ext` / `arrays_row` / `arrays_idx` / `cong` / `trans` primitives.
#[test]
fn test_array_store_permutation_lowers_to_checked_array_rules() {
    let mut terms = TermStore::new();
    let clause = store_permutation_clause(&mut terms, false);
    let output = export_store_permutation(clause, &terms);

    // The unproved placeholder and the unknown internal name are both gone.
    assert!(!output.contains(":rule hole"), "{output}");
    assert!(!output.contains("store_permutation"), "{output}");
    for rule in [
        ":rule arrays_ext",
        ":rule arrays_row",
        ":rule arrays_idx",
        ":rule cong",
        ":rule subproof",
    ] {
        assert!(output.contains(rule), "missing {rule} in {output}");
    }
    // The derivation must conclude EXACTLY the clause AY certified.
    assert!(
        output.contains(
            "(step t0 (cl (= i j) \
             (= (store (store a i v) j w) (store (store a j w) i v))) :rule resolution"
        ),
        "{output}"
    );
}

/// The index disequality is the whole side condition, and the derivation has to
/// discharge it in whichever orientation the clause spells.
#[test]
fn test_array_store_permutation_accepts_the_reversed_index_equality() {
    use ay_core::TheoryLemmaKind;

    let mut terms = TermStore::new();
    let clause = store_permutation_clause(&mut terms, true);
    // The classifier assigns the same kind either way round, so the printer is
    // the only thing that could have been orientation-sensitive.
    assert_eq!(
        recognize_array_theory_lemma(&terms, &clause),
        Some(TheoryLemmaKind::ArrayStorePermutation)
    );
    let output = export_store_permutation(clause, &terms);

    assert!(!output.contains(":rule hole"), "{output}");
    assert!(output.contains(":rule arrays_ext"), "{output}");
    assert!(
        output.contains(
            "(step t0 (cl (= j i) \
             (= (store (store a i v) j w) (store (store a j w) i v))) :rule resolution"
        ),
        "{output}"
    );
}

/// NEGATIVE: without the index disequality the clause is simply FALSE — at
/// `i = j` the two chains are `store(a, i, w)` and `store(a, i, v)`. The printer
/// must keep the honest `hole` rather than derive it.
#[test]
fn test_array_store_permutation_without_the_index_guard_stays_a_hole() {
    use ay_core::{ArraySort, Symbol};

    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int))),
    );
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left_inner = terms.mk_store(array, i, v);
    let left = terms.mk_store(left_inner, j, w);
    let right_inner = terms.mk_store(array, j, w);
    let right = terms.mk_store(right_inner, i, v);
    let unrelated = terms.mk_var("p", Sort::Bool);
    let array_equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "array",
        vec![unrelated, array_equality],
        TheoryLemmaKind::ArrayStorePermutation,
    );
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
    .expect("an unguarded permutation clause still renders");
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule arrays_ext"), "{output}");
}

/// NEGATIVE: a REPEATED index term writes the same `(index, value)` multiset but
/// denotes a different array — `store(store(a, i, v), i, w)` is `store(a, i, w)`
/// while `store(store(a, i, w), i, v)` is `store(a, i, v)`. The derivation must
/// not be emitted for it.
#[test]
fn test_array_store_permutation_with_a_repeated_index_stays_a_hole() {
    use ay_core::{ArraySort, Symbol};

    let mut terms = TermStore::new();
    let array = terms.mk_var(
        "a",
        Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int))),
    );
    let i = terms.mk_var("i", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left_inner = terms.mk_store(array, i, v);
    let left = terms.mk_store(left_inner, i, w);
    let right_inner = terms.mk_store(array, i, w);
    let right = terms.mk_store(right_inner, i, v);
    let index_equality = terms.mk_app(Symbol::named("="), [i, i], Sort::Bool);
    let array_equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "array",
        vec![index_equality, array_equality],
        TheoryLemmaKind::ArrayStorePermutation,
    );
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
    .expect("a repeated-index clause still renders");
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule arrays_ext"), "{output}");
}

/// NEGATIVE: two chains over DIFFERENT base arrays are unrelated, whatever they
/// write on top.
#[test]
fn test_array_store_permutation_over_two_bases_stays_a_hole() {
    use ay_core::{ArraySort, Symbol, TheoryLemmaKind};

    let mut terms = TermStore::new();
    let sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let a = terms.mk_var("a", sort.clone());
    let b = terms.mk_var("b", sort);
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left_inner = terms.mk_store(a, i, v);
    let left = terms.mk_store(left_inner, j, w);
    let right_inner = terms.mk_store(b, j, w);
    let right = terms.mk_store(right_inner, i, v);
    let index_equality = terms.mk_app(Symbol::named("="), [i, j], Sort::Bool);
    let array_equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_theory_lemma_with_kind(
        "array",
        vec![index_equality, array_equality],
        TheoryLemmaKind::ArrayStorePermutation,
    );
    let output = try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &terms,
        &scope_covering_proof(&proof),
        None,
    )
    .expect("a two-base clause still renders");
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule arrays_ext"), "{output}");
}

/// REGRESSION: the transposition derivation inlines the printed chains into
/// the scope of the `arrays_ext` witness's `choice` binder, which is
/// literally `x`. A chain that mentions a user symbol named `x` would have it
/// CAPTURED by that binder — the exported document would claim a different
/// term than the one the checker constructs, and come back carcara-`invalid`
/// where the honest hole is `holey`. The lowering must decline, exactly as
/// the `arrays_ext` witness installation lane declines, and keep the hole.
#[test]
fn test_array_store_permutation_mentioning_the_witness_binder_stays_a_hole() {
    use ay_core::{ArraySort, Symbol};

    // Once with the colliding symbol as a stored VALUE, once as the BASE.
    for base_is_x in [false, true] {
        let mut terms = TermStore::new();
        let sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
        let array = terms.mk_var(if base_is_x { "x" } else { "a" }, sort);
        let i = terms.mk_var("i", Sort::Int);
        let j = terms.mk_var("j", Sort::Int);
        let v = terms.mk_var(if base_is_x { "v" } else { "x" }, Sort::Int);
        let w = terms.mk_var("w", Sort::Int);
        let left_inner = terms.mk_store(array, i, v);
        let left = terms.mk_store(left_inner, j, w);
        let right_inner = terms.mk_store(array, j, w);
        let right = terms.mk_store(right_inner, i, v);
        let index_equality = terms.mk_app(Symbol::named("="), [i, j], Sort::Bool);
        let array_equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

        let output = export_store_permutation(vec![index_equality, array_equality], &terms);
        assert!(
            output.contains(":rule hole"),
            "base_is_x={base_is_x}: {output}"
        );
        assert!(
            !output.contains(":rule arrays_ext"),
            "base_is_x={base_is_x}: {output}"
        );
        // No witness may be built over the colliding chain at all: any
        // `(choice ((x ...)` here would capture the clause's own `x`.
        assert!(
            !output.contains("(choice ((x "),
            "base_is_x={base_is_x}: {output}"
        );
    }
}

/// REGRESSION: the collision can also arrive as an application HEAD — a
/// user FUNCTION named `x` applied to arguments. The printed `(x 0)` is a
/// parse error inside `(choice ((x S)) …)`, so an unguarded lowering would
/// regress the document from `holey` to `invalid`. Measured on carcara
/// 1.1.0: `(x 0)` parses at the top level but not under the binder.
#[test]
fn test_array_store_permutation_with_a_function_named_x_stays_a_hole() {
    use ay_core::{ArraySort, Symbol};

    let mut terms = TermStore::new();
    let sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let array = terms.mk_var("a", sort);
    let zero = terms.mk_int(0.into());
    // Index i = (x 0): an application whose HEAD wears the binder's name.
    let i = terms.mk_app(Symbol::named("x"), [zero], Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let w = terms.mk_var("w", Sort::Int);
    let left_inner = terms.mk_store(array, i, v);
    let left = terms.mk_store(left_inner, j, w);
    let right_inner = terms.mk_store(array, j, w);
    let right = terms.mk_store(right_inner, i, v);
    let index_equality = terms.mk_app(Symbol::named("="), [i, j], Sort::Bool);
    let array_equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);

    let output = export_store_permutation(vec![index_equality, array_equality], &terms);
    assert!(output.contains(":rule hole"), "{output}");
    assert!(!output.contains(":rule arrays_ext"), "{output}");
    assert!(!output.contains("(choice ((x "), "{output}");
}
