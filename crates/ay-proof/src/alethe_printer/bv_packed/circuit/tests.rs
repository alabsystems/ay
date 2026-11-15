// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_core::{Proof, TheoryLemmaKind};

const INDEX_CASES: [(&str, &str); 5] = [
    ("0-0", include_str!("../fixtures/coro-index-0-0.smt2")),
    ("0-7", include_str!("../fixtures/coro-index-0-7.smt2")),
    ("7-0", include_str!("../fixtures/coro-index-7-0.smt2")),
    ("7-7", include_str!("../fixtures/coro-index-7-7.smt2")),
    ("3-4", include_str!("../fixtures/coro-index-3-4.smt2")),
];

pub(super) type TestResult<T = ()> = Result<T, Box<dyn std::error::Error>>;

pub(super) fn original(problem: &str) -> TestResult<(ay_frontend::Context, TermId, TermId)> {
    let mut context = ay_frontend::Context::new();
    for command in ay_frontend::parse(problem)? {
        context.process_command(&command)?;
    }
    let parsed = context
        .assertions_parsed()
        .first()
        .cloned()
        .ok_or("circuit fixture asserts no formula")?;
    let root = aggregate_tests::raw_fixture_term(&mut context, &parsed);
    let negative = context.terms.mk_not_raw(root);
    Ok((context, root, negative))
}

pub(super) fn certificate(name: &str, problem: &str) -> TestResult {
    let (context, root, negative) = original(problem)?;
    let printer = AlethePrinter::new(&context.terms);
    let text = printer
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .expect(name);
    let proof = format!(
        "(assume a {})\n{text}(step done (cl) :rule resolution :premises (a t7))\n",
        printer.format_term(root)
    );
    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
    let path = std::env::temp_dir().join(format!("ay-circuit-{name}-{}.json", std::process::id()));
    std::fs::write(&path, serde_json::to_vec(&serde_json::json!({"type":"alethe_certificate","version":"1.0","problem":problem,"proof":proof})).unwrap()).unwrap();
    println!("independent replay certificate: {}", path.display());
    Ok(())
}

/// The printed derivation is decided by the counted caps: a refutation's
/// only wall clock is the outer hang guard, not a three-second deadline that
/// refused this certificate under contention.
#[test]
fn circuit_refutation_wall_is_only_the_hang_guard() -> TestResult {
    let (context, root, _) = original(INDEX_CASES[0].1)?;
    let printer = AlethePrinter::new(&context.terms);
    let mut proof = PackedProof::new(&printer, ProofId(7)).ok_or("packed proof")?;
    let assumption = proof.fresh();
    let mut circuit = Circuit::new(&mut proof);
    let (bit, equality) = circuit.boolean(root, 0).ok_or("circuit input")?;
    let unit = circuit
        .proof
        .transport_unit(&equality, &assumption)
        .ok_or("transported unit")?;
    circuit.input(vec![bit], unit).ok_or("circuit clause")?;
    let before = Instant::now();
    circuit.refute().ok_or("circuit refutation")?;
    let deadline = circuit.deadline.ok_or("refutation deadline")?;
    assert!(deadline >= before + REFUTATION_HANG_GUARD);
    assert_eq!(REFUTATION_HANG_GUARD, Duration::from_secs(300));
    Ok(())
}

#[test]
fn original_coroutine_index_circuits_have_checked_source_derivations() -> TestResult {
    for (name, problem) in INDEX_CASES {
        certificate(name, problem)?;
    }
    Ok(())
}

#[test]
fn circuit_full_width_dualities_and_double_negation_are_explicit() -> TestResult {
    for width in [1, 9, 64, 128] {
        for op in ["bvult", "bvugt"] {
            let dual = if op == "bvult" { "bvuge" } else { "bvule" };
            certificate(&format!("{op}-{width}"), &format!("(set-logic QF_BV) (declare-const a (_ BitVec {width})) (declare-const b (_ BitVec {width})) (assert (and (not (not ({op} a b))) ({dual} a b))) (check-sat)"))?;
        }
    }
    Ok(())
}

#[test]
fn circuit_missing_guard_changed_source_and_small_budget_decline() -> TestResult {
    let (_, problem) = INDEX_CASES[0];
    let problem = problem.replace(
        "(bvuge (bvadd (_ bv24 64) frame) (bvadd (_ bv8 64) vbase))",
        "true",
    );
    let (context, _, negative) = original(&problem)?;
    assert!(AlethePrinter::new(&context.terms)
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    let (context, root, negative) = original(INDEX_CASES[0].1)?;
    let mut overrides = DetHashMap::default();
    overrides.insert(root, "false".into());
    assert!(
        AlethePrinter::new_with_overrides(&context.terms, Some(&overrides))
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none()
    );
    let printer = AlethePrinter::new_with_overrides_and_budget(&context.terms, None, Some(1024));
    assert!(printer
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    assert!(printer.work_budget_exhausted());
    Ok(())
}

#[test]
fn original_coroutine_indices_fit_native_refutation_limits() -> TestResult {
    for (name, problem) in INDEX_CASES {
        let (context, root, negative) = original(problem)?;
        let mut proof = Proof::new();
        let assume = proof.add_assume(root, None);
        let lemma =
            proof.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
        proof.add_resolution(vec![], root, assume, lemma);
        crate::check_proof_strict(&proof, &context.terms)
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
    }
    Ok(())
}

#[test]
fn original_coroutine_array_fits_native_refutation_limits() -> TestResult {
    let (context, root, negative) = original(include_str!("../fixtures/coroutine_disjoint.smt2"))?;
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], root, assume, lemma);
    crate::check_proof_strict(&proof, &context.terms).unwrap();
    Ok(())
}

#[test]
fn circuit_repeated_source_and_malformed_children_decline_before_rendering() {
    let mut terms = ay_core::TermStore::new();
    let mut root = terms.mk_bool(true);
    for _ in 0..14 {
        root = terms.mk_app(Symbol::named("and"), &[root, root], Sort::Bool);
    }
    let negative = terms.mk_not_raw(root);
    assert!(AlethePrinter::new(&terms)
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    let bit = terms.mk_bool(true);
    let bad = terms.mk_app(Symbol::named("bvadd"), &[bit, bit], Sort::bitvec(8));
    let eq = terms.mk_app(Symbol::named("="), &[bad, bad], Sort::Bool);
    let negative = terms.mk_not_raw(eq);
    assert!(AlethePrinter::new(&terms)
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
}

#[test]
fn original_coroutine_array_has_a_checked_source_circuit() -> TestResult {
    certificate(
        "array-original",
        include_str!("../fixtures/coroutine_disjoint.smt2"),
    )?;
    Ok(())
}

fn span_problem(width: u32, offset: u32) -> String {
    format!("(set-logic QF_ABV)(declare-const a (_ BitVec {width}))(declare-const b (_ BitVec {width}))(declare-const v (_ BitVec 8))(declare-const w (_ BitVec 8))(assert (and (or (bvuge a (bvadd b (_ bv2 {width}))) (bvuge b (bvadd a (_ bv2 {width})))) (and (bvugt (bvadd a (_ bv2 {width})) a) (and (bvugt (bvadd b (_ bv2 {width})) b) (not (= v (select (store (store ((as const (Array (_ BitVec {width}) (_ BitVec 8))) (_ bv0 8)) b v) (bvadd a (_ bv{offset} {width})) w) b)))))))(check-sat)")
}

pub(super) fn native(problem: &str) -> TestResult<bool> {
    let (context, root, negative) = original(problem)?;
    let mut proof = Proof::new();
    let assume = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(vec![], root, assume, lemma);
    Ok(crate::check_proof_strict(&proof, &context.terms).is_ok())
}

#[test]
fn symbolic_spans_cover_all_offsets_and_full_widths() -> TestResult {
    for width in [9, 64, 128] {
        let problem = span_problem(width, 1);
        assert!(native(&problem)?, "width {width}");
        certificate(&format!("span-{width}"), &problem)?;
    }
    Ok(())
}

#[test]
fn symbolic_spans_refuse_missing_guards_and_outside_writes() -> TestResult {
    let baseline = span_problem(9, 1);
    let missing = baseline.replace("(bvuge a (bvadd b (_ bv2 9)))", "true");
    let wrap = baseline.replace("(bvugt (bvadd a (_ bv2 9)) a)", "true");
    let outside = span_problem(9, 2);
    for problem in [missing, wrap, outside] {
        assert!(!native(&problem)?);
        let (context, _, negative) = original(&problem)?;
        assert!(AlethePrinter::new(&context.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
    Ok(())
}

#[test]
fn source_bound_array_checked_read_over_write_and_counterexamples() -> TestResult {
    for width in [9, 64] {
        let problem = format!("(set-logic QF_ABV)(declare-const memory (Array (_ BitVec {width}) (_ BitVec 8)))(declare-const i (_ BitVec {width}))(declare-const j (_ BitVec {width}))(declare-const value (_ BitVec 8))(assert (and (distinct i j) (not (= (select (store memory i value) j) (select memory j)))))(check-sat)");
        assert!(native(&problem)?);
        certificate(&format!("source-bound-array-{width}"), &problem)?;
        let missing_guard = problem.replace("(distinct i j)", "true");
        assert!(!native(&missing_guard)?);
        let (context, _, negative) = original(&missing_guard)?;
        assert!(AlethePrinter::new(&context.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
    Ok(())
}

#[test]
fn source_bound_array_functionality_has_checked_wire_derivations() -> TestResult {
    for width in [9, 64, 128] {
        let problem = format!("(set-logic QF_ABV)(declare-const memory (Array (_ BitVec {width}) (_ BitVec 8)))(declare-const other (Array (_ BitVec {width}) (_ BitVec 8)))(declare-const i (_ BitVec {width}))(declare-const j (_ BitVec {width}))(assert (and (= i j) (not (= (select memory i) (select memory j)))))(check-sat)");
        assert!(native(&problem)?);
        certificate(&format!("source-bound-functionality-{width}"), &problem)?;
        for mutant in [
            problem.replace("(select memory j)", "(select other j)"),
            problem.replace("(= i j)", "true"),
        ] {
            assert!(!native(&mutant)?);
            let (context, _, negative) = original(&mutant)?;
            assert!(AlethePrinter::new(&context.terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none());
        }
    }
    Ok(())
}

#[test]
fn source_bound_array_offset_functionality_has_checked_wire_derivations() -> TestResult {
    for width in [9, 64, 128] {
        let differences = [0, 7, 17]
            .map(|offset| {
                format!("(not (= (select memory (bvadd i (_ bv{} {width}))) (select memory (bvadd j (_ bv{} {width})))))", offset + 3, offset + 5)
            })
            .join(" ");
        let premise = format!("(= (bvsub i j) (_ bv2 {width}))");
        let problem = format!("(set-logic QF_ABV)(declare-const memory (Array (_ BitVec {width}) (_ BitVec 8)))(declare-const i (_ BitVec {width}))(declare-const j (_ BitVec {width}))(assert (and {premise} (or {differences})))(check-sat)");
        assert!(native(&problem)?);
        certificate(
            &format!("source-bound-offset-functionality-{width}"),
            &problem,
        )?;
        let mutant = problem.replace(&premise, &format!("(= (bvsub i j) (_ bv3 {width}))"));
        assert!(!native(&mutant)?);
        let (context, _, negative) = original(&mutant)?;
        assert!(AlethePrinter::new(&context.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
    Ok(())
}

#[test]
fn source_bound_array_original_frame_has_native_and_wire_derivations() -> TestResult {
    let problem = include_str!("../fixtures/source-bound-frame.smt2");
    assert!(native(problem)?, "the full arbitrary-memory frame theorem");
    let (context, root, _) = original(problem)?;
    let printer = AlethePrinter::new(&context.terms);
    source::preflight(&printer, root).expect("complete frame source stays bounded");
    certificate("source-bound-array-frame", problem)?;
    Ok(())
}
