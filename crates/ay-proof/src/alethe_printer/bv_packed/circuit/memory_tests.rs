// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original complete 48-byte calling-frame memory obligations and diagnostics.
//! These certify memory algebra only, not the semantics of a foreign callee.

use super::tests::{certificate, original, TestResult};
use super::*;
use ay_core::{Proof, TheoryLemmaKind};

const CASES: [(&str, &str); 6] = [
    (
        "output-memory",
        include_str!("memory_fixtures/output-memory.smt2"),
    ),
    ("cell32", include_str!("memory_fixtures/cell32.smt2")),
    ("cell64", include_str!("memory_fixtures/cell64.smt2")),
    (
        "saved-register",
        include_str!("memory_fixtures/saved-register.smt2"),
    ),
    (
        "cell-value",
        include_str!("memory_fixtures/cell-value.smt2"),
    ),
    (
        "outside-frame",
        include_str!("memory_fixtures/outside-frame.smt2"),
    ),
];

#[test]
fn frontend_calling_frame_terms_retain_checked_native_refutations() {
    let mut failures = Vec::new();
    for (name, problem) in CASES {
        let mut context = ay_frontend::Context::new();
        for command in ay_frontend::parse(problem).unwrap() {
            context.process_command(&command).unwrap();
        }
        assert_eq!(context.assertions.len(), 1);
        let root = context.assertions[0];
        let negative = context.terms.mk_not_raw(root);
        let mut proof = Proof::new();
        let assume = proof.add_assume(root, None);
        let lemma =
            proof.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
        proof.add_resolution(vec![], root, assume, lemma);
        let result = crate::check_proof_strict(&proof, &context.terms);
        println!("frontend memory {name}: native={result:?}");
        if let Err(error) = result {
            failures.push(format!("{name}: {error:?}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
}

#[test]
fn frontend_calling_frame_spellings_have_complete_documents() -> TestResult {
    for (name, problem) in CASES {
        let mut context = ay_frontend::Context::new();
        for command in ay_frontend::parse(problem).unwrap() {
            context.process_command(&command).unwrap();
        }
        assert_eq!(context.assertions.len(), 1);
        let root = context.assertions[0];
        let rendered = AlethePrinter::new(&context.terms).format_term(root);
        let declarations = problem.split_once("(assert").unwrap().0;
        // This certificate is for the explicit canonical spelling. The
        // original authored spelling remains covered by the separate tests;
        // no equivalence bridge to that original source is assumed here.
        let normalized = format!("{declarations}(assert {rendered})\n(check-sat)\n");
        certificate(&format!("frontend-calling-frame-{name}"), &normalized)?;
    }
    Ok(())
}

#[test]
fn original_calling_frame_memory_queries_require_native_certificates() -> TestResult {
    let mut failures = Vec::new();
    for (name, problem) in CASES {
        let (context, root, negative) = original(problem)?;
        let mut proof = Proof::new();
        let assume = proof.add_assume(root, None);
        let lemma =
            proof.add_theory_lemma_with_kind("bv", vec![negative], TheoryLemmaKind::BvBitBlast);
        proof.add_resolution(vec![], root, assume, lemma);
        if let Err(error) = crate::check_proof_strict(&proof, &context.terms) {
            diagnose_refusal(name, &context.terms, root, negative);
            failures.push(format!("{name}: {error:?}"));
        }
    }
    assert!(failures.is_empty(), "{}", failures.join("\n"));
    Ok(())
}

#[test]
fn original_calling_frame_memory_queries_emit_complete_documents() -> TestResult {
    let mut failures = Vec::new();
    for (name, problem) in CASES {
        let (context, root, negative) = original(problem)?;
        if AlethePrinter::new(&context.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none()
        {
            diagnose_refusal(name, &context.terms, root, negative);
            failures.push(name);
        } else {
            certificate(&format!("calling-frame-{name}"), problem)?;
        }
    }
    assert!(
        failures.is_empty(),
        "missing complete documents: {failures:?}"
    );
    Ok(())
}

fn diagnose_refusal(name: &str, terms: &ay_core::TermStore, root: TermId, negative: TermId) {
    let printer = AlethePrinter::new(terms);
    let preflight = source::preflight(&printer, root).is_some();
    let disjoint = crate::checker::bv_bitblast::disjoint::Shape::recognize(terms, &[negative]);
    let mut proof = PackedProof::new(&printer, ProofId(7)).unwrap();
    let assumption = proof.fresh();
    proof
        .append(&format!(
            "(assume {assumption} {})\n",
            printer.format_term(root)
        ))
        .unwrap();
    let mut circuit = Circuit::new(&mut proof);
    let built = circuit.boolean(root, 0);
    let boolean = built.is_some();
    let mut refuted = false;
    if let Some((bit, equality)) = built {
        if let Some(unit) = circuit.proof.transport_unit(&equality, &assumption) {
            if circuit.input(vec![bit], unit).is_some() {
                refuted = circuit.refute().is_some();
            }
        }
    }
    // Diagnostic reconstruction only. No emitted document or authority is
    // returned; a disjoint shape would need the separate original derivation.
    println!("memory refusal {name}: preflight={preflight} disjoint={} boolean={boolean} refuted={refuted} visited={} atoms={} clauses={} literals={} words={} addresses={} arrays={} bytes={} work={} exhausted={}",
        disjoint.is_some(), circuit.proof.visited, circuit.atoms.len(), circuit.clauses.len(),
        circuit.literals, circuit.words.len(), circuit.addresses.len(), circuit.arrays.len(),
        circuit.proof.out.len() + circuit.proof.definitions.len(), printer.work_used(),
        printer.work_budget_exhausted());
}
