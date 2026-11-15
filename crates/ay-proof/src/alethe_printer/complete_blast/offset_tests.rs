// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The complete bit-blast bridges an offset equality as the circuit lane
//! does, from the solver's own (canonical) assertion.

use super::*;

/// external-codegen's lowered coroutine-slot query at two bytes.
const SLOT: &str = include_str!("../bv_packed/fixtures/coro-slot-2.smt2");
/// The same query with a separation guard one byte short: satisfiable.
const SLOT_SHORT: &str = include_str!("../bv_packed/fixtures/coro-slot-2-short.smt2");

fn lemma(problem: &str) -> (ay_frontend::Context, TermId, TermId) {
    let mut context = ay_frontend::Context::new();
    for command in ay_frontend::parse(problem).expect("fixture parses") {
        context
            .process_command(&command)
            .expect("fixture elaborates");
    }
    let root = context.assertions[0];
    let negative = context.terms.mk_not_raw(root);
    (context, root, negative)
}

#[test]
fn the_slot_lemma_prints_through_the_shared_difference() {
    let (context, root, negative) = lemma(SLOT);
    let printer = AlethePrinter::new(&context.terms);
    let text = printer
        .format_bv_complete_blast_refutation(ProofId(1), &[negative])
        .expect("the slot lemma prints");
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    assert!(
        text.contains(":rule poly_simp_rel"),
        "the atoms are bridged"
    );
    assert_eq!(
        text.matches("(bvadd vbase (bvneg frame))").count(),
        1,
        "one subtractor serves every atom over the pair"
    );
    // The lemma is over the solver's canonical assertion, so the replayed
    // problem asserts that assertion as it prints.
    let asserted = printer.format_term(root);
    let declarations: Vec<&str> = SLOT
        .lines()
        .filter(|line| line.starts_with("(set-logic") || line.starts_with("(declare-const"))
        .collect();
    let problem = format!(
        "{}\n(assert {asserted})\n(check-sat)\n",
        declarations.join("\n")
    );
    let proof = format!(
        "(assume a {asserted})\n{text}(step done (cl) :rule resolution :premises (a t1))\n"
    );
    let path = std::env::temp_dir().join(format!(
        "ay-complete-blast-offset-slot-2-{}.json",
        std::process::id()
    ));
    let certificate = serde_json::json!({
        "type": "alethe_certificate",
        "version": "1.0",
        "problem": problem,
        "proof": proof,
    });
    std::fs::write(&path, certificate.to_string()).expect("certificate written");
    println!("independent replay certificate: {}", path.display());
}

#[test]
fn an_overlapping_slot_is_not_refuted() {
    let (context, _, negative) = lemma(SLOT_SHORT);
    let printer = AlethePrinter::new(&context.terms);
    assert!(printer
        .format_bv_complete_blast_refutation(ProofId(1), &[negative])
        .is_none());
}
