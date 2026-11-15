// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The circuit lane refutes a root the exporter spells as authored.
//!
//! The exporter assumes a folded assertion as written, so the whole-query
//! lemma's root prints with the problem's `(_ bvN W)` literals while this lane
//! spells them in binary (`literal_spelling`). Before the lane compared the two
//! up to literal spelling it declined every such root, and external-codegen's 128-bit
//! arithmetic theorems went to the complete bit-blast (`SubU128`: 83.5 MB in
//! 30-60 s where this lane prints 18.9 MB). The shape below is theirs in
//! miniature: a carried sum against its low byte, `(= true ..)` around the
//! claim.

use super::tests::{original, TestResult};
use super::*;

const AUTHORED: &str = "(and (= s (bvadd (concat x y) (_ bv1 16))) (and (= m (bvadd y (_ bv1 8))) (not (= true (= ((_ extract 7 0) s) m)))))";

fn problem(assertion: &str) -> String {
    format!(
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n(declare-const y (_ BitVec 8))\n\
         (declare-const s (_ BitVec 16))\n(declare-const m (_ BitVec 8))\n(assert {assertion})\n\
         (check-sat)\n"
    )
}

fn refuted_under(spelling: &str) -> TestResult<Option<String>> {
    let (context, root, negative) = original(&problem(AUTHORED))?;
    let mut overrides = DetHashMap::default();
    overrides.insert(root, spelling.to_string());
    let printer = AlethePrinter::new_with_overrides(&context.terms, Some(&overrides));
    assert_eq!(
        printer.format_term(root),
        spelling,
        "the root prints as given"
    );
    Ok(printer.format_bv_circuit_refutation(ProofId(7), &[negative]))
}

#[test]
fn a_root_spelled_as_authored_is_refuted() -> TestResult {
    let (context, root, negative) = original(&problem(AUTHORED))?;
    let canonical = AlethePrinter::new(&context.terms);
    assert!(
        canonical.format_term(root).contains("#b0000000000000001"),
        "the lane's own spelling of the literals is binary"
    );
    assert!(canonical
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_some());
    let text = refuted_under(AUTHORED)?.ok_or("the authored root is refuted")?;
    assert!(
        text.lines()
            .any(|line| line.starts_with("(assume ") && line.ends_with(&format!(" {AUTHORED})"))),
        "the hypothesis is the root as the exporter prints it"
    );
    assert!(!text.contains(":rule hole") && !text.contains(":rule trust"));
    Ok(())
}

/// NEGATIVE: only the spelling of a literal is forgiven. A root printed with
/// another value, another width or another term is never refuted on the
/// lane's word for it.
#[test]
fn a_root_printed_as_another_term_is_not_refuted() -> TestResult {
    for wrong in [
        AUTHORED.replace("(_ bv1 8)", "(_ bv2 8)"),
        AUTHORED.replace("(_ bv1 16)", "(_ bv1 17)"),
        AUTHORED.replace("(bvadd y", "(bvsub y"),
    ] {
        assert!(refuted_under(&wrong)?.is_none(), "{wrong}");
    }
    Ok(())
}
