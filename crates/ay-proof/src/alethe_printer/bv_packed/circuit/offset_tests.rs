// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::tests::{certificate, original, TestResult};
use super::*;

/// external-codegen's lowered coroutine-slot query at two bytes: every loaded byte
/// is an `ite` chain over `(= (bvadd (bvadd 24 j) frame) (bvadd i vbase))`.
const SLOT: &str = include_str!("../fixtures/coro-slot-2.smt2");
/// The same query with a separation guard one byte short: satisfiable.
const SLOT_SHORT: &str = include_str!("../fixtures/coro-slot-2-short.smt2");

#[test]
fn the_slot_query_prints_one_shared_difference() -> TestResult {
    certificate("offset-slot-2", SLOT)?;
    let (context, _, negative) = original(SLOT)?;
    let printer = AlethePrinter::new(&context.terms);
    let text = printer
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .ok_or("the slot lemma prints")?;
    assert!(
        text.contains(":rule poly_simp_rel"),
        "every atom is bridged"
    );
    assert_eq!(
        text.matches("(bvsub (bvsub vbase frame) (_ bv").count(),
        text.matches(":rule poly_simp_rel").count(),
        "each bridge compares the ONE difference with its constant"
    );
    assert_eq!(
        text.matches("(cl (= (bvsub vbase frame) (bvadd vbase (bvneg frame))))")
            .count(),
        1,
        "the difference is re-spelled once"
    );
    Ok(())
}

#[test]
fn an_overlapping_slot_has_no_refutation() -> TestResult {
    let (context, _, negative) = original(SLOT_SHORT)?;
    let printer = AlethePrinter::new(&context.terms);
    assert!(printer
        .format_bv_circuit_refutation(ProofId(7), &[negative])
        .is_none());
    Ok(())
}
