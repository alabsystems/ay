// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::tests::{certificate, native, original, TestResult};
use super::*;

fn problem(width: u32, changed: bool, omit_guard: bool) -> String {
    let length = 40_u128;
    let mask = u128::MAX >> (128 - width);
    let bound = mask - length;
    let sep = if omit_guard {
        "true".to_owned()
    } else {
        format!("(or (bvule (bvadd output (_ bv40 {width})) (bvsub stack (_ bv16 {width}))) (bvuge output stack))")
    };
    let value = "output_value";
    let right_value = if changed { "wrong" } else { "output_value" };
    format!("(set-logic QF_ABV)
(declare-const stack (_ BitVec {width}))
(declare-const output (_ BitVec {width}))
(declare-const observe (_ BitVec {width}))
(declare-const value (_ BitVec 8))
(declare-const output_value (_ BitVec 8))
(declare-const wrong (_ BitVec 8))
(declare-const memory (Array (_ BitVec {width}) (_ BitVec 8)))
(assert (and {sep} (and (bvule output (_ bv{bound} {width}))
(and (bvuge stack (_ bv16 {width}))
(not (and
(= (select (store (store memory (bvsub stack (_ bv16 {width})) value) output {value}) (bvsub stack (_ bv16 {width}))) value)
(or (not (or (bvult observe (bvsub stack (_ bv16 {width}))) (bvuge observe stack)))
(= (select (store (store (store memory (bvsub stack (_ bv16 {width})) value) output {value}) output {value}) observe)
(select (store (store memory output {value}) output {right_value}) observe)))))))))
(check-sat)")
}

#[test]
fn common_output_writes_have_checked_original_certificates() -> TestResult {
    for width in [9, 64, 128] {
        let source = problem(width, false, false);
        assert!(native(&source)?, "native width={width}");
        certificate(&format!("common-output-{width}"), &source)?;
    }
    Ok(())
}

#[test]
fn changed_outputs_and_missing_separation_do_not_prove_preservation() -> TestResult {
    for (changed, omit_guard) in [(true, false), (false, true)] {
        let source = problem(9, changed, omit_guard);
        assert!(
            !native(&source)?,
            "changed={changed}, omitted separation={omit_guard}"
        );
        let (ctx, _, negative) = original(&source)?;
        assert!(AlethePrinter::new(&ctx.terms)
            .format_bv_circuit_refutation(ProofId(7), &[negative])
            .is_none());
    }
    Ok(())
}

// Malformed overwritten values are checked directly in the term-store tests;
// they are deliberately not accepted by the frontend parser used here.

fn full_range_problem(width: u32, offset: u32, protected: bool) -> String {
    let mask = u128::MAX >> (128 - width);
    let exclusive_bound = mask - 40;
    let last_bound = mask - 39;
    let mut source = problem(width, false, false).replace(
        &format!("(bvule output (_ bv{exclusive_bound} {width}))"),
        &format!("(bvule output (_ bv{last_bound} {width}))"),
    );
    if protected {
        let before =
            format!("(bvule (bvadd output (_ bv40 {width})) (bvsub stack (_ bv16 {width})))");
        source = source.replace(
            &before,
            &format!("(and (bvule output (_ bv{exclusive_bound} {width})) {before})"),
        );
    }
    source.replace(
        " output output_value)",
        &format!(" (bvadd output (_ bv{offset} {width})) output_value)"),
    )
}

#[test]
fn last_byte_ranges_with_guarded_exclusive_ends_have_checked_certificates() -> TestResult {
    for width in [9, 64, 128] {
        for offset in [0, 39] {
            let source = full_range_problem(width, offset, true);
            assert!(native(&source)?, "width={width}, offset={offset}");
            certificate(&format!("last-byte-{width}-{offset}"), &source)?;
        }
    }
    Ok(())
}

#[test]
fn wrapped_exclusive_ends_and_crossing_accesses_do_not_prove_separation() -> TestResult {
    let unprotected = full_range_problem(9, 0, false);
    let crossing = full_range_problem(9, 39, true)
        .replace("(bvule output (_ bv472 9))", "(bvule output (_ bv473 9))");
    let swapped = full_range_problem(9, 39, true).replace(
        "(select (store (store memory (bvadd output (_ bv39 9)) output_value) (bvadd output (_ bv39 9)) output_value) observe)",
        "(select (store (store memory (bvadd output (_ bv39 9)) output_value) (bvadd output (_ bv39 9)) wrong) observe)");
    assert_ne!(swapped, full_range_problem(9, 39, true));
    for (name, source) in [
        ("wrapped-end", unprotected),
        ("crossing-access", crossing),
        ("changed-result", swapped),
    ] {
        assert!(!native(&source)?, "{name}");
        let (context, _, negative) = original(&source)?;
        assert!(
            AlethePrinter::new(&context.terms)
                .format_bv_circuit_refutation(ProofId(7), &[negative])
                .is_none(),
            "{name}"
        );
    }
    Ok(())
}

#[test]
fn original_full_last_byte_output_query_has_checked_certificate() -> TestResult {
    let source = include_str!("../fixtures/output_memory_full_range.smt2");
    assert!(native(source)?, "original 64-bit output-buffer query");
    certificate("original-output-full-range", source)?;
    Ok(())
}
