// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! These are exact whole implications from a complete, guarded original trace.
//! Passing them is not a claim that the original 20-second solve is now Safe.

use super::*;
use sha2::{Digest, Sha256};

const SIX: &str = include_str!("clause6.smt2");
const TWELVE: &str = include_str!("clause12.smt2");

#[test]
fn r29_clause6_exact_capture_closes_constant_bits_and_array_congruence() {
    check_capture(
        SIX,
        15_709,
        "173a2faa84d0e4a8c7324453c8d908df87c10f71d08c445a797f38c7d337bd96",
        38,
        40,
    );
}

#[test]
fn r29_clause12_exact_capture_closes_boolean_false_equalities() {
    check_capture(
        TWELVE,
        32_295,
        "933e77eea5fc538e70fc743426b324b6477d4738a730bc3b749dc6d0204bf169",
        55,
        66,
    );
}

#[test]
#[should_panic(expected = "contains undeclared or differently typed variable")]
fn captured_fixture_cannot_infer_an_omitted_bitvector_as_integer() {
    let omitted = TWELVE
        .replace("  (obj_size_at_0x42_bv32 (_ BitVec 32))\n", "")
        .replace(
            " (_ BitVec 32) (Array (_ BitVec 32) Bool)))",
            " (Array (_ BitVec 32) Bool)))",
        );
    assert_ne!(omitted, TWELVE);
    original::parse(&omitted);
}

fn check_capture(text: &str, bytes: usize, hash: &str, body_len: usize, head_len: usize) {
    assert_eq!(text.len(), bytes);
    assert_eq!(format!("{:x}", Sha256::digest(text.as_bytes())), hash);
    for name in ["body", "head"] {
        let prefix = format!("; {name} expression SHA256 ");
        let expected = text
            .lines()
            .find_map(|line| line.strip_prefix(&prefix))
            .unwrap();
        let definition = text.find(&format!("(define-fun captured_{name}")).unwrap();
        let expression = text[definition..]
            .lines()
            .find(|line| line.starts_with("(and "))
            .unwrap();
        assert_eq!(
            format!("{:x}", Sha256::digest(expression.as_bytes())),
            expected
        );
    }
    let (body, head) = original::parse(text);
    let ChcExpr::Op(ChcOp::And, body_args) = &body else {
        panic!("captured body")
    };
    let ChcExpr::Op(ChcOp::And, head_args) = &head else {
        panic!("captured head")
    };
    assert_eq!(body_args.len(), body_len);
    assert_eq!(head_args.len(), head_len);
    assert_eq!(prove(&body, &head), Ok(true));
}

#[test]
fn captured_clause6_operand_width_and_array_default_mutations_decline() {
    let boundary = SIX.find("(define-fun captured_head").unwrap();
    let (prefix, head) = SIX.split_at(boundary);
    for (before, after) in [
        (
            "(concat (_ bv66 32) (_ bv0 32))",
            "(concat (_ bv67 32) (_ bv0 32))",
        ),
        ("(_ bv283467841536 64)", "(_ bv283467841536 63)"),
        (
            "((_ extract 31 0) (_ bv4 64))",
            "((_ extract 31 0) (_ bv5 64))",
        ),
        ("Bool)) true)", "Bool)) false)"),
    ] {
        let changed = format!("{prefix}{}", head.replacen(before, after, 1));
        assert_ne!(changed, SIX);
        // The malformed width remains a well-parsed expression; full typing,
        // not parser rejection or a changed source formula, must deny proof.
        let (body, head) = original::parse(&changed);
        assert_eq!(prove(&body, &head), Ok(false));
    }
}

#[test]
fn captured_clause12_boolean_polarity_mutation_declines() {
    let boundary = TWELVE.find("(define-fun captured_head").unwrap();
    let (prefix, head) = TWELVE.split_at(boundary);
    let name = "_testcrate_0::chc_std_alloc_realloc_grow_full_mem_bool_at_0x4200000000_bv64";
    let changed = format!(
        "{prefix}{}",
        head.replacen(&format!("(not {name})"), name, 1)
    );
    assert_ne!(changed, TWELVE);
    let (body, head) = original::parse(&changed);
    assert_eq!(prove(&body, &head), Ok(false));
}
