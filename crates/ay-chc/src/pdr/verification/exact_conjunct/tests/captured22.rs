// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact next original obligation after the clause6/12 congruence repair.
//! Passing this single implication is not whole-original R29 acceptance.

use super::*;
use ay_core::resource::{ChildSpec, Guard, NodeLabel};
use sha2::{Digest, Sha256};

const INPUT: &str = include_str!("clause22.smt2");

#[test]
fn r29_clause22_exact_capture_proves_constant_product_and_selected_ites() {
    assert_eq!(INPUT.len(), 36_680);
    assert_eq!(
        format!("{:x}", Sha256::digest(INPUT.as_bytes())),
        "7ced598d2527f8eb752e590432b5f908273f41dbb22683835e2c2a9f6ca98b86"
    );
    let expressions: Vec<_> = INPUT
        .lines()
        .filter(|line| line.starts_with("(and "))
        .collect();
    assert_eq!(expressions.len(), 2);
    for (expression, hash) in expressions.iter().zip([
        "55a9d923fb9f4df06de3aca2520a4bf8c14351b0058a1d2949e3dade4e90219f",
        "f0deff89c6a6ed10d8996df62e0d050525630d6213311fc0fc36612f6eb50131",
    ]) {
        assert_eq!(format!("{:x}", Sha256::digest(expression.as_bytes())), hash);
    }
    let (body, head) = original::parse(INPUT);
    let (ChcExpr::Op(ChcOp::And, body_args), ChcExpr::Op(ChcOp::And, head_args)) = (&body, &head)
    else {
        panic!("original conjunctions");
    };
    assert_eq!(body_args.len(), 69);
    assert_eq!(head_args.len(), 72);
    assert_eq!(prove(&body, &head), Ok(true));
}

#[test]
fn captured_clause22_changed_product_or_boolean_polarities_are_not_proved() {
    let offset = INPUT.find("(define-fun captured_head").unwrap();
    let (prefix, head) = INPUT.split_at(offset);
    for (before, after) in [
        (
            "(_ bv147573952589676412932 128)",
            "(_ bv147573952589676412933 128)",
        ),
        (
            " _testcrate_0::chc_std_alloc_realloc_grow_full_9_fld0 (=",
            " (not _testcrate_0::chc_std_alloc_realloc_grow_full_9_fld0) (=",
        ),
        // The tag-only change still implies the head: the alternate base is
        // nonzero in the premise. Select that arm AND negate its equality so
        // this is an independently checked SAT countermodel, not an assumed
        // negative based solely on different syntax.
        (
            concat!(
                "(ite (= ((_ extract 63 32) _testcrate_0::chc_std_alloc_realloc_grow_full_3) ",
                "(_ bv9 32)) (= _testcrate_0::chc_std_alloc_realloc_grow_full_5"
            ),
            concat!(
                "(ite (= ((_ extract 63 32) _testcrate_0::chc_std_alloc_realloc_grow_full_3) ",
                "(_ bv66 32)) (distinct _testcrate_0::chc_std_alloc_realloc_grow_full_5"
            ),
        ),
    ] {
        let changed = format!("{prefix}{}", head.replacen(before, after, 1));
        assert_ne!(changed, INPUT);
        let (body, head) = original::parse(&changed);
        assert_eq!(prove(&body, &head), Ok(false));
    }
}

#[test]
fn whole_clause22_has_one_deterministic_owner_without_renewing_short_credit() {
    let (body, head) = original::parse(INPUT);
    let generous = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(1_000_001)));
    let scope = generous.enter();
    assert_eq!(prove(&body, &head), Ok(true));
    let used = generous.ticks();
    assert!(used > 1 && used <= 1_000_000);
    drop(scope);
    let exact = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used + 1)));
    let scope = exact.enter();
    assert_eq!(prove(&body, &head), Ok(true));
    assert_eq!(exact.ticks(), used);
    drop(scope);
    let short = Guard::root_child(ChildSpec::new(NodeLabel::Check).with_rlimit(Some(used - 1)));
    let scope = short.enter();
    let mut owner = Owner::capture().unwrap();
    assert_eq!(entails(&body, &head, &mut owner), Err(Error::Resource));
    drop(scope);
    assert_eq!(entails(&body, &head, &mut owner), Err(Error::Resource));
}
