// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn source_copies_preserve_wide_const_array_keys_without_expanding_legacy_admission() {
    let token = CancellationToken::new();
    for width in [129, 136, crate::MAX_BITVECTOR_WIDTH] {
        let key = ChcSort::BitVec(width);
        let value = ChcExpr::const_array(key.clone(), ChcExpr::BitVec(7, 8));
        let live = control(&token);
        assert!(!supported_sort(&key));
        assert!(copyable_const_key(&key));
        preflight(&value, &live, &mut 0).unwrap();
        assert_eq!(copy_term(&value, 0, &live), Some(value.clone()));
        let i = binder("i", 64);
        let term = ChcExpr::BitVec(0, 64);
        assert_eq!(simultaneous(&value, &[(&i, &term)], &live), Some(value));
    }
    for width in [0, crate::MAX_BITVECTOR_WIDTH + 1, u32::MAX] {
        let bad = ChcExpr::const_array(ChcSort::BitVec(width), ChcExpr::BitVec(0, 8));
        assert!(preflight(&bad, &control(&token), &mut 0).is_none());
        assert!(copy_term(&bad, 0, &control(&token)).is_none());
    }
}

#[test]
fn wide_const_key_payload_is_charged_before_copy_and_refusal_is_sticky() {
    let token = CancellationToken::new();
    let key = ChcSort::BitVec(crate::MAX_BITVECTOR_WIDTH);
    let value = ChcExpr::const_array(key, ChcExpr::BitVec(0, 8));
    let short = control(&token);
    short.bytes(MAX_COPY_BYTES - 128).unwrap();
    // Two nodes alone fit exactly; the additional key-width payload does not.
    assert!(copy_term(&value, 0, &short).is_none());
    assert!(short.poll().is_none());
    assert!(copy_term(&ChcExpr::Bool(true), 0, &short).is_none());
    let short_preflight = control(&token);
    short_preflight.bytes(MAX_COPY_BYTES - 1024).unwrap();
    assert!(preflight(&value, &short_preflight, &mut 0).is_none());
    assert!(short_preflight.poll().is_none());
    assert_eq!(copy_term(&value, 0, &control(&token)), Some(value));
}

#[test]
fn wide_source_terms_do_not_authorize_wide_direct_premise_binders() {
    let token = CancellationToken::new();
    let wide = binder("i", 136);
    let term = ChcExpr::BitVec(0, 136);
    assert!(simultaneous(
        &ChcExpr::var(wide.clone()),
        &[(&wide, &term)],
        &control(&token)
    )
    .is_none());
    let stopped = control(&token);
    token.cancel();
    let value = ChcExpr::const_array(ChcSort::BitVec(136), ChcExpr::BitVec(0, 8));
    assert!(copy_term(&value, 0, &stopped).is_none());
    token.reset();
    assert!(copy_term(&value, 0, &stopped).is_none());
    assert_eq!(copy_term(&value, 0, &control(&token)), Some(value));
}
