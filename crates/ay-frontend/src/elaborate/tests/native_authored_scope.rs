// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;
use crate::command::Term as Parsed;

fn marker() -> Parsed {
    Parsed::Symbol(NATIVE_API_ASSERTION_PLACEHOLDER.to_owned())
}

#[test]
fn native_source_keeps_repeated_roots_without_parsed_retention() {
    let mut ctx = Context::new();
    ctx.set_retain_parsed_assertions(false);
    let root = ctx.terms.true_term();
    ctx.add_native_assertion_with_parsed(root, marker());
    ctx.add_native_assertion_with_parsed(root, marker());
    assert!(ctx.assertions_parsed.is_empty());
    assert_eq!(
        ctx.native_authored_assertion_terms_aligned_bounded(2),
        Some(vec![root, root])
    );
    assert!(ctx
        .native_authored_assertion_terms_aligned_bounded(1)
        .is_none());
}

#[test]
fn native_origin_does_not_depend_on_retained_marker_spelling() {
    let mut ctx = Context::new();
    let root = ctx.terms.true_term();
    ctx.add_native_assertion_with_parsed(root, Parsed::Const(crate::command::Constant::True));
    assert_eq!(
        ctx.native_authored_assertion_terms_aligned_bounded(1),
        Some(vec![root])
    );
}

#[test]
fn text_marker_and_mixed_rows_never_gain_native_origin() {
    let mut ctx = Context::new();
    let root = ctx.terms.true_term();
    ctx.add_assertion_with_parsed(root, marker());
    assert!(ctx
        .native_authored_assertion_terms_aligned_bounded(2)
        .is_none());
    assert_eq!(
        ctx.native_assertion_surfaces_for(&[root], 2, &mut |_| true),
        Some(NativeAssertionSurfaces::Unavailable)
    );
    ctx.add_native_assertion_with_parsed(root, marker());
    assert!(ctx
        .native_authored_assertion_terms_aligned_bounded(2)
        .is_none());
    assert_eq!(
        ctx.native_assertion_surfaces_for(&[root, root], 2, &mut |_| true),
        Some(NativeAssertionSurfaces::Unavailable)
    );
}

#[test]
fn parsed_text_assertion_does_not_gain_native_origin() {
    let mut ctx = Context::new();
    for command in parse("(assert true)").unwrap() {
        ctx.process_command(&command).unwrap();
    }
    assert!(ctx
        .native_authored_assertion_terms_aligned_bounded(1)
        .is_none());
}

#[test]
fn transient_or_reordered_working_rows_cannot_authenticate_source() {
    let mut ctx = Context::new();
    let a = ctx.terms.true_term();
    let b = ctx.terms.false_term();
    ctx.add_native_assertion_with_parsed(a, marker());
    ctx.add_native_assertion_with_parsed(b, marker());
    ctx.assertions.swap(0, 1);
    assert!(ctx
        .native_authored_assertion_terms_aligned_bounded(3)
        .is_none());
    ctx.assertions.swap(0, 1);
    ctx.add_transient_assertion_with_parsed(a, marker());
    assert!(ctx
        .native_authored_assertion_terms_aligned_bounded(3)
        .is_none());
    ctx.truncate_assertions(2);
    assert_eq!(
        ctx.native_authored_assertion_terms_aligned_bounded(2),
        Some(vec![a, b])
    );
}

#[test]
fn popped_text_scope_restores_native_source_inventory() {
    let mut ctx = Context::new();
    let root = ctx.terms.true_term();
    ctx.add_native_assertion_with_parsed(root, marker());
    ctx.process_command(&crate::Command::Push(1)).unwrap();
    ctx.add_assertion_with_parsed(root, marker());
    assert!(ctx
        .native_authored_assertion_terms_aligned_bounded(2)
        .is_none());
    ctx.process_command(&crate::Command::Pop(1)).unwrap();
    assert_eq!(
        ctx.native_authored_assertion_terms_aligned_bounded(1),
        Some(vec![root])
    );
}

#[test]
fn frozen_native_original_comparison_ignores_working_rewrites_and_preserves_occurrences() {
    let mut ctx = Context::new();
    ctx.set_retain_parsed_assertions(false);
    let a = ctx.terms.true_term();
    let b = ctx.terms.false_term();
    for root in [a, b, a] {
        ctx.add_native_assertion_with_parsed(root, marker());
    }
    ctx.assertions.clear();
    ctx.assertions.push(b);
    assert!(ctx.native_authored_originals_match_bounded(&[a, b, a], 3));
    for expected in [&[b, a, a][..], &[a, b][..], &[a, b, a, a][..], &[][..]] {
        assert!(!ctx.native_authored_originals_match_bounded(expected, 4));
    }
    assert!(!ctx.native_authored_originals_match_bounded(&[a, b, a], 2));
    ctx.add_assertion_with_parsed(a, marker());
    assert!(!ctx.native_authored_originals_match_bounded(&[a, b, a, a], 4));

    let mut text = Context::new();
    text.add_assertion_with_parsed(a, marker());
    assert!(!text.native_authored_originals_match_bounded(&[a], 1));
}
