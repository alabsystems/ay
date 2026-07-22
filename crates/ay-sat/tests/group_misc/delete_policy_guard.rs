// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

fn function_body<'a>(source: &'a str, signature: &str) -> &'a str {
    let start = source
        .find(signature)
        .unwrap_or_else(|| panic!("function `{signature}` must exist"));
    let open_brace = source[start..]
        .find('{')
        .map(|offset| start + offset)
        .expect("function opening brace must exist");

    let mut depth = 0usize;
    for (offset, ch) in source[open_brace..].char_indices() {
        match ch {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    let close_brace = open_brace + offset;
                    return &source[open_brace + 1..close_brace];
                }
            }
            _ => {}
        }
    }

    panic!("function `{signature}` closing brace must exist");
}

#[test]
fn bce_and_condition_use_shared_delete_policy() {
    // BCE: must use delete_clause_with_snapshot exclusively.
    // After the reschedule-wrapper refactoring, the deletion logic lives in
    // bce_body(), not the public bce() wrapper.
    let bce_body = function_body(
        include_str!("../../src/solver/inprocessing/bce.rs"),
        "fn bce_body(&mut self) {",
    );
    assert!(
        bce_body.contains("self.delete_clause_with_snapshot(")
            && bce_body.contains("ReasonPolicy::Skip"),
        "bce must use delete_clause_with_snapshot with ReasonPolicy::Skip \
         for unified gate-snapshot-delete safety contract",
    );
    assert!(
        !bce_body.contains("delete_clause_checked("),
        "bce must not bypass delete_clause_with_snapshot via direct delete_clause_checked calls",
    );

    // Condition: eliminated clauses must use delete_clause_with_snapshot;
    // root-satisfied GC may use delete_clause_checked with ClearLevel0 (#5052).
    // condition() delegates to condition_body() which contains the actual logic.
    let cond_body = function_body(
        include_str!("../../src/solver/inprocessing/condition.rs"),
        "fn condition_body(&mut self) {",
    );
    assert!(
        cond_body.contains("self.delete_clause_with_snapshot(")
            && cond_body.contains("ReasonPolicy::Skip"),
        "condition must use delete_clause_with_snapshot with ReasonPolicy::Skip \
         for eliminated clauses",
    );
    // Root-satisfied GC uses delete_clause_checked with ClearLevel0 — that's
    // legitimate because root-level assignments are permanent and no
    // reconstruction entry is needed. Verify the pairing is correct.
    for line in cond_body.lines() {
        if line.contains("delete_clause_checked(") {
            assert!(
                line.contains("ReasonPolicy::ClearLevel0"),
                "condition: any delete_clause_checked call must use ReasonPolicy::ClearLevel0 \
                 (root-satisfied GC only), found: {line}",
            );
        }
    }
}
