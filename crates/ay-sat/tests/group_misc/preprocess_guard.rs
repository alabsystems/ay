// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

fn preprocess_body(source: &str) -> &str {
    let signature = "pub(super) fn preprocess(&mut self) -> bool {";
    let start = source
        .find(signature)
        .expect("preprocess definition must exist");
    let open_brace = source[start..]
        .find('{')
        .map(|offset| start + offset)
        .expect("preprocess opening brace must exist");

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

    panic!("preprocess closing brace must exist");
}

#[test]
fn test_preprocess_propagate_checks_always_guard_empty_clause() {
    // The preprocess function uses `propagate_check_unsat()` which is defined as:
    //   self.has_empty_clause || self.search_propagate().is_some()
    // Verify that preprocess calls propagate_check_unsat (not raw search_propagate),
    // and that propagate_check_unsat itself includes the has_empty_clause guard.
    let config_source = include_str!("../../src/solver/config_preprocess.rs");
    let preprocess = preprocess_body(config_source);

    const CALL: &str = "self.propagate_check_unsat()";
    let calls = preprocess.match_indices(CALL).count();

    assert!(
        calls > 0,
        "expected preprocess to call propagate_check_unsat() at least once"
    );

    // Verify that propagate_check_unsat contains the has_empty_clause guard.
    // The function may use either short-circuit form or if-let form.
    let prop_source = include_str!("../../src/solver/propagation.rs");
    assert!(
        prop_source.contains("self.has_empty_clause || self.search_propagate().is_some()")
            || (prop_source.contains("self.has_empty_clause")
                && prop_source.contains("self.search_propagate()")),
        "propagate_check_unsat must include has_empty_clause guard"
    );

    // Ensure no raw search_propagate().is_some() calls exist in preprocess
    // (they should all go through propagate_check_unsat).
    assert!(
        !preprocess.contains("self.search_propagate().is_some()"),
        "preprocess must not use raw search_propagate().is_some() — use propagate_check_unsat()"
    );
}
