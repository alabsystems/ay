// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

/// Guard: `collect_sat_stats!` must remain a write-only snapshot with no
/// assertions. Any `debug_assert!` inside the macro expands at 28+ sites
/// with phase-ambiguous state, causing P1 panics (#4756, #4804).
///
/// This test reads the macro source and fails if `debug_assert` appears
/// between the macro_rules definition and its closing brace.
#[test]
fn test_collect_sat_stats_macro_contains_no_assertions() {
    let source = include_str!("../pipeline_setup_macros.rs");

    // Find the macro definition
    let macro_start = source
        .find("macro_rules! collect_sat_stats")
        .expect("collect_sat_stats! macro not found in pipeline_setup_macros.rs");

    // Find the matching closing brace: the macro ends with `};`
    // after the pattern body. We scan for the first `};` after start.
    let after_start = &source[macro_start..];
    let macro_end = after_start
        .find(";\n}")
        .expect("could not find end of collect_sat_stats! macro");

    let macro_body = &after_start[..macro_end];

    // Check for any assertion macro (assert!, debug_assert!, assert_eq!, etc.)
    for keyword in ["debug_assert", "assert!", "assert_eq!", "assert_ne!"] {
        assert!(
            !macro_body.contains(keyword),
            "GUARD VIOLATION: collect_sat_stats! macro must not contain `{keyword}`.\n\
             Phase-sensitive assertions belong in stats_contract.rs finalize helpers.\n\
             See: the development design notes\n\
             Macro body:\n{macro_body}"
        );
    }
}
