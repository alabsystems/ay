// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Regression tests for the `sv = ""` wrong-model bug on `(= sv "xyz")`
//! (#str-eq-literal-model-binding).
//!
//! Root cause: `inline_determined_string_vars` (strings_eval.rs), invoked at
//! the top of `check_sat` whenever the formula has strings, substituted a
//! literal-pinned variable `v := "lit"` into EVERY assertion — including the
//! defining equality itself, collapsing `(= sv "xyz")` to `(= "xyz" "xyz")`.
//! `sv` then no longer occurred anywhere: the string theory never bound it,
//! model validation ran on assertions that no longer mentioned it, and both
//! `(get-model)` and `(get-value)` fell through to the unconstrained-String
//! printer default `""` — a model violating the user's own assertion.
//!
//! The fix keeps the defining equality verbatim (and re-asserts a binding
//! mined from a nested conjunct or a `(= (str.len v) 0)` derivation), so the
//! solver genuinely binds the variable and the emitted witness is the
//! asserted literal.

/// The original minimal repro: `(= sv "xyz")` must model `sv` as `"xyz"`
/// in both get-model and get-value — never the empty string.
#[test]
fn test_eq_literal_binds_model_value() {
    let smt = r#"
(set-logic ALL)
(declare-const sv String)
(assert (= sv "xyz"))
(check-sat)
(get-model)
(get-value (sv))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    assert!(
        output.contains(r#"(define-fun sv () String "xyz")"#),
        "get-model must bind sv to the asserted literal \"xyz\": {output}"
    );
    assert!(
        output.contains(r#"((sv "xyz"))"#),
        "get-value must report the asserted literal \"xyz\": {output}"
    );
}

/// Symmetric orientation `(= "xyz" sv)` must bind identically.
#[test]
fn test_eq_literal_symmetric_orientation() {
    let smt = r#"
(set-logic ALL)
(declare-const sv String)
(assert (= "xyz" sv))
(check-sat)
(get-value (sv))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    assert!(
        output.contains(r#"((sv "xyz"))"#),
        "get-value must report \"xyz\" for the symmetric equality: {output}"
    );
}

/// A binding mined from a NESTED `and` conjunct has no top-level defining
/// equality to preserve; the fix re-asserts it. The model must still bind
/// the literal.
#[test]
fn test_eq_literal_nested_conjunct_binding() {
    let smt = r#"
(set-logic ALL)
(declare-const sv String)
(assert (and (= sv "abc") (str.prefixof "a" sv)))
(check-sat)
(get-value (sv))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    assert!(
        output.contains(r#"((sv "abc"))"#),
        "nested-conjunct binding must survive inlining: {output}"
    );
}

/// A pinned variable feeding a concat: both the pinned variable and the
/// derived one must have correct, consistent model values (before the fix:
/// `a = ""` while `b = "xy"` — mutually inconsistent with `(= b (str.++ a "y"))`).
#[test]
fn test_eq_literal_chained_concat_values() {
    let smt = r#"
(set-logic ALL)
(declare-const a String)
(declare-const b String)
(assert (= a "x"))
(assert (= b (str.++ a "y")))
(check-sat)
(get-value (a b))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    assert!(
        output.contains(r#"((a "x") (b "xy"))"#),
        "pinned var and derived concat must both be correct: {output}"
    );
}

/// A live string predicate alongside the pinned equality: `sv` must satisfy
/// BOTH (before the fix it reported `sv = ""`, violating both conjuncts).
#[test]
fn test_eq_literal_with_live_contains() {
    let smt = r#"
(set-logic ALL)
(declare-const sv String)
(assert (= sv "xyz"))
(assert (str.contains sv "y"))
(check-sat)
(get-value (sv))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    assert!(
        output.contains(r#"((sv "xyz"))"#),
        "pinned value must satisfy the live contains constraint: {output}"
    );
}

/// The contradiction twin must stay refuted: pinning must never make a
/// conflicting predicate satisfiable.
#[test]
fn test_eq_literal_conflicting_contains_not_sat() {
    let smt = r#"
(set-logic ALL)
(declare-const sv String)
(assert (= sv "xyz"))
(assert (str.contains sv "q"))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert_ne!(
        crate::common::sat_result(&output),
        Some("sat"),
        "\"xyz\" does not contain \"q\": {output}"
    );
}

/// Motivating case for the inlining pass (#mix-str2int-array-index): the
/// retained defining equality must NOT stop the substitution from grounding
/// `(str.to_int s)` — the contradictory array reads must still be refuted.
#[test]
fn test_mix_str2int_array_index_still_refuted() {
    let smt = r#"
(set-logic ALL)
(declare-const s String)
(declare-const a (Array Int Int))
(assert (= s ""))
(assert (= (select a (str.to_int s)) 5))
(assert (= (select a (- 1)) 6))
(check-sat)
"#;
    let output = crate::common::solve(smt);
    assert_eq!(
        crate::common::sat_result(&output),
        Some("unsat"),
        "str.to_int grounding through the inlined literal must refute the \
         conflicting array reads: {output}"
    );
}

/// `(= (str.len sv) 0)` derives the binding `sv := ""` (Case 2 of the
/// inlining pass); the emitted model must be the (genuinely valid) empty
/// string in both outputs.
#[test]
fn test_len_zero_binding_models_empty() {
    let smt = r#"
(set-logic ALL)
(declare-const sv String)
(assert (= (str.len sv) 0))
(check-sat)
(get-value (sv))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    assert!(
        output.contains(r#"((sv ""))"#),
        "len-0 binding must model the empty string: {output}"
    );
}

/// Sibling-variable materialization on the witness-accept path
/// (#str-witness-sibling-len): when one variable is decided by the
/// prefix/suffix witness pre-pass, a SECOND variable constrained only via its
/// `str.len` LIA proxy must still be materialized to a length-correct
/// witness. Before the fix the accept path validated at `pivot_enum_depth >
/// 0` where `materialize_string_witnesses` is a no-op, and the model printed
/// the default `""` (length 0), violating `(= (str.len s1) 2)`.
#[test]
fn test_witness_accept_materializes_sibling_len_var() {
    let smt = r#"
(set-logic ALL)
(declare-const s0 String)
(declare-const s1 String)
(assert (str.prefixof "xyz" s0))
(assert (= (str.len s1) 2))
(check-sat)
(get-value (s1))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    let value = extract_string_value(&output, "s1");
    assert_eq!(
        value.chars().count(),
        2,
        "s1 must be a length-2 witness, got {value:?}: {output}"
    );
}

/// Same shape with a suffix witness and a third unconstrained variable.
#[test]
fn test_witness_accept_materializes_sibling_len_var_suffix() {
    let smt = r#"
(set-logic ALL)
(declare-const s0 String)
(declare-const s1 String)
(declare-const s2 String)
(assert (str.suffixof "yz" s1))
(assert (= (str.len s2) 2))
(check-sat)
(get-value (s2))
"#;
    let output = crate::common::solve(smt);
    assert_eq!(crate::common::sat_result(&output), Some("sat"), "{output}");
    let value = extract_string_value(&output, "s2");
    assert_eq!(
        value.chars().count(),
        2,
        "s2 must be a length-2 witness, got {value:?}: {output}"
    );
}

/// Extract the quoted string value reported for `var` in a get-value line
/// like `((s1 "aa"))`. Panics (failing the test) when the pair is missing.
fn extract_string_value(output: &str, var: &str) -> String {
    let needle = format!("(({var} \"");
    let start = output
        .find(&needle)
        .unwrap_or_else(|| panic!("no get-value pair for {var} in: {output}"))
        + needle.len();
    let rest = &output[start..];
    let end = rest
        .find('"')
        .unwrap_or_else(|| panic!("unterminated string value for {var} in: {output}"));
    rest[..end].to_string()
}

/// Incremental push/pop around a pinned variable: the binding must survive
/// repeated check-sat calls (the inlining rewrites `ctx.assertions` in
/// place, so idempotency across solves matters).
#[test]
fn test_eq_literal_incremental_stability() {
    let smt = r#"
(set-logic ALL)
(declare-const sv String)
(assert (= sv "xyz"))
(check-sat)
(get-value (sv))
(push 1)
(declare-const t String)
(assert (= t (str.++ sv "w")))
(check-sat)
(get-value (sv t))
(pop 1)
(check-sat)
(get-value (sv))
"#;
    let output = crate::common::solve(smt);
    let sats = output.lines().filter(|l| l.trim() == "sat").count();
    assert_eq!(sats, 3, "all three check-sat calls must be sat: {output}");
    assert_eq!(
        output.matches(r#"((sv "xyz"))"#).count(),
        2,
        "sv must stay \"xyz\" across push/pop: {output}"
    );
    assert!(
        output.contains(r#"((sv "xyz") (t "xyzw"))"#),
        "pushed derived value must be consistent with the pinned one: {output}"
    );
}
