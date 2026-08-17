// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Textually included by `tests_globals` to preserve test FQNs.

// --- Declarations field tests ---

#[test]
fn test_declarations_field_no_check_sat() {
    let r = translate_fzn(
        "var int: x;\nvar int: y;\n\
         constraint int_eq(x, y);\nsolve satisfy;\n",
    );
    // declarations should NOT contain check-sat or get-value
    assert!(!r.declarations.contains("(check-sat)"));
    assert!(!r.declarations.contains("(get-value"));
    // but smtlib should
    assert!(r.smtlib.contains("(check-sat)"));
    assert!(r.smtlib.contains("(get-value"));
}

#[test]
fn test_smt_var_names_populated() {
    let r = translate_fzn("var int: x;\nvar int: y;\nsolve satisfy;\n");
    assert!(r.smt_var_names.contains(&"x".to_string()));
    assert!(r.smt_var_names.contains(&"y".to_string()));
}

#[test]
fn test_smt_var_names_includes_array_elements() {
    let r = translate_fzn("array [1..3] of var 1..5: q;\nsolve satisfy;\n");
    assert!(r.smt_var_names.contains(&"q_1".to_string()));
    assert!(r.smt_var_names.contains(&"q_2".to_string()));
    assert!(r.smt_var_names.contains(&"q_3".to_string()));
}

// --- Global: regular ---

#[test]
fn test_regular_simple_dfa() {
    // DFA: 2 states, alphabet {1, 2}, accepts strings ending in '1'
    // State 1: initial. On '1' → state 2, on '2' → state 1.
    // State 2: accepting. On '1' → state 2, on '2' → state 1.
    // Transition table (flat): [2, 1, 2, 1] (state1_sym1=2, state1_sym2=1, state2_sym1=2, state2_sym2=1)
    let r = translate_fzn(
        "array [1..2] of var 1..2: x;\n\
         constraint fzn_regular(x, 2, 2, [2, 1, 2, 1], 1, {2});\n\
         solve satisfy;\n",
    );
    // Should have layered Boolean variables
    assert!(r.smtlib.contains("(declare-const _reg0_0_1 Bool)"));
    assert!(r.smtlib.contains("(declare-const _reg0_0_2 Bool)"));
    // Initial state: state 1 is true, state 2 is false
    assert!(r.smtlib.contains("(assert _reg0_0_1)"));
    assert!(r.smtlib.contains("(assert (not _reg0_0_2))"));
    // Accepting: final layer, state 2 must be true
    assert!(r.smtlib.contains("(assert _reg0_2_2)"));
}

#[test]
fn test_regular_three_state_dfa() {
    // DFA: 3 states, alphabet {1, 2}, accepts if we reach state 3
    // Transition: s1+a1→s2, s1+a2→s1, s2+a1→s3, s2+a2→s1, s3+a1→s3, s3+a2→s3
    // Flat: [2, 1, 3, 1, 3, 3]
    let r = translate_fzn(
        "array [1..3] of var 1..2: x;\n\
         constraint regular(x, 3, 2, [2, 1, 3, 1, 3, 3], 1, {3});\n\
         solve satisfy;\n",
    );
    // Should have 4 layers (0..3) × 3 states
    assert!(r.smtlib.contains("(declare-const _reg0_3_3 Bool)"));
    // Accepting condition
    assert!(r.smtlib.contains("(assert _reg0_3_3)"));
}

#[test]
fn test_regular_empty_word_still_enforces_acceptance() {
    let r = translate_fzn(
        "array [1..0] of var 1..2: x;\n\
         constraint regular(x, 2, 1, [1, 2], 1, {2});\n\
         solve satisfy;\n",
    );
    assert!(r.smtlib.contains("(assert _reg0_0_1)"));
    assert!(r.smtlib.contains("(assert _reg0_0_2)"));
}

#[test]
fn test_regular_rejects_invalid_state_references() {
    let bad_initial = translate_fzn_err(
        "array [1..1] of var 1..1: x;\n\
         constraint regular(x, 2, 1, [1, 2], 3, {1});\n\
         solve satisfy;\n",
    );
    assert!(bad_initial.to_string().contains("initial state 3"));

    let bad_transition = translate_fzn_err(
        "array [1..1] of var 1..1: x;\n\
         constraint regular(x, 2, 1, [1, 3], 1, {1});\n\
         solve satisfy;\n",
    );
    assert!(bad_transition
        .to_string()
        .contains("transition destination 3"));

    let bad_accepting = translate_fzn_err(
        "array [1..1] of var 1..1: x;\n\
         constraint regular(x, 2, 1, [1, 2], 1, {3});\n\
         solve satisfy;\n",
    );
    assert!(bad_accepting.to_string().contains("accepting state 3"));
}
