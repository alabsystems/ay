// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

// ========== get-assertions tests ==========

#[test]
fn test_get_assertions_empty() {
    let input = r#"
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert_eq!(outputs[0], "()");
}

#[test]
fn test_get_assertions_single() {
    let input = r#"
        (declare-const a Bool)
        (assert a)
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains('a'),
        "Expected assertion 'a': {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_multiple() {
    let input = r#"
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (assert (not b))
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains('a'),
        "Expected assertion 'a': {}",
        outputs[0]
    );
    assert!(
        outputs[0].contains("not"),
        "Expected 'not' in assertions: {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_with_compound() {
    let input = r#"
        (declare-const x Bool)
        (declare-const y Bool)
        (assert (and x y))
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("and"),
        "Expected 'and' in assertions: {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_with_euf() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains('='),
        "Expected '=' in assertions: {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_requotes_symbols_with_colons() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const |foo::bar| Int)
        (assert (= |foo::bar| 0))
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    assert!(
        outputs[0].contains("|foo::bar|"),
        "Expected quoted symbol in assertions: {}",
        outputs[0]
    );

    let sexp = parse_sexp(&outputs[0]).unwrap();
    let SExpr::List(ref items) = sexp else {
        panic!("Expected assertions list, got: {sexp:?}");
    };
    assert_eq!(items.len(), 1);
    let SExpr::List(assertion) = &items[0] else {
        panic!("Expected assertion term list, got: {items:?}");
    };
    assert_eq!(assertion.len(), 3, "Assertion: {assertion:?}");
    assert!(matches!(&assertion[0], SExpr::Symbol(s) if s == "="));
    assert!(matches!(&assertion[1], SExpr::Symbol(s) if s == "foo::bar"));
}

#[test]
fn test_get_assertions_after_push_pop() {
    let input = r#"
        (declare-const a Bool)
        (assert a)
        (push 1)
        (declare-const b Bool)
        (assert b)
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Both a and b should be in assertions
    assert!(
        outputs[0].contains('a'),
        "Expected assertion 'a': {}",
        outputs[0]
    );
    assert!(
        outputs[0].contains('b'),
        "Expected assertion 'b': {}",
        outputs[0]
    );
}

#[test]
fn test_get_assertions_after_pop() {
    let input = r#"
        (declare-const a Bool)
        (assert a)
        (push 1)
        (declare-const b Bool)
        (assert b)
        (pop 1)
        (get-assertions)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Only 'a' should remain after pop
    assert!(
        outputs[0].contains('a'),
        "Expected assertion 'a' to remain: {}",
        outputs[0]
    );
    // Check that the output only contains one assertion
    // (the "(a)" pattern should be the whole content)
    assert!(
        !outputs[0].contains('b'),
        "Did not expect 'b' after pop: {}",
        outputs[0]
    );
}

// ========== get-assignment Tests ==========

#[test]
fn test_get_assignment_not_enabled() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named my_assertion))
        (check-sat)
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    assert!(
        outputs[1].contains("error"),
        "Expected error about produce-assignments: {}",
        outputs[1]
    );
}

#[test]
fn test_get_assignment_enabled_sat() {
    let input = r#"
        (set-option :produce-assignments true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named my_assertion))
        (check-sat)
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Should contain assignment for my_assertion
    assert!(
        outputs[1].contains("my_assertion"),
        "Expected named term in assignment: {}",
        outputs[1]
    );
    // Since 'a' is asserted, my_assertion should be true
    assert!(
        outputs[1].contains("true"),
        "Expected true value: {}",
        outputs[1]
    );
}

#[test]
fn test_get_assignment_multiple_named() {
    let input = r#"
        (set-option :produce-assignments true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (! a :named a_holds))
        (assert (! (not b) :named not_b_holds))
        (check-sat)
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Both named terms should appear
    assert!(
        outputs[1].contains("a_holds"),
        "Expected a_holds: {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("not_b_holds"),
        "Expected not_b_holds: {}",
        outputs[1]
    );
}

#[test]
fn test_get_assignment_no_named_terms() {
    let input = r#"
        (set-option :produce-assignments true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat)
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Should return empty list since no named terms
    assert_eq!(outputs[1], "()");
}

#[test]
fn test_get_assignment_before_check_sat() {
    let input = r#"
        (set-option :produce-assignments true)
        (declare-const a Bool)
        (assert (! a :named my_a))
        (get-assignment)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 1);
    // Should return error since no check-sat yet
    assert!(
        outputs[0].contains("error"),
        "Expected error about unavailable assignment: {}",
        outputs[0]
    );
}

// ========== get-unsat-core Tests ==========

#[test]
fn test_get_unsat_core_not_enabled() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named pos_a))
        (assert (! (not a) :named neg_a))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(
        outputs[1].contains("error"),
        "Expected error about produce-unsat-cores: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_core_enabled() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named pos_a))
        (assert (! (not a) :named neg_a))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // SOUNDNESS: the returned core must itself be UNSAT. Here `a` and `(not a)`
    // contradict, so {neg_a} alone is satisfiable — a core of only one of them
    // is unsound. Both named assertions must be present. (Regression for the
    // unsound-unsat-core bug where only neg_a was returned.)
    assert!(
        outputs[1].contains("pos_a"),
        "core must contain pos_a (a is needed for UNSAT): {}",
        outputs[1]
    );
    assert!(
        outputs[1].contains("neg_a"),
        "core must contain neg_a ((not a) is needed for UNSAT): {}",
        outputs[1]
    );
}

/// SOUNDNESS + MINIMALITY self-check for unsat cores over EUF congruence — the
/// validation gate for an Unsat-Core track entry (P4): a returned core must
/// (a) EXCLUDE assertions irrelevant to the contradiction (minimality — not the
/// whole assertion set), and (b) be genuinely UNSAT when re-asserted in
/// ISOLATION ("never emit an unverified core"). Mirrors the differential check
/// against z3: for `a=b=c ∧ f(a)≠f(c)` plus two irrelevant assertions, AY
/// returns the minimal core `(A2 A1 A3)`, and that core re-checks UNSAT.
#[test]
fn test_unsat_core_euf_congruence_sound_and_minimal() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun c () U)
        (declare-fun d () U)
        (declare-fun f (U) U)
        (assert (! (= a b) :named A1))
        (assert (! (= b c) :named A2))
        (assert (! (not (= (f a) (f c))) :named A3))
        (assert (! (= a d) :named A4_irrelevant))
        (assert (! (= d d) :named A5_irrelevant))
        (check-sat)
        (get-unsat-core)
    "#;
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    let core = &outputs[1];
    // Soundness: the three assertions driving the congruence contradiction.
    for needed in ["A1", "A2", "A3"] {
        assert!(
            core.contains(needed),
            "core must contain {needed} (needed for UNSAT): {core}"
        );
    }
    // Minimality: irrelevant assertions must be excluded.
    for irrelevant in ["A4_irrelevant", "A5_irrelevant"] {
        assert!(
            !core.contains(irrelevant),
            "core must NOT contain {irrelevant} (irrelevant to UNSAT): {core}"
        );
    }

    // Self-check gate: re-assert ONLY the core members; the result must still be
    // UNSAT. A core that is SAT in isolation would be an unsound (DQ) answer.
    let core_only = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun a () U)
        (declare-fun b () U)
        (declare-fun c () U)
        (declare-fun f (U) U)
        (assert (= a b))
        (assert (= b c))
        (assert (not (= (f a) (f c))))
        (check-sat)
    "#;
    let core_commands = parse(core_only).unwrap();
    let mut core_exec = Executor::new();
    let core_outputs = core_exec.execute_all(&core_commands).unwrap();
    assert_eq!(
        core_outputs,
        vec!["unsat"],
        "re-asserted unsat core must be genuinely UNSAT (self-check gate)"
    );
}

/// SOUNDNESS regression: with a trivially-true named/unnamed assertion present,
/// the unsat-core redirect must still return a genuinely-UNSAT subset, not a
/// satisfiable singleton. Previously returned just (neg_a) which is SAT.
#[test]
fn test_get_unsat_core_with_tautology_present_is_genuinely_unsat() {
    // Unnamed trivially-true assertion `(or true false)`.
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named n1))
        (assert (! (not a) :named n2))
        (assert (or true false))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(
        outputs[1].contains("n1") && outputs[1].contains("n2"),
        "core must contain both n1 and n2 to be genuinely UNSAT: {}",
        outputs[1]
    );

    // Named tautology variant: `(! (or b (not b)) :named n3)`.
    let input2 = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert (! a :named n1))
        (assert (! (not a) :named n2))
        (assert (! (or b (not b)) :named n3))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands2 = parse(input2).unwrap();
    let mut exec2 = Executor::new();
    let outputs2 = exec2.execute_all(&commands2).unwrap();

    assert_eq!(outputs2.len(), 2);
    assert_eq!(outputs2[0], "unsat");
    assert!(
        outputs2[1].contains("n1") && outputs2[1].contains("n2"),
        "core must contain both n1 and n2 to be genuinely UNSAT: {}",
        outputs2[1]
    );
}

#[test]
fn test_get_unsat_core_after_sat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert (! a :named pos_a))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "sat");
    // Should return error since last result was not unsat
    assert!(
        outputs[1].contains("error"),
        "Expected error about unsat core not available: {}",
        outputs[1]
    );
}

#[test]
fn test_get_unsat_core_no_named_terms() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (assert (not a))
        (check-sat)
        (get-unsat-core)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    // Should return empty list since no named terms
    assert_eq!(outputs[1], "()");
}
