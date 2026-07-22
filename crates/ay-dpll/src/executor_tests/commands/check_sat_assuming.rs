// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn test_check_sat_assuming_sat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (check-sat-assuming (b))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // With a=true asserted and b assumed, should be SAT
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_check_sat_assuming_unsat() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat-assuming ((not a)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // With a=true asserted and (not a) assumed, should be UNSAT
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_check_sat_assuming_does_not_modify_stack() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (assert a)
        (check-sat-assuming ((not a)))
        (check-sat)
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // First check-sat-assuming with (not a) should be UNSAT
    // Second check-sat (without assumption) should be SAT
    assert_eq!(outputs, vec!["unsat", "sat"]);
}

#[test]
fn test_check_sat_assuming_multiple_assumptions() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (declare-const b Bool)
        (declare-const c Bool)
        (check-sat-assuming (a b c))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // All assumptions are satisfiable together
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_check_sat_assuming_contradictory_assumptions() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (check-sat-assuming (a (not a)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Contradictory assumptions should be UNSAT
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_check_sat_assuming_empty() {
    let input = r#"
        (set-logic QF_UF)
        (declare-const a Bool)
        (assert a)
        (check-sat-assuming ())
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Empty assumptions - equivalent to check-sat
    assert_eq!(outputs, vec!["sat"]);
}

#[test]
fn test_check_sat_assuming_euf() {
    let input = r#"
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (= a b))
        (check-sat-assuming ((distinct a b)))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // a=b asserted, (distinct a b) assumed should be UNSAT
    assert_eq!(outputs, vec!["unsat"]);
}

#[test]
fn test_check_sat_assuming_qf_nira_with_real_terms_returns_unknown() {
    let input = r#"
        (set-logic QF_NIRA)
        (declare-const x Real)
        (declare-const y Int)
        (check-sat-assuming ((= (* x x) (to_real y))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["unknown"]);
}

#[test]
fn test_check_sat_assuming_qf_seqbv_respects_all_assumptions_7656() {
    let input = r#"
        (set-logic QF_SEQBV)
        (declare-const s0 (Seq (_ BitVec 64)))
        (declare-const s1 (Seq (_ BitVec 64)))
        (check-sat-assuming (
            (= (seq.nth s0 0) (_ bv0 64))
            (= (seq.nth s0 0) (seq.nth s1 0))
        ))
        (check-sat-assuming (
            (= (seq.nth s0 0) (_ bv0 64))
            (not (= (seq.nth s1 0) (_ bv0 64)))
        ))
        (check-sat-assuming (
            (= (seq.nth s0 0) (seq.nth s1 0))
            (not (= (seq.nth s1 0) (_ bv0 64)))
        ))
        (check-sat-assuming (
            (= (seq.nth s0 0) (_ bv0 64))
            (= (seq.nth s0 0) (seq.nth s1 0))
            (not (= (seq.nth s1 0) (_ bv0 64)))
        ))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    assert_eq!(outputs, vec!["sat", "sat", "sat", "unsat"]);
}

/// Regression test for #7656: incremental check-sat-assuming in QF_SEQBV
/// must not leak UNSAT state from one call into subsequent calls.
///
/// Without incremental state isolation, contradictory assumptions encoded
/// as permanent unit clauses in the persistent SAT solver would cause
/// subsequent satisfiable calls to return false UNSAT.
#[test]
fn test_check_sat_assuming_qf_seqbv_incremental_state_isolation_7656() {
    let input = r#"
        (set-logic QF_SEQBV)
        (declare-const s0 (Seq (_ BitVec 8)))
        (declare-const s1 (Seq (_ BitVec 8)))

        ; First: sat (no contradiction)
        (check-sat-assuming ((= (seq.nth s0 0) #x42)))

        ; Second: unsat (contradictory assumptions)
        (check-sat-assuming ((= (seq.nth s0 0) #x42) (= (seq.nth s0 0) #x43)))

        ; Third: sat again -- UNSAT state from second call must not persist
        (check-sat-assuming ((= (seq.nth s0 0) #x42)))

        ; Fourth: unsat (assertion + assumption contradiction)
        (assert (= (seq.nth s0 0) (seq.nth s1 0)))
        (check-sat-assuming ((= (seq.nth s0 0) #x42) (not (= (seq.nth s1 0) #x42))))
    "#;

    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();

    // Z3 produces: sat, unsat, sat, unsat
    assert_eq!(outputs, vec!["sat", "unsat", "sat", "unsat"]);
}

#[test]
fn named_cores_ground_mixed_int_bv_array_completeness_matches_unnamed() {
    // #named-cores-ground-sat regression (probe pair
    // deductive-checks/docs/probes/2026-07-19-named-cores-collateral): with
    // `:produce-unsat-cores` and `:named` assertions — the consumer
    // deductive-checks's STANDARD encoding — a trivially-SAT ground mixed
    // Int/BV/Array query must stay `sat`, exactly like its stripped
    // (cores-off, unnamed) equivalent.
    //
    // The named→assumption core redirect routed the whole query through the
    // QfBvLiaIndep ASSUMPTION lane: `solve_bv_core` disables preprocessing
    // whenever assumptions are present (#5581) and the resulting
    // trusted-BV-model Sat fails the emission gates, demoting to
    // unknown(incomplete). The redirect is a core-tracking strategy, not a
    // verdict authority — a final Unknown is now re-solved through the
    // plain pipeline (`rescue_named_core_redirect_unknown`), so
    // sat-with-cores == sat-without for the SAME ground formula.
    let decls = r#"
        (declare-const i (_ BitVec 32))
        (declare-const seed_pre (_ BitVec 32))
        (declare-const s_pre (Array (_ BitVec 64) (_ BitVec 32)))
        (declare-const seed (_ BitVec 32))
        (declare-const len_pre Int)
        (declare-const i_pre (_ BitVec 32))
        (declare-const len Int)
        (declare-const s (Array (_ BitVec 64) (_ BitVec 32)))
    "#;
    let named_asserts = r#"
        (assert (! (<= 0 len) :named dn0))
        (assert (! (<= 0 len_pre) :named dn1))
        (assert (! (= (select s_pre #x0000000000000000) seed_pre) :named dn2))
        (assert (! (= (select s #x0000000000000000) seed) :named dn3))
        (assert (! (<= 1 len_pre) :named dn4))
        (assert (! (< len 1) :named dn5))
    "#;
    let stripped_asserts = r#"
        (assert (<= 0 len))
        (assert (<= 0 len_pre))
        (assert (= (select s_pre #x0000000000000000) seed_pre))
        (assert (= (select s #x0000000000000000) seed))
        (assert (<= 1 len_pre))
        (assert (< len 1))
    "#;

    let with_cores_plain = format!(
        "(set-option :produce-unsat-cores true)\n(set-logic ALL)\n{decls}{named_asserts}(check-sat)"
    );
    let with_cores_assuming = format!(
        "(set-option :produce-unsat-cores true)\n(set-logic ALL)\n{decls}{named_asserts}(check-sat-assuming ())"
    );
    let stripped = format!("(set-logic ALL)\n{decls}{stripped_asserts}(check-sat)");

    for (tag, input) in [
        ("named+cores plain check-sat", with_cores_plain),
        ("named+cores check-sat-assuming", with_cores_assuming),
        ("stripped", stripped),
    ] {
        let commands = parse(&input).unwrap();
        let mut exec = Executor::new();
        let outputs = exec.execute_all(&commands).unwrap();
        assert_eq!(
            outputs,
            vec!["sat"],
            "{tag}: ground mixed Int/BV/Array must be decided sat \
             (named-core redirect must not cost completeness)"
        );
    }
}
