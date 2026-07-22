// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Executor-level regression tests for the Nielsen word-equation pre-pass
//! (Track A3 Milestones 1–2).
//!
//! Each case is a symbolic word equation that the CEGAR string pipeline
//! previously returned `unknown` on (its `EmptySplit` dedup latches the
//! sticky-incomplete flag). All verdicts here were cross-checked against
//! z3 4.15.4 (Milestone 1) / z3 4.16.0 (Stage 2, except the noted timeout);
//! the SAT models are additionally validated by the executor's own full
//! model validation before the pre-pass may answer.

use crate::Executor;
use ay_frontend::parse;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    outputs.join("\n")
}

fn verdict(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

/// `x ++ "ab" = "a" ++ y` — sat (e.g. x="", y="b"). z3: sat.
#[test]
fn test_word_eq_align_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "ab") (str.++ "a" y)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// `x ++ x = "aba"` — unsat (2|x| = 3 is infeasible). z3: unsat.
#[test]
fn test_word_eq_parity_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x x) "aba"))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `"a" ++ x = x ++ "b"` — unsat (character counts differ). z3: unsat.
#[test]
fn test_word_eq_parikh_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ "a" x) (str.++ x "b")))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// `x ++ y = y ++ x AND x != y` — sat (e.g. x="", y="b"). z3: sat.
#[test]
fn test_word_eq_commute_vars_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) (str.++ y x)))
(assert (not (= x y)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// `x ++ "ab" = "a" ++ y AND |x| = 2` — sat (x="aa", y="aab"). z3: sat.
#[test]
fn test_word_eq_exact_len_sat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "ab") (str.++ "a" y)))
(assert (= (str.len x) 2))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// `x ++ x ++ x = "ab"` — unsat (3|x| = 2 is infeasible). z3: unsat.
#[test]
fn test_word_eq_cube_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x x x) "ab"))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// Chained equations: `x ++ "b" = "ab" ++ y AND y ++ "c" = z` — sat. z3: sat.
#[test]
fn test_word_eq_chain_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(declare-fun z () String)
(assert (= (str.++ x "b") (str.++ "ab" y)))
(assert (= (str.++ y "c") z))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// The pre-pass must NOT fire a wrong UNSAT when out-of-fragment constraints
/// make the equations' minimal solutions invalid: the SAT candidate x=""
/// fails validation against `str.contains`, and the answer falls through to
/// the normal pipeline (which may answer sat via witnesses or unknown — but
/// never unsat, the formula is satisfiable, e.g. x="ca", y="cab").
#[test]
fn test_word_eq_out_of_fragment_never_wrong() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "ab") (str.++ x "ab")))
(assert (str.contains x "c"))
(check-sat)
"#;
    let out = solve(smt);
    assert_ne!(verdict(&out), Some("unsat"));
}

/// Exact-length conflict: `x ++ "ab" = "a" ++ y AND |x|=1 AND |y|=1` — unsat
/// (|lhs| = 3, |rhs| = 2). z3: unsat.
#[test]
fn test_word_eq_len_conflict_unsat() {
    let smt = r#"
(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "ab") (str.++ "a" y)))
(assert (= (str.len x) 1))
(assert (= (str.len y) 1))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// M2: `str.suffixof "c" (x ++ "b")` — unsat (last char is "b"). z3: unsat.
#[test]
fn test_word_eq_m2_suffixof_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.suffixof "c" (str.++ x "b")))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// M2: `str.contains "ab" (x ++ "c")` — unsat ("ab" has no "c"). z3: unsat.
#[test]
fn test_word_eq_m2_contains_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (str.contains "ab" (str.++ x "c")))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// M2: symbolic containment with a nonempty side constraint — sat
/// (e.g. x="a", y=""). z3: sat.
#[test]
fn test_word_eq_m2_contains_symbolic_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.contains (str.++ x "b") (str.++ "a" y)))
(assert (not (= x "")))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// M2: prefixof coupled with a commutation equation and a disequation — sat
/// (e.g. x="", y="a"...; requires harvesting beyond the first solved form,
/// the leaf-dedup regression). z3: sat.
#[test]
fn test_word_eq_m2_prefix_commute_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (str.prefixof (str.++ x "a") (str.++ "a" y)))
(assert (= (str.++ x y) (str.++ y x)))
(assert (not (= y "")))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

// ── Stage 2: quadratic depth + regex coupling ───────────────────────────

/// S2: `x·a = a·x` (⇒ x ∈ a*) with `x ∈ a*·b` — unsat via derivative
/// pruning (mirrors we18). z3: unsat.
#[test]
fn test_word_eq_s2_re_commute_astar_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "a") (str.++ "a" x)))
(assert (str.in_re x (re.++ (re.* (str.to_re "a")) (str.to_re "b"))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// S2: negative membership filters the `x = ""` leaf; bounded canonical
/// revisits surface `x = "ab"` (mirrors we19). z3: sat.
#[test]
fn test_word_eq_s2_re_neg_membership_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "ab") (str.++ "ab" x)))
(assert (not (str.in_re x (str.to_re ""))))
(assert (= y (str.++ x "b")))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// S2: forced length 2|x| = 4 plus `(_ re.loop 3 5)` — unsat (mirrors
/// we20). z3: unsat.
#[test]
fn test_word_eq_s2_re_loop_len_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x x) "aaaa"))
(assert (str.in_re x ((_ re.loop 3 5) (str.to_re "a"))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// S2: intersection derivatives guide to the unique non-empty witness
/// x = "aa" (mirrors we21). z3: sat.
#[test]
fn test_word_eq_s2_re_inter_opt_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ "a" x) (str.++ x "a")))
(assert (str.in_re x (re.inter (re.* (re.range "a" "b")) (re.opt (str.to_re "aa")))))
(assert (not (= x "")))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// S2: commuting non-empty words over disjoint alphabets (a+ vs b+) —
/// Lyndon–Schützenberger refutation (mirrors we22). z3: unsat.
#[test]
fn test_word_eq_s2_re_disjoint_commute_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) (str.++ y x)))
(assert (str.in_re x (re.+ (str.to_re "a"))))
(assert (str.in_re y (re.+ (str.to_re "b"))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// S2: x commutes with "ab" but x ∈ b+ (mirrors we23). z3: unsat.
#[test]
fn test_word_eq_s2_re_bplus_commute_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "ab") (str.++ "ab" x)))
(assert (str.in_re x (re.+ (str.to_re "b"))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// S2: regex witnesses for commuting variables, x ∈ (ab)+ and y = (ab)^2
/// (mirrors we24). z3: sat.
#[test]
fn test_word_eq_s2_re_loop_witness_sat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x y) (str.++ y x)))
(assert (str.in_re x (re.++ (str.to_re "ab") (re.* (str.to_re "ab")))))
(assert (str.in_re y ((_ re.loop 2 2) (str.to_re "ab"))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// S2: quadratic rotation `x·a·x·b = b·x·a·x` — σ(x·a·x) must be a power
/// of "b" yet contains 'a' (mirrors we25). z3 4.16.0 TIMES OUT here; the
/// verdict follows from the Lyndon–Schützenberger commutation lemma (see
/// `commutation_conflict` in ay-strings word_eq.rs).
#[test]
fn test_word_eq_s2_quad_primitive_root_unsat() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "a" x "b") (str.++ "b" x "a" x)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

/// S2 soundness guard: an untranslatable regex (re.comp) must be SKIPPED,
/// never mistranslated — the formula is satisfiable (x = ""), so any
/// `unsat` here is a soundness bug. z3: sat.
#[test]
fn test_word_eq_s2_re_comp_out_of_fragment_never_wrong() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(assert (= (str.++ x "a") (str.++ "a" x)))
(assert (str.in_re x (re.comp (str.to_re "a"))))
(check-sat)
"#;
    assert_ne!(verdict(&solve(smt)), Some("unsat"));
}

/// Model check: the produced assignment must satisfy the equation exactly
/// (materialized by the pre-pass, validated by the executor).
#[test]
fn test_word_eq_model_values() {
    let smt = r#"
(set-logic QF_S)
(declare-fun x () String)
(declare-fun y () String)
(assert (= (str.++ x "ab") (str.++ "a" y)))
(check-sat)
(get-value (x y))
"#;
    let out = solve(smt);
    assert_eq!(verdict(&out), Some("sat"));
    // Parse the two returned values and re-check the equation directly.
    let vals: Vec<String> = out
        .lines()
        .flat_map(|l| {
            let mut v = Vec::new();
            let mut rest = l;
            while let Some(idx) = rest.find('"') {
                let tail = &rest[idx + 1..];
                if let Some(end) = tail.find('"') {
                    v.push(tail[..end].to_string());
                    rest = &tail[end + 1..];
                } else {
                    break;
                }
            }
            v
        })
        .collect();
    assert_eq!(vals.len(), 2, "expected two string values in {out:?}");
    let (x, y) = (&vals[0], &vals[1]);
    assert_eq!(
        format!("{x}ab"),
        format!("a{y}"),
        "model violates the equation"
    );
}
