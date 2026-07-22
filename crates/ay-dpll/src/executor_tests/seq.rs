// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sequence theory executor-level regression tests (#6486, #8456).
//!
//! Tests that Seq-sorted queries return correct results. #6486 originally
//! worked around incomplete Seq model extraction by setting `skip_model_eval`.
//! #8456 removed the skip and enabled full model validation for Seq theories
//! using TERM_FLAG_SEQ and SAT-fallback in the observation pipeline.

use crate::Executor;
use ay_frontend::parse;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    outputs.join("\n")
}

fn solve_self_checked(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    exec.set_self_check(true);
    // Mirror the CLI contract: self-check requires proof production for UNSAT.
    // This SAT regression exercises the independent model side of that mode.
    exec.set_produce_proofs(true);
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    outputs.join("\n")
}

fn sat_result(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

// ---------------------------------------------------------------------------
// Regression: #6486 — Seq equality on fresh variables returns Unknown
// ---------------------------------------------------------------------------

/// Two fresh Seq(Int) variables asserted equal must be SAT.
/// Before #6486 fix, this returned Unknown because extract_model()
/// could not concretize unconstrained Seq variables.
#[test]
fn test_seq_eq_fresh_variables_is_sat_6486() {
    let smt = r#"
(set-logic QF_SEQ)
(declare-const a (Seq Int))
(declare-const b (Seq Int))
(assert (= a b))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "Seq(Int) equality on fresh variables: expected sat, got: {result}"
    );
}

/// Two fresh Seq(Int) variables asserted distinct: must be SAT-or-UNKNOWN,
/// never `unsat` (the formula IS satisfiable: a=[], b=[0]).
///
/// #nonstring-seq-failclose: on the baseline this returned `sat` but the model
/// was NOT producible — `(get-value (a b))` errored with "no model value
/// available for term of sort (Seq Int)", the exact modelless wrong-`sat`
/// signature the two audits flagged (a `sat` AY cannot back with a witness).
/// The non-string-seq fail-closed gate now downgrades this to a sound `unknown`
/// because AY cannot produce AND validate a complete model. (The sibling
/// `(= a b)` case DOES produce a valid model — a=[], b=[] — and correctly stays
/// `sat`.) Accept `sat` (with a real model) or `unknown`; reject only `unsat`.
#[test]
fn test_seq_distinct_fresh_variables_not_unsat_6486() {
    let smt = r#"
(set-logic QF_SEQ)
(declare-const a (Seq Int))
(declare-const b (Seq Int))
(assert (distinct a b))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "Seq(Int) distinct on fresh variables: expected sat or unknown \
         (never unsat), got: {result}"
    );
}

/// Seq(Int) variable equated to seq.unit of unconstrained Int must be SAT.
/// This exercises the SeqLIA path since `seq.unit` plus Int elements routes
/// through the combined EUF+Seq+LIA solver.
#[test]
fn test_seq_unit_variable_element_is_sat_6486() {
    let smt = r#"
(set-logic QF_SEQLIA)
(declare-const a (Seq Int))
(declare-const x Int)
(assert (= a (seq.unit x)))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("sat"),
        "Seq(Int) eq seq.unit(x): expected sat, got: {result}"
    );
}

// ---------------------------------------------------------------------------
// Model validation: Seq theory (#8456)
// ---------------------------------------------------------------------------

/// Seq concat satisfiability: model validation runs on the result.
/// Before #8456, this would use skip_model_eval and never verify the model.
#[test]
fn test_seq_concat_sat_with_validation_8456() {
    let smt = r#"
(set-logic QF_SEQ)
(declare-const a (Seq Int))
(declare-const b (Seq Int))
(declare-const c (Seq Int))
(assert (= c (seq.++ a b)))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(r, Some("sat"), "Seq concat: expected sat, got: {result}");
}

/// Seq length constraint with model validation (#8456).
#[test]
fn test_seq_len_constraint_sat_8456() {
    let smt = r#"
(set-logic QF_SEQLIA)
(declare-const a (Seq Int))
(assert (> (seq.len a) 0))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert!(
        matches!(r, Some("sat") | Some("unknown")),
        "Seq length > 0: expected sat or unknown, got: {result}"
    );
}

/// A symbolic sequence length above the old 64-element ground-reasoning cap is
/// still a small, concrete model witness. Model completion may materialize that
/// witness without asking the sequence theory to unroll it, then the strict and
/// independent gates validate the candidate before SAT is exposed.
#[test]
fn test_seq_len_above_ground_cap_has_validated_sat_model() {
    let smt = r#"
(set-logic QF_SEQLIA)
(declare-const a (Seq Int))
(assert (> (seq.len a) 100))
(check-sat)
"#;
    let result = solve_self_checked(smt);
    assert_eq!(
        sat_result(&result),
        Some("sat"),
        "Seq length > 100 has a bounded, independently validatable witness: {result}"
    );
}

/// Seq contradiction: empty sequence cannot have positive length.
#[test]
fn test_seq_empty_length_unsat_8456() {
    let smt = r#"
(set-logic QF_SEQLIA)
(declare-const a (Seq Int))
(assert (= a (as seq.empty (Seq Int))))
(assert (> (seq.len a) 0))
(check-sat)
"#;
    let result = solve(smt);
    let r = sat_result(&result);
    assert_eq!(
        r,
        Some("unsat"),
        "Empty seq with positive length should be unsat, got: {result}"
    );
}

// ---------------------------------------------------------------------------
// SOUNDNESS regression: non-string sequence wrong-`sat` fail-close
// (#nonstring-seq-failclose).
//
// AY's symbolic non-string sequence theory ((Seq Int)/(Seq Bool)/
// (Seq (_ BitVec n))/(Seq Real)) was systemically UNSOUND on the sat side:
// many seq.* ops returned a wrong `sat` for an UNSATISFIABLE formula, with a
// model that could not be produced or that falsified its own assertions. The
// non-string-seq fail-closed gate downgrades these `sat`s to `unknown`. Each
// probe below is genuinely UNSAT (z3 decides unsat); AY must return `unsat` or
// `unknown` — NEVER `sat`. These are a representative subset of the two audits'
// 15+ wrong-verdict probes.
// ---------------------------------------------------------------------------

/// Assert the given seq problem never returns a (wrong) `sat`.
fn assert_not_sat(smt: &str, label: &str) {
    let result = solve(smt);
    let r = sat_result(&result);
    assert!(
        matches!(r, Some("unsat") | Some("unknown")),
        "{label}: non-string-seq wrong-sat must fail-close to unsat/unknown, \
         got: {result}"
    );
}

/// seq.prefixof positional propagation into seq.nth (meta-audit new #1).
#[test]
fn test_nonstring_seq_prefixof_nth_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const a (Seq Int))
(declare-const x (Seq Int))
(assert (seq.prefixof a x))
(assert (= (seq.len a) 1))
(assert (not (= (seq.nth x 0) (seq.nth a 0))))
(check-sat)"#,
        "seq.prefixof->nth",
    );
}

/// seq.suffixof + equal lengths forcing x=a (meta-audit new #2).
#[test]
fn test_nonstring_seq_suffixof_nth_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const a (Seq Int))
(declare-const x (Seq Int))
(assert (seq.suffixof a x))
(assert (= (seq.len a) 1))
(assert (= (seq.len x) 1))
(assert (not (= (seq.nth x 0) (seq.nth a 0))))
(check-sat)"#,
        "seq.suffixof->nth",
    );
}

/// seq.replace over (Seq Int) with a self-falsifying model (meta-audit new #3).
#[test]
fn test_nonstring_seq_replace_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const s (Seq Int))
(assert (= s (seq.replace (seq.unit 2) (seq.unit 2) (seq.unit 9))))
(assert (not (= s (seq.unit 9))))
(check-sat)"#,
        "seq.replace",
    );
}

/// seq.extract subsequence fact not propagated to seq.contains (meta-audit new #4).
#[test]
fn test_nonstring_seq_extract_contains_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const a (Seq Int))
(assert (= (seq.extract a 1 2) (seq.++ (seq.unit 1) (seq.unit 2))))
(assert (not (seq.contains a (seq.unit 1))))
(check-sat)"#,
        "seq.extract->contains",
    );
}

/// seq.indexof decoupled from element content (meta-audit new #5).
#[test]
fn test_nonstring_seq_indexof_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const a (Seq Int))
(assert (= (seq.indexof a (seq.unit 9) 0) 2))
(assert (= (seq.nth a 2) 8))
(check-sat)"#,
        "seq.indexof",
    );
}

/// Seq-of-BitVec: BV op on a seq.nth result decoupled from equality
/// (meta-audit new #6). The seq element sort is a BitVec, not Char.
#[test]
fn test_nonstring_seq_of_bitvec_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const s (Seq (_ BitVec 8)))
(assert (= (seq.nth s 0) #xff))
(assert (bvult (seq.nth s 0) #x80))
(check-sat)"#,
        "seq-of-bitvec",
    );
}

/// Seq Int arithmetic-pinned seq.nth + bare disequality (meta-audit new #7).
#[test]
fn test_nonstring_seq_nth_arith_diseq_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const s (Seq Int))
(assert (< (seq.nth s 0) 6))
(assert (> (seq.nth s 0) 4))
(assert (distinct (seq.nth s 0) 5))
(check-sat)"#,
        "seq.nth+arith",
    );
}

/// seq.at over a concat of length-constrained symbolic seqs (meta-audit
/// fix-incomplete m1).
#[test]
fn test_nonstring_seq_at_concat_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const a (Seq Int))
(declare-const b (Seq Int))
(assert (= (seq.len a) 1))
(assert (not (= (seq.at (seq.++ a b) 0) a)))
(check-sat)"#,
        "seq.at-concat",
    );
}

/// seq.nth through a variable bound to a concat with both lengths fixed
/// (meta-audit fix-incomplete f3).
#[test]
fn test_nonstring_seq_nth_var_concat_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const a (Seq Int))
(declare-const b (Seq Int))
(declare-const x (Seq Int))
(assert (= x (seq.++ a b)))
(assert (= (seq.len a) 1))
(assert (= (seq.len b) 1))
(assert (not (= (seq.nth x 0) (seq.nth a 0))))
(check-sat)"#,
        "seq.nth-var-concat",
    );
}

/// seq.extract overlapping self-contradiction (meta-audit fix-incomplete).
#[test]
fn test_nonstring_seq_extract_overlap_not_sat() {
    assert_not_sat(
        r#"(set-logic ALL)
(declare-const a (Seq Int))
(assert (> (seq.len a) 5))
(assert (= (seq.extract a 0 3)
           (seq.++ (seq.unit 1) (seq.++ (seq.unit 2) (seq.unit 3)))))
(assert (= (seq.extract a 1 1) (seq.unit 9)))
(check-sat)"#,
        "seq.extract-overlap",
    );
}

/// A GENUINE non-string-seq SAT whose model IS producible/validatable must
/// stay `sat` (the fail-close must not over-degrade): s = (seq.unit 5).
#[test]
fn test_nonstring_seq_genuine_sat_stays_sat() {
    let smt = r#"(set-logic ALL)
(declare-const s (Seq Int))
(assert (= s (seq.unit 5)))
(check-sat)"#;
    let result = solve(smt);
    assert_eq!(
        sat_result(&result),
        Some("sat"),
        "a genuine, validatable (Seq Int) sat must stay sat, got: {result}"
    );
}

/// #7656 nth-only witness: a (Seq BV) constant whose ONLY constraint is a
/// pinned `seq.nth` at a constant index (no `seq.len` term anywhere) is
/// trivially satisfiable — the witness length is inferred as `1 + max index`
/// and the model-check gates re-validate the produced witness. This was the
/// check-sat-assuming qf_seqbv regression shape: the empty-default witness
/// made the independent evaluator report "seq.nth index out of range" and the
/// non-string-seq gate fail-closed a genuine sat to unknown.
#[test]
fn test_nonstring_seq_nth_only_no_len_is_sat_7656() {
    let smt = r#"(set-logic ALL)
(declare-const s (Seq (_ BitVec 8)))
(assert (= (seq.nth s 2) #x07))
(check-sat)"#;
    let result = solve(smt);
    assert_eq!(
        sat_result(&result),
        Some("sat"),
        "nth-only (Seq BV) constraint with unconstrained length must be sat, got: {result}"
    );
}
