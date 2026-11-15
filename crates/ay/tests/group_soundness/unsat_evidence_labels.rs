// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Evidence policy P4 (2026-10-02): every published UNSAT says on stderr how
//! much evidence stands behind it, and a reproduction is never dressed up as a
//! check.
//!
//! * A refutation AY's strict checker accepted is `evidence=E2` with
//!   `corroboration=none`.
//! * A `discharged-trust` admission — unproved steps admitted because a fresh
//!   executor running the same code re-decided the query — is `evidence=E1`,
//!   names its corroboration arm and what that re-solve ran without
//!   (`disabled=none` says it re-ran exactly the same code), and prints a
//!   `c ay.proof.corroboration` line naming where the re-solve ran
//!   (`source=direct`, or the nested probe that carried it up).
//! * `--rigor strict` carries the full evidence promise: it refuses E1.
//!
//! The fixtures are pinned to their current route (each assertion names it),
//! so a lane that later certifies one of them fails this test loudly instead
//! of letting it pass without exercising the label it exists for.

use ntest::timeout;
use std::process::Command;

use super::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};
use crate::spawn::OutputTimeout;

/// Congruence clash over an uninterpreted sort: a strict proof.
const STRICT_PROOF: &str = "(set-logic QF_UF)
(declare-sort U 0)
(declare-fun a () U)
(declare-fun b () U)
(declare-fun f (U) U)
(assert (= a b))
(assert (not (= (f a) (f b))))
(check-sat)
";

/// The string rewrite `(str.replace y \"\" \"\") = y` (D7: QF_SLIA
/// str-pred-small-rw_233): its refutation keeps one unproved step, admitted by
/// a direct fresh-executor re-decision. Since step (4a) of the trust discharge
/// (3d69b77a6) that re-decision asks whether the authored obligation entails
/// the deferred clauses before it re-solves the whole query, so this admission
/// is `corroboration=entailment`. The whole-query `resolve` arm is pinned by
/// the LNH fixture below, whose re-solve must run without LNH.
const DIRECT_ENTAILMENT: &str = "(set-logic QF_SLIA)
(declare-fun x () String)
(declare-fun y () String)
(assert (not (= (= x (str.replace y \"\" \"\")) (= x y))))
(check-sat)
";

/// A closed-sentence theorem sealing a nested refutation that rests on a
/// re-solve (D7: UFNIRA funcprobs problem_C10_sol1). Before P4 this printed
/// no corroboration line at all.
const NESTED_CLOSED_SENTENCE: &str = "(set-logic UFNIRA)
(declare-fun f (Real) Real)
(assert (forall ((x Real)) (= (f x) x)))
(assert (not (and
  (forall ((x Real) (y Real)) (=> (< x y) (<= (f x) (f y))))
  (forall ((x Real)) (= (f (f x)) x)))))
(check-sat)
";

/// Pigeonhole 7 into 6 over declared constants (main's LNH on/off fixture
/// `php7_6_symmetric_unsat`; z3 5.1.0: unsat). LNH engages, its facts reach
/// the refutation as trust steps, and the re-solve that corroborates them runs
/// without it (P1). That re-solve is step (4a)'s entailment question, which
/// the fresh executor answers within its counts in the outer query's metered
/// posture (`unsat_cert/screened_reconfirmation.rs`).
const LNH_PIGEONHOLE: &str = "(set-logic QF_UF)
(declare-sort U 0)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U)
(declare-const c3 U) (declare-const c4 U) (declare-const c5 U)
(declare-const x0 U) (declare-const x1 U) (declare-const x2 U) (declare-const x3 U)
(declare-const x4 U) (declare-const x5 U) (declare-const x6 U)
(assert (distinct c0 c1 c2 c3 c4 c5))
(assert (or (= x0 c0) (= x0 c1) (= x0 c2) (= x0 c3) (= x0 c4) (= x0 c5)))
(assert (or (= x1 c0) (= x1 c1) (= x1 c2) (= x1 c3) (= x1 c4) (= x1 c5)))
(assert (or (= x2 c0) (= x2 c1) (= x2 c2) (= x2 c3) (= x2 c4) (= x2 c5)))
(assert (or (= x3 c0) (= x3 c1) (= x3 c2) (= x3 c3) (= x3 c4) (= x3 c5)))
(assert (or (= x4 c0) (= x4 c1) (= x4 c2) (= x4 c3) (= x4 c4) (= x4 c5)))
(assert (or (= x5 c0) (= x5 c1) (= x5 c2) (= x5 c3) (= x5 c4) (= x5 c5)))
(assert (or (= x6 c0) (= x6 c1) (= x6 c2) (= x6 c3) (= x6 c4) (= x6 c5)))
(assert (distinct x0 x1 x2 x3 x4 x5 x6))
(check-sat)
";

/// Pigeonhole 9 into 8, the same shape one size up (z3 5.1.0: unsat). Without
/// LNH no CDCL search refutes it inside step (4a)'s counts (its question
/// spends them in about 0.15 s), so the whole-query `resolve` arm admits it:
/// step (4) re-decides the query with the symmetry its own solve proved
/// (`carry_lnh`).
const LNH_PIGEONHOLE_9_8: &str = "(set-logic QF_UF)
(declare-sort U 0)
(declare-const c0 U) (declare-const c1 U) (declare-const c2 U) (declare-const c3 U)
(declare-const c4 U) (declare-const c5 U) (declare-const c6 U) (declare-const c7 U)
(declare-const x0 U) (declare-const x1 U) (declare-const x2 U) (declare-const x3 U)
(declare-const x4 U) (declare-const x5 U) (declare-const x6 U) (declare-const x7 U)
(declare-const x8 U)
(assert (distinct c0 c1 c2 c3 c4 c5 c6 c7))
(assert (or (= x0 c0) (= x0 c1) (= x0 c2) (= x0 c3) (= x0 c4) (= x0 c5) (= x0 c6) (= x0 c7)))
(assert (or (= x1 c0) (= x1 c1) (= x1 c2) (= x1 c3) (= x1 c4) (= x1 c5) (= x1 c6) (= x1 c7)))
(assert (or (= x2 c0) (= x2 c1) (= x2 c2) (= x2 c3) (= x2 c4) (= x2 c5) (= x2 c6) (= x2 c7)))
(assert (or (= x3 c0) (= x3 c1) (= x3 c2) (= x3 c3) (= x3 c4) (= x3 c5) (= x3 c6) (= x3 c7)))
(assert (or (= x4 c0) (= x4 c1) (= x4 c2) (= x4 c3) (= x4 c4) (= x4 c5) (= x4 c6) (= x4 c7)))
(assert (or (= x5 c0) (= x5 c1) (= x5 c2) (= x5 c3) (= x5 c4) (= x5 c5) (= x5 c6) (= x5 c7)))
(assert (or (= x6 c0) (= x6 c1) (= x6 c2) (= x6 c3) (= x6 c4) (= x6 c5) (= x6 c6) (= x6 c7)))
(assert (or (= x7 c0) (= x7 c1) (= x7 c2) (= x7 c3) (= x7 c4) (= x7 c5) (= x7 c6) (= x7 c7)))
(assert (or (= x8 c0) (= x8 c1) (= x8 c2) (= x8 c3) (= x8 c4) (= x8 c5) (= x8 c6) (= x8 c7)))
(assert (distinct x0 x1 x2 x3 x4 x5 x6 x7 x8))
(check-sat)
";

/// Pigeonhole 8 into 7 over an uninterpreted sort, pigeons 2..7 each barred
/// from one hole so the symmetry strengthening stays off (z3 5.1.0: unsat).
/// The outer search exhausts its bookkeeping meter and leaves a bare trust
/// closer; step (3)'s native array lane re-decides it with a checked SAT
/// refutation built from the lane's own whole clause trace.
const BARRED_PIGEONHOLE: &str = "(set-logic QF_UF)
(declare-sort U 0)
(declare-const a0 U) (declare-const a1 U) (declare-const a2 U) (declare-const a3 U)
(declare-const a4 U) (declare-const a5 U) (declare-const a6 U) (declare-const a7 U)
(declare-const h0 U) (declare-const h1 U) (declare-const h2 U) (declare-const h3 U)
(declare-const h4 U) (declare-const h5 U) (declare-const h6 U)
(assert (or (= a0 h0) (= a0 h1) (= a0 h2) (= a0 h3) (= a0 h4) (= a0 h5) (= a0 h6)))
(assert (or (= a1 h0) (= a1 h1) (= a1 h2) (= a1 h3) (= a1 h4) (= a1 h5) (= a1 h6)))
(assert (or (= a2 h0) (= a2 h1) (= a2 h3) (= a2 h4) (= a2 h5) (= a2 h6)))
(assert (or (= a3 h0) (= a3 h1) (= a3 h2) (= a3 h4) (= a3 h5) (= a3 h6)))
(assert (or (= a4 h0) (= a4 h1) (= a4 h2) (= a4 h3) (= a4 h5) (= a4 h6)))
(assert (or (= a5 h0) (= a5 h1) (= a5 h2) (= a5 h3) (= a5 h4) (= a5 h6)))
(assert (or (= a6 h0) (= a6 h1) (= a6 h2) (= a6 h3) (= a6 h4) (= a6 h5)))
(assert (or (= a7 h1) (= a7 h2) (= a7 h3) (= a7 h4) (= a7 h5) (= a7 h6)))
(assert (distinct a0 a1 a2 a3 a4 a5 a6 a7))
(check-sat)
";

/// The same pigeonhole with an unrelated integer constraint (QF_UFLIA): the
/// clause goes to step (3)'s native bit-vector lane instead, whose checked
/// SAT refutation also rests on its own whole clause trace.
fn barred_pigeonhole_uflia() -> String {
    BARRED_PIGEONHOLE
        .replace("(set-logic QF_UF)", "(set-logic QF_UFLIA)")
        .replace(
            "(check-sat)",
            "(declare-const k Int)\n(assert (> k 0))\n(check-sat)",
        )
}

struct Run {
    verdicts: Vec<String>,
    stderr: String,
    context: String,
}

fn run(query: &str, flags: &[&str]) -> Run {
    let dir = tempfile::tempdir().expect("tempdir");
    let smt2 = dir.path().join("query.smt2");
    std::fs::write(&smt2, query).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(flags)
        .arg(&smt2)
        .output_timeout(QUERY_TIMEOUT)
        .expect("run ay");
    let stdout = String::from_utf8_lossy(&output.stdout).into_owned();
    let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
    let context = format!("flags {flags:?}\nstdout:\n{stdout}\nstderr:\n{stderr}");
    Run {
        verdicts: verdict_lines(&stdout),
        stderr,
        context,
    }
}

/// The `key=value` fields of the first stderr line starting with `prefix`
/// (the part before the em dash that starts its prose).
fn fields(stderr: &str, prefix: &str) -> Option<Vec<(String, String)>> {
    let line = stderr.lines().find(|l| l.starts_with(prefix))?;
    let head = line.split(" — ").next().unwrap_or(line);
    Some(
        head.split_whitespace()
            .filter_map(|w| w.split_once('='))
            .map(|(k, v)| (k.to_string(), v.trim_end_matches(';').to_string()))
            .collect(),
    )
}

fn field<'a>(fields: &'a [(String, String)], key: &str) -> Option<&'a str> {
    fields
        .iter()
        .find(|(k, _)| k == key)
        .map(|(_, v)| v.as_str())
}

/// Assert one field's value, with the whole run as context.
fn expect(fields: &[(String, String)], key: &str, want: &str, why: &str, run: &Run) {
    assert_eq!(field(fields, key), Some(want), "{why}: {}", run.context);
}

/// The evidence fields of the UNSAT publication: from the certificate line,
/// or — when no document was emitted — from the no-certificate warning,
/// which carries the same fields after `unsat_admission=`.
fn evidence_fields(run: &Run) -> Vec<(String, String)> {
    if let Some(f) = fields(&run.stderr, "c ay.proof.certificate ") {
        return f;
    }
    let warning = run
        .stderr
        .lines()
        .find(|l| l.starts_with("c warning: no proof certificate emitted"))
        .unwrap_or_else(|| panic!("no certificate line nor warning: {}", run.context));
    let tail = &warning[warning
        .find("unsat_admission=")
        .unwrap_or_else(|| panic!("the warning names no admission: {}", run.context))..];
    tail.split_whitespace()
        .filter_map(|w| w.split_once('='))
        .map(|(k, v)| {
            let v = v.trim_end_matches(|c: char| c == ';' || c == ',' || c == ')' || c == '.');
            (k.to_string(), v.to_string())
        })
        .collect()
}

#[test]
#[timeout(600_000)]
fn a_strict_proof_is_e2_with_no_corroboration() {
    let run = run(STRICT_PROOF, &[]);
    assert_eq!(run.verdicts, ["unsat"], "{}", run.context);
    let f = evidence_fields(&run);
    expect(&f, "unsat_admission", "strict-proof", "label", &run);
    expect(&f, "evidence", "E2", "label", &run);
    expect(&f, "corroboration", "none", "label", &run);
    expect(&f, "disabled", "none", "label", &run);
    assert!(
        fields(&run.stderr, "c ay.proof.corroboration ").is_none(),
        "a checked refutation was not corroborated: {}",
        run.context
    );
}

#[test]
#[timeout(600_000)]
fn a_direct_entailment_admission_is_e1_and_says_it_reran_the_same_code() {
    let run = run(DIRECT_ENTAILMENT, &[]);
    assert_eq!(run.verdicts, ["unsat"], "{}", run.context);
    let f = evidence_fields(&run);
    let route = "the fixture no longer reaches the trust discharge, so it pins nothing";
    expect(&f, "unsat_admission", "discharged-trust", route, &run);
    expect(&f, "evidence", "E1", "label", &run);
    expect(&f, "corroboration", "entailment", "label", &run);
    expect(&f, "disabled", "none", "label", &run);
    let corroboration = fields(&run.stderr, "c ay.proof.corroboration ")
        .unwrap_or_else(|| panic!("E1 prints its corroboration line: {}", run.context));
    expect(&corroboration, "method", "entailment", "label", &run);
    expect(&corroboration, "source", "direct", "label", &run);
    expect(&corroboration, "disabled", "none", "label", &run);
    assert!(
        !run.stderr.contains("fresh-executor-resolve"),
        "the retired tag must not be printed: {}",
        run.context
    );
}

#[test]
#[timeout(600_000)]
fn a_nested_resolve_passes_its_corroboration_up() {
    let run = run(NESTED_CLOSED_SENTENCE, &[]);
    assert_eq!(run.verdicts, ["unsat"], "{}", run.context);
    let f = evidence_fields(&run);
    let route = "the fixture no longer rests on a nested trust discharge, so it pins nothing";
    expect(&f, "unsat_admission", "discharged-trust", route, &run);
    expect(&f, "evidence", "E1", "label", &run);
    expect(&f, "corroboration", "resolve", "label", &run);
    let corroboration = fields(&run.stderr, "c ay.proof.corroboration ")
        .unwrap_or_else(|| panic!("the nested arm must reach the outer solve: {}", run.context));
    let nested = "nested:closed-sentence";
    expect(&corroboration, "source", nested, "label", &run);
}

/// P1, as the reader sees it: the re-solve that admitted an LNH-using
/// refutation ran without LNH, and `disabled=` names it.
#[test]
#[timeout(600_000)]
fn an_entailment_that_ran_without_lnh_names_it() {
    let run = run(LNH_PIGEONHOLE, &[]);
    assert_eq!(run.verdicts, ["unsat"], "z3 5.1.0: unsat; {}", run.context);
    let f = evidence_fields(&run);
    let route = "the fixture no longer rests on an LNH trust discharge, so it pins nothing";
    expect(&f, "unsat_admission", "discharged-trust", route, &run);
    expect(&f, "evidence", "E1", "label", &run);
    expect(&f, "corroboration", "entailment", "label", &run);
    expect(&f, "disabled", "lnh-symmetry", "label", &run);
    let corroboration = fields(&run.stderr, "c ay.proof.corroboration ")
        .unwrap_or_else(|| panic!("E1 prints its corroboration line: {}", run.context));
    expect(&corroboration, "method", "entailment", "label", &run);
    expect(&corroboration, "source", "direct", "label", &run);
    expect(&corroboration, "disabled", "lnh-symmetry", "label", &run);
}

/// P1 on the whole-query `resolve` arm: step (4a) cannot answer without LNH,
/// so step (4) admits the refutation, and `disabled=` still names LNH.
#[test]
#[timeout(600_000)]
fn a_resolve_that_ran_without_lnh_names_it() {
    let run = run(LNH_PIGEONHOLE_9_8, &[]);
    assert_eq!(run.verdicts, ["unsat"], "z3 5.1.0: unsat; {}", run.context);
    let f = evidence_fields(&run);
    let route = "the fixture no longer rests on an LNH trust discharge, so it pins nothing";
    expect(&f, "unsat_admission", "discharged-trust", route, &run);
    expect(&f, "evidence", "E1", "label", &run);
    expect(&f, "corroboration", "resolve", "label", &run);
    expect(&f, "disabled", "lnh-symmetry", "label", &run);
    let corroboration = fields(&run.stderr, "c ay.proof.corroboration ")
        .unwrap_or_else(|| panic!("E1 prints its corroboration line: {}", run.context));
    expect(&corroboration, "method", "resolve", "label", &run);
    expect(&corroboration, "source", "direct", "label", &run);
    expect(&corroboration, "disabled", "lnh-symmetry", "label", &run);
}

#[test]
#[timeout(600_000)]
fn rigor_strict_refuses_an_e1_admission() {
    let run = run(DIRECT_ENTAILMENT, &["--rigor", "strict"]);
    assert_eq!(
        run.verdicts,
        ["unknown"],
        "--rigor strict carries the full evidence promise; a reproduction is not evidence: {}",
        run.context
    );
}

/// Step (3)'s lanes keep their unmetered clause trace in the default posture,
/// so a closer whose checked refutation rests on that trace keeps the
/// `standalone-tautology` record. Metering the lanes with the query's
/// reconstruction budget (the rejected first r30-step3-lanes patch) turned
/// both of these into step (4a)'s `entailment`.
#[test]
#[timeout(600_000)]
fn a_trace_backed_step_3_discharge_is_a_standalone_tautology() {
    let uflia = barred_pigeonhole_uflia();
    for (query, lane) in [(BARRED_PIGEONHOLE, "array"), (uflia.as_str(), "bit-vector")] {
        let run = run(query, &[]);
        assert_eq!(run.verdicts, ["unsat"], "z3 5.1.0: unsat; {}", run.context);
        let f = evidence_fields(&run);
        let route = "the fixture no longer reaches the trust discharge, so it pins nothing";
        expect(&f, "unsat_admission", "discharged-trust", route, &run);
        expect(&f, "evidence", "E1", lane, &run);
        expect(&f, "corroboration", "standalone-tautology", lane, &run);
    }
}
