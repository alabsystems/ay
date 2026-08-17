// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end faithfulness tests for `--dump-bv-cnf`.
//!
//! The dump is a certificate boundary: it must be the complete DIMACS formula
//! handed to the SAT solver, not merely the BV operator-gate subset.

use ay_drat_check::checker::DratChecker;
use ay_drat_check::cnf_parser::{parse_cnf, CnfFormula};
use ay_drat_check::drat_parser::parse_drat;
use ntest::timeout;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::sync::atomic::{AtomicUsize, Ordering};

const MODULAR_IDENTITY_UNSAT: &str = r#"(set-logic QF_BV)
(set-option :timeout 30000)
(set-option :produce-models true)
(declare-const x (_ BitVec 8))
(assert (not (= (bvadd x x) (bvshl x (_ bv1 8)))))
(check-sat)
(get-value (x))
(exit)
"#;

const MODULAR_IDENTITY_SAT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x x) (bvshl x (_ bv1 8))))
(check-sat)
(exit)
"#;

const CONSTRAINED_BV_SAT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x (_ bv1 8)) (_ bv7 8)))
(check-sat)
(exit)
"#;

const EARLY_FALSE_UNSAT: &str = r#"(set-logic QF_BV)
(assert false)
(check-sat)
(exit)
"#;

const SIMPLIFIED_NON_LITERAL_UNSAT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (not (= x x)))
(check-sat)
(exit)
"#;

const DELAYED_MULTIPLICATION_UNSAT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 16))
(declare-const y (_ BitVec 16))
(assert (= ((_ extract 0 0) x) #b0))
(assert (= ((_ extract 0 0) y) #b0))
(assert (= (bvmul x y) #x0007))
(check-sat)
(exit)
"#;

const ASSUMPTION_UNSAT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const a Bool)
(assert (= x #x01))
(assert (or a (= x #x02)))
(check-sat-assuming ((not a)))
(exit)
"#;

const INCREMENTAL_FINAL_SAT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x01))
(push 1)
(assert (= x #x02))
(check-sat)
(pop 1)
(check-sat)
(exit)
"#;

const IN_PROCESS_STALE_REGRESSION: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= (bvadd x (_ bv1 8)) (_ bv7 8)))
(check-sat)
(reset)
(set-logic QF_BV)
(assert false)
(check-sat)
(exit)
"#;

const UNSUPPORTED_AFTER_VALID_EXPORT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x07))
(check-sat)
(reset)
(set-logic QF_LIA)
(declare-const y Int)
(assert (= y 0))
(check-sat)
(exit)
"#;

const DISCARDED_ASSERTION_AFTER_VALID_EXPORT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x07))
(check-sat)
(assert (= (unknown-bv-operation x) #x07))
(check-sat)
(exit)
"#;

const MAXSMT_CHECK: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert-soft (= x #x00) :weight 1)
(check-sat)
(exit)
"#;

const OPTIMIZATION_ASSUMING_CHECK: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(maximize x)
(check-sat-assuming ())
(exit)
"#;

const FAILED_ASSUMING_COMMAND_AFTER_VALID_EXPORT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x07))
(check-sat)
(check-sat-assuming (missing-assumption))
(exit)
"#;

const GET_CONSEQUENCES_AFTER_VALID_EXPORT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const a Bool)
(assert (= x #x01))
(assert a)
(check-sat)
(get-consequences () (a))
(exit)
"#;

const SOLVER_APPLY_AFTER_VALID_EXPORT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x01))
(check-sat)
(apply ctx-solver-simplify)
(exit)
"#;

const NAMED_CORE_REDIRECT: &str = r#"(set-logic QF_BV)
(set-option :produce-unsat-cores true)
(declare-const x (_ BitVec 8))
(assert (! (= x #x01) :named named_x))
(check-sat)
(exit)
"#;

const MALFORMED_DECISION_AFTER_VALID_EXPORT: &str = r#"(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(assert (= x #x01))
(check-sat)
(check-sat-assuming (
"#;

const MISMATCHED_DECLARED_QF_BV_WITH_ARRAY: &str = r#"(set-logic QF_BV)
(declare-const memory (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (select memory #x00) #x2a))
(check-sat)
(exit)
"#;

const DECLARED_QF_ABV: &str = r#"(set-logic QF_ABV)
(declare-const memory (Array (_ BitVec 8) (_ BitVec 8)))
(assert (= (select memory #x00) #x2a))
(check-sat)
(exit)
"#;

struct TempDir(PathBuf);

impl TempDir {
    fn new(test_name: &str) -> Self {
        static FILE_ID: AtomicUsize = AtomicUsize::new(0);
        let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
        let path = std::env::temp_dir().join(format!(
            "ay_bv_cnf_dump_{}_{}_{}",
            std::process::id(),
            test_name,
            id
        ));
        std::fs::create_dir(&path).expect("create temporary test directory");
        Self(path)
    }

    fn path(&self, name: &str) -> PathBuf {
        self.0.join(name)
    }

    fn write(&self, name: &str, contents: &str) -> PathBuf {
        let path = self.path(name);
        std::fs::write(&path, contents).expect("write temporary test input");
        path
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

fn ay_binary() -> &'static str {
    env!("CARGO_BIN_EXE_ay")
}

fn output_text(output: &Output) -> (String, String) {
    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

fn assert_smt_verdict(output: &Output, verdict: &str) {
    let (stdout, stderr) = output_text(output);
    assert!(
        output.status.success(),
        "SMT solve failed: status={:?}; stdout={stdout}; stderr={stderr}",
        output.status.code()
    );
    assert!(
        stdout.lines().any(|line| line.trim() == verdict),
        "expected SMT verdict {verdict:?}; stdout={stdout}; stderr={stderr}"
    );
}

fn assert_smt_verdict_before_expected_model_error(output: &Output, verdict: &str) {
    let (stdout, stderr) = output_text(output);
    assert!(
        stdout.lines().any(|line| line.trim() == verdict),
        "expected SMT verdict {verdict:?}; status={:?}; stdout={stdout}; stderr={stderr}",
        output.status.code()
    );
    // This byte-exact ExternalCodegen query deliberately asks for a value after an
    // UNSAT result. AY reports the correct verdict and then rejects get-value,
    // matching the certificate caller, which consumes the verdict line.
    if !output.status.success() {
        assert!(
            stderr.is_empty() || stdout.contains("model is not available"),
            "only the expected post-UNSAT get-value error is permitted; stdout={stdout}; stderr={stderr}"
        );
    }
}

fn run_smt_dump(input: &Path, dump: &Path) -> Output {
    Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--dump-bv-cnf")
        .arg(dump)
        .arg(input)
        .output()
        .expect("spawn ay SMT dump")
}

fn read_cnf(path: &Path) -> (String, CnfFormula) {
    let text = std::fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("read dumped CNF {}: {error}", path.display()));
    let formula = parse_cnf(text.as_bytes())
        .unwrap_or_else(|error| panic!("parse dumped CNF {}: {error}", path.display()));
    (text, formula)
}

fn replay_cnf(path: &Path) -> Output {
    Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg(path)
        .output()
        .expect("spawn ay CNF replay")
}

fn assert_sat_replay(path: &Path) {
    let output = replay_cnf(path);
    let (stdout, stderr) = output_text(&output);
    assert_eq!(
        output.status.code(),
        Some(10),
        "dumped CNF must replay SAT; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "s SATISFIABLE"),
        "dumped CNF must report SAT; stdout={stdout}; stderr={stderr}"
    );
}

fn assert_unsat_replay(path: &Path) {
    let output = replay_cnf(path);
    let (stdout, stderr) = output_text(&output);
    assert_eq!(
        output.status.code(),
        Some(20),
        "dumped CNF must replay UNSAT; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "s UNSATISFIABLE"),
        "dumped CNF must report UNSAT; stdout={stdout}; stderr={stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn modular_identity_unsat_dump_replays_with_verified_drat() {
    let temp = TempDir::new("modular_unsat");
    let input = temp.write("obligation.smt2", MODULAR_IDENTITY_UNSAT);
    let dump = temp.path("obligation.cnf");
    let proof = temp.path("obligation.drat");

    let output = run_smt_dump(&input, &dump);
    assert_smt_verdict_before_expected_model_error(&output, "unsat");

    let (cnf_text, formula) = read_cnf(&dump);
    assert!(
        !formula.clauses.is_empty(),
        "UNSAT obligation must not be exported as the empty SAT CNF:\n{cnf_text}"
    );

    let replay = Command::new(ay_binary())
        .arg("solve")
        .arg("--verify-proof")
        .arg("--proof")
        .arg(&proof)
        .arg(&dump)
        .output()
        .expect("spawn ay proof-producing CNF replay");
    let (stdout, stderr) = output_text(&replay);
    assert_eq!(
        replay.status.code(),
        Some(20),
        "dumped CNF must replay UNSAT; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.lines().any(|line| line.trim() == "s UNSATISFIABLE"),
        "dumped CNF must report UNSAT; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stderr.contains("verify-proof") && stderr.contains("verified"),
        "replay proof must pass AY's independent verifier; stderr={stderr}"
    );

    let proof_bytes = std::fs::read(&proof).expect("read replay DRAT proof");
    assert!(
        !proof_bytes.is_empty(),
        "replay DRAT proof must be non-empty"
    );
    let steps = parse_drat(&proof_bytes).expect("parse replay DRAT proof");
    let mut checker = DratChecker::new(formula.num_vars, true);
    checker
        .verify(&formula.clauses, &steps)
        .expect("independently verify replay DRAT proof");
}

#[test]
#[timeout(60_000)]
fn satisfiable_dumps_remain_satisfiable() {
    for (name, smt) in [
        ("identity", MODULAR_IDENTITY_SAT),
        ("constrained", CONSTRAINED_BV_SAT),
    ] {
        let temp = TempDir::new(name);
        let input = temp.write("input.smt2", smt);
        let dump = temp.path("input.cnf");

        let output = run_smt_dump(&input, &dump);
        assert_smt_verdict(&output, "sat");
        let (_, formula) = read_cnf(&dump);
        if name == "constrained" {
            assert!(
                formula.num_vars > 0 && !formula.clauses.is_empty(),
                "non-trivial SAT query should exercise the assembled-CNF writer"
            );
        }
        assert_sat_replay(&dump);
    }
}

#[test]
#[timeout(60_000)]
fn early_terminal_query_cannot_reuse_a_stale_dump() {
    for (name, smt) in [
        ("literal-false", EARLY_FALSE_UNSAT),
        ("simplified-non-literal", SIMPLIFIED_NON_LITERAL_UNSAT),
    ] {
        let temp = TempDir::new(name);
        let input = temp.write("early-unsat.smt2", smt);
        let dump = temp.write("early-unsat.cnf", "STALE-DUMP-SENTINEL\n");

        let output = run_smt_dump(&input, &dump);
        assert_smt_verdict(&output, "unsat");

        let bytes = std::fs::read(&dump).expect("terminal query must produce canonical CNF");
        assert_ne!(
            bytes, b"STALE-DUMP-SENTINEL\n",
            "a terminal path must never leave the pre-solve dump in place"
        );
        assert_unsat_replay(&dump);
    }
}

#[test]
#[timeout(60_000)]
fn delayed_operations_and_assumptions_are_present_in_dump() {
    for (name, smt) in [
        ("delayed-multiplication", DELAYED_MULTIPLICATION_UNSAT),
        ("check-sat-assuming", ASSUMPTION_UNSAT),
    ] {
        let temp = TempDir::new(name);
        let input = temp.write("input.smt2", smt);
        let dump = temp.path("input.cnf");

        let output = run_smt_dump(&input, &dump);
        assert_smt_verdict(&output, "unsat");
        let (_, formula) = read_cnf(&dump);
        assert!(
            formula.num_vars > 0 && !formula.clauses.is_empty(),
            "{name} must use a non-trivial complete encoding"
        );
        assert_unsat_replay(&dump);
    }
}

#[test]
#[timeout(60_000)]
fn incremental_stream_exports_the_final_active_query() {
    let temp = TempDir::new("incremental");
    let input = temp.write("input.smt2", INCREMENTAL_FINAL_SAT);
    let dump = temp.path("input.cnf");

    let output = run_smt_dump(&input, &dump);
    let (stdout, stderr) = output_text(&output);
    assert!(
        output.status.success(),
        "incremental solve failed; stdout={stdout}; stderr={stderr}"
    );
    let verdicts: Vec<_> = stdout
        .lines()
        .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .map(str::trim)
        .collect();
    assert_eq!(verdicts, ["unsat", "sat"], "stdout={stdout}");
    let (_, formula) = read_cnf(&dump);
    assert!(formula.num_vars > 0 && !formula.clauses.is_empty());
    assert_sat_replay(&dump);
}

#[test]
#[timeout(60_000)]
fn later_early_check_replaces_an_artifact_in_the_same_process() {
    let temp = TempDir::new("same-process-stale");
    let input = temp.write("input.smt2", IN_PROCESS_STALE_REGRESSION);
    let dump = temp.path("input.cnf");

    let output = run_smt_dump(&input, &dump);
    let (stdout, stderr) = output_text(&output);
    assert!(
        output.status.success(),
        "multi-check solve failed; stdout={stdout}; stderr={stderr}"
    );
    let verdicts: Vec<_> = stdout
        .lines()
        .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .map(str::trim)
        .collect();
    assert_eq!(verdicts, ["sat", "unsat"], "stdout={stdout}");
    assert_unsat_replay(&dump);
}

#[test]
#[timeout(60_000)]
fn dump_write_failure_prevents_a_verdict() {
    let temp = TempDir::new("write-failure");
    let input = temp.write("input.smt2", CONSTRAINED_BV_SAT);
    let dump = temp.path("missing-parent").join("input.cnf");

    let output = run_smt_dump(&input, &dump);
    let (stdout, stderr) = output_text(&output);
    assert!(
        !output.status.success(),
        "unwritable certificate destination must fail; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !stdout
            .lines()
            .any(|line| matches!(line.trim(), "sat" | "unsat" | "unknown")),
        "a verdict must not escape after certificate export fails; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("artifact export failed") || stderr.contains("artifact export failed"),
        "failure must identify the certificate export boundary; stdout={stdout}; stderr={stderr}"
    );
    assert!(!dump.exists());
}

#[test]
#[timeout(60_000)]
fn unsupported_later_check_clears_the_preceding_artifact() {
    let temp = TempDir::new("unsupported-after-valid");
    let input = temp.write("input.smt2", UNSUPPORTED_AFTER_VALID_EXPORT);
    let dump = temp.path("input.cnf");

    let output = run_smt_dump(&input, &dump);
    let (stdout, stderr) = output_text(&output);
    assert!(
        !output.status.success(),
        "unsupported second query must fail; stdout={stdout}; stderr={stderr}"
    );
    let verdicts: Vec<_> = stdout
        .lines()
        .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .map(str::trim)
        .collect();
    // The rejected second check answers with the synthesized fail-closed
    // `unknown` (every decision query emits a verdict); only the certified
    // first decision may emit a definitive sat/unsat.
    assert_eq!(
        verdicts,
        ["sat", "unknown"],
        "only the first supported check may emit a definitive verdict; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("supports pure QF_BV") || stderr.contains("supports pure QF_BV"),
        "fragment rejection must be explicit; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !dump.exists(),
        "rejected later check must remove the preceding check's artifact"
    );
}

#[test]
#[timeout(60_000)]
fn discarded_problem_command_after_valid_export_fails_without_second_verdict() {
    let temp = TempDir::new("discarded-command-after-valid");
    let input = temp.write("input.smt2", DISCARDED_ASSERTION_AFTER_VALID_EXPORT);
    let dump = temp.path("input.cnf");

    let output = run_smt_dump(&input, &dump);
    let (stdout, stderr) = output_text(&output);
    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    let verdicts: Vec<_> = stdout
        .lines()
        .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .map(str::trim)
        .collect();
    assert_eq!(
        verdicts,
        ["sat"],
        "a discarded assertion must not produce an uncertified second verdict; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("cannot certify a transcript")
            || stderr.contains("cannot certify a transcript"),
        "certificate-boundary failure must be explicit; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !dump.exists(),
        "the rejected second check must remove the first check's artifact"
    );
}

#[test]
#[timeout(60_000)]
fn optimization_and_maxsmt_checks_fail_before_verdict_and_clear_stale_dump() {
    for (name, smt) in [
        ("maxsmt", MAXSMT_CHECK),
        ("optimization-assuming", OPTIMIZATION_ASSUMING_CHECK),
    ] {
        let temp = TempDir::new(name);
        let input = temp.write("input.smt2", smt);
        let dump = temp.write("input.cnf", "STALE-DUMP-SENTINEL\n");

        let output = run_smt_dump(&input, &dump);
        let (stdout, stderr) = output_text(&output);
        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        // The rejected check answers the synthesized fail-closed `unknown`
        // (every decision query emits a verdict); a definitive sat/unsat must
        // never escape.
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat")),
            "optimization must be rejected without a definitive verdict; stdout={stdout}; stderr={stderr}"
        );
        assert!(
            stdout.contains("does not support optimization or MaxSMT")
                || stderr.contains("does not support optimization or MaxSMT"),
            "stdout={stdout}; stderr={stderr}"
        );
        assert!(!dump.exists(), "rejected check must clear stale artifact");
    }
}

#[test]
#[timeout(60_000)]
fn failed_assumption_elaboration_and_internal_probes_retire_prior_artifact() {
    // A failed decision query (the elaboration-failed `check-sat-assuming`)
    // answers the synthesized fail-closed `unknown`; failed non-decision
    // probes emit no verdict of their own. Either way no definitive second
    // sat/unsat may escape and the artifact must be retired.
    for (name, smt, expected_verdicts) in [
        (
            "failed-assumption-elaboration",
            FAILED_ASSUMING_COMMAND_AFTER_VALID_EXPORT,
            vec!["sat", "unknown"],
        ),
        (
            "get-consequences-probe",
            GET_CONSEQUENCES_AFTER_VALID_EXPORT,
            vec!["sat"],
        ),
        (
            "solver-apply-probe",
            SOLVER_APPLY_AFTER_VALID_EXPORT,
            vec!["sat"],
        ),
    ] {
        let temp = TempDir::new(name);
        let input = temp.write("input.smt2", smt);
        let dump = temp.path("input.cnf");

        let output = run_smt_dump(&input, &dump);
        let (stdout, stderr) = output_text(&output);
        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        let verdicts: Vec<_> = stdout
            .lines()
            .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
            .map(str::trim)
            .collect();
        assert_eq!(
            verdicts, expected_verdicts,
            "only the certified first decision may emit a definitive verdict; stdout={stdout}; stderr={stderr}"
        );
        assert!(!dump.exists(), "rejected follow-up must retire artifact");
    }
}

#[test]
#[timeout(60_000)]
fn named_core_redirect_and_malformed_decision_retire_artifacts_before_verdict() {
    // The rejected named-core check answers the synthesized fail-closed
    // `unknown` (every decision query emits a verdict); a definitive
    // sat/unsat never escapes an unexported decision.
    for (name, smt, expected_verdicts) in [
        ("named-core", NAMED_CORE_REDIRECT, vec!["unknown"]),
        (
            "malformed-decision",
            MALFORMED_DECISION_AFTER_VALID_EXPORT,
            vec!["sat"],
        ),
    ] {
        let temp = TempDir::new(name);
        let input = temp.write("input.smt2", smt);
        let dump = temp.write("output.cnf", "STALE-DUMP-SENTINEL\n");

        let output = run_smt_dump(&input, &dump);
        let (stdout, stderr) = output_text(&output);
        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        let verdicts: Vec<_> = stdout
            .lines()
            .filter(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
            .map(str::trim)
            .collect();
        assert_eq!(
            verdicts, expected_verdicts,
            "only fully exported decisions may escape; stdout={stdout}; stderr={stderr}"
        );
        assert!(!dump.exists(), "failed decision must retire the artifact");
    }
}

#[test]
#[timeout(60_000)]
fn certificate_mode_bypasses_the_crash_unknown_wrapper() {
    let temp = TempDir::new("no-wrapper");
    let input = temp.write("input.smt2", CONSTRAINED_BV_SAT);
    let dump = temp.path("output.cnf");

    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--dump-bv-cnf")
        .arg(&dump)
        .arg(&input)
        .env("AY_INTERNAL_TEST_ABORT_SOLVE_CHILD", "1")
        .output()
        .expect("spawn certificate-mode no-wrapper check");

    assert_smt_verdict(&output, "sat");
    assert!(
        dump.exists(),
        "the direct solve must publish its certificate"
    );
}

#[test]
#[timeout(60_000)]
fn mismatched_declared_logic_cannot_bypass_pure_qf_bv_gate() {
    for (name, smt) in [
        ("mismatched-array", MISMATCHED_DECLARED_QF_BV_WITH_ARRAY),
        ("declared-abv", DECLARED_QF_ABV),
    ] {
        let temp = TempDir::new(name);
        let input = temp.write("input.smt2", smt);
        let dump = temp.path("input.cnf");

        let output = run_smt_dump(&input, &dump);
        let (stdout, stderr) = output_text(&output);
        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        // The rejected check answers the synthesized fail-closed `unknown`
        // (every decision query emits a verdict); a definitive sat/unsat must
        // never escape the unexportable formula.
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat")),
            "unsupported array formula must be rejected without a definitive verdict; stdout={stdout}; stderr={stderr}"
        );
        assert!(
            stdout.contains("supports pure QF_BV") || stderr.contains("supports pure QF_BV"),
            "stdout={stdout}; stderr={stderr}"
        );
        assert!(!dump.exists());
    }
}

#[test]
#[timeout(60_000)]
fn dump_destination_cannot_alias_input_or_proof() {
    let temp = TempDir::new("path-collision");
    let input = temp.write("input.smt2", CONSTRAINED_BV_SAT);
    let original_input = std::fs::read(&input).expect("read original input");

    let input_collision = run_smt_dump(&input, &input);
    let (stdout, stderr) = output_text(&input_collision);
    assert!(
        !input_collision.status.success(),
        "stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("aliases the input path") || stderr.contains("aliases the input path"),
        "stdout={stdout}; stderr={stderr}"
    );
    assert_eq!(
        std::fs::read(&input).expect("input survives collision rejection"),
        original_input,
        "certificate setup must never truncate its own input"
    );

    let shared_output = temp.path("shared.out");
    let proof_collision = Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--dump-bv-cnf")
        .arg(&shared_output)
        .arg("--proof")
        .arg(&shared_output)
        .arg(&input)
        .output()
        .expect("spawn ay with colliding proof and CNF outputs");
    let (stdout, stderr) = output_text(&proof_collision);
    assert!(
        !proof_collision.status.success(),
        "stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("aliases the proof path") || stderr.contains("aliases the proof path"),
        "stdout={stdout}; stderr={stderr}"
    );
    assert!(!shared_output.exists());
}

#[test]
#[timeout(60_000)]
fn dump_destination_and_coordination_lock_cannot_alias_other_cli_paths() {
    let temp = TempDir::new("expanded-path-collision");
    let input = temp.write("input.smt2", CONSTRAINED_BV_SAT);

    for (flag, label) in [
        ("--progress-json", "progress JSON"),
        ("--replay", "replay input"),
        ("--diagnostic-file", "diagnostic output"),
        ("--decision-trace", "decision trace"),
        ("--solution-file", "solution witness"),
        ("--trace-file", "trace output"),
        ("--dump-encoding", "encoding dump"),
        ("--decision-log", "decision log"),
        ("--dpll-diagnostic-file", "DPLL diagnostic output"),
        ("--dpll-trace-file", "DPLL trace output"),
    ] {
        let shared = temp.path(&format!("{}.shared", flag.trim_start_matches("--")));
        let output = Command::new(ay_binary())
            .arg("solve")
            .arg("--no-verify-proof")
            .arg("--dump-bv-cnf")
            .arg(&shared)
            .arg(flag)
            .arg(&shared)
            .arg(&input)
            .output()
            .unwrap_or_else(|error| panic!("spawn collision check for {flag}: {error}"));
        let (stdout, stderr) = output_text(&output);
        assert!(
            !output.status.success(),
            "{flag}: stdout={stdout}; stderr={stderr}"
        );
        assert!(
            stdout.contains(&format!("aliases the {label} path"))
                || stderr.contains(&format!("aliases the {label} path")),
            "{flag}: stdout={stdout}; stderr={stderr}"
        );
        assert!(!shared.exists(), "{flag} collision must not create output");
    }

    let dump = temp.path("certificate.cnf");
    let lock_input = temp.write(".certificate.cnf.ay-bv-cnf.lock", CONSTRAINED_BV_SAT);
    let original = std::fs::read(&lock_input).expect("read lock-collision input");
    let output = run_smt_dump(&lock_input, &dump);
    let (stdout, stderr) = output_text(&output);
    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        stdout.contains("coordination lock") || stderr.contains("coordination lock"),
        "stdout={stdout}; stderr={stderr}"
    );
    assert_eq!(
        std::fs::read(&lock_input).expect("lock-collision input survives"),
        original
    );
    assert!(!dump.exists());
}

#[test]
#[timeout(60_000)]
fn paired_drat_destination_and_lock_cannot_alias_input_or_other_outputs() {
    let temp = TempDir::new("drat-expanded-path-collision");
    let input = temp.write("input.smt2", CONSTRAINED_BV_SAT);
    let original_input = std::fs::read(&input).expect("read original input");
    let dump = temp.path("certificate.cnf");

    let input_collision = Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--dump-bv-cnf")
        .arg(&dump)
        .arg("--proof")
        .arg(&input)
        .arg("--proof-format")
        .arg("drat")
        .arg(&input)
        .output()
        .expect("spawn DRAT/input collision check");
    let (stdout, stderr) = output_text(&input_collision);
    assert!(
        !input_collision.status.success(),
        "stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stdout.contains("BV DRAT proof path") || stderr.contains("BV DRAT proof path"),
        "stdout={stdout}; stderr={stderr}"
    );
    assert_eq!(
        std::fs::read(&input).expect("input survives DRAT collision rejection"),
        original_input
    );
    assert!(!dump.exists());

    let proof = temp.path("certificate.drat");
    let drat_lock = temp.path(".certificate.drat.ay-bv-cnf.lock");
    let lock_collision = Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--dump-bv-cnf")
        .arg(&dump)
        .arg("--proof")
        .arg(&proof)
        .arg("--trace-file")
        .arg(&drat_lock)
        .arg(&input)
        .output()
        .expect("spawn DRAT-lock/output collision check");
    let (stdout, stderr) = output_text(&lock_collision);
    assert!(
        !lock_collision.status.success(),
        "stdout={stdout}; stderr={stderr}"
    );
    assert!(
        (stdout.contains("DRAT coordination lock") || stderr.contains("DRAT coordination lock"))
            && (stdout.contains("trace output") || stderr.contains("trace output")),
        "stdout={stdout}; stderr={stderr}"
    );
    assert!(!dump.exists());
    assert!(!proof.exists());
    assert!(!drat_lock.exists());
}

#[test]
#[timeout(60_000)]
fn paired_cnf_and_drat_paths_are_pairwise_disjoint() {
    let temp = TempDir::new("certificate-pairwise-collision");
    let input = temp.write("input.smt2", CONSTRAINED_BV_SAT);
    let dump = temp.path("certificate.cnf");
    let cnf_lock = temp.path(".certificate.cnf.ay-bv-cnf.lock");

    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--dump-bv-cnf")
        .arg(&dump)
        .arg("--proof")
        .arg(&cnf_lock)
        .arg("--proof-format")
        .arg("drat")
        .arg(&input)
        .output()
        .expect("spawn pairwise CNF-lock/DRAT collision check");
    let (stdout, stderr) = output_text(&output);
    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        (stdout.contains("CNF coordination lock") || stderr.contains("CNF coordination lock"))
            && (stdout.contains("proof path") || stderr.contains("proof path")),
        "stdout={stdout}; stderr={stderr}"
    );
    assert!(!dump.exists());
    assert!(!cnf_lock.exists());
}

#[test]
#[cfg(unix)]
#[timeout(60_000)]
fn paired_drat_hard_link_alias_of_input_is_rejected() {
    let temp = TempDir::new("drat-hard-link-input-collision");
    let input = temp.write("input.smt2", CONSTRAINED_BV_SAT);
    let original_input = std::fs::read(&input).expect("read original input");
    let proof_alias = temp.path("proof.drat");
    std::fs::hard_link(&input, &proof_alias).expect("hard-link proof path to input");
    let dump = temp.path("certificate.cnf");

    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--dump-bv-cnf")
        .arg(&dump)
        .arg("--proof")
        .arg(&proof_alias)
        .arg(&input)
        .output()
        .expect("spawn hard-link collision check");
    let (stdout, stderr) = output_text(&output);
    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        stdout.contains("BV DRAT proof path") || stderr.contains("BV DRAT proof path"),
        "stdout={stdout}; stderr={stderr}"
    );
    assert_eq!(
        std::fs::read(&input).expect("input survives hard-link rejection"),
        original_input
    );
    assert!(!dump.exists());
}

#[test]
#[timeout(60_000)]
fn non_solve_early_modes_reject_requested_export_and_remove_stale_artifact() {
    // B58: the `-p` z3-compat parameter dump lost its arm here — the retired
    // env alias was the ONLY channel that could smuggle an export request
    // into that early mode, so the rejection property now holds by
    // construction (there is nothing to reject).
    for mode in ["features"] {
        let temp = TempDir::new(mode);
        let dump = temp.write("stale.cnf", "STALE-DUMP-SENTINEL\n");
        let mut command = Command::new(ay_binary());
        command.arg("solve");
        command.arg("--dump-bv-cnf").arg(&dump).arg("--features");
        let output = command.output().expect("spawn incompatible early mode");
        let (stdout, stderr) = output_text(&output);
        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat" | "unknown")),
            "early mode must not synthesize a verdict; stdout={stdout}; stderr={stderr}"
        );
        assert!(
            stderr.contains("no check-sat query was executed"),
            "stdout={stdout}; stderr={stderr}"
        );
        assert!(!dump.exists(), "early rejection must remove stale artifact");
    }
}

#[test]
#[timeout(60_000)]
fn non_executor_routes_reject_export_before_any_verdict() {
    let dimacs = "p cnf 1 1\n1 0\n";
    let horn = "(set-logic HORN)\n(declare-fun p () Bool)\n(assert p)\n(check-sat)\n";
    let fixedpoint = "(declare-rel p ())\n(rule p)\n(query p)\n";

    for (name, contents) in [
        ("dimacs-file", dimacs),
        ("horn-file", horn),
        ("fp-file", fixedpoint),
    ] {
        let temp = TempDir::new(name);
        let extension = if name == "dimacs-file" { "cnf" } else { "smt2" };
        let input = temp.write(&format!("input.{extension}"), contents);
        let dump = temp.write("stale.cnf", "STALE-DUMP-SENTINEL\n");
        let output = run_smt_dump(&input, &dump);
        let (stdout, stderr) = output_text(&output);
        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        assert!(
            !stdout.lines().any(|line| matches!(
                line.trim(),
                "sat" | "unsat" | "unknown" | "s SATISFIABLE" | "s UNSATISFIABLE" | "s UNKNOWN"
            )),
            "non-Executor route must not emit a verdict; stdout={stdout}; stderr={stderr}"
        );
        assert!(!dump.exists());
    }

    let temp = TempDir::new("dimacs-stdin");
    let dump = temp.write("stale.cnf", "STALE-DUMP-SENTINEL\n");
    let mut child = Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--dump-bv-cnf")
        .arg(&dump)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn piped DIMACS rejection");
    child
        .stdin
        .take()
        .expect("piped stdin")
        .write_all(dimacs.as_bytes())
        .expect("write DIMACS stdin");
    let output = child.wait_with_output().expect("wait for DIMACS rejection");
    let (stdout, stderr) = output_text(&output);
    assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
    assert!(
        !stdout.lines().any(|line| matches!(
            line.trim(),
            "sat" | "unsat" | "unknown" | "s SATISFIABLE" | "s UNSATISFIABLE" | "s UNKNOWN"
        )),
        "stdout={stdout}; stderr={stderr}"
    );
    assert!(!dump.exists());
}

#[test]
#[timeout(60_000)]
fn dynamic_output_channels_are_forbidden_in_certificate_mode() {
    for option in ["regular-output-channel", "diagnostic-output-channel"] {
        let temp = TempDir::new(option);
        let dump = temp.write("output.cnf", "STALE-DUMP-SENTINEL\n");
        let input = temp.write(
            "input.smt2",
            &format!(
                "(set-logic QF_BV)\n(set-option :{option} \"{}\")\n(assert true)\n(check-sat)\n",
                dump.display()
            ),
        );
        let output = run_smt_dump(&input, &dump);
        let (stdout, stderr) = output_text(&output);
        assert!(!output.status.success(), "stdout={stdout}; stderr={stderr}");
        assert!(
            !stdout
                .lines()
                .any(|line| matches!(line.trim(), "sat" | "unsat" | "unknown")),
            "stdout={stdout}; stderr={stderr}"
        );
        assert!(
            stdout.contains("forbids dynamic SMT-LIB output channels")
                || stderr.contains("forbids dynamic SMT-LIB output channels"),
            "stdout={stdout}; stderr={stderr}"
        );
        assert!(!dump.exists());
    }
}

#[test]
#[timeout(60_000)]
fn retired_bv_dimacs_environment_alias_is_inert() {
    // B58: the env aliases are retired; `--dump-bv-cnf` is the one carrier.
    // Setting the legacy names must neither export nor change the verdict.
    let temp = TempDir::new("legacy_alias");
    let input = temp.write("input.smt2", CONSTRAINED_BV_SAT);
    let dump = temp.path("legacy.cnf");

    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg(&input)
        .env("AY_DUMP_BV_CNF", &dump)
        .env("AY_DUMP_BV_DIMACS", &dump)
        .output()
        .expect("spawn ay with retired BV dump env names set");
    assert_smt_verdict(&output, "sat");
    assert!(
        !dump.exists(),
        "retired env aliases must not produce an export"
    );
}

/// A single invocation `ay --dump-bv-cnf CNF --proof DRAT input.smt2` emits BOTH
/// the CNF and a drat-trim-checkable DRAT from the SAME bit-blasted solve — the
/// DRAT verifies against the CNF with the in-tree independent checker. This is
/// the single-invocation B-cert (#56): the CNF and its UNSAT certificate come
/// from one solve, not a dump-then-re-solve round trip.
fn run_single_invocation_bv_drat(input: &Path, dump: &Path, proof: &Path) -> Output {
    Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--dump-bv-cnf")
        .arg(dump)
        .arg("--proof")
        .arg(proof)
        .arg(input)
        .output()
        .expect("spawn single-invocation ay BV DRAT")
}

#[test]
#[timeout(60_000)]
fn single_invocation_emits_cnf_and_independently_checkable_drat() {
    let temp = TempDir::new("single_invocation_drat");
    let input = temp.write("obligation.smt2", MODULAR_IDENTITY_UNSAT);
    let dump = temp.path("obligation.cnf");
    let proof = temp.path("obligation.drat");

    let output = run_single_invocation_bv_drat(&input, &dump, &proof);
    assert_smt_verdict_before_expected_model_error(&output, "unsat");

    let (cnf_text, formula) = read_cnf(&dump);
    assert!(
        !formula.clauses.is_empty(),
        "UNSAT obligation must not be exported as the empty SAT CNF:\n{cnf_text}"
    );

    let proof_bytes =
        std::fs::read(&proof).expect("single-invocation DRAT must be written on unsat");
    assert!(
        !proof_bytes.is_empty(),
        "single-invocation DRAT proof must be non-empty"
    );
    let steps = parse_drat(&proof_bytes).expect("parse single-invocation DRAT proof");
    let mut checker = DratChecker::new(formula.num_vars, true);
    checker
        .verify(&formula.clauses, &steps)
        .expect("single-invocation DRAT must verify against the dumped CNF from the same solve");
}

#[test]
#[timeout(60_000)]
fn single_invocation_trivial_false_emits_empty_clause_drat() {
    for (name, smt) in [
        ("literal-false", EARLY_FALSE_UNSAT),
        ("simplified-non-literal", SIMPLIFIED_NON_LITERAL_UNSAT),
    ] {
        let temp = TempDir::new(name);
        let input = temp.write("input.smt2", smt);
        let dump = temp.path("input.cnf");
        let proof = temp.path("input.drat");

        let output = run_single_invocation_bv_drat(&input, &dump, &proof);
        assert_smt_verdict(&output, "unsat");

        let (_, formula) = read_cnf(&dump);
        let proof_bytes =
            std::fs::read(&proof).expect("trivial-false single-invocation must still emit a DRAT");
        let steps = parse_drat(&proof_bytes).expect("parse trivial-false DRAT");
        let mut checker = DratChecker::new(formula.num_vars, true);
        checker
            .verify(&formula.clauses, &steps)
            .expect("trivial-false empty-clause DRAT must verify against the canonical CNF");
    }
}

#[test]
#[timeout(60_000)]
fn single_invocation_sat_emits_no_unsat_proof_and_clears_stale() {
    let temp = TempDir::new("single_invocation_sat");
    let dump = temp.path("input.cnf");
    let proof = temp.path("input.drat");

    // First produce a real UNSAT proof at the target path...
    let unsat_input = temp.write("unsat.smt2", MODULAR_IDENTITY_UNSAT);
    let unsat = run_single_invocation_bv_drat(&unsat_input, &dump, &proof);
    assert_smt_verdict_before_expected_model_error(&unsat, "unsat");
    assert!(proof.exists(), "UNSAT run must leave a DRAT proof");

    // ...then a SAT query to the SAME paths must clear it: a wrong-fact twin
    // emits no UNSAT certificate.
    let sat_input = temp.write("sat.smt2", CONSTRAINED_BV_SAT);
    let sat = run_single_invocation_bv_drat(&sat_input, &dump, &proof);
    assert_smt_verdict(&sat, "sat");
    assert!(
        !proof.exists(),
        "a SAT verdict must leave no DRAT proof behind (no stale UNSAT certificate)"
    );
}

#[test]
#[timeout(60_000)]
fn single_invocation_drat_requires_dump_bv_cnf() {
    // `--proof X.drat` on an SMT-LIB input WITHOUT `--dump-bv-cnf` stays a hard
    // error (SMT proofs are Alethe); only the CNF-dump coupling relaxes it.
    let temp = TempDir::new("drat_requires_dump");
    let input = temp.write("input.smt2", MODULAR_IDENTITY_UNSAT);
    let proof = temp.path("input.drat");

    let output = Command::new(ay_binary())
        .arg("solve")
        .arg("--no-verify-proof")
        .arg("--proof")
        .arg(&proof)
        .arg(&input)
        .output()
        .expect("spawn ay with bare DRAT proof request");
    let (stdout, stderr) = output_text(&output);
    assert!(
        !output.status.success(),
        "bare --proof X.drat on SMT input must be rejected; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        stderr.contains("SMT-LIB mode requires Alethe"),
        "rejection must name the Alethe requirement; stderr={stderr}"
    );
    assert!(
        !proof.exists(),
        "a rejected DRAT request must not create a proof file"
    );
}

#[test]
#[timeout(60_000)]
fn single_invocation_drat_rejects_check_sat_assuming() {
    // check-sat-assuming augments the dumped CNF with assumption units, which a
    // live DRAT does not fold into its final derivation, so it fails closed
    // rather than emit an uncheckable certificate.
    let temp = TempDir::new("drat_assuming");
    let input = temp.write("input.smt2", ASSUMPTION_UNSAT);
    let dump = temp.path("input.cnf");
    let proof = temp.path("input.drat");

    let output = run_single_invocation_bv_drat(&input, &dump, &proof);
    let (stdout, stderr) = output_text(&output);
    assert!(
        stdout.contains("does not support check-sat-assuming")
            || stderr.contains("does not support check-sat-assuming"),
        "assumption-augmented DRAT must fail closed; stdout={stdout}; stderr={stderr}"
    );
    assert!(
        !proof.exists(),
        "a fail-closed assumption DRAT must not leave a proof file"
    );
}
