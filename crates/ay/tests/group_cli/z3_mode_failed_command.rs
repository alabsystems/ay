// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Under `--z3-mode`, a command that fails inside the executor ends that
//! command, not the session: z3 reports the error and keeps answering, and
//! drivers that hold one solver process open (Verus's AIR) depend on it.

use ntest::timeout;
use std::io::Write;
use std::process::{Command, Stdio};

/// Declarations for the failing query below.
pub(crate) const DECLS: &str = r#"
(declare-sort Poly 0)
(declare-fun %R (Poly) Real)
(declare-fun Mul (Int Int) Int)
(declare-datatypes ((D 0)) (((This (This/0 Int)) (That (That/v Int)))))
(declare-const t D)
(declare-const p Poly)
(declare-const a Int)
(declare-const b Int)
(declare-const failing_str String)
"#;

/// A decision query the executor refuses with an error in every rigor
/// posture: maximizing a String has no optimization order, so
/// `check-sat` fails with `UnsupportedOptimization` (z3 rejects the
/// same maximize at elaboration). The earlier no-combined-decision-
/// procedure fixture (datatype + nonlinear Int + Real mix) now
/// answers a plain `unknown` by design — a theory mix with no
/// combined lane is incomplete, never an execution error — so it
/// can no longer drive the executor-failure machinery these tests
/// exist to pin. The maximize is registered in the same push scope
/// as the check in the session tests, and `pop` drops it, so later
/// queries decide normally.
///
pub(crate) const FAILING_QUERY: &str = r#"
(maximize failing_str)
(check-sat)
"#;

fn run_stdin(args: &[&str], input: &str) -> std::process::Output {
    let mut child = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg("-in")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("spawn ay -in");
    child
        .stdin
        .as_mut()
        .expect("child stdin")
        .write_all(input.as_bytes())
        .expect("write SMT-LIB input");
    child.wait_with_output().expect("wait for ay -in")
}

fn answers(stdout: &str) -> Vec<&str> {
    stdout
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .collect()
}

/// The fixture must really fail, or the tests below prove nothing: outside
/// `--z3-mode` the failure still ends the session.
#[test]
#[timeout(120_000)]
fn the_fixture_query_fails_and_plain_mode_still_exits() {
    let input = format!("{DECLS}{FAILING_QUERY}(echo \"after-error\")\n");
    let output = run_stdin(&["-q"], &input);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.contains("(error"),
        "the fixture query must fail with an execution error; stderr: {stderr}"
    );
    assert!(!output.status.success(), "plain mode exits non-zero");
    assert!(
        !stdout.contains("after-error"),
        "plain mode ends the session at the failure; stdout: {stdout}"
    );
}

/// The guard above runs with the proofs plain mode produces by default, but
/// the tests that share the fixture run under `--z3-mode`, which produces
/// none, and a new capability can decide the fixture on that path alone: the
/// previous query stayed refused above while ground-first refuted it under
/// `--z3-mode`, and seven tests failed on an `unsat` they did not expect.
/// This guard runs the fixture on both proof-free paths and names the change.
#[test]
#[timeout(120_000)]
fn the_fixture_query_is_refused_without_proofs() {
    let input = format!("{DECLS}{FAILING_QUERY}(get-info :reason-unknown)\n");
    for args in [&["-q", "--z3-mode"][..], &["-q", "--no-proof"][..]] {
        let output = run_stdin(args, &input);
        let stdout = String::from_utf8_lossy(&output.stdout);
        let stderr = String::from_utf8_lossy(&output.stderr);
        let found = answers(&stdout);
        assert!(
            !found.contains(&"unsat"),
            "ay {args:?} answered unsat on FAILING_QUERY, whose assertions are \
             satisfiable: a wrong verdict; stdout: {stdout}; stderr: {stderr}"
        );
        let refused = if args.contains(&"--z3-mode") {
            stdout.contains(
                "(:reason-unknown \"(incomplete decision-execution-error \"\"unsupported optimization",
            )
        } else {
            stderr.contains("(error \"unsupported optimization")
        };
        assert!(
            found == ["unknown"] && refused,
            "ay {args:?} no longer refuses FAILING_QUERY (answers {found:?}): the \
             z3_mode_* tests that share the fixture prove nothing until it is \
             re-pinned to a query ay still refuses with an execution error; \
             stdout: {stdout}; stderr: {stderr}"
        );
    }
}

#[test]
#[timeout(120_000)]
fn z3_mode_answers_every_command_after_a_failed_query() {
    let input = format!(
        "{DECLS}(push)\n{FAILING_QUERY}(get-info :reason-unknown)\n(echo \"after-error\")\n\
         (pop)\n(push)\n(assert false)\n(check-sat)\n(pop)\n(check-sat)\n"
    );
    let output = run_stdin(&["-q", "--z3-mode"], &input);
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        stderr.is_empty(),
        "z3 prints no error for this query, so neither does ay: stderr: {stderr}"
    );
    assert!(
        stdout.contains("(:reason-unknown \"(incomplete decision-execution-error \"\""),
        "the failed query explains its unknown in one SMT-LIB string; stdout: {stdout}"
    );
    assert!(!stdout.contains("(error"), "stdout: {stdout}");
    assert!(stdout.contains("after-error"), "stdout: {stdout}");
    assert_eq!(
        answers(&stdout),
        ["unknown", "unsat", "sat"],
        "one unknown for the failed query, then z3's answers; stdout: {stdout}"
    );
    assert!(
        output.status.success(),
        "no error was printed, so the run exits 0, as z3 does on this input"
    );
}

/// The failed query ran in a scope that is popped afterwards. Nothing it
/// asserted may survive into the next query: `x = 1` is gone, so `x = 2` is
/// satisfiable (z3: sat).
#[test]
#[timeout(120_000)]
fn z3_mode_state_after_a_failed_query_is_the_popped_problem() {
    let input = format!(
        "(declare-const x Int)\n{DECLS}(push)\n(assert (= x 1))\n{FAILING_QUERY}(pop)\n\
         (assert (= x 2))\n(check-sat)\n"
    );
    let output = run_stdin(&["-q", "--z3-mode"], &input);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(
        answers(&stdout),
        ["unknown", "sat"],
        "stdout: {stdout}; stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// z3 refuses to change `:global-declarations` once the session holds a
/// declaration ("option value cannot be modified after initialization"). A
/// session that accepted the change could give declarations of one session
/// different lifetimes, which a rebuilt executor would not reproduce: this
/// script answered `sat` after the failed query, where z3 answers `unsat`.
#[test]
#[timeout(120_000)]
fn z3_mode_rejects_global_declarations_after_initialization() {
    let input = "(set-option :global-declarations true)\n(declare-const b Bool)\n(push)\n\
                 (declare-const k Int)\n(assert (= k 5))\n(define-fun five () Int 5)\n\
                 (set-option :global-declarations false)\n(pop)\n(check-sat-assuming (k))\n\
                 (define-fun five () Int 7)\n(assert (not (= five 5)))\n(check-sat)\n";
    let output = run_stdin(&["-q", "--z3-mode"], input);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains(
            "error setting ':global-decls', option value cannot be modified after initialization"
        ),
        "stdout: {stdout}"
    );
    assert!(
        stdout.contains("named expression already defined"),
        "`five` is still defined, so its redefinition is refused; stdout: {stdout}"
    );
    assert_eq!(answers(&stdout).last(), Some(&"unsat"), "stdout: {stdout}");
}

/// The same shape with a query that fails inside the executor, so the
/// session is rebuilt from its replay log: the declaration made under
/// `:global-declarations` inside a popped level has to survive the rebuild.
#[test]
#[timeout(120_000)]
fn z3_mode_rebuild_keeps_global_declarations_of_a_popped_level() {
    let input = format!(
        "(set-option :global-declarations true)\n{DECLS}(push)\n(define-fun five () Int 5)\n\
         (set-option :global-declarations false)\n(pop)\n(push)\n{FAILING_QUERY}(pop)\n\
         (define-fun five () Int 7)\n(assert (not (= five 5)))\n(check-sat)\n"
    );
    let output = run_stdin(&["-q", "--z3-mode"], &input);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("option value cannot be modified after initialization"),
        "stdout: {stdout}"
    );
    assert_eq!(
        answers(&stdout),
        ["unknown", "unsat"],
        "stdout: {stdout}; stderr: {}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Without any option change: declarations made under global declarations
/// in a level popped before the failure are part of the rebuilt executor.
#[test]
#[timeout(120_000)]
fn z3_mode_rebuild_replays_global_declarations() {
    let input = format!(
        "(set-option :global-declarations true)\n{DECLS}(push)\n(define-fun five () Int 5)\n\
         (pop)\n(push)\n{FAILING_QUERY}(pop)\n(define-fun five () Int 7)\n\
         (assert (not (= five 5)))\n(check-sat)\n"
    );
    let output = run_stdin(&["-q", "--z3-mode"], &input);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("named expression already defined"),
        "stdout: {stdout}"
    );
    assert_eq!(answers(&stdout), ["unknown", "unsat"], "stdout: {stdout}");
}

/// z3 accepts the option before the session is initialized, and again after
/// `(reset)`.
#[test]
#[timeout(120_000)]
fn z3_mode_accepts_global_declarations_before_initialization_and_after_reset() {
    let input = "(set-logic ALL)\n(set-option :produce-models true)\n\
                 (set-option :global-declarations true)\n(declare-const x Int)\n(reset)\n\
                 (set-option :global-decls false)\n(get-option :global-declarations)\n";
    let output = run_stdin(&["-q", "--z3-mode"], input);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(!stdout.contains("(error"), "stdout: {stdout}");
    assert!(stdout.trim_end().ends_with("false"), "stdout: {stdout}");
}

/// z3 keeps `:global-declarations` across `(reset)`: `five` survives the pop,
/// so its redefinition is refused and the goal is `unsat`. The frontend used to
/// return to scoped declarations while `get-option` still reported `true`.
#[test]
#[timeout(120_000)]
fn z3_mode_keeps_global_declarations_across_reset() {
    let input = "(set-option :global-declarations true)\n(declare-const b Bool)\n(reset)\n\
                 (get-option :global-declarations)\n(push)\n(define-fun five () Int 5)\n(pop)\n\
                 (define-fun five () Int 7)\n(assert (not (= five 5)))\n(check-sat)\n";
    let output = run_stdin(&["-q", "--z3-mode"], input);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(stdout.starts_with("true\n"), "stdout: {stdout}");
    assert!(
        stdout.contains("named expression already defined"),
        "stdout: {stdout}"
    );
    assert_eq!(answers(&stdout), ["unsat"], "stdout: {stdout}");
}

/// A non-Bool assumption is refused before any solving, with z3's message,
/// and the session goes on.
#[test]
#[timeout(120_000)]
fn z3_mode_rejects_a_non_boolean_assumption() {
    let input =
        "(declare-const xi Int)\n(check-sat-assuming (xi))\n(echo \"after\")\n(check-sat)\n";
    let output = run_stdin(&["-q", "--z3-mode"], input);
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert!(
        stdout.contains("invalid check-sat command, argument must be a Boolean literal"),
        "stdout: {stdout}"
    );
    assert!(!stdout.contains("solve loop"), "stdout: {stdout}");
    assert!(stdout.contains("after"), "stdout: {stdout}");
    assert_eq!(answers(&stdout).last(), Some(&"sat"), "stdout: {stdout}");
}
