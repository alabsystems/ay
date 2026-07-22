// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! End-to-end CLI soundness for `match` and the drop-command backstop
//! (#match-soundness).
//!
//! Part 2: a `(match ...)` over a datatype now parses, elaborates, and SOLVES,
//! so the canonical wrong-direction repro yields `unsat` (matching z3) instead
//! of a silently-dropped-constraint `sat`.
//!
//! Part 1: any problem-contributing command that fails to parse OR elaborate is
//! reported as a recoverable `(error ...)` and dropped, after which `check-sat`
//! must fail closed to `unknown` (NEVER a definitive sat/unsat on the incomplete
//! remainder). This is generic over the discarded construct, so the class of
//! bug cannot recur for any unsupported syntax.

use ntest::timeout;
use std::process::Command;

/// Run the built `ay` binary on `smt` (written to a temp file) and return the
/// last sat/unsat/unknown verdict printed to STDOUT (ignoring `c ay.` logs on
/// stderr and any `(error ...)` / `(:...)` lines on stdout).
fn ay_verdict(smt: &str) -> String {
    let ay_path = env!("CARGO_BIN_EXE_ay");
    let temp_path = std::env::temp_dir().join(format!(
        "ay_match_backstop_{}_{:?}.smt2",
        std::process::id(),
        std::thread::current().id()
    ));
    std::fs::write(&temp_path, smt).unwrap();
    struct CleanupGuard(std::path::PathBuf);
    impl Drop for CleanupGuard {
        fn drop(&mut self) {
            let _ = std::fs::remove_file(&self.0);
        }
    }
    let _cleanup = CleanupGuard(temp_path.clone());

    let output = Command::new(ay_path)
        .arg(&temp_path)
        .output()
        .expect("failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    stdout
        .lines()
        .map(str::trim)
        .rfind(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .unwrap_or("<none>")
        .to_string()
}

/// Part 2 end-to-end: the repro from the bug report is now `unsat` (was a wrong
/// `sat` from the dropped `match` assertion).
#[test]
#[timeout(60_000)]
fn test_match_repro_unsat_end_to_end() {
    let smt = r#"(set-logic ALL)
(declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
(declare-const a L)
(assert (= a (cns 5 nl)))
(assert (= (match a ((nl 0) ((cns h t) h))) 6))
(check-sat)
"#;
    assert_eq!(ay_verdict(smt), "unsat");
}

/// Part 2 end-to-end: the SAT companion of the repro.
#[test]
#[timeout(60_000)]
fn test_match_repro_sat_end_to_end() {
    let smt = r#"(set-logic ALL)
(declare-datatypes ((L 0)) (((nl) (cns (hd Int) (tl L)))))
(declare-const a L)
(assert (= a (cns 5 nl)))
(assert (= (match a ((nl 0) ((cns h t) h))) 5))
(check-sat)
"#;
    assert_eq!(ay_verdict(smt), "sat");
}

/// Part 1 backstop, ELABORATION drop: an `assert` over an unknown operator is
/// reported and dropped; check-sat must answer `unknown`, never sat/unsat.
#[test]
#[timeout(60_000)]
fn test_unsupported_op_forces_unknown() {
    let smt = r#"(set-logic ALL)
(declare-const x Int)
(assert (totally-unsupported-op x))
(check-sat)
"#;
    assert_eq!(ay_verdict(smt), "unknown");
}

/// Part 1 backstop, PARSE drop: an `assert` whose term fails to parse is dropped
/// (here an application with a non-symbol, non-(_/as) head); check-sat must
/// answer `unknown` even though the remaining assertion alone is satisfiable.
#[test]
#[timeout(60_000)]
fn test_unparseable_assert_forces_unknown() {
    let smt = r#"(set-logic ALL)
(declare-const x Int)
(assert ((bogus) x))
(assert (= x 1))
(check-sat)
"#;
    assert_eq!(ay_verdict(smt), "unknown");
}

/// Part 1 must NOT over-taint: dropping a pure QUERY/option command (here an
/// unparseable `get-info`) leaves the assertion set intact, so check-sat still
/// answers definitively.
#[test]
#[timeout(60_000)]
fn test_dropped_query_does_not_taint() {
    let smt = r#"(set-logic ALL)
(declare-const x Int)
(assert (= x 1))
(get-info (bogus))
(check-sat)
"#;
    assert_eq!(ay_verdict(smt), "sat");
}

/// A `define-fun-rec` applied to a SYMBOLIC argument unfolds without bound
/// (AY has no recursive-function decision procedure). Rather than exit 1 with
/// NO verdict on stdout — the worst shape for a coprocess driver — the
/// recursion-limit failure taints the problem so `check-sat` fails closed to
/// `unknown` (always sound). z3 answers `sat` here; `unknown` is a sound
/// under-approximation, never a wrong sat/unsat.
#[test]
#[timeout(60_000)]
fn test_recursive_fun_over_symbolic_arg_forces_unknown() {
    let smt = r#"(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(define-fun-rec len ((l Lst)) Int (ite (= l nil) 0 (+ 1 (len (tl l)))))
(declare-const x Lst)
(assert (= (len x) 2))
(check-sat)
"#;
    assert_eq!(ay_verdict(smt), "unknown");
}

/// The taint must NOT over-fire: a `define-fun-rec` applied to a fully CONCRETE
/// argument unfolds to a bound and yields a real verdict (here the sum of
/// [1, 2] is 3, so `(not (= 3 3))` is `unsat`), matching z3.
#[test]
#[timeout(60_000)]
fn test_recursive_fun_over_concrete_arg_decides() {
    let smt = r#"(set-logic ALL)
(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))
(define-fun-rec sm ((l Lst)) Int (ite (= l nil) 0 (+ (hd l) (sm (tl l)))))
(assert (not (= (sm (cons 1 (cons 2 nil))) 3)))
(check-sat)
"#;
    assert_eq!(ay_verdict(smt), "unsat");
}
