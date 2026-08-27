// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-output DEMAND through the binary (#model-demand).
//!
//! The SMT-LIB FILE lane is the only lane that holds the whole script before
//! the first solve, so it is the only one that can PROVE nobody will read a
//! model. When it can, the executor skips witness cosmetics (counterexample
//! minimization) -- and nothing else. `:model_minimization.runs` is the
//! observable; `--stats` prints it.
//!
//! Motive, measured on `incremental/ABVFPLRA/inv_Newton_true-unreach-call.c`:
//! 85 `(check-sat)`, zero `(get-model)`, and every satisfiable answer paid for
//! a minimization pass whose result was discarded unread.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

/// A script whose raw assignment has something a minimization pass can work
/// on, so "0 runs" is a decision and not an empty work list.
const SHRINKABLE: &str = "(set-logic QF_LIA)\n\
                          (declare-const x Int)\n\
                          (declare-const y Int)\n\
                          (assert (> x 90))\n\
                          (assert (> y x))\n\
                          (check-sat)\n";

fn run(script: &str, extra_args: &[&str]) -> String {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let path = std::env::temp_dir().join(format!(
        "ay_model_demand_{}_{}.smt2",
        std::process::id(),
        ID.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, script).unwrap();
    let _guard = CleanupGuard(path.clone());

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--stats")
        .args(extra_args)
        .arg(&path)
        .output()
        .expect("failed to spawn ay");
    format!(
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    )
}

/// `--stats` prints extra counters as `:name value`; absent means never set,
/// which for this counter means never entered.
fn minimization_runs(out: &str) -> u64 {
    out.lines()
        .filter_map(|line| line.trim().strip_prefix(":model_minimization.runs "))
        .filter_map(|value| value.trim().parse::<u64>().ok())
        .next_back()
        .unwrap_or(0)
}

fn assert_sat(out: &str) {
    assert!(
        out.lines().any(|l| l.trim() == "sat"),
        "script must answer sat: {out:?}"
    );
}

/// The control is the whole test: the SAME script plus one `(get-model)` must
/// run the cosmetic pass. Without that arm, "0 runs" would also be what a
/// broken counter looks like.
#[test]
fn a_script_that_never_reads_a_model_sheds_the_cosmetic_pass() {
    let consumed = run(&format!("{SHRINKABLE}(get-model)\n"), &[]);
    assert_sat(&consumed);
    assert!(
        minimization_runs(&consumed) > 0,
        "control: a script that prints its model must polish it: {consumed:?}"
    );

    let unread = run(SHRINKABLE, &[]);
    assert_sat(&unread);
    assert_eq!(
        minimization_runs(&unread),
        0,
        "no reader in the script, so no cosmetics: {unread:?}"
    );
}

/// `(get-value ...)` reads the model just as `(get-model)` does, and so does
/// z3's `(eval ...)`. Each must defeat shedding on its own.
#[test]
fn every_model_reading_command_defeats_shedding() {
    for reader in ["(get-value (x))", "(eval x)", "(get-assignment)"] {
        let out = run(&format!("{SHRINKABLE}{reader}\n"), &[]);
        assert_sat(&out);
        assert!(
            minimization_runs(&out) > 0,
            "{reader} reads the model and must defeat shedding: {out:?}"
        );
    }
}

/// `--z3-model` prints the model after a `sat` verdict with no in-script
/// command at all, so the host flag is demand by itself.
#[test]
fn the_model_flag_defeats_shedding() {
    let out = run(SHRINKABLE, &["--z3-model"]);
    assert_sat(&out);
    assert!(
        minimization_runs(&out) > 0,
        "--z3-model prints the model, so it must be polished: {out:?}"
    );
}

/// `--minimize-model` is an explicit request for a SMALL witness. Honour the
/// intent even when no command in the script reads one.
#[test]
fn the_minimize_model_flag_defeats_shedding() {
    let out = run(SHRINKABLE, &["--minimize-model"]);
    assert_sat(&out);
    assert!(
        minimization_runs(&out) > 0,
        "--minimize-model asks for a minimized witness: {out:?}"
    );
}

/// `:produce-models false` makes `(get-model)` an error, so the script has no
/// reader even though it contains the command. This is the arm the host's
/// up-front text scan cannot decide -- the executor decides it.
#[test]
fn produce_models_false_sheds_even_with_a_get_model_present() {
    let out = run(
        &format!("(set-option :produce-models false)\n{SHRINKABLE}(get-model)\n"),
        &[],
    );
    assert_sat(&out);
    assert_eq!(
        minimization_runs(&out),
        0,
        "`:produce-models false` leaves no reader: {out:?}"
    );
}

/// An UNTERMINATED trailing form is invisible to the demand scan (the chunker
/// only emits a command once its parens close). That is safe only because such
/// a form cannot RUN either. Pin the fact rather than the assumption: the
/// script still answers `sat`, and no model is printed.
#[test]
fn unterminated_trailing_get_model_never_runs() {
    let out = run(&format!("{SHRINKABLE}(get-model"), &[]);
    assert_sat(&out);
    assert!(
        !out.contains("define-fun"),
        "an unclosed (get-model must not execute: {out:?}"
    );
}

/// Shedding is COSMETICS ONLY. The verdict and the model gate are unchanged:
/// the same script answers `sat` either way and still reports a confirmed
/// model-check gate result.
#[test]
fn shedding_does_not_disarm_the_model_gate() {
    let unread = run(SHRINKABLE, &[]);
    let consumed = run(&format!("{SHRINKABLE}(get-model)\n"), &[]);
    assert_sat(&unread);
    assert_sat(&consumed);

    let gate_line = |out: &str| {
        out.lines()
            .find(|l| l.trim().starts_with(":model_check_gate.result"))
            .map(|l| l.trim().to_string())
    };
    assert_eq!(
        gate_line(&unread),
        gate_line(&consumed),
        "the model gate must report identically with and without a reader"
    );
    assert!(
        gate_line(&unread).is_some(),
        "the gate must still report on a shed run: {unread:?}"
    );
}

/// A QUOTED command head is the same command. `(|get-model|)` executes and
/// prints a model in AY (its parser normalizes the bars away before dispatch),
/// exactly as it does in z3 — so it must register as DEMAND.
///
/// The earlier `command_head_symbol` compared the raw head text against the
/// unquoted spellings, so `|get-model|` missed the lookup and the run shed its
/// cosmetics while still printing a model. That was verdict-safe — the model is
/// built, validated and gate-checked regardless, and only the polish differed —
/// but it contradicted the demand contract.
///
/// This pins the contract, not the polish: the quoted spelling must be treated
/// identically to the bare one.
#[test]
fn quoted_get_model_head_counts_as_demand() {
    let bare = run(&format!("{SHRINKABLE}(get-model)\n"), &[]);
    let quoted = run(&format!("{SHRINKABLE}(|get-model|)\n"), &[]);
    assert_sat(&bare);
    assert_sat(&quoted);
    assert!(
        quoted.contains("define-fun"),
        "(|get-model|) must execute and print a model: {quoted:?}"
    );
    assert_eq!(
        minimization_runs(&quoted),
        minimization_runs(&bare),
        "a quoted head is the same command, so it must register the same demand"
    );
}
