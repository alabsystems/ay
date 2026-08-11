// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `(set-option :key value)` for keys AY does not implement.
//!
//! Expectations are literals measured against the pinned oracle (Z3 5.0.0),
//! not computed by shelling out to z3, so the suite still pins the surface on
//! machines without it.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn run(script: &str) -> (i32, String) {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let path = std::env::temp_dir().join(format!(
        "ay_set_option_unknown_{}_{}.smt2",
        std::process::id(),
        ID.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, script).unwrap();
    let _guard = CleanupGuard(path.clone());

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("--z3-mode")
        .arg(&path)
        .output()
        .expect("failed to spawn ay");
    (
        output.status.code().expect("ay died on a signal"),
        String::from_utf8_lossy(&output.stdout).into_owned(),
    )
}

/// The reported column is the start of the VALUE token, so it moves with the
/// whitespace before the value and NOT with the length of the value.
#[test]
fn unknown_option_column_is_the_value_token() {
    let (_, one_space) = run("(set-option :foo true)\n(check-sat)\n");
    assert!(
        one_space.starts_with("(error \"line 1 column 18: unknown parameter 'foo'\n"),
        "got: {one_space:?}"
    );

    let (_, four_spaces) = run("(set-option :foo    true)\n(check-sat)\n");
    assert!(
        four_spaces.starts_with("(error \"line 1 column 21: unknown parameter 'foo'\n"),
        "got: {four_spaces:?}"
    );

    // Same keyword, different value lengths -- the column must not move.
    for value in ["1", "123456", "verylongvalue"] {
        let (_, out) = run(&format!("(set-option :foo {value})\n(check-sat)\n"));
        assert!(
            out.starts_with("(error \"line 1 column 18: unknown parameter 'foo'\n"),
            "value {value:?} moved the column: {out:?}"
        );
    }
}

/// The reported name is normalized `-` -> `_`, as z3 prints it.
#[test]
fn unknown_option_name_is_normalized_in_the_report() {
    for (written, reported) in [
        ("foo-bar", "foo_bar"),
        ("foo_bar", "foo_bar"),
        ("a-b-c-d", "a_b_c_d"),
    ] {
        let (_, out) = run(&format!("(set-option :{written} true)\n(check-sat)\n"));
        assert!(
            out.contains(&format!("unknown parameter '{reported}'")),
            ":{written} must be reported as '{reported}': {out:?}"
        );
    }
}

/// An unknown option sets the exit status to 1 but does NOT stop the script:
/// the following `(check-sat)` still runs and prints its verdict. Measured on
/// the oracle, which prints the error, then `sat`, then exits 1.
#[test]
fn unknown_option_reports_but_continues_execution() {
    let (code, out) = run("(set-option :foo true)\n(check-sat)\n");
    assert_eq!(code, 1, "unknown option must exit 1: {out:?}");
    assert!(
        out.contains("Legal parameters are:"),
        "the legal-parameter list must follow the message: {out:?}"
    );
    // A standalone verdict line -- a bare `contains("sat")` would also match
    // the legal parameter list, which mentions several `sat.*` parameters.
    assert!(
        out.lines().any(|l| l.trim() == "sat"),
        "the following check-sat must still run: {out:?}"
    );
}

/// Global parameters are normalized before lookup, so both spellings resolve.
/// SMT-LIB options are matched VERBATIM, so only the hyphen spelling does.
#[test]
fn global_parameters_normalize_but_smtlib_options_do_not() {
    for accepted in [
        "auto_config",
        "auto-config",
        "produce-models",
        "print-success",
        "timeout",
    ] {
        let (code, out) = run(&format!("(set-option :{accepted} true)\n(check-sat)\n"));
        assert_ne!(code, 1, ":{accepted} must be accepted: {out:?}");
        assert!(
            !out.contains("unknown parameter"),
            ":{accepted} must be accepted: {out:?}"
        );
    }

    // `produce_models` is NOT an SMT-LIB option spelling, and there is no
    // global parameter by that name either, so z3 rejects it.
    let (code, out) = run("(set-option :produce_models true)\n(check-sat)\n");
    assert_eq!(code, 1, "got: {out:?}");
    assert!(
        out.contains("unknown parameter 'produce_models'"),
        "{out:?}"
    );
}

/// Every option AY itself dispatches on must be accepted. These are neither
/// SMT-LIB standard names nor global parameters, so a check built only from
/// those two families rejects them -- and rejecting `:global-decls`, z3's own
/// alias for `:global-declarations`, silently broke global-declaration scope
/// semantics. All measured accepted by the oracle.
#[test]
fn options_ay_dispatches_on_are_accepted() {
    for option in [
        "error-behavior",
        "global-decls",
        "global-declarations",
        "int-real-coercions",
        "print-warning",
        "rlimit",
        "verbosity",
    ] {
        let (_, out) = run(&format!("(set-option :{option} true)\n(check-sat)\n"));
        assert!(
            !out.contains("unknown parameter"),
            ":{option} is a valid z3 option and must be accepted: {out:?}"
        );
    }
}

/// Valid module-qualified options stay accepted. Rejecting them turned VALID
/// options into errors and changed answers -- `:opt.priority box` drives box
/// optimization, and treating it as a global parameter broke it outright.
#[test]
fn module_qualified_options_are_accepted() {
    for module_option in [
        ":opt.priority box",
        ":smt.arith.solver 2",
        ":SMT.Arith.Solver 2", // module lookup is case-insensitive
        ":pp.max_width 100",
        ":model.compact true",
        ":rewriter.flat true",
    ] {
        let (code, out) = run(&format!("(set-option {module_option})\n(check-sat)\n"));
        assert_ne!(code, 1, "{module_option} must be accepted: {out:?}");
        assert!(
            !out.contains("unknown parameter"),
            "{module_option} must be accepted: {out:?}"
        );
    }
}

/// An unknown parameter inside a KNOWN module gets its own diagnostic, naming
/// the module and listing that module's legal parameters -- which, unlike the
/// `-pm:<module>` help output, carry no prose descriptions.
#[test]
fn unknown_parameter_in_known_module_names_the_module() {
    let (code, out) = run("(set-option :opt.nonexistent 1)\n(check-sat)\n");
    assert_eq!(code, 1, "got: {out:?}");
    assert!(
        out.starts_with(
            "(error \"line 1 column 30: unknown parameter 'nonexistent' at module 'opt'\n\
             Legal parameters are:\n"
        ),
        "got: {out:?}"
    );
    // Description-free form: `-pm:opt` would say
    // "elim_01 (bool) eliminate 01 variables (default: true)".
    assert!(
        out.contains("\n  elim_01 (bool) (default: true)\n"),
        "module legal list must drop descriptions: {out:?}"
    );
}

/// The split is at the FIRST dot only, and both halves normalize (`-` -> `_`,
/// lowercased) for the lookup AND in the report.
#[test]
fn module_and_parameter_names_are_normalized() {
    for (written, reported) in [
        ("opt.non-existent", "'non_existent' at module 'opt'"),
        ("OPT.nonexistent", "'nonexistent' at module 'opt'"),
        ("SMT.Nonexistent", "'nonexistent' at module 'smt'"),
        // Not a nested module: everything after the first dot is the parameter.
        ("opt.priority.deeper", "'priority.deeper' at module 'opt'"),
    ] {
        let (_, out) = run(&format!("(set-option :{written} 1)\n(check-sat)\n"));
        assert!(
            out.contains(&format!("unknown parameter {reported}")),
            ":{written} must report {reported}: {out:?}"
        );
    }
}

/// An unknown MODULE is a different, single-line diagnostic -- no legal list.
#[test]
fn unknown_module_is_reported_as_an_invalid_parameter() {
    for (written, module) in [
        ("nosuchmodule.foo", "nosuchmodule"),
        ("no-such-module.foo", "no_such_module"),
        ("NoSuchModule.foo", "nosuchmodule"),
    ] {
        let (code, out) = run(&format!("(set-option :{written} 1)\n(check-sat)\n"));
        assert_eq!(code, 1, ":{written} got: {out:?}");
        assert!(
            out.contains(&format!("invalid parameter, unknown module '{module}'\")")),
            ":{written} must name module '{module}': {out:?}"
        );
        assert!(
            !out.contains("Legal parameters are:"),
            "an unknown module gets no legal list: {out:?}"
        );
    }
}

/// Bare names are lowercased for lookup and in the report, but SMT-LIB option
/// spellings are matched VERBATIM first -- so `:Produce-Models` is not the
/// SMT-LIB option, falls through to the global lookup, and is rejected as
/// `produce_models`.
#[test]
fn bare_names_are_lowercased_but_smtlib_options_are_verbatim() {
    let (_, out) = run("(set-option :FOO true)\n(check-sat)\n");
    assert!(out.contains("unknown parameter 'foo'"), "{out:?}");

    let (_, out) = run("(set-option :Foo-Bar true)\n(check-sat)\n");
    assert!(out.contains("unknown parameter 'foo_bar'"), "{out:?}");

    // Case-insensitive global parameter lookup.
    let (code, out) = run("(set-option :AUTO_CONFIG true)\n(check-sat)\n");
    assert_ne!(code, 1, ":AUTO_CONFIG must be accepted: {out:?}");

    let (code, out) = run("(set-option :Produce-Models true)\n(check-sat)\n");
    assert_eq!(code, 1, "got: {out:?}");
    assert!(
        out.contains("unknown parameter 'produce_models'"),
        "{out:?}"
    );
}
