// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The default certificate (`<input>.alethe`) under strict proofs, requested
//! by `--strict-proofs`, by the in-script `(set-option :check-proofs-strict
//! true)`, or by both: each query is held back, certified and withheld under
//! the request in force when it was answered, and gets exactly one response.

use ntest::timeout;
use std::process::Command;

use super::strict_admission_routes::{unproved_rules, COMPLETE_CERTIFICATE, HOLED_BY_THE_PRINTER};
use super::strict_admission_spellings::ASSUMING_PREFIX;
use super::strict_certificate_publication::QUERY_TIMEOUT;
use crate::spawn::OutputTimeout;

/// Both spellings of strict proofs, alone and together, as
/// `(name, --strict-proofs, (set-option :check-proofs-strict true))`.
pub(super) const STRICT_SPELLINGS: [(&str, bool, bool); 3] = [
    ("option", false, true),
    ("flag", true, false),
    ("flag and option", true, true),
];

/// What sits at the default certificate path `<input>.alethe` before a run.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum DefaultPath {
    /// Nothing: the certificate can be published.
    Free,
    /// A stale file, which publication never replaces.
    Occupied,
    /// Nothing, but the input's directory is read-only.
    #[cfg(unix)]
    ReadOnlyDirectory,
}

/// The planted stale certificate.
const STALE_CERTIFICATE: &str = "stale certificate from an earlier run\n";

/// What `ay [--strict-proofs] query.smt2` published.
pub(super) struct FileRun {
    pub(super) success: bool,
    /// The exit code, if the run exited.
    pub(super) code: Option<i32>,
    /// The non-empty stdout lines, in order.
    pub(super) lines: Vec<String>,
    /// `<input>.alethe` after the run, if it is a file.
    pub(super) certificate: Option<String>,
    pub(super) context: String,
}

/// Run the file route on `body` under one strict spelling, with the default
/// certificate path prepared as `path`.
pub(super) fn run_strict_file(
    body: &str,
    spelling: (&str, bool, bool),
    path: DefaultPath,
) -> FileRun {
    let (name, flag, option) = spelling;
    let script = if option {
        format!("(set-option :check-proofs-strict true)\n{body}")
    } else {
        body.to_string()
    };
    let args: &[&str] = if flag { &["--strict-proofs"] } else { &[] };
    run_file(name, args, &script, path)
}

/// Run `ay <args> query.smt2` on `script`, with the default certificate path
/// prepared as `path`.
pub(super) fn run_file(name: &str, args: &[&str], script: &str, path: DefaultPath) -> FileRun {
    let dir = tempfile::tempdir().expect("tempdir");
    let smt2 = dir.path().join("query.smt2");
    let default_path = dir.path().join("query.smt2.alethe");
    std::fs::write(&smt2, script).expect("write query");
    match path {
        DefaultPath::Free => {}
        DefaultPath::Occupied => {
            std::fs::write(&default_path, STALE_CERTIFICATE).expect("plant stale certificate");
        }
        #[cfg(unix)]
        DefaultPath::ReadOnlyDirectory => make_read_only(dir.path(), &default_path),
    }
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg(&smt2)
        .output_timeout(QUERY_TIMEOUT);
    #[cfg(unix)]
    {
        use std::os::unix::fs::PermissionsExt;
        std::fs::set_permissions(dir.path(), std::fs::Permissions::from_mode(0o755))
            .expect("restore directory permissions");
    }
    let output = output.expect("run ay");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    FileRun {
        success: output.status.success(),
        code: output.status.code(),
        lines: stdout
            .lines()
            .map(str::trim)
            .filter(|l| !l.is_empty())
            .map(str::to_string)
            .collect(),
        certificate: std::fs::read_to_string(&default_path).ok(),
        context: format!(
            "{name} {args:?} / {path:?} (exit {:?})\nscript:\n{script}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            output.status
        ),
    }
}

/// Make `directory` read-only. A privileged runner ignores mode bits, so there
/// a directory planted at the default path makes publication fail instead.
#[cfg(unix)]
fn make_read_only(directory: &std::path::Path, default_path: &std::path::Path) {
    use std::os::unix::fs::PermissionsExt;
    std::fs::set_permissions(directory, std::fs::Permissions::from_mode(0o555))
        .expect("make directory read-only");
    let probe = directory.join(".ay-write-probe");
    if std::fs::File::create_new(&probe).is_ok() {
        std::fs::remove_file(&probe).expect("remove write probe");
        std::fs::create_dir(default_path).expect("block the default certificate path");
    }
}

/// The paths where the default certificate cannot be published.
fn unpublishable_paths() -> Vec<DefaultPath> {
    let mut paths = vec![DefaultPath::Occupied];
    #[cfg(unix)]
    paths.push(DefaultPath::ReadOnlyDirectory);
    paths
}

/// Checks a run whose one strict `unsat` lost its certificate: exactly one
/// response for the query, `unknown`, saying why, and no file replaced.
fn assert_withheld_once(run: &FileRun, path: DefaultPath, expected_lines: &[&str]) {
    let context = &run.context;
    assert_eq!(run.lines, expected_lines, "{context}");
    assert!(
        context.contains("(:reason-unknown (incomplete proof-publication-failed))"),
        "the withheld verdict must say why: {context}"
    );
    assert!(run.success, "{context}");
    if path == DefaultPath::Occupied {
        assert_eq!(
            run.certificate.as_deref(),
            Some(STALE_CERTIFICATE),
            "publication replaced an existing file: {context}"
        );
    }
}

/// Checks that the run published its strict `unsat`'s complete certificate.
pub(super) fn assert_certificate_published(run: &FileRun) {
    let context = &run.context;
    let document = run
        .certificate
        .as_deref()
        .unwrap_or_else(|| panic!("no certificate was published: {context}"));
    assert!(
        document.contains("(assume ") && document.contains("(cl)"),
        "{context}"
    );
    assert_eq!(unproved_rules(document), 0, "{context}");
}

/// A strict `unsat` whose default certificate cannot be published is ONE
/// `unknown`, whichever spelling asked for strict proofs.
///
/// Measured on main 1e9b1b229 with only the in-script option: a pre-existing
/// `<input>.alethe` or a read-only directory made one `check-sat` print
/// `unsat`, and then `unknown` at EOF, after the responses to later commands.
/// The hold-back decision read only the flag, latched before the script ran;
/// the publication posture read both spellings.
#[test]
#[timeout(600_000)]
fn a_strict_unsat_whose_certificate_cannot_be_published_is_one_unknown() {
    let trailing = format!("{COMPLETE_CERTIFICATE}(echo \"after-check-sat\")\n");
    for spelling in STRICT_SPELLINGS {
        for path in unpublishable_paths() {
            let run = run_strict_file(COMPLETE_CERTIFICATE, spelling, path);
            assert_withheld_once(&run, path, &["unknown"]);
            // The response comes before the next command's, never at EOF.
            let run = run_strict_file(&trailing, spelling, path);
            assert_withheld_once(&run, path, &["unknown", "after-check-sat"]);
        }
    }
}

/// With the default path free, a strict `unsat` is published once, with its
/// certificate, in command order.
///
/// A no-change guard, not a regression test: main passes it too, in all three
/// spellings. It pins that holding the option's `unsat` back costs a
/// publishable query neither its `unsat` nor its certificate.
#[test]
#[timeout(600_000)]
fn a_strict_unsat_with_a_free_default_path_is_published_with_its_certificate() {
    let trailing = format!("{COMPLETE_CERTIFICATE}(echo \"after-check-sat\")\n");
    for spelling in STRICT_SPELLINGS {
        let run = run_strict_file(COMPLETE_CERTIFICATE, spelling, DefaultPath::Free);
        assert_eq!(run.lines, ["unsat"], "{}", run.context);
        assert!(run.success, "{}", run.context);
        assert_certificate_published(&run);
        let run = run_strict_file(&trailing, spelling, DefaultPath::Free);
        assert_eq!(run.lines, ["unsat", "after-check-sat"], "{}", run.context);
        assert_certificate_published(&run);
    }
}

/// A strict `unsat` that is no longer the current result at EOF — a `pop` or
/// a later query follows it — still gets its certificate, or is withheld.
///
/// Measured on main 1e9b1b229 with only the in-script option: both scripts
/// printed `unsat` and wrote no certificate, with no refusal and no
/// downgrade, because the certificate was only attempted at EOF.
#[test]
#[timeout(600_000)]
fn a_strict_unsat_before_a_pop_or_a_later_query_is_certified_per_query() {
    let scoped = "(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(push 1)
(assert (= a b))
(assert (= b c))
(assert (distinct a c))
(check-sat)
(pop 1)
";
    let later_query = format!("{scoped}(check-sat)\n");
    for spelling in STRICT_SPELLINGS {
        for (script, published, withheld) in [
            (scoped, &["unsat"][..], &["unknown"][..]),
            (&later_query, &["unsat", "sat"][..], &["unknown", "sat"][..]),
        ] {
            let run = run_strict_file(script, spelling, DefaultPath::Free);
            assert_eq!(run.lines, published, "{}", run.context);
            assert!(run.success, "{}", run.context);
            assert_certificate_published(&run);
            for path in unpublishable_paths() {
                let run = run_strict_file(script, spelling, path);
                assert_withheld_once(&run, path, withheld);
            }
        }
    }
}

/// The option that requests strict proofs in the script, and its retraction.
pub(super) const STRICT_ON: &str = "(set-option :check-proofs-strict true)\n";
const STRICT_OFF: &str = "(set-option :check-proofs-strict false)\n";

/// One query whose certificate the strict document check refuses for each
/// reason it has, and one it admits: a step the printer renders as `hole`, an
/// `assume` of a rewritten `check-sat-assuming` literal, and a complete one.
fn certificates_strict_judges() -> [(&'static str, String); 3] {
    [
        ("holed by the printer", HOLED_BY_THE_PRINTER.to_string()),
        (
            "assumes a rewritten literal",
            format!("{ASSUMING_PREFIX}(check-sat-assuming ((not (distinct a b))))\n"),
        ),
        ("complete", COMPLETE_CERTIFICATE.to_string()),
    ]
}

/// An option set AFTER a `check-sat` applies to later queries only, so it
/// does not judge the certificate of the query answered before it: that
/// query's `unsat` and its default certificate are exactly what the same run
/// without the option publishes, on every invocation that publishes one.
///
/// Measured on the round-0 head of this fix (e0f9987c2): the hold-back, the
/// certificate's posture and the strict document check judged the query under
/// the request recorded when it was answered, but the screen and the check on
/// the written bytes re-read the LIVE option at EOF. A holed certificate, or
/// one assuming a rewritten literal, printed `unsat`, `end` and then failed
/// with exit 1 ("this query's unsat is already published"), leaving a 0-byte
/// `<input>.alethe`, plain and under `--self-check`, `--rigor certified` and
/// `-smt2` alike. Main (7a64c258f) printed `unsat`, `end`, `unknown`: two
/// responses to one `check-sat`, and the same 0-byte file.
#[test]
#[timeout(600_000)]
fn a_strict_option_set_after_a_check_sat_does_not_judge_that_querys_certificate() {
    let invocations: [&[&str]; 4] = [
        &[],
        &["--self-check"],
        &["--rigor", "certified"],
        &["-smt2"],
    ];
    for (name, query) in certificates_strict_judges() {
        for args in invocations {
            let without = run_file(
                name,
                args,
                &format!("{query}(echo \"end\")\n"),
                DefaultPath::Free,
            );
            let late = run_file(
                name,
                args,
                &format!("{query}{STRICT_ON}(echo \"end\")\n"),
                DefaultPath::Free,
            );
            let context = format!("{}\nwithout the option: {}", late.context, without.context);
            assert_eq!(without.lines, ["unsat", "end"], "{context}");
            assert_eq!(late.lines, without.lines, "{context}");
            assert!(late.success, "{context}");
            assert!(
                late.certificate
                    .as_deref()
                    .is_some_and(|d| d.contains("(cl)")),
                "the query's certificate was not published: {context}"
            );
            assert_eq!(
                late.certificate, without.certificate,
                "the late option changed this query's certificate: {context}"
            );
        }
    }
}

/// The strict option toggled mid-script: each query is held back, certified
/// and withheld under the request in force when IT started, and every query
/// gets exactly one response, in command order.
///
/// Measured on main (7a64c258f): the hold-back read the flag alone and the
/// publication posture read the live option at EOF. With the default path
/// occupied or read-only, "off then on" printed `unsat`, `unsat`, `unknown`,
/// and "on then off" and "on then reset" printed `unsat`, `unsat` for a query
/// answered under the option.
#[test]
#[timeout(600_000)]
fn a_strict_option_toggled_mid_script_judges_each_query_under_its_own_request() {
    let off_then_on = format!("{COMPLETE_CERTIFICATE}{STRICT_ON}(check-sat)\n");
    let on_then_off = format!("{STRICT_ON}{COMPLETE_CERTIFICATE}{STRICT_OFF}(check-sat)\n");
    // `(reset)` returns every option to its default, so it retracts the option.
    let on_then_reset = format!("{STRICT_ON}{COMPLETE_CERTIFICATE}(reset)\n{COMPLETE_CERTIFICATE}");
    for path in unpublishable_paths() {
        // The strict second query's certificate cannot be published.
        let run = run_file("off then on", &[], &off_then_on, path);
        assert_withheld_once(&run, path, &["unsat", "unknown"]);
        // The strict first query's cannot; the second's is optional.
        let run = run_file("on then off", &[], &on_then_off, path);
        assert_withheld_once(&run, path, &["unknown", "unsat"]);
        let run = run_file("on then reset", &[], &on_then_reset, path);
        assert_withheld_once(&run, path, &["unknown", "unsat"]);
    }
    for script in [&off_then_on, &on_then_off, &on_then_reset] {
        let run = run_file("toggled", &[], script, DefaultPath::Free);
        assert_eq!(run.lines, ["unsat", "unsat"], "{}", run.context);
        assert!(run.success, "{}", run.context);
        assert_certificate_published(&run);
    }
    // A holed certificate is refused for the query the option was in force
    // for, and only that one.
    let holed_then_strict = format!("{HOLED_BY_THE_PRINTER}{STRICT_ON}(check-sat)\n");
    let run = run_file("holed, then on", &[], &holed_then_strict, DefaultPath::Free);
    assert_eq!(run.lines, ["unsat", "unknown"], "{}", run.context);
    assert!(
        run.context
            .contains("(:reason-unknown (incomplete proof-trusted))"),
        "{}",
        run.context
    );
    assert!(run.success, "{}", run.context);
}

/// A second refutation for one run. It shares no symbol with
/// [`COMPLETE_CERTIFICATE`], so a certificate shows which query it certifies.
const OTHER_REFUTATION: &str = "(set-logic QF_UF)
(declare-sort V 0)
(declare-const p V)
(declare-const q V)
(assert (= p q))
(assert (distinct q p))
(check-sat)
";

/// One default certificate per run, seen through `(reset)`. A strict query's
/// certificate is published before its `unsat` is, so it keeps
/// `<input>.alethe`; AY never replaces a file, so a later query has none. The
/// later query is not strict under the option, which `(reset)` retracts: its
/// `unsat` stands, and the warning says the file is this run's certificate for
/// an earlier query. Under the flag it is strict too, so it is `unknown`.
/// Without strict proofs the file certifies the last `unsat`, as before.
///
/// Measured on main db768acbd: with the option the file certified the query
/// after the reset and the strict query had no certificate; under the flag
/// the later query was `unknown` because the file "could not be published:
/// File exists", which did not say whose file it was.
#[test]
#[timeout(600_000)]
fn the_first_strict_querys_certificate_keeps_the_default_path_through_a_reset() {
    let reset = "(reset)\n";
    let first = "(assume t0 (= a b))";
    let later = "(= p q)";
    let mine = "was already written by this run for an earlier query";
    let by_option = format!("{STRICT_ON}{COMPLETE_CERTIFICATE}{reset}{OTHER_REFUTATION}");
    let run = run_file("option, reset", &[], &by_option, DefaultPath::Free);
    let context = &run.context;
    assert_eq!(run.lines, ["unsat", "unsat"], "{context}");
    assert!(run.success, "{context}");
    assert_certificate_published(&run);
    let certificate = run.certificate.as_deref().unwrap_or_default();
    assert!(
        certificate.contains(first) && !certificate.contains(later),
        "{context}"
    );
    assert!(context.contains(mine), "{context}");

    let unsat_twice = format!("{COMPLETE_CERTIFICATE}{reset}{OTHER_REFUTATION}");
    let run = run_file(
        "flag, reset",
        &["--strict-proofs"],
        &unsat_twice,
        DefaultPath::Free,
    );
    let context = &run.context;
    assert_eq!(run.lines, ["unsat", "unknown"], "{context}");
    assert!(context.contains(mine), "{context}");
    let certificate = run.certificate.as_deref().unwrap_or_default();
    assert!(
        certificate.contains(first) && !certificate.contains(later),
        "{context}"
    );

    let run = run_file("not strict, reset", &[], &unsat_twice, DefaultPath::Free);
    let context = &run.context;
    assert_eq!(run.lines, ["unsat", "unsat"], "{context}");
    let certificate = run.certificate.as_deref().unwrap_or_default();
    assert!(
        certificate.contains(later) && !certificate.contains(first),
        "{context}"
    );
    assert!(!context.contains(mine), "{context}");
}
