// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A strict `unsat` after an `(error ...)` earlier in the same problem. No
//! certificate may embed source that failed continued execution, so the
//! default certificate (`<input>.alethe`) cannot be published for it: under
//! strict proofs, in either spelling, the query's one response is `unknown`,
//! in command order, and the rest of the script still runs.

use ntest::timeout;

use super::strict_admission_routes::COMPLETE_CERTIFICATE;
use super::strict_default_publication::{
    assert_certificate_published, run_file, run_strict_file, DefaultPath, FileRun, STRICT_ON,
    STRICT_SPELLINGS,
};

/// Commands that print an `(error ...)` and leave the problem whole, so the
/// query after them is still `unsat`.
///
/// `get-assignment` and `eval` with no model were not recorded as errors on
/// main db768acbd: each printed an unpositioned error, the run exited 0, and
/// the strict `unsat` after it was published with its certificate, under
/// either spelling. z3 exits 1 for both.
const TRIGGERS: [(&str, &str); 6] = [
    ("a duplicate declaration", "(declare-const a U)\n"),
    ("an unknown option", "(set-option :no-such-key 1)\n"),
    ("get-model before any check-sat", "(get-model)\n"),
    ("get-value before any check-sat", "(get-value (a))\n"),
    ("get-assignment before any check-sat", "(get-assignment)\n"),
    ("eval before any check-sat", "(eval a)\n"),
];

/// The complete refutation with `trigger` just before its `check-sat`, and a
/// marker after it.
fn after(trigger: &str) -> String {
    COMPLETE_CERTIFICATE.replace(
        "(check-sat)\n",
        &format!("{trigger}(check-sat)\n(echo \"end\")\n"),
    )
}

/// The stdout responses in order, an `(error ...)` (which may span lines, as
/// an unknown option's does) as `(error)`.
fn responses(run: &FileRun) -> Vec<String> {
    let mut responses = Vec::new();
    let mut inside_error = false;
    for line in &run.lines {
        if inside_error {
            inside_error = !line.ends_with("\")");
            continue;
        }
        if line.starts_with("(error ") {
            inside_error = !line.ends_with("\")");
            responses.push("(error)".to_string());
            continue;
        }
        responses.push(line.clone());
    }
    responses
}

/// The cause `unknown` and a required certificate's failure both name.
const CAUSE: &str = "a command earlier in this problem failed";

/// Checks a run whose strict `unsat` after an error is withheld: the expected
/// responses, the reason on the record, and exit 1 only for the printed error
/// (z3 exits 1 when it printed one), never a publication failure.
fn assert_withheld_after_error(run: &FileRun, expected: &[&str]) {
    let context = &run.context;
    assert_eq!(responses(run), expected, "{context}");
    assert!(
        context.contains("(:reason-unknown (incomplete proof-publication-failed))"),
        "the withheld verdict must say why: {context}"
    );
    assert!(context.contains(CAUSE), "{context}");
    assert!(
        !context.contains("required UNSAT publication failed"),
        "{context}"
    );
    assert_eq!(run.code, Some(1), "{context}");
}

/// A strict `unsat` after an `(error ...)` is ONE `unknown`, and the script
/// goes on, whichever spelling asked for strict proofs.
///
/// Measured on base aba6406be: under `--strict-proofs` each of these scripts
/// printed the error and nothing else, and exited 1 with "Error: required
/// UNSAT publication failed: SMT UNSAT artifacts were not prepared before
/// publication" (the held `unsat` reached publication with no transaction
/// prepared). With only the in-script option it printed `unsat` with no
/// certificate, breaking the strict promise. The round-1 head of
/// `fix/strict-option-single-answer` (37163fc0f) held the option's `unsat`
/// back too, and so failed the option exactly as the flag.
#[test]
#[timeout(600_000)]
fn a_strict_unsat_after_an_error_is_one_unknown_and_the_script_goes_on() {
    for (name, trigger) in TRIGGERS {
        let script = after(trigger);
        for spelling in STRICT_SPELLINGS {
            let run = run_strict_file(&script, spelling, DefaultPath::Free);
            let context = format!("{name}: {}", run.context);
            assert_withheld_after_error(&run, &["(error)", "unknown", "end"]);
            assert_eq!(run.certificate, None, "{context}");
        }
    }
}

/// Without strict proofs the same `unsat` stands, with no certificate: the
/// default certificate is optional. A no-change guard for the first four
/// triggers: base prints the same. For `get-assignment` and `eval` base exited
/// 0 and wrote the certificate (see [`TRIGGERS`]).
#[test]
#[timeout(600_000)]
fn without_strict_proofs_an_unsat_after_an_error_stands() {
    for (name, trigger) in TRIGGERS {
        let run = run_file(name, &[], &after(trigger), DefaultPath::Free);
        let context = &run.context;
        assert_eq!(responses(&run), ["(error)", "unsat", "end"], "{context}");
        assert_eq!(run.certificate, None, "{context}");
        assert_eq!(run.code, Some(1), "{context}");
    }
}

/// The incremental pattern: `(get-model)` after an `unsat`, then later
/// queries. The first query is published with its certificate; the strict
/// `unsat` after the error is `unknown`; the `sat` after the `pop` stands.
///
/// Measured on base aba6406be: `unsat`, the error, `unsat`, `sat`, `end` with
/// only the option; with the flag the run stopped after the error with "SMT
/// UNSAT artifacts were not prepared before publication". The round-1 head
/// failed the option the same way.
#[test]
#[timeout(600_000)]
fn a_strict_unsat_after_get_model_errors_in_an_incremental_script_is_unknown() {
    let incremental = "(set-logic QF_UF)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const c U)
(push 1)
(assert (= a b))
(assert (= b c))
(assert (distinct a c))
(check-sat)
(get-model)
(check-sat)
(pop 1)
(check-sat)
(echo \"end\")
";
    for spelling in STRICT_SPELLINGS {
        let run = run_strict_file(incremental, spelling, DefaultPath::Free);
        assert_withheld_after_error(&run, &["unsat", "(error)", "unknown", "sat", "end"]);
        assert_certificate_published(&run);
    }
    let run = run_file("not strict", &[], incremental, DefaultPath::Free);
    assert_eq!(
        responses(&run),
        ["unsat", "(error)", "unsat", "sat", "end"],
        "{}",
        run.context
    );
}

/// `(reset)` starts a new problem, which may carry artifacts again: its strict
/// `unsat` is published with its certificate. A no-change guard: base passes
/// it too; it pins that the withholding above ends with the problem.
#[test]
#[timeout(600_000)]
fn after_a_reset_a_strict_unsat_is_published_with_its_certificate() {
    for (name, flag, option) in STRICT_SPELLINGS {
        // `(reset)` retracts the in-script option, so it is set again after.
        let again = if option { STRICT_ON } else { "" };
        let script = format!("(get-model)\n(reset)\n{again}{COMPLETE_CERTIFICATE}");
        let args: &[&str] = if flag { &["--strict-proofs"] } else { &[] };
        let run = run_file(name, args, &script, DefaultPath::Free);
        assert_eq!(responses(&run), ["(error)", "unsat"], "{}", run.context);
        assert_eq!(run.code, Some(1), "{}", run.context);
        assert_certificate_published(&run);
    }
}

/// A required certificate (`--proof FILE`, `--proof-artifact`,
/// `--emit-firewall-lean`) keeps its posture after an error: the run fails
/// loudly at that `unsat`, with no response to it or to the rest of the
/// script, as for any required certificate it cannot publish, and the error
/// names the request, its own target and the cause. So the one-response
/// promise above is the default certificate's; a required certificate fails
/// the run instead.
///
/// Measured on base db768acbd for all three requests, with and without
/// `--strict-proofs` (and on aba6406be for `--proof`): the same stdout and
/// exit 1, with the internal "SMT UNSAT artifacts were not prepared before
/// publication" as the only message.
#[test]
#[timeout(600_000)]
fn a_required_certificate_after_an_error_fails_naming_the_cause() {
    let out = tempfile::tempdir().expect("tempdir");
    let proof = out.path().join("explicit.alethe");
    let envelope = out.path().join("artifact.json");
    let lemmas = out.path().join("lemmas");
    let [proof_arg, envelope_arg, lemmas_arg] =
        [&proof, &envelope, &lemmas].map(|path| path.to_str().expect("utf-8 path"));
    let requests: [(&[&str], String); 3] = [
        (
            &["--proof", proof_arg],
            format!("--proof requires {proof_arg}"),
        ),
        (
            &["--proof-artifact", envelope_arg],
            format!("--proof-artifact {envelope_arg} requires the certificate "),
        ),
        (
            &["solve", "--emit-firewall-lean", lemmas_arg],
            format!("--emit-firewall-lean {lemmas_arg} requires the certificate "),
        ),
    ];
    for (request, names) in &requests {
        for strict in [&[][..], &["--strict-proofs"][..]] {
            let args = [request, strict].concat();
            let run = run_file(
                "required",
                &args,
                &after("(get-model)\n"),
                DefaultPath::Free,
            );
            let context = &run.context;
            assert_eq!(responses(&run), ["(error)"], "{context}");
            assert_eq!(run.code, Some(1), "{context}");
            assert!(context.contains(names.as_str()), "{context}");
            assert!(context.contains(CAUSE), "{context}");
            assert!(!context.contains("were not prepared"), "{context}");
            assert_eq!(run.certificate, None, "{context}");
            for path in [&proof, &envelope, &lemmas] {
                assert!(!path.exists(), "{} was written: {context}", path.display());
            }
        }
    }
}
