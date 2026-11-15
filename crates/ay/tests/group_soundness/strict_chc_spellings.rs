// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The in-script `(set-option :check-proofs-strict true)` is a strict request
//! on HORN (CHC) scripts too.
//!
//! Measured on 84c52bacd: with `--strict-proofs`, the CHC runner ground-checks
//! an UNSAFE counterexample before it publishes `unsat`, re-discharges a SAFE
//! invariant before it publishes `sat`, and refuses `--stdin` for want of a
//! persistent certificate. With only the in-script option on the same scripts,
//! none of the three ran: the file route and `--stdin` published `unsat`/`sat`
//! and the "strict trace check"/"strict checked replay" lines never appeared.
//! Every one of those gates read only the command-line flag.

use ntest::timeout;
use std::process::Command;

use super::strict_admission_routes::StrictSpelling;
use super::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};
use crate::spawn::OutputTimeout;

const STRICT_OPTION: &str = "(set-option :check-proofs-strict true)";

/// Reachable error: `inv` holds at 0 and is closed under `+ 1`, so `x > 5`
/// is reached. UNSAFE, published as `unsat`.
const UNSAFE_HORN: &str = "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (inv x) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
";

/// Unreachable error: `inv` stops at 5. SAFE, published as `sat`.
const SAFE_HORN: &str = "(set-logic HORN)
(declare-fun inv (Int) Bool)
(assert (forall ((x Int)) (=> (= x 0) (inv x))))
(assert (forall ((x Int)) (=> (and (inv x) (< x 5)) (inv (+ x 1)))))
(assert (forall ((x Int)) (=> (and (inv x) (> x 5)) false)))
(check-sat)
";

/// Printed only when STEP D (the UNSAFE ground check) ran and passed.
const UNSAFE_GATE_RAN: &str =
    "CHC strict trace check: UNSAFE counterexample independently ground-checked";
/// Printed only when STEP C (the SAFE checked replay) ran and passed.
const SAFE_GATE_RAN: &str =
    "CHC strict checked replay: SAFE certificate independently re-discharged";
/// The refusal of a strict CHC run with no persistent certificate.
const NO_CERTIFICATE_REFUSAL: &str = "requires a persistent native CHC certificate";

/// Where the option sits in the script.
#[derive(Clone, Copy, Debug)]
enum Placement {
    /// Before `(set-logic HORN)`: on the incremental route the executor sees
    /// it, not the CHC runner.
    BeforeLogic,
    /// After `(set-logic HORN)`: inside the CHC text itself.
    AfterLogic,
}

fn with_option(script: &str, placement: Placement) -> String {
    match placement {
        Placement::BeforeLogic => format!("{STRICT_OPTION}\n{script}"),
        Placement::AfterLogic => script.replacen(
            "(set-logic HORN)\n",
            &format!("(set-logic HORN)\n{STRICT_OPTION}\n"),
            1,
        ),
    }
}

/// How strictness is (or is not) asked for.
#[derive(Clone, Copy, Debug)]
enum Request {
    Strict(StrictSpelling, Placement),
    NotStrict,
}

impl Request {
    const ALL_STRICT: [Request; 3] = [
        Request::Strict(StrictSpelling::CommandLine, Placement::BeforeLogic),
        Request::Strict(StrictSpelling::InScript, Placement::BeforeLogic),
        Request::Strict(StrictSpelling::InScript, Placement::AfterLogic),
    ];

    fn script(self, script: &str) -> String {
        match self {
            Request::Strict(StrictSpelling::InScript, placement) => with_option(script, placement),
            Request::Strict(StrictSpelling::CommandLine, _) | Request::NotStrict => {
                script.to_string()
            }
        }
    }

    fn flag(self) -> &'static [&'static str] {
        match self {
            Request::Strict(StrictSpelling::CommandLine, _) => &["--strict-proofs"],
            _ => &[],
        }
    }
}

/// The HORN input routes.
#[derive(Clone, Copy, Debug)]
enum HornRoute {
    /// `ay FILE`: auto-detected HORN, synthesized `FILE.chccert`.
    File,
    /// `ay --chc FILE`: the forced CHC portfolio route.
    ForcedChcFile,
    /// `ay FILE --proof FILE.chccert`: an explicit certificate.
    FileWithProof,
    /// `ay --stdin`: no persistent certificate is possible.
    Stdin,
    /// `ay --incremental`: no persistent certificate is possible.
    Incremental,
}

const CERTIFYING_ROUTES: [HornRoute; 3] = [
    HornRoute::File,
    HornRoute::ForcedChcFile,
    HornRoute::FileWithProof,
];
const STREAM_ROUTES: [HornRoute; 2] = [HornRoute::Stdin, HornRoute::Incremental];

struct HornOutcome {
    success: bool,
    verdicts: Vec<String>,
    stderr: String,
    context: String,
}

fn run_horn(route: HornRoute, request: Request, script: &str) -> HornOutcome {
    let script = request.script(script);
    let dir = tempfile::tempdir().expect("tempdir");
    let input = dir.path().join("horn.smt2");
    let mut command = Command::new(env!("CARGO_BIN_EXE_ay"));
    command.args(request.flag());
    let output = match route {
        HornRoute::File | HornRoute::ForcedChcFile | HornRoute::FileWithProof => {
            std::fs::write(&input, &script).expect("write HORN input");
            if matches!(route, HornRoute::ForcedChcFile) {
                command.arg("--chc");
            }
            if matches!(route, HornRoute::FileWithProof) {
                command
                    .arg("--proof")
                    .arg(dir.path().join("explicit.chccert"));
            }
            command.arg(&input).output_timeout(QUERY_TIMEOUT)
        }
        HornRoute::Stdin => command
            .arg("--stdin")
            .output_timeout_with_stdin(script.as_bytes(), QUERY_TIMEOUT),
        HornRoute::Incremental => command
            .arg("--incremental")
            .output_timeout_with_stdin(script.as_bytes(), QUERY_TIMEOUT),
    }
    .unwrap_or_else(|e| panic!("{route:?} {request:?}: run ay: {e}"));
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    HornOutcome {
        success: output.status.success(),
        verdicts: verdict_lines(&stdout),
        context: format!(
            "{route:?} {request:?} (exit {:?})\nscript:\n{script}\nstdout:\n{stdout}\nstderr:\n{stderr}",
            output.status
        ),
        stderr,
    }
}

/// On every route that can certify, both spellings run the UNSAFE ground
/// check and the SAFE re-discharge before the verdict is published; with
/// neither spelling, neither gate runs (so the gate lines discriminate).
#[test]
#[timeout(600_000)]
fn the_in_script_strict_option_runs_the_chc_strict_gates_on_every_certifying_route() {
    for route in CERTIFYING_ROUTES {
        for (script, verdict, gate_line) in [
            (UNSAFE_HORN, "unsat", UNSAFE_GATE_RAN),
            (SAFE_HORN, "sat", SAFE_GATE_RAN),
        ] {
            for request in Request::ALL_STRICT {
                let outcome = run_horn(route, request, script);
                let context = &outcome.context;
                assert!(outcome.success, "{context}");
                assert_eq!(outcome.verdicts, [verdict], "{context}");
                assert!(
                    outcome.stderr.contains(gate_line),
                    "the strict CHC gate did not run before the verdict: {context}"
                );
            }

            let outcome = run_horn(route, Request::NotStrict, script);
            let context = &outcome.context;
            assert_eq!(outcome.verdicts, [verdict], "{context}");
            assert!(
                !outcome.stderr.contains(UNSAFE_GATE_RAN)
                    && !outcome.stderr.contains(SAFE_GATE_RAN),
                "a strict CHC gate ran with no strict request: {context}"
            );
        }
    }
}

/// On the stream routes a strict CHC run has no persistent certificate, so
/// both spellings refuse before solving, name the spelling, and print no
/// verdict. Without a strict request the same scripts are decided.
#[test]
#[timeout(600_000)]
fn the_in_script_strict_option_refuses_a_chc_stream_without_a_certificate() {
    for route in STREAM_ROUTES {
        for (script, verdict) in [(UNSAFE_HORN, "unsat"), (SAFE_HORN, "sat")] {
            for request in Request::ALL_STRICT {
                let outcome = run_horn(route, request, script);
                let context = &outcome.context;
                assert!(!outcome.success, "{context}");
                assert!(
                    outcome.verdicts.is_empty(),
                    "a strict CHC stream published a verdict with no certificate: {context}"
                );
                assert!(outcome.stderr.contains(NO_CERTIFICATE_REFUSAL), "{context}");
                let spelling = match request {
                    Request::Strict(StrictSpelling::CommandLine, _) => "--strict-proofs",
                    _ => STRICT_OPTION,
                };
                assert!(
                    outcome
                        .stderr
                        .contains(&format!("Error: {spelling} requires")),
                    "the refusal must name the strict spelling used: {context}"
                );
            }

            let outcome = run_horn(route, Request::NotStrict, script);
            let context = &outcome.context;
            assert_eq!(outcome.verdicts, [verdict], "{context}");
            assert!(
                !outcome.stderr.contains(NO_CERTIFICATE_REFUSAL),
                "{context}"
            );
        }
    }
}
