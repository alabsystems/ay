// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A surface verdict is never `Supported` for a pair pinned Carcara cannot
//! accept for a reason outside the proof's steps: a problem its parser
//! refuses, or a step only one of AY's gate invocations accepts — the
//! canonical `carcara check -- PROOF PROBLEM` and the older
//! `--expand-let-bindings`.
//!
//! REGRESSIONS (measured 2026-09-30 at c57bd8481, carcara 1.1.0 git 9a352ee):
//!
//! * `benchmarks/smt/QF_LIA/system_01.smt2` (also `system_10`, `system_15`)
//!   assert a one-argument `+`. AY answered `unsat`, the surface said
//!   `Supported`, and pinned Carcara stopped at the PROBLEM in both
//!   invocations: `parser error: expected at least 2 arguments, got 1`.
//!   `Unsupported`, naming the application, since 56f030d09.
//! * `benchmarks/smt/QF_BV_extract_concat/ext_con_004_001_0016.smt2` asserts a
//!   `let`. AY's document eliminates it with `:rule let`: `valid` in the
//!   canonical invocation, and under `--expand-let-bindings` `checking failed
//!   on step 't0.l' with rule 'let'`, because the flag expands the `let`
//!   before the rule sees it. Now `WithoutLetExpansion`.
//!
//! NEGATIVE CONTROLS: each standard-arity twin, and a `let`-free twin, stays
//! `Supported` and is a literal `valid` in both invocations.

use super::{
    exact_carcara_verdict, parse, refuse_pinned_carcara_misjudgments, require_carcara_or_skip,
    workspace_root, CarcaraSurface, Executor, Logic, Solver, StrictProofVerdict,
};
use ntest::timeout;
use std::fmt::Write as _;
use std::path::Path;

/// The three measured QF_LIA files and, for each, the rewrite that gives every
/// one-argument `+` in it the standard spelling.
const UNARY_PLUS_FILES: [(&str, &[(&str, &str)]); 3] = [
    ("QF_LIA/system_01.smt2", &[("(+ (* 2 v2))", "(* 2 v2)")]),
    ("QF_LIA/system_10.smt2", &[("(+ (* -1 v0))", "(* -1 v0)")]),
    (
        "QF_LIA/system_15.smt2",
        &[("(+ (* 3 v0))", "(* 3 v0)"), ("(+ (* 5 v1))", "(* 5 v1)")],
    ),
];

/// The smallest problem whose refutation eliminates a `let`.
const LET_ROOTED: &str = "(set-logic QF_UF)
(declare-fun p () Bool)
(declare-fun q () Bool)
(assert (let ((a p)) (and a q)))
(assert (not p))
(check-sat)
";

fn benchmark(relative: &str) -> String {
    std::fs::read_to_string(workspace_root().join("benchmarks/smt").join(relative))
        .unwrap_or_else(|e| panic!("read {relative}: {e}"))
}

/// The problem-scoped document and the surface verdict read with it.
fn certificate(label: &str, problem: &str) -> (String, CarcaraSurface) {
    // The checker reads the file as written; the session must not `(exit)`.
    let mut session = String::new();
    for line in problem.lines().filter(|line| line.trim() != "(exit)") {
        writeln!(&mut session, "{line}").expect("write to String");
    }
    let script = format!("(set-option :produce-proofs true)\n{session}");
    let commands = parse(&script).unwrap_or_else(|e| panic!("{label}: {e}"));
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    assert_eq!(outputs.last().map(String::as_str), Some("unsat"), "{label}");
    let (document, surface) = exec
        .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
        .unwrap_or_else(|| panic!("{label}: no retained proof"))
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(
        !document.contains(":rule hole") && !document.contains(":rule trust"),
        "{label}: {document}"
    );
    (document, surface)
}

/// Pinned Carcara's verdict in the second gate invocation.
fn expanding_carcara_verdict(carcara: &Path, problem: &str, proof: &str) -> (bool, String) {
    refuse_pinned_carcara_misjudgments("expanding Carcara verdict", problem, proof);
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write exact problem");
    std::fs::write(&proof_path, proof).expect("write exact proof");
    let output = std::process::Command::new(carcara)
        .args(["check", "--no-color", "--expand-let-bindings", "--"])
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run pinned Carcara");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let diagnostic = format!(
        "status={:?}; stdout={}; stderr={}",
        output.status.code(),
        stdout.trim(),
        String::from_utf8_lossy(&output.stderr).trim()
    );
    (
        output.status.success() && stdout.trim() == "valid",
        diagnostic,
    )
}

/// Both invocations' verdicts, or `None` without a checker.
fn both_verdicts(
    carcara: Option<&Path>,
    problem: &str,
    proof: &str,
) -> Option<((bool, String), (bool, String))> {
    let carcara = carcara?;
    Some((
        exact_carcara_verdict(carcara, problem, proof),
        expanding_carcara_verdict(carcara, problem, proof),
    ))
}

#[test]
#[timeout(120_000)]
fn a_problem_pinned_carcara_cannot_parse_is_never_a_supported_certificate() {
    let carcara = require_carcara_or_skip();
    for (relative, rewrites) in UNARY_PLUS_FILES {
        let problem = benchmark(relative);
        let (document, surface) = certificate(relative, &problem);
        assert!(
            matches!(&surface, CarcaraSurface::Unsupported { reason }
                if reason.contains("`+` is applied to 1 argument")),
            "{relative}: {surface:?}"
        );
        if let Some(((plain, plain_why), (expanding, expanding_why))) =
            both_verdicts(carcara.as_deref(), &problem, &document)
        {
            for (valid, why) in [(plain, plain_why), (expanding, expanding_why)] {
                assert!(
                    !valid && why.contains("expected at least 2 arguments, got 1"),
                    "{relative}: pinned Carcara refuses the problem itself: {why}"
                );
            }
        }

        // NEGATIVE: the standard-arity twin.
        let twin = rewrites
            .iter()
            .fold(problem.clone(), |text, (from, to)| text.replace(from, to));
        assert_ne!(twin, problem, "{relative}: the rewrite applies");
        let (document, surface) = certificate(relative, &twin);
        assert_eq!(surface, CarcaraSurface::Supported, "{relative} twin");
        if let Some(((plain, plain_why), (expanding, expanding_why))) =
            both_verdicts(carcara.as_deref(), &twin, &document)
        {
            assert!(plain, "{relative} twin: {plain_why}\n{document}");
            assert!(expanding, "{relative} twin: {expanding_why}\n{document}");
        }
    }
}

#[test]
#[timeout(120_000)]
fn a_let_rule_certificate_names_the_invocation_that_accepts_it() {
    let carcara = require_carcara_or_skip();
    let measured = benchmark("QF_BV_extract_concat/ext_con_004_001_0016.smt2");
    for (label, problem) in [
        ("let-rooted", LET_ROOTED),
        ("ext_con_004_001_0016", measured.as_str()),
    ] {
        let (document, surface) = certificate(label, problem);
        assert!(document.contains(":rule let)"), "{label}: {document}");
        assert_eq!(surface, CarcaraSurface::WithoutLetExpansion, "{label}");
        if let Some(((plain, plain_why), (expanding, expanding_why))) =
            both_verdicts(carcara.as_deref(), problem, &document)
        {
            assert!(
                plain,
                "{label}: the canonical invocation accepts it: {plain_why}"
            );
            assert!(
                !expanding && expanding_why.contains("with rule 'let'"),
                "{label}: `--expand-let-bindings` refuses exactly the let step: {expanding_why}"
            );
        }
    }

    // NEGATIVE: the `let`-free twin.
    let twin = LET_ROOTED.replace("(let ((a p)) (and a q))", "(and p q)");
    let (document, surface) = certificate("let-free", &twin);
    assert!(!document.contains("(let "), "{document}");
    assert_eq!(surface, CarcaraSurface::Supported);
    if let Some(((plain, plain_why), (expanding, expanding_why))) =
        both_verdicts(carcara.as_deref(), &twin, &document)
    {
        assert!(plain, "{plain_why}");
        assert!(expanding, "{expanding_why}");
    }
}

/// The library artifact discloses what the executor's paired export does.
#[test]
#[timeout(120_000)]
fn the_unsat_artifact_carries_both_disclosures() {
    for (label, logic, problem, authored, expected) in [
        (
            "unary-plus",
            Logic::QfLia,
            benchmark("QF_LIA/system_01.smt2"),
            "(+ (* 2 v2))",
            None,
        ),
        (
            "let-rooted",
            Logic::QfUf,
            LET_ROOTED.to_string(),
            "(let ((a p)) (and a q))",
            Some(CarcaraSurface::WithoutLetExpansion),
        ),
    ] {
        let mut solver = Solver::try_new(logic).expect("solver");
        solver.set_produce_proofs(true);
        // The solver owns the logic and the query.
        let mut declarations = String::new();
        for line in problem.lines().filter(|line| {
            !["(set-logic", "(check-sat", "(exit"]
                .iter()
                .any(|command| line.starts_with(command))
        }) {
            writeln!(&mut declarations, "{line}").expect("write to String");
        }
        solver
            .parse_smtlib2(&declarations)
            .expect("parse the fixture");
        assert!(solver.check_sat().is_unsat(), "{label}");
        let artifact = solver
            .export_last_unsat_artifact()
            .unwrap_or_else(|| panic!("{label}: a strict-checked refutation publishes"));
        // The exact problem the artifact pairs its document with keeps the
        // authored spelling, so the verdict describes that pair too.
        let transport = artifact
            .alethe_problem_smt2
            .as_deref()
            .unwrap_or_else(|| panic!("{label}: the artifact carries its exact problem"));
        assert!(transport.contains(authored), "{label}: {transport}");
        assert!(
            matches!(artifact.strict_verdict, StrictProofVerdict::Verified(_)),
            "{label}: {:?}",
            artifact.strict_verdict
        );
        match expected {
            Some(surface) => assert_eq!(artifact.carcara_surface, surface, "{label}"),
            None => assert!(
                matches!(&artifact.carcara_surface, CarcaraSurface::Unsupported { reason }
                    if reason.contains("`+` is applied to 1 argument")),
                "{label}: {:?}",
                artifact.carcara_surface
            ),
        }
    }
}

/// The negative-literal shorthand: an unquoted `-16` is the numeral to z3,
/// cvc5, pinned Carcara and AY's parser alike.
const NEGATIVE_SHORTHAND: &str = "(set-logic QF_LIA)
(declare-fun x () Int)
(assert (<= x -16))
(assert (<= (* -1 x) 15))
(check-sat)
";

/// REGRESSION (measured 2026-10-01 on origin/main 7d78f77dcd): b02bbed887
/// made `quote_symbol` quote a name that reads as a signed number, and the
/// authored echo spelled the shorthand `-16` as the SYMBOL `|-16|`. Every
/// `assume` holding a negative literal stopped matching the problem for
/// pinned Carcara, and `system_01`'s native SOS step, whose literals
/// `la_generic` could no longer read, printed as a `hole` (the failure of
/// `a_problem_pinned_carcara_cannot_parse_is_never_a_supported_certificate`).
///
/// The parser now reads an unquoted `-16` as the numeral and only `|-16|` as
/// the symbol, so the echo prints the one bare and the other quoted. TWIN: a
/// declared `|-16|` beside a bare `-16` — the bare one is still the number,
/// as z3 reads it.
#[test]
#[timeout(120_000)]
fn the_negative_literal_shorthand_is_a_numeral_in_the_certificate() {
    let carcara = require_carcara_or_skip();
    let declared = NEGATIVE_SHORTHAND
        .replace("(declare-fun x ", "(declare-fun |-16| ")
        .replace("(<= x -16)", "(<= |-16| -16)")
        .replace(" x)", " |-16|)");
    for (label, problem, assume) in [
        ("shorthand", NEGATIVE_SHORTHAND, "(<= x -16)"),
        ("declared", declared.as_str(), "(<= |-16| -16)"),
    ] {
        let (document, surface) = certificate(label, problem);
        assert!(
            document
                .lines()
                .any(|line| line.starts_with("(assume ") && line.ends_with(&format!(" {assume})"))),
            "{label}: {document}"
        );
        assert!(!document.contains(":rule hole"), "{label}: {document}");
        assert_eq!(surface, CarcaraSurface::Supported, "{label}");
        if let Some(((plain, plain_why), (expanding, expanding_why))) =
            both_verdicts(carcara.as_deref(), problem, &document)
        {
            assert!(plain, "{label}: {plain_why}\n{document}");
            assert!(expanding, "{label}: {expanding_why}\n{document}");
        }
    }
    // The measured files: no negative literal of theirs is quoted.
    for (relative, _) in UNARY_PLUS_FILES {
        let (document, _) = certificate(relative, &benchmark(relative));
        assert!(!document.contains("|-"), "{relative}: {document}");
    }
}
