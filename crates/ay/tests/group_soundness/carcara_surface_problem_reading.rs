// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `carcara_surface=supported` on the certificate line is never printed for a
//! pair pinned Carcara cannot accept for a reason outside the proof's steps:
//! a problem its parser refuses, or a step only one of the invocations AY's
//! gates have used accepts — the canonical `carcara check -- PROOF PROBLEM`
//! and `--expand-let-bindings`. `supported` is a claim about spellings; an
//! `assume` that is not the problem's own is `foreign_assumes=yes`.
//!
//! REGRESSIONS (measured 2026-09-30 at c57bd8481, carcara 1.1.0 git 9a352ee):
//!
//! * `benchmarks/smt/QF_LIA/system_01.smt2` (also `system_10`, `system_15`)
//!   asserts `(<= (+ (* 2 v2)) -16)`, a one-argument `+`. `ay --proof`
//!   answered `unsat` with `trust_free=yes carcara_surface=supported`, and
//!   pinned Carcara stopped at the PROBLEM in either invocation: `parser
//!   error: expected at least 2 arguments, got 1`. Since 56f030d09 the line
//!   says `carcara_surface=unsupported` and names the application, and
//!   `--strict-proofs`, which claims an external check, withholds the `unsat`.
//! * `(let () p)`, `(forall () p)`, `(exists () p)` and `(! p)` in an
//!   assertion the refutation never uses: AY reads them, pinned Carcara
//!   refuses the problem (`expected non-empty sequence`), and at b9c6ada1e the
//!   line still said `trust_free=yes carcara_surface=supported` and
//!   `--strict-proofs` published the `unsat`. Now `unsupported`.
//! * `benchmarks/smt/QF_BV_extract_concat/ext_con_004_001_0016.smt2` asserts a
//!   `let`, which the document eliminates with `:rule let`: `valid` in the
//!   canonical invocation, and under `--expand-let-bindings` `checking failed
//!   on step 't0.l' with rule 'let'`. No spelling is valid in both, so the
//!   line now says `carcara_surface=without-let-expansion` and names the
//!   invocation; `--strict-proofs` still publishes it.
//!
//! NEGATIVE CONTROLS: the standard-arity twins, a non-empty-binder twin and a
//! `let`-free twin stay `supported` and are a literal `valid` in both
//! invocations. The replays are skipped with a note without `carcara`
//! (`CARCARA_PATH`, or `carcara` on `PATH`).

use ntest::timeout;
use std::path::PathBuf;
use std::process::Command;

use crate::alethe_dialect_disclosure::pinned_carcara_verdict_in;
use crate::spawn::OutputTimeout;
use crate::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};

const EXPAND: &[&str] = &["--expand-let-bindings"];

/// Each one-argument-`+` file and the rewrite that spells every such `+`
/// the standard way.
const UNARY_PLUS_FILES: [(&str, &[(&str, &str)]); 3] = [
    ("QF_LIA/system_01.smt2", &[("(+ (* 2 v2))", "(* 2 v2)")]),
    ("QF_LIA/system_10.smt2", &[("(+ (* -1 v0))", "(* -1 v0)")]),
    (
        "QF_LIA/system_15.smt2",
        &[("(+ (* 3 v0))", "(* 3 v0)"), ("(+ (* 5 v1))", "(* 5 v1)")],
    ),
];

const LET_FILE: &str = "QF_BV_extract_concat/ext_con_004_001_0016.smt2";

/// The binder of `ext_con_004_001_0016`'s one `let`.
const LET_BINDINGS: &str = "(let ((?v_0 ((_ extract 15 4) a)) (?v_1 ((_ extract 11 0) a))) ";

struct Run {
    verdicts: Vec<String>,
    certificate: Option<String>,
    stderr: String,
    problem: PathBuf,
    proof: PathBuf,
    _dir: tempfile::TempDir,
}

fn benchmark(relative: &str) -> String {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("../../benchmarks/smt")
        .join(relative);
    std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()))
}

fn run(script: &str, flags: &[&str]) -> Run {
    let dir = tempfile::tempdir().expect("tempdir");
    let problem = dir.path().join("query.smt2");
    let proof = dir.path().join("query.alethe");
    std::fs::write(&problem, script).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("-smt2")
        .arg(&problem)
        .args(flags)
        .arg("--proof")
        .arg(&proof)
        .args(["--proof-format", "alethe"])
        .output_timeout(QUERY_TIMEOUT)
        .expect("ay answers");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    let certificate = stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.certificate "))
        .map(str::to_string);
    Run {
        verdicts: verdict_lines(&stdout),
        certificate,
        stderr,
        problem,
        proof,
        _dir: dir,
    }
}

/// A published, hole-free certificate's line.
fn published(run: &Run, context: &str) -> String {
    assert_eq!(run.verdicts, ["unsat"], "{context}\n{}", run.stderr);
    let certificate = run
        .certificate
        .clone()
        .unwrap_or_else(|| panic!("{context}: no certificate line\n{}", run.stderr));
    assert!(
        certificate.contains(" unproved_steps=0 ") && certificate.contains(" trust_free=yes "),
        "{context}: {certificate}"
    );
    certificate
}

/// Both invocations' verdicts (last stdout line, stderr), or `None` without
/// a checker.
fn both_verdicts(run: &Run) -> Option<((String, String), (String, String))> {
    let plain = pinned_carcara_verdict_in(&run.problem, &run.proof, &[])?;
    let expanding = pinned_carcara_verdict_in(&run.problem, &run.proof, EXPAND)?;
    Some((plain, expanding))
}

fn assert_supported_and_valid(run: &Run, context: &str) {
    let certificate = published(run, context);
    assert!(
        certificate.contains(" carcara_surface=supported "),
        "{context}: {certificate}"
    );
    if let Some(((plain, plain_err), (expanding, expanding_err))) = both_verdicts(run) {
        assert_eq!(plain, "valid", "{context}: {plain_err}");
        assert_eq!(expanding, "valid", "{context}: {expanding_err}");
    }
}

#[test]
#[timeout(300_000)]
fn a_problem_pinned_carcara_cannot_parse_is_disclosed_unsupported() {
    for (relative, rewrites) in UNARY_PLUS_FILES {
        let problem = benchmark(relative);
        let default = run(&problem, &[]);
        let certificate = published(&default, relative);
        assert!(
            certificate.contains(" carcara_surface=unsupported "),
            "{relative}: {certificate}"
        );
        assert!(
            default
                .stderr
                .lines()
                .any(|line| line.starts_with("c warning: ")
                    && line.contains("carcara_surface=unsupported")
                    && line.contains("`+` is applied to 1 argument")),
            "{relative}: the warning names the application:\n{}",
            default.stderr
        );
        if let Some(((plain, plain_err), (expanding, expanding_err))) = both_verdicts(&default) {
            for (verdict, stderr) in [(plain, plain_err), (expanding, expanding_err)] {
                assert_ne!(verdict, "valid", "{relative}");
                assert!(
                    stderr.contains("expected at least 2 arguments, got 1"),
                    "{relative}: pinned Carcara refuses the problem itself: {stderr}"
                );
            }
        }
        // `--strict-proofs` claims an external check, so it withholds the
        // verdict and leaves no certificate behind.
        let strict = run(&problem, &["--strict-proofs"]);
        assert_eq!(
            strict.verdicts,
            ["unknown"],
            "{relative}\n{}",
            strict.stderr
        );
        assert_eq!(
            std::fs::metadata(&strict.proof).map_or(0, |metadata| metadata.len()),
            0,
            "{relative}: a withheld verdict left a certificate"
        );

        // NEGATIVE: the standard-arity twin.
        let twin = rewrites
            .iter()
            .fold(problem.clone(), |text, (from, to)| text.replace(from, to));
        assert_ne!(twin, problem, "{relative}: the rewrite applies");
        assert_supported_and_valid(&run(&twin, &[]), &format!("{relative} twin"));
    }
}

#[test]
#[timeout(300_000)]
fn a_let_rule_certificate_names_the_invocation_that_accepts_it() {
    let problem = benchmark(LET_FILE);
    for flags in [&[][..], &["--strict-proofs"][..]] {
        let context = format!("{LET_FILE} {flags:?}");
        let run = run(&problem, flags);
        let certificate = published(&run, &context);
        assert!(
            certificate.contains(" carcara_surface=without-let-expansion "),
            "{context}: {certificate}"
        );
        assert!(
            run.stderr
                .lines()
                .any(|line| line.starts_with("c warning: ")
                    && line.contains("carcara_surface=without-let-expansion")
                    && line.contains("carcara check -- PROOF PROBLEM")
                    && line.contains("--expand-let-bindings")),
            "{context}: the warning names the invocation:\n{}",
            run.stderr
        );
        let proof = std::fs::read_to_string(&run.proof).expect("read the certificate");
        assert!(proof.contains(":rule let)"), "{context}");
        if let Some(((plain, plain_err), (expanding, expanding_err))) = both_verdicts(&run) {
            assert_eq!(plain, "valid", "{context}: {plain_err}");
            assert_ne!(expanding, "valid", "{context}");
            assert!(
                expanding_err.contains("with rule 'let'"),
                "{context}: `--expand-let-bindings` refuses exactly the let step: {expanding_err}"
            );
        }
    }

    // NEGATIVE: the same assertion with its bindings spelled out, and the
    // `let`'s closing parenthesis (the last before `(check-sat)`) dropped.
    let mut twin = problem.replacen(LET_BINDINGS, "", 1);
    let close = twin.find("\n(check-sat)").expect("the query") - 1;
    assert_eq!(twin.remove(close), ')', "{twin}");
    let twin = twin
        .replace("?v_0", "((_ extract 15 4) a)")
        .replace("?v_1", "((_ extract 11 0) a)");
    assert!(!twin.contains("(let ") && !twin.contains("?v_"), "{twin}");
    assert_supported_and_valid(&run(&twin, &[]), &format!("{LET_FILE} let-free twin"));
}

/// A refutation that never reads the assertion written before it.
fn with_unused_assertion(assertion: &str) -> String {
    format!(
        "(set-logic ALL)\n(declare-fun v0 () Int)\n(declare-fun p () Bool)\n{assertion}\n\
         (assert (= (* -3 v0) 40))\n(assert (= (* -3 v0) -44))\n(check-sat)\n"
    )
}

#[test]
#[timeout(300_000)]
fn an_empty_binder_or_attribute_list_is_disclosed_unsupported() {
    for (assertion, reason) in [
        ("(assert (let () p))", "with no binder"),
        ("(assert (forall () p))", "with no binder"),
        ("(assert (let ((a p)) (exists () a)))", "with no binder"),
        ("(assert (! p))", "with no attribute"),
    ] {
        let problem = with_unused_assertion(assertion);
        let default = run(&problem, &[]);
        let certificate = published(&default, assertion);
        assert!(
            certificate.contains(" carcara_surface=unsupported "),
            "{assertion}: {certificate}"
        );
        assert!(
            default
                .stderr
                .lines()
                .any(|line| line.starts_with("c warning: ")
                    && line.contains("carcara_surface=unsupported")
                    && line.contains(reason)),
            "{assertion}: the warning names the construct:\n{}",
            default.stderr
        );
        if let Some(((plain, plain_err), (expanding, expanding_err))) = both_verdicts(&default) {
            for (verdict, stderr) in [(plain, plain_err), (expanding, expanding_err)] {
                assert_ne!(verdict, "valid", "{assertion}");
                assert!(
                    stderr.contains("expected non-empty sequence"),
                    "{assertion}: pinned Carcara refuses the problem itself: {stderr}"
                );
            }
        }
        let strict = run(&problem, &["--strict-proofs"]);
        assert_eq!(
            strict.verdicts,
            ["unknown"],
            "{assertion}\n{}",
            strict.stderr
        );
        assert_eq!(
            std::fs::metadata(&strict.proof).map_or(0, |metadata| metadata.len()),
            0,
            "{assertion}: a withheld verdict left a certificate"
        );
    }

    // NEGATIVE: every list non-empty.
    let twin = with_unused_assertion(
        "(assert (! (let ((a p)) (exists ((y Int)) (or a (= y v0)))) :named n))",
    );
    assert_supported_and_valid(&run(&twin, &[]), "non-empty twin");
}

/// The mirror of the `:rule let` document: an assumed `let` the printer can
/// eliminate on the bridge's certified arm.
///
/// `(let ((a (+ x 1))) (<= a y))`. At 8b4bcfd5a the authored spelling of the
/// assumed root rode every print site, the `la_generic` lemma over it read as
/// `Divergent`, and the query took the native NRA-SOS bundle, whose document
/// `assume`s the EXPANDED `(<= (+ x 1) y)`: the canonical invocation refused
/// that `assume`, `--expand-let-bindings` accepted it, the certificate said
/// `foreign_assumes=yes`, and `--strict-proofs` withheld the verdict. This
/// test pinned that disclosure "until a printer bridged this `let`". The
/// printer now confines a certified `let` spelling to its own `assume`
/// (`ay-proof` `alethe_printer/let_assume_confinement.rs`), so the default
/// route publishes the `:rule let` bridge: `valid` in the canonical
/// invocation, `without-let-expansion`, and `--strict-proofs` publishes it.
///
/// NEGATIVE: `(+ 1 x)` substitutes to a spelling the document does not print
/// (`(+ x 1)`), so the bridge is uncertified, nothing is confined, and the
/// expanded `assume` is still disclosed `foreign_assumes=yes` and withheld
/// under `--strict-proofs`. Pinned Carcara refuses that document in BOTH
/// invocations, so it is a plain foreign `assume`.
///
/// NEGATIVE, the class this test pinned before the bridge existed: an `assume`
/// that matches the problem's `let` ONLY after expansion. The `QF_NIA` query
/// takes the native NRA-SOS bundle, which `assume`s the expanded
/// `(< (+ (* x x) 1) y)`: `--expand-let-bindings` accepts it, the canonical
/// invocation refuses it, the certificate says `foreign_assumes=yes`, and
/// `--strict-proofs` withholds the verdict. A foreign-assume check that
/// compared after `let` expansion would fail here.
#[test]
#[timeout(300_000)]
fn a_certified_let_assume_is_bridged_and_an_uncertified_one_stays_foreign() {
    let problem = "(set-logic QF_LIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n\
                   (assert (let ((a (+ x 1))) (<= a y)))\n(assert (< y x))\n(check-sat)\n";
    for flags in [&[][..], &["--strict-proofs"][..]] {
        let context = format!("certified let {flags:?}");
        let run = run(problem, flags);
        let certificate = published(&run, &context);
        assert!(
            certificate.contains(" foreign_assumes=no ")
                && certificate.contains(" carcara_surface=without-let-expansion "),
            "{context}: {certificate}"
        );
        let proof = std::fs::read_to_string(&run.proof).expect("read the certificate");
        assert!(proof.contains(":rule let)"), "{context}: {proof}");
        if let Some(((plain, plain_err), (expanding, expanding_err))) = both_verdicts(&run) {
            assert_eq!(plain, "valid", "{context}: {plain_err}");
            assert_ne!(expanding, "valid", "{context}");
            assert!(
                expanding_err.contains("with rule 'let'"),
                "{context}: `--expand-let-bindings` refuses exactly the let step: {expanding_err}"
            );
        }
    }

    // NEGATIVE: the uncertified mirror keeps the disclosure.
    let mirror = problem.replace("(+ x 1)", "(+ 1 x)");
    let default = run(&mirror, &[]);
    assert_eq!(default.verdicts, ["unsat"], "{}", default.stderr);
    let certificate = default.certificate.clone().expect("a certificate line");
    assert!(
        certificate.contains(" foreign_assumes=yes ")
            && certificate.contains(" trust_free=no ")
            && certificate.contains(" ay_self_checkable=no "),
        "{certificate}"
    );
    if let Some(((plain, plain_err), _)) = both_verdicts(&default) {
        assert_ne!(plain, "valid", "{plain_err}");
        assert!(
            plain_err.contains("could not match term to any of the original problem premises"),
            "the canonical invocation refuses the assume: {plain_err}"
        );
    }
    let strict = run(&mirror, &["--strict-proofs"]);
    assert_eq!(strict.verdicts, ["unknown"], "{}", strict.stderr);

    // NEGATIVE: an `assume` that matches the problem's `let` only after
    // expansion (see the doc comment).
    let expand_only = "(set-logic QF_NIA)\n(declare-fun x () Int)\n(declare-fun y () Int)\n\
                       (assert (let ((a (* x x))) (< (+ a 1) y)))\n(assert (< y 1))\n(check-sat)\n";
    let default = run(expand_only, &[]);
    assert_eq!(default.verdicts, ["unsat"], "{}", default.stderr);
    let certificate = default.certificate.clone().expect("a certificate line");
    assert!(
        certificate.contains(" foreign_assumes=yes ") && certificate.contains(" trust_free=no "),
        "{certificate}"
    );
    if let Some(((plain, plain_err), (expanding, expanding_err))) = both_verdicts(&default) {
        assert_ne!(plain, "valid", "{plain_err}");
        assert!(
            plain_err.contains("could not match term to any of the original problem premises"),
            "the canonical invocation refuses the expanded assume: {plain_err}"
        );
        assert_eq!(
            expanding, "valid",
            "only expansion matches it: {expanding_err}"
        );
    }
    let strict = run(expand_only, &["--strict-proofs"]);
    assert_eq!(strict.verdicts, ["unknown"], "{}", strict.stderr);
}

/// A `let` root whose certified spelling repeats ANOTHER assumed `let` root's
/// authored text keeps the document it had before confinement.
///
/// `(let ((y c)) (or (not (let ((x a)) (p (f x)))) (q y)))` spells the first
/// assertion's `(let ((x a)) (p (f x)))` verbatim, so its own bridge is
/// certified only while that inner spelling prints. MEASURED at 6ccb67539
/// with the inner root confined and the outer one not: the wire-gap screen
/// (`proof_has_known_wire_gap`) recomputed the outer bridge from a wire view
/// without the inner spelling, saw a gap, and the route it took printed an
/// `or_pos` over the outer root before that root's `assume`: `invalid
/// surface proof step t1: or_pos source term does not print as an or-term`,
/// no artifact. Leaving the WHOLE nested group unconfined keeps the document
/// published before confinement (MEASURED byte-identical at af2995e57: one
/// visible hole, the outer bridge's). The test pins publication and an honest
/// plain-invocation verdict, not that hole, so closing it later is no re-pin.
#[test]
#[timeout(300_000)]
fn a_let_root_spelled_inside_another_let_root_keeps_its_document() {
    let problem = "(set-logic QF_UF)\n(declare-sort U 0)\n(declare-fun a () U)\n\
                   (declare-fun c () U)\n(declare-fun f (U) U)\n(declare-fun p (U) Bool)\n\
                   (declare-fun q (U) Bool)\n(assert (let ((x a)) (p (f x))))\n\
                   (assert (let ((y c)) (or (not (let ((x a)) (p (f x)))) (q y))))\n\
                   (assert (not (q c)))\n(check-sat)\n";
    let run = run(problem, &[]);
    assert_eq!(run.verdicts, ["unsat"], "{}", run.stderr);
    let certificate = run
        .certificate
        .clone()
        .unwrap_or_else(|| panic!("no certificate line\n{}", run.stderr));
    assert!(
        certificate.contains(" foreign_assumes=no "),
        "{certificate}"
    );
    if let Some(((plain, plain_err), _)) = both_verdicts(&run) {
        assert!(
            plain == "holey" || plain == "valid",
            "the canonical invocation: {plain} {plain_err}"
        );
    }
}
