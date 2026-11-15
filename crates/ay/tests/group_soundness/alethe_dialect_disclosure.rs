// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The certificate line tells the truth about which Carcara accepts the
//! document (`--alethe-dialect`).
//!
//! REGRESSION (475ba9547, measured 2026-09-29): a `bvashr` refutation over a
//! symbolic sign printed Clean's sign-filled `bitblast_ashr` layer under
//! `unproved_steps=0 trust_free=yes ay_self_checkable=yes
//! carcara_surface=supported`, and pinned Carcara 9a352ee refused it at
//! `bitblast_ashr`. The default stays Clean's spelling (external-codegen promotes on
//! Clean, under `--strict-proofs`), and the line now says
//! `carcara_surface=clean-dialect`. `--alethe-dialect pinned-carcara` prints
//! the pinned spelling, disclosed `supported`, which pinned Carcara accepts.
//! A `zero_extend` past the packed word lane's closed-case bound, or one the
//! complete bit-blast lane keeps ([`ZERO_EXTEND_EXPECTED`]), is disclosed in
//! both dialects, naming its consumer rule. Admitted small-support Circuit
//! cases are instead explicitly `supported` and pinned `valid`.
//! REGRESSION (measured 2026-09-30 on c57bd8481): a `zero_extend` of a
//! 16-bit word with at most eight symbolic bits ([`ZERO_EXTEND_CLOSED_CASES`])
//! kept Clean's `refl` under `--alethe-dialect pinned-carcara` too, and
//! pinned Carcara refused it, although the closed cases it does check fit
//! that bound. The pinned dialect now prints them in the packed word lane:
//! `supported` and `valid`.
//! REGRESSION (e9b297e37, measured 2026-09-30 on 938ec0327): a `bvudiv` /
//! `bvurem` refutation printed Clean's fixed divider under
//! `carcara_surface=supported`, and pinned Carcara refused it at
//! `bitblast_udiv` / `bitblast_urem`. Over a symbolic dividend pinned
//! Carcara's own divider is false, so both dialects keep Clean's and disclose
//! it.
//! REGRESSION (measured 2026-09-30 on 57cef15fd and 426f40600): the eight
//! byte-wide divider refutations in [`DIVIDER_REPRODUCERS`] were published
//! under `--strict-proofs` as `carcara_surface=supported` in both dialects,
//! and pinned Carcara refused every one at its first divider step. In the
//! default dialect each is now `clean-dialect`; in the pinned dialect a
//! literal zero divisor prints pinned Carcara's divider (true there) and is
//! `supported` and `valid`, and every other one stays disclosed.
//! NEGATIVE CONTROL: a shift-only document with no such step stays
//! `supported`. The replays are skipped with a note without `carcara`
//! (`CARCARA_PATH`, or `carcara` on `PATH`).

use std::process::Command;

use crate::spawn::OutputTimeout;
use crate::strict_certificate_publication::{verdict_lines, QUERY_TIMEOUT};

#[path = "alethe_dialect_dt_project.rs"]
mod dt_project;

/// p01: a symbolic byte shifted right arithmetically by a constant.
const ASHR: &str = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
    (assert (not (= (bvashr x #x03) ((_ sign_extend 3) ((_ extract 7 3) x)))))\n(check-sat)\n";
/// The same identity for the logical shifts: no `bitblast_ashr`, no `zero_extend`.
const LOGICAL: &str = "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
    (assert (not (= (bvlshr (bvshl x #x03) #x03) (bvand x #x1f))))\n(check-sat)\n";
/// Exact observed contracts for the unchanged four public conformance
/// problems. The byte-read and two-byte Circuit cases now have standard
/// derivations. The wide packed word and complete-bitblast cases retain the
/// disclosed consumer identity. Every case stays in both dialect loops.
#[derive(Clone, Copy)]
enum ZeroExtendExpected {
    CleanOnly(&'static str),
    Standard,
}

const ZERO_EXTEND_EXPECTED: [ZeroExtendExpected; 4] = [
    ZeroExtendExpected::CleanOnly("refl"),
    ZeroExtendExpected::Standard,
    ZeroExtendExpected::CleanOnly("refl"),
    ZeroExtendExpected::Standard,
];

fn zero_extend_problems() -> impl Iterator<Item = (&'static str, ZeroExtendExpected)> {
    let problems = ay_proof::CleanOnlySpelling::ZeroExtendAsConcat.conformance_problems();
    assert_eq!(problems.len(), ZERO_EXTEND_EXPECTED.len());
    problems.iter().copied().zip(ZERO_EXTEND_EXPECTED)
}

/// `zero_extend` of a 16-bit source with at most eight symbolic bits, in the
/// packed word lane: a byte under eight literal zeros, and a closed word.
const ZERO_EXTEND_CLOSED_CASES: [&str; 2] = [
    "(set-logic QF_BV)\n(declare-const b (_ BitVec 8))\n\
     (assert (not (= ((_ extract 15 0) (bvlshr ((_ zero_extend 16) (concat #x00 b)) (_ bv3 32))) \
     (bvlshr (concat #x00 b) (_ bv3 16)))))\n(check-sat)\n",
    "(set-logic QF_BV)\n(declare-const y (_ BitVec 32))\n\
     (assert (not (= (bvadd ((_ zero_extend 16) #x0005) y) (bvadd y #x00000005))))\n(check-sat)\n",
];

/// A symbolic dividend under a constant divisor, `bvudiv` then `bvurem`.
/// Four bits: pinned Carcara prints the whole expected divider term when it
/// refuses the step, and at eight bits that print alone takes minutes.
const DIVIDE: [(&str, &str); 2] = [
    (
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 4))\n\
         (assert (bvult x (bvudiv x #x3)))\n(check-sat)\n",
        "bitblast_udiv",
    ),
    (
        "(set-logic QF_BV)\n(declare-const x (_ BitVec 4))\n\
         (assert (bvult #x2 (bvurem x #x3)))\n(check-sat)\n",
        "bitblast_urem",
    ),
];

/// The measured byte-wide divider refutations, the rule each prints, and
/// whether its divisor is a literal zero: a zero divisor, a power-of-two
/// divisor against its shift or mask (in each literal spelling), `x / x`, and
/// the division identity over a symbolic divisor (both dividers; pinned
/// Carcara stops at the remainder's).
const DIVIDER_REPRODUCERS: [(&str, &str, bool); 8] = [
    (
        "(assert (not (= (bvudiv x (_ bv0 8)) (_ bv255 8))))",
        "bitblast_udiv",
        true,
    ),
    (
        "(assert (not (= (bvurem x (_ bv0 8)) x)))",
        "bitblast_urem",
        true,
    ),
    (
        "(assert (not (= (bvurem x (_ bv16 8)) (bvand x (_ bv15 8)))))",
        "bitblast_urem",
        false,
    ),
    (
        "(assert (not (= (bvudiv x (_ bv2 8)) (bvlshr x (_ bv1 8)))))",
        "bitblast_udiv",
        false,
    ),
    (
        "(assert (not (= (bvudiv x #x04) (bvlshr x #x02))))",
        "bitblast_udiv",
        false,
    ),
    (
        "(assert (not (= (bvudiv x (_ bv8 8)) (bvlshr x #b00000011))))",
        "bitblast_udiv",
        false,
    ),
    (
        "(assert (not (= (bvudiv x x) (ite (= x #x00) #xff #x01))))",
        "bitblast_udiv",
        false,
    ),
    (
        "(assert (not (= (bvadd (bvmul (bvudiv x y) y) (bvurem x y)) x)))",
        "bitblast_urem",
        false,
    ),
];

struct Run {
    certificate: String,
    stderr: String,
    problem: std::path::PathBuf,
    proof: std::path::PathBuf,
    _dir: tempfile::TempDir,
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
    assert_eq!(
        verdict_lines(&stdout),
        ["unsat"],
        "{flags:?}\n{stdout}\n{stderr}"
    );
    let certificate = stderr
        .lines()
        .find(|line| line.starts_with("c ay.proof.certificate "))
        .unwrap_or_else(|| panic!("no certificate line:\n{stderr}"))
        .to_string();
    assert!(
        certificate.contains(" unproved_steps=0 ") && certificate.contains(" trust_free=yes "),
        "{certificate}"
    );
    Run {
        certificate,
        stderr,
        problem,
        proof,
        _dir: dir,
    }
}

/// Pinned Carcara's verdict on the written certificate, or `None` without it.
/// A pair on which pinned Carcara's verdict is not evidence
/// (`ay_core::pinned_carcara`) fails first, before the checker runs.
fn pinned_carcara(run: &Run) -> Option<(String, String)> {
    pinned_carcara_verdict(&run.problem, &run.proof)
}

/// Pinned Carcara's last stdout line and its stderr on the certificate at
/// `proof` for the query at `problem`, or `None` (with a note) when no checker
/// runs: `CARCARA_PATH`, else `carcara` on `PATH`. A pair on which pinned
/// Carcara's verdict is not evidence (`ay_core::pinned_carcara`) fails first,
/// before the checker runs.
///
/// The invocation is AY's canonical one, `carcara check -- PROOF PROBLEM`. A
/// `supported` certificate's spelling reads the same under
/// `--expand-let-bindings`; a `without-let-expansion` one is checked only in
/// the canonical invocation ([`pinned_carcara_verdict_in`]).
pub(super) fn pinned_carcara_verdict(
    problem: &std::path::Path,
    proof: &std::path::Path,
) -> Option<(String, String)> {
    pinned_carcara_verdict_in(problem, proof, &[])
}

/// [`pinned_carcara_verdict`] with `flags` before the operands:
/// `&["--expand-let-bindings"]` is the other invocation AY's gates have used.
pub(super) fn pinned_carcara_verdict_in(
    problem: &std::path::Path,
    proof: &std::path::Path,
    flags: &[&str],
) -> Option<(String, String)> {
    let problem_text = std::fs::read_to_string(problem).expect("read the query");
    let proof_text = std::fs::read_to_string(proof).expect("read the certificate");
    if let Err(misjudged) =
        ay_core::pinned_carcara::pinned_carcara_can_judge(&problem_text, &proof_text)
    {
        panic!("{}: {misjudged}\n{proof_text}", proof.display());
    }
    let checker = std::env::var_os("CARCARA_PATH").unwrap_or_else(|| "carcara".into());
    let probe = Command::new(&checker).arg("--version").output();
    if !probe.is_ok_and(|probe| probe.status.success()) {
        eprintln!("carcara not on PATH (nor CARCARA_PATH): the pinned replay is skipped");
        return None;
    }
    let output = Command::new(&checker)
        .arg("check")
        .args(flags)
        .arg("--")
        .arg(proof)
        .arg(problem)
        .output_timeout(QUERY_TIMEOUT)
        .expect("carcara answers");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let verdict = stdout.lines().last().unwrap_or("").trim().to_string();
    Some((verdict, String::from_utf8_lossy(&output.stderr).to_string()))
}

/// A Standard conformance case requires a real successful checker run.
/// This intentionally has no optional availability probe: neither absence,
/// a guard refusal, a timeout, a failed child nor extra verdict output can
/// turn a required positive replay into a skipped check.
pub(super) fn require_pinned_carcara_valid(problem: &std::path::Path, proof: &std::path::Path) {
    let problem_text = std::fs::read_to_string(problem).expect("read the query");
    let proof_text = std::fs::read_to_string(proof).expect("read the certificate");
    if let Err(misjudged) =
        ay_core::pinned_carcara::pinned_carcara_can_judge(&problem_text, &proof_text)
    {
        panic!("{}: {misjudged}\n{proof_text}", proof.display());
    }
    let checker = std::env::var_os("CARCARA_PATH").unwrap_or_else(|| "carcara".into());
    let output = Command::new(&checker)
        .arg("check")
        .arg("--")
        .arg(proof)
        .arg(problem)
        .output_timeout(QUERY_TIMEOUT)
        .expect("required pinned Carcara must run for a Standard case");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    assert!(
        output.status.success(),
        "required pinned checker failed: {stdout}\n{stderr}"
    );
    assert_eq!(stdout.lines().collect::<Vec<_>>(), ["valid"], "{stderr}");
}

/// NEGATIVE CONTROL: the replay refuses, before the checker runs, the pair
/// pinned carcara prints `valid` for only through its `evaluate` defect, so
/// neither a `valid` assertion nor a disclosed refusal can pass on it.
#[test]
#[should_panic(expected = "is not evidence")]
fn the_pinned_replay_refuses_a_document_pinned_carcara_misjudges() {
    let dir = tempfile::tempdir().expect("tempdir");
    let problem = dir.path().join("query.smt2");
    let proof = dir.path().join("query.alethe");
    std::fs::write(
        &problem,
        ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROBLEM,
    )
    .expect("write query");
    std::fs::write(&proof, ay_core::pinned_carcara::FALSE_VALID_CONTROL_PROOF)
        .expect("write proof");
    pinned_carcara(&Run {
        certificate: String::new(),
        stderr: String::new(),
        problem,
        proof,
        _dir: dir,
    });
}

fn assert_disclosed(run: &Run) {
    assert!(
        run.certificate.contains(" carcara_surface=clean-dialect "),
        "{}",
        run.certificate
    );
    assert!(
        run.stderr
            .lines()
            .any(|line| line.starts_with("c warning: ")
                && line.contains("carcara_surface=clean-dialect")
                && !line.contains("holey")),
        "the disclosure names the class, in words external-codegen does not read as a gap:\n{}",
        run.stderr
    );
}

fn assert_disclosed_and_refused_at(run: &Run, rule: &str) {
    assert_disclosed(run);
    if let Some((verdict, stderr)) = pinned_carcara(run) {
        assert_ne!(verdict, "valid", "a clean-dialect certificate was accepted");
        assert!(stderr.contains(&format!("with rule '{rule}'")), "{stderr}");
    }
}

#[test]
fn the_certificate_line_discloses_the_clean_ashr_layer_and_the_pinned_dialect_is_valid() {
    for flags in [&[][..], &["--strict-proofs"][..]] {
        // Default: the Clean layer, still published under `--strict-proofs`.
        assert_disclosed_and_refused_at(&run(ASHR, flags), "bitblast_ashr");

        let pinned = [flags, &["--alethe-dialect", "pinned-carcara"][..]].concat();
        let pinned = run(ASHR, &pinned);
        assert!(
            pinned.certificate.contains(" carcara_surface=supported "),
            "{}",
            pinned.certificate
        );
        if let Some((verdict, stderr)) = pinned_carcara(&pinned) {
            assert_eq!(verdict, "valid", "{stderr}");
        }
    }
}

#[test]
fn a_document_without_a_clean_only_step_stays_supported() {
    let control = run(LOGICAL, &[]);
    assert!(
        control.certificate.contains(" carcara_surface=supported "),
        "{}",
        control.certificate
    );
    assert!(
        !control.stderr.contains("clean-dialect"),
        "{}",
        control.stderr
    );
    if let Some((verdict, stderr)) = pinned_carcara(&control) {
        assert_eq!(verdict, "valid", "{stderr}");
    }
}

/// Every unchanged case has one exact contract in each dialect: the
/// remaining consumer spelling is disclosed and refused at its identity;
/// the newly standard byte cases must be supported and strictly valid.
#[test]
fn zero_extend_conformance_has_case_specific_contracts_in_both_dialects() {
    let rule_key = ay_proof::CleanOnlySpelling::ZeroExtendAsConcat.consumer_rule();
    for flags in [&[][..], &["--alethe-dialect", "pinned-carcara"][..]] {
        for (script, expected) in zero_extend_problems() {
            let run = run(script, flags);
            match expected {
                ZeroExtendExpected::CleanOnly(rule) => {
                    assert_disclosed_and_refused_at(&run, rule);
                    assert!(
                        run.stderr
                            .lines()
                            .any(|line| line.starts_with("c warning: ")
                                && line.contains("carcara_surface=clean-dialect")
                                && line.contains(rule_key)),
                        "{flags:?}: the warning names {rule_key}:\n{}",
                        run.stderr
                    );
                }
                ZeroExtendExpected::Standard => {
                    assert!(
                        run.certificate.contains(" carcara_surface=supported "),
                        "{}",
                        run.certificate
                    );
                    assert!(
                        !run.stderr.contains("carcara_surface=clean-dialect"),
                        "{}",
                        run.stderr
                    );
                    let proof =
                        std::fs::read_to_string(&run.proof).expect("read the standard certificate");
                    assert!(!proof.contains(":rule hole") && !proof.contains(":rule trust"));
                    require_pinned_carcara_valid(&run.problem, &run.proof);
                }
            }
        }
    }
}

/// The default dialect keeps Clean's `refl` and discloses it; the pinned
/// dialect prints the closed cases, `supported` and a literal `valid`. The
/// negative twins are the zero_extend conformance problems
/// ([`ZERO_EXTEND_EXPECTED`]): the first remains a fully symbolic 16-bit word
/// past the bound, and the third stays in the complete bit-blast lane. The
/// fourth conformance case now has a standard packed-circuit derivation.
#[test]
fn a_zero_extend_within_the_closed_case_bound_is_pinned_valid_in_the_pinned_dialect() {
    for script in ZERO_EXTEND_CLOSED_CASES {
        assert_disclosed_and_refused_at(&run(script, &[]), "refl");
        let pinned = run(script, &["--alethe-dialect", "pinned-carcara"]);
        assert!(
            pinned.certificate.contains(" carcara_surface=supported "),
            "{}",
            pinned.certificate
        );
        assert!(
            !pinned.stderr.contains("clean-dialect"),
            "{}",
            pinned.stderr
        );
        if let Some((verdict, stderr)) = pinned_carcara(&pinned) {
            assert_eq!(verdict, "valid", "{script}: {stderr}");
        }
    }
}

#[test]
fn a_symbolic_divider_is_disclosed_in_both_dialects_and_under_strict_proofs() {
    for flags in [
        &[][..],
        &["--strict-proofs"][..],
        &["--alethe-dialect", "pinned-carcara"][..],
    ] {
        for (script, rule) in DIVIDE {
            let run = run(script, flags);
            assert!(
                run.stderr
                    .lines()
                    .any(|line| line.starts_with("c warning: ")
                        && line.contains("bitblast_udiv or bitblast_urem")),
                "{flags:?}: the warning names the divider:\n{}",
                run.stderr
            );
            assert_disclosed_and_refused_at(&run, rule);
        }
    }
}

/// The measured byte-wide dividers, under `--strict-proofs` in both
/// dialects. A disclosed one is not replayed: pinned Carcara's refusal prints
/// the divider it expected without sharing, which grows exponentially with
/// the width (measured: 3.5 KB of stderr at 2 bits, 85 KB at 3, 9.9 MB at 4,
/// and no answer within 300 s at 8); the four-bit [`DIVIDE`] rows replay the
/// refusal. A `supported` one must be `valid`.
#[test]
fn the_measured_byte_dividers_are_disclosed_as_pinned_carcara_judges_them() {
    for (flags, pinned) in [
        (&["--strict-proofs"][..], false),
        (
            &["--strict-proofs", "--alethe-dialect", "pinned-carcara"][..],
            true,
        ),
    ] {
        for (assertion, rule, zero_divisor) in DIVIDER_REPRODUCERS {
            let script = format!(
                "(set-logic QF_BV)\n(declare-const x (_ BitVec 8))\n\
                 (declare-const y (_ BitVec 8))\n{assertion}\n(check-sat)\n"
            );
            let run = run(&script, flags);
            let proof = std::fs::read_to_string(&run.proof).expect("read the certificate");
            assert!(
                proof.contains(&format!(":rule {rule}")),
                "{assertion} {flags:?}: the certificate prints no {rule} step"
            );
            if pinned && zero_divisor {
                assert!(
                    run.certificate.contains(" carcara_surface=supported "),
                    "{assertion} {flags:?}: {}",
                    run.certificate
                );
                if let Some((verdict, stderr)) = pinned_carcara(&run) {
                    assert_eq!(verdict, "valid", "{assertion} {flags:?}: {stderr}");
                }
            } else {
                assert_disclosed(&run);
            }
        }
    }
}

/// PRECEDENCE: an authored problem pinned Carcara cannot parse makes the
/// certificate `unsupported` in either dialect, never `clean-dialect`: the
/// checker stops at the problem before any step's spelling matters. The
/// prefix is a `set-info` whose quoted symbol has a `\`, which pinned Carcara's
/// lexer rejects and which leaves the proof unchanged. `clean-dialect` alone
/// still publishes under `--strict-proofs`; the unparseable problem does not.
#[test]
fn a_problem_pinned_carcara_cannot_parse_is_unsupported_in_either_dialect() {
    let script = format!("(set-info :source |C:\\ay|)\n{ASHR}");
    for flags in [&[][..], &["--alethe-dialect", "pinned-carcara"][..]] {
        let run = run(&script, flags);
        assert!(
            run.certificate.contains(" carcara_surface=unsupported "),
            "{flags:?}: {}",
            run.certificate
        );
        assert!(
            run.stderr.contains("lexer") && !run.stderr.contains("clean-dialect"),
            "{flags:?}: the warning is the parse gap's, not the dialect's:\n{}",
            run.stderr
        );
        if let Some((verdict, stderr)) = pinned_carcara(&run) {
            assert_ne!(verdict, "valid", "{stderr}");
        }
    }
    let dir = tempfile::tempdir().expect("tempdir");
    let problem = dir.path().join("query.smt2");
    std::fs::write(&problem, &script).expect("write query");
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("-smt2")
        .arg(&problem)
        .arg("--strict-proofs")
        .output_timeout(QUERY_TIMEOUT)
        .expect("ay answers");
    let stdout = String::from_utf8_lossy(&output.stdout);
    assert_eq!(verdict_lines(&stdout), ["unknown"], "{stdout}");
}
