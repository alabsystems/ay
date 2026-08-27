// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The declared-checker capability axis gates SR-witnessed proof emission.
//!
//! AY's SR symmetry routes (aux-free WLOG chains, orbitope staircase) write
//! DSR substitution-witnessed `a`-lines into the DRAT stream. Measured
//! 2026-08-24: those witnesses verify ONLY under dsr-trim — drat-trim and
//! dpr-trim both report `s NOT VERIFIED`. A SAT-COMP submission declares its
//! checker up front and a rejected UNSAT proof is disqualifying, so
//! `--proof-checker` declares the checker and the solver clamps SR-witnessed
//! emission whenever the declaration cannot consume it. The axis is paired
//! with the emitted FORMAT, because the two witnessed surfaces are not
//! interchangeable:
//!
//!   * default / `--proof-checker dsr-trim` (DRAT surface) — SR routes fire
//!     (historical behaviour, nothing changes for existing users and
//!     measurements);
//!   * `--proof-checker dpr-trim` — SR routes skip cleanly to plain CDCL, the
//!     answer is unchanged, and every emitted step is RUP/RAT-checkable. This
//!     is what the generated submission run.sh USED to pass, and the clamp is
//!     why: it cost the whole symmetry bucket (~56 instances);
//!   * `--proof-format veripb --proof-checker veripb` (what the generated
//!     submission run.sh passes as of 2026-08-25) — SR routes fire again,
//!     serialized as VeriPB `red` steps whose witness argument IS the
//!     substitution, under a checker on the official 2026 menu;
//!   * any checker/format mismatch (`drat` + `veripb`, `veripb` + `dsr-trim`)
//!     clamps, because neither checker can read the other's file.

use ay_test_support::veripb;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

struct DirGuard(PathBuf);

impl Drop for DirGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_dir_all(&self.0);
    }
}

/// Direct PHP(6,5) encoding: `x_{p,h}` = pigeon `p` in hole `h`, at-least-one
/// hole per pigeon, at-most-one pigeon per hole. UNSAT, solved in
/// milliseconds, and exactly the row-interchangeable shape the SR-witnessed
/// orbitope/aux-free routes recognize (verified: the default run emits 70
/// witnessed steps for it).
fn php_cnf(pigeons: usize, holes: usize) -> String {
    let var = |p: usize, h: usize| p * holes + h + 1;
    let mut clauses: Vec<String> = Vec::new();
    for p in 0..pigeons {
        let alo: Vec<String> = (0..holes).map(|h| var(p, h).to_string()).collect();
        clauses.push(format!("{} 0", alo.join(" ")));
    }
    for h in 0..holes {
        for p1 in 0..pigeons {
            for p2 in (p1 + 1)..pigeons {
                clauses.push(format!("-{} -{} 0", var(p1, h), var(p2, h)));
            }
        }
    }
    format!(
        "p cnf {} {}\n{}\n",
        pigeons * holes,
        clauses.len(),
        clauses.join("\n")
    )
}

fn scratch() -> (PathBuf, DirGuard) {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let dir = std::env::temp_dir().join(format!(
        "ay_declared_checker_sr_gate_{}_{}",
        std::process::id(),
        ID.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::create_dir_all(&dir).unwrap();
    std::fs::write(dir.join("php_6_5.cnf"), php_cnf(6, 5)).unwrap();
    (dir.clone(), DirGuard(dir))
}

/// Solve the PHP instance writing a proof in `format`; `extra` carries the
/// `--proof-checker` declaration under test. Returns `(exit, stderr)`.
fn solve_with_proof_format(
    dir: &Path,
    proof: &Path,
    format: &str,
    extra: &[&str],
) -> (i32, String) {
    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("solve")
        .args([
            "--proof",
            proof.to_str().unwrap(),
            "--proof-format",
            format,
            "--no-verify-proof",
        ])
        .args(extra)
        .arg(dir.join("php_6_5.cnf"))
        .output()
        .expect("failed to run ay");
    (
        output.status.code().expect("ay died on a signal"),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

fn solve_with_proof(dir: &Path, proof: &Path, extra: &[&str]) -> (i32, String) {
    solve_with_proof_format(dir, proof, "drat", extra)
}

/// Count VeriPB `red` steps that carry a *substitution* witness — a mapping
/// whose image is a literal rather than a constant. That is the part of the
/// witness a plain RAT step can never have, so it is the pseudo-Boolean
/// counterpart of `witnessed_addition_lines` on the DRAT surface.
fn substitution_witnessed_red_steps(proof: &Path) -> (usize, usize) {
    let text = std::fs::read_to_string(proof).expect("proof file must exist");
    let mut witnessed = 0usize;
    let mut reds = 0usize;
    for line in text.lines() {
        if !line.starts_with("red ") {
            continue;
        }
        reds += 1;
        let Some((_, witness)) = line.split_once(" : ") else {
            continue;
        };
        // `x12 -> x13` is a substitution; `x12 -> 1` / `x12 -> 0` is the
        // assignment part that a plain RAT pivot witness also has.
        if witness.contains("-> x") || witness.contains("-> ~x") {
            witnessed += 1;
        }
    }
    (witnessed, reds)
}

/// Count text-DRAT addition lines that carry a witness. By the DSR/DPR
/// convention the witness opens by REPEATING the clause pivot, so a witnessed
/// line is exactly an addition line whose first literal token occurs again.
/// Plain solver-emitted additions never contain a duplicate literal.
fn witnessed_addition_lines(proof: &Path) -> (usize, usize) {
    let text = std::fs::read_to_string(proof).expect("proof file must exist");
    let mut witnessed = 0usize;
    let mut additions = 0usize;
    for line in text.lines() {
        let tokens: Vec<&str> = line.split_whitespace().collect();
        match tokens.first() {
            None | Some(&"d") | Some(&"c") => continue,
            Some(&"0") if tokens.len() == 1 => continue,
            Some(_) => {}
        }
        additions += 1;
        let body = match tokens.last() {
            Some(&"0") => &tokens[..tokens.len() - 1],
            _ => &tokens[..],
        };
        if body.len() > 1 && body[1..].contains(&body[0]) {
            witnessed += 1;
        }
    }
    (witnessed, additions)
}

/// Default declaration is dsr-trim: the SR-witnessed route fires exactly as
/// before the axis existed, and the proof carries substitution witnesses.
#[test]
fn default_declaration_keeps_sr_witnessed_route() {
    let (dir, _guard) = scratch();
    let proof = dir.join("default.drat");
    let (code, stderr) = solve_with_proof(&dir, &proof, &[]);
    assert_eq!(
        code, 20,
        "PHP(6,5) must be UNSAT (exit 20); stderr: {stderr}"
    );
    let (witnessed, additions) = witnessed_addition_lines(&proof);
    assert!(
        witnessed > 0,
        "default (dsr-trim) declaration must emit SR-witnessed steps, got \
         {witnessed}/{additions} witnessed additions; stderr: {stderr}"
    );
}

/// An explicit `--proof-checker dsr-trim` is byte-identical policy to the
/// default: SR witnesses present.
#[test]
fn explicit_dsr_trim_matches_default() {
    let (dir, _guard) = scratch();
    let proof = dir.join("dsr.drat");
    let (code, stderr) = solve_with_proof(&dir, &proof, &["--proof-checker", "dsr-trim"]);
    assert_eq!(
        code, 20,
        "PHP(6,5) must be UNSAT (exit 20); stderr: {stderr}"
    );
    let (witnessed, _) = witnessed_addition_lines(&proof);
    assert!(
        witnessed > 0,
        "explicit dsr-trim must keep the SR route enabled; stderr: {stderr}"
    );
}

/// A `dpr-trim` declaration clamps the SR-witnessed routes: still a correct
/// UNSAT answer, but every emitted addition is witness-free so the run can
/// never hand its declared checker a proof it rejects. The skip must be
/// announced, not silent (master-plan G7).
///
/// This was the submission's declaration until 2026-08-25; it is kept under
/// test because the clamp is the fail-closed half of the axis and must keep
/// working for every off-surface checker, not because anything ships it.
#[test]
fn dpr_trim_declaration_disables_sr_witnessed_routes() {
    let (dir, _guard) = scratch();
    let proof = dir.join("dpr.drat");
    let (code, stderr) = solve_with_proof(&dir, &proof, &["--proof-checker", "dpr-trim"]);
    assert_eq!(
        code, 20,
        "the SR clamp must be a clean fallback, not a refusal (exit 20); stderr: {stderr}"
    );
    let (witnessed, additions) = witnessed_addition_lines(&proof);
    assert_eq!(
        witnessed, 0,
        "declared checker dpr-trim rejects DSR substitution witnesses, so the \
         proof must contain none ({witnessed}/{additions} witnessed); stderr: {stderr}"
    );
    assert!(
        additions > 0,
        "the plain-CDCL fallback must still emit a real refutation; stderr: {stderr}"
    );
    assert!(
        stderr.contains("does not accept DSR substitution witnesses"),
        "the SR skip must name the declared-checker reason (G7: no silent route \
         drops); stderr: {stderr}"
    );
}

/// Locate an external checker binary: `$PATH`, then the two provisioning
/// locations this repo's measurement sessions use. Returns `None` (skip)
/// when the tool is not installed — mirroring the optional-z3 guard in
/// `rust_horn_bmc_canaries_9618.rs`.
fn external_checker(name: &str) -> Option<PathBuf> {
    if let Ok(path) = std::env::var("PATH") {
        for dir in std::env::split_paths(&path) {
            let candidate = dir.join(name);
            if candidate.is_file() {
                return Some(candidate);
            }
        }
    }
    let home = std::env::var_os("HOME").map(PathBuf::from)?;
    for prefix in [".local/bin", "ay-bench/bin"] {
        let candidate = home.join(prefix).join(name);
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

/// End-to-end: the proof emitted under the dpr-trim declaration passes every
/// external checker that is installed (dsr-trim always accepts a superset;
/// drat-trim and dpr-trim are the ones the old SR emission failed).
#[test]
fn dpr_trim_declared_proof_verifies_under_external_checkers() {
    let (dir, _guard) = scratch();
    let proof = dir.join("dpr_external.drat");
    let (code, stderr) = solve_with_proof(&dir, &proof, &["--proof-checker", "dpr-trim"]);
    assert_eq!(
        code, 20,
        "PHP(6,5) must be UNSAT (exit 20); stderr: {stderr}"
    );

    let mut checked = 0usize;
    for name in ["dsr-trim", "dpr-trim", "drat-trim"] {
        let Some(checker) = external_checker(name) else {
            eprintln!("{name} not found; skipping optional external check");
            continue;
        };
        let output = Command::new(&checker)
            .arg(dir.join("php_6_5.cnf"))
            .arg(&proof)
            .output()
            .expect("failed to run external checker");
        let stdout = String::from_utf8_lossy(&output.stdout);
        assert!(
            stdout.contains("s VERIFIED") && !stdout.contains("NOT VERIFIED"),
            "{name} must verify the dpr-trim-declared proof; stdout: {stdout}"
        );
        checked += 1;
    }
    if checked == 0 {
        eprintln!("no external checker installed; emission-shape assertions above still ran");
    }
}

/// `--proof-format veripb --proof-checker veripb`: the SR-witnessed routes are
/// ENABLED again, and their witnesses ride VeriPB's native `red` rule. This is
/// the whole point of the pseudo-Boolean emitter — the symmetry bucket becomes
/// shippable under a checker on the official SAT-COMP 2026 menu.
#[test]
fn veripb_declaration_keeps_sr_witnessed_route() {
    let (dir, _guard) = scratch();
    let proof = dir.join("veripb.pbp");
    let (code, stderr) =
        solve_with_proof_format(&dir, &proof, "veripb", &["--proof-checker", "veripb"]);
    assert_eq!(
        code, 20,
        "PHP(6,5) must be UNSAT (exit 20); stderr: {stderr}"
    );
    let text = std::fs::read_to_string(&proof).expect("proof file must exist");
    assert!(
        text.starts_with("pseudo-Boolean proof version 3.0\n"),
        "the derivation must carry the VeriPB header; got: {:?}",
        &text[..text.len().min(80)]
    );
    assert!(
        text.ends_with("output NONE;\nconclusion UNSAT;\nend pseudo-Boolean proof;\n"),
        "the derivation must be terminated by the output/conclusion section"
    );
    let (witnessed, reds) = substitution_witnessed_red_steps(&proof);
    assert!(
        witnessed > 0,
        "the veripb declaration must keep the SR route enabled, got \
         {witnessed}/{reds} substitution-witnessed red steps; stderr: {stderr}"
    );
}

/// Declaring VeriPB while emitting DRAT clamps: VeriPB cannot read a `.drat`
/// at all, so a DSR `a`-line under that declaration would be a proof the run's
/// own checker rejects.
#[test]
fn veripb_declaration_on_drat_surface_clamps_sr() {
    let (dir, _guard) = scratch();
    let proof = dir.join("veripb_on_drat.drat");
    let (code, stderr) = solve_with_proof(&dir, &proof, &["--proof-checker", "veripb"]);
    assert_eq!(
        code, 20,
        "the clamp must be a clean fallback, not a refusal (exit 20); stderr: {stderr}"
    );
    let (witnessed, additions) = witnessed_addition_lines(&proof);
    assert_eq!(
        witnessed, 0,
        "veripb cannot read a DRAT stream, so the DRAT proof must carry no \
         witnessed additions ({witnessed}/{additions}); stderr: {stderr}"
    );
    assert!(
        additions > 0,
        "the fallback must still refute; stderr: {stderr}"
    );
    // G7: the skip is announced, and the announcement names the FORMAT as the
    // obstacle rather than falsely claiming veripb rejects the witness itself.
    assert!(
        stderr.contains("cannot read the emitted proof format"),
        "the mismatch skip must name the format, not the witness; stderr: {stderr}"
    );
}

/// The mirror mismatch: declaring dsr-trim while emitting VeriPB. dsr-trim
/// cannot read a `.pbp`, so the witnessed routes clamp here too.
#[test]
fn dsr_trim_declaration_on_veripb_surface_clamps_sr() {
    let (dir, _guard) = scratch();
    let proof = dir.join("dsr_on_veripb.pbp");
    let (code, stderr) =
        solve_with_proof_format(&dir, &proof, "veripb", &["--proof-checker", "dsr-trim"]);
    assert_eq!(
        code, 20,
        "the clamp must be a clean fallback, not a refusal (exit 20); stderr: {stderr}"
    );
    let (witnessed, reds) = substitution_witnessed_red_steps(&proof);
    assert_eq!(
        witnessed, 0,
        "dsr-trim cannot read a pseudo-Boolean derivation, so no substitution \
         witness may be emitted onto it ({witnessed}/{reds}); stderr: {stderr}"
    );
    assert!(reds > 0, "the fallback must still refute; stderr: {stderr}");
    assert!(
        stderr.contains("cannot read the emitted proof format"),
        "the mismatch skip must name the format, not the witness; stderr: {stderr}"
    );
}

/// End-to-end: the SR-witnessed VeriPB derivation is accepted by the real
/// checker. This is the claim the whole emitter exists to make, so it is
/// asserted against the binary rather than against emission shape alone.
///
/// It resolves the checker through `ay_test_support::veripb`, NOT through the
/// `external_checker` PATH scan the DRAT-family probes above use, and the
/// difference is load-bearing rather than stylistic. Published VeriPB 3.0.2
/// carries ten confirmed wrong-verdict defects (`ci/veripb.pin`,
/// `ci/veripb-soundness/`) — measured 2026-08-24, a stock build of upstream
/// `main` still had five of the nine fixtures gated then ACCEPTED, i.e. it will print
/// `s VERIFIED UNSATISFIABLE` for satisfiable input. "VeriPB accepted it" is
/// only evidence when you can say WHICH VeriPB, so this suite uses the
/// resolver that self-tests the binary and honours the workspace pin. A
/// resolved-but-bogus checker fails loudly; a genuinely absent one is a skip
/// only under `AY_VERIPB_OPTIONAL`.
#[test]
fn veripb_declared_proof_verifies_under_veripb() {
    let Some(checker) = veripb::require_checker("declared-checker-sr-gate") else {
        return;
    };
    let (dir, _guard) = scratch();
    let proof = dir.join("veripb_external.pbp");
    let (code, stderr) =
        solve_with_proof_format(&dir, &proof, "veripb", &["--proof-checker", "veripb"]);
    assert_eq!(
        code, 20,
        "PHP(6,5) must be UNSAT (exit 20); stderr: {stderr}"
    );
    let (witnessed, _) = substitution_witnessed_red_steps(&proof);
    assert!(
        witnessed > 0,
        "the proof under test must contain SR witnesses"
    );

    // VeriPB reads the DIMACS CNF directly (variable `i` is `x<i>`), so the
    // instance is the formula argument — no OPB translation step. `--cnf` is
    // passed explicitly because the shared runner otherwise defaults to
    // `--opb`.
    veripb::run(&checker, &dir.join("php_6_5.cnf"), &proof, &["--cnf"])
        .assert_verified(&veripb::Expect::UNSAT, "declared-checker-sr-gate");
}
