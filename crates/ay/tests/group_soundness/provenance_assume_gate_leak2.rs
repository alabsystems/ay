// Provenance-aware `assume` gate — leak-2 regression.
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// An UNSAT proof is only trustworthy if every `assume` on the path to the
// empty clause is backed by the problem's provenance: an original asserted
// formula, or a quantifier instantiation that traces back to an asserted
// `forall`. A theory that ASSERTS a fact it never proved (e.g. an injected
// `seq.len (seq.++ s t) = seq.len s + seq.len t` identity) rides a free axiom
// an external checker accepts blindly — laundering "trust" into a certified
// UNSAT with no `:rule trust`/`hole` step anywhere.
//
// `--strict-proofs` and `--self-check` must downgrade such a verdict to
// `unknown` (a foreign `assume` is exactly as unverified as a `trust`
// fallback), while a genuinely provenance-backed UNSAT — including a
// finite-domain `forall` whose proof assumes the original `forall` and
// derives its instances via `forall_inst` — must stay `unsat`.

use ntest::timeout;
use std::io::Write;
use std::process::Command;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

fn ay_bin() -> String {
    env!("CARGO_BIN_EXE_ay").to_string()
}

fn run(flag: Option<&str>, body: &str) -> (String, String) {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("probe.smt2");
    let mut f = std::fs::File::create(&path).expect("create tmp smt2");
    f.write_all(body.as_bytes()).expect("write tmp smt2");
    drop(f);

    let mut cmd = Command::new(ay_bin());
    if let Some(flag) = flag {
        cmd.arg(flag);
    }
    cmd.arg("-t:20000").arg(&path);
    let output = cmd
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    (stdout, stderr)
}

fn first_verdict(stdout: &str) -> String {
    stdout
        .lines()
        .find(|l| !l.starts_with("c "))
        .unwrap_or("")
        .trim()
        .to_string()
}

// A non-string sequence problem AY refutes only by ASSUMING an injected
// `seq.len` additivity axiom (not a problem assertion) — the exact leak-2
// shape (strings-seq-fp-gen `seq_q1_01`).
const SEQ_INJECTED_AXIOM: &str = "\
(set-logic ALL)
(declare-const s (Seq Int))
(declare-const t (Seq Int))
(assert (= (seq.len (seq.++ s t)) (+ (seq.len s) (seq.len t) 1)))
(check-sat)
";

// A finite-domain `forall` whose refutation legitimately assumes the ORIGINAL
// `forall` and derives its ground instances via `forall_inst` (quant-gen
// `F03`). Every `assume` is provenance-backed.
const FORALL_INST_BACKED: &str = "\
(set-logic UFLIA)
(declare-fun f (Int) Int)
(assert (forall ((x Int) (y Int)) (=> (and (<= 0 x) (< x y) (<= y 25)) (< (f x) (f y)))))
(assert (= (f 0) 2))
(assert (= (f 25) 26))
(check-sat)
";

// A plain LIA contradiction whose proof assumes only the two problem
// assertions (Farkas closes it).
const CLEAN_LIA_UNSAT: &str = "\
(set-logic QF_LIA)
(declare-const x Int)
(assert (< x 0))
(assert (> x 1))
(check-sat)
";

#[test]
#[timeout(60_000)]
fn seq_injected_axiom_default_is_unsat() {
    // The gate is opt-in: the default verdict is unchanged (this is the
    // behavior the leak-2 gate must fence, not silence by default).
    let (stdout, _) = run(None, SEQ_INJECTED_AXIOM);
    assert_eq!(
        first_verdict(&stdout),
        "unsat",
        "default (no gate) verdict changed:\n{stdout}"
    );
}

#[test]
#[timeout(60_000)]
fn seq_injected_axiom_demotes_under_self_check() {
    let (stdout, stderr) = run(Some("--self-check"), SEQ_INJECTED_AXIOM);
    let v = first_verdict(&stdout);
    assert_ne!(
        v, "unsat",
        "leak-2: --self-check accepted an UNSAT riding a provenance-unbacked \
         `assume` (injected seq.len axiom).\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(v, "unknown", "expected downgrade to unknown; got {v:?}");
}

#[test]
#[timeout(60_000)]
fn seq_injected_axiom_demotes_under_strict_proofs() {
    let (stdout, stderr) = run(Some("--strict-proofs"), SEQ_INJECTED_AXIOM);
    let v = first_verdict(&stdout);
    assert_ne!(
        v, "unsat",
        "leak-2: --strict-proofs accepted an UNSAT riding a provenance-unbacked \
         `assume`.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(v, "unknown", "expected downgrade to unknown; got {v:?}");
    assert!(
        stderr.contains("(:reason-unknown (incomplete proof-trusted))"),
        "expected the proof-trusted reason on stderr; got:\n{stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn forall_inst_backed_stays_unsat_under_self_check() {
    let (stdout, stderr) = run(Some("--self-check"), FORALL_INST_BACKED);
    assert_eq!(
        first_verdict(&stdout),
        "unsat",
        "leak-2 regressed a provenance-backed forall_inst UNSAT (F03).\n\
         stdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

#[test]
#[timeout(60_000)]
fn forall_inst_backed_stays_unsat_under_strict_proofs() {
    let (stdout, _) = run(Some("--strict-proofs"), FORALL_INST_BACKED);
    assert_eq!(
        first_verdict(&stdout),
        "unsat",
        "leak-2 regressed a provenance-backed forall_inst UNSAT (F03) under \
         --strict-proofs:\n{stdout}"
    );
}

#[test]
#[timeout(30_000)]
fn clean_lia_unsat_stays_under_self_check() {
    let (stdout, _) = run(Some("--self-check"), CLEAN_LIA_UNSAT);
    assert_eq!(
        first_verdict(&stdout),
        "unsat",
        "leak-2 regressed a clean Farkas UNSAT:\n{stdout}"
    );
}
