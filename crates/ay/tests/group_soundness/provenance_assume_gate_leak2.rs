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
    // The injected axiom's step is refused by the MANDATORY certification
    // funnel (66538b006), which runs before the strict-proofs terminal-trust
    // gate. a208f658d fixed that order deliberately ("applied earlier it would
    // relabel rejections certification already makes (`SelfCheckRejected`
    // silently becoming `ProofTrusted`)") and pins this exact problem as
    // `SelfCheckRejected` under strict proofs at the library boundary
    // (`strict_proof_terminal_trust_library_gate::
    // terminal_trust_is_distinct_from_self_check_rejection`). `proof-trusted`
    // is reserved for a verdict certification ACCEPTED whose terminal chain
    // still is not trust-free, so it must not appear here.
    assert!(
        stderr.contains("(:reason-unknown (incomplete self-check-rejected))")
            && stderr.contains("computed UNSAT rejected by mandatory strict certification"),
        "expected the certification funnel's typed refusal of the injected axiom on stderr; \
         got:\n{stderr}"
    );
    assert!(
        !stderr.contains("(:reason-unknown (incomplete proof-trusted))"),
        "a certification refusal must not be relabelled as a strict-proof gate rejection; \
         got:\n{stderr}"
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

/// Mechanism pin for the two F03 tests above: in plain proof mode the
/// published certificate must be the provenance-backed `forall_inst`
/// derivation, with no unproved step.
///
/// The finite-domain expansion replaces the `forall` by its ground instances
/// and preprocessing tightens and folds them, so 25 instance conjuncts reach
/// the proof as trust leaves. Trust surgery re-derives each one from the
/// ORIGINAL `forall` by `forall_inst` (`plan_quant_consequence`, ded7b9c72).
/// Up to 76e895f9c that certificate was trust-free and Carcara-`valid`; after
/// c25240fc9 the surgery was discarded WHOLE, leaving 25 `hole`s, so
/// `--self-check` and `--strict-proofs` answered `unknown`. Three defects, each
/// alone enough to discard it: (1) for the 23 middle leaves the leaf IS the
/// folded instance and the plan's lemma degenerated to `(cl (not L) L)`, which
/// the surface audit's `unique_atoms` refuses (an identity consequence now
/// needs no lemma); (2) the chain is built from the PARSED body but
/// instantiated the elaborated `forall`, whose body normalization rewrote (it
/// now instantiates the raw surface rebuild, as `QuantNegationPlan` already
/// did, registered as an authored premise); (3) every chain bridges the
/// authored `(< (f x) (f y))` to its `Int`-tightened `(<= (f x) (+ (f y) (-
/// 1)))` with a `la_generic` that pinned Carcara accepts only through integer
/// strengthening, which the audit's printed replay omitted (it now applies the
/// sound `Int` subset).
#[test]
#[timeout(60_000)]
fn forall_inst_backed_certificate_is_hole_free() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("f03.smt2");
    std::fs::write(&path, FORALL_INST_BACKED).expect("write tmp smt2");
    let output = Command::new(ay_bin())
        .arg("-t:20000")
        .arg(&path)
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("failed to spawn ay");
    let stdout = String::from_utf8_lossy(&output.stdout).to_string();
    let stderr = String::from_utf8_lossy(&output.stderr).to_string();
    assert_eq!(
        first_verdict(&stdout),
        "unsat",
        "stdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("unsat_admission=strict-proof"),
        "AY's strict checker must admit the F03 refutation itself (not a trust discharge).\n\
         stderr:\n{stderr}"
    );
    let alethe = std::fs::read_to_string(dir.path().join("f03.smt2.alethe"))
        .unwrap_or_else(|e| panic!("F03 certificate must be written: {e}\nstderr:\n{stderr}"));
    assert!(
        !alethe.contains(":rule hole") && !alethe.contains(":rule trust"),
        "the F03 certificate must carry no unproved step:\n{alethe}"
    );
    assert!(
        alethe.contains(":rule forall_inst"),
        "the F03 instances must be derived from the original forall by forall_inst:\n{alethe}"
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
