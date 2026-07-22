// Strict-proof UNSAT acceptance regression (#8759).
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// AY's Alethe proof writer emits `:rule trust` at critical proof steps on
// certain QF_LRA instances — on `rand_70_300_1155482584_11.lp.smt2` roughly
// 32/113 steps including the terminal empty-clause derivation (confirmed
// false UNSAT against Z3's `sat` verdict, #8511/#8754/#8758). `--strict-proofs`
// inspects the internal Alethe proof, walks backwards from every empty-clause
// step, and downgrades the verdict to `unknown` with
// `(:reason-unknown (incomplete proof-trusted))` when any `AletheRule::Trust`
// or trust-emitting `TheoryLemmaKind` (e.g. `Generic`) is reachable via the
// `premises` graph.
//
// The test here is a behavioral guard:
//  1. `rand_70_300_1155482584_11.lp.smt2` must downgrade to `unknown`
//     with the expected reason-unknown line when `--strict-proofs` is set.
//  2. A small hand-rolled true-UNSAT QF_LRA instance must still return
//     `unsat` under `--strict-proofs` (we must not accidentally reject
//     clean `th_resolution`-terminated proofs).

use ntest::timeout;
use std::io::Write;
use std::process::Command;
use std::time::Duration;

use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

fn ay_bin() -> String {
    env!("CARGO_BIN_EXE_ay").to_string()
}

fn qf_lra_false_unsat_path() -> String {
    format!(
        "{}/../../benchmarks/smtcomp/QF_LRA/rand_70_300_1155482584_11.lp.smt2",
        env!("CARGO_MANIFEST_DIR")
    )
}

/// #8759: strict-proof mode downgrades the `rand_70_300_*_11` false UNSAT
/// to `unknown` with the `(incomplete proof-trusted)` reason.
#[test]
#[timeout(120_000)]
fn strict_proofs_downgrades_rand_70_300_11_false_unsat() {
    let benchmark = qf_lra_false_unsat_path();
    if !std::path::Path::new(&benchmark).is_file() {
        eprintln!("SKIP: optional QF_LRA benchmark not found: {benchmark}");
        return;
    }
    let output = Command::new(ay_bin())
        .arg("--strict-proofs")
        .arg("-t:60000")
        .arg(&benchmark)
        .output_timeout(Duration::from_secs(115))
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let first_line = stdout.trim().lines().next().unwrap_or("").to_string();

    assert_ne!(
        first_line, "unsat",
        "Soundness regression (#8759): strict-proof mode must not accept the \
         known false-UNSAT instance rand_70_300_*_11.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
    assert_eq!(
        first_line, "unknown",
        "Expected strict-proof downgrade to `unknown`; got {first_line:?}.\nstdout:\n{stdout}"
    );
    assert!(
        stderr.contains("(:reason-unknown (incomplete proof-trusted))"),
        "Expected `(:reason-unknown (incomplete proof-trusted))` on stderr \
         after strict-proof downgrade (#8759). stderr was:\n{stderr}"
    );
}

/// #8759: strict-proof mode must preserve true UNSAT verdicts that do not
/// rely on `:rule trust` — i.e., it must not regress correctness on clean
/// `th_resolution`-terminated proofs.
#[test]
#[timeout(30_000)]
fn strict_proofs_preserves_clean_true_unsat() {
    let dir = tempfile::tempdir().expect("tempdir");
    let path = dir.path().join("true_unsat_lra.smt2");
    let mut f = std::fs::File::create(&path).expect("create tmp smt2");
    writeln!(
        f,
        "(set-logic QF_LRA)\n\
         (declare-const x Real)\n\
         (declare-const y Real)\n\
         (assert (<= x 5.0))\n\
         (assert (>= y 10.0))\n\
         (assert (= x y))\n\
         (check-sat)\n\
         (exit)"
    )
    .expect("write tmp smt2");
    drop(f);

    let output = Command::new(ay_bin())
        .arg("--strict-proofs")
        .arg("-t:15000")
        .arg(&path)
        .output_timeout(DEFAULT_CHILD_TIMEOUT)
        .expect("failed to spawn ay");

    let stdout = String::from_utf8_lossy(&output.stdout);
    let first_line = stdout.trim().lines().next().unwrap_or("").to_string();
    assert_eq!(
        first_line, "unsat",
        "strict-proof mode regressed a clean QF_LRA UNSAT: got {first_line:?}.\nstdout:\n{stdout}"
    );
}

/// TIER-0 certification leak: a sequence-theory UNSAT that AY refutes with a
/// *clean* Alethe proof (zero `hole`/`trust`, no foreign `assume`) but that no
/// independent checker can confirm.
///
/// Here `(seq.nth s 0)` is forced to two distinct integer constants (10 and
/// 11). AY's arithmetic core treats `(seq.nth s 0)` as an opaque atom and
/// collapses the contradiction to a `la_generic` + `resolution` chain — a
/// proof that carries NO trust/hole step and NO foreign assume, so neither the
/// #8759 trust gate nor the leak-2 provenance gate fires. But the proof is not
/// independently checkable: carcara rejects the problem at parse time (`sort
/// 'Seq' is not defined`), no firewall-Lean lemma covers sequences, and there
/// is no DRAT lane. Under `--strict-proofs` (and `--self-check`) this must
/// downgrade to a sound `unknown` rather than ship a bare, uncheckable `unsat`.
#[test]
#[timeout(30_000)]
fn strict_proofs_downgrades_uncheckable_seq_unsat() {
    let smt = "(set-logic ALL)\n\
               (declare-const s (Seq Int))\n\
               (assert (= (seq.len s) 4))\n\
               (assert (= (seq.nth s 0) 10))\n\
               (assert (= (seq.nth s 3) 20))\n\
               (assert (> (seq.nth s 1) 1))\n\
               (assert (= (seq.nth s 0) 11))\n\
               (check-sat)\n\
               (exit)\n";

    // Baseline: default (non-strict) mode still DECIDES this as `unsat`
    // (completeness is preserved — the internal refutation is sound).
    for (flag, dir) in [
        (None, "default"),
        (Some("--strict-proofs"), "strict"),
        (Some("--self-check"), "selfcheck"),
    ] {
        let tmp = tempfile::tempdir().expect("tempdir");
        let path = tmp.path().join("seq_uncheckable_unsat.smt2");
        std::fs::write(&path, smt).expect("write smt2");
        let mut cmd = Command::new(ay_bin());
        if let Some(f) = flag {
            cmd.arg(f);
        }
        cmd.arg("-t:15000").arg(&path);
        let output = cmd
            .output_timeout(DEFAULT_CHILD_TIMEOUT)
            .expect("failed to spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout);
        let first_line = stdout
            .lines()
            .find(|l| matches!(l.trim(), "sat" | "unsat" | "unknown"))
            .unwrap_or("")
            .trim()
            .to_string();
        match flag {
            None => assert_eq!(
                first_line, "unsat",
                "default mode should still decide the seq contradiction as unsat ({dir}).\nstdout:\n{stdout}"
            ),
            Some(_) => {
                assert_ne!(
                    first_line, "unsat",
                    "TIER-0 leak: {dir} mode shipped a bare `unsat` for a sequence \
                     refutation with no independently-checkable proof.\nstdout:\n{stdout}"
                );
                assert_eq!(
                    first_line, "unknown",
                    "{dir} mode should downgrade the uncheckable seq unsat to `unknown`; \
                     got {first_line:?}.\nstdout:\n{stdout}"
                );
            }
        }
    }
}
