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

use crate::corpus::optional_corpus_file;
use crate::spawn::{OutputTimeout, DEFAULT_CHILD_TIMEOUT};

fn ay_bin() -> String {
    env!("CARGO_BIN_EXE_ay").to_string()
}

const QF_LRA_FALSE_UNSAT: &str = "benchmarks/smtcomp/QF_LRA/rand_70_300_1155482584_11.lp.smt2";

/// #8759: strict-proof mode never publishes `unsat` on the `rand_70_300_*_11`
/// SAT instance (z3: `sat`).
///
/// DECISION (2026-09-24): this test used to also require the historical false
/// UNSAT to still be produced internally so that strict mode could catch it
/// (`unknown` with `(incomplete proof-trusted)`). That false UNSAT is gone: at
/// d14c2313e AY answers `unknown` at a 300 s budget in default, `--no-proof`
/// and `--strict-proofs` modes alike, and z3 answers `sat`. The test ran only
/// on hosts holding the gitignored corpus until bedafe466, so the change went
/// unseen. A guard that needs a soundness bug to persist is obsolete; the
/// soundness invariant (never `unsat` here) is kept unchanged, `sat` (the
/// right answer) and `unknown` are accepted, and the strict-proof
/// `(incomplete proof-trusted)` downgrade itself stays pinned by
/// `strict_proof_terminal_trust_library_gate.rs` (ay-dpll) and
/// `provenance_assume_gate_leak2.rs`.
#[test]
#[timeout(120_000)]
fn strict_proofs_downgrades_rand_70_300_11_false_unsat() {
    // Gitignored corpus: absent means skip (announced), or a failure under
    // `AY_REQUIRE_CORPUS=1` — never a pass that checked something.
    let Some(benchmark) = optional_corpus_file(
        "strict_proofs_downgrades_rand_70_300_11_false_unsat",
        QF_LRA_FALSE_UNSAT,
    ) else {
        return;
    };
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
    assert!(
        first_line == "sat" || first_line == "unknown",
        "Expected `sat` or `unknown` on the SAT instance; got {first_line:?}.\nstdout:\n{stdout}\nstderr:\n{stderr}"
    );
}

/// FP forward-error UNSATs are in the strict proof subset: the refutation
/// closes through the typed `fp_forward_error` theory lemma (independently
/// re-derived by `ay-proof`'s analytic checker), not `:rule trust`.
///
/// Owner decision D7 (31c874c43, 2026-09-22; the refusal first landed with
/// c93a232b2) makes every consumer that CLAIMS an external re-check refuse a
/// certificate pinned Carcara 1.1.0 cannot parse, and names `--strict-proofs`
/// as one: `(_ FloatingPoint 11 53)` is outside that checker's sort grammar,
/// so the verdict is withheld as `(incomplete proof-trusted)` WITH the surface
/// as its stated cause. The library twin is
/// `strict_proof_terminal_trust_library_gate::strict_proofs_refusal_names_the_unsupported_carcara_surface`.
///
/// What this test still guards (#8759's FP half, 361e3038f): the forward-error
/// lemma must stay trust-free. The plain run must publish `unsat` admitted by
/// AY's strict checker (`unsat_admission=strict-proof`), and the strict-proofs
/// refusal must cite ONLY the unsupported surface. A lemma regressed to
/// `:rule trust` changes the admission and adds "a trust or hole step reaches
/// the empty clause" to the refusal, and fails here.
#[test]
#[timeout(60_000)]
fn strict_proofs_refuses_fp_forward_error_unsat_for_its_surface_only() {
    let dir = tempfile::tempdir().expect("tempdir");
    // One file per run: a file-input `unsat` writes `<file>.alethe` beside it,
    // and a second run must not collide with the first run's certificate.
    let solve = |name: &str, flag: Option<&str>| {
        let path = dir.path().join(name);
        let mut f = std::fs::File::create(&path).expect("create tmp smt2");
        writeln!(
            f,
            "(set-logic QF_FPLRA)\n\
             (declare-const x Float64)\n\
             (declare-const y Float64)\n\
             (assert (and (fp.isNormal x) (<= (fp.to_real (fp.abs x)) 1.0)))\n\
             (assert (and (fp.isNormal y) (<= (fp.to_real (fp.abs y)) 1.0)))\n\
             (assert (>= (- (fp.to_real (fp.add RNE x y))\n\
                            (+ (fp.to_real x) (fp.to_real y)))\n\
                         0.3))\n\
             (check-sat)\n\
             (exit)"
        )
        .expect("write tmp smt2");
        drop(f);
        let mut cmd = Command::new(ay_bin());
        if let Some(flag) = flag {
            cmd.arg(flag);
        }
        let output = cmd
            .arg("-t:30000")
            .arg(&path)
            .output_timeout(DEFAULT_CHILD_TIMEOUT)
            .expect("failed to spawn ay");
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();
        let first_line = stdout.trim().lines().next().unwrap_or("").to_string();
        (first_line, stdout, stderr)
    };

    // The refutation itself: published, and admitted by AY's own strict
    // checker, which re-derived the forward-error lemma.
    let (plain, plain_stdout, plain_stderr) = solve("fp_forward_error_plain.smt2", None);
    assert_eq!(
        plain, "unsat",
        "the forward-error refutation must publish in plain mode: got {plain:?}.\n\
         stdout:\n{plain_stdout}\nstderr:\n{plain_stderr}"
    );
    assert!(
        plain_stderr.contains("unsat_admission=strict-proof"),
        "AY's strict checker must admit the forward-error refutation (a lemma regressed to \
         `:rule trust` changes the admission).\nstderr:\n{plain_stderr}"
    );

    // Strict proofs: refused for the unsupported external surface, and for
    // nothing else (D7).
    let (strict, strict_stdout, stderr) =
        solve("fp_forward_error_strict.smt2", Some("--strict-proofs"));
    assert_eq!(
        strict, "unknown",
        "D7: --strict-proofs withholds an FP certificate pinned Carcara cannot parse: got \
         {strict:?}.\nstdout:\n{strict_stdout}\nstderr:\n{stderr}"
    );
    assert!(
        stderr.contains("(:reason-unknown (incomplete proof-trusted))")
            && stderr.contains("external-recheck surface is unsupported")
            && stderr.contains("FloatingPoint"),
        "the refusal must carry the typed reason and name the unsupported FloatingPoint \
         surface.\nstderr:\n{stderr}"
    );
    assert!(
        !stderr.contains("a trust or hole step reaches the empty clause"),
        "the forward-error refutation must be trust-free: the only refusal cause is the \
         surface.\nstderr:\n{stderr}"
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
