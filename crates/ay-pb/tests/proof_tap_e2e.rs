// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0
//
// End-to-end proof-tap validation (proof-tap spec M5): the native CDCL solver
// runs the DENSE conflict-analysis fast path with micro-op capture
// (`PbCdclSolver::with_proof_tap_interruptible`), the serializer thread emits
// a VeriPB v3 proof, and the OFFICIAL VeriPB checker accepts it. Gated on the
// checker being present (VERIPB_BIN env, `veripb` on PATH, or the cert_ci.sh
// cache path) so CI without it skips gracefully.

use std::io::BufWriter;
use std::path::PathBuf;
use std::process::Command;

use ay_pb::cdcl::{PbCdclResult, PbCdclSolver};

fn veripb_bin() -> Option<PathBuf> {
    if let Some(p) = std::env::var_os("VERIPB_BIN") {
        let p = PathBuf::from(p);
        if p.exists() {
            return Some(p);
        }
    }
    if let Ok(path) = which_veripb() {
        return Some(path);
    }
    let cache = std::env::var_os("XDG_CACHE_HOME")
        .map(PathBuf::from)
        .or_else(|| std::env::var_os("HOME").map(|h| PathBuf::from(h).join(".cache")))?;
    let default = cache.join("ay-veripb/VeriPB/target/release/veripb");
    default.exists().then_some(default)
}

fn which_veripb() -> Result<PathBuf, ()> {
    let out = Command::new("which")
        .arg("veripb")
        .output()
        .map_err(|_| ())?;
    if !out.status.success() {
        return Err(());
    }
    let path = String::from_utf8_lossy(&out.stdout).trim().to_string();
    if path.is_empty() {
        return Err(());
    }
    Ok(PathBuf::from(path))
}

struct TapRun {
    result: PbCdclResult,
    stats: ay_pb::PbCdclStats,
    proof: String,
    verdict: Option<String>,
}

/// Solves `opb` with the proof tap and (when the checker is present) runs the
/// OFFICIAL VeriPB checker over the produced proof. Panics on any proof
/// error; returns the solver result plus the checker verdict line.
fn solve_with_tap_and_check(label: &str, opb: &str) -> TapRun {
    let instance = ay_pb::parse_opb(opb).expect("test OPB parses");
    let dir = std::env::temp_dir().join(format!("ay_proof_tap_{label}_{}", std::process::id()));
    std::fs::create_dir_all(&dir).expect("create temp dir");
    let opb_path = dir.join("instance.opb");
    let proof_path = dir.join("proof.pbp");
    std::fs::write(&opb_path, opb).expect("write opb");

    let proof_file = std::fs::File::create(&proof_path).expect("create proof file");
    let mut solver =
        PbCdclSolver::with_proof_tap_interruptible(&instance, BufWriter::new(proof_file), || false)
            .expect("tap solver constructs");
    let result = solver.solve_interruptible(|| false);
    solver
        .conclude_proof()
        .unwrap_or_else(|e| panic!("[{label}] proof must conclude cleanly: {e}"));
    let stats = solver.stats().clone();
    drop(solver);

    let proof = std::fs::read_to_string(&proof_path).expect("read back proof");

    let verdict = veripb_bin().map(|veripb| {
        let output = Command::new(&veripb)
            .arg(&opb_path)
            .arg(&proof_path)
            .output()
            .expect("run veripb");
        let stdout = String::from_utf8_lossy(&output.stdout).to_string();
        let stderr = String::from_utf8_lossy(&output.stderr).to_string();
        stdout
            .lines()
            .find(|l| l.starts_with("s "))
            .map(str::to_string)
            .unwrap_or_else(|| format!("NO-VERDICT\nstdout: {stdout}\nstderr: {stderr}"))
    });
    if verdict.is_none() {
        eprintln!("[{label}] VeriPB checker not present; proof-text checks only");
    }

    let _ = std::fs::remove_dir_all(&dir);
    TapRun {
        result,
        stats,
        proof,
        verdict,
    }
}

fn assert_verified_unsat(label: &str, run: &TapRun) {
    assert!(
        matches!(run.result, PbCdclResult::Unsatisfiable),
        "[{label}] expected UNSAT, got {:?}",
        run.result
    );
    assert!(
        run.proof.contains("conclusion UNSAT"),
        "[{label}] proof must conclude UNSAT:\n{}",
        run.proof
    );
    if let Some(verdict) = &run.verdict {
        assert!(
            verdict.starts_with("s VERIFIED"),
            "[{label}] official checker rejected the tap proof: {verdict}\nproof:\n{}",
            run.proof
        );
    }
}

/// Root-conflict UNSAT (no frames): header + contradiction RUP + conclusion.
#[test]
fn tap_certifies_trivial_unsat() {
    let run = solve_with_tap_and_check(
        "trivial",
        "* #variable= 1 #constraint= 2\n+1 x1 >= 1 ;\n-1 x1 >= 0 ;\n",
    );
    assert_verified_unsat("trivial", &run);
}

/// Clausal UNSAT over 2 vars (all four sign combinations): exercises real
/// conflict-analysis frames through the dense path.
#[test]
fn tap_certifies_clausal_unsat_with_frames() {
    let run = solve_with_tap_and_check(
        "clausal",
        "* #variable= 2 #constraint= 4\n\
         +1 x1 +1 x2 >= 1 ;\n\
         +1 x1 +1 ~x2 >= 1 ;\n\
         +1 ~x1 +1 x2 >= 1 ;\n\
         +1 ~x1 +1 ~x2 >= 1 ;\n",
    );
    assert_verified_unsat("clausal", &run);
    assert!(
        run.proof.contains("pol "),
        "expected at least one tap-generated pol frame:\n{}",
        run.proof
    );
}

/// Pigeonhole PHP(4,3): needs genuine search (decisions + backjumps), so the
/// proof contains multiple dense frames and the empty-lemma root refutation.
#[test]
fn tap_certifies_pigeonhole_4_3() {
    let run = solve_with_tap_and_check(
        "php43",
        "* #variable= 12 #constraint= 7\n\
         +1 x1 +1 x2 +1 x3 >= 1 ;\n\
         +1 x4 +1 x5 +1 x6 >= 1 ;\n\
         +1 x7 +1 x8 +1 x9 >= 1 ;\n\
         +1 x10 +1 x11 +1 x12 >= 1 ;\n\
         -1 x1 -1 x4 -1 x7 -1 x10 >= -1 ;\n\
         -1 x2 -1 x5 -1 x8 -1 x11 >= -1 ;\n\
         -1 x3 -1 x6 -1 x9 -1 x12 >= -1 ;\n",
    );
    assert_verified_unsat("php43", &run);
    assert!(
        run.stats.conflicts > 0,
        "php(4,3) must produce conflicts, got stats {:?}",
        run.stats
    );
}

/// Coefficient-heavy UNSAT: exercises the proven round-to-one weakening +
/// division replay (non-unit c/w and partial weakening pairs).
#[test]
fn tap_certifies_coefficient_heavy_unsat() {
    let run = solve_with_tap_and_check(
        "coeffs",
        "* #variable= 4 #constraint= 2\n\
         +3 x1 +3 x2 +5 x3 +5 x4 >= 12 ;\n\
         +3 ~x1 +3 ~x2 +5 ~x3 +5 ~x4 >= 5 ;\n",
    );
    assert_verified_unsat("coeffs", &run);
}

/// A wider PB UNSAT family mixing cardinality rows and weighted rows, sized
/// to force deep search so many frames flow through the ring.
#[test]
fn tap_certifies_weighted_pigeonhole_5_4() {
    let mut opb = String::from("* #variable= 20 #constraint= 9\n");
    // 5 pigeons x 4 holes; var index = (p-1)*4 + h.
    for p in 0..5 {
        let base = p * 4;
        opb.push_str(&format!(
            "+2 x{} +2 x{} +2 x{} +2 x{} >= 2 ;\n",
            base + 1,
            base + 2,
            base + 3,
            base + 4
        ));
    }
    for h in 1..=4 {
        opb.push_str(&format!(
            "-1 x{} -1 x{} -1 x{} -1 x{} -1 x{} >= -1 ;\n",
            h,
            h + 4,
            h + 8,
            h + 12,
            h + 16
        ));
    }
    let run = solve_with_tap_and_check("wphp54", &opb);
    assert_verified_unsat("wphp54", &run);
}

/// FAIL-CLOSED (hard rule): a sink that dies mid-proof must degrade to
/// "correct answer, NO certificate" — `conclude_proof` errors, the solve
/// verdict is unaffected, and nothing pretends to be a proof.
#[test]
fn tap_sink_failure_voids_the_proof_but_preserves_the_verdict() {
    struct FailAfter {
        writes_left: usize,
    }
    impl std::io::Write for FailAfter {
        fn write(&mut self, buf: &[u8]) -> std::io::Result<usize> {
            if self.writes_left == 0 {
                return Err(std::io::Error::other("injected sink failure"));
            }
            self.writes_left -= 1;
            Ok(buf.len())
        }
        fn flush(&mut self) -> std::io::Result<()> {
            Ok(())
        }
    }

    let opb = "* #variable= 12 #constraint= 7\n\
         +1 x1 +1 x2 +1 x3 >= 1 ;\n\
         +1 x4 +1 x5 +1 x6 >= 1 ;\n\
         +1 x7 +1 x8 +1 x9 >= 1 ;\n\
         +1 x10 +1 x11 +1 x12 >= 1 ;\n\
         -1 x1 -1 x4 -1 x7 -1 x10 >= -1 ;\n\
         -1 x2 -1 x5 -1 x8 -1 x11 >= -1 ;\n\
         -1 x3 -1 x6 -1 x9 -1 x12 >= -1 ;\n";
    let instance = ay_pb::parse_opb(opb).expect("test OPB parses");
    // A handful of writes cover the proof header (each `writeln!` may issue
    // several); the derivation + conclusion need many more, so the sink dies
    // mid-proof no matter how the writes split.
    let mut solver =
        PbCdclSolver::with_proof_tap_interruptible(&instance, FailAfter { writes_left: 8 }, || {
            false
        })
        .expect("header fits the write budget");
    let result = solver.solve_interruptible(|| false);
    assert!(
        matches!(result, PbCdclResult::Unsatisfiable),
        "the verdict must survive a dead proof sink, got {result:?}"
    );
    let err = solver
        .conclude_proof()
        .expect_err("a failed sink must void the certificate");
    let message = err.to_string();
    assert!(
        !message.is_empty(),
        "the stored proof error should describe the failure"
    );
}

/// SAT decision instance: the tap concludes with the witness and the checker
/// validates the SAT conclusion.
#[test]
fn tap_certifies_sat_witness() {
    let run = solve_with_tap_and_check(
        "sat",
        "* #variable= 3 #constraint= 3\n\
         +1 x1 +1 x2 >= 1 ;\n\
         +2 x2 +1 x3 >= 2 ;\n\
         +1 ~x1 +1 ~x3 >= 1 ;\n",
    );
    assert!(
        matches!(run.result, PbCdclResult::Satisfiable(_)),
        "expected SAT, got {:?}",
        run.result
    );
    assert!(
        run.proof.contains("conclusion SAT"),
        "proof must conclude SAT:\n{}",
        run.proof
    );
    if let Some(verdict) = &run.verdict {
        assert!(
            verdict.starts_with("s VERIFIED"),
            "official checker rejected the SAT tap proof: {verdict}\nproof:\n{}",
            run.proof
        );
    }
}

/// FOLLOW-ON A (empty-lemma root refutation — closes the PHASE 3 residual): a
/// pair of complementary cardinality rows whose sum is `0 >= 1`. DENSE conflict
/// analysis resolves the single conflict down to an EMPTY `0 >= degree>0` lemma
/// at RoundingSat getAssertionLevel == -1 (conflict_dense.rs:459-489). Because
/// the frame's `pol` chain id IS itself a checker-verified contradiction,
/// handle_unsat_proof concludes UNSAT DIRECTLY on that id (proof_logging.rs:214-
/// 234) instead of emitting a redundant fresh `rup >= 1 ;`. This is the first
/// full solver+checker run that exercises the 469 shortcut end to end.
#[test]
fn tap_certifies_empty_lemma_root_refutation() {
    let run = solve_with_tap_and_check(
        "empty_lemma",
        "* #variable= 3 #constraint= 2\n\
         +1 x1 +1 x2 +1 x3 >= 2 ;\n\
         +1 ~x1 +1 ~x2 +1 ~x3 >= 2 ;\n",
    );
    assert_verified_unsat("empty_lemma", &run);

    // The empty-lemma path concludes on the frame's chain id, NOT a fresh
    // `rup >= 1 ;` contradiction step: no derivation line may start with `rup`.
    assert!(
        !run.proof.lines().any(|l| l.trim_start().starts_with("rup")),
        "empty-lemma refutation must NOT emit a redundant contradiction RUP:\n{}",
        run.proof
    );
    // The last derivation line (immediately before `output NONE;`) is the `pol`
    // frame the conclusion points at — proof of a chain-id conclusion.
    let last_derivation = run
        .proof
        .lines()
        .take_while(|l| !l.starts_with("output NONE;"))
        .filter(|l| !l.trim().is_empty())
        .last()
        .expect("proof has a derivation section");
    assert!(
        last_derivation.starts_with("pol "),
        "conclusion must land on a pol chain id (last derivation = {last_derivation:?}):\n{}",
        run.proof
    );
    // The single dense frame is allocated id 3 (input rows 1,2 then the frame),
    // and the UNSAT conclusion references exactly it.
    assert!(
        run.proof.contains("conclusion UNSAT : 3;"),
        "conclusion must reference the empty-lemma chain id 3:\n{}",
        run.proof
    );
    assert_eq!(
        run.stats.conflicts, 1,
        "the complementary-cardinality pair refutes in exactly one conflict, got {:?}",
        run.stats
    );
}

/// FOLLOW-ON B item-3 (delete-through-suppression whitelist) is DEFERRED, not
/// silently gapped: tap-mode optimization proof is a not-yet-built phase, so a
/// suppressed OPT re-solve — and the del-through-suppression whitelist it guards
/// (should_suppress_optimization_intermediate_proof_step) — is UNREACHABLE under
/// the tap. This pins the explicit fail-closed fence (cdcl.rs
/// solve_optimize_*_with_stop): a tap solver entering the OPT loop stores
/// TapUnsupportedStep and voids the tap, so conclude_proof REFUSES to commit an
/// OPT proof rather than emitting an unsuppressed or unconcludable one. When
/// tap-mode OPT lands, this test changes.
#[test]
fn tap_mode_optimization_fails_closed_no_committed_proof() {
    let opb = "* #variable= 2 #constraint= 1\nmin: 1 x1 1 x2 ;\n+1 x1 +1 x2 >= 1 ;\n";
    let instance = ay_pb::parse_opb(opb).expect("opb parses");
    let objective = instance.objective.clone().expect("has min objective");
    let sink: Vec<u8> = Vec::new();
    let mut solver = PbCdclSolver::with_proof_tap_interruptible(&instance, sink, || false)
        .expect("tap solver constructs");
    let _ = solver.solve_optimize_interruptible(&objective, None, || false);
    // The OPT-loop fence stored ProofError::TapUnsupportedStep and dropped the
    // tap; conclude_proof must surface it — never commit an OPT proof.
    let err = solver
        .conclude_proof()
        .expect_err("tap-mode optimization must fail closed, never commit an OPT proof");
    assert!(
        format!("{err}").to_lowercase().contains("tap"),
        "expected a tap-unsupported proof error, got: {err}"
    );
}
