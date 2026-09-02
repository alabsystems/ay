// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scope of the `MODEL-UNCONFIRMED` transcript diagnostic.
//!
//! The deferred-trust discharge corroborates a refutation by re-solving it in a
//! fresh `Executor`. That probe reaches the same publication funnel and, when
//! its own proof leans on a trust step, cannot certify ITSELF -- but the outer
//! certification can still succeed. Narrating the probe's failure on the shared
//! transcript reported a problem the user's query did not have.
//!
//! Both directions are asserted here: the probe must stay silent, and a genuine
//! user-level non-certification must still be announced. Suppressing the second
//! would hide an uncertified verdict, which is the whole point of the line.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use ntest::timeout;

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
        let _ = std::fs::remove_file(self.0.with_extension("smt2.alethe"));
    }
}

fn run(args: &[&str], script: &str) -> (i32, String, String) {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let path = std::env::temp_dir().join(format!(
        "ay_unconfirmed_scope_{}_{}.smt2",
        std::process::id(),
        ID.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, script).unwrap();
    let _guard = CleanupGuard(path.clone());

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg(&path)
        .output()
        .expect("failed to spawn ay");
    (
        output.status.code().expect("ay died on a signal"),
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
    )
}

/// The corroborating probe must not narrate its own non-certification.
///
/// Assuming `p` forces `x < 0` against `x > 0`. The outer certification
/// discharges every collected trust clause and publishes a CERTIFIED `unsat`,
/// so nothing about this query is unconfirmed -- yet the probe's diagnostic
/// used to appear on stderr and made it look otherwise.
#[test]
#[timeout(30_000)]
fn a_corroborating_probe_does_not_report_its_own_non_certification() {
    let (code, stdout, stderr) = run(
        &["--z3-mode"],
        "(set-logic QF_LIA)\n\
         (declare-const x Int)\n\
         (declare-const p Bool)\n\
         (assert (=> p (< x 0)))\n\
         (assert (> x 0))\n\
         (check-sat-assuming (p))\n",
    );

    assert_eq!(stdout.trim(), "unsat", "stderr={stderr}");
    assert_eq!(code, 0, "z3 exits 0 here: {stderr}");
    assert!(
        !stderr.contains("MODEL-UNCONFIRMED"),
        "the outer verdict IS certified; the probe must stay silent: {stderr}"
    );
}

/// ... but a genuine user-level non-certification is still announced.
///
/// The guard is scoped to nested discharge solves only. If it ever silenced the
/// user's own query, an uncertified verdict would ship unannounced -- strictly
/// worse than the noise it removes.
///
/// FIXTURE HISTORY: the original fixture (a `forall` over `f` refuted by one
/// ground instance) was chosen because AY could compute its UNSAT but not
/// certify it. The #quant-unit-authority campaign (c674b5e43 and successors)
/// deliberately taught the exact-fragment builder to certify precisely that
/// `forall_inst` chain, so the old fixture now publishes a trust-free,
/// self-checkable certificate and no longer exercises this announcement at
/// all. Today's fixture contradicts two `mod` constraints -- `x = 3 (mod 4)`
/// forces `x` odd while `x = 0 (mod 2)` forces it even -- which AY refutes
/// internally but cannot back with a fully-checked refutation proof, so
/// `--self-check` withholds the verdict through the same funnel
/// (`check_sat.rs` self-check gate -> `record_model_validation_unknown_diagnostic`).
/// If THIS fixture ever certifies too, replace it with another genuinely
/// uncertifiable query rather than deleting the assertions: the announcement
/// itself is what is under test.
#[test]
#[timeout(30_000)]
fn a_user_level_non_certification_is_still_announced() {
    let (_, stdout, stderr) = run(
        &["--self-check"],
        "(set-logic QF_LIA)\n\
         (declare-const x Int)\n\
         (assert (= (mod x 4) 3))\n\
         (assert (= (mod x 2) 0))\n\
         (check-sat)\n",
    );

    assert!(
        stderr.contains("MODEL-UNCONFIRMED"),
        "a verdict AY cannot certify must still say so: {stderr} / {stdout}"
    );
    assert!(
        stdout.contains("unknown"),
        "--self-check withholds an uncertified verdict: {stdout}"
    );
}
