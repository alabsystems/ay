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
///
/// Run with `-q`, not `--z3-mode`: `--z3-mode` never prints the line, so it
/// could not see the probe narrate.
#[test]
#[timeout(30_000)]
fn a_corroborating_probe_does_not_report_its_own_non_certification() {
    let (code, stdout, stderr) = run(
        &["-q"],
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
/// all. The next fixture contradicted two `mod` constraints (`x = 3 (mod 4)`
/// against `x = 0 (mod 2)`); the div/mod purification's `divmod_def`
/// derivation (35dd59b81) made that refutation strict-checked, so it now
/// certifies (`unsat_admission=strict-proof`) and `--self-check` publishes
/// `unsat`. Today's fixture asks for an integer square root of 2: AY refutes
/// `x * x = 2` over `Int` internally, but the nonlinear refutation rests on a
/// trust step (`unsat_admission=discharged-trust` in the default posture), so
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
        "(set-logic QF_NIA)\n\
         (declare-const x Int)\n\
         (assert (= (* x x) 2))\n\
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

/// A candidate the model gate rejected is withheld in EVERY mode, so the line
/// never calls it published.
///
/// On this SMT-COMP file model validation rejects the isolated QF_AUFLIA
/// ladder's model; the combiner re-solve (`#qfax-isolated-lane-retry`) then
/// builds a different model that passes validation, and `sat` is published.
/// Outside `--self-check` the line used to read `[UNCONFIRMED/published]`,
/// which read as the rejected model being published. `--self-check` publishes
/// the same `sat`, so the published model passed the fail-closed self-check.
///
/// WHICH model check rejects the candidate is not under test. Through
/// 7a0755f7a the strict arrays oracle refused it at assertion 60; the z3-parity
/// merge 7afcf77ae (which reworked the QF_AUFLIA read-pin repair) reshapes it,
/// and the evaluator now refuses its store definition at assertion 30
/// (`model validation incomplete`) before the oracle runs. Both are the model
/// gate refusing a candidate, and a tier read off the mode would print either
/// one as `[UNCONFIRMED/published]`.
///
/// If this file stops producing a rejected candidate, replace it with one that
/// does rather than dropping the first assertion: the label is what is tested.
#[test]
#[timeout(120_000)]
fn a_rejected_candidate_is_never_reported_as_published() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join(
        "../ay-dpll/tests/group_auflia/data/storecomm_invalid_t1_pp_sf_ni_00030_008.cvc.smt2",
    );
    let script =
        std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("read {}: {e}", path.display()));
    for args in [&[][..], &["--self-check"][..]] {
        let (code, stdout, stderr) = run(args, &script);
        assert_eq!(code, 0, "{args:?}: {stderr}");
        assert_eq!(stdout.trim(), "sat", "{args:?}: stderr={stderr}");
        let announced_withheld = stderr.lines().any(|line| {
            line.contains(
                "MODEL-UNCONFIRMED [UNCONFIRMED/withheld] (not a refutation — see [AY SOUNDNESS GATE] for caught invalid models) ",
            ) && (line.contains("strict model-validation oracle")
                || line.contains("model validation incomplete"))
        });
        assert!(
            announced_withheld,
            "{args:?}: the rejected candidate must be announced as withheld: {stderr}"
        );
        assert!(
            !stderr.contains("UNCONFIRMED/published"),
            "{args:?}: no candidate the gate rejected is published: {stderr}"
        );
    }
}

/// A publication-funnel refusal must not label itself `published`.
///
/// This is the other half of the scope question, and it bit a consumer. The
/// line's tier used to be read off `--self-check` alone, so at DEFAULT rigor a
/// verdict the UNSAT funnel had just REFUSED announced
/// `[UNCONFIRMED/published]` and then answered `unknown` two lines later. A
/// downstream project (deductive-checks) read the tier as the verdict and reported ay
/// as publishing an uncertified UNSAT. ay had done the opposite: it threw a
/// CORRECT refutation away.
///
/// FIXTURE. `Box`/`Unbox` over a one-constructor `Pair` datatype, with
/// `generic_id` pinned to the identity on the boxed value — the shape
/// deductive-checks's generic-return monomorphization emits. z3 answers `unsat`, and
/// so does this binary under `--no-proof`; with the default proof posture the
/// strict checker rejects an `eq_congruent_pred` step the producer
/// mis-attributed, the deferred-trust discharge cannot rescue it, and the
/// funnel withholds. If this fixture ever CERTIFIES, replace it with another
/// query the funnel refuses rather than deleting the assertions: the tier
/// label is what is under test, not this particular incompleteness.
#[test]
#[timeout(60_000)]
fn a_funnel_refusal_is_labelled_withheld_at_default_rigor() {
    let (_, stdout, stderr) = run(
        &[],
        "(set-logic ALL)\n\
         (declare-sort Poly 0)\n\
         (declare-datatypes ((P 0)) (((mkP (pa (_ BitVec 64)) (pb (_ BitVec 8))))))\n\
         (declare-fun unbox (Poly) P)\n\
         (declare-fun box (P) Poly)\n\
         (declare-fun gid (Poly) Poly)\n\
         (assert (= (mkP #x0000000000000009 #x02) (unbox (box (mkP #x0000000000000009 #x02)))))\n\
         (assert (or (= (unbox (box (mkP #x0000000000000009 #x02))) \
                        (unbox (gid (box (mkP #x0000000000000009 #x02))))) \
                     (not (= (box (mkP #x0000000000000009 #x02)) \
                             (gid (box (mkP #x0000000000000009 #x02)))))))\n\
         (assert (not (= #x0000000000000009 \
                         (pa (unbox (gid (box (mkP #x0000000000000009 #x02))))))))\n\
         (assert (= (box (mkP #x0000000000000009 #x02)) \
                    (gid (box (mkP #x0000000000000009 #x02)))))\n\
         (check-sat)\n",
    );

    assert!(
        stderr.contains("MODEL-UNCONFIRMED"),
        "fixture no longer reaches the funnel refusal — replace it: {stderr} / {stdout}"
    );
    assert!(
        stderr.contains("computed UNSAT rejected by mandatory strict certification"),
        "fixture must be refused by the UNSAT publication funnel: {stderr}"
    );
    assert!(
        !stderr.contains("[UNCONFIRMED/published]"),
        "a refused verdict is WITHHELD; the tier must not claim it shipped: {stderr}"
    );
    assert!(
        stderr.contains("[UNCONFIRMED/withheld]"),
        "the refusal must still name its tier: {stderr}"
    );
    assert!(
        stdout.contains("unknown") && !stdout.contains("unsat"),
        "the funnel withheld the verdict, so the answer is unknown: {stdout}"
    );
}
