// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// The negative controls behind the binder-capture guard, against the real
// checker. The scan itself, `binders_pinned_carcara_misreads`, and its unit
// tests live in `ay_core::pinned_carcara::binder_capture`, shared by every
// Carcara runner in the workspace.

/// Pinned Carcara in the corpus runner's invocation with NO gate policy
/// applied: the control below must see the checker's own answer.
#[cfg(test)]
fn unguarded_plain_carcara_output(carcara: &Path, problem: &str, proof: &str) -> String {
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write control problem");
    std::fs::write(&proof_path, proof).expect("write control proof");
    let output = std::process::Command::new(carcara)
        .args(["check", "--no-color", "--"])
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run carcara check (control)");
    format!(
        "{:?} {}",
        carcara_stdout_verdict(
            output.status.success(),
            &String::from_utf8_lossy(&output.stdout)
        ),
        String::from_utf8_lossy(&output.stderr).trim()
    )
}

/// The negative controls behind the guard, end to end against the REAL
/// checker: both problems are SATISFIABLE (z3 `sat`), yet pinned Carcara
/// prints `valid` for these refutations of them in both gate invocations,
/// with no flag beyond them. Both shared verdict helpers must refuse either
/// before the checker runs, so no assertion in either direction passes on it.
#[test]
#[timeout(60_000)]
fn a_valid_verdict_on_a_problem_carcara_misreads_is_not_evidence() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let rebinding = "(set-logic ALL)\n(declare-const x Int)\n\
                     (assert (! (= x 5) :named c))\n\
                     (assert (exists ((c Bool)) (not c)))\n(check-sat)\n";
    let rebinding_proof = "(assume a0 (exists ((c Bool)) (not c)))\n\
         (assume a1 (= x 5))\n\
         (step t1 (cl (= (exists ((c Bool)) (not c)) (not c))) :rule qnt_rm_unused)\n\
         (step t2 (cl (not (= (exists ((c Bool)) (not c)) (not c))) \
         (not (exists ((c Bool)) (not c))) (not c)) :rule equiv_pos2)\n\
         (step t3 (cl (not c)) :rule resolution :premises (t2 t1 a0))\n\
         (step t4 (cl) :rule resolution :premises (t3 a1))\n";
    let capture = "(set-logic ALL)\n(declare-const y Int)\n\
                   (assert (! (= y 0) :named n))\n\
                   (assert (forall ((y Int)) n))\n(check-sat)\n";
    let capture_proof = "(assume a0 (forall ((y Int)) (= y 0)))\n\
         (step t1 (cl (or (not (forall ((y Int)) (= y 0))) (= 1 0))) :rule forall_inst :args (1))\n\
         (step t2 (cl (not (forall ((y Int)) (= y 0))) (= 1 0)) :rule or :premises (t1))\n\
         (step t3 (cl (= 1 0)) :rule resolution :premises (t2 a0))\n\
         (step t4 (cl (= (= 1 0) false)) :rule evaluate)\n\
         (step t5 (cl (not (= 1 0)) false) :rule equiv1 :premises (t4))\n\
         (step t6 (cl (not false)) :rule false)\n\
         (step t7 (cl) :rule resolution :premises (t3 t5 t6))\n";
    for (name, problem, proof) in [
        ("named_label_rebinding_control", rebinding, rebinding_proof),
        ("named_label_capture_control", capture, capture_proof),
    ] {
        assert_eq!(
            unguarded_carcara_verdict(&carcara, problem, proof),
            CarcaraVerdict::Valid,
            "{name}: pinned carcara no longer accepts this refutation of a satisfiable \
             problem under --expand-let-bindings; re-measure the capture guard"
        );
        let plain = unguarded_plain_carcara_output(&carcara, problem, proof);
        assert!(
            plain.starts_with("Valid"),
            "{name}: pinned carcara no longer accepts it in its plain invocation \
             either; re-measure the capture guard: {plain}"
        );
        assert_refused_as_not_evidence(&format!("{name}: no-allowance helper"), || {
            carcara_verdict_without_allowances(&carcara, name, problem, proof);
        });
        assert_refused_as_not_evidence(&format!("{name}: exact-verdict helper"), || {
            exact_carcara_verdict(&carcara, problem, proof);
        });
    }
}
