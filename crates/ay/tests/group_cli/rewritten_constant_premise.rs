// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `#rewritten-constant-premise`: a refutation whose only `assume` leaf is the
//! Boolean constant a DISCHARGED assertion collapsed to must never self-certify.
//!
//! Measured at 55e938d90 on `benchmarks/smt/QF_AX/storeinv_minimal.smt2`, whose
//! single authored assert is `(not (= (store a i (select a i)) a))`. AY answered
//!
//!   c ay.proof.certificate unproved_steps=0 foreign_assumes=no trust_free=yes
//!     ay_self_checkable=yes
//!   unsat
//!
//! beside the three-line artifact
//!
//!   (assume t0 false)
//!   (step t1 (cl (not false)) :rule false)
//!   (step t2 (cl) :rule resolution :premises (t0 t1))
//!
//! which carcara rejects at the first step ("could not match term to any of the
//! original problem premises: false"). Preprocessing had rewritten
//! `ctx.assertions` in place to the constant, and the leak-2 provenance set is
//! built from that stack, so the constant read as an authored premise. The
//! solver proved the assertion contradictory, discarded the argument, and
//! asserted bare `false` — the finite-enum pigeonhole class.
//!
//! Two properties, and BOTH matter:
//!   * a constant that only preprocessing produced is refused (`--self-check`
//!     answers `unknown`), and
//!   * a file that literally says `(assert false)` still self-certifies, because
//!     there the constant genuinely is a premise an external checker can match.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

/// Discharged by preprocessing: the ROW identity `store(a, i, select(a, i)) = a`
/// makes the one authored assert contradictory, and the assertion slot collapses
/// to `false`.
const DISCHARGED_TO_FALSE_SMT: &str = "\
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a () (Array Index Elem))
(declare-fun i () Index)
(assert (not (= (store a i (select a i)) a)))
(check-sat)
(exit)
";

/// The same discharged file plus one irrelevant `(assert true)`. Authorizing
/// `true` must NOT authorize `false`: an earlier version of the guard asked
/// only "is some Boolean constant authored?", so this single extra line
/// re-opened the laundering hole and certified an artifact carcara calls
/// invalid. Adversarial review found it one line away from the canary above.
const DISCHARGED_PLUS_ASSERT_TRUE_SMT: &str = "\
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a () (Array Index Elem))
(declare-fun i () Index)
(assert true)
(assert (not (= (store a i (select a i)) a)))
(check-sat)
(exit)
";

/// A quoted identifier whose decoded spelling is `false` remains a symbol; it
/// does not author the Boolean constant that preprocessing produced.
const DISCHARGED_PLUS_QUOTED_FALSE_SMT: &str = "\
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-sort Elem 0)
(declare-fun a () (Array Index Elem))
(declare-fun i () Index)
(declare-const |false| Bool)
(assert |false|)
(assert (not (= (store a i (select a i)) a)))
(check-sat)
(exit)
";

/// The constant really is the authored premise here.
const AUTHORED_FALSE_SMT: &str = "\
(set-logic QF_AX)
(set-info :status unsat)
(declare-sort Index 0)
(declare-fun i () Index)
(assert false)
(check-sat)
(exit)
";

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

/// Run `ay solve --self-check --proof <tmp>.alethe` and return
/// `(stdout, stderr, artifact)`.
fn run_self_check(stem: &str, contents: &str) -> (String, String, Option<String>) {
    static FILE_ID: AtomicUsize = AtomicUsize::new(0);
    let id = FILE_ID.fetch_add(1, Ordering::Relaxed);
    let base = std::env::temp_dir().join(format!(
        "ay_rewritten_constant_premise_{stem}_{}_{}",
        std::process::id(),
        id
    ));
    let path = base.with_extension("smt2");
    let proof_path = base.with_extension("alethe");
    std::fs::write(&path, contents).expect("write temp smt2");
    let _input_cleanup = CleanupGuard(path.clone());
    let _proof_cleanup = CleanupGuard(proof_path.clone());
    // The default emission path also writes `<input>.smt2.alethe`; clean it up.
    let _sibling_cleanup = CleanupGuard(PathBuf::from(format!("{}.alethe", path.display())));

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .arg("solve")
        .arg("--self-check")
        .arg("--proof")
        .arg(&proof_path)
        .arg("-T:60")
        .arg(&path)
        .output()
        .expect("spawn ay");

    (
        String::from_utf8_lossy(&output.stdout).into_owned(),
        String::from_utf8_lossy(&output.stderr).into_owned(),
        std::fs::read_to_string(&proof_path).ok(),
    )
}

fn verdict(stdout: &str) -> String {
    stdout
        .lines()
        .find(|line| matches!(line.trim(), "sat" | "unsat" | "unknown"))
        .unwrap_or_default()
        .trim()
        .to_string()
}

#[test]
fn a_preprocessing_discharged_assertion_does_not_launder_false_into_a_premise() {
    let (stdout, stderr, artifact) = run_self_check("discharged", DISCHARGED_TO_FALSE_SMT);

    assert_eq!(
        verdict(&stdout),
        "unknown",
        "a refutation whose only `assume` leaf is a preprocessing-produced \
         `false` has no argument at all and must not self-certify; \
         stdout={stdout:?} stderr={stderr:?} artifact={artifact:?}"
    );

    // Belt and braces: if an artifact was published anyway, it must not be the
    // bare `assume false` stub advertised as clean.
    if let Some(text) = &artifact {
        let bare_false_leaf = text
            .lines()
            .any(|line| line.trim() == "(assume t0 false)" || line.trim().ends_with(" false)"));
        let advertised_clean = stderr.lines().any(|line| {
            line.starts_with("c ay.proof.certificate ")
                && line.contains("foreign_assumes=no")
                && line.contains("trust_free=yes")
                && line.contains("ay_self_checkable=yes")
        });
        assert!(
            !(bare_false_leaf && advertised_clean),
            "an `assume false` leaf must never be disclosed as a clean \
             certificate; stderr={stderr:?} artifact={text:?}"
        );
    }
}

#[test]
fn an_authored_assert_false_still_self_certifies() {
    let (stdout, stderr, artifact) = run_self_check("authored", AUTHORED_FALSE_SMT);

    assert_eq!(
        verdict(&stdout),
        "unsat",
        "`(assert false)` really does assert the constant, so the guard must \
         not cost this verdict; stdout={stdout:?} stderr={stderr:?} \
         artifact={artifact:?}"
    );
}

#[test]
fn authoring_true_does_not_authorize_false_as_a_premise() {
    let (stdout, stderr, artifact) =
        run_self_check("discharged_plus_true", DISCHARGED_PLUS_ASSERT_TRUE_SMT);

    assert_eq!(
        verdict(&stdout),
        "unknown",
        "`(assert true)` authorizes `true` and nothing else; it must not \
         launder a preprocessing-produced `false` into a matchable premise; \
         stdout={stdout:?} stderr={stderr:?} artifact={artifact:?}"
    );

    if let Some(text) = &artifact {
        let bare_false_leaf = text
            .lines()
            .any(|line| line.trim() == "(assume t0 false)" || line.trim().ends_with(" false)"));
        let advertised_clean = stderr.lines().any(|line| {
            line.starts_with("c ay.proof.certificate ")
                && line.contains("foreign_assumes=no")
                && line.contains("trust_free=yes")
                && line.contains("ay_self_checkable=yes")
        });
        assert!(
            !(bare_false_leaf && advertised_clean),
            "published a bare `assume false` artifact advertised as clean; \
             artifact={text:?} stderr={stderr:?}"
        );
    }
}

#[test]
fn a_quoted_false_identifier_does_not_authorize_the_false_constant() {
    let (stdout, stderr, artifact) = run_self_check(
        "discharged_plus_quoted_false",
        DISCHARGED_PLUS_QUOTED_FALSE_SMT,
    );

    assert_eq!(
        verdict(&stdout),
        "unknown",
        "`|false|` is an ordinary quoted identifier, not the Boolean constant; \
         it must not authorize a preprocessing-produced `false` premise; \
         stdout={stdout:?} stderr={stderr:?} artifact={artifact:?}"
    );
}
