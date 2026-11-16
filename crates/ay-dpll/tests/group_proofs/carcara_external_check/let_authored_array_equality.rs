// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An array equality authored through a `let` exports a certificate pinned
//! Carcara checks `valid` in its canonical invocation, with the `let` spelling
//! confined to the equality's own `assume`.
//!
//! REGRESSION (measured 2026-10-06 at 8b4bcfd5a, carcara 1.1.0 git 9a352ee):
//! `benchmarks/smt/QF_AUFLIA/storeinv_nf_size2.smt2` asserts
//!
//! ```text
//! (let ((?v_0 (store a2 i1 (select a1 i1))) (?v_1 (store a1 i1 (select a2 i1))))
//!   (= (store ?v_1 i2 (select ?v_0 i2)) (store ?v_0 i2 (select ?v_1 i2))))
//! ```
//!
//! and AY refused the whole export: "invalid surface proof step t18: no
//! or_pos instance over the printed surface reproduces this clause". The
//! authored `let` text was the equality's spelling at every print site: the
//! `ArrayRowChain` lemma printed before its `assume` and three congruence
//! explanations printed `hole`, because no lowering decomposes a `let`. The
//! same assertions without the `let` publish a `valid` certificate. The
//! printer now confines a certified `let` spelling to its `assume` before any
//! step prints (`ay-proof` `alethe_printer/let_assume_confinement.rs`), and
//! the congruence-explanation render check reads the table the export prints.
//!
//! `storeinv_cross_2idx_minimal` and `storeinv_nf_size3` stayed holey after the
//! fix with exactly their `let`-free twins' holes (an `ArrayGuardedRowExpansion`
//! and an `ArithClauseTautology` lowering gap that no `let` is involved in),
//! so they are not pinned here. The first gap is lowered since 2026-10-08
//! (`ay-proof` `alethe_printer/guarded_row_expansion.rs`), which makes
//! `storeinv_cross_2idx_minimal` `valid`; the second since 2026-10-09
//! (`ay-proof` `alethe_printer_eq_transitive_arith.rs`), which makes
//! `storeinv_nf_size3` `valid` (pinned in `arith_equality_chain.rs`).
//!
//! NEGATIVE CONTROL: the `let`-free twin is `Supported` and `valid` in both
//! invocations.

use super::{
    exact_carcara_verdict, parse, refuse_pinned_carcara_misjudgments, require_carcara_or_skip,
    workspace_root, CarcaraSurface, Executor,
};
use ntest::timeout;
use std::fmt::Write as _;
use std::path::Path;

/// The smallest two-binding form: one `let` over the assumed array equality.
const TWO_BINDING_LET: &str = "(set-logic QF_AUFLIA)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (let ((?v_0 (store a2 i1 (select a1 i1)))
              (?v_1 (store a1 i1 (select a2 i1))))
          (= (store ?v_1 i2 (select ?v_0 i2))
             (store ?v_0 i2 (select ?v_1 i2)))))
(assert (not (= (select a1 (sk a1 a2)) (select a2 (sk a1 a2)))))
(check-sat)
";

/// The measured corpus file.
const MEASURED: &str = "benchmarks/smt/QF_AUFLIA/storeinv_nf_size2.smt2";

/// [`TWO_BINDING_LET`] with the `let` expanded.
const LET_FREE_TWIN: &str = "(set-logic QF_AUFLIA)
(declare-fun a1 () (Array Int Int))
(declare-fun a2 () (Array Int Int))
(declare-fun i1 () Int)
(declare-fun i2 () Int)
(declare-fun sk ((Array Int Int) (Array Int Int)) Int)
(assert (= (store (store a1 i1 (select a2 i1)) i2 (select (store a2 i1 (select a1 i1)) i2))
           (store (store a2 i1 (select a1 i1)) i2 (select (store a1 i1 (select a2 i1)) i2))))
(assert (not (= (select a1 (sk a1 a2)) (select a2 (sk a1 a2)))))
(check-sat)
";

/// The problem-scoped document and its surface verdict; a `hole` or `trust`
/// step fails the test.
fn certificate(label: &str, problem: &str) -> (String, CarcaraSurface) {
    let mut session = String::new();
    for line in problem.lines().filter(|line| line.trim() != "(exit)") {
        writeln!(&mut session, "{line}").expect("write to String");
    }
    let script = format!("(set-option :produce-proofs true)\n{session}");
    let commands = parse(&script).unwrap_or_else(|e| panic!("{label}: {e}"));
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "{label}: {:?}",
        exec.unknown_reason()
    );
    let (document, surface) = exec
        .try_export_last_proof_alethe_for_problem_scope_with_carcara_surface()
        .unwrap_or_else(|| panic!("{label}: no retained proof"))
        .unwrap_or_else(|e| panic!("{label}: {e}"));
    assert!(
        !document.contains(":rule hole") && !document.contains(":rule trust"),
        "{label}: {document}"
    );
    (document, surface)
}

/// Every line carrying an authored `let` is one of the bridge's three: the
/// `assume` (`tK.a`), the `let` step (`tK.l`) and the `equiv_pos2` (`tK.e`).
fn let_spelling_is_confined_to_bridges(document: &str) -> bool {
    document
        .lines()
        .filter(|line| line.contains("(let "))
        .all(|line| {
            let Some(id) = line
                .strip_prefix("(assume ")
                .or_else(|| line.strip_prefix("(step "))
                .and_then(|rest| rest.split_whitespace().next())
            else {
                return false;
            };
            #[expect(
                clippy::case_sensitive_file_extension_comparisons,
                reason = "Alethe proof-step suffixes are case-sensitive identifiers, not filesystem extensions"
            )]
            let is_authored_bridge_step =
                id.ends_with(".a") || id.ends_with(".l") || id.ends_with(".e");
            is_authored_bridge_step
        })
}

/// Pinned Carcara with `--expand-let-bindings`.
fn expanding_carcara_verdict(carcara: &Path, problem: &str, proof: &str) -> (bool, String) {
    refuse_pinned_carcara_misjudgments("expanding Carcara verdict", problem, proof);
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write exact problem");
    std::fs::write(&proof_path, proof).expect("write exact proof");
    let output = std::process::Command::new(carcara)
        .args(["check", "--no-color", "--expand-let-bindings", "--"])
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run pinned Carcara");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let diagnostic = format!(
        "status={:?}; stdout={}; stderr={}",
        output.status.code(),
        stdout.trim(),
        String::from_utf8_lossy(&output.stderr).trim()
    );
    (
        output.status.success() && stdout.trim() == "valid",
        diagnostic,
    )
}

#[test]
#[timeout(240_000)]
fn a_let_authored_array_equality_exports_a_valid_certificate() {
    let carcara = require_carcara_or_skip();
    let measured = workspace_root().join(MEASURED);
    let benchmark = std::fs::read_to_string(&measured)
        .unwrap_or_else(|e| panic!("read {}: {e}", measured.display()));
    for (label, problem) in [
        ("two-binding let", TWO_BINDING_LET),
        ("storeinv_nf_size2", benchmark.as_str()),
    ] {
        let (document, surface) = certificate(label, problem);
        assert!(document.contains(":rule let)"), "{label}: {document}");
        assert!(
            let_spelling_is_confined_to_bridges(&document),
            "{label}: the let spelling leaked past its assume:\n{document}"
        );
        assert_eq!(surface, CarcaraSurface::WithoutLetExpansion, "{label}");
        if let Some(carcara) = carcara.as_deref() {
            let (plain, plain_why) = exact_carcara_verdict(carcara, problem, &document);
            assert!(
                plain,
                "{label}: canonical invocation: {plain_why}\n{document}"
            );
            let (expanding, expanding_why) = expanding_carcara_verdict(carcara, problem, &document);
            assert!(
                !expanding && expanding_why.contains("with rule 'let'"),
                "{label}: `--expand-let-bindings` refuses exactly the let step: {expanding_why}"
            );
        }
    }

    // NEGATIVE: the `let`-free twin.
    let (document, surface) = certificate("let-free twin", LET_FREE_TWIN);
    assert!(!document.contains("(let "), "{document}");
    assert_eq!(surface, CarcaraSurface::Supported);
    if let Some(carcara) = carcara.as_deref() {
        let (plain, plain_why) = exact_carcara_verdict(carcara, LET_FREE_TWIN, &document);
        assert!(plain, "{plain_why}");
        let (expanding, expanding_why) =
            expanding_carcara_verdict(carcara, LET_FREE_TWIN, &document);
        assert!(expanding, "{expanding_why}");
    }
}
