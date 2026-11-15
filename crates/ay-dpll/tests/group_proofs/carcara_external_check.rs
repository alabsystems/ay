// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::print_stderr)]

use ay_core::Sort;
use ay_dpll::api::{CarcaraSurface, Logic, Solver, StrictProofVerdict};
use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::collections::BTreeSet;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicBool, AtomicU64, Ordering};
use std::sync::Arc;

#[path = "carcara_external_check/arith_equality_chain.rs"]
mod arith_equality_chain;
#[path = "carcara_external_check/arithmetic_use_site_spellings.rs"]
mod arithmetic_use_site_spellings;
#[path = "carcara_external_check/artifact_dialect.rs"]
mod artifact_dialect;
#[path = "carcara_external_check/ashr_dialect.rs"]
mod ashr_dialect;
#[path = "carcara_external_check/authored_spelling_bridges.rs"]
mod authored_spelling_bridges;
#[path = "carcara_external_check/bv_conflict_clause.rs"]
mod bv_conflict_clause;
#[path = "carcara_external_check/chainable_equality_surface.rs"]
mod chainable_equality_surface;
#[path = "carcara_external_check/closed_guard.rs"]
mod closed_guard;
#[path = "carcara_external_check/closed_spelling_chain.rs"]
mod closed_spelling_chain;
#[path = "carcara_external_check/comparison_constant_instances.rs"]
mod comparison_constant_instances;
#[path = "carcara_external_check/datatype_selector_project.rs"]
mod datatype_selector_project;
#[path = "carcara_external_check/define_fun_reading.rs"]
mod define_fun_reading;
#[path = "carcara_external_check/duplicate_authored_root.rs"]
mod duplicate_authored_root;
#[path = "carcara_external_check/equated_universal.rs"]
mod equated_universal;
#[path = "carcara_external_check/expansion_certificate_assume.rs"]
mod expansion_certificate_assume;
#[path = "carcara_external_check/finite_expansion_provenance.rs"]
mod finite_expansion_provenance;
#[path = "carcara_external_check/folded_assertion_bridges.rs"]
mod folded_assertion_bridges;
#[path = "carcara_external_check/folded_atom_assumptions.rs"]
mod folded_atom_assumptions;
#[path = "carcara_external_check/folded_conjunction_assumptions.rs"]
mod folded_conjunction_assumptions;
#[path = "carcara_external_check/frame_ite_lift.rs"]
mod frame_ite_lift;
#[path = "carcara_external_check/ground_closure.rs"]
mod ground_closure;
#[path = "carcara_external_check/ground_instance_closure.rs"]
mod ground_instance_closure;
#[path = "carcara_external_check/guarded_instance_derivation.rs"]
mod guarded_instance_derivation;
#[path = "carcara_external_check/guarded_row_expansion.rs"]
mod guarded_row_expansion;
#[path = "carcara_external_check/instance_surface.rs"]
mod instance_surface;
#[path = "carcara_external_check/let_authored_array_equality.rs"]
mod let_authored_array_equality;
#[path = "carcara_external_check/named_label_uses.rs"]
mod named_label_uses;
#[path = "carcara_external_check/negated_goal_conjuncts.rs"]
mod negated_goal_conjuncts;
#[path = "carcara_external_check/negative_shorthand_congruence.rs"]
mod negative_shorthand_congruence;
#[path = "carcara_external_check/nia_negated_conjunct.rs"]
mod nia_negated_conjunct;
#[path = "carcara_external_check/nra_sos_lowering.rs"]
mod nra_sos_lowering;
#[path = "carcara_external_check/nullary_macro_assertions.rs"]
mod nullary_macro_assertions;
#[path = "carcara_external_check/or_pos_de_morgan_surface.rs"]
mod or_pos_de_morgan_surface;
#[path = "carcara_external_check/packed_eq_transitive.rs"]
mod packed_eq_transitive;
#[path = "carcara_external_check/permuted_disjunction_cong.rs"]
mod permuted_disjunction_cong;
#[path = "carcara_external_check/printed_split_guard.rs"]
mod printed_split_guard;
#[path = "carcara_external_check/problem_surface_invocation.rs"]
mod problem_surface_invocation;
#[path = "carcara_external_check/published_spelling.rs"]
mod published_spelling;
#[path = "carcara_external_check/qsat_evidence.rs"]
mod qsat_evidence;
#[path = "carcara_external_check/read_over_write_chain.rs"]
mod read_over_write_chain;
#[path = "carcara_external_check/replacement_proof_premises.rs"]
mod replacement_proof_premises;
#[path = "carcara_external_check/rewritten_universal_body.rs"]
mod rewritten_universal_body;
#[path = "carcara_external_check/skolem_channel_siblings.rs"]
mod skolem_channel_siblings;
#[path = "carcara_external_check/surface_accessor_dialect.rs"]
mod surface_accessor_dialect;
#[path = "carcara_external_check/swapped_macro_equality.rs"]
mod swapped_macro_equality;
#[path = "carcara_external_check/tseitin_equality_pivot.rs"]
mod tseitin_equality_pivot;
#[path = "carcara_external_check/vacuous_binder_constant.rs"]
mod vacuous_binder_constant;
include!("carcara_external_check/fixtures.rs");
fn workspace_root() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR"))
        .parent()
        .and_then(|p| p.parent())
        .expect("workspace root")
        .to_path_buf()
}

fn keep_alethe_artifacts() -> bool {
    ay_core::misc_cli_flags().keep_alethe_artifacts
}

fn find_carcara() -> Option<PathBuf> {
    if let Some(path) = std::env::var_os("CARCARA_PATH") {
        let path = PathBuf::from(path);
        assert!(
            path.is_file(),
            "CARCARA_PATH is configured but does not name a checker file: {}",
            path.display()
        );
        return Some(path);
    }

    if let Some(home) = std::env::var_os("HOME") {
        let candidate = PathBuf::from(home).join(".cargo/bin/carcara");
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    let candidates = [
        workspace_root().join("bin/carcara"),
        workspace_root().join("reference/carcara/target/release/carcara"),
        workspace_root().join("reference/carcara/target/researcher_20/release/carcara"),
        PathBuf::from("/tmp/carcara/target/release/carcara"),
        PathBuf::from("/usr/local/bin/carcara"),
        PathBuf::from("/opt/homebrew/bin/carcara"),
    ];
    for candidate in candidates {
        if candidate.is_file() {
            return Some(candidate);
        }
    }

    let path_var = std::env::var_os("PATH")?;
    for dir in std::env::split_paths(&path_var) {
        let candidate = dir.join("carcara");
        if candidate.is_file() {
            return Some(candidate);
        }
    }
    None
}

fn required_carcara_for_corpus() -> PathBuf {
    find_carcara().unwrap_or_else(|| {
        panic!(
            "the canonical external UNSAT corpus requires the real Carcara checker; \
             set CARCARA_PATH or install it with `cargo install --git \
             https://github.com/ufmg-smite/carcara.git`"
        )
    })
}

fn require_carcara_or_skip() -> Option<PathBuf> {
    if let Some(path) = find_carcara() {
        return Some(path);
    }

    assert!(
        std::env::var_os("CI").is_none(),
        "carcara not found. External Alethe verification is mandatory in CI.\n\
         Install: cargo install --git https://github.com/ufmg-smite/carcara.git"
    );

    eprintln!("carcara not found, skipping external Alethe verification");
    None
}

/// The shared refusal for every Carcara runner in this module: the corpus
/// helpers (`exact_carcara_verdict`, `carcara_verdict_without_allowances`) and
/// the bespoke ones. Called BEFORE the checker runs: pinned Carcara's verdict
/// on a flagged pair (`ay_core::pinned_carcara`) is not evidence in either
/// direction, so the runner fails the test rather than return a verdict any
/// assertion (`valid`, `holey`, `invalid`, or a tamper test's not-`valid`)
/// could pass on.
fn refuse_pinned_carcara_misjudgments(label: &str, problem: &str, proof: &str) {
    if let Err(misjudged) = ay_core::pinned_carcara::pinned_carcara_can_judge(problem, proof) {
        panic!("{label}: {misjudged}\n{proof}");
    }
}

fn exact_carcara_verdict(carcara: &Path, problem: &str, proof: &str) -> (bool, String) {
    refuse_pinned_carcara_misjudgments("exact Carcara verdict", problem, proof);
    let directory = tempfile::tempdir().expect("temporary Carcara directory");
    let problem_path = directory.path().join("problem.smt2");
    let proof_path = directory.path().join("proof.alethe");
    std::fs::write(&problem_path, problem).expect("write exact problem");
    std::fs::write(&proof_path, proof).expect("write exact proof");
    let output = std::process::Command::new(carcara)
        .arg("check")
        .arg("--no-color")
        .arg("--")
        .arg(&proof_path)
        .arg(&problem_path)
        .output()
        .expect("run production Carcara checker");
    let stdout = String::from_utf8_lossy(&output.stdout);
    let stderr = String::from_utf8_lossy(&output.stderr);
    let diagnostic = format!(
        "status={:?}; stdout={}; stderr={}",
        output.status.code(),
        stdout.trim(),
        stderr.trim()
    );
    (
        trust_free_carcara_verdict_is_valid(output.status.success(), &stdout),
        diagnostic,
    )
}

include!("carcara_external_check/runner.rs");
include!("carcara_external_check/evaluate_guard.rs");
include!("carcara_external_check/macro_capture_guard_tests.rs");
include!("carcara_external_check/aci_simp_guard.rs");
include!("carcara_external_check/ite_bv.rs");
include!("carcara_external_check/uf_lia.rs");
include!("carcara_external_check/corpus_rows.rs");
include!("carcara_external_check/corpus_oracle.rs");
include!("carcara_external_check/corpus.rs");
include!("carcara_external_check/model_checker_consumer_unsupported.rs");
include!("carcara_external_check/authored_assume.rs");
include!("carcara_external_check/normalized_bv.rs");
include!("carcara_external_check/equality_lattice_strict.rs");
include!("carcara_external_check/cut_chain_strict.rs");

/// Production gate for Trust's bounded E5 shift-count contradiction.
///
/// Native strict verification and external Carcara verification are separate
/// verdicts. The latter consumes the exact problem bytes carried beside the
/// proof artifact; both proof tampering and problem/surface substitution must
/// be independently rejected.
/// D7 (2026-09-22) negative control at the external-checker boundary: a
/// `Seq`-sorted artifact is PUBLISHED at the strict-checker class with
/// `carcara_surface = unsupported(...)`, and the pinned Carcara really cannot
/// parse it — so a consumer that hands the document to Carcara without
/// reading the disclosure gets a refusal, never a `valid`. The disclosure is
/// what lets a claiming consumer refuse BEFORE the round-trip, with the reason.
#[test]
#[timeout(60_000)]
fn test_seq_artifact_discloses_unsupported_surface_and_pinned_carcara_rejects_it() {
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    let mut solver = Solver::try_new(Logic::All).expect("ALL solver");
    solver.set_produce_proofs(true);
    solver
        .parse_smtlib2(
            "(declare-const s (Seq Int))\n\
             (assert (= (seq.len s) 1))\n\
             (assert (= (seq.len s) 2))\n",
        )
        .expect("seq fixture must parse");
    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat(),
        "seq length pinned twice: {details:?}"
    );
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("D7: the Seq artifact is published with its surface disclosed");
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(_)
    ));
    let reason = artifact
        .carcara_surface
        .unsupported_reason()
        .expect("the Seq surface is disclosed as unsupported")
        .to_string();
    assert!(reason.contains("(Seq Int)"), "{reason}");

    let problem = artifact.alethe_problem_smt2.clone().unwrap_or_else(|| {
        "(set-logic ALL)\n(declare-const s (Seq Int))\n(assert (= (seq.len s) 1))\n\
         (assert (= (seq.len s) 2))\n(check-sat)\n"
            .to_string()
    });
    let (valid, diagnostic) = exact_carcara_verdict(&carcara, &problem, &artifact.alethe);
    assert!(
        !valid,
        "pinned Carcara must NOT accept a Seq-sorted document it cannot parse: {diagnostic}"
    );
}

#[test]
#[timeout(60_000)]
fn test_e5_shift_exact_artifact_is_native_strict_and_carcara_valid() {
    let carcara = required_carcara_for_corpus();
    let mut solver = Solver::try_new(Logic::QfBv).expect("QF_BV solver");
    solver.set_produce_proofs(true);
    let x = solver.declare_const("x", Sort::bitvec(8));
    let zero = solver.bv_const(0, 8);
    let one = solver.bv_const(1, 8);
    let positive = solver.bvult(zero, x);
    let shifted = solver.bvlshr(x, one);
    let non_strict = solver.bvule(x, shifted);
    let contradiction = solver.and(positive, non_strict);
    solver.assert_term(contradiction);

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat(),
        "bounded shift contradiction must be UNSAT: {details:?}"
    );
    let artifact = solver
        .export_last_unsat_artifact()
        .expect("E5 UNSAT must export a proof artifact");
    assert!(matches!(
        artifact.strict_verdict,
        StrictProofVerdict::Verified(ref quality) if quality.is_complete()
    ));
    // D7 positive control: a QF_BV document is inside pinned Carcara's
    // grammar, says so, and round-trips through the real checker below.
    assert_eq!(
        artifact.carcara_surface,
        CarcaraSurface::Supported,
        "a QF_BV artifact must disclose a supported pinned-Carcara surface"
    );
    assert!(
        !artifact.alethe.contains(":rule hole") && !artifact.alethe.contains(":rule trust"),
        "external artifact must contain no unchecked rule:\n{}",
        artifact.alethe
    );
    let exact_problem = artifact
        .alethe_problem_smt2
        .as_deref()
        .expect("QF_BV artifact must carry exact checker problem bytes");
    let normalized_shift = "(concat #b0 ((_ extract 7 1) x))";
    assert!(exact_problem.contains(normalized_shift), "{exact_problem}");
    assert!(!exact_problem.contains("bvlshr"), "{exact_problem}");
    assert!(!exact_problem.contains("zero_extend"), "{exact_problem}");

    let (valid, diagnostic) = exact_carcara_verdict(&carcara, exact_problem, &artifact.alethe);
    assert!(
        valid,
        "exact E5 artifact must be Carcara-valid: {diagnostic}"
    );

    let tampered_proof = artifact
        .alethe
        .replacen(":rule bitblast_const", ":rule false", 1);
    assert_ne!(
        tampered_proof, artifact.alethe,
        "proof tamper target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(&carcara, exact_problem, &tampered_proof);
    assert!(!valid, "Carcara accepted a tampered proof: {diagnostic}");

    let tampered_problem = exact_problem.replacen("#b00000000", "#b00000001", 1);
    assert_ne!(
        tampered_problem, exact_problem,
        "problem tamper target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(&carcara, &tampered_problem, &artifact.alethe);
    assert!(!valid, "Carcara accepted a tampered problem: {diagnostic}");

    // A consumer rebuilding the pre-normalization source formula produces an
    // equivalent SMT proposition, but not the exact assumption surface bound
    // into this Alethe certificate. That pair must be refused.
    let rebuilt_problem = exact_problem.replacen(normalized_shift, "(bvlshr x #x01)", 1);
    assert_ne!(
        rebuilt_problem, exact_problem,
        "normalization-binding target missing"
    );
    let (valid, diagnostic) = exact_carcara_verdict(&carcara, &rebuilt_problem, &artifact.alethe);
    assert!(
        !valid,
        "Carcara accepted proof against consumer-rebuilt problem: {diagnostic}"
    );
}

/// The external-codegen GUARDED-division obligation, verbatim from a captured bridge
/// query. `(and (not (= b 0)) (not (= X X)))` folds to `false` at elaboration
/// and used to export the three-step `assume`/`hole`/`resolution` rescue —
/// `holey`, never `valid`. `promote_and_self_eq_contradiction_collapse` must
/// make it fully re-derivable by an INDEPENDENT checker.
///
/// Verified against the untouched problem text, never a re-derived assumption
/// scope: replaying AY's own printed assumes as the problem cannot detect an
/// `assume` that fails to match the real input.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_guarded_self_equality_division() {
    let problem = r#"
(set-logic QF_BV)
(declare-const a (_ BitVec 32))
(declare-const b (_ BitVec 32))
(assert (and (not (= b (_ bv0 32))) (not (= (bvsub a (bvmul (bvudiv a b) b)) (bvsub a (bvmul (bvudiv a b) b))))))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(problem, "guarded_self_eq_division");
    assert!(
        !proof.contains(":rule hole"),
        "guarded self-equality must not publish an unproved step:\n{proof}"
    );
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, "guarded_self_eq_division", problem, &proof),
        "guarded self-equality proof must be trust-free verifiable by carcara"
    );
}

/// A folded `let` assertion must remain source-exact at the assumption
/// boundary, then use the certified Alethe `let` bridge before `and_pos` sees
/// the expanded conjunction. AY's internal checker does not compare assumes
/// to the original SMT-LIB syntax, so only pinned Carcara catches this scope
/// mismatch.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_let_linear_conjunction_collapse() {
    let problem = r#"
(set-logic QF_LIA)
(declare-fun x0 () Int)
(declare-fun x1 () Int)
(assert (let ((?v_0 (* 1 x0)) (?v_1 (* (- 1) x0)))
  (and (<= (+ ?v_0 ?v_1) (- 1)) (<= (+ (* 1 x1) (* 0 x0)) 0))))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(problem, "let_linear_conjunction_collapse");
    assert!(
        !proof.contains(":rule hole") && !proof.contains(":rule trust"),
        "let conjunction collapse must remain fully proved:\n{proof}"
    );
    assert!(
        proof.contains(":rule let") && proof.contains(":rule and_pos"),
        "the proof must bridge the source let before extracting its conjunct:\n{proof}"
    );
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    // This is specifically a proof of let elimination. Carcara's
    // `--expand-let-bindings` erases the `let` term from the proof before it
    // can apply `:rule let`; run the pinned checker in AY's canonical
    // invocation, its ordinary parser mode, so both the source premise and
    // certified rule stay present (`problem_surface_invocation.rs`).
    let (valid, diagnostic) = exact_carcara_verdict(&carcara, problem, &proof);
    assert!(
        valid,
        "pinned Carcara must accept the source-exact let proof: {diagnostic}"
    );
}

/// The external-codegen memory-image obligation: a QF_ABV self-equality over
/// `select`/`store`/const-array terms. Two independent gaps kept this `holey`:
/// the faithful rebuilders had no array fragment, and AY's internal
/// `(const-array v)` spelling does not parse as SMT-LIB. Both are on the path
/// this test exercises, and the const-array one can only be caught by an
/// external checker — AY's own strict checker accepts the internal spelling.
#[test]
#[timeout(60_000)]
fn test_carcara_trust_free_array_backed_self_equality() {
    let problem = r#"
(set-logic QF_ABV)
(declare-const base (_ BitVec 64))
(declare-const val (_ BitVec 64))
(declare-const fill (_ BitVec 8))
(assert (not (= ((_ zero_extend 56) (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) fill) (bvadd base (_ bv8 64)) ((_ extract 7 0) val)) base))
                ((_ zero_extend 56) (select (store ((as const (Array (_ BitVec 64) (_ BitVec 8))) fill) (bvadd base (_ bv8 64)) ((_ extract 7 0) val)) base)))))
(check-sat)
"#;
    let proof = solve_unsat_and_get_proof(problem, "array_self_eq");
    assert!(
        !proof.contains(":rule hole"),
        "array self-equality must not publish an unproved step:\n{proof}"
    );
    assert!(
        !proof.contains("(const-array"),
        "AY's internal constant-array spelling does not parse as SMT-LIB:\n{proof}"
    );
    let Some(carcara) = require_carcara_or_skip() else {
        return;
    };
    assert!(
        run_carcara_trust_free(&carcara, "array_self_eq", problem, &proof),
        "array self-equality proof must be trust-free verifiable by carcara"
    );
}
