// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The wire screen (`screen.rs`): a strict candidate whose PUBLISHED document
//! has a gap is reverted completely.
//!
//! On 938ec0327 every closed spelling measured with the lane's own candidate
//! renders without a `hole` at the COMMITTED state (`bvsub` at 8/64/96/128
//! bits, `bvmul` at 64/128; a closed 8-bit `bvsub` instance guard, which
//! printed as `hole` before the complete bit-blast series, is pinned Carcara
//! `valid` as `CLOSED_SUB_GUARD` in `carcara_external_check/ground_closure.rs`),
//! so the gap is reached here at the presentation boundary, through the same
//! `presents_wire_clean` export. A hole-free spelling pinned Carcara refuses
//! is out of this screen's sight; `EVALUATED_OPERATORS` keeps those out of
//! the search instead (`tests/operators.rs`).

use super::*;

/// One authored assertion, the negated 4-bit quotient-remainder identity.
const QUOTIENT_REMAINDER: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_BV)
    (declare-const m (_ BitVec 4))
    (declare-const n (_ BitVec 4))
    (assert (not (= m (bvadd (bvmul (bvudiv m n) n) (bvurem m n)))))
    (check-sat)
"#;

/// The screen's render asks the complete bit-blast only until the solve's
/// stop (`make_proof_assembly_should_stop`), as the authored cascade's does:
/// stopped, a proof of the authored assertion by the one `BvBitBlast` lemma
/// only the complete bit-blast lowers presents as not clean and runs no
/// refutation. The twin: unstopped, the same proof presents clean, through
/// that refutation.
///
/// Counterfactual: with `renders_wire_clean` rendering through the
/// exporter's `try_export_alethe_with_authored_surfaces` (the complete
/// bit-blast `Asked`, which no stop reaches), the stopped screen runs the
/// lemma's refutation and answers clean.
#[test]
fn the_presentation_screen_honours_the_solve_stop() {
    use ay_proof::resolution_dag_memo::{reset_resolution_dag_memo, resolution_dag_memo_counters};
    use std::sync::atomic::{AtomicBool, Ordering};
    use std::sync::Arc;

    let mut exec = solved(QUOTIENT_REMAINDER, "unsat");
    let root = *exec.ctx.assertions.last().expect("the authored assertion");
    assert!(matches!(exec.ctx.terms.get(root), TermData::Not(_)));
    let refuted = exec.ctx.terms.mk_not_raw(root);
    let mut proof = Proof::new();
    let assumption = proof.add_assume(root, None);
    let lemma = proof.add_theory_lemma_with_kind("bv", vec![refuted], TheoryLemmaKind::BvBitBlast);
    proof.add_resolution(Vec::new(), root, assumption, lemma);

    let interrupt = Arc::new(AtomicBool::new(true));
    exec.set_solve_controls(Some(interrupt.clone()), None);
    reset_resolution_dag_memo();
    assert!(
        !exec.presents_wire_clean(&proof),
        "a stopped render is not clean"
    );
    assert_eq!(resolution_dag_memo_counters(), (0, 0), "no refutation ran");

    interrupt.store(false, Ordering::Relaxed);
    reset_resolution_dag_memo();
    assert!(
        exec.presents_wire_clean(&proof),
        "the unstopped render is clean"
    );
    assert_ne!(
        resolution_dag_memo_counters(),
        (0, 0),
        "through the complete bit-blast's refutation"
    );
}

/// The lane's candidate for the executed fixture: the closure refutes it
/// and the strict checker accepts the emitted derivation.
fn strict_candidate(exec: &mut Executor) -> (GroundRoots, Proof) {
    let mut search = GroundSearch::default();
    let roots = exec.ground_closure_roots().expect("ground roots");
    let foralls = exec.flat_ground_closure_foralls();
    let conflict = exec
        .saturate_ground_search(&mut search, &roots.search, &foralls)
        .expect("the closure refutes the instance");
    let candidate = exec
        .emit_ground_closure_refutation(&search, conflict)
        .expect("a candidate is emitted");
    assert!(exec
        .check_proof_strict_with_datatypes(&candidate)
        .is_ok_and(|quality| quality.is_complete()));
    (roots, candidate)
}

/// Commit `candidate` over a placeholder and require the lane to revert it
/// completely: the exact incumbent proof, override table and both premise
/// ledgers, and the cascade member then leaves the placeholder alone.
fn assert_reverted(exec: &mut Executor, roots: &GroundRoots, candidate: Proof) {
    let mut proof = placeholder();
    let before = (
        format!("{:?}", proof.steps),
        exec.last_proof_term_overrides.clone(),
    );
    let ledgers = (
        exec.last_proof_rebuild_originals.clone(),
        exec.last_proof_raw_original_assertions.clone(),
    );
    assert!(!exec.commit_raw_ground_closure(&mut proof, candidate, &roots.raw));
    assert_eq!(
        (
            format!("{:?}", proof.steps),
            exec.last_proof_term_overrides.clone()
        ),
        before
    );
    assert_eq!(
        (
            exec.last_proof_rebuild_originals.clone(),
            exec.last_proof_raw_original_assertions.clone(),
        ),
        ledgers,
        "a reverted candidate leaves no raw root in either premise ledger"
    );
    exec.replace_with_raw_authored_ground_closure_refutation(&mut proof);
    assert_eq!(format!("{:?}", proof.steps), before.0);
}

/// Unsat at `i = #x30`, and the closure refutes it strictly, but the guard
/// `(bvsge i #x30)` elaborates to `(bvsle #x30 i)`: the committed state
/// exports clean, while the published instance is re-spelled from the
/// authored `(=> (bvsge ..) ..)` body, under which the clausifying `or` step
/// has no spelling and ships as `hole`.
const NORMALIZED_GUARD: &str = r#"
    (set-option :produce-proofs true)
    (set-logic ALL)
    (declare-const data (Array (_ BitVec 8) (_ BitVec 8)))
    (assert (= data (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) #x07) #x30 #x08)))
    (assert (forall ((i (_ BitVec 8))) (=> (bvsge i #x30) (= (select data i) #x07))))
    (check-sat)
"#;

/// NEGATIVE TWIN of the publication path: the screen judges the bytes the
/// post-cascade presentation passes leave, so a candidate they would hole is
/// reverted after the commit -- the exact incumbent proof, override table and
/// both premise ledgers are restored -- and the verdict stays `unknown`.
/// Counterfactual (dt-array-rows review, 09b0371c6): with the screen
/// exporting the committed state only, this candidate is kept and the
/// published document is `holey`.
#[test]
fn a_candidate_the_presentation_passes_would_hole_is_never_committed() {
    let mut exec = solved(NORMALIZED_GUARD, "unknown");
    let (roots, candidate) = strict_candidate(&mut exec);
    assert_reverted(&mut exec, &roots, candidate);
}

/// The presentation screen runs the passes on a clone and restores every
/// executor field they write, whatever it decides.
#[test]
fn the_presentation_screen_leaves_no_trace() {
    let mut exec = solved(NORMALIZED_GUARD, "unknown");
    let (roots, candidate) = strict_candidate(&mut exec);
    for &root in &roots.raw {
        exec.record_raw_authored_problem_assertion(root);
    }
    let snapshot = |exec: &Executor| {
        (
            exec.last_proof_term_overrides.clone(),
            exec.last_proof_rebuild_originals.clone(),
            exec.last_proof_raw_original_assertions.clone(),
            exec.last_unsat_proof_reconstruction_suppressed,
            format!("{:?}", exec.last_proof_decline),
        )
    };
    let before = snapshot(&exec);
    let _ = exec.presents_wire_clean(&candidate);
    assert_eq!(snapshot(&exec), before);
    // Not vacuous: run bare, the same passes do write executor state here
    // (the authored spelling of the instance, at least).
    let mut presented = candidate.clone();
    exec.rehome_elaborated_conjunction_assumes(&mut presented);
    exec.restore_reachable_authored_assume_surface_overrides(&presented);
    assert_ne!(
        snapshot(&exec),
        before,
        "the presentation passes wrote nothing the screen had to restore"
    );
}

/// The single-assertion selector projection: its UNSAT proof is an `assume`,
/// one `DatatypeSelectorProject` lemma and a resolution, a lemma the Clean
/// dialect prints as `dt_project` and the pinned dialect as `hole`.
const DT_PROJECTION: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_DT)
    (declare-datatypes ((Pair 0)) (((mk (fst Int) (snd Int)))))
    (declare-const a Int)
    (declare-const b Int)
    (assert (not (= (fst (mk a b)) a)))
    (check-sat)
"#;

/// The screen judges the bytes the executor will PUBLISH, so it renders in
/// the executor's Alethe dialect: the same proof is wire-clean in the Clean
/// dialect, which prints the projection as `dt_project`, and not in the
/// pinned one, which prints it as `hole`.
///
/// Counterfactual (dt_project review round 2, mutant M8): with
/// `renders_wire_clean` rendering in the thread's default (Clean) dialect,
/// a pinned-dialect executor judged this proof wire-clean while its
/// published document carries the hole. No ground-closure candidate carries
/// a datatype lemma today, so this pins the screen's contract on the
/// executor's own proof rather than on a lane candidate.
#[test]
fn the_presentation_screen_renders_in_the_executor_dialect() {
    let mut exec = solved(DT_PROJECTION, "unsat");
    let proof = exec.last_proof.clone().expect("a proof after UNSAT");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::DatatypeSelectorProject,
                ..
            }
        )),
        "the fixture's proof carries the projection lemma: {:?}",
        proof.steps
    );
    assert!(
        exec.presents_wire_clean(&proof),
        "the Clean dialect prints the projection as dt_project"
    );
    exec.set_alethe_dialect(ay_proof::AletheDialect::PinnedCarcara);
    assert!(
        !exec.presents_wire_clean(&proof),
        "the pinned dialect prints the projection as hole"
    );
    exec.set_alethe_dialect(ay_proof::AletheDialect::Clean);
    assert!(
        exec.presents_wire_clean(&proof),
        "the judgement follows the dialect back"
    );
}
