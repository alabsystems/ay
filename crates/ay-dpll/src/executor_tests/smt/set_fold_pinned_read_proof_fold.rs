// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The deductive-checks set-fold obligation under PROOF PRODUCTION
//! (`C_sets/87167-00066` of the 2026-09-16 solver-fix round, reduced by a
//! greedy assertion deleter to the six-assertion ground core below).
//!
//! Two defects, both proof-mode only, both z3-`unsat`:
//!
//! * E-matching modulo the EUF model merged a `forall` body's own subterm
//!   (`(select inv x)` for the binder `x`) into a ground class, so the most
//!   specific trigger matched only `x := x` and the fallback trigger that
//!   carries the refutation never ran
//!   (`ematching/pattern.rs::augment_with_euf_model`,
//!   #ematching-model-class-ground).
//! * The dense-array pass that folds a pinned cell read into a bit-vector sum
//!   is gated off under proofs, so the BV/LIA bridge lane decomposed
//!   `(bvadd (select state 0) (select ordering 0))` over `bv2nat`, tied both
//!   arrays into the arithmetic lane, and the strict gate refused every
//!   candidate model (`arrays-read-conflict-uneval`) — `unknown (incomplete)`
//!   (`theories/bv_finite_array.rs::pinned_bv_array_read_fold_window`,
//!   #proof-capability).
//!
//! The no-proof twins were `unsat` before and stay `unsat`; the sat controls
//! flip the goal to an unconstrained cell and must never come back `unsat`.

use super::*;

/// Run a script the way the CLI drives it: command by command through the
/// AUTHORED boundary (`execute_authored`), which is the entry that may mint
/// the plain hard-query authority a `check-sat` from a file gets. The
/// generic `execute_all` boundary takes a different route and does not
/// reproduce either defect.
fn run_authored(exec: &mut Executor, input: &str) -> Vec<String> {
    let commands = parse(input).unwrap();
    let mut out = Vec::new();
    for cmd in &commands {
        if let Some(line) = exec.execute_authored(cmd).unwrap() {
            out.push(line);
        }
    }
    out
}

/// The CLI's plain-solve posture (`ay file.smt2`, batteries on): the
/// synthesized-default certificate is best-effort and budgeted
/// (`set_best_effort_produce_proofs`), which switches the tracker on and
/// records the proof during search — the posture under which both defects
/// show — and the command deadline (`--timeout`) scopes the lanes' internal
/// budgets. A bare executor records no proof and does not reproduce either.
fn verdict(input: &str) -> Vec<String> {
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000_000);
    exec.set_timeout(Some(std::time::Duration::from_secs(60)));
    run_authored(&mut exec, input)
}

/// The `--no-proof` / `--z3-mode` posture: the proof cycle is shed.
fn verdict_shed(input: &str) -> Vec<String> {
    let mut exec = Executor::new();
    exec.set_competition_mode(true);
    exec.set_timeout(Some(std::time::Duration::from_secs(60)));
    run_authored(&mut exec, input)
}

const DECLS: &str = r#"
        (declare-const __deductive_checks_collection_ctor_Set_usize_empty (Array (_ BitVec 64) Bool))
        (declare-const __set_len_insert_8 Int)
        (declare-const __set_fold_ordering_9 (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-const __set_fold_inv_10 (Array (_ BitVec 64) (_ BitVec 64)))
        (declare-const __set_fold_state_12 (Array (_ BitVec 64) (_ BitVec 64)))
"#;

/// The six-assertion ground core: `len = 1`, `ordering[0]` is in the
/// singleton set `{9}`, `state[0] = 0`, `state[1] = state[0] + ordering[0]`,
/// and the negated goal `state[int2bv(len)] != 9`.
const GROUND_CORE: &str = r#"
        (assert (! (= __deductive_checks_collection_ctor_Set_usize_empty ((as const (Array (_ BitVec 64) Bool)) false)) :named dn0))
        (assert (! (= 1 __set_len_insert_8) :named dn21))
        (assert (! (or (select (store __deductive_checks_collection_ctor_Set_usize_empty #x0000000000000009 true) (select __set_fold_ordering_9 #x0000000000000000)) (not (bvult #x0000000000000000 ((_ int2bv 64) __set_len_insert_8)))) :named dn22))
        (assert (! (= #x0000000000000000 (select __set_fold_state_12 #x0000000000000000)) :named dn33))
        (assert (! (or (not (bvult #x0000000000000000 ((_ int2bv 64) __set_len_insert_8))) (= (bvadd (select __set_fold_state_12 #x0000000000000000) (select __set_fold_ordering_9 #x0000000000000000)) (select __set_fold_state_12 #x0000000000000001))) :named dn35))
"#;

const GOAL_NEGATED: &str = r#"
        (assert (! (not (= #x0000000000000009 (select __set_fold_state_12 ((_ int2bv 64) __set_len_insert_8)))) :named dn39))
        (check-sat)
"#;

/// The same goal over the unconstrained cell `state[2]`: satisfiable.
const GOAL_UNCONSTRAINED_CELL: &str = r#"
        (assert (! (not (= #x0000000000000009 (select __set_fold_state_12 #x0000000000000002))) :named dn39))
        (check-sat)
"#;

fn query(body: &str) -> String {
    format!("(set-option :produce-unsat-cores true)\n(set-logic ALL)\n{DECLS}{body}")
}

/// The reduced ground core in the plain proof-carrying posture: was
/// `unknown (incomplete)`.
#[test]
fn ground_core_is_unsat_under_proof_production() {
    let input = query(&format!("{GROUND_CORE}{GOAL_NEGATED}"));
    let mut exec = Executor::new();
    exec.set_best_effort_produce_proofs(1_000_000);
    exec.set_timeout(Some(std::time::Duration::from_secs(60)));
    let out = run_authored(&mut exec, &input);
    if out != vec!["unsat"] {
        eprintln!("actual={out:?}");
        eprintln!(
            "reason={:?}",
            run_authored(&mut exec, "(get-info :reason-unknown)")
        );
    }
    assert_eq!(out, vec!["unsat"]);
}

/// The shed (`--no-proof`) twin, unchanged by the fold: the outer dense pass
/// already folds the pinned read there.
#[test]
fn ground_core_is_unsat_without_proofs() {
    let input = query(&format!("{GROUND_CORE}{GOAL_NEGATED}"));
    assert_eq!(verdict_shed(&input), vec!["unsat"]);
}

/// Sat control (z3: `sat`): the fold must not manufacture a refutation. The
/// CLI publishes `sat` here; the in-process best-effort posture fails closed
/// to `unknown` on both the pre-fix and the fixed tree, so the pin is the
/// soundness direction only.
#[test]
fn ground_core_with_unconstrained_goal_cell_is_never_unsat_under_proof_production() {
    let input = query(&format!("{GROUND_CORE}{GOAL_UNCONSTRAINED_CELL}"));
    let out = verdict(&input);
    assert_ne!(
        out,
        vec!["unsat"],
        "sat control must not be refuted: {out:?}"
    );
}

/// The captured obligation's second half with its two universals (the
/// surjection and the fold-step frame axioms) and the bounded-index ground
/// instances deductive-checks emits beside them. Proof-carrying: was
/// `unknown (quantifier-unhandled)`; z3: `unsat`.
const QUANTIFIED_FRAME: &str = r#"
        (assert (! (= __deductive_checks_collection_ctor_Set_usize_empty ((as const (Array (_ BitVec 64) Bool)) false)) :named dn0))
        (assert (! (ite (select __deductive_checks_collection_ctor_Set_usize_empty #x0000000000000009) (= 0 __set_len_insert_8) (= 1 __set_len_insert_8)) :named dn21))
        (assert (! (and (<= __set_len_insert_8 18446744073709551615) (<= 0 __set_len_insert_8)) :named dn40))
        (assert (! (or (select (store __deductive_checks_collection_ctor_Set_usize_empty #x0000000000000009 true) (select __set_fold_ordering_9 #x0000000000000000)) (not (bvult #x0000000000000000 ((_ int2bv 64) __set_len_insert_8)))) :named dn22))
        (assert (! (or (select (store __deductive_checks_collection_ctor_Set_usize_empty #x0000000000000009 true) (select __set_fold_ordering_9 #x0000000000000001)) (not (bvult #x0000000000000001 ((_ int2bv 64) __set_len_insert_8)))) :named dn23))
        (assert (! (or (not (bvult #x0000000000000000 ((_ int2bv 64) __set_len_insert_8))) (not (bvult #x0000000000000001 ((_ int2bv 64) __set_len_insert_8))) (not (= (select __set_fold_ordering_9 #x0000000000000000) (select __set_fold_ordering_9 #x0000000000000001)))) :named dn26))
        (assert (! (forall ((__set_fold_surj_x_11 (_ BitVec 64))) (or (and (bvult (select __set_fold_inv_10 __set_fold_surj_x_11) ((_ int2bv 64) __set_len_insert_8)) (= __set_fold_surj_x_11 (select __set_fold_ordering_9 (select __set_fold_inv_10 __set_fold_surj_x_11)))) (not (select (store __deductive_checks_collection_ctor_Set_usize_empty #x0000000000000009 true) __set_fold_surj_x_11)))) :named dn32))
        (assert (! (= #x0000000000000000 (select __set_fold_state_12 #x0000000000000000)) :named dn33))
        (assert (! (forall ((__set_fold_step_i_13 (_ BitVec 64))) (or (= (bvadd (select __set_fold_state_12 __set_fold_step_i_13) (select __set_fold_ordering_9 __set_fold_step_i_13)) (select __set_fold_state_12 (bvadd __set_fold_step_i_13 #x0000000000000001))) (not (bvult __set_fold_step_i_13 ((_ int2bv 64) __set_len_insert_8))))) :named dn34))
        (assert (! (or (not (bvult #x0000000000000000 ((_ int2bv 64) __set_len_insert_8))) (= (bvadd (select __set_fold_state_12 #x0000000000000000) (select __set_fold_ordering_9 #x0000000000000000)) (select __set_fold_state_12 #x0000000000000001))) :named dn35))
        (assert (! (or (not (bvult #x0000000000000001 ((_ int2bv 64) __set_len_insert_8))) (= (bvadd (select __set_fold_state_12 #x0000000000000001) (select __set_fold_ordering_9 #x0000000000000001)) (select __set_fold_state_12 #x0000000000000002))) :named dn36))
"#;

#[test]
fn quantified_frame_is_unsat_under_proof_production() {
    let input = query(&format!("{QUANTIFIED_FRAME}{GOAL_NEGATED}"));
    assert_eq!(verdict(&input), vec!["unsat"]);
}

#[test]
fn quantified_frame_is_unsat_without_proofs() {
    let input = query(&format!("{QUANTIFIED_FRAME}{GOAL_NEGATED}"));
    assert_eq!(verdict_shed(&input), vec!["unsat"]);
}

/// Sat control with the universals present (z3: `sat`). A quantified `sat`
/// may legitimately fail closed to `unknown`; what it must never do is come
/// back `unsat`.
#[test]
fn quantified_frame_with_unconstrained_goal_cell_is_never_unsat() {
    let input = query(&format!("{QUANTIFIED_FRAME}{GOAL_UNCONSTRAINED_CELL}"));
    let out = verdict(&input);
    assert_ne!(
        out,
        vec!["unsat"],
        "sat control must not be refuted: {out:?}"
    );
}
