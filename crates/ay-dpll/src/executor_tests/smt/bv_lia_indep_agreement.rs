// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `_BV_LIA_INDEP` lanes that satisfy a mixed disjunction through different
//! branches (`executor/theories/combined/bv_lia_indep_agreement.rs`).
//!
//! Reduced from the TPA interpolant checks of model-checker-consumer
//! `safe_symbolic_from_elem` (its SingleLoop transition: Int locations, Bool
//! and BitVec arguments, a BitVec-indexed memory). Every query here is
//! satisfiable and z3 answers `sat`; before the agreement step AY handed the
//! independent gate a merged witness that falsifies the root (`[AY SOUNDNESS
//! GATE] caught an INVALID model`) and answered `unknown`.

use super::*;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap()
}

/// `sat`, the root true under the published model, and no witness the
/// independent gate refuted on the way. (The BV lane's own validation may
/// still reject its Int-blind witness, `MODEL-UNCONFIRMED`: that candidate is
/// withheld by design and never reaches the gate.)
fn assert_sat_with_no_gate_refutation(declarations: &str, root: &str) {
    let input = format!(
        "(set-logic ALL)\n(set-option :produce-models true)\n{declarations}\n\
         (assert {root})\n(check-sat)\n(get-value ({root}))\n(get-info :all-statistics)\n"
    );
    let outputs = run(&input);
    assert_eq!(outputs[0], "sat", "{root}: {outputs:?}");
    assert!(outputs[1].ends_with("true))"), "{root}: {}", outputs[1]);
    assert!(
        !outputs[2].contains("soundness-gate.invalid-models"),
        "{root}: the gate caught an invalid model: {}",
        outputs[2]
    );
}

const DECLARATIONS: &str = "(declare-const a Bool)\n(declare-const b Bool)\n\
     (declare-const m (Array (_ BitVec 64) (_ BitVec 32)))\n\
     (declare-const i (_ BitVec 64))\n(declare-const x (_ BitVec 32))\n\
     (declare-const l Int)";

#[test]
fn branch_disagreement_over_a_bitvec_array_read_is_sat() {
    assert_sat_with_no_gate_refutation(
        DECLARATIONS,
        "(or (and a (= (select m i) #x00000002)) (= l 1))",
    );
}

/// The reduced TPA check itself: a Bool argument pair, the memory read, and
/// an Int location.
#[test]
fn the_reduced_tpa_interpolant_check_is_sat() {
    assert_sat_with_no_gate_refutation(
        DECLARATIONS,
        "(or (and (= a b) (= (select m i) #x00000002)) (= l 1))",
    );
}

#[test]
fn branch_disagreement_over_a_bitvec_variable_is_sat() {
    assert_sat_with_no_gate_refutation(DECLARATIONS, "(or (and a (= x #x00000002)) (= l 1))");
}

/// Controls: with both branches closed the same disjunctions are unsat.
#[test]
fn closing_both_branches_is_unsat() {
    for root in [
        "(or (and a (= (select m i) #x00000002)) (= l 1))",
        "(or (and a (= x #x00000002)) (= l 1))",
    ] {
        let input = format!(
            "(set-logic ALL)\n{DECLARATIONS}\n(assert {root})\n\
             (assert (not (= l 1)))\n(assert (not (= x #x00000002)))\n\
             (assert (not (= (select m i) #x00000002)))\n(check-sat)\n"
        );
        assert_eq!(run(&input), vec!["unsat"], "{root}");
    }
}

/// The AUFLIA cross-check answering `unknown` (#bv-lia-indep-unknown-agreement).
///
/// Reduced from the TPA reachability checks of model-checker-consumer's per-row CHC route
/// over `safe_wide_array_as_bytes`, `safe_static_bytes` and
/// `safe_static_wide_as_bytes` (model-checker-consumer the development design notes
/// 2026-10-13-per-row-chc-route-still-trips-the-model-gate-d65293086`); the
/// names are the SingleLoop encoding's. The BV lane satisfies the root
/// through a branch its Int atoms make false (`(= .loc_k 1)` is an opaque
/// literal to it, and its witness values no Int term). The AUFLIA lane's own
/// validation refuses its witness, which leaves a BitVec variable of a
/// BitVec disequality at the default value the disequality excludes, so it
/// answers `unknown`. That arm then published the BV witness alone, and the
/// gate caught it. z3 answers `sat` on both.
const SINGLE_LOOP_DECLARATIONS: &str = "(declare-const .loc_4_2 Int)\n\
     (declare-const .loc_6_2 Int)\n(declare-const .loc_7_2 Int)\n\
     (declare-const .arg_4_0_1 (_ BitVec 64))\n(declare-const .arg_4_0_2 (_ BitVec 64))\n\
     (declare-const .arg_10_0_1 (_ BitVec 64))\n\
     (declare-const .arg_4_1_2 (Array (_ BitVec 64) (_ BitVec 8)))\n\
     (declare-const .arg_10_1_1 (Array (_ BitVec 64) (_ BitVec 8)))\n\
     (declare-const .arg_4_17_2 (_ BitVec 64))\n(declare-const .arg_2_17_1 (_ BitVec 64))\n\
     (declare-const .arg_4_18_2 (Array (_ BitVec 64) (_ BitVec 8)))\n\
     (declare-const .arg_2_18_1 (Array (_ BitVec 64) (_ BitVec 8)))\n\
     (declare-const .arg_6_2_2 Bool)\n(declare-const .arg_1_3_1 Bool)\n\
     (declare-const .arg_7_3_2 (_ BitVec 64))";

/// The agreement step decides it: AUFLIA, re-decided with the BV lane's
/// BitVec-predicate values, takes the BV lane's branch, and the merge holds.
#[test]
fn an_auflia_unknown_goes_through_the_agreement_step() {
    assert_sat_with_no_gate_refutation(
        SINGLE_LOOP_DECLARATIONS,
        "(or (and (= .loc_6_2 0) (= .arg_4_0_2 .arg_10_0_1) (= .arg_4_1_2 .arg_10_1_1)) \
         (and (= .loc_6_2 1) (not (= .arg_4_0_1 (_ bv0 64)))))",
    );
}

/// The 19 TPA checks that stayed `unknown` after the AUFLIA-unknown arm got
/// the agreement step needed two more things (#uninterpreted-bitvec-class-values,
/// #bv-lia-indep-pinned-bv-lane). Here AUFLIA's witness left `.arg_7_3_2` at the
/// default 0 against its committed `(= .arg_7_3_2 #x0000000400000002)`, so the
/// lane answered `unknown` and gave the agreement step no witness; and once it
/// valued that variable from its EUF class, it and the BV lane still took
/// different branches, the BV lane's `(= .loc_7_2 1)` and `(= .loc_4_2 0)`
/// opaque literals agreeing with no AUFLIA witness. The BV lane re-decided
/// under AUFLIA's arithmetic takes AUFLIA's branch. This answered `unknown`
/// at 29a0f2cab; z3 answers `sat`.
#[test]
fn lanes_that_agree_once_the_bv_lane_is_pinned_are_sat() {
    assert_sat_with_no_gate_refutation(
        SINGLE_LOOP_DECLARATIONS,
        "(or (and (= .loc_7_2 0) (= .arg_6_2_2 .arg_1_3_1)) \
         (and (= .loc_7_2 1) (= .loc_4_2 0) (= .arg_7_3_2 (_ bv17179869186 64))) \
         (and (= .loc_4_2 1) (= .loc_7_2 0) (= .arg_4_17_2 .arg_2_17_1) \
         (= .arg_4_18_2 .arg_2_18_1)))",
    );
}

/// Control: with every branch closed the same root is `unsat`. The pinned BV
/// lane's `unsat` is conditional on one AUFLIA witness and is never what
/// answers it.
#[test]
fn closing_every_pinned_branch_is_unsat() {
    let root = "(or (and (= .loc_7_2 0) (= .arg_6_2_2 .arg_1_3_1)) \
         (and (= .loc_7_2 1) (= .loc_4_2 0) (= .arg_7_3_2 (_ bv17179869186 64))) \
         (and (= .loc_4_2 1) (= .loc_7_2 0) (= .arg_4_17_2 .arg_2_17_1) \
         (= .arg_4_18_2 .arg_2_18_1)))";
    let input = format!(
        "(set-logic ALL)\n{SINGLE_LOOP_DECLARATIONS}\n(assert {root})\n\
         (assert (not (= .arg_6_2_2 .arg_1_3_1)))\n\
         (assert (not (= .arg_7_3_2 (_ bv17179869186 64))))\n\
         (assert (not (= .arg_4_17_2 .arg_2_17_1)))\n(check-sat)\n"
    );
    assert_eq!(run(&input), vec!["unsat"], "{root}");
}

/// A branch whose BitVec atom EUF cannot refute (`bvult` is an uninterpreted
/// predicate to AUFLIA) next to one the BV lane can meet: whichever lane
/// pins the other, the published witness takes the feasible branch.
#[test]
fn a_bitvec_infeasible_auflia_branch_is_not_published() {
    assert_sat_with_no_gate_refutation(
        SINGLE_LOOP_DECLARATIONS,
        "(or (and (= .loc_7_2 0) (bvult .arg_7_3_2 (_ bv0 64))) \
         (and (= .loc_7_2 1) (= .arg_7_3_2 (_ bv5 64))))",
    );
}
