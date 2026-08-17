// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kill-switch coverage for the trace-free qpf instance-refutation authority
//! (#bitblast-original-clause-authority, #quant-unit-authority).
//!
//! This file deliberately holds ONE test in its own binary: it mutates the
//! process environment, which must never race sibling tests in a shared
//! process.

#![allow(clippy::panic)]

mod common;

/// The UFBV fixpoint universal the qpf lane refutes; with the campaign kill
/// switch OFF the publication gate must downgrade to the exact baseline
/// `unknown`, and with the switch back ON the same input must decide `unsat`.
/// Deleting either the call-site guard or the internal guard of
/// `checked_qpf_instance_refutation_authorizes_current_query` makes the OFF
/// half fail.
#[test]
fn qpf_bitblast_authority_is_fully_covered_by_the_kill_switch() {
    let smt = r#"
        (set-logic UFBV)
        (declare-fun fa0 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa1 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (declare-fun fa2 ((_ BitVec 8) (_ BitVec 8) (_ BitVec 8)) (_ BitVec 8))
        (assert (forall ((a0 (_ BitVec 8)) (a1 (_ BitVec 8)) (a2 (_ BitVec 8)))
          (=> (and (= a0 #x01) (= a1 (bvadd a0 #x01)) (= a2 (bvadd a1 #x01)))
              (and (= (fa0 a2 a1 a0) #x01)
                   (= (fa1 a2 a1 a0) (bvadd (fa0 a2 a1 a0) #x01))
                   (= (fa2 a2 a1 a0) (bvadd (fa1 a2 a1 a0) #x01))
                   (or (= a2 (fa0 a2 a1 a0)) (= a2 (fa1 a2 a1 a0)))))))
        (check-sat)
    "#;

    let off_guard = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
        no_quant_unit_authority: true,
        ..Default::default()
    });
    let off_results = common::solve_vec(smt);
    drop(off_guard);
    assert!(
        off_results.iter().any(|r| r == "unknown") && !off_results.iter().any(|r| r == "unsat"),
        "with the kill switch off every authority channel is disabled \
         and the publication gate must restore the baseline downgrade; got {off_results:?}"
    );

    let on_results = common::solve_vec(smt);
    assert!(
        on_results.iter().any(|r| r == "unsat"),
        "with the kill switch on (default) the recorded qpf instance must \
         re-derive a checked trace-free refutation and publish unsat; got {on_results:?}"
    );
}
