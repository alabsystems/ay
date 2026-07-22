// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Minimal repro for BV+Array sort mismatch crash in PDR.

use ay_chc::{testing, PdrConfig, PdrResult};
use ntest::timeout;

/// Minimal case: BV-indexed array with variable-index store, BV scalar property.
/// Crashes with "mk_bvult expects BitVec args" because __p0_a0 (Array sort) ends
/// up in a bvult expression.
#[test]
#[timeout(10_000)]
fn repro_bv_array_sort_mismatch() {
    let input = r#"
(set-logic HORN)
(declare-fun |inv| ( (Array (_ BitVec 32) Bool) (_ BitVec 32) ) Bool)

; Init
(assert
  (forall ( (ov (Array (_ BitVec 32) Bool)) (cnt (_ BitVec 32)) )
    (=>
      (and
        (= cnt #x00000000)
        (= ov ((as const (Array (_ BitVec 32) Bool)) false))
      )
      (inv ov cnt)
    )
  )
)

; Transition: store at variable index, increment counter
(assert
  (forall (
    (ov (Array (_ BitVec 32) Bool)) (cnt (_ BitVec 32))
    (ov2 (Array (_ BitVec 32) Bool)) (cnt2 (_ BitVec 32))
  )
    (=>
      (and
        (inv ov cnt)
        (bvult cnt #x0000000A)
        (= ov2 (store ov cnt true))
        (= cnt2 (bvadd cnt #x00000001))
      )
      (inv ov2 cnt2)
    )
  )
)

; Bad: counter exceeds bound
(assert
  (forall ( (ov (Array (_ BitVec 32) Bool)) (cnt (_ BitVec 32)) )
    (=>
      (and (inv ov cnt) (bvugt cnt #x0000000B))
      false
    )
  )
)

(check-sat)
(exit)
"#;
    let mut config = PdrConfig::default();
    config.solve_timeout = Some(std::time::Duration::from_secs(5));
    config.verbose = true;
    let result = testing::pdr_solve_from_str(input, config);
    // The BV scalar property (cnt <= 11) is provable by PDR even with Array params.
    // Scalarization projects out the array, and the BV counter invariant is discoverable.
    // Asserting Safe (not just !Unsafe) catches regressions where the solver bails to Unknown.
    assert!(
        matches!(result, Ok(PdrResult::Safe(_))),
        "Expected Safe for BV+Array sort mismatch problem, got {result:?}"
    );
}
