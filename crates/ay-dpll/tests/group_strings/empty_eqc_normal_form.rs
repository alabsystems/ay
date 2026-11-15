// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The empty-string EQC's normal form in word-equation comparison.
//!
//! When a concat term lands in the equivalence class of `""`, the core solver
//! compares its normal form against that class's own, the singleton `[rep]`.
//! That component used to be treated as the constant `""`, so a non-empty
//! variable facing it was sent to a ConstSplit against the empty constant: a
//! debug build panicked (`ConstSplit char_offset 0 >= constant y length 0`)
//! and answered `unknown` ("internal solver error"); a release build degraded
//! the split to an EmptySplit and could not refute. The component is now
//! skipped, and N_ENDPOINT_EQ infers the rest of the concat empty.
//!
//! The formula is the case `proptest_strings_soundness` shrank to. It is
//! UNSATISFIABLE (`y` cannot start with both "cc" and "by"); z3 4.16.0 answers
//! `unsat`. The path it takes depends on term numbering: dropping even the
//! unused `x` declaration avoids it, so it is kept verbatim.

use crate::common::{run_executor_smt_with_timeout, SolverOutcome};
use ntest::timeout;

#[test]
#[timeout(60_000)]
fn concat_in_the_empty_class_is_refuted_without_a_split_on_the_empty_constant() {
    let outcome = run_executor_smt_with_timeout(
        r#"(set-logic QF_S)
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (str.contains y "xab"))
(assert (str.prefixof "cc" y))
(assert (str.contains y "byaa"))
(assert (str.prefixof "by" y))
(assert (str.prefixof "aaa" z))
(check-sat)
"#,
        10,
    )
    .unwrap_or_else(|e| panic!("executor error: {e}"));
    assert_eq!(
        outcome,
        SolverOutcome::Unsat,
        "y cannot have both prefixes \"cc\" and \"by\"; z3 answers unsat"
    );
}
