// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use crate::Executor;
use ay_frontend::parse;

fn run(input: &str) -> Vec<String> {
    let cmds = parse(input).expect("parse");
    let mut exec = Executor::new();
    exec.execute_all(&cmds).expect("exec")
}

/// Non-proof propositional SAT exercises the incremental pipeline.
#[test]
fn test_propositional_incremental_sat_6705() {
    let r = run("(set-logic QF_BOOL)\n(declare-const a Bool)\n(assert a)\n(check-sat)");
    assert_eq!(r, vec!["sat"]);
}

/// Non-proof propositional UNSAT exercises the incremental pipeline.
#[test]
fn test_propositional_incremental_unsat_6705() {
    let r = run(
        "(set-logic QF_BOOL)\n(declare-const a Bool)\n(assert a)\n(assert (not a))\n(check-sat)",
    );
    assert_eq!(r, vec!["unsat"]);
}

/// Multi-clause propositional: (p ∨ q) ∧ (¬p ∨ r) ∧ (¬q ∨ r) ∧ ¬r is UNSAT.
#[test]
fn test_propositional_incremental_multi_clause_unsat_6705() {
    let r = run(r#"
        (set-logic QF_BOOL)
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-const r Bool)
        (assert (or p q))
        (assert (or (not p) r))
        (assert (or (not q) r))
        (assert (not r))
        (check-sat)
    "#);
    assert_eq!(r, vec!["unsat"]);
}
