// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pins for `#dt-lazy-frontier-diet`
//! (`executor/theories/euf/dt.rs`, `try_solve_dt_auflia_lazy`): the
//! AUFLIA lazy lane arms the frontier tester diet for its depth-1
//! selector slice. The omission is verdict-preserving by the lane's
//! discipline — omitted (D)/(G) clauses are datatype tautologies over
//! frontier terms whose tester atoms occur nowhere else, a lane UNSAT
//! still refutes the authored assertions, and a lane `Sat` publishes
//! only through the independent gate. These two guards hold the
//! verdicts on a branching recursive datatype whose frontier terms
//! (`(l t)`, `(r t)`) carry the load: a gate-confirmed `sat`, and an
//! `unsat` whose contradiction is constructor disjointness on a
//! frontier term itself (decided by the lane or, if the diet makes it
//! miss, by the unchanged eager authority — never `sat`, never
//! `unknown`). Both inputs agree under z3 4.16.0.

use crate::Executor;
use ay_frontend::parse;

const FRONTIER_DIET_SAT: &str = r#"
(set-logic QF_UFDTLIA)
(declare-datatypes ((Tree 0)) (((node (l Tree) (r Tree) (v Int)) (wrap (c Tree)) (leaf (p Int)))))
(declare-fun f (Tree) Int)
(declare-fun t () Tree)
(assert (= (f (l t)) 5))
(assert (> (f (r t)) (f (l t))))
(assert (= t (node (leaf 1) (wrap (leaf 2)) 3)))
(check-sat)
"#;

const FRONTIER_DIET_UNSAT: &str = r#"
(set-logic QF_UFDTLIA)
(declare-datatypes ((Tree 0)) (((node (l Tree) (r Tree) (v Int)) (wrap (c Tree)) (leaf (p Int)))))
(declare-fun t () Tree)
(assert (= (l t) (leaf 1)))
(assert (= (l t) (wrap (leaf 1))))
(check-sat)
"#;

fn verdict_of(input: &str) -> (String, Executor) {
    let commands = parse(input).expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    let output = executor
        .execute_all(&commands)
        .expect("commands must execute");
    let verdict = output
        .iter()
        .rev()
        .map(|line| line.trim())
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .unwrap_or_default()
        .to_string();
    (verdict, executor)
}

#[test]
fn frontier_diet_lane_preserves_confirmed_sat() {
    let (verdict, executor) = verdict_of(FRONTIER_DIET_SAT);
    assert_eq!(verdict, "sat");
    assert_eq!(
        executor
            .statistics()
            .get_string("model_check_gate.result")
            .map(str::to_owned),
        Some("confirmed-sat".to_string()),
        "the published sat must carry the independent gate's confirmation"
    );
}

#[test]
fn frontier_diet_lane_preserves_frontier_disjointness_unsat() {
    let (verdict, _executor) = verdict_of(FRONTIER_DIET_UNSAT);
    assert_eq!(verdict, "unsat");
}
