// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pins for `#dt-lazy-bv-confirmed-sat`
//! (`executor/theories/euf/dt.rs`, `DtLazyAcceptance::SatWhenConfirmed`).
//!
//! The DT+BV routes took the sparse on-demand DT lane UNSAT-only: a lane
//! `Sat` was demoted to a lane miss so the eager authority — and its
//! datatype-carrying-array degrade gate and D0 model-e-graph recheck —
//! stayed terminal. On Certora-shaped problems (recursive datatype with
//! fan-out 7 over wide BV fields, DT used as a hash-input encoding) the
//! lane finds a model from ~500 sparse axioms while the eager authority
//! materializes tens of thousands of selector axioms at depth 3 and
//! memouts to `unknown` — so the demotion discarded the only reachable
//! verdict. The lane may now publish a `Sat` on these routes when the
//! independent fail-closed gate CONFIRMS the model against the authored
//! assertions and the D0 model-e-graph recheck is clean; anything less
//! remains a lane miss with the eager authority terminal.
//!
//! The window below is `sat` under z3 4.16.0; before this change AY
//! answered `unknown` at any tested budget up to 30 s (lane `Sat`
//! demoted at 13 base assertions, eager round generating 23,270
//! axioms / 67,257 terms; unbounded it eventually agrees). It asserts
//! the verdict AND
//! the gate evidence, because a `sat` without
//! `model_check_gate.result = confirmed-sat` is not publishable evidence.

use crate::Executor;
use ay_frontend::parse;

fn execute(input: &str) -> (Executor, Vec<String>) {
    execute_with_timeout(input, None)
}

fn execute_with_timeout(
    input: &str,
    timeout: Option<std::time::Duration>,
) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
    executor.set_timeout(timeout);
    let output = executor
        .execute_all(&commands)
        .expect("commands must execute");
    (executor, output)
}

fn verdict(output: &[String]) -> String {
    output
        .iter()
        .rev()
        .map(|line| line.trim().to_string())
        .find(|line| matches!(line.as_str(), "sat" | "unsat" | "unknown"))
        .unwrap_or_default()
}

fn gate(executor: &Executor) -> Option<String> {
    executor
        .statistics()
        .get_string("model_check_gate.result")
        .map(str::to_owned)
}

/// Certora-shaped DT+BV window: recursive datatype (fan-out 7) over BV64
/// fields with a DT->BV hash function. Every `x_i` is bound to a
/// constructor over earlier nodes and the BV constraints are trivially
/// satisfiable; only the eager selector frontier makes it hard.
const CERTORA_MINI: &str = r#"
    (set-logic QF_UFBVDT)
    (declare-datatypes ((Node 0)) (((leaf (lv (_ BitVec 64)))
      (n2 (a Node) (b Node) (v2 (_ BitVec 64)))
      (n4 (c Node) (d Node) (e Node) (f Node) (v4 (_ BitVec 64)))
      (n1 (g Node) (v1 (_ BitVec 64))))))
    (declare-fun h (Node) (_ BitVec 64))
    (declare-const x0 Node) (declare-const w0 (_ BitVec 64))
    (declare-const x1 Node) (declare-const w1 (_ BitVec 64))
    (declare-const x2 Node) (declare-const w2 (_ BitVec 64))
    (declare-const x3 Node) (declare-const w3 (_ BitVec 64))
    (declare-const x4 Node) (declare-const w4 (_ BitVec 64))
    (declare-const x5 Node) (declare-const w5 (_ BitVec 64))
    (assert (= x0 (leaf w0)))
    (assert (= (h x0) (bvadd w0 #x0000000000000001)))
    (assert (= x1 (n1 x0 w1)))
    (assert (= (h x1) (bvadd w1 #x0000000000000001)))
    (assert (= x2 (n2 x1 x0 w2)))
    (assert (= (h x2) (bvadd w2 #x0000000000000001)))
    (assert (= x3 (n4 x2 x1 x0 x2 w3)))
    (assert (= (h x3) (bvadd w3 #x0000000000000001)))
    (assert (= x4 (n1 x3 w4)))
    (assert (= (h x4) (bvadd w4 #x0000000000000001)))
    (assert (= x5 (n2 x4 x3 w5)))
    (assert (= (h x5) (bvadd w5 #x0000000000000001)))
    (assert (bvult w0 #x0000000000000100))
    (check-sat)
"#;

/// Negative control: the same shape with a constructor clash forced
/// through the hash equalities must stay `unsat` — the confirmed-Sat
/// acceptance must not let a spurious lane witness through when the
/// authored assertions are genuinely contradictory.
const CERTORA_MINI_CLASH: &str = r#"
    (set-logic QF_UFBVDT)
    (declare-datatypes ((Node 0)) (((leaf (lv (_ BitVec 64)))
      (n1 (g Node) (v1 (_ BitVec 64))))))
    (declare-const x Node)
    (declare-const w (_ BitVec 64))
    (assert (= x (leaf w)))
    (assert (is-n1 x))
    (check-sat)
"#;

#[test]
fn dtbv_lane_sat_publishes_when_independently_confirmed() {
    // Bounded budget: unbounded, the eager authority eventually reaches
    // the same `sat` (measured 78 s in a debug test run) — the lane's
    // contribution is reaching it inside a realistic budget, where the
    // eager frontier instead answers `unknown` (CLI: `unknown` at
    // `-T:20`/`T:30` before this change).
    let (executor, output) =
        execute_with_timeout(CERTORA_MINI, Some(std::time::Duration::from_secs(30)));
    assert_eq!(
        verdict(&output),
        "sat",
        "z3 answers `sat`; the sparse lane finds the witness and the \
         independent gate confirms it, so demoting it to the eager \
         authority (23k axioms -> unknown) withdraws a reachable verdict"
    );
    assert_eq!(
        gate(&executor).as_deref(),
        Some("confirmed-sat"),
        "the published `sat` must carry the independent gate's confirmation"
    );
}

#[test]
fn dtbv_constructor_clash_stays_unsat() {
    let (_executor, output) = execute(CERTORA_MINI_CLASH);
    assert_eq!(
        verdict(&output),
        "unsat",
        "`x = leaf(w)` with `is-n1(x)` is a constructor clash; no lane \
         acceptance may publish a witness for it"
    );
}
