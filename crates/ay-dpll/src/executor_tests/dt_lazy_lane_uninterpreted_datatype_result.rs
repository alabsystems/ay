// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Pins for `#dt-lazy-uninterpreted-datatype-result`
//! (`executor/theories/euf/dt.rs`, `try_solve_dt_auflia_lazy`).
//!
//! The lazy DT+LIA lane builds a model of its own, and on a datatype-sorted
//! application of an UNINTERPRETED function — `(declare-fun g (Int) Lst)` used
//! under testers — it commits no value the publish funnel can read. The
//! independent gate answers `CannotConfirm` ("model commits no value for this
//! application of `g`") and `apply_independent_model_gate` fails closed on that
//! UNCONDITIONALLY, so the lane's `Sat` cannot be published at all; returning it
//! only denies the eager DT authority the turn in which it builds a model the
//! gate DOES confirm.
//!
//! Both windows below are `sat` under z3 5.1.0, were `sat` before the lane was
//! default-on at `solve_dt_uf_lia`, and became `unknown` with it — a WITHDRAWN
//! verdict. Each pin therefore asserts the published verdict AND the evidence
//! that makes it publishable, because a `sat` without
//! `model_check_gate.result = confirmed-sat` is the half-result this campaign
//! does not ship.

use crate::Executor;
use ay_frontend::parse;

fn execute(input: &str) -> (Executor, Vec<String>) {
    let commands = parse(input).expect("valid SMT-LIB test input");
    let mut executor = Executor::new();
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

/// Exhaustiveness shape: a datatype-sorted UF application constrained by two
/// testers that agree. `(g n)` is a `cons`, and nothing pins `n` or the fields —
/// the lane's model leaves the application itself unvalued.
const DEXH: &str = r#"
    (set-logic QF_UFDTLIA)
    (declare-datatypes ((Lst 0)) (((cons (hd Int) (tl Lst)) (nil))))
    (declare-fun g (Int) Lst)
    (declare-const n Int)
    (assert (not (is-nil (g n))))
    (assert (is-cons (g n)))
    (check-sat)
"#;

/// UF-result-under-tester shape: two applications of the same datatype-sorted
/// function are distinct and one is a `cons`. Satisfied by any `g` that is not
/// constant; again the lane values neither application.
const UF_DISTINCT: &str = r#"
    (set-logic QF_UFDTLIA)
    (declare-datatypes ((Lst 0)) (((cons (hd Int) (tl Lst)) (nil))))
    (declare-fun g (Int) Lst)
    (declare-const n Int)
    (declare-const m Int)
    (assert (distinct (g n) (g m)))
    (assert (is-cons (g n)))
    (check-sat)
"#;

#[test]
fn tester_over_datatype_sorted_uf_application_publishes_a_confirmed_sat() {
    let (executor, output) = execute(DEXH);
    assert_eq!(
        verdict(&output),
        "sat",
        "z3 5.1.0 answers `sat`; a lane whose model the gate cannot confirm must \
         fall back to the eager DT authority rather than withdraw the verdict"
    );
    assert_eq!(
        gate(&executor).as_deref(),
        Some("confirmed-sat"),
        "the published `sat` must carry the independent gate's confirmation"
    );
}

#[test]
fn distinct_datatype_sorted_uf_applications_publish_a_confirmed_sat() {
    let (executor, output) = execute(UF_DISTINCT);
    assert_eq!(
        verdict(&output),
        "sat",
        "z3 5.1.0 answers `sat`; the lane's unconfirmable witness must not \
         consume the route's terminal answer"
    );
    assert_eq!(
        gate(&executor).as_deref(),
        Some("confirmed-sat"),
        "the published `sat` must carry the independent gate's confirmation"
    );
}
