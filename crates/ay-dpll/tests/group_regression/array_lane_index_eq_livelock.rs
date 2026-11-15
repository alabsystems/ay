// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The combiner's index pass must converge (#no-index-eq-livelock, z3-parity
//! campaign 2026-09-22/23).
//!
//! Store chains of depth >= 2 with SYMBOLIC store indices under one equality
//! plus an inequality read. z3 5.1.0 answers `sat` in a millisecond. The
//! AUFLIA route's first SAT model on these shapes decides the read index
//! equal to every store index, EUF proves the store-index pairs equal
//! transitively, and `propagate_array_index_info` asserted each pair into the
//! array solver as an external (sentinel) edge on EVERY Nelson-Oppen
//! fixpoint — claiming progress each time, although the atom-keyed
//! `known_equal` behind `undecided_index_pairs` never sees such an edge and
//! kept reporting the pair — until the loop's 100-iteration cap returned the
//! sound `Unknown` (`:smt.no_rounds_total 200` over two combiner checks,
//! `unknown (incomplete)` in 40 ms, both postures). The pass now restarts the
//! loop only when the edge or its reasons are new, and otherwise lets the
//! pair fall through to the model-value path, where it gets the SAT-level
//! `(= idx1 idx2)` split the array solver's ROW checks can consume.
//!
//! As a single QF_ALIA `check-sat` the two-assertion shape is decided on
//! main too: the arrays-to-LIA rescue saturates before it bails, and the
//! reads it interns feed the route's axiom fixpoint. Every path that reaches
//! the route WITHOUT that saturation — a UF application beside the problem,
//! an `(Array Int Bool)` beside it, a `push` scope — hit the cap on main
//! `f399eca07a`; those are the reproducers below (sat, confirmed, in 12–27
//! split-loop rounds with the fix). The plain shapes pin that the fix leaves
//! the rescue-decided path decided.
//!
//! Every verdict here agrees with z3 5.1.0 and the file's `:status`.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;
use std::time::Duration;

const STORE3_DECLS: &str = r#"
(declare-fun k0 () Int)
(declare-fun k4 () Int)
(declare-fun i0_0 () Int)
(declare-fun i0_2 () Int)
(declare-fun v0_0 () Int)
(declare-fun v0_1 () Int)
(declare-fun v0_2 () Int)
(declare-fun s0 () (Array Int Int))
(declare-fun t0 () (Array Int Int))
"#;

const STORE3_CHAIN: &str = r#"
(assert (= s0 (store (store (store t0 i0_0 v0_0) k4 v0_1) i0_2 v0_2)))
"#;

const STORE3_READ: &str = "(assert (> (select s0 k0) 3))\n";

fn store3(logic: &str, extra_decls: &str, body: &str, tail: &str) -> String {
    format!("(set-info :status sat)\n(set-logic {logic})\n{STORE3_DECLS}{extra_decls}{body}{tail}")
}

const STORE4_DECLS: &str = r#"
(declare-fun k0 () Int)
(declare-fun x () Int)
(declare-fun s () (Array Int Int))
(declare-fun t () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun v0 () Int)
(declare-fun i1 () Int)
(declare-fun v1 () Int)
(declare-fun i2 () Int)
(declare-fun v2 () Int)
(declare-fun i3 () Int)
(declare-fun v3 () Int)
(assert (= s (store (store (store (store t i0 v0) i1 v1) i2 v2) i3 v3)))
(assert (< (select s k0) x))
"#;

/// Depth two, `= 7` read: decided on main (the loop happened to converge);
/// it must stay decided.
const STORE2_READ_EQ_SAT: &str = r#"
(set-info :status sat)
(set-logic QF_ALIA)
(declare-fun k0 () Int)
(declare-fun x () Int)
(declare-fun s () (Array Int Int))
(declare-fun t () (Array Int Int))
(declare-fun i0 () Int)
(declare-fun v0 () Int)
(declare-fun i1 () Int)
(declare-fun v1 () Int)
(assert (= s (store (store t i0 v0) i1 v1)))
(assert (= (select s k0) 7))
(check-sat)
"#;

fn verdict(script: &str) -> Vec<String> {
    let commands = parse(script).unwrap();
    let mut exec = Executor::new();
    exec.set_timeout(Some(Duration::from_secs(20)));
    exec.execute_all(&commands).unwrap()
}

/// The QF_ALIA reproducer as a single check-sat: decided through the
/// rescue's saturation on main; it must stay `sat`.
#[test]
#[timeout(60_000)]
fn store3_read_sat_stays_decided_sat() {
    let script = store3(
        "QF_ALIA",
        "",
        &format!("{STORE3_CHAIN}{STORE3_READ}"),
        "(check-sat)\n",
    );
    assert_eq!(verdict(&script), vec!["sat"]);
}

/// A UF application beside the problem (QF_AUFLIA): the rescue does not
/// apply, and main ran both combiner checks to the 100-iteration cap.
#[test]
#[timeout(60_000)]
fn store3_read_beside_uf_is_decided_sat() {
    let script = store3(
        "QF_AUFLIA",
        "(declare-fun f (Int) Int)\n",
        &format!("{STORE3_CHAIN}{STORE3_READ}(assert (= (f k0) 1))\n"),
        "(check-sat)\n",
    );
    assert_eq!(verdict(&script), vec!["sat"]);
}

/// The same problem inside a `push` scope: the rescue declines incremental
/// mode, and main hit the cap.
#[test]
#[timeout(60_000)]
fn store3_read_under_push_is_decided_sat() {
    let script = store3(
        "QF_ALIA",
        "",
        &format!("(push 1)\n{STORE3_CHAIN}{STORE3_READ}"),
        "(check-sat)\n(pop 1)\n",
    );
    assert_eq!(verdict(&script), vec!["sat"]);
}

/// An `(Array Int Bool)` read beside it: the rescue supports only Int->Int
/// arrays, and main hit the cap.
#[test]
#[timeout(60_000)]
fn store3_read_beside_bool_array_is_decided_sat() {
    let script = store3(
        "QF_ALIA",
        "(declare-fun m () (Array Int Bool))\n",
        &format!("{STORE3_CHAIN}{STORE3_READ}(assert (select m k0))\n"),
        "(check-sat)\n",
    );
    assert_eq!(verdict(&script), vec!["sat"]);
}

/// Depth four, `< x` read, a UF beside it: the cap on main.
#[test]
#[timeout(60_000)]
fn store4_read_lt_beside_uf_is_decided_sat() {
    let script = format!(
        "(set-info :status sat)\n(set-logic QF_AUFLIA)\n{STORE4_DECLS}\
         (declare-fun f (Int) Int)\n(assert (= (f k0) 1))\n(check-sat)\n"
    );
    assert_eq!(verdict(&script), vec!["sat"]);
}

/// Depth four, `< x` read, as a single QF_ALIA check-sat: rescue-decided on
/// main; it must stay `sat`.
#[test]
#[timeout(60_000)]
fn store4_read_lt_stays_decided_sat() {
    let script =
        format!("(set-info :status sat)\n(set-logic QF_ALIA)\n{STORE4_DECLS}(check-sat)\n");
    assert_eq!(verdict(&script), vec!["sat"]);
}

#[test]
#[timeout(60_000)]
fn store2_read_eq_sat_stays_decided_sat() {
    assert_eq!(verdict(STORE2_READ_EQ_SAT), vec!["sat"]);
}
