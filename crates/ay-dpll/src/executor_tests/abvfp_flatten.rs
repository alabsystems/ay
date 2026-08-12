// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Executor-level tests for the QF_ABVFP constant-index array-read elimination
//! (`executor/theories/fp/flatten_reads.rs`) and for the FP model values the
//! independent gate now reads.
//!
//! Two things are being pinned here, and the second matters more than the first:
//!
//! 1. **Capability** — a QF_ABVFP query whose only array uses are reads at
//!    bitvector-literal indices is now DECIDED instead of answered `unknown`.
//! 2. **Soundness** — the rewrite is an equivalence, so it must never turn a
//!    satisfiable input into `unsat` or an unsatisfiable input into `sat`, and it
//!    must ABSTAIN (keeping today's `unknown`) on every shape whose side
//!    condition fails. The index-aliasing test is the sharpest of these: keying
//!    cells on index SYNTAX rather than numeric VALUE would split one array cell
//!    into two independent variables and manufacture a false `sat`.

use crate::Executor;
use ay_frontend::parse;

fn solve(smt: &str) -> String {
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    outputs.join("\n")
}

fn verdict(output: &str) -> Option<&str> {
    output
        .lines()
        .map(str::trim)
        .find(|line| matches!(*line, "sat" | "unsat" | "unknown"))
}

// ---------------------------------------------------------------------------
// 1. Capability
// ---------------------------------------------------------------------------

/// A constant-index read feeding an FP predicate is now decided `sat`. Before
/// the pre-pass this whole shape returned `unknown` (the read-over-write
/// expansion is the identity with zero stores, so the array reads reached the
/// bit-blaster intact and the congruence relaxation degraded the `sat`).
#[test]
fn qf_abvfp_constant_index_read_decides_sat() {
    let smt = r#"
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (bvult (_ bv3 8) (select a (_ bv0 32))))
(assert (fp.isNaN ((_ to_fp 5 11) (concat (select a (_ bv1 32)) (select a (_ bv0 32))))))
(check-sat)
"#;
    assert_eq!(
        verdict(&solve(smt)),
        Some("sat"),
        "constant-index reads must be eliminated and the residue decided"
    );
}

/// The same lane must reach `unsat` when the cells are contradictory.
#[test]
fn qf_abvfp_constant_index_read_decides_unsat() {
    let smt = r#"
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (select a (_ bv7 32)) (_ bv1 8)))
(assert (= (select a (_ bv7 32)) (_ bv2 8)))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("unsat"));
}

// ---------------------------------------------------------------------------
// 2. Soundness — the rewrite is an equivalence in BOTH directions
// ---------------------------------------------------------------------------

/// THE keying test. `(_ bv4 32)` and `#x00000004` are the same index, so
/// `(select a (_ bv4 32))` and `(select a #x00000004)` are the SAME array cell
/// and cannot differ. Keying the fresh constants on index syntax would make
/// this `sat` — a fabricated model. It must be `unsat`.
#[test]
fn equal_index_values_written_differently_are_one_cell() {
    let smt = r#"
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (= (select a (_ bv4 32)) (select a #x00000004))))
(check-sat)
"#;
    assert_eq!(
        verdict(&solve(smt)),
        Some("unsat"),
        "two spellings of index 4 must collapse to one cell"
    );
}

/// Two DIFFERENT arrays read at the same index are independent, so their values
/// may differ: this must stay `sat`. (The mirror of the test above — aliasing
/// cells across arrays would wrongly make it `unsat`.)
#[test]
fn distinct_arrays_at_the_same_index_stay_independent() {
    let smt = r#"
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (= (select a (_ bv4 32)) (select b (_ bv4 32)))))
(check-sat)
"#;
    assert_eq!(verdict(&solve(smt)), Some("sat"));
}

/// A satisfiable input must never come back `unsat`. Distinct indices of one
/// array are independent cells, so every combination of values is available.
#[test]
fn satisfiable_input_is_never_turned_unsat() {
    let smt = r#"
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (select a (_ bv0 32)) (_ bv1 8)))
(assert (= (select a (_ bv1 32)) (_ bv2 8)))
(assert (not (= (select a (_ bv2 32)) (_ bv3 8))))
(check-sat)
"#;
    assert_ne!(
        verdict(&solve(smt)),
        Some("unsat"),
        "independent cells must not be forced equal"
    );
}

/// An unsatisfiable input must never come back `sat` — the FP side of the
/// formula stays live through the rewrite (nothing FP-sorted is abstracted).
#[test]
fn unsatisfiable_input_is_never_turned_sat() {
    let smt = r#"
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (select a (_ bv0 32)) (_ bv0 8)))
(assert (= (select a (_ bv1 32)) (_ bv0 8)))
(assert (fp.isNaN ((_ to_fp 5 11) (concat (select a (_ bv1 32)) (select a (_ bv0 32))))))
(check-sat)
"#;
    // `#x0000` is +zero, which is not NaN, so the conjunction is unsatisfiable.
    assert_ne!(
        verdict(&solve(smt)),
        Some("sat"),
        "the FP theory must still constrain the flattened residue"
    );
}

/// `store` breaks the side condition (cells become positionally dependent), so
/// the pass must ABSTAIN. The verdict must not be a wrong `sat`.
#[test]
fn store_bearing_input_is_never_answered_sat_by_this_lane() {
    let smt = r#"
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (= (select (store a (_ bv0 32) (_ bv5 8)) (_ bv0 32)) (_ bv6 8)))
(check-sat)
"#;
    assert_ne!(
        verdict(&solve(smt)),
        Some("sat"),
        "read-over-write must not be flattened away"
    );
}

/// A symbolic index breaks the side condition: abstain, never guess. Asserting
/// two reads at symbolic indices differ is satisfiable, so the wrong answer to
/// guard against here is `unsat`.
#[test]
fn symbolic_index_abstains_rather_than_aliasing_cells() {
    let smt = r#"
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun i () (_ BitVec 32))
(assert (not (= (select a i) (select a (_ bv0 32)))))
(check-sat)
"#;
    assert_ne!(
        verdict(&solve(smt)),
        Some("unsat"),
        "a symbolic index must not be collapsed onto a literal one"
    );
}

/// An extensional array comparison can observe cells the formula never reads,
/// so the pass must abstain. `(distinct a b)` with both arrays otherwise
/// unconstrained is satisfiable; the wrong answer to guard against is `unsat`.
#[test]
fn array_disequality_abstains() {
    let smt = r#"
(set-logic QF_ABVFP)
(declare-fun a () (Array (_ BitVec 32) (_ BitVec 8)))
(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))
(assert (not (= a b)))
(assert (= (select a (_ bv0 32)) (select b (_ bv0 32))))
(check-sat)
"#;
    assert_ne!(
        verdict(&solve(smt)),
        Some("unsat"),
        "arrays agreeing at one index may still differ elsewhere"
    );
}

// ---------------------------------------------------------------------------
// 3. The independent gate now reads FP model values
// ---------------------------------------------------------------------------

/// Every ground FP `sat` AY ever emitted reported
/// `cannot-confirm / model does not pin this leaf`: the theory's `FpModel` held
/// the concrete value and the gate never read it. With
/// `ModelValue::FloatingPoint` wired in, a bit-exact FP predicate is now
/// independently CONFIRMED.
#[test]
fn ground_fp_sat_is_independently_confirmed() {
    let smt = r#"
(set-logic QF_FP)
(declare-fun y () (_ FloatingPoint 11 53))
(assert (fp.isNormal y))
(check-sat)
"#;
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    let out = outputs.join("\n");
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(
        exec.statistics().get_string("model_check_gate.result"),
        Some("confirmed-sat"),
        "the gate must now confirm a bit-exact FP witness, not decline it"
    );
}

/// Current AY has an independent exact-rational IEEE-754 evaluator: it computes
/// the unrounded result and applies the selected rounding mode once. Keep this
/// port aligned with that stronger gate rather than ratcheting the retired
/// `cannot-confirm` behavior from the salvage branch.
#[test]
fn rounded_fp_arithmetic_is_independently_confirmed() {
    let smt = r#"
(set-logic QF_FP)
(declare-fun x () (_ FloatingPoint 11 53))
(declare-fun y () (_ FloatingPoint 11 53))
(assert (fp.isNormal (fp.add RNE x y)))
(check-sat)
"#;
    let commands = parse(smt).expect("parse failed");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute_all failed");
    let out = outputs.join("\n");
    assert_eq!(verdict(&out), Some("sat"), "{out}");
    assert_eq!(
        exec.statistics().get_string("model_check_gate.result"),
        Some("confirmed-sat"),
        "the independent exact-rational FP evaluator must confirm rounded arithmetic"
    );
}
