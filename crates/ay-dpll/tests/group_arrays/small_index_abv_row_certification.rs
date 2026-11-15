// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small-index QF_ABV read-over-write must publish a proof AY's own strict
//! checker accepts.
//!
//! MEASURED on ay 3211f7fc7 (the Trust 450403669e bundle) with
//! `ay -smt2 q.smt2 --strict-proofs --proof q.alethe --proof-format alethe`:
//!
//! ```text
//! (assert (not (= v (select (store ((as const (Array (_ BitVec 8) (_ BitVec 8)))
//!                                   (_ bv0 8)) off v) off))))
//! computed UNSAT rejected by mandatory strict certification:
//! strict UNSAT proof validation failed: step t0 uses unsupported hole rule
//! unknown
//! (:reason-unknown (incomplete self-check-rejected))
//! ```
//!
//! at every index/element width pair in [`ROW1_WIDTHS`] (a declared base array
//! instead answered `the provisional UNSAT verdict has no proof`), while
//! idx4/elem8, idx7/elem8 and every index of 9 bits or more answered a
//! trust-free `unsat`. external-codegen's 8-bit FrameLayout obligations
//! ([`FRAME_LAYOUT_8BIT`]) failed the same way (`step t0/t1 uses unsupported
//! hole rule`, `step t3 uses unverified trust rule`); their 64-bit twins
//! passed. These tests ask through the in-script spelling,
//! `(set-option :check-proofs-strict true)`, under which 75e539df0 answered
//! `unknown` with `SelfCheckRejected` at the same widths.
//!
//! The certification lane for these roots is the checker's own bit-blast of
//! the authored assertion (`BvBitBlast`), and for an index sort of at most
//! eight bits it scalarized the array over its whole domain. That overran the
//! proof-producing envelope, the lemma was refused, and nothing else could
//! certify the refutation. The checker now retries such a read through its
//! store chain; see `ay_proof::checker::bv_bitblast::proof_producing_control`.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// `(index width, element width)` pairs measured `self-check-rejected`.
const ROW1_WIDTHS: [(u32, u32); 9] = [
    (8, 1),
    (8, 4),
    (8, 8),
    (8, 16),
    (8, 32),
    (8, 64),
    (7, 32),
    (7, 64),
    (6, 64),
];

/// The four external-codegen FrameLayout (8-bit) obligations, as external-codegen's
/// `generate_smt2_query` writes them (its `:timeout`/`:produce-models`
/// options dropped).
const FRAME_LAYOUT_8BIT: [(&str, &str); 4] = [
    (
        "callee-save pair slots don't overlap (8-bit)",
        "(declare-const val_a (_ BitVec 8))
         (declare-const val_b (_ BitVec 8))
         (declare-const offset_a (_ BitVec 8))
         (declare-const offset_b (_ BitVec 8))
         (assert (and (not (= offset_a offset_b)) (not (= val_a (select (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) (_ bv0 8)) offset_a val_a) offset_b val_b) offset_a)))))",
    ),
    (
        "distinct slots have non-overlapping memory (8-bit)",
        "(declare-const val_a (_ BitVec 8))
         (declare-const val_b (_ BitVec 8))
         (declare-const slot_a (_ BitVec 8))
         (declare-const slot_b (_ BitVec 8))
         (assert (and (not (= slot_a slot_b)) (not (= val_a (select (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) (_ bv0 8)) slot_a val_a) slot_b val_b) slot_a)))))",
    ),
    (
        "callee-save restore is identity (8-bit)",
        "(declare-const reg_val (_ BitVec 8))
         (declare-const offset (_ BitVec 8))
         (assert (not (= reg_val (select (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) (_ bv0 8)) offset reg_val) offset))))",
    ),
    (
        "triple callee-save slots preserve first value (8-bit)",
        "(declare-const val_a (_ BitVec 8))
         (declare-const val_b (_ BitVec 8))
         (declare-const val_c (_ BitVec 8))
         (declare-const off_a (_ BitVec 8))
         (declare-const off_b (_ BitVec 8))
         (declare-const off_c (_ BitVec 8))
         (assert (and (not (= off_a off_c)) (and (not (= off_a off_b)) (not (= val_a (select (store (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) (_ bv0 8)) off_a val_a) off_b val_b) off_c val_c) off_a))))))",
    ),
];

/// Solve `body` under strict proof checking and return the published proof.
/// Panics with the executor's own reason when the UNSAT is not published.
fn strict_proof(label: &str, body: &str) -> String {
    let script = format!(
        "(set-option :produce-proofs true)\n\
         (set-option :check-proofs-strict true)\n\
         (set-logic QF_ABV)\n{body}\n(check-sat)\n"
    );
    let commands = parse(&script).expect("fixture script must parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("fixture script must run");
    assert_eq!(
        outputs.last().map(String::as_str),
        Some("unsat"),
        "{label}: the strictly checked UNSAT must be published; got {outputs:?}, \
         reason {:?}",
        exec.unknown_reason()
    );
    let get_proof = parse("(get-proof)").expect("(get-proof) must parse");
    let proof = exec
        .execute_all(&get_proof)
        .expect("(get-proof) must run")
        .pop()
        .expect("(get-proof) must print the proof");
    assert!(
        proof.contains("(assume ") && proof.contains("(cl)"),
        "{label}: expected an Alethe refutation, got:\n{proof}"
    );
    for gap in [":rule hole", ":rule trust"] {
        assert!(
            !proof.contains(gap),
            "{label}: the published proof must not rest on `{gap}`:\n{proof}"
        );
    }
    proof
}

#[test]
#[timeout(600_000)]
fn small_index_read_over_write_publishes_a_strict_proof_at_every_refused_width() {
    for (index, element) in ROW1_WIDTHS {
        let body = format!(
            "(declare-const off (_ BitVec {index}))\n\
             (declare-const v (_ BitVec {element}))\n\
             (assert (not (= v (select (store ((as const (Array (_ BitVec {index}) (_ BitVec {element}))) (_ bv0 {element})) off v) off))))"
        );
        strict_proof(&format!("idx{index}/elem{element}"), &body);
    }
}

/// The same read through a declared (non-constant) array. Measured on
/// 3211f7fc7 at the same widths: `computed UNSAT rejected by mandatory strict
/// certification: the provisional UNSAT verdict has no proof`.
#[test]
#[timeout(600_000)]
fn small_index_read_over_write_of_a_declared_array_publishes_a_strict_proof() {
    for (index, element) in ROW1_WIDTHS {
        let body = format!(
            "(declare-const a (Array (_ BitVec {index}) (_ BitVec {element})))\n\
             (declare-const off (_ BitVec {index}))\n\
             (declare-const v (_ BitVec {element}))\n\
             (assert (not (= v (select (store a off v) off))))"
        );
        strict_proof(&format!("declared idx{index}/elem{element}"), &body);
    }
}

#[test]
#[timeout(600_000)]
fn external_codegen_eight_bit_frame_layout_obligations_publish_strict_proofs() {
    for (label, body) in FRAME_LAYOUT_8BIT {
        strict_proof(label, body);
    }
}

#[test]
#[timeout(600_000)]
fn an_eight_bit_read_over_write_that_can_differ_stays_satisfiable() {
    // The lane that now certifies the reads above must not certify a read the
    // later write may have overwritten: without `(not (= a b))` this is SAT.
    let script = "(set-option :produce-proofs true)\n\
         (set-option :check-proofs-strict true)\n\
         (set-logic QF_ABV)\n\
         (declare-const a (_ BitVec 8))\n\
         (declare-const b (_ BitVec 8))\n\
         (declare-const va (_ BitVec 8))\n\
         (declare-const vb (_ BitVec 8))\n\
         (assert (not (= va (select (store (store ((as const (Array (_ BitVec 8) (_ BitVec 8))) (_ bv0 8)) a va) b vb) a))))\n\
         (check-sat)\n";
    let commands = parse(script).expect("fixture script must parse");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("fixture script must run");
    assert_eq!(outputs.last().map(String::as_str), Some("sat"));
}
