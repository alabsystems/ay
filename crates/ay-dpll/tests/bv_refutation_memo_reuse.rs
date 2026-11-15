// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One bit-blast refutation per CNF, across a whole publication.
//!
//! `checked_bv_bitblast_lowering_supported` answers a SUPPORT question by
//! building the answer and discarding it, `proof_has_known_wire_gap` asks it
//! once per `TheoryLemma`, and one publication asks THAT about the same
//! unchanged document several times before the exporter re-derives the very
//! same documents to keep their text. This pins the collapse of all of it:
//! after a QF_BV publication, the export must be served a refutation the
//! support question derived.
//!
//! It is a pin on the DUPLICATION, not on a count. The repeated support
//! questions used to be most of the hits; they no longer reach the
//! refutation memo at all, because a lemma the printer has already spelled
//! is answered from `alethe_printer/bv_support_memo.rs` without a render.
//! What is left to share is the support question's refutation with the
//! export's render of the same lemma (measured 2026-10-01: 1 hit for 2
//! misses, where the support question's repeats had made it strictly more
//! hits than misses).

use ay_dpll::Executor;
use ay_frontend::parse;
use ay_proof::resolution_dag_memo::{reset_resolution_dag_memo, resolution_dag_memo_counters};
use ntest::timeout;

/// UNSAT only by real bit-blasting: `x + 1 <u x` holds exactly at the all-ones
/// word, which the second assertion excludes. No named identity lane in the
/// printer's dispatch recognizes it, so it reaches the arbitrary-QF_BV
/// full-blast-plus-SAT-refutation fallback.
const WRAPAROUND: &str = r#"
    (set-option :produce-proofs true)
    (set-option :check-proofs-strict true)
    (set-logic QF_BV)
    (declare-const x (_ BitVec 8))
    (assert (bvult (bvadd x (_ bv1 8)) x))
    (assert (not (= x (_ bv255 8))))
    (check-sat)
    (get-proof)
"#;

#[test]
#[timeout(600_000)]
fn a_publication_refutes_each_distinct_bit_blast_once() {
    reset_resolution_dag_memo();

    let commands = parse(WRAPAROUND).expect("parse SMT-LIB script");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute SMT-LIB script");
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "expected UNSAT, got {outputs:?}"
    );

    let (hits, misses) = resolution_dag_memo_counters();
    eprintln!("MEASURED refutation memo: {hits} hits / {misses} misses");
    assert!(
        misses > 0,
        "the fixture must actually reach a bit-blast refutation; got {hits} hits / {misses} misses"
    );
    assert!(
        hits > 0,
        "the export re-renders what the support question refuted: \
         it must be served that refutation from the memo, \
         got {hits} hits / {misses} misses"
    );
}
