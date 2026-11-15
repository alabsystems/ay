// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Pure bit-vector UNSATs under `(set-option :check-proofs-strict true)`.
//!
//! The native refutation of these problems ends in one multi-literal
//! `BvBitBlast` conflict clause. It renders with no unproved step, but the
//! known-wire-gap screen reports every multi-literal bit-blast lemma as a gap
//! on purpose (`ay_proof::alethe_printer::complete_blast::clause`), and under
//! the in-script option the library strict gate
//! (`decline_trust_bearing_unsat_under_strict_proofs`) withholds any screened
//! gap. The guarded joint collapse repairs that: `and_neg` over the authored
//! roots plus ONE single-literal `BvBitBlast` lemma, which the screen admits.
//!
//! MEASURED on a branch that judged "nothing left to repair" by the render
//! alone (fix/2026-09-23/ay-selfcheck-abv before this test): the incumbent was
//! kept, and both problems below, like nine of the `benchmarks/smt/QF_BV`
//! puzzles, answered `unknown (incomplete proof-trusted)` where main answered
//! `unsat`.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const STRICT: &str = "(set-option :produce-proofs true)\n(set-option :check-proofs-strict true)\n";

/// Two strict orders that contradict each other.
const TWO_STRICT_ORDERS: &str = "\
(set-logic QF_BV)
(declare-const x (_ BitVec 8))
(declare-const y (_ BitVec 8))
(assert (bvult x y))
(assert (bvult y x))
(check-sat)
(get-proof)
";

/// `benchmarks/smt/QF_BV/puzzle_01.smt2`.
const PUZZLE_01: &str = "\
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 8))
(declare-fun v1 () (_ BitVec 8))
(assert (= (bvadd v1 v0) #x6c))
(assert (= (bvxor v1 v0) #xca))
(assert (= (bvor v1 v0) #x47))
(assert (= (bvxor v0 v1) #xcc))
(assert (= (bvand v1 v0) #xfc))
(check-sat)
(get-proof)
";

fn assert_strict_unsat(label: &str, script: &str) {
    let commands = parse(&format!("{STRICT}{script}")).expect("fixture script must parse");
    let mut executor = Executor::new();
    let outputs = executor
        .execute_all(&commands)
        .expect("fixture script must run");
    let [verdict, proof] = outputs.as_slice() else {
        panic!("{label}: expected a verdict and a proof, got {outputs:?}");
    };
    assert_eq!(
        verdict,
        "unsat",
        "{label}: `:check-proofs-strict` withheld the UNSAT ({:?})",
        executor.unknown_reason()
    );
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
}

#[test]
#[timeout(120_000)]
fn two_contradicting_strict_orders_publish_unsat_under_in_script_strict_proofs() {
    assert_strict_unsat("bvult x y, bvult y x", TWO_STRICT_ORDERS);
}

#[test]
#[timeout(120_000)]
fn qf_bv_puzzle_publishes_unsat_under_in_script_strict_proofs() {
    assert_strict_unsat("puzzle_01", PUZZLE_01);
}
