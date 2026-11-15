// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One proof build sweeps each exact-division obligation once.
//!
//! The 44-bit `x / 1000003 < 17592134` (the quotient's range, tight: the
//! largest quotient is `(2^44 - 1) / 1000003 = 17592133`) is a divider
//! obligation no sweep closes in the strict producer's envelope. Its proof
//! build asks the strict checker about it in more than one spelling (the
//! residual-trust rescue, then the exact-authored lane), and each spelling's
//! exact-division attempt stops on a proof-size cap and would sweep the whole
//! 200,000-conflict envelope again (measured on fd4e00f75 with the memo
//! bypassed: two such sweeps, 66 s and 95 s). The build's memo
//! (`ay_proof::ExactDivisionSweepMemo`) keeps the first sweep whole and
//! withholds the rest.
//!
//! This pins the build's memo, not the query's sweep count. A spelling the
//! memo withholds is refused without a sweep, and that refusal is not the
//! envelope's verdict (`exact_division_sweeps::DECLINED`): it is decided
//! afresh outside the build. Here the unrewritten authored replay decides it,
//! in a probe executor with a memo of its own, and sweeps it again (96 s on
//! fd4e00f75), so the query makes two whole sweeps with the memo as without.
//!
//! The fixture was the remainder's range, the 40-bit `x % 1000003 < 1000003`
//! (model-checker-consumer's divider harness obligation, two sweeps on 85f8d30d3). Since
//! 7726721a1 the guarded collapse derives `d = 0 or x % d < d` for every
//! authored `bvurem` (`BvUremBound`), and that joint is now asked before any
//! spelling would pay for the exact divider
//! (`guarded/urem_bound/before_division.rs`), so that obligation costs no
//! sweep at all (pinned below; on 7f0f14325 its first spelling still swept
//! the whole envelope, 30 s of a 32 s release run). No such theorem covers a
//! quotient.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

const REMAINDER_IN_RANGE_40: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_BV)
    (declare-const x (_ BitVec 40))
    (assert (not (bvult (bvurem x #x00000f4243) #x00000f4243)))
    (check-sat)
"#;

const QUOTIENT_IN_RANGE_44: &str = r#"
    (set-option :produce-proofs true)
    (set-logic QF_BV)
    (declare-const x (_ BitVec 44))
    (assert (not (bvult (bvudiv x #x000000f4243) #x000010c6f46)))
    (check-sat)
"#;

#[test]
#[timeout(600_000)]
fn a_proof_build_sweeps_an_exact_division_obligation_once() {
    let commands = parse(QUOTIENT_IN_RANGE_44).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute");
    assert_ne!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "{outputs:?}"
    );
    let memo = exec.exact_division_sweep_memo();
    eprintln!("MEASURED exact-division sweep memo: {memo:?}");
    assert_eq!(
        memo.failed_signatures(),
        1,
        "the first sweep ran whole: {memo:?}"
    );
    assert!(
        memo.skipped_sweeps() >= 1,
        "a later spelling's sweep withheld: {memo:?}"
    );
}

#[test]
#[timeout(600_000)]
fn a_remainder_obligation_the_bound_theorem_closes_costs_no_sweep() {
    let commands = parse(REMAINDER_IN_RANGE_40).expect("parse");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute");
    assert_eq!(outputs, ["unsat"]);
    let proof = exec.last_proof().expect("a proof after unsat");
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ay_core::ProofStep::TheoryLemma {
                kind: ay_core::TheoryLemmaKind::BvUremBound,
                ..
            }
        )),
        "certified by the bound theorem: {proof:#?}"
    );
    assert!(ay_proof::terminal_trust_report(proof).is_trust_free());
    let memo = exec.exact_division_sweep_memo();
    eprintln!("MEASURED exact-division sweep memo: {memo:?}");
    assert_eq!(
        memo.failed_signatures(),
        0,
        "no sweep spent its envelope: {memo:?}"
    );
    assert_eq!(memo.skipped_sweeps(), 0, "none was withheld: {memo:?}");
}
