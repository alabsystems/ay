// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Five bit-blasted obligations under ONE retained request ledger.
//!
//! Each obligation's live proof checks charge about 2 GB of logical bytes
//! (the bit-blast envelopes) against a live byte ceiling sized for one proof:
//! without settlement on drop the fourth obligation is refused.

use crate::smt::executor_adapter::{ReplayLimit, RetainedReplayProgress};
use crate::{
    ChcExpr, ChcOp, ChcParser, ChcPdrProofRun, ChcProblem, InvariantModel, PredicateInterpretation,
    VerifiedChcResult, VerifiedInvariant,
};
use ay_core::time::Instant;
use ay_dpll::api::{
    MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA, MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF,
};
use std::sync::Arc;
use std::time::Duration;

const RELATIONS: usize = 5;
const ARGS: &str = "((start (_ BitVec 64)) (end (_ BitVec 64)) (off (_ BitVec 64)))";
const FACTS: &str = "(and (bvule start end) (bvule end (_ bv5 64)) \
                     (bvule off (_ bv4 64)) (bvule (bvadd start off) (_ bv4 64)))";

fn chain() -> ChcProblem {
    let mut input = String::from("(set-logic HORN)\n");
    for index in 0..RELATIONS {
        input.push_str(&format!(
            "(declare-rel P{index} ((_ BitVec 64) (_ BitVec 64) (_ BitVec 64)))\n"
        ));
    }
    input.push_str(
        "(declare-rel error ())\n(declare-var start (_ BitVec 64))\n\
         (declare-var end (_ BitVec 64))\n(declare-var off (_ BitVec 64))\n",
    );
    input.push_str(&format!("(rule (=> {FACTS} (P0 start end off)))\n"));
    for index in 1..RELATIONS {
        input.push_str(&format!(
            "(rule (=> (P{} start end off) (P{index} start end off)))\n",
            index - 1
        ));
    }
    input.push_str(&format!(
        "(rule (=> (and (P{} start end off) (bvult (bvadd start off) start)) error))\n\
         (query error)\n",
        RELATIONS - 1
    ));
    ChcParser::parse(&input).expect("BV64 chain must parse")
}

/// Valid interpretations padded with `index` raw neutral conjuncts, so no
/// consecution is `p /\ not p`: each needs a bit-level proof.
fn padded_model(problem: &ChcProblem) -> InvariantModel {
    let mut text = String::from("(define-fun error () Bool false)\n");
    for index in 0..RELATIONS {
        text.push_str(&format!("(define-fun P{index} {ARGS} Bool {FACTS})\n"));
    }
    let parsed = InvariantModel::parse_smtlib(&text, problem).expect("model must parse");
    let mut model = InvariantModel::new();
    for predicate in problem.predicates() {
        let interpretation = parsed.get(&predicate.id).expect("every relation");
        let Some(index) = predicate.name.strip_prefix('P') else {
            model.set(predicate.id, interpretation.clone());
            continue;
        };
        let index: usize = index.parse().expect("P<index>");
        let ChcExpr::Op(ChcOp::And, facts) = &interpretation.formula else {
            panic!("the facts parse as one conjunction");
        };
        #[expect(
            clippy::rc_clone_in_vec_init,
            reason = "the retained-model fixture intentionally shares one immutable padding node across the prefix"
        )]
        let mut padded = vec![Arc::new(ChcExpr::Bool(true)); index];
        padded.extend(facts.iter().cloned());
        let formula = ChcExpr::Op(ChcOp::And, padded);
        model.set(
            predicate.id,
            PredicateInterpretation::new(interpretation.vars.clone(), formula),
        );
    }
    model
}

fn ceilings(rows: usize) -> (usize, usize) {
    let mut callback = || true;
    let owner = RetainedReplayProgress::new_for_retained_rows(
        ReplayLimit::Until(Instant::now() + Duration::from_secs(60)),
        &mut callback,
        rows,
    )
    .expect("request owner");
    let (_, _, max_work, max_bytes) = owner.ledger();
    (max_work, max_bytes)
}

/// The checked replay builds its request owner with this constructor and
/// this row count. Its ceilings must not scale with the rows, and its byte
/// ceiling must stay ONE proof's: a larger byte ceiling would admit all five
/// obligations cumulatively and this test would stop pinning settlement.
fn assert_unscaled_ceilings(rows: usize) {
    let (max_work, max_bytes) = ceilings(rows);
    assert_eq!((max_work, max_bytes), ceilings(1));
    assert!(
        max_bytes
            <= MAX_PROOF_PRODUCING_BV_LEMMAS_PER_PROOF * MAX_PROOF_PRODUCING_BV_BYTES_PER_LEMMA
    );
}

#[test]
fn five_bit_blasted_obligations_replay_and_recheck_under_one_request_ledger() {
    let problem = chain();
    assert_unscaled_ceilings(problem.clauses().len());
    // Each P_i is the same facts conjunction plus neutral `true`s, so the
    // model is valid. from_validated skips the ordinary model validator on
    // purpose: the strict checked replay below proves every original clause
    // and is this model's validation here.
    let run = ChcPdrProofRun::new(
        problem.clone(),
        VerifiedChcResult::Safe(VerifiedInvariant::from_validated(padded_model(&problem))),
        "retained-settlement",
    );
    let checked = run
        .run_checked_replay(Duration::from_secs(60))
        .expect("every obligation's settled proof bytes fit one live ceiling");
    let rows = &checked.summary().obligations;
    assert_eq!(rows.len(), problem.clauses().len());
    assert!(rows.iter().all(|row| row.strict_cert.is_some()));
    checked
        .recheck_with_fresh_ay(Duration::from_secs(60))
        .expect("the fresh recheck settles each obligation too");
}
