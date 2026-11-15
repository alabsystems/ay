// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::*;

fn shared_chain(terms: &mut TermStore) -> (TermId, TermId) {
    let variable = terms.mk_var("shared", Sort::bitvec(1));
    let mut term = variable;
    // Four raw shared layers unfold to only 31 nodes per occurrence. The
    // equality must visit both occurrences; neither builder folding nor a
    // solver/memo shortcut is involved.
    for _ in 0..4 {
        term = app(terms, "bvadd", &[term, term], Sort::bitvec(1));
    }
    (variable, app(terms, "=", &[term, term], Sort::Bool))
}

#[test]
fn every_assignment_walk_poll_refuses_terminally_and_a_fresh_retry_is_clean() {
    let mut terms = TermStore::new();
    let (_, identity) = shared_chain(&mut terms);
    let snapshot = terms.entries_snapshot();
    let mut calls = 0usize;
    assert_eq!(
        validate(&terms, ProofId(17), &[identity], &mut || {
            calls += 1;
            Ok(())
        }),
        Ok(())
    );
    assert!(
        calls > 100 && calls < 2_000,
        "bounded fixture polls: {calls}"
    );
    for refused in 1..=calls {
        let mut ordinal = 0;
        let result = validate(&terms, ProofId(17), &[identity], &mut || {
            ordinal += 1;
            if ordinal == refused {
                Err(ProofCheckError::ResourceLimit)
            } else {
                Ok(())
            }
        });
        assert_eq!(
            result,
            Err(ProofCheckError::ResourceLimit),
            "poll {refused}/{calls}"
        );
        assert_eq!(ordinal, refused, "no callback after refusal");
    }
    assert_eq!(terms.entries_snapshot(), snapshot);
    assert_eq!(compare_clause(&terms, &[identity]), Ok(()));
}

fn every_evaluation_poll(terms: &TermStore, term: TermId, env: &[(TermId, EvalValue)]) {
    let mut calls = 0;
    let expected = evaluate(terms, term, env, &mut || {
        calls += 1;
        Ok::<(), ProofCheckError>(())
    });
    assert!(calls > 1 && calls < 1_000);
    for refused in 1..=calls {
        let mut ordinal = 0;
        let actual = evaluate(terms, term, env, &mut || {
            ordinal += 1;
            if ordinal == refused {
                Err(ProofCheckError::ResourceLimit)
            } else {
                Ok(())
            }
        });
        assert_eq!(
            actual,
            Err(EvalError::Interrupted(ProofCheckError::ResourceLimit))
        );
        assert_eq!(ordinal, refused);
    }
    assert_eq!(evaluate(terms, term, env, &mut || Ok(())), expected);
    let _ = compare(terms, term, env);
}

#[test]
fn every_expression_environment_repeat_and_final_poll_preserves_typed_interruption() {
    let mut terms = TermStore::new();
    let (variable, identity) = shared_chain(&mut terms);
    let unrelated = terms.mk_var("unrelated", Sort::Bool);
    let env = [
        (unrelated, EvalValue::Bool(false)),
        (unrelated, EvalValue::Bool(true)),
        (variable, EvalValue::BitVec { value: 1, width: 1 }),
    ];
    every_evaluation_poll(&terms, identity, &env);
    let one = bv(&mut terms, 1, 1);
    let repeated = indexed(&mut terms, "repeat", &[64], one, 64);
    every_evaluation_poll(&terms, repeated, &[]);
    let unknown = app(&mut terms, "unknown", &[], Sort::Bool);
    every_evaluation_poll(&terms, unknown, &[]);
    let truth = terms.true_term();
    every_evaluation_poll(&terms, truth, &[]);
    let falsity = terms.false_term();
    for (name, value) in [("or", truth), ("and", falsity)] {
        let wide = app(&mut terms, name, &[value; 16], Sort::Bool);
        every_evaluation_poll(&terms, wide, &[]);
    }
}

#[test]
fn cancellation_is_not_unsupported_and_precancel_wins_over_a_false_or_malformed_clause() {
    let mut terms = TermStore::new();
    let falsity = terms.false_term();
    let unknown = app(&mut terms, "unknown", &[], Sort::Bool);
    for clause in [vec![], vec![falsity], vec![unknown]] {
        let mut calls = 0;
        assert_eq!(
            validate(&terms, ProofId(17), &clause, &mut || {
                calls += 1;
                Err(ProofCheckError::ResourceLimit)
            }),
            Err(ProofCheckError::ResourceLimit)
        );
        assert_eq!(calls, 1);
        assert!(compare_clause(&terms, &clause).is_err());
    }
    // The internal evaluator must preserve the actual typed refusal payload,
    // even if it is not the ResourceLimit used by the public sticky carrier.
    assert_eq!(
        evaluate(&terms, unknown, &[], &mut || Err(37u8)),
        Err(EvalError::Interrupted(37))
    );
}
