// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::{Proof, ProofStep, Sort, TermStore};

use super::*;

enum Context {
    Untyped,
    Typed,
}

fn fixture() -> (TermStore, Proof, [TermId; 2]) {
    let mut terms = TermStore::new();
    let positive = terms.mk_var("terminal_progress", Sort::Bool);
    let negative = terms.mk_not_raw(positive);
    let mut proof = Proof::new();
    let left = proof.add_assume(positive, None);
    let right = proof.add_assume(negative, None);
    proof.add_resolution(vec![], positive, left, right);
    for _ in 0..2 {
        proof.steps.push(ProofStep::Anchor {
            end_step: ProofId(2),
            variables: vec![],
        });
    }
    (terms, proof, [positive, negative])
}

fn strict(
    context: &Context,
    proof: &Proof,
    terms: &TermStore,
    assertions: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<crate::ProofQuality, ProofCheckError> {
    match context {
        Context::Untyped => crate::quality::check_proof_strict_with_context_and_progress(
            proof,
            terms,
            None,
            None,
            Some(assertions),
            progress,
        ),
        Context::Typed => crate::quality::check_proof_strict_with_typed_context_and_progress(
            proof,
            terms,
            None,
            None,
            &[],
            Some(assertions),
            progress,
        ),
    }
}

/// #completed-check-accepted. The fixture ends in two `anchor` steps, whose
/// validation makes no callback, so each contributes exactly its admission
/// charge `(1, 0)`. Nothing may follow them: the walk used to end with a
/// post-step poll, a whole-proof Skolem pass and a metered terminal scan, and
/// each of those turned a proof validated through its last step into
/// `ResourceLimit` when the caller's stop arrived late.
#[test]
fn both_strict_entrypoints_make_no_callback_after_the_final_step() {
    let (terms, proof, assertions) = fixture();
    for context in [Context::Untyped, Context::Typed] {
        let mut trace = Vec::new();
        strict(&context, &proof, &terms, &assertions, &mut |work, bytes| {
            trace.push((work, bytes));
            true
        })
        .expect("valid strict refutation with trailing anchors");
        assert!(
            trace.ends_with(&[(1, 0), (1, 0)]),
            "the last callbacks are the two trailing anchors' admissions: {:?}",
            &trace[trace.len().saturating_sub(8)..]
        );
        let total = trace.len();
        // A stop raised once the final step has been admitted (and, having no
        // callback of its own, validated) is never observed: accepted.
        let mut calls = 0;
        let accepted = strict(&context, &proof, &terms, &assertions, &mut |_, _| {
            calls += 1;
            calls <= total
        });
        assert!(accepted.is_ok(), "{accepted:?}");
        assert_eq!(calls, total);
        // Negative controls: refusing the final step's own admission, or any
        // earlier callback, still cancels the walk.
        for stop in [total, total - 1, 1] {
            let mut calls = 0;
            assert_eq!(
                strict(&context, &proof, &terms, &assertions, &mut |_, _| {
                    calls += 1;
                    calls < stop
                }),
                Err(ProofCheckError::ResourceLimit),
                "refused at callback {stop} of {total}"
            );
            assert_eq!(calls, stop);
        }
    }
}

/// The diagnostic walk validates this fixture's steps unmetered
/// (`ProofStep::Resolution`, `assume`, `anchor`) and its terminal scan is
/// bookkeeping, so it makes no callback at all and cannot be cancelled after
/// the fact: a caller that refuses everything still receives the verdict the
/// walk reached.
#[test]
fn partial_quality_entrypoint_makes_no_callback_after_the_final_step() {
    let (terms, proof, _) = fixture();
    let mut calls = 0;
    let (summary, quality, error) = crate::quality::check_proof_partial_with_quality_and_progress(
        &proof,
        &terms,
        &mut |_, _| {
            calls += 1;
            false
        },
    );
    assert_eq!(calls, 0);
    assert_eq!(error, None);
    assert!(quality.is_some());
    assert_eq!(summary.checked_steps, 5);
}
