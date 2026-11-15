// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #literal-decode-payload, end to end through the metered strict walk.
//!
//! The resolution family's strict validators decode a literal's leading-`not`
//! chain and then treat the atom as an opaque `TermId`; their payload is
//! therefore that decode count, not a walk of the DAG below the atom. These
//! tests pin the count, show a refutation the reachable-DAG walk would have
//! priced past a tight envelope now checks inside it, and — the part that
//! matters — show that the SAME envelope still refuses the forged twins with
//! the validator's typed error, so the meter did not decide the verdict.

use super::*;
use ay_core::{ArraySort, Sort, Symbol};

/// Whole-walk envelope the fixtures are measured against. Far below the
/// production constant so a fixture that still fits is a fixture whose
/// charges are small in absolute terms, not merely smaller than before.
const ENVELOPE: usize = 100_000;

/// `(= (select CHAIN i) v)` over a `levels`-deep swap chain that cites the
/// previous array twice per level: the DAG grows by three nodes per level
/// while the TREE unfolds about `2^levels`-fold — the literal shape of every
/// `QF_AX/swap` resolution step.
fn shared_chain_atom(terms: &mut TermStore, levels: usize) -> TermId {
    let array_sort = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let mut chain = terms.mk_var("a", array_sort.clone());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    for _ in 0..levels {
        let read = terms.mk_app(Symbol::named("select"), vec![chain, j], Sort::Int);
        chain = terms.mk_app(
            Symbol::named("store"),
            vec![chain, i, read],
            array_sort.clone(),
        );
    }
    let v = terms.mk_var("v", Sort::Int);
    let read_back = terms.mk_app(Symbol::named("select"), vec![chain, i], Sort::Int);
    terms.mk_app(Symbol::named("="), vec![read_back, v], Sort::Bool)
}

fn run_under(
    proof: &Proof,
    terms: &TermStore,
    budget: usize,
) -> (Result<(), ProofCheckError>, usize) {
    let mut spent = 0usize;
    let outcome = check_proof_strict_with_context_and_progress(
        proof,
        terms,
        None,
        None,
        None,
        &mut |work, _bytes| {
            spent += work;
            spent <= budget
        },
    );
    (outcome.map(|_| ()), spent)
}

/// `assume (not (not A))`, `assume (not A)`, then the closing step given by
/// `close`, over a deep shared-chain atom `A`. Also returns the derived-clause
/// table the closing step sees, for calling the payload meters directly.
fn refutation(
    terms: &mut TermStore,
    close: impl FnOnce(TermId, TermId) -> ProofStep,
) -> (Proof, TermId, Vec<Option<Vec<TermId>>>) {
    let atom = shared_chain_atom(terms, 16);
    let not_atom = terms.mk_not_raw(atom);
    let not_not_atom = terms.mk_not_raw(not_atom);
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::Assume(not_not_atom));
    proof.steps.push(ProofStep::Assume(not_atom));
    proof.steps.push(close(atom, not_atom));
    let derived = vec![Some(vec![not_not_atom]), Some(vec![not_atom])];
    (proof, atom, derived)
}

/// The pivot-annotated binary form (`ProofStep::Resolution`).
#[test]
fn pivot_resolution_payload_is_the_exact_decode_and_forgeries_are_refused() {
    let mut terms = TermStore::new();
    let (valid, _atom, derived) = refutation(&mut terms, |atom, _| ProofStep::Resolution {
        clause: Vec::new(),
        pivot: atom,
        clause1: ProofId(0),
        clause2: ProofId(1),
    });

    // The payload is exactly what the validator decodes: the empty clause (0),
    // the pivot (1), `(not (not A))` (1 + 2) and `(not A)` (1 + 1) — six
    // decode units over three literal slots.
    let payload = literal_decode_payload(&valid.steps[2], &terms, &derived, &mut |_, _| true)
        .expect("decode payload fits usize");
    assert_eq!(payload.work, 6);
    assert_eq!(payload.unfolded_work, 6);
    assert_eq!(payload.bytes, 3 * size_of::<TermId>());

    // The reachable-DAG walk this replaces, on the same step, priced the
    // resolution past the envelope by itself (the tree-unfolded figure times
    // the four decode passes `binary_resolution_charge` bills).
    let walked = meter_step_term_payload(
        &valid.steps[2],
        &terms,
        &derived,
        &mut TermCostMemo::default(),
        &mut |_, _| true,
    )
    .expect("payload walk fits usize");
    assert!(walked.unfolded_work > 65_536, "{walked:?}");
    let (old_charge, _) = binary_resolution_charge(1, 1, 0, walked.unfolded_work, false)
        .expect("old charge fits usize");
    assert!(
        old_charge > ENVELOPE,
        "the fixture must be one the old model refused: {old_charge}"
    );

    let (outcome, spent) = run_under(&valid, &terms, usize::MAX);
    assert!(outcome.is_ok(), "the refutation must check: {outcome:?}");
    assert!(
        spent < ENVELOPE,
        "whole walk must fit the envelope: {spent}"
    );
    assert!(run_under(&valid, &terms, ENVELOPE).0.is_ok());

    // Mutation 1: the conclusion keeps the pivot.
    let (forged, _, _) = refutation(&mut terms, |atom, _| ProofStep::Resolution {
        clause: vec![atom],
        pivot: atom,
        clause1: ProofId(0),
        clause2: ProofId(1),
    });
    assert!(
        matches!(
            run_under(&forged, &terms, ENVELOPE).0,
            Err(ProofCheckError::InvalidResolution { .. })
        ),
        "a resolvent that keeps the pivot must be refused by the validator, not the meter"
    );
    // Mutation 2: a pivot that occurs in neither premise.
    let stranger = terms.mk_var("q", Sort::Bool);
    let (forged, _, _) = refutation(&mut terms, |_, _| ProofStep::Resolution {
        clause: Vec::new(),
        pivot: stranger,
        clause1: ProofId(0),
        clause2: ProofId(1),
    });
    assert!(
        matches!(
            run_under(&forged, &terms, ENVELOPE).0,
            Err(ProofCheckError::InvalidResolution { .. })
        ),
        "a pivot absent from both premises must be refused by the validator, not the meter"
    );
}

/// The Alethe `resolution` step in both its argument-free and its
/// pivot-directed forms, and `th_resolution`. The directed form is
/// occurrence-exact in its negation depth, so over the premises
/// `(not (not A))` / `(not A)` its annotation is `:args ((not A) false)`:
/// polarity `false` puts `(not (not A))` in the accumulator and `(not A)` in
/// the next premise.
#[test]
fn alethe_resolution_steps_take_the_decode_payload_and_forgeries_are_refused() {
    for (rule, directed) in [
        (AletheRule::Resolution, false),
        (AletheRule::Resolution, true),
        (AletheRule::ThResolution, false),
        (AletheRule::ThResolution, true),
    ] {
        let mut terms = TermStore::new();
        let false_term = terms.false_term();
        let args_for = move |not_atom: TermId| {
            if directed {
                vec![not_atom, false_term]
            } else {
                Vec::new()
            }
        };
        let (valid, _atom, derived) = refutation(&mut terms, |_, not_atom| ProofStep::Step {
            rule: rule.clone(),
            clause: Vec::new(),
            premises: vec![ProofId(0), ProofId(1)],
            args: args_for(not_atom),
        });
        let payload = literal_decode_payload(&valid.steps[2], &terms, &derived, &mut |_, _| true)
            .expect("decode payload fits usize");
        // Clause (0), args (`(not A)` 2 + polarity 1 when directed), premises
        // (3 + 2).
        assert_eq!(
            payload.work,
            if directed { 8 } else { 5 },
            "{rule:?} directed={directed}"
        );

        let (outcome, spent) = run_under(&valid, &terms, usize::MAX);
        assert!(outcome.is_ok(), "{rule:?} directed={directed}: {outcome:?}");
        assert!(spent < ENVELOPE, "{rule:?} directed={directed}: {spent}");
        assert!(run_under(&valid, &terms, ENVELOPE).0.is_ok());

        let (forged, _, _) = refutation(&mut terms, |atom, not_atom| ProofStep::Step {
            rule: rule.clone(),
            clause: vec![atom],
            premises: vec![ProofId(0), ProofId(1)],
            args: args_for(not_atom),
        });
        assert!(
            matches!(
                run_under(&forged, &terms, ENVELOPE).0,
                Err(ProofCheckError::InvalidResolution { .. })
            ),
            "{rule:?} directed={directed}: a resolvent that keeps the pivot must be refused by the validator"
        );
    }
}
