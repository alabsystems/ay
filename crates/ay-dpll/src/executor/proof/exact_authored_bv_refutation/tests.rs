// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Deny-only wire scheduling: every successful candidate still replays.

use super::*;
use std::cell::{Cell, RefCell};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::Arc;

use crate::api::proofs::EnvelopeStop;

const CONTRADICTION: &str = "(declare-const x (_ BitVec 4))
    (assert (= x #x0)) (assert (= x #x1))";
const AFFINE: &str = "(declare-const x (_ BitVec 16))
    (assert (not (= (bvadd x #x0000) x)))";

fn fixture(script: &str) -> Executor {
    fixture_with_retention(script, true)
}

fn fixture_with_retention(script: &str, retain: bool) -> Executor {
    let mut executor = Executor::new();
    executor.ctx.set_retain_parsed_assertions(retain);
    // Preserve exact authored syntax rather than letting assertion elaboration
    // turn a tautological equality's negation into a bare false constant.
    for command in ay_frontend::parse(script).expect("typed source") {
        if let ay_frontend::Command::Assert(surface) = command {
            let root = executor
                .raw_intern_ground_bv_surface(&surface)
                .expect("raw source");
            executor.ctx.add_assertion_with_parsed(root, surface);
        } else {
            executor.execute(&command).expect("declaration");
        }
    }
    executor
}

fn lemma(proof: &Proof) -> (TheoryLemmaKind, &[TermId]) {
    proof
        .steps
        .iter()
        .find_map(|step| match step {
            ProofStep::TheoryLemma { kind, clause, .. } => Some((kind.clone(), clause.as_slice())),
            _ => None,
        })
        .expect("one proposed lemma")
}

fn opposites(executor: &mut Executor) -> Vec<TermId> {
    executor
        .exact_concrete_authored_scope()
        .iter()
        .map(|&root| match executor.ctx.terms.get(root) {
            TermData::Not(inner) => *inner,
            _ => executor.ctx.terms.mk_not_raw(root),
        })
        .collect()
}

#[test]
fn presentation_denial_precedes_native_semantic_recognition() {
    let mut executor = fixture(CONTRADICTION);
    let clause = opposites(&mut executor);
    let offers = Cell::new(0);
    assert!(executor
        .exact_authored_bv_refutation(|executor, candidate| {
            offers.set(offers.get() + 1);
            assert_eq!(
                lemma(candidate),
                (TheoryLemmaKind::BvBitBlast, clause.as_slice())
            );
            assert!(!executor.ctx.terms.strict_bv_semantics_validated(&clause));
            false
        })
        .is_none());
    assert_eq!(offers.get(), 1);
    assert!(!executor.ctx.terms.strict_bv_semantics_validated(&clause));
    assert!(
        executor.recognize_bv_bitblast_until_stopped(&clause),
        "the denied candidate was genuinely valid, not a vacuous SAT refusal"
    );
}

#[test]
fn actual_wire_gap_keeps_incumbent_and_does_not_validate_the_candidate() {
    let mut executor = fixture(CONTRADICTION);
    // Without an observable document, the existing screen deliberately refuses
    // a multi-literal complete-blast question. Exercise that real callback.
    assert!(!executor.proof_document_observable());
    let clause = opposites(&mut executor);
    let mut incumbent = Proof::new();
    incumbent.add_rule_step(AletheRule::Trust, vec![], vec![], vec![]);
    let before = format!("{:?}", incumbent.steps);
    executor.repair_wire_gap_with_exact_authored_bv_refutation(&mut incumbent);
    assert_eq!(format!("{:?}", incumbent.steps), before);
    assert!(!executor.ctx.terms.strict_bv_semantics_validated(&clause));
    assert!(
        executor.certification_stop().is_none(),
        "semantic denial is not cancellation"
    );
}

#[test]
fn clean_wire_candidate_preserves_exact_assumptions_and_strict_export() {
    let mut executor = fixture(CONTRADICTION);
    executor.set_produce_proofs(true);
    let authored = executor.exact_concrete_authored_scope();
    let proof = executor
        .exact_authored_bv_refutation(|executor, candidate| {
            executor.wire_repair_candidate_prints_clean(candidate)
        })
        .expect("the existing complete blast renders the contradiction");
    assert_eq!(
        proof
            .steps
            .iter()
            .filter_map(|step| match step {
                ProofStep::Assume(term) => Some(*term),
                _ => None,
            })
            .collect::<Vec<_>>(),
        authored
    );
    assert!(executor
        .check_proof_strict_with_datatypes(&proof)
        .is_ok_and(|quality| quality.is_complete()));
    let document = ay_proof::try_export_alethe_with_problem_scope_and_overrides(
        &proof,
        &executor.ctx.terms,
        &authored,
        None,
    )
    .expect("same original scope");
    assert!(!document.contains(":rule hole") && !document.contains(":rule trust"));
}

#[test]
fn bv_denial_does_not_hide_same_source_affine_fallback() {
    let mut executor = fixture(AFFINE);
    executor.set_produce_proofs(true);
    let offers = RefCell::new(Vec::new());
    let proof = executor
        .exact_authored_bv_refutation(|_, candidate| {
            let kind = lemma(candidate).0;
            offers.borrow_mut().push(kind.clone());
            kind == TheoryLemmaKind::ArithClauseTautology
        })
        .expect("the independently recognized affine theorem remains available");
    assert_eq!(
        *offers.borrow(),
        [
            TheoryLemmaKind::BvBitBlast,
            TheoryLemmaKind::ArithClauseTautology
        ]
    );
    assert_eq!(lemma(&proof).0, TheoryLemmaKind::ArithClauseTautology);
    assert!(executor.check_proof_strict_with_datatypes(&proof).is_ok());
}

#[test]
fn unconditional_advice_cannot_accept_a_satisfiable_source_or_foreign_scope() {
    let mut executor = fixture("(declare-const x (_ BitVec 4)) (assert (= x #x0))");
    assert!(executor.exact_authored_bv_refutation(|_, _| true).is_none());
    let mut executor = fixture(CONTRADICTION);
    let proof = executor
        .exact_authored_bv_refutation(|_, _| true)
        .expect("native twin");
    let scope = executor.exact_concrete_authored_scope();
    assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &scope[..1]).is_err());
}

#[test]
fn one_shot_preflight_stop_survives_affine_retry_and_helper_return() {
    let mut executor = fixture(AFFINE);
    executor.set_produce_proofs(true);
    let armed = Arc::new(AtomicBool::new(false));
    let observed = Arc::clone(&armed);
    let _original = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.swap(false, Ordering::SeqCst)
    }));
    let offers = Cell::new(0);
    assert!(executor
        .exact_authored_bv_refutation(|_, _| {
            offers.set(offers.get() + 1);
            armed.store(true, Ordering::SeqCst);
            assert!(
                ay_core::resource::check_stop_requested(),
                "nested wire callback consumed stop"
            );
            false
        })
        .is_none());
    assert_eq!(offers.get(), 1, "no alternate kind after refusal");
    assert!(
        !armed.load(Ordering::SeqCst),
        "one-shot callback already cleared"
    );
    assert_eq!(executor.certification_stop(), Some(EnvelopeStop::Caller));
    assert!(executor.evaluation_stop_origin().is_some());
    assert!(executor
        .exact_authored_bv_refutation(|_, _| panic!("no renewed attempt"))
        .is_none());
    assert!(
        executor.should_abort_theory_loop(),
        "enclosing publication cannot revive it"
    );
}

/// #check-sat-assuming-empty-core: a core-minimizer subset attempt starts from
/// a fresh evaluation attempt. A stop a previous attempt's strict walk noted
/// (here an opaque caller stop, which no later poll re-observes) must not
/// refuse this attempt's repair (and, through it, the attempt), or every
/// attempt after the first stop is dead on arrival.
#[test]
fn a_previous_subset_attempts_noted_stop_does_not_refuse_the_next_attempt() {
    let mut executor = fixture(CONTRADICTION);
    let parked = executor.park_evaluation_decision();
    executor.note_certification_stop(EnvelopeStop::Caller);
    executor.begin_subset_evaluation_attempt();
    assert!(executor.exact_authored_bv_refutation(|_, _| true).is_some());
    assert_eq!(executor.evaluation_stop_origin(), None);
    executor.restore_evaluation_decision(parked);
}

/// #check-sat-assuming-empty-core: the same, across public decisions. A stop
/// noted during query N (its certification's strict walk) is not query N+1's
/// refusal, whatever its kind.
#[test]
fn a_previous_decisions_noted_stop_does_not_refuse_the_next_decision() {
    for stop in [
        EnvelopeStop::Interrupt,
        EnvelopeStop::Caller,
        EnvelopeStop::Backstop,
    ] {
        let mut executor = fixture(CONTRADICTION);
        executor.note_certification_stop(stop);
        executor.begin_external_decision_query(false);
        assert_eq!(executor.certification_stop(), None, "{stop:?}");
        assert!(
            executor.exact_authored_bv_refutation(|_, _| true).is_some(),
            "{stop:?}"
        );
        assert_eq!(executor.evaluation_stop_origin(), None, "{stop:?}");
    }
}

/// #check-sat-assuming-empty-core: a search lane narrows only the search wall,
/// and proof assembly obeys the certification envelope
/// (`build_unsat_assembly/stop.rs`). A strict walk that polled an expired
/// slice notes a `Backstop`; under a live envelope that is not the repair's
/// refusal, nor the attempt's: neither while the slice is still expired (the
/// core minimizer's subset attempt), nor once the lane restored the wall.
#[test]
fn a_search_slice_stop_a_strict_walk_noted_does_not_refuse_the_repair() {
    let far = ay_core::time::Instant::now().checked_add(std::time::Duration::from_secs(3_600));
    let mut executor = fixture(CONTRADICTION);
    executor.set_deadline(far);
    executor.set_search_deadline(Some(ay_core::time::Instant::now()));
    assert!(executor
        .check_proof_strict_with_datatypes(&Proof::new())
        .is_err());
    assert_eq!(
        executor.certification_stop(),
        Some(EnvelopeStop::Backstop),
        "fixture: the walk noted the expired slice"
    );
    let _ = executor.exact_authored_bv_refutation(|_, _| true);
    assert_eq!(executor.evaluation_stop_origin(), None);
    executor.set_search_deadline(far);
    assert!(executor.exact_authored_bv_refutation(|_, _| true).is_some());
    assert_eq!(executor.evaluation_stop_origin(), None);
}

/// Negative twin: within one attempt a noted stop the continuation cannot
/// re-observe (an opaque caller stop), and a backstop of the expired
/// certification envelope, still refuse the repair before any advice, and the
/// refusal is retained on the enclosing attempt.
#[test]
fn a_stop_noted_in_the_same_attempt_still_refuses_its_repair() {
    let mut executor = fixture(CONTRADICTION);
    executor.note_certification_stop(EnvelopeStop::Caller);
    assert!(executor
        .exact_authored_bv_refutation(|_, _| panic!("stopped before advice"))
        .is_none());
    assert!(executor.evaluation_stop_origin().is_some());

    let mut executor = fixture(CONTRADICTION);
    executor.set_deadline(Some(ay_core::time::Instant::now()));
    assert!(executor
        .check_proof_strict_with_datatypes(&Proof::new())
        .is_err());
    assert_eq!(executor.certification_stop(), Some(EnvelopeStop::Backstop));
    assert!(executor
        .exact_authored_bv_refutation(|_, _| panic!("stopped before advice"))
        .is_none());
    assert!(executor.evaluation_stop_origin().is_some());
}

#[test]
fn caught_original_callback_panic_remains_on_the_enclosing_attempt() {
    let mut executor = fixture(AFFINE);
    let original = ay_core::resource::enter_check_stop(Arc::new(|| panic!("original callback")));
    assert!(std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        executor.exact_authored_bv_refutation(|_, _| true)
    }))
    .is_err());
    drop(original);
    assert!(executor.evaluation_stop_origin().is_some());
    assert!(executor
        .exact_authored_bv_refutation(|_, _| panic!("stopped repair"))
        .is_none());
}

#[test]
fn preexisting_interrupt_and_deadline_prevent_even_presentation_advice() {
    for deadline in [false, true] {
        let mut executor = fixture(CONTRADICTION);
        if deadline {
            executor.set_deadline(Some(ay_core::time::Instant::now()));
        } else {
            executor.set_solve_controls(Some(Arc::new(AtomicBool::new(true))), None);
        }
        assert!(executor
            .exact_authored_bv_refutation(|_, _| panic!("stopped before advice"))
            .is_none());
        assert_eq!(
            executor.certification_stop(),
            Some(if deadline {
                EnvelopeStop::Backstop
            } else {
                EnvelopeStop::Interrupt
            })
        );
    }
}

#[test]
fn parsed_source_keeps_the_existing_exact_refutation_path() {
    let mut executor = fixture(CONTRADICTION);
    assert!(!executor.ctx.assertions_parsed().is_empty());
    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Trust, vec![], vec![], vec![]);
    assert!(!executor.try_authenticated_native_bv_refutation(&mut proof));
    assert_eq!(
        executor.evaluation_attempt().native_bv_refutation_count(),
        0
    );
    assert!(executor.exact_authored_bv_refutation(|_, _| true).is_some());
}

#[test]
fn genuine_65_duplicate_rows_preserve_exact_parsed_and_unretained_scope() {
    for retain in [true, false] {
        let mut executor = fixture_with_retention(CONTRADICTION, retain);
        let authored = executor.exact_concrete_authored_scope();
        assert_eq!(authored.len(), 2);
        let surface = ay_frontend::parse(CONTRADICTION)
            .expect("source")
            .into_iter()
            .find_map(|command| match command {
                ay_frontend::Command::Assert(surface) => Some(surface),
                _ => None,
            })
            .expect("first genuine source row");
        for _ in 2..65 {
            executor
                .ctx
                .add_assertion_with_parsed(authored[0], surface.clone());
        }
        assert_eq!(executor.ctx.assertions.len(), 65);
        assert_eq!(
            executor.ctx.assertions_parsed().len(),
            if retain { 65 } else { 0 }
        );
        executor.begin_public_solve(false);
        executor.bind_unsat_query_assumptions(&[]);
        assert_eq!(
            executor.native_bv_source_kind(&|| false),
            Some(NativeAssertionSurfaces::Other)
        );
        assert_eq!(executor.exact_concrete_authored_scope(), authored);
        // The existing epoch getter supports up to 1024 raw roots. Native
        // scheduling/grammar has its separate cap of 64; genuine source keeps the
        // old stable two-root projection even when the epoch contains 65 rows.
        assert_eq!(
            NativeBvRefutationScope::capture(&executor)
                .expect("authenticated epoch, independent of native scheduling")
                .roots()
                .len(),
            65
        );
        let mut incumbent = Proof::new();
        assert!(!executor.try_authenticated_native_bv_refutation(&mut incumbent));
        let proof = executor
            .exact_authored_bv_refutation(|_, _| true)
            .expect("legacy duplicate source refutation");
        assert_eq!(lemma(&proof).0, TheoryLemmaKind::BvBitBlast);
        assert_eq!(lemma(&proof).1.len(), 2);
        assert_eq!(
            proof
                .steps
                .iter()
                .filter_map(|step| match step {
                    ProofStep::Assume(root) => Some(*root),
                    _ => None,
                })
                .collect::<Vec<_>>(),
            authored
        );
        assert!(Executor::proof_derives_empty_clause(&proof));
        assert!(executor
            .check_proof_strict_with_datatypes(&proof)
            .is_ok_and(|quality| quality.is_complete()));
        assert!(ay_proof::validate_reachable_assumes_in_problem_scope(&proof, &authored).is_ok());
    }
}
