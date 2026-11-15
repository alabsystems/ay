// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #strict-walk-memo adversarial currency tests.
//!
//! Every conjunct of `entry_is_current`, the never-store arms and the
//! bounded-retention rules are pinned RED-on-deletion here. The stale-hit
//! tests are deliberately adversarial: they mutate the document (and
//! separately the term store, the authored scope, the shadow latches and
//! the Skolem registries) AFTER a cached accept and require the next call
//! to MISS and re-walk. Arms 4–7 pin the checker-visible-metadata
//! conjunct AND its four `ay-core` mutator bumps (`mark_to_real_shadowed`,
//! `mark_is_int_shadowed`, `mark_skolem_symbol`, `register_skolem_choice`
//! — including the same-size overwrite direction); arm 4 is the landed
//! reproducer from the adversarial review of `ebcf2aa8fc`.

use std::str::FromStr;

use ay_core::{Proof, ProofStep, Sort, TermId};
use ay_proof::{ProofCheckError, ProofQuality};
use ntest::timeout;
use num_bigint::BigInt;

use super::strict_memo::{StrictWalkKey, STRICT_WALK_MEMO_MAX_PAYLOAD};
use crate::executor::Executor;

/// One strict-certifiable UNSAT solve, returning the executor and a clone of
/// its finished proof document.
fn solved_executor() -> (Executor, Proof) {
    let input = r#"
        (set-option :produce-proofs true)
        (set-option :check-proofs-strict true)
        (set-logic QF_LRA)
        (declare-const x Real)
        (assert (< x 0))
        (assert (> x 0))
        (check-sat)
    "#;
    let commands = ay_frontend::parse(input).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(outputs[0], "unsat");
    let proof = exec.last_proof.clone().expect("UNSAT retains a proof");
    (exec, proof)
}

fn hits(exec: &Executor) -> u64 {
    exec.strict_check_memo_hits.get()
}

/// An empty-context key for driving `strict_walk_memo_store`/`_lookup`
/// directly in the unit-level tests below.
fn empty_key<'a>() -> StrictWalkKey<'a> {
    StrictWalkKey {
        datatype_decls: &[],
        selector_decls: &[],
        member_signatures: &[],
        problem: &[],
    }
}

fn tiny_proof(term: TermId) -> Proof {
    let mut proof = Proof::default();
    proof.add_step(ProofStep::Assume(term));
    proof
}

/// A repeated identical walk replays the stored verdict: outcome AND metered
/// work byte-identical, one memo hit counted, and the hit statistic is
/// published.
#[test]
#[timeout(60000)]
fn a_repeat_identical_walk_replays_the_stored_verdict() {
    let (exec, proof) = solved_executor();
    let stats = exec.statistics();
    assert!(
        stats.get_int("proof.strict_check_memo_hits").is_some(),
        "memo-hit statistic must be published with the M0(a) counters"
    );
    exec.strict_walk_memo.borrow_mut().clear();

    let h0 = hits(&exec);
    let (first, first_work) = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h0, "a cold call must be a miss");
    let (second, second_work) = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h0 + 1,
        "an identical repeat under an unchanged context must replay from the memo"
    );
    assert_eq!(first, second, "a replay must be the checker's own verdict");
    assert_eq!(
        first_work, second_work,
        "a replay must report the original walk's metered work — it is the \
         campaign's deterministic cost figure and a hit must not report a \
         cheaper walk than the one it replays"
    );
    // The invocation counters keep counting ENTRIES (M0(a) semantics are
    // unchanged); the hit counter is what separates walks from replays.
    assert!(exec.strict_check_invocations.get() >= 2);
}

/// THE stale-hit direction, arm 1: mutate the DOCUMENT after a cached accept.
/// Both a truncation and a content-preserving reorder must MISS — deleting
/// the `entry.proof == *proof` conjunct in `entry_is_current` turns this RED.
#[test]
#[timeout(60000)]
fn a_document_mutation_after_a_cached_accept_misses_and_rewalks() {
    let (exec, mut proof) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();

    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    let h1 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h1 + 1, "precondition: the accept is cached");

    // Adversarial mutation A: drop the final step.
    let removed = proof.steps.pop().expect("finished proof has steps");
    let h2 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h2,
        "a truncated document must MISS and re-walk — a hit here is a \
         verdict for a document the checker never saw"
    );

    // Adversarial mutation B: same steps, same length, different ORDER —
    // put the removed step back and swap the first two steps.
    proof.steps.push(removed);
    assert!(proof.steps.len() >= 2, "fixture needs two steps to reorder");
    proof.steps.swap(0, 1);
    let h3 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h3,
        "a reordered document of identical length must MISS — document \
         identity is literal equality, not a size fingerprint"
    );
}

/// THE stale-hit direction, arm 2: intern a NEW term after a cached accept.
/// The term-store snapshot stamp retires the entry — deleting the
/// `entry.term_snapshot` conjunct turns this RED.
#[test]
#[timeout(60000)]
fn interning_a_term_after_a_cached_accept_misses_and_rewalks() {
    let (mut exec, proof) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();

    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    let h1 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h1 + 1, "precondition: the accept is cached");

    let stamp_before = exec.ctx.terms.snapshot_stamp();
    let novel = BigInt::from_str("987654321987654321987654321").unwrap();
    let _ = exec.ctx.terms.mk_int(novel);
    assert_ne!(
        stamp_before,
        exec.ctx.terms.snapshot_stamp(),
        "fixture: interning a novel constant must retire the snapshot stamp"
    );

    let h2 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h2,
        "an unchanged document over a CHANGED term universe must MISS — \
         TermIds are only meaningful relative to the store snapshot"
    );
    // The re-walk re-stores under the new stamp; the memo works again.
    let h3 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h3 + 1, "re-walked verdict is cached afresh");
}

/// THE stale-hit direction, arm 3: change the AUTHORED SCOPE after a cached
/// accept without touching the term store. Deleting the `entry.problem`
/// conjunct turns this RED.
#[test]
#[timeout(60000)]
fn an_authored_scope_change_after_a_cached_accept_misses() {
    let (mut exec, proof) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();

    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    let h1 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h1 + 1, "precondition: the accept is cached");

    // Extend the authored window with an EXISTING term that is not already in
    // the strict scope: the scope vector changes while the term store does
    // not, isolating the scope conjunct from the stamp conjunct.
    let scope_before = exec.complete_problem_assertions_for_strict_proof();
    let stamp_before = exec.ctx.terms.snapshot_stamp();
    let addition = exec
        .ctx
        .terms
        .term_ids()
        .find(|id| !scope_before.contains(id))
        .expect("some interned term lies outside the authored scope");
    match exec.self_check_authored_assertions.as_mut() {
        Some(authored) => authored.push(addition),
        None => exec.self_check_authored_assertions = Some(vec![addition]),
    }
    assert_ne!(
        scope_before,
        exec.complete_problem_assertions_for_strict_proof(),
        "fixture: the authored scope must actually change"
    );
    assert_eq!(
        stamp_before,
        exec.ctx.terms.snapshot_stamp(),
        "fixture: the term store must NOT change in this arm"
    );

    let h2 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h2,
        "an unchanged document under a CHANGED authored scope must MISS — \
         the scope is the checker's freshness/authorization authority"
    );
}

/// A STOPPING caller never receives a cached answer: the stop must surface
/// as the walk's own `Cancelled`, which downstream reverts without latching
/// (the commit gate's tier 4). Deleting the stop poll in
/// `strict_walk_memo_lookup` turns this RED.
#[test]
#[timeout(60000)]
fn a_stopping_caller_observes_cancellation_without_counting_a_cached_hit() {
    let (mut exec, proof) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    let h1 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h1 + 1, "precondition: the verdict is cached");

    let now = std::time::Instant::now();
    let expired = now
        .checked_sub(std::time::Duration::from_millis(50))
        .unwrap_or(now);
    exec.set_solve_controls(None, Some(expired));
    let h2 = hits(&exec);
    let (outcome, _) = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h2,
        "a stopping caller must MISS — cached knowledge must not change \
         what a dying solve decides"
    );
    assert!(
        matches!(outcome, Err(ProofCheckError::Cancelled)),
        "the stop must surface as the walk's own Cancelled: {outcome:?}"
    );
    // With the stop cleared the memo serves again.
    exec.set_solve_controls(None, None);
    let h3 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h3 + 1, "clearing the stop restores the hit");
}

#[test]
fn one_shot_original_refusal_is_not_a_miss_followed_by_a_fresh_walk() {
    use std::sync::{
        atomic::{AtomicUsize, Ordering},
        Arc,
    };
    let (exec, proof) = solved_executor();
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    let before = hits(&exec);
    let calls = Arc::new(AtomicUsize::new(0));
    let observed = calls.clone();
    let _scope = ay_core::resource::enter_check_stop(Arc::new(move || {
        observed.fetch_add(1, Ordering::SeqCst) == 0
    }));
    let result = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(result.0, Err(ProofCheckError::Cancelled));
    assert_eq!(result.1, 0);
    assert_eq!(hits(&exec), before);
    assert_eq!(calls.load(Ordering::SeqCst), 1);
    assert_eq!(
        exec.certification_stop.get(),
        Some(crate::api::proofs::EnvelopeStop::Caller)
    );
}

/// A cancellation is a fact about the caller, not the document: it must
/// never be stored. Deleting the `Cancelled` early-return in
/// `strict_walk_memo_store` turns this RED.
#[test]
#[timeout(60000)]
fn a_cancelled_walk_is_never_stored() {
    let (exec, _) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();
    let doc = tiny_proof(exec.ctx.terms.true_term());
    let key = empty_key();
    exec.strict_walk_memo_store(&doc, &key, &Err(ProofCheckError::Cancelled), 42);
    assert!(
        exec.strict_walk_memo_lookup(&doc, &key).is_none(),
        "a cancelled walk left a stored verdict behind"
    );
}

/// Registry, signature and scope drift each retire an entry independently;
/// an unchanged context replays the stored verdict WITH its original work.
/// Deleting any single conjunct of `entry_is_current` turns exactly one
/// assertion here RED.
#[test]
#[timeout(60000)]
fn every_context_conjunct_is_an_independent_invalidator() {
    let (exec, _) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();
    let doc = tiny_proof(exec.ctx.terms.true_term());
    let key = empty_key();
    let quality = ProofQuality::default();
    exec.strict_walk_memo_store(&doc, &key, &Ok(quality.clone()), 7777);

    // Unchanged context: replay, with the original metered work.
    match exec.strict_walk_memo_lookup(&doc, &key) {
        Some((Ok(replayed), 7777)) => assert_eq!(replayed, quality),
        other => panic!("unchanged context must replay the stored verdict, got {other:?}"),
    }

    let decls = vec![("C".to_string(), vec!["c0".to_string()])];
    let with_decls = StrictWalkKey {
        datatype_decls: &decls,
        ..empty_key()
    };
    assert!(
        exec.strict_walk_memo_lookup(&doc, &with_decls).is_none(),
        "datatype-declaration drift must be a miss"
    );

    let with_selectors = StrictWalkKey {
        selector_decls: &decls,
        ..empty_key()
    };
    assert!(
        exec.strict_walk_memo_lookup(&doc, &with_selectors)
            .is_none(),
        "selector-registry drift must be a miss"
    );

    let signatures = vec![ay_proof::DatatypeMemberSignature {
        identity: "C".to_string(),
        argument_sorts: Vec::new(),
        result_sort: Sort::Bool,
        nullary_term: None,
    }];
    let with_signatures = StrictWalkKey {
        member_signatures: &signatures,
        ..empty_key()
    };
    assert!(
        exec.strict_walk_memo_lookup(&doc, &with_signatures)
            .is_none(),
        "member-signature drift must be a miss"
    );

    let problem = vec![exec.ctx.terms.true_term()];
    let with_problem = StrictWalkKey {
        problem: &problem,
        ..empty_key()
    };
    assert!(
        exec.strict_walk_memo_lookup(&doc, &with_problem).is_none(),
        "authored-scope drift must be a miss"
    );

    // A different document under the SAME context is a miss too.
    let other_doc = tiny_proof(exec.ctx.terms.false_term());
    assert!(
        exec.strict_walk_memo_lookup(&other_doc, &key).is_none(),
        "document drift must be a miss"
    );
}

/// Documents past the retention payload bound are walked normally and simply
/// not stored. Deleting the bound turns this RED (and unbounds memo memory).
#[test]
#[timeout(60000)]
fn an_oversized_document_is_not_retained() {
    let (exec, _) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();
    let mut doc = Proof::default();
    doc.add_step(ProofStep::Step {
        rule: ay_core::AletheRule::Trust,
        clause: vec![exec.ctx.terms.true_term(); STRICT_WALK_MEMO_MAX_PAYLOAD + 1],
        premises: Vec::new(),
        args: Vec::new(),
    });
    let key = empty_key();
    exec.strict_walk_memo_store(&doc, &key, &Ok(ProofQuality::default()), 1);
    assert!(
        exec.strict_walk_memo_lookup(&doc, &key).is_none(),
        "an oversized document must not be retained"
    );
}

/// The ring keeps at most its capacity, evicting oldest-first, and a
/// re-stored identical document replaces its predecessor instead of
/// duplicating it.
#[test]
#[timeout(60000)]
fn the_memo_is_a_bounded_ring_with_identity_replacement() {
    let (exec, _) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();
    let key = empty_key();
    let terms: Vec<TermId> = exec.ctx.terms.term_ids().take(5).collect();
    assert!(terms.len() >= 5, "fixture needs five interned terms");
    for &term in &terms {
        exec.strict_walk_memo_store(&tiny_proof(term), &key, &Ok(ProofQuality::default()), 1);
    }
    assert!(
        exec.strict_walk_memo_lookup(&tiny_proof(terms[0]), &key)
            .is_none(),
        "the oldest entry past capacity must have been evicted"
    );
    for &term in &terms[1..] {
        assert!(
            exec.strict_walk_memo_lookup(&tiny_proof(term), &key)
                .is_some(),
            "recent entries within capacity must be retained"
        );
    }
    // Identity replacement: re-storing a document already present keeps ONE
    // entry for it and does not evict a neighbour. Deliberately re-store a
    // MIDDLE entry, not the ring's front: at the front, plain eviction and
    // identity replacement coincide, and the mutation that deletes the
    // replacement (duplicating the document and evicting the oldest
    // neighbour) would pass unobserved.
    exec.strict_walk_memo_store(&tiny_proof(terms[3]), &key, &Ok(ProofQuality::default()), 2);
    for &term in &terms[1..] {
        assert!(
            exec.strict_walk_memo_lookup(&tiny_proof(term), &key)
                .is_some(),
            "identity replacement must not evict a live neighbour"
        );
    }
    match exec.strict_walk_memo_lookup(&tiny_proof(terms[3]), &key) {
        Some((_, 2)) => {}
        other => panic!("re-store must supersede the stored verdict, got {other:?}"),
    }
}

/// The per-check session reset forgets every stored verdict alongside the
/// M0(a) counter reset. Pinned at `reset_solve_session_state` directly: a
/// repeated identical `(check-sat)` can short-circuit without a session
/// reset, and an assertion-set change also retires entries through the
/// snapshot stamp — only the direct call isolates the clear itself, so
/// deleting the `strict_walk_memo.borrow_mut().clear()` line turns exactly
/// this test RED.
#[test]
#[timeout(60000)]
fn the_session_reset_clears_the_memo() {
    let (mut exec, _) = solved_executor();
    let doc = tiny_proof(exec.ctx.terms.true_term());
    let key = empty_key();
    exec.strict_walk_memo_store(&doc, &key, &Ok(ProofQuality::default()), 3);
    assert!(exec.strict_walk_memo_lookup(&doc, &key).is_some());
    exec.reset_solve_session_state();
    assert!(
        exec.strict_walk_memo_lookup(&doc, &key).is_none(),
        "the session reset must start the next check with an empty memo"
    );
    assert_eq!(
        exec.strict_check_memo_hits.get(),
        0,
        "the hit counter shares the per-publication reset"
    );
}

/// THE stale-hit direction, arm 4 — the REVIEWER'S REPRODUCER (landed from
/// the adversarial review of `ebcf2aa8fc`, adapted): flip the `to_real`
/// shadow latch after a cached verdict. The latch is checker-read TermStore
/// metadata that mutates WITHOUT retiring the snapshot stamp — on the
/// reviewed SHA the memo replayed a verdict embedding an `Evaluate`
/// acceptance the checker would no longer grant (`FinalClauseNotEmpty`
/// served where a fresh walk decides `InvalidTheoryLemma`). Deleting the
/// `checker_metadata_generation` conjunct in `entry_is_current` — or the
/// bump in `TermStore::mark_to_real_shadowed` — turns this RED.
#[test]
#[timeout(60000)]
fn a_to_real_shadow_flip_after_a_cached_verdict_misses_and_rewalks() {
    use num_rational::BigRational;
    let input = r#"
        (set-option :produce-proofs true)
        (set-logic QF_UFLIRA)
        (declare-const x Int)
        (assert (> x 0))
        (check-sat)
    "#;
    let commands = ay_frontend::parse(input).unwrap();
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).unwrap();

    // (= (to_real 1) 1.0) in the executor's own store.
    let one = exec.ctx.terms.mk_int(BigInt::from(1));
    let real_one = exec
        .ctx
        .terms
        .mk_rational(BigRational::from(BigInt::from(1)));
    let to_real = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("to_real"), [one], Sort::Real);
    let eq = exec
        .ctx
        .terms
        .mk_app(ay_core::Symbol::named("="), [to_real, real_one], Sort::Bool);

    let mut proof = Proof::default();
    proof.add_step(ProofStep::Step {
        rule: ay_core::AletheRule::Evaluate,
        clause: vec![eq],
        premises: vec![],
        args: vec![],
    });

    exec.strict_walk_memo.borrow_mut().clear();
    let (fresh_before, _) = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    let h = hits(&exec);
    let (cached, _) = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h + 1, "precondition: the verdict is cached");
    assert_eq!(cached, fresh_before, "precondition: the replay is faithful");

    // Flip a checker input the stamp does not cover. No interning happens.
    let stamp_before = exec.ctx.terms.snapshot_stamp();
    exec.ctx.terms.mark_to_real_shadowed();
    assert_eq!(
        stamp_before,
        exec.ctx.terms.snapshot_stamp(),
        "precondition: the latch flip leaves the snapshot stamp unchanged"
    );

    let h2 = hits(&exec);
    let (served, _) = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h2,
        "a shadow-latch flip after a cached verdict must MISS and re-walk"
    );

    // Ground truth: what a real walk decides NOW.
    exec.strict_walk_memo.borrow_mut().clear();
    let (fresh_after, _) = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        served, fresh_after,
        "STALE HIT: the memo served a verdict for a checker-input state the \
         checker never walked"
    );
    assert_ne!(
        fresh_before, fresh_after,
        "fixture: the latch flip must actually change the checker's verdict \
         (otherwise this test proves nothing about staleness)"
    );
}

/// THE stale-hit direction, arm 5: flip the `is_int` shadow latch after a
/// cached accept. Isolated from the stamp exactly as arm 4. Deleting the
/// bump in `TermStore::mark_is_int_shadowed` turns this RED.
#[test]
#[timeout(60000)]
fn an_is_int_shadow_flip_after_a_cached_accept_misses() {
    let (mut exec, proof) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();

    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    let h1 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h1 + 1, "precondition: the accept is cached");

    let stamp_before = exec.ctx.terms.snapshot_stamp();
    exec.ctx.terms.mark_is_int_shadowed();
    assert_eq!(
        stamp_before,
        exec.ctx.terms.snapshot_stamp(),
        "precondition: the latch flip leaves the snapshot stamp unchanged"
    );

    let h2 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h2,
        "an is_int shadow flip after a cached accept must MISS — the ground \
         evaluator's acceptance depends on the latch"
    );
    // The re-walk re-stores under the new metadata generation.
    let h3 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h3 + 1, "re-walked verdict is cached afresh");
}

/// THE stale-hit direction, arm 6: register a NEW Skolem symbol after a
/// cached accept, with zero interning. `skolem_symbols` is insert-only, and
/// every in-publication registrar happens to mint fresh terms first — an
/// UNPINNED accident this test replaces with an enforced conjunct. Deleting
/// the bump in `TermStore::mark_skolem_symbol` turns this RED.
#[test]
#[timeout(60000)]
fn a_skolem_symbol_registration_after_a_cached_accept_misses() {
    let (mut exec, proof) = solved_executor();
    exec.strict_walk_memo.borrow_mut().clear();

    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    let h1 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h1 + 1, "precondition: the accept is cached");

    let stamp_before = exec.ctx.terms.snapshot_stamp();
    assert!(
        !exec.ctx.terms.is_skolem_symbol("sk!memo_probe!0"),
        "fixture: the probe name must be a NEW registration"
    );
    exec.ctx.terms.mark_skolem_symbol("sk!memo_probe!0");
    assert_eq!(
        stamp_before,
        exec.ctx.terms.snapshot_stamp(),
        "precondition: registering a name interns no term"
    );

    let h2 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h2,
        "a Skolem-symbol registration after a cached accept must MISS — \
         `is_skolem_symbol` is the checker's witness authority"
    );
    let h3 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h3 + 1, "re-walked verdict is cached afresh");
}

/// THE stale-hit direction, arm 7 — the ACCEPT→REJECT flip direction the
/// review named: `register_skolem_choice` OVERWRITES on re-registration,
/// changing the table at UNCHANGED size with zero interning. A cached
/// verdict must not survive the overwrite. Deleting the bump in
/// `TermStore::register_skolem_choice` turns this RED.
#[test]
#[timeout(60000)]
fn a_skolem_choice_overwrite_after_a_cached_accept_misses() {
    let (mut exec, proof) = solved_executor();

    // Mint the witness Var and its choice BODY, and register the FIRST
    // choice, all BEFORE the cached walk — afterwards only the overwrite
    // may touch the store.
    let witness = exec.ctx.terms.mk_fresh_var("sk!memo_overwrite", Sort::Real);
    let body_a = exec.ctx.terms.true_term();
    let body_b = exec.ctx.terms.false_term();
    exec.ctx.terms.register_skolem_choice(
        witness,
        ay_core::SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Real,
            body: body_a,
        },
    );
    let table_size_before = exec.ctx.terms.skolem_choices().count();

    exec.strict_walk_memo.borrow_mut().clear();
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    let h1 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h1 + 1, "precondition: the accept is cached");

    // OVERWRITE the registered choice: same witness, different body.
    let stamp_before = exec.ctx.terms.snapshot_stamp();
    exec.ctx.terms.register_skolem_choice(
        witness,
        ay_core::SkolemChoice {
            binder: "x".to_string(),
            sort: Sort::Real,
            body: body_b,
        },
    );
    assert_eq!(
        stamp_before,
        exec.ctx.terms.snapshot_stamp(),
        "precondition: the overwrite interns no term"
    );
    assert_eq!(
        exec.ctx.terms.skolem_choices().count(),
        table_size_before,
        "precondition: the overwrite leaves the table SIZE unchanged — the \
         direction a size fingerprint could never observe"
    );
    assert_eq!(
        exec.ctx
            .terms
            .skolem_choice(witness)
            .map(|choice| choice.body),
        Some(body_b),
        "precondition: the overwrite actually replaced the choice"
    );

    let h2 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(
        hits(&exec),
        h2,
        "a same-size skolem_choice overwrite after a cached accept must \
         MISS — the checker validates sko_ex witnesses against this table"
    );
    let h3 = hits(&exec);
    let _ = exec.check_proof_strict_with_datatypes_reporting_work(&proof);
    assert_eq!(hits(&exec), h3 + 1, "re-walked verdict is cached afresh");
}
