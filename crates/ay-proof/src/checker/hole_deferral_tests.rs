// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `hole` is a member of the trust family and must be DEFERRED, not rejected.
//!
//! The deferred-trust path exists because AY decides many BV/array clauses and
//! exports the learned theory clause as an unjustified step, the Alethe rule set
//! being incomplete there. Rejecting such a step BY NAME throws away a correct
//! refutation; the fix was to replace "reject by name" with "verify" — collect
//! the clause and discharge it independently.
//!
//! That machinery only ever recognised `AletheRule::Trust`. But AY treats `Hole`
//! as the same thing everywhere else it matters:
//!
//! - `executor/proof_euf_lemma.rs` and `executor/proof.rs` both match
//!   `rule: AletheRule::Trust | AletheRule::Hole` in one pattern;
//! - `ay-proof/src/terminal_trust.rs` counts `Hole` steps as reachable trust;
//! - `arrays_to_lia.rs` and `theories/combined/mod.rs` DOWNGRADE an existing
//!   step to `Hole`, keeping its clause — so a hole carries a real obligation,
//!   not a placeholder.
//!
//! Only the checker's collector and the certification funnel disagreed, and a
//! census of nine `ay-dpll` buckets put `uses unsupported hole rule` at the top
//! of what remains after the shape-rule fixes.
//!
//! This is the same correction already recorded for `TheoryLemmaKind::Generic`
//! in `unsat_cert.rs`: the checker reported a different error VARIANT for what is
//! semantically the same situation, so the rescue never fired. Deferring changes
//! only WHICH steps get re-examined. The discharge itself is untouched — every
//! collected clause still has to survive the forged-UNSAT guard, full strict
//! validation of every non-deferred step, and an independent solve.
//!
//! The load-bearing test here is the second one: PLAIN strict mode, with no
//! collector, must still reject a hole outright. Deferral is only ever available
//! to a caller that has committed to discharging what it collects.

use crate::checker::*;
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId, TermStore};

/// `(cl (or p (not p)))` as a hole step, followed by the terminal empty clause.
///
/// The hole's clause is deliberately a real, non-empty obligation — that is what
/// a downgraded theory step looks like.
fn hole_proof() -> (TermStore, Proof, Vec<TermId>) {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);
    let tautology = terms.mk_app(Symbol::named("or"), vec![p, not_p], Sort::Bool);

    let mut proof = Proof::new();
    proof.add_rule_step(AletheRule::Hole, vec![tautology], Vec::new(), Vec::new());
    proof.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());

    (terms, proof, vec![tautology])
}

#[test]
fn collecting_mode_defers_a_hole_step_instead_of_rejecting_it() {
    let (terms, proof, clause) = hole_proof();

    let collected = check_proof_collecting_trust(&proof, &terms)
        .expect("a hole step must be DEFERRED for independent discharge, not rejected by name");

    assert!(
        collected.contains(&(ProofId(0), clause)),
        "the hole's clause must actually reach the collector — deferring without \
         collecting would admit it unverified, which is the one outcome this \
         path must never produce. got {collected:?}"
    );
}

/// THE LOAD-BEARING CASE. Without a collector there is nobody to discharge the
/// obligation, so a hole must still be a hard rejection.
#[test]
fn plain_strict_mode_still_rejects_a_hole_step() {
    let (terms, proof, _) = hole_proof();

    let err = crate::quality::check_proof_strict(&proof, &terms)
        .expect_err("plain strict mode has no discharger, so a hole must stay rejected");

    assert!(
        matches!(err, ProofCheckError::HoleStep { step: ProofId(0) }),
        "expected HoleStep at the hole, got {err:?}"
    );
}

/// A deferred hole must still enter the derived-clause table, exactly as a
/// deferred `Trust` does, or downstream resolution/DRUP linkage breaks.
#[test]
fn a_deferred_hole_clause_is_available_to_later_steps() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not(p);

    let mut proof = Proof::new();
    // t0: hole  (cl p)
    proof.add_rule_step(AletheRule::Hole, vec![p], Vec::new(), Vec::new());
    // t1: hole  (cl (not p))
    proof.add_rule_step(AletheRule::Hole, vec![not_p], Vec::new(), Vec::new());
    // t2: resolve t0 with t1 on p  ->  empty clause
    proof.add_resolution(Vec::new(), p, ProofId(0), ProofId(1));

    let collected = check_proof_collecting_trust(&proof, &terms).expect(
        "resolution over two deferred holes must link up — a deferred step whose \
         clause never lands in the derived table would break every proof that \
         resolves against it",
    );

    assert_eq!(
        collected.len(),
        2,
        "both holes must be collected for discharge, got {collected:?}"
    );
}
