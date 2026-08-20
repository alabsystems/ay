// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Native-API certification for the deductive-checks PANIC-FREEDOM VC shape.
//!
//! Captured byte-for-byte from the query the VerifierConsumer compiler emits for
//! `tests/trust-falsification/proved/contract_panic_annotated.rs` (the single
//! rejected query of that compile). Two structures the arithmetic-ITE Farkas
//! lane could not seed made it decline, so the exported UNSAT kept its
//! unverifiable `trust` closer and mandatory strict certification downgraded a
//! correct refutation to `unknown` ("step t1 uses unverified trust rule"):
//!
//! * `(= __trust_u__3 (< __trust_u_i 8))` — a `bool` temporary bound to a
//!   comparison. `usable_atom` accepts any binary `=`, so the whole IFF
//!   interned as ONE opaque SAT variable: the theory atom never reached the
//!   LRA oracle and neither implication was available to the case split.
//! * `(or (and (not (< i 8)) (<= 8 u)) (and (< i 8) (<= 8 u)))` — "both paths
//!   reach the bound". An `(and …)` is not a usable atom, so the entire clause
//!   was dropped and the bound `(<= 8 u)` never entered the database.
//!
//! Both are now derived, not assumed: `equiv_pos1`/`equiv_pos2` for the iff and
//! positional `and_pos` weakening for the distribution, every step re-derived
//! by the unchanged strict checker before the candidate may replace the trust
//! proof.

use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep, TermId, TermStore};
use num_bigint::BigInt;

use crate::api::{Logic, Solver, Sort};

/// The captured obligation (query-14299-00002) as ONE top-level conjunction,
/// built term by term through the NATIVE API — exactly how VerifierConsumer's in-process
/// backend asserts it: no SMT-LIB text, so no authored surface exists and the
/// parse-mode zip a surface-matching lane would need is unavailable.
fn assert_panic_freedom_obligation(solver: &mut Solver) {
    let flag = solver.declare_const("__trust_u__3", Sort::Bool);
    let index = solver.declare_const("__trust_u_i", Sort::Int);
    let slot = solver.declare_const("__trust_u__5", Sort::Int);
    let key = solver.declare_const("__trust_u_k#s1_0_s2_0", Sort::Int);

    let zero = solver.int_const(0);
    let seven = solver.int_const(7);
    let eight = solver.int_const(8);
    let usize_max = solver.int_const_bigint(&BigInt::from(u64::MAX));

    let mut conjuncts = Vec::new();
    conjuncts.push(solver.le(zero, index));
    conjuncts.push(solver.le(index, usize_max));
    conjuncts.push(solver.eq(slot, key));

    // (ite flag (= i k) (= k 7))
    let then_branch = solver.eq(index, key);
    let else_branch = solver.eq(key, seven);
    conjuncts.push(solver.ite(flag, then_branch, else_branch));

    // (= flag (< i 8)) — the Bool/theory IFF.
    let in_range = solver.lt(index, eight);
    conjuncts.push(solver.eq(flag, in_range));

    // (or (and (not (< i 8)) (<= 8 u)) (and (< i 8) (<= 8 u))) — the
    // disjunction whose DISJUNCTS ARE CONJUNCTIONS.
    let bound = solver.le(eight, slot);
    let out_of_range = solver.not(in_range);
    let high_path = solver.and_many(&[out_of_range, bound]);
    let low_path = solver.and_many(&[in_range, bound]);
    conjuncts.push(solver.or_many(&[high_path, low_path]));

    let obligation = solver.and_many(&conjuncts);
    solver
        .try_assert_named(obligation, "dn0")
        .expect("obligation asserts");
}

/// The rule of every `Step` in `proof`.
fn rules(proof: &Proof) -> Vec<AletheRule> {
    proof
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::Step { rule, .. } => Some(rule.clone()),
            _ => None,
        })
        .collect()
}

/// Whether `term` is an `(and t₁ t₂)` — the shape of a conjunctive DISJUNCT,
/// as opposed to the many-conjunct obligation root.
fn is_binary_conjunction(terms: &TermStore, term: TermId) -> bool {
    matches!(
        terms.get(term),
        TermData::App(ay_core::Symbol::Named(name), args) if name == "and" && args.len() == 2
    )
}

/// Solve the captured obligation natively and return the published proof plus
/// the term store it is written over.
fn certified_panic_freedom_proof() -> (Proof, TermStore) {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    // Mirror the VerifierConsumer in-process backend exactly: proof production ON, which
    // makes strict certification mandatory for the published verdict.
    solver.set_produce_proofs(true);
    solver.set_produce_unsat_cores(true);
    assert_panic_freedom_obligation(&mut solver);

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat(),
        "captured panic-freedom obligation must publish UNSAT, got {:?} \
         (unknown_reason: {:?}, executor_error: {:?})",
        details.result.result(),
        details.unknown_reason,
        details.executor_error,
    );
    assert!(
        details.result.was_unsat_strictly_verified(),
        "native UNSAT must be strictly certified, not a trust-backed downgrade"
    );
    let proof = solver
        .executor
        .last_proof()
        .expect("UNSAT publishes a proof")
        .clone();
    let terms = solver.executor.terms().clone();
    (proof, terms)
}

/// Regression pin for the panic-freedom certification gap: the captured query
/// must publish a strictly certified, TRUST-FREE UNSAT through the native API.
#[test]
fn test_trust_native_panic_freedom_publishes_certified_unsat() {
    let (proof, terms) = certified_panic_freedom_proof();
    assert!(
        ay_proof::terminal_trust_report(&proof).is_trust_free(),
        "the empty-clause derivation must not depend on trust"
    );
    let quality = ay_proof::check_proof_strict(&proof, &terms)
        .expect("native panic-freedom UNSAT has a strict proof");
    assert_eq!(
        quality.trust_count, 0,
        "proof must be trust-free: {quality}"
    );
    assert_eq!(quality.hole_count, 0, "proof must be hole-free: {quality}");
    assert!(quality.is_complete(), "proof must be complete: {quality}");
}

/// Both new seeding lanes must actually carry the refutation. Without the iff
/// lane there is no `equiv_pos*` step; without the disjunction distribution
/// there is no `or` clausification (this problem's only `or` has conjunctive
/// disjuncts, which the flat lane drops outright) and no `and_pos` over a
/// two-conjunct disjunct.
#[test]
fn test_trust_native_panic_freedom_uses_checked_iff_and_distribution() {
    let (proof, terms) = certified_panic_freedom_proof();
    let rules = rules(&proof);
    assert!(
        rules
            .iter()
            .any(|rule| matches!(rule, AletheRule::EquivPos1 | AletheRule::EquivPos2)),
        "the Bool/theory iff must be decomposed by a checked equiv_pos rule, got {rules:?}"
    );
    assert!(
        rules.iter().any(|rule| matches!(rule, AletheRule::Or)),
        "the conjunctive disjunction must be clausified, got {rules:?}"
    );
    assert!(
        proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::Step { rule: AletheRule::AndPos(_), args, .. }
                if args.first().is_some_and(|&term| is_binary_conjunction(&terms, term))
        )),
        "a conjunctive disjunct must be weakened by a positional and_pos step"
    );
}

/// Sanity floor for the encoding: without the "both paths reach the bound"
/// disjunction the obligation is satisfiable, so the UNSAT above is genuinely
/// about that disjunction and not an artifact of the captured shape.
#[test]
fn test_trust_native_panic_freedom_without_bound_is_sat() {
    let mut solver = Solver::try_new(Logic::All).expect("solver");
    let flag = solver.declare_const("__trust_u__3", Sort::Bool);
    let index = solver.declare_const("__trust_u_i", Sort::Int);
    let slot = solver.declare_const("__trust_u__5", Sort::Int);
    let key = solver.declare_const("__trust_u_k#s1_0_s2_0", Sort::Int);
    let zero = solver.int_const(0);
    let seven = solver.int_const(7);
    let eight = solver.int_const(8);
    let usize_max = solver.int_const_bigint(&BigInt::from(u64::MAX));

    let mut conjuncts = Vec::new();
    conjuncts.push(solver.le(zero, index));
    conjuncts.push(solver.le(index, usize_max));
    conjuncts.push(solver.eq(slot, key));
    let then_branch = solver.eq(index, key);
    let else_branch = solver.eq(key, seven);
    conjuncts.push(solver.ite(flag, then_branch, else_branch));
    let in_range = solver.lt(index, eight);
    conjuncts.push(solver.eq(flag, in_range));
    let obligation = solver.and_many(&conjuncts);
    solver.assert_term(obligation);

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat(),
        "without the bound disjunction the obligation is satisfiable, got {:?}",
        details.result.result()
    );
}

// ---- NEGATIVE CONTROLS ----
//
// The seeding lanes are only sound because the STRICT CHECKER re-derives every
// step they emit — the candidate replaces the trust proof solely on
// `check_proof_strict(...).is_complete()`. These pin that the checking is real:
// each takes the accepted proof, corrupts exactly one of the new lanes' steps
// into a shape the rule does NOT license, and requires rejection. Stub either
// validator to `Ok(())` and these fail while everything above still passes.

/// `equiv_pos1` and `equiv_pos2` differ only in operand POLARITY. Relabelling
/// the emitted `equiv_pos2` — clause `(cl (not (= a b)) (not a) b)` — as
/// `equiv_pos1`, whose licensed clause is `(cl (not (= a b)) a (not b))`,
/// must be rejected: otherwise the iff lane could seed `b → a` while claiming
/// `a → b`, and a refutation resting on the wrong direction would certify.
#[test]
fn test_equiv_pos_polarity_swap_is_rejected() {
    let (proof, terms) = certified_panic_freedom_proof();
    let mut forged = proof.clone();
    let mut swapped = 0usize;
    for step in &mut forged.steps {
        if let ProofStep::Step { rule, .. } = step {
            match rule {
                AletheRule::EquivPos2 => {
                    *rule = AletheRule::EquivPos1;
                    swapped += 1;
                }
                AletheRule::EquivPos1 => {
                    *rule = AletheRule::EquivPos2;
                    swapped += 1;
                }
                _ => {}
            }
        }
    }
    assert!(
        swapped > 0,
        "the accepted proof must contain an equiv_pos step to corrupt"
    );
    let verdict = ay_proof::check_proof_strict(&forged, &terms);
    assert!(
        verdict.is_err(),
        "a polarity-swapped equiv_pos step must be REJECTED, got {verdict:?}"
    );
}

/// `and_pos` is POSITIONAL: `(cl (not (and t₀ t₁)) t₁)` is licensed at index 1
/// and at no other index. Re-indexing the disjunct-weakening step must be
/// rejected: otherwise the distribution lane could weaken `(and p q)` to `p`
/// while claiming `q`, seeding a clause the disjunction does not entail.
#[test]
fn test_and_pos_position_forgery_is_rejected() {
    let (proof, terms) = certified_panic_freedom_proof();
    let mut forged = proof.clone();
    let mut reindexed = 0usize;
    for step in &mut forged.steps {
        let ProofStep::Step {
            rule: rule @ AletheRule::AndPos(_),
            args,
            ..
        } = step
        else {
            continue;
        };
        // Only the conjunctive DISJUNCTS — the steps the distribution lane
        // adds — so this control cannot pass on the pre-existing root
        // flattening alone.
        if !args
            .first()
            .is_some_and(|&term| is_binary_conjunction(&terms, term))
        {
            continue;
        }
        let AletheRule::AndPos(position) = rule else {
            continue;
        };
        *position = 1 - *position;
        reindexed += 1;
    }
    assert!(
        reindexed > 0,
        "the accepted proof must contain a disjunct-weakening and_pos to corrupt"
    );
    let verdict = ay_proof::check_proof_strict(&forged, &terms);
    assert!(
        verdict.is_err(),
        "a re-indexed and_pos step must be REJECTED, got {verdict:?}"
    );
}

/// The clausification of the conjunctive disjunction is itself checked: an `or`
/// step whose clause is not the disjunction's decomposition must be rejected,
/// so the lane cannot introduce a literal the `or` does not carry.
#[test]
fn test_or_clausification_forgery_is_rejected() {
    let (proof, terms) = certified_panic_freedom_proof();
    let mut forged = proof.clone();
    let mut truncated = 0usize;
    for step in &mut forged.steps {
        if let ProofStep::Step {
            rule: AletheRule::Or,
            clause,
            ..
        } = step
        {
            if clause.len() > 1 {
                clause.truncate(1);
                truncated += 1;
            }
        }
    }
    assert!(
        truncated > 0,
        "the accepted proof must contain a multi-literal or step to corrupt"
    );
    let verdict = ay_proof::check_proof_strict(&forged, &terms);
    assert!(
        verdict.is_err(),
        "an or step that drops a disjunct must be REJECTED, got {verdict:?}"
    );
}
