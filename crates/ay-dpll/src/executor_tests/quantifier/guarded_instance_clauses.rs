// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural specs for guarded instance clauses
//! (#quantifier-guarded-instances).
//!
//! The verdict-level spec lives in
//! `crates/ay-dpll/tests/group_quantifiers/guarded_disjunct_instantiation.rs`.
//! What is checked HERE is the shape of what reaches the solver, because two
//! of the three soundness properties are invisible from a verdict:
//!
//! 1. the clause is `(or (not qproxy) instance)` — a two-literal disjunction
//!    whose first literal is the negation of a proxy the abstraction minted,
//!    never a bare instance;
//! 2. the clause is never threaded as a conflict-verification SUPPORT AXIOM,
//!    whose contract is "true in every model of the CURRENT problem" and whose
//!    consumers (`instance_closure_ground_unsat`) trust it outright; and
//! 3. the clause is never an authored PROBLEM ASSERTION, so a proof exporter
//!    cannot label it `h{idx}` and claim it as an input. A guarded clause is a
//!    consequence of the abstraction, whose proxy is not authored vocabulary;
//!    a labelled assumption would be a document asserting an inference AY
//!    never made. Its checked derivation is built from the authored side
//!    instead — the clause's resolvent on the proxy, by `forall_inst` from the
//!    authored clause carrying the universal
//!    (`authored_consequence_replay/guarded_clausal.rs`).

use super::*;
use ay_core::term::{Symbol, TermData, TermId};

/// The stage's canonical shape: a universal reachable only under a positive
/// `or`, with the sibling disjunct forced false through a two-step chain the
/// unit-fact refinement cannot see through, so the universal is NOT entailed
/// and is therefore a proxy target.
const DISJUNCT_POSITION_FORALL: &str = r#"
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const c Bool)
    (declare-const d Bool)
    (assert (or c (forall ((x Int)) (> (f x) 0))))
    (assert (or (not c) d))
    (assert (not d))
    (assert (< (f 1) 0))
    (check-sat)
"#;

fn solved(input: &str) -> Executor {
    let commands = parse(input).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let _ = exec.execute_all(&commands).expect("execution succeeds");
    exec
}

/// The lane fires at all on the shape it exists for, and every clause it
/// asserted has the guarded two-literal shape with a minted proxy under the
/// negation. Without this the two negative specs below would pass vacuously.
#[test]
fn a_guarded_clause_is_a_proxy_guarded_two_literal_disjunction() {
    let exec = solved(DISJUNCT_POSITION_FORALL);
    assert!(
        !exec.guarded_instance_clauses.is_empty(),
        "the disjunct-position universal must produce at least one guarded \
         clause; the negative specs below are vacuous without it"
    );
    let proxies: Vec<TermId> = exec.quantifier_proxies.values().copied().collect();
    for &clause in &exec.guarded_instance_clauses {
        let TermData::App(Symbol::Named(name), args) = exec.ctx.terms.get(clause).clone() else {
            panic!("a guarded clause must be an application, got {clause:?}");
        };
        assert_eq!(name, "or", "a guarded clause must be a disjunction");
        assert_eq!(
            args.len(),
            2,
            "a guarded clause is exactly `(or (not qproxy) instance)`"
        );
        let TermData::Not(guard) = exec.ctx.terms.get(args[0]).clone() else {
            panic!("the first literal must be the NEGATION of the proxy");
        };
        assert!(
            proxies.contains(&guard),
            "the guard must be a proxy this solve's abstraction minted, so the \
             clause is discharged exactly when the abstracted universal is \
             asserted true"
        );
        assert!(
            !crate::ematching::contains_quantifier(&exec.ctx.terms, args[1]),
            "the instance must be ground: `flatten_and_strip_quantifiers` has \
             already run, so a quantified clause pushed here would reach the \
             ground solve unstripped"
        );
    }
}

/// A guarded clause must never be threaded as a support axiom. The support
/// set's contract is universal instantiation of an UNCONDITIONALLY asserted
/// forall — every member is true in every model of the problem — and
/// `instance_closure_ground_unsat` re-solves against it and trusts the result.
/// A guarded clause is true in every model of the ABSTRACTION, which is a
/// different claim, so it must not travel there.
#[test]
fn a_guarded_clause_is_never_a_support_axiom() {
    let exec = solved(DISJUNCT_POSITION_FORALL);
    for support in &exec.active_support_axioms {
        assert!(
            !exec.guarded_instance_clauses.contains(&support.term),
            "a guarded instance clause reached `active_support_axioms`; its \
             consumers treat that set as unconditionally entailed"
        );
    }
}

/// A guarded clause must never be an authored problem assertion. The proof
/// exporter labels an assertion `h{idx}` exactly when it is in
/// `proof_problem_assertions()` — the set frozen by
/// `install_proof_source_provenance` before any preprocessing — and demotes
/// everything else. Claiming a guarded clause as an input would be a proof
/// asserting something the query never said.
#[test]
fn a_guarded_clause_is_never_an_authored_problem_assertion() {
    let mut exec = solved(DISJUNCT_POSITION_FORALL);
    let authored = exec.proof_problem_assertions();
    let original = exec.proof_original_problem_assertions();
    for &clause in &exec.guarded_instance_clauses {
        assert!(
            !authored.contains(&clause),
            "a guarded instance clause entered the authored problem-assertion \
             set; the exporter would label it `h{{idx}}` and the document would \
             claim it as an input"
        );
        assert!(
            !original.contains(&clause),
            "a guarded instance clause entered the immutable authored snapshot"
        );
    }
}

/// Per-check-sat lifecycle: the record is cleared at the top of
/// `process_quantifiers`, so a clause minted for an earlier query can never be
/// read back by a later one, and a quantifier-free query leaves it empty.
#[test]
fn guarded_clause_records_are_per_check_sat() {
    let input = r#"
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const c Bool)
        (declare-const d Bool)
        (push 1)
        (assert (or c (forall ((x Int)) (> (f x) 0))))
        (assert (or (not c) d))
        (assert (not d))
        (assert (< (f 1) 0))
        (check-sat)
        (pop 1)
        (assert (< (f 1) 0))
        (check-sat)
    "#;
    let exec = solved(input);
    assert!(
        exec.guarded_instance_clauses.is_empty(),
        "the second, quantifier-free check-sat must leave the record empty; a \
         stale clause from the popped scope would be read back by every \
         downstream consumer"
    );
}

/// (#guarded-nested-quantifiers) A universal under a disjunct whose instance
/// holds another universal: the instance is no longer dropped. Its clause is
/// guarded by the outer proxy, carries the inner universal's own proxy in
/// place of the quantifier, and the inner universal's instances are guarded
/// by that proxy in turn.
const NESTED_UNDER_DISJUNCT: &str = r#"
    (set-logic UFLIA)
    (declare-fun P (Int) Bool)
    (declare-fun R (Int Int) Bool)
    (declare-const c Bool)
    (declare-const d Bool)
    (assert (or c (forall ((x Int)) (! (=> (P x) (forall ((z Int)) (! (R x z) :pattern ((R x z))))) :pattern ((P x))))))
    (assert (or (not c) d))
    (assert (not d))
    (assert (P 7))
    (assert (not (R 7 20)))
    (check-sat)
"#;

#[test]
fn a_nested_universal_gets_a_proxy_and_guarded_instances_of_its_own() {
    let exec = solved(NESTED_UNDER_DISJUNCT);
    let proxies: Vec<TermId> = exec.quantifier_proxies.values().copied().collect();
    assert!(
        proxies.len() >= 2,
        "the inner universal must get a proxy of its own; proxies: {proxies:?}"
    );
    let guards: Vec<TermId> = exec
        .guarded_instance_clauses
        .iter()
        .filter_map(|&clause| match exec.ctx.terms.get(clause) {
            TermData::App(_, args) => match exec.ctx.terms.get(args[0]) {
                TermData::Not(guard) => Some(*guard),
                _ => None,
            },
            _ => None,
        })
        .collect();
    assert!(
        guards.len() >= 2 && guards.iter().any(|g| guards.iter().any(|h| h != g)),
        "both the outer and the inner proxy must guard clauses; guards: {guards:?}"
    );
    for &clause in &exec.guarded_instance_clauses {
        assert!(
            !crate::ematching::contains_quantifier(&exec.ctx.terms, clause),
            "a guarded clause reached the ground solve with a quantifier in it"
        );
    }
}
