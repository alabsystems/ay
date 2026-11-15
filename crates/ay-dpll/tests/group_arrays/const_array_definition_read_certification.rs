// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Mandatory certification of a refutation that preprocessing folds through a
//! constant-array read.
//!
//! A conjunct pins `z` to `((as const (Array (_ BitVec 4) (_ BitVec 3))) (g x))`.
//! The early ABV preprocessing loop substitutes it into
//! `(not (= (select z #x9) (g x)))`, and `TermStore::mk_select` folds the read
//! of the constant array to `(g x)`, so the assertion collapses to `false`. The
//! propagation replay had a ROW1 leg for a substituted `store` but none for a
//! substituted constant array, so the collapse stayed a premiseless
//! `trust (cl false)` and an explicit proof request answered `unknown`
//! (`step t0 uses unverified trust rule`) although the query is unsat (z3 5.1.0
//! agrees). The replay now closes the read with the checker's existing
//! `ArrayRowChain` sub-schema (E) lemma
//! `(cl (not (= z K)) (= (select z i) (g x)))`.
//!
//! The leg replays a fold the propagation records name. The definition as its
//! OWN root is not covered yet: no propagation record names the fold of the
//! read there, so no lane has a rewrite to plan (see
//! [`a_standalone_definition_read_fold_never_publishes_an_unchecked_unsat`]).

use ay_core::{ProofStep, TermData, TheoryLemmaKind};
use ay_dpll::Executor;
use ay_frontend::parse;

const PREAMBLE: &str = r#"
    (set-logic QF_AUFBV)
    (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
    (declare-const x (_ BitVec 4))
    (declare-const y (_ BitVec 4))
    (declare-fun g ((_ BitVec 4)) (_ BitVec 3))
    (assert (and (bvult x #x3) (= z ((as const (Array (_ BitVec 4) (_ BitVec 3))) (g x)))))
"#;

/// The repro (`r_uf_default_unsat`): a read at a literal index.
const LITERAL_INDEX_READ: &str = "(assert (not (= (select z #x9) (g x))))\n";

/// The same fold at a symbolic index: schema (E) admits any well-sorted index.
const SYMBOLIC_INDEX_READ: &str = "(assert (not (= (select z y) (g x))))\n";

/// Negative twin: the read's value is a DIFFERENT application of `g`, so the
/// constant-array fold does not refute it and the query is satisfiable.
const DIFFERENT_FILL_READ: &str = "(assert (not (= (select z #x9) (g y))))\n";

fn solve(read: &str) -> (Executor, Vec<String>) {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let script = format!("{PREAMBLE}{read}(check-sat)\n");
    let outputs = executor.execute_all(&parse(&script).unwrap()).unwrap();
    (executor, outputs)
}

/// Solve under an explicit proof request, check the retained refutation
/// strictly, and return the published `(get-proof)` document.
fn certified_document(read: &str) -> String {
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let script = format!("{PREAMBLE}{read}(check-sat)\n(get-proof)\n");
    let outputs = executor.execute_all(&parse(&script).unwrap()).unwrap();
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("unsat"),
        "the query is unsat (z3 5.1.0) and the refutation must survive mandatory \
         certification: {outputs:?}"
    );
    let proof = executor
        .last_proof()
        .expect("a certified UNSAT keeps its proof");
    let terms = executor.terms();
    // The (E) lemma: a negated array equality with a constant-array side.
    let const_read_lemma = proof.steps.iter().any(|step| match step {
        ProofStep::TheoryLemma {
            kind: TheoryLemmaKind::ArrayRowChain,
            clause,
            ..
        } => clause.iter().any(|&literal| match terms.get(literal) {
            TermData::Not(inner) => matches!(terms.get(*inner),
                TermData::App(symbol, sides) if symbol.name() == "="
                    && sides.iter().any(|&side| terms.get_const_array(side).is_some())),
            _ => false,
        }),
        _ => false,
    });
    assert!(
        const_read_lemma,
        "the folded read must be closed by the ArrayRowChain (E) lemma"
    );
    assert!(
        !proof.steps.iter().any(|step| matches!(
            step,
            ProofStep::TheoryLemma {
                kind: TheoryLemmaKind::Generic,
                ..
            }
        )),
        "no Generic lemma may remain in the certified refutation"
    );
    ay_proof::check_proof_strict(proof, terms)
        .expect("the plain strict checker must accept the refutation");
    let document = outputs.get(1).expect("published proof").clone();
    assert!(!document.contains(":rule trust"), "{document}");
    document
}

/// Before the fix: `unknown`, `step t0 uses unverified trust rule`.
#[test]
fn folded_const_array_read_is_strictly_certified() {
    certified_document(LITERAL_INDEX_READ);
}

#[test]
fn folded_const_array_read_at_a_symbolic_index_is_strictly_certified() {
    certified_document(SYMBOLIC_INDEX_READ);
}

#[test]
fn const_array_read_of_a_different_value_stays_sat() {
    let (_, outputs) = solve(DIFFERENT_FILL_READ);
    assert_eq!(
        outputs.first().map(String::as_str),
        Some("sat"),
        "(g y) is unconstrained, so the read can differ: {outputs:?}"
    );
}

/// KNOWN GAP, pinned as a contract rather than as the gap. With the
/// definition as its own root, `(assert (= z K))`, QF_AUFBV preprocessing
/// folds the read assertion to `false` as well, but no propagation record
/// names that fold (one entry and one rewrite are recorded, neither of them
/// the read assertion's), so no replay lane has a rewrite to plan and the fold
/// stays a premiseless `trust (cl false)`: an explicit proof request answers
/// `unknown` (`step t1 uses unverified trust rule`, a628c3b2a, with and
/// without the leg). Whatever a later producer record changes, the answer is
/// never `sat`, and an `unsat` keeps only a refutation the strict checker
/// accepts.
#[test]
fn a_standalone_definition_read_fold_never_publishes_an_unchecked_unsat() {
    let script = r#"
        (set-logic QF_AUFBV)
        (declare-const z (Array (_ BitVec 4) (_ BitVec 3)))
        (declare-const x (_ BitVec 4))
        (declare-fun g ((_ BitVec 4)) (_ BitVec 3))
        (assert (= z ((as const (Array (_ BitVec 4) (_ BitVec 3))) (g x))))
        (assert (not (= (select z #x9) (g x))))
        (check-sat)
    "#;
    let mut executor = Executor::new();
    executor.set_produce_proofs(true);
    let outputs = executor.execute_all(&parse(script).unwrap()).unwrap();
    match outputs.first().map(String::as_str) {
        Some("unknown") => assert!(executor.last_proof().is_none(), "{outputs:?}"),
        Some("unsat") => {
            let proof = executor
                .last_proof()
                .expect("a certified UNSAT keeps its proof");
            ay_proof::check_proof_strict(proof, executor.terms())
                .expect("an unsat must keep a strictly checked refutation");
        }
        _ => panic!("the query is unsat (z3 5.1.0): {outputs:?}"),
    }
}
