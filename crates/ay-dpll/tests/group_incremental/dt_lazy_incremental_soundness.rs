// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Regression tests for the lazy DT lane's incremental gate
//! (#dt-lazy-incremental-gate; mv-rerun-20260718 follow-up merge blocker).
//!
//! The lane's fallback isolation (#dt-lazy-isolation) rolls the term store
//! back via `TermStore::rollback_to`, whose contract — no rolled-back TermId
//! survives anywhere — is unenforceable under an incremental session: the
//! persistent `IncrementalTheoryState` (encoded_assertions keyed by TermId,
//! tseitin `term_to_var`, activation scopes, theory atoms, recorded lemmas)
//! outlives the lane, and the inner solve itself routes to the PERSISTENT
//! pipeline when incremental. After a rollback, later terms recycle the
//! freed TermIds and the stale encodings alias them to unrelated SAT
//! literals — false conflicts, observed as a WRONG `unsat` on a
//! push/pop-wrapped SATISFIABLE QF_DT query (a Barrett `typed_v1l20042`
//! fragment). The fix gates the whole lane off when `incremental_mode` is
//! set or the persistent theory state carries content; the base line
//! answered a sound `unknown` on this route, so nothing that worked is
//! lost. These tests pin the SOUND answers: the satisfiable queries must
//! never come back `unsat` (either `sat` or a fail-closed `unknown` is
//! acceptable; `unsat` is a soundness bug), while the genuinely
//! unsatisfiable middle query must stay `unsat`.

use crate::common::solve_vec;
use ntest::timeout;

const PREAMBLE: &str = r#"
(set-option :produce-models true)
(set-logic QF_DT)
(declare-datatypes ((nat 0)(list 0)(tree 0)) (((succ (pred nat)) (zero))
((cons (car tree) (cdr list)) (null))
((node (children list)) (leaf (data nat)))
))
(declare-fun x1 () nat)
(declare-fun x2 () list)
(declare-fun x3 () tree)
"#;

/// A deep mutually-recursive Barrett-shaped assertion that is SATISFIABLE
/// (a fragment of QF_DT typed_v1l20042, which the full battery answers
/// sat + Dolmen-valid in single-shot mode).
const SAT_BARRETT_FRAGMENT: &str = r#"
(assert (and (not (= (cons (leaf (ite ((_ is leaf) (node (ite ((_ is node) (leaf zero)) (children (leaf zero)) null))) (data (node (ite ((_ is node) (leaf zero)) (children (leaf zero)) null))) zero)) (ite ((_ is node) (node (cons (node (ite ((_ is node) (leaf (ite ((_ is succ) x1) (pred x1) zero))) (children (leaf (ite ((_ is succ) x1) (pred x1) zero))) null)) (ite ((_ is cons) (ite ((_ is cons) x2) (cdr x2) null)) (cdr (ite ((_ is cons) x2) (cdr x2) null)) null)))) (children (node (cons (node (ite ((_ is node) (leaf (ite ((_ is succ) x1) (pred x1) zero))) (children (leaf (ite ((_ is succ) x1) (pred x1) zero))) null)) (ite ((_ is cons) (ite ((_ is cons) x2) (cdr x2) null)) (cdr (ite ((_ is cons) x2) (cdr x2) null)) null)))) null)) (cons (leaf zero) (ite ((_ is cons) (ite ((_ is node) (ite ((_ is cons) x2) (car x2) (leaf zero))) (children (ite ((_ is cons) x2) (car x2) (leaf zero))) null)) (cdr (ite ((_ is node) (ite ((_ is cons) x2) (car x2) (leaf zero))) (children (ite ((_ is cons) x2) (car x2) (leaf zero))) null)) null)))) (= (ite ((_ is cons) x2) (car x2) (leaf zero)) (leaf x1))))
"#;

/// Extract the check-sat verdict lines, in order.
fn verdicts(lines: &[String]) -> Vec<String> {
    lines
        .iter()
        .map(|l| l.trim())
        .filter(|l| matches!(*l, "sat" | "unsat" | "unknown"))
        .map(str::to_owned)
        .collect()
}

/// A single push/pop-wrapped SATISFIABLE query. The regression answered
/// `unsat` (wrong): the lazy DT lane's fallback rollback recycled TermIds
/// that the persistent incremental pipeline still mapped to stale SAT
/// literals. Sound answers are `sat` or `unknown` — never `unsat`.
#[test]
#[timeout(120000)]
fn push_pop_wrapped_sat_barrett_query_is_never_unsat() {
    let smt = format!("{PREAMBLE}(push 1){SAT_BARRETT_FRAGMENT}(check-sat)\n(pop 1)");
    let out = solve_vec(&smt);
    let v = verdicts(&out);
    assert_eq!(v.len(), 1, "expected one verdict, got {v:?}");
    assert_ne!(
        v[0], "unsat",
        "WRONG UNSAT on a push/pop-wrapped satisfiable QF_DT query \
         (#dt-lazy-incremental-gate regression)"
    );
}

/// Three sequential push/pop queries with true answers sat / unsat / sat.
/// The regression answered unsat / unsat / unsat. Queries 1 and 3 must
/// never be `unsat` (sat or fail-closed unknown are both sound); query 2
/// (`x1 = succ x1`, an occurs-check cycle) must stay `unsat`.
#[test]
#[timeout(120000)]
fn three_query_session_stays_sound_after_lazy_lane_gate() {
    let smt = format!(
        "{PREAMBLE}\
         (push 1){SAT_BARRETT_FRAGMENT}(check-sat)\n(pop 1)\n\
         (push 1)\n(assert (= x1 (succ x1)))\n(check-sat)\n(pop 1)\n\
         (push 1)\n(assert ((_ is succ) x1))\n(assert (= (pred x1) zero))\n\
         (check-sat)\n(pop 1)"
    );
    let out = solve_vec(&smt);
    let v = verdicts(&out);
    assert_eq!(v.len(), 3, "expected three verdicts, got {v:?}");
    assert_ne!(
        v[0], "unsat",
        "query 1 is satisfiable; unsat is a soundness bug: {v:?}"
    );
    assert_eq!(
        v[1], "unsat",
        "query 2 (x1 = succ x1) is an occurs-check contradiction: {v:?}"
    );
    assert_ne!(
        v[2], "unsat",
        "query 3 is satisfiable; unsat is a soundness bug: {v:?}"
    );
}
