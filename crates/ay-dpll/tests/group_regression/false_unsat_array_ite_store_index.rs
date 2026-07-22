// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness regression: wrong UNSAT on a satisfiable array formula whose
//! store index is a term-level ITE (`(store A0 (ite c -2 2) v)`).
//!
//! Root cause (LRA/LIA): `parse_linear_expr` substituted the ITE branch
//! selected by the condition's CURRENT Boolean assignment. Conflicts derived
//! from the substituted parse did not carry the condition literal as a
//! premise. Concretely, with the shared store-index term `k = (ite c -2 2)`
//! and `c` assigned false, the branch-and-bound split atom `(<= k 1)` parsed
//! as `2 <= 1` and produced the length-1 theory conflict `{(<= k 1)}`,
//! learned as the unit clause `k > 1` — FALSE for `c = true` (k = -2).
//! Together with sibling condition-blind conflicts this made the Boolean
//! skeleton unsatisfiable, and the fail-open "#8595 use conflict anyway"
//! arms in the lazy split loop laundered the unverifiable conflicts into
//! learned clauses.
//!
//! Fix: term-level arithmetic ITEs are parsed as opaque variables and their
//! branch semantics are provided by SAT-level link lemmas
//! `cond => (= ite then)` / `(not cond) => (= ite else)` requested via
//! `NeedModelEqualities { implied: true }`, so every explanation carries the
//! condition literal. The lazy split loop's unverifiable-conflict arms are
//! now fail-closed (Unknown instead of learning an unverified clause).
//!
//! Z3 4.15.4 confirms `sat`; the model AY produces after the fix was pinned
//! back into the formula and confirmed `sat` by Z3.

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

/// Fuzzer-found formula (arrays fragment): AY at build 1791 answered `unsat`,
/// Z3 answers `sat` (e.g. A1 = const -1, i2 = -1, i3 = -4 satisfies the
/// second disjunct `select(store(A1, i1, -4*i2), 7) != 4*i3`).
const ARRAY_ITE_STORE_INDEX_SAT: &str = r#"
(set-logic ALL)
(declare-const A0 (Array Int Int))
(declare-const A1 (Array Int Int))
(declare-const i0 Int)
(declare-const i1 Int)
(declare-const i2 Int)
(declare-const i3 Int)
(declare-const b0 Bool)
(assert (or
  (and
    (not (= (select (store A0 (ite (= (+ i3 1) (+ (- 5) i2)) (- 2) 2) (+ i1 (- 6))) (* 3 i3))
            (select A0 i3)))
    (xor (< i1 0)
         (< (select (store A0 (+ i0 (- 1)) (+ i0 4)) (+ i1 (ite (= i1 (- 6)) 5 i1)))
            (select (store A0 (- i1) (- 2)) 1))))
  (not (= (select (store A1 i1 (* i2 (- 4))) 7) (* 4 i3)))))
(check-sat)
"#;

#[test]
#[timeout(60_000)]
fn test_array_ite_store_index_must_be_sat() {
    let commands = parse(ARRAY_ITE_STORE_INDEX_SAT).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["sat"],
        "Array formula with ITE store index is SAT (Z3-confirmed) but AY \
         returned {outputs:?}. Bug: LRA parse-time ITE branch substitution \
         produced condition-blind conflicts (false unit clauses)."
    );
}

/// Direct LIA-level regression for the condition-blind conflict: a bound atom
/// over an ITE-valued shared term must not be refuted without the condition
/// literal as premise. `(<= k 1)` with `k = (ite c -2 2)` is satisfiable
/// (c = true gives k = -2). The old parse-time substitution under `c = false`
/// produced the false unit clause `k > 1`, which then contradicted the
/// `c = true` branch and yielded a wrong UNSAT.
const ITE_BOUND_ATOM_SAT: &str = r#"
(set-logic QF_UFLIA)
(declare-const c Bool)
(declare-const x Int)
(declare-fun f (Int) Int)
(assert (= x (f 0)))
(assert (<= (ite c (- 2) 2) 1))
(assert (=> c (= x 5)))
(check-sat)
"#;

#[test]
#[timeout(60_000)]
fn test_ite_bound_atom_must_be_sat() {
    let commands = parse(ITE_BOUND_ATOM_SAT).unwrap();
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).unwrap();
    assert_eq!(
        outputs,
        vec!["sat"],
        "Bound atom over a term-level ITE is SAT (c = true) but AY returned \
         {outputs:?}."
    );
}
