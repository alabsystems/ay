// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Named unsat-core pigeonhole fast-path tests (#uc-qfdt): under
//! `produce-unsat-cores` with every assert named (the SMT-COMP Unsat-Core
//! track shape), a finite-enum disequality clique of size `> k` must answer
//! `unsat` via the pigeonhole fast path and emit EXACTLY the clique-edge
//! assertions plus the clique members' membership (domain-narrowing)
//! assertions as the core — and must NEVER fire on sat / recursive-datatype
//! inputs.

use super::*;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap()
}

/// Parse the `(get-unsat-core)` output `(n1 n2 ...)` into a set of names.
fn core_names(output: &str) -> Vec<String> {
    output
        .trim()
        .trim_start_matches('(')
        .trim_end_matches(')')
        .split_whitespace()
        .map(str::to_string)
        .collect()
}

/// Named Bouvier-shaped synthetic: 3-ctor enum, 5 vars, K4 clique among
/// v1..v4 (4 > k = 3 → pigeonhole UNSAT), plus an irrelevant edge (v1,v5).
/// The core must be exactly the 6 clique-edge asserts + the sort's
/// membership asserts (the validator-friendly domain chains) — the
/// irrelevant clique-external edge stays out.
#[test]
fn test_named_pigeonhole_core_fires_exact_core() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_DT)
        (declare-datatype E ((e0) (e1) (e2)))
        (declare-const v1 E)
        (declare-const v2 E)
        (declare-const v3 E)
        (declare-const v4 E)
        (declare-const v5 E)
        (assert (! (= v1 e0) :named mem1))
        (assert (! (or (= v2 e0) (= v2 e1)) :named mem2))
        (assert (! (or (= v3 e0) (= v3 e1) (= v3 e2)) :named mem3))
        (assert (! (or (= v4 e0) (= v4 e1) (= v4 e2)) :named mem4))
        (assert (! (or (= v5 e0) (= v5 e1) (= v5 e2)) :named mem5))
        (assert (! (distinct v1 v2) :named edge12))
        (assert (! (distinct v1 v3) :named edge13))
        (assert (! (distinct v1 v4) :named edge14))
        (assert (! (distinct v2 v3) :named edge23))
        (assert (! (distinct v2 v4) :named edge24))
        (assert (! (distinct v3 v4) :named edge34))
        (assert (! (distinct v1 v5) :named extra15))
        (check-sat)
        (get-unsat-core)
    "#;
    let outputs = run(input);
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    let mut names = core_names(&outputs[1]);
    names.sort();
    let mut expected: Vec<String> = [
        "edge12", "edge13", "edge14", "edge23", "edge24", "edge34", // clique edges
        "mem1", "mem2", "mem3", "mem4", "mem5", // the sort's membership chains
    ]
    .iter()
    .map(|s| s.to_string())
    .collect();
    expected.sort();
    assert_eq!(
        names, expected,
        "core must be exactly the clique edges + clique membership: {}",
        outputs[1]
    );
}

/// SOUNDNESS: the emitted core must re-check UNSAT in isolation (the
/// competition validation semantics: keep only core-named asserts).
#[test]
fn test_named_pigeonhole_core_revalidates_unsat() {
    let core_only = r#"
        (set-logic QF_DT)
        (declare-datatype E ((e0) (e1) (e2)))
        (declare-const v1 E)
        (declare-const v2 E)
        (declare-const v3 E)
        (declare-const v4 E)
        (assert (= v1 e0))
        (assert (or (= v2 e0) (= v2 e1)))
        (assert (or (= v3 e0) (= v3 e1) (= v3 e2)))
        (assert (or (= v4 e0) (= v4 e1) (= v4 e2)))
        (assert (distinct v1 v2))
        (assert (distinct v1 v3))
        (assert (distinct v1 v4))
        (assert (distinct v2 v3))
        (assert (distinct v2 v4))
        (assert (distinct v3 v4))
        (check-sat)
    "#;
    let outputs = run(core_only);
    assert_eq!(
        outputs,
        vec!["unsat"],
        "the pigeonhole core re-asserted in isolation must be UNSAT"
    );
}

/// NON-FIRING (sat): a K3 clique over a 3-ctor enum is satisfiable — the
/// fast path must not fire and the named-mode answer must not be a
/// wrong-unsat. (With the QfDt unknown-retry, the scoped fallback answers
/// `sat`.)
#[test]
fn test_named_mode_sat_instance_not_wrong_unsat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_DT)
        (declare-datatype E ((e0) (e1) (e2)))
        (declare-const v1 E)
        (declare-const v2 E)
        (declare-const v3 E)
        (assert (! (or (= v1 e0) (= v1 e1) (= v1 e2)) :named mem1))
        (assert (! (distinct v1 v2) :named edge12))
        (assert (! (distinct v1 v3) :named edge13))
        (assert (! (distinct v2 v3) :named edge23))
        (check-sat)
    "#;
    let outputs = run(input);
    assert_eq!(outputs.len(), 1);
    assert_eq!(
        outputs[0], "sat",
        "K3 over a 3-inhabitant enum is SAT; named mode must answer it"
    );
}

/// NON-FIRING (recursive datatype): a recursive List datatype is INFINITE —
/// no cardinality, no pigeonhole. Distinct list constants are satisfiable;
/// the fast path must never manufacture an unsat here.
#[test]
fn test_named_mode_recursive_dt_not_wrong_unsat() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_DT)
        (declare-datatypes ((Lst 0)) (((nil) (cons (head Bool) (tail Lst)))))
        (declare-const l1 Lst)
        (declare-const l2 Lst)
        (declare-const l3 Lst)
        (assert (! (distinct l1 l2) :named e12))
        (assert (! (distinct l1 l3) :named e13))
        (assert (! (distinct l2 l3) :named e23))
        (check-sat)
    "#;
    let outputs = run(input);
    assert_eq!(outputs.len(), 1);
    assert_ne!(
        outputs[0], "unsat",
        "3 distinct constants of an infinite recursive datatype are SAT; \
         any unsat here is a soundness bug"
    );
}

/// FALLBACK (no clique): a named QF_DT contradiction that is NOT a
/// pigeonhole (x = e0 and x = e1) must still be answered through the
/// generic redirect with a genuinely-unsat core.
#[test]
fn test_named_mode_non_pigeonhole_unsat_still_answered() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_DT)
        (declare-datatype E ((e0) (e1) (e2)))
        (declare-const x E)
        (assert (! (= x e0) :named n1))
        (assert (! (= x e1) :named n2))
        (check-sat)
        (get-unsat-core)
    "#;
    let outputs = run(input);
    assert_eq!(outputs.len(), 2);
    assert_eq!(outputs[0], "unsat");
    assert!(
        outputs[1].contains("n1") && outputs[1].contains("n2"),
        "core must contain both contradicting assertions: {}",
        outputs[1]
    );
}
