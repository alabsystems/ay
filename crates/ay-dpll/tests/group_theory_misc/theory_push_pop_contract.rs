// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

#![allow(clippy::panic)]

//! Push/pop contract conformance tests for ALL theory solvers.
//!
//! Contract under test (see `TheorySolver::push` doc in `ay-core/src/theory.rs`):
//!
//! > After `push(); <mutations>; pop();`, the solver MUST produce the same
//! > `check()` and `propagate()` results as if the mutations never happened.
//!
//! Every theory solver (EUF, LRA, LIA, BV, Arrays, DT, Strings, NIA) has a
//! corresponding test that exercises:
//!   1. Base assertions -> check-sat (SAT)
//!   2. push -> contradicting assertions -> check-sat (UNSAT)
//!   3. pop -> check-sat (SAT again, proving the scoped assertions were undone)
//!   4. Optionally: post-pop assertions that would conflict with popped state
//!      but are compatible with the base state (SAT, proving no state leak)
//!
//! Additionally, nested push/pop and repeated check-sat stability tests verify
//! that scope nesting and re-checking are sound.
//!
//! Part of #3664.

use std::fmt::Write as _;

use ay_dpll::Executor;
use ay_frontend::parse;
use ntest::timeout;

struct PushPopContractCase<'a> {
    logic: &'a str,
    declarations: &'a [&'a str],
    base_assertions: &'a [&'a str],
    scoped_assertions: &'a [&'a str],
    post_pop_assertions: &'a [&'a str],
}

fn run_case(case: &PushPopContractCase<'_>) -> Vec<String> {
    run_case_with_post_pop_rechecks(case, 0)
}

fn run_case_with_post_pop_rechecks(
    case: &PushPopContractCase<'_>,
    post_pop_rechecks: usize,
) -> Vec<String> {
    let mut smt = String::new();
    writeln!(&mut smt, "(set-logic {})", case.logic).expect("write logic");
    for declaration in case.declarations {
        writeln!(&mut smt, "{declaration}").expect("write declaration");
    }
    for assertion in case.base_assertions {
        writeln!(&mut smt, "(assert {assertion})").expect("write base assertion");
    }
    writeln!(&mut smt, "(check-sat)").expect("write base check-sat");
    writeln!(&mut smt, "(push 1)").expect("write push");
    for assertion in case.scoped_assertions {
        writeln!(&mut smt, "(assert {assertion})").expect("write scoped assertion");
    }
    writeln!(&mut smt, "(check-sat)").expect("write scoped check-sat");
    writeln!(&mut smt, "(pop 1)").expect("write pop");
    for assertion in case.post_pop_assertions {
        writeln!(&mut smt, "(assert {assertion})").expect("write post-pop assertion");
    }
    writeln!(&mut smt, "(check-sat)").expect("write post-pop check-sat");
    for _ in 0..post_pop_rechecks {
        writeln!(&mut smt, "(check-sat)").expect("write post-pop recheck");
    }

    let commands = parse(&smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT:\n{smt}"));
    let mut exec = Executor::new();
    let output = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT:\n{smt}"))
        .join("\n");
    output
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .map(ToOwned::to_owned)
        .collect()
}

/// Run a raw SMT-LIB script and extract check-sat results.
fn run_smt(smt: &str) -> Vec<String> {
    let commands = parse(smt).unwrap_or_else(|err| panic!("parse failed: {err}\nSMT:\n{smt}"));
    let mut exec = Executor::new();
    let output = exec
        .execute_all(&commands)
        .unwrap_or_else(|err| panic!("execution failed: {err}\nSMT:\n{smt}"))
        .join("\n");
    output
        .lines()
        .map(str::trim)
        .filter(|line| matches!(*line, "sat" | "unsat" | "unknown"))
        .map(ToOwned::to_owned)
        .collect()
}

#[test]
#[timeout(10_000)]
fn contract_lia_scope_restoration() {
    let case = PushPopContractCase {
        logic: "QF_LIA",
        declarations: &["(declare-fun x () Int)", "(declare-fun y () Int)"],
        base_assertions: &["(= (+ x y) 10)"],
        scoped_assertions: &["(>= x 100)", "(>= y 100)"],
        post_pop_assertions: &["(<= x 5)"],
    };

    assert_eq!(run_case(&case), vec!["sat", "unsat", "sat"]);
}

#[test]
#[timeout(10_000)]
fn contract_euf_scope_restoration() {
    let case = PushPopContractCase {
        logic: "QF_UF",
        declarations: &[
            "(declare-sort S 0)",
            "(declare-fun a () S)",
            "(declare-fun b () S)",
        ],
        base_assertions: &["(not (= a b))"],
        scoped_assertions: &["(= a b)"],
        post_pop_assertions: &[],
    };

    assert_eq!(run_case(&case), vec!["sat", "unsat", "sat"]);
}

#[test]
#[timeout(10_000)]
fn contract_euf_post_pop_recheck_is_stable() {
    let case = PushPopContractCase {
        logic: "QF_UF",
        declarations: &[
            "(declare-sort S 0)",
            "(declare-fun a () S)",
            "(declare-fun b () S)",
        ],
        base_assertions: &["(not (= a b))"],
        scoped_assertions: &["(= a b)"],
        post_pop_assertions: &[],
    };

    assert_eq!(
        run_case_with_post_pop_rechecks(&case, 1),
        vec!["sat", "unsat", "sat", "sat"]
    );
}

/// Regression for #3657 root cause class:
/// scoped tester knowledge must not leak after pop.
#[test]
#[timeout(10_000)]
fn contract_dt_tester_state_restoration() {
    let case = PushPopContractCase {
        logic: "QF_DT",
        declarations: &[
            "(declare-datatype Option ((None) (Some (value Int))))",
            "(declare-fun x () Option)",
        ],
        base_assertions: &[],
        scoped_assertions: &["(is-Some x)"],
        post_pop_assertions: &["(= x None)"],
    };

    assert_eq!(run_case(&case), vec!["sat", "sat", "sat"]);
}

#[test]
#[timeout(10_000)]
fn contract_dt_post_pop_recheck_is_stable() {
    let case = PushPopContractCase {
        logic: "QF_DT",
        declarations: &[
            "(declare-datatype Option ((None) (Some (value Int))))",
            "(declare-fun x () Option)",
        ],
        base_assertions: &[],
        scoped_assertions: &["(is-Some x)"],
        post_pop_assertions: &["(= x None)"],
    };

    assert_eq!(
        run_case_with_post_pop_rechecks(&case, 1),
        vec!["sat", "sat", "sat", "sat"]
    );
}

/// NIA is incomplete; "unknown" is acceptable for nonlinear model construction,
/// but sign conflicts must be detected strictly.
/// Part of #3752: tighten scoped sign-conflict assertion.
#[test]
#[timeout(10_000)]
fn contract_nia_scope_restoration() {
    let case = PushPopContractCase {
        logic: "QF_NIA",
        declarations: &["(declare-fun x () Int)", "(declare-fun y () Int)"],
        base_assertions: &["(= x 0)", "(= (* x y) 0)"],
        scoped_assertions: &["(> x 0)", "(> y 0)", "(< (* x y) 0)"],
        post_pop_assertions: &[],
    };
    let results = run_case(&case);

    assert_eq!(
        results.len(),
        3,
        "expected 3 check-sat results: {results:?}"
    );
    // NIA-INCOMPLETE: base scope (x=0, x*y=0) returns unknown; solver cannot
    // evaluate nonlinear product under concrete assignment.
    assert!(
        matches!(results[0].as_str(), "sat" | "unknown"),
        "base scope should be SAT/Unknown, got: {}",
        results[0]
    );
    // STRICT: scoped contradiction is a sign conflict (x>0 ∧ y>0 ∧ x*y<0),
    // detected by the sign lemma.
    assert_eq!(
        results[1].as_str(),
        "unsat",
        "scoped sign conflict must be UNSAT (sign lemma), got: {}",
        results[1]
    );
    // NIA-INCOMPLETE: post-pop scope returns unknown; same as base scope.
    assert!(
        matches!(results[2].as_str(), "sat" | "unknown"),
        "post-pop scope should be SAT/Unknown, got: {}",
        results[2]
    );
}

#[test]
#[timeout(10_000)]
fn contract_nia_post_pop_recheck_avoids_scoped_unsat_leak() {
    let case = PushPopContractCase {
        logic: "QF_NIA",
        declarations: &["(declare-fun x () Int)", "(declare-fun y () Int)"],
        base_assertions: &["(= x 0)", "(= (* x y) 0)"],
        scoped_assertions: &["(> x 0)", "(> y 0)", "(< (* x y) 0)"],
        post_pop_assertions: &[],
    };

    let results = run_case_with_post_pop_rechecks(&case, 1);
    assert_eq!(
        results.len(),
        4,
        "expected 4 check-sat results with one post-pop recheck: {results:?}"
    );
    assert_eq!(
        results[1].as_str(),
        "unsat",
        "scoped sign conflict must be UNSAT (sign lemma), got: {}",
        results[1]
    );
    assert!(
        matches!(results[2].as_str(), "sat" | "unknown"),
        "first post-pop check should be SAT/Unknown, got: {}",
        results[2]
    );
    assert!(
        matches!(results[3].as_str(), "sat" | "unknown"),
        "second post-pop check should be SAT/Unknown, got: {}",
        results[3]
    );
}

// ============================================================================
// LRA (Linear Real Arithmetic) - contract coverage
// ============================================================================

/// LRA scope restoration: scoped bounds must not leak after pop.
#[test]
#[timeout(10_000)]
fn contract_lra_scope_restoration() {
    let case = PushPopContractCase {
        logic: "QF_LRA",
        declarations: &["(declare-fun x () Real)", "(declare-fun y () Real)"],
        // Base: x + y = 10.0
        base_assertions: &["(= (+ x y) 10.0)"],
        // Scoped: x >= 100 AND y >= 100 contradicts x+y=10
        scoped_assertions: &["(>= x 100.0)", "(>= y 100.0)"],
        // Post-pop: x <= 5 is compatible with x+y=10 (e.g., x=5, y=5)
        post_pop_assertions: &["(<= x 5.0)"],
    };

    assert_eq!(run_case(&case), vec!["sat", "unsat", "sat"]);
}

/// LRA post-pop recheck stability: repeated check-sat after pop must be stable.
#[test]
#[timeout(10_000)]
fn contract_lra_post_pop_recheck_is_stable() {
    let case = PushPopContractCase {
        logic: "QF_LRA",
        declarations: &["(declare-fun x () Real)", "(declare-fun y () Real)"],
        base_assertions: &["(= (+ x y) 10.0)"],
        scoped_assertions: &["(>= x 100.0)", "(>= y 100.0)"],
        post_pop_assertions: &[],
    };

    assert_eq!(
        run_case_with_post_pop_rechecks(&case, 1),
        vec!["sat", "unsat", "sat", "sat"]
    );
}

/// LRA nested push/pop: inner scope UNSAT must not leak through outer scope.
#[test]
#[timeout(10_000)]
fn contract_lra_nested_push_pop() {
    let results = run_smt(
        r#"
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (declare-fun y () Real)
        (assert (>= x 0.0))
        (assert (>= y 0.0))
        (check-sat)

        (push 1)
        (assert (<= x 10.0))
        (check-sat)

        (push 1)
        (assert (>= x 20.0))
        ; x <= 10 AND x >= 20 is UNSAT
        (check-sat)
        (pop 1)

        ; Back to level 1: x >= 0, y >= 0, x <= 10
        (check-sat)
        (pop 1)

        ; Back to level 0: x >= 0, y >= 0 only
        (check-sat)

        ; Verify x <= 10 did not leak: x = 100 should be SAT
        (push 1)
        (assert (>= x 100.0))
        (check-sat)
        (pop 1)
        "#,
    );
    assert_eq!(results, vec!["sat", "sat", "unsat", "sat", "sat", "sat"]);
}

// ============================================================================
// BV (Bitvectors) - contract coverage
// ============================================================================

/// BV scope restoration: scoped bitvector constraints must not leak after pop.
#[test]
#[timeout(10_000)]
fn contract_bv_scope_restoration() {
    let case = PushPopContractCase {
        logic: "QF_BV",
        declarations: &["(declare-fun x () (_ BitVec 8))"],
        // Base: x = #x0A (10)
        base_assertions: &["(= x #x0A)"],
        // Scoped: x = #xFF contradicts x = #x0A
        scoped_assertions: &["(= x #xFF)"],
        // Post-pop: bvult x #x10 is compatible with x = #x0A
        post_pop_assertions: &["(bvult x #x10)"],
    };

    assert_eq!(run_case(&case), vec!["sat", "unsat", "sat"]);
}

/// BV post-pop recheck stability.
#[test]
#[timeout(10_000)]
fn contract_bv_post_pop_recheck_is_stable() {
    let case = PushPopContractCase {
        logic: "QF_BV",
        declarations: &["(declare-fun x () (_ BitVec 8))"],
        base_assertions: &["(= x #x0A)"],
        scoped_assertions: &["(= x #xFF)"],
        post_pop_assertions: &[],
    };

    assert_eq!(
        run_case_with_post_pop_rechecks(&case, 1),
        vec!["sat", "unsat", "sat", "sat"]
    );
}

/// BV nested push/pop with contradicting scoped constraints.
#[test]
#[timeout(10_000)]
fn contract_bv_nested_push_pop() {
    let results = run_smt(
        r#"
        (set-logic QF_BV)
        (declare-fun x () (_ BitVec 8))
        (assert (bvuge x #x05))
        (check-sat)

        (push 1)
        (assert (bvule x #x0F))
        ; x >= 5 AND x <= 15 is SAT
        (check-sat)

        (push 1)
        (assert (bvuge x #x20))
        ; x <= 15 AND x >= 32 is UNSAT
        (check-sat)
        (pop 1)

        ; Back to level 1: x >= 5 AND x <= 15
        (check-sat)
        (pop 1)

        ; Back to level 0: x >= 5 only. x = 0xFF should be SAT.
        (push 1)
        (assert (= x #xFF))
        (check-sat)
        (pop 1)
        "#,
    );
    assert_eq!(results, vec!["sat", "sat", "unsat", "sat", "sat"]);
}

// ============================================================================
// Arrays - contract coverage
// ============================================================================

/// Array scope restoration: scoped store/select constraints must not leak.
#[test]
#[timeout(10_000)]
fn contract_array_scope_restoration() {
    let case = PushPopContractCase {
        logic: "QF_AX",
        declarations: &[
            "(declare-sort Elem 0)",
            "(declare-fun a () (Array Int Elem))",
            "(declare-fun e1 () Elem)",
            "(declare-fun e2 () Elem)",
        ],
        // Base: a[0] = e1
        base_assertions: &["(= (select a 0) e1)"],
        // Scoped: a[0] = e2 AND e1 != e2 contradicts a[0] = e1
        scoped_assertions: &["(= (select a 0) e2)", "(not (= e1 e2))"],
        // Post-pop: only a[0] = e1 survives
        post_pop_assertions: &[],
    };

    assert_eq!(run_case(&case), vec!["sat", "unsat", "sat"]);
}

/// Array post-pop recheck stability.
#[test]
#[timeout(10_000)]
fn contract_array_post_pop_recheck_is_stable() {
    let case = PushPopContractCase {
        logic: "QF_AX",
        declarations: &[
            "(declare-sort Elem 0)",
            "(declare-fun a () (Array Int Elem))",
            "(declare-fun e1 () Elem)",
            "(declare-fun e2 () Elem)",
        ],
        base_assertions: &["(= (select a 0) e1)"],
        scoped_assertions: &["(= (select a 0) e2)", "(not (= e1 e2))"],
        post_pop_assertions: &[],
    };

    assert_eq!(
        run_case_with_post_pop_rechecks(&case, 1),
        vec!["sat", "unsat", "sat", "sat"]
    );
}

/// Array nested push/pop: store in inner scope must be undone.
#[test]
#[timeout(10_000)]
fn contract_array_nested_push_pop() {
    let results = run_smt(
        r#"
        (set-logic QF_AX)
        (declare-sort Elem 0)
        (declare-fun a () (Array Int Elem))
        (declare-fun b () (Array Int Elem))
        (declare-fun e1 () Elem)
        (declare-fun e2 () Elem)
        (assert (not (= e1 e2)))
        (assert (= (select a 0) e1))
        (check-sat)

        (push 1)
        ; In scope: b = store(a, 0, e2), so select(b, 0) = e2
        (assert (= b (store a 0 e2)))
        (assert (= (select b 0) e1))
        ; select(store(a,0,e2),0) = e2 but we assert e1: UNSAT since e1 != e2
        (check-sat)
        (pop 1)

        ; After pop: only a[0] = e1 and e1 != e2 survive
        (check-sat)
        "#,
    );
    assert_eq!(results, vec!["sat", "unsat", "sat"]);
}

// ============================================================================
// Strings - contract coverage
// ============================================================================

fn assert_string_result(actual: &str, expected: &str, context: &str) {
    assert_eq!(actual, expected, "{context}");
}

/// String scope restoration: scoped string equality must not leak after pop.
/// Uses the same pattern as strings_prover_audit.rs::memory_push_pop_scope_isolation.
///
#[test]
#[timeout(30_000)]
fn contract_strings_scope_restoration() {
    let results = run_smt(
        "\
(set-logic QF_S)
(declare-fun x () String)
(push 1)
(assert (= x \"hello\"))
(assert (= x \"world\"))
(check-sat)
(pop 1)
(assert (= x \"hello\"))
(check-sat)
",
    );
    assert_eq!(
        results.len(),
        2,
        "expected 2 check-sat results: {results:?}"
    );
    assert_string_result(&results[0], "unsat", "x=\"hello\" AND x=\"world\" in scope");
    assert_string_result(&results[1], "sat", "x=\"hello\" after pop");
}

/// String multi-cycle push/pop: state from cycle 1 must not leak into cycle 2.
#[test]
#[timeout(30_000)]
fn contract_strings_multi_cycle_no_accumulation() {
    let results = run_smt(
        "\
(set-logic QF_S)
(declare-fun x () String)
(push 1)
(assert (= x \"a\"))
(assert (= x \"b\"))
(check-sat)
(pop 1)
(push 1)
(assert (= x \"c\"))
(assert (= x \"d\"))
(check-sat)
(pop 1)
(assert (= x \"hello\"))
(check-sat)
",
    );
    assert_eq!(
        results.len(),
        3,
        "expected 3 check-sat results: {results:?}"
    );
    assert_string_result(&results[0], "unsat", "cycle 1: x=\"a\" AND x=\"b\"");
    assert_string_result(&results[1], "unsat", "cycle 2: x=\"c\" AND x=\"d\"");
    assert_string_result(&results[2], "sat", "after pops: x=\"hello\"");
}

// ============================================================================
// Cross-theory: UFLIA (EUF + LIA combined) - contract coverage
// ============================================================================

/// UFLIA scope restoration: combined theory state must be fully restored.
/// This catches bugs where one theory restores but the other does not,
/// or where the Nelson-Oppen equality bridge leaks stale equalities.
#[test]
#[timeout(10_000)]
fn contract_uflia_scope_restoration() {
    let case = PushPopContractCase {
        logic: "QF_UFLIA",
        declarations: &[
            "(declare-fun f (Int) Int)",
            "(declare-fun x () Int)",
            "(declare-fun y () Int)",
        ],
        // Base: f(x) = 5
        base_assertions: &["(= (f x) 5)"],
        // Scoped: x = y AND f(y) != 5 contradicts f(x)=5 by congruence
        scoped_assertions: &["(= x y)", "(not (= (f y) 5))"],
        // Post-pop: f(x) = 5 still holds; f(y) can be anything
        post_pop_assertions: &["(= (f y) 10)"],
    };

    assert_eq!(run_case(&case), vec!["sat", "unsat", "sat"]);
}

/// UFLIA nested push/pop: verifies both EUF and LIA undo correctly at depth 2.
#[test]
#[timeout(10_000)]
fn contract_uflia_nested_push_pop() {
    let results = run_smt(
        r#"
        (set-logic QF_UFLIA)
        (declare-fun f (Int) Int)
        (declare-fun x () Int)
        (declare-fun y () Int)
        (assert (= (f x) 5))
        (assert (>= x 0))
        (check-sat)

        (push 1)
        (assert (= x y))
        ; f(x)=5 and x=y, so f(y)=5 by congruence. SAT.
        (check-sat)

        (push 1)
        (assert (not (= (f y) 5)))
        ; Contradicts f(y)=5 from congruence. UNSAT.
        (check-sat)
        (pop 1)

        ; Back to level 1: x=y, f(x)=5. SAT.
        (check-sat)
        (pop 1)

        ; Back to level 0: f(x)=5, x>=0 only. No x=y constraint.
        ; f(y) can be anything. SAT.
        (check-sat)
        "#,
    );
    assert_eq!(results, vec!["sat", "sat", "unsat", "sat", "sat"]);
}

// ============================================================================
// Multi-cycle push/pop: verifies no accumulation across scope cycles
// ============================================================================

/// LIA multi-cycle: assertions from scope N must not leak into scope N+1.
/// This catches the common bug where assertion trail marks are not properly
/// reset between consecutive push/pop cycles.
#[test]
#[timeout(10_000)]
fn contract_lia_multi_cycle_no_accumulation() {
    let results = run_smt(
        r#"
        (set-logic QF_LIA)
        (declare-fun x () Int)
        (assert (>= x 0))
        (check-sat)

        ; Cycle 1: add x >= 100
        (push 1)
        (assert (>= x 100))
        (check-sat)
        (pop 1)

        ; Cycle 2: add x <= 5. Should be SAT if cycle 1 did not leak x >= 100.
        (push 1)
        (assert (<= x 5))
        (check-sat)
        (pop 1)

        ; Cycle 3: add x = 3
        (push 1)
        (assert (= x 3))
        (check-sat)
        (pop 1)

        ; Global: only x >= 0
        (check-sat)
        "#,
    );
    assert_eq!(results, vec!["sat", "sat", "sat", "sat", "sat"]);
}

/// LRA multi-cycle: no accumulation across scope cycles for real arithmetic.
#[test]
#[timeout(10_000)]
fn contract_lra_multi_cycle_no_accumulation() {
    let results = run_smt(
        r#"
        (set-logic QF_LRA)
        (declare-fun x () Real)
        (assert (>= x 0.0))
        (check-sat)

        ; Cycle 1: x >= 100
        (push 1)
        (assert (>= x 100.0))
        (check-sat)
        (pop 1)

        ; Cycle 2: x <= 5. SAT if no leak from cycle 1.
        (push 1)
        (assert (<= x 5.0))
        (check-sat)
        (pop 1)

        ; Global: only x >= 0
        (check-sat)
        "#,
    );
    assert_eq!(results, vec!["sat", "sat", "sat", "sat"]);
}

/// EUF multi-cycle: equivalence class merges from one scope must not persist
/// into the next scope.
#[test]
#[timeout(10_000)]
fn contract_euf_multi_cycle_no_accumulation() {
    let results = run_smt(
        r#"
        (set-logic QF_UF)
        (declare-sort S 0)
        (declare-fun a () S)
        (declare-fun b () S)
        (declare-fun c () S)
        (assert (not (= a c)))
        (check-sat)

        ; Cycle 1: merge a=b
        (push 1)
        (assert (= a b))
        (check-sat)
        (pop 1)

        ; Cycle 2: merge b=c. a!=c should still hold (a and c are distinct).
        ; If cycle 1 leaked a=b, then b=c would force a=c, contradiction.
        (push 1)
        (assert (= b c))
        (check-sat)
        (pop 1)

        ; Global: only a != c
        (check-sat)
        "#,
    );
    assert_eq!(results, vec!["sat", "sat", "sat", "sat"]);
}

/// QF_ABV (Arrays + Bitvectors) push/pop: array axioms from popped scope must
/// not persist. Without incremental_mode dispatch, the non-incremental path
/// scans ALL TermStore terms (including dead ones from popped scopes) for array
/// axiom generation, causing phantom axioms and Unknown/timeout (#6727).
#[test]
#[timeout(10_000)]
fn contract_abv_scope_restoration() {
    let case = PushPopContractCase {
        logic: "QF_ABV",
        declarations: &[
            "(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))",
            "(declare-fun v1 () (_ BitVec 8))",
            "(declare-fun v2 () (_ BitVec 8))",
        ],
        // Base: select(a, #x00) = v1
        base_assertions: &["(= (select a #x00) v1)"],
        // Scoped: select(a, #x00) = v2 AND v1 != v2 contradicts base
        scoped_assertions: &["(= (select a #x00) v2)", "(not (= v1 v2))"],
        // Post-pop: only base survives
        post_pop_assertions: &[],
    };
    assert_eq!(run_case(&case), vec!["sat", "unsat", "sat"]);
}

/// QF_ABV post-pop recheck stability (#6727).
#[test]
#[timeout(10_000)]
fn contract_abv_post_pop_recheck_is_stable() {
    let case = PushPopContractCase {
        logic: "QF_ABV",
        declarations: &[
            "(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))",
            "(declare-fun v1 () (_ BitVec 8))",
            "(declare-fun v2 () (_ BitVec 8))",
        ],
        base_assertions: &["(= (select a #x00) v1)"],
        scoped_assertions: &["(= (select a #x00) v2)", "(not (= v1 v2))"],
        post_pop_assertions: &[],
    };
    assert_eq!(
        run_case_with_post_pop_rechecks(&case, 1),
        vec!["sat", "unsat", "sat", "sat"]
    );
}

/// QF_AUFBV (Arrays + UF + Bitvectors) push/pop: same phantom axiom class
/// as ABV but also exercises UF congruence axiom generation (#6727).
#[test]
#[timeout(10_000)]
fn contract_aufbv_scope_restoration() {
    let case = PushPopContractCase {
        logic: "QF_AUFBV",
        declarations: &[
            "(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))",
            "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))",
            "(declare-fun v1 () (_ BitVec 8))",
            "(declare-fun v2 () (_ BitVec 8))",
        ],
        // Base: f(select(a, #x00)) = v1
        base_assertions: &["(= (f (select a #x00)) v1)"],
        // Scoped: f(select(a, #x00)) = v2 AND v1 != v2 contradicts base via EUF
        scoped_assertions: &["(= (f (select a #x00)) v2)", "(not (= v1 v2))"],
        // Post-pop: only base survives
        post_pop_assertions: &[],
    };
    assert_eq!(run_case(&case), vec!["sat", "unsat", "sat"]);
}

/// QF_AUFBV post-pop recheck stability (#6727).
#[test]
#[timeout(10_000)]
fn contract_aufbv_post_pop_recheck_is_stable() {
    let case = PushPopContractCase {
        logic: "QF_AUFBV",
        declarations: &[
            "(declare-fun a () (Array (_ BitVec 8) (_ BitVec 8)))",
            "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))",
            "(declare-fun v1 () (_ BitVec 8))",
            "(declare-fun v2 () (_ BitVec 8))",
        ],
        base_assertions: &["(= (f (select a #x00)) v1)"],
        scoped_assertions: &["(= (f (select a #x00)) v2)", "(not (= v1 v2))"],
        post_pop_assertions: &[],
    };
    assert_eq!(
        run_case_with_post_pop_rechecks(&case, 1),
        vec!["sat", "unsat", "sat", "sat"]
    );
}
