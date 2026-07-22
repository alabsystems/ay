// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

//! D2 lazy DT lane end-to-end soundness (`DESIGN_lazy_dt.md` stage D2:
//! `try_solve_dt_lazy` routing + `ay_dt::DtSplitOnDemand` splits + the D0
//! ground-structural-disequality rule).
//!
//! Pure QF_DT shapes here route enum-lane -> LAZY lane -> eager fallback, so
//! every assertion below exercises the lazy lane first (default-on). The
//! unsat cases must be conflict-derived inside the lane (or, fail-closed, by
//! the eager fallback — either way `unsat` is the only sound answer); the
//! sat cases guard against over-firing conflicts and split-starvation, and
//! pass only through the always-on model gates.

use ntest::timeout;

/// Ground structural disequality through a frame chain: two ground towers
/// with the same top constructor but different contents merged via state
/// copies. The old clash rule cannot see it (same top constructor); rule 1b
/// must refute it during search. MUST be unsat.
#[test]
#[timeout(60_000)]
fn test_ground_diseq_frame_chain_unsat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B) (C))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const s0 tower)
        (declare-const s1 tower)
        (declare-const s2 tower)
        (assert (= s0 (stack A (stack B (stack C empty)))))
        (assert (= s1 s0))
        (assert (= s2 s1))
        (assert (= s2 (stack A (stack C (stack B empty)))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "two structurally different ground towers cannot be equal"
    );
}

/// Ground-diseq sat control: the SAME chain equated to the structurally
/// IDENTICAL ground tower (written as a distinct syntactic occurrence) must
/// stay sat — guards rule 1b against flagging equal ground values.
#[test]
#[timeout(60_000)]
fn test_ground_eq_frame_chain_stays_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B) (C))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const s0 tower)
        (declare-const s1 tower)
        (declare-const s2 tower)
        (assert (= s0 (stack A (stack B (stack C empty)))))
        (assert (= s1 s0))
        (assert (= s2 s1))
        (assert (= s2 (stack A (stack B (stack C empty)))))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "sat", "identical ground towers are equal");
}

/// The blocksworld sat-side capability shape from the diagnosis (task
/// wo8e5ybw1): distinct selector-application enum values over a 2-value
/// enum. Needs the D2 domain-closure split (or the model gates + repair) to
/// commit `top x` / `top y` to the two enum constructors. MUST be sat.
#[test]
#[timeout(60_000)]
fn test_enum_selector_distinct_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (assert ((_ is stack) x))
        (assert ((_ is stack) y))
        (assert (distinct (top x) (top y)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "two stacks can carry the two distinct enum values"
    );
}

/// Enum pigeonhole control for the split rule: THREE pairwise-distinct
/// selector values over a 2-value enum. MUST be unsat (guards the D2 split
/// clauses' completeness/soundness pairing: the splits commit each value and
/// the disequalities pigeonhole them).
#[test]
#[timeout(60_000)]
fn test_enum_selector_pigeonhole_unsat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (declare-const z tower)
        (assert (distinct (top x) (top y)))
        (assert (distinct (top y) (top z)))
        (assert (distinct (top x) (top z)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "three pairwise-distinct values do not fit a 2-value enum"
    );
}

/// Mini blocksworld BMC step, unsat direction: one guarded move from a
/// known ground state; both branches contradict the asserted goal. The lazy
/// lane must refute BOTH move branches through selector projection over
/// materialized atoms + ground disequality. MUST be unsat.
#[test]
#[timeout(60_000)]
fn test_mini_bmc_step_goal_unreachable_unsat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B) (C))))
        (declare-datatypes ((mv 0)) (((pop-it) (keep))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const s0 tower)
        (declare-const s1 tower)
        (declare-const c0 mv)
        (assert (= s0 (stack A (stack B empty))))
        (assert (ite (= c0 pop-it) (= s1 (rest s0)) (= s1 s0)))
        (assert (= s1 (stack C empty)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "unsat",
        "neither pop (-> stack B empty) nor keep (-> stack A ...) reaches stack C empty"
    );
}

/// Mini blocksworld BMC step, sat direction: the pop branch reaches the
/// goal. Exercises projection `rest(s0) = (stack B empty)` + the move enum
/// split + the model gates end-to-end. MUST be sat.
#[test]
#[timeout(60_000)]
fn test_mini_bmc_step_goal_reachable_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B) (C))))
        (declare-datatypes ((mv 0)) (((pop-it) (keep))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const s0 tower)
        (declare-const s1 tower)
        (declare-const c0 mv)
        (assert (= s0 (stack A (stack B empty))))
        (assert (ite (= c0 pop-it) (= s1 (rest s0)) (= s1 s0)))
        (assert (= s1 (stack B empty)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(result.trim(), "sat", "pop-it reaches (stack B empty)");
}

/// Deep ground disequality (17-level towers, the blocksworld initial-state
/// scale): equal prefixes except one block deep inside. MUST be unsat, and
/// fast (the conflict is one rule-1b clause, not a case-split search).
#[test]
#[timeout(60_000)]
fn test_deep_ground_towers_unsat() {
    let mut push = String::new();
    let mut t1 = "empty".to_string();
    let mut t2 = "empty".to_string();
    for i in 0..17 {
        // Towers differ only at level 8 (b1 there is "C" — 8 % 3 == 2).
        let b1 = ["A", "B", "C"][i % 3];
        let b2 = if i == 8 { "A" } else { b1 };
        t1 = format!("(stack {b1} {t1})");
        t2 = format!("(stack {b2} {t2})");
    }
    push.push_str(&format!(
        r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B) (C))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (assert (= x {t1}))
        (assert (= y x))
        (assert (= y {t2}))
        (check-sat)
    "#
    ));
    let result = crate::common::solve(&push);
    assert_eq!(result.trim(), "unsat", "towers differ at level 8");
}

/// Uncommitted-class fallback safety: a recursive-sort variable constrained
/// only by testers has NO enum split base and no committed constructor; the
/// lane must still answer sat (via gates or eager fallback), never a wrong
/// verdict. Guards the trimmed-scope decision (no recursive splits).
#[test]
#[timeout(60_000)]
fn test_recursive_uncommitted_class_stays_sat() {
    let smt = r#"
        (set-logic QF_DT)
        (declare-datatypes ((blk 0)) (((A) (B))))
        (declare-datatypes ((tower 0)) (((stack (top blk) (rest tower)) (empty))))
        (declare-const x tower)
        (declare-const y tower)
        (assert ((_ is stack) x))
        (assert ((_ is empty) y))
        (assert (not (= x y)))
        (check-sat)
    "#;
    let result = crate::common::solve(smt);
    assert_eq!(
        result.trim(),
        "sat",
        "is-stack(x), is-empty(y), x != y is satisfiable"
    );
}
