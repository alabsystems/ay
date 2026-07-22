// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unsat-core dedup + EUF/ArrayEuf deletion-minimization tests
//! (#uc-core-dedup, #uc-core-minimize).
//!
//! 2025 UC scoring pays `#named asserts − |core|` per validated unsat answer,
//! so a padded (all-named) or duplicate-label core scores 0. These tests pin:
//!
//! 1. TermId dedup: hash-consed duplicate assert bodies (same TermId, several
//!    `:named` labels / repeated asserts) never print a label twice.
//! 2. QF_UF / QF_AX deletion minimization: a theory-level refutation whose
//!    SAT-level failed-assumption harvest is EMPTY (the EUF a=b,b=c,a!=c
//!    shape) must NOT pad to all named assertions — the deletion loop shrinks
//!    to a solve-verified subset that excludes irrelevant named asserts.
//! 3. Determinism: same instance, fresh executors → byte-identical core.

use super::*;

fn run(input: &str) -> Vec<String> {
    let commands = parse(input).unwrap();
    let mut exec = Executor::new();
    exec.execute_all(&commands).unwrap()
}

/// Parse the `(get-unsat-core)` output `(n1 n2 ...)` into a list of names.
fn core_names(output: &str) -> Vec<String> {
    output
        .trim()
        .trim_start_matches('(')
        .trim_end_matches(')')
        .split_whitespace()
        .map(str::to_string)
        .collect()
}

// ========== 1. TermId dedup (#uc-core-dedup) ==========

/// Two `:named` labels on the SAME (hash-consed) assert body share one
/// TermId. The printed core must contain at most one entry for that TermId —
/// never the same label twice, and never both labels.
#[test]
fn test_core_dedups_hash_consed_duplicate_named_asserts() {
    let outputs = run(r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (assert (! (= a b) :named n1))
        (assert (! (= a b) :named n2))
        (assert (! (not (= a b)) :named n3))
        (check-sat)
        (get-unsat-core)
    "#);
    assert_eq!(outputs[0], "unsat");
    let names = core_names(&outputs[1]);
    let mut sorted = names.clone();
    sorted.sort();
    sorted.dedup();
    assert_eq!(
        sorted.len(),
        names.len(),
        "duplicate label in printed core: {names:?}"
    );
    assert!(
        !(names.contains(&"n1".to_string()) && names.contains(&"n2".to_string())),
        "both labels of one TermId printed (dedup by TermId must keep one): {names:?}"
    );
    assert!(
        names.contains(&"n3".to_string()),
        "load-bearing member n3 missing: {names:?}"
    );
}

// ========== 2. QF_UF minimization (#uc-core-minimize) ==========

/// The canonical empty-harvest shape: the EUF transitivity refutation
/// a=b, b=c, a!=c surfaces an EMPTY SAT-level core, which used to be padded
/// to ALL named assertions (reduction 0). The deletion loop must exclude the
/// irrelevant named asserts.
#[test]
fn test_qfuf_core_minimized_excludes_irrelevant_named_asserts() {
    let outputs = run(r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (declare-const e U)
        (declare-const f U)
        (assert (! (= a b) :named h1))
        (assert (! (= b c) :named h2))
        (assert (! (not (= a c)) :named h3))
        (assert (! (= d e) :named irr1))
        (assert (! (= e f) :named irr2))
        (check-sat)
        (get-unsat-core)
    "#);
    assert_eq!(outputs[0], "unsat");
    let names = core_names(&outputs[1]);
    for needed in ["h1", "h2", "h3"] {
        assert!(
            names.contains(&needed.to_string()),
            "load-bearing member {needed} missing from core: {names:?}"
        );
    }
    for irrelevant in ["irr1", "irr2"] {
        assert!(
            !names.contains(&irrelevant.to_string()),
            "irrelevant member {irrelevant} not minimized away: {names:?}"
        );
    }
}

/// UF congruence refutation with an unnamed base assertion: the printed core
/// conjoined with the UNNAMED assertions must stay unsatisfiable, and the
/// irrelevant named assert must go.
#[test]
fn test_qfuf_core_minimized_with_unnamed_base() {
    let outputs = run(r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-fun g (U) U)
        (declare-const x U)
        (declare-const y U)
        (declare-const p U)
        (declare-const q U)
        (assert (= x y))
        (assert (! (not (= (g x) (g y))) :named goal))
        (assert (! (= p q) :named irr))
        (check-sat)
        (get-unsat-core)
    "#);
    assert_eq!(outputs[0], "unsat");
    let names = core_names(&outputs[1]);
    assert!(
        names.contains(&"goal".to_string()),
        "goal missing from core: {names:?}"
    );
    assert!(
        !names.contains(&"irr".to_string()),
        "irrelevant member not minimized away: {names:?}"
    );
}

// ========== QF_AX minimization ==========

/// Store-commutation refutation (the storecomm family shape): the two
/// load-bearing asserts stay, the irrelevant equality goes.
#[test]
fn test_qfax_core_minimized_excludes_irrelevant_named_asserts() {
    let outputs = run(r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_AX)
        (declare-sort I 0)
        (declare-sort E 0)
        (declare-const arr (Array I E))
        (declare-const i I)
        (declare-const j I)
        (declare-const x E)
        (declare-const y E)
        (declare-const u E)
        (declare-const v E)
        (assert (! (distinct i j) :named neq))
        (assert (! (not (= (store (store arr i x) j y)
                           (store (store arr j y) i x))) :named goal))
        (assert (! (= u v) :named irr))
        (check-sat)
        (get-unsat-core)
    "#);
    assert_eq!(outputs[0], "unsat");
    let names = core_names(&outputs[1]);
    assert!(
        names.contains(&"goal".to_string()),
        "goal missing from core: {names:?}"
    );
    assert!(
        !names.contains(&"irr".to_string()),
        "irrelevant member not minimized away: {names:?}"
    );
}

// ========== 3. Determinism ==========

/// Same instance, two fresh executors → byte-identical core (instance-derived
/// deterministic subset order; no wall-clock-dependent choice under a
/// non-binding budget).
#[test]
fn test_minimized_core_deterministic_across_runs() {
    let input = r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (declare-const e U)
        (declare-const f U)
        (declare-const g U)
        (assert (! (= a b) :named h1))
        (assert (! (= b c) :named h2))
        (assert (! (= c d) :named h3))
        (assert (! (not (= a d)) :named h4))
        (assert (! (= e f) :named irr1))
        (assert (! (= f g) :named irr2))
        (assert (! (= e g) :named irr3))
        (check-sat)
        (get-unsat-core)
    "#;
    let first = run(input);
    let second = run(input);
    assert_eq!(first[0], "unsat");
    assert_eq!(first, second, "minimized core must be run-to-run identical");
}

// ========== SAT-level harvest already small: minimization must not grow ==========

/// A propositional-flavored QF_UF conflict where the MiniSat-style harvest
/// already names a small core: minimization must keep it at most that size
/// (the 2018-Goel-hwbench guard shape).
#[test]
fn test_small_harvest_core_stays_small() {
    let outputs = run(r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-const p Bool)
        (declare-const q Bool)
        (declare-const r Bool)
        (assert (! p :named a1))
        (assert (! (not p) :named a2))
        (assert (! q :named a3))
        (assert (! r :named a4))
        (check-sat)
        (get-unsat-core)
    "#);
    assert_eq!(outputs[0], "unsat");
    let names = core_names(&outputs[1]);
    assert!(
        names.len() <= 2,
        "core should stay at the {{a1, a2}} conflict: {names:?}"
    );
    assert!(
        !names.contains(&"a3".to_string()) && !names.contains(&"a4".to_string()),
        "irrelevant members leaked into core: {names:?}"
    );
}

// ========== Named-assert rewrite provenance (#uc-named-provenance) ==========

/// A NAMED assert that is a Bool ITE is rewritten in place by
/// `rewrite_assertion_bool_ites` BEFORE the named-core redirect. The
/// rewritten form must keep the label through the rewrite-provenance map
/// instead of tripping the fail-closed coverage guard, which pads the core
/// to ALL named assertions (the 2018-Goel-hwbench reduction-0 shape:
/// itc99 318->316, h_b08 170->167 were pure pad+dedup).
#[test]
fn test_named_bool_ite_assert_keeps_core_provenance() {
    let outputs = run(r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const p Bool)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (assert (! (ite p (= a b) (and p (= a b))) :named h1))
        (assert (! (not (= a b)) :named h2))
        (assert (! (= c d) :named irr))
        (check-sat)
        (get-unsat-core)
    "#);
    assert_eq!(outputs[0], "unsat");
    let names = core_names(&outputs[1]);
    assert!(
        names.contains(&"h1".to_string()) && names.contains(&"h2".to_string()),
        "rewritten named assert lost its label (provenance): {names:?}"
    );
    assert!(
        !names.contains(&"irr".to_string()),
        "irrelevant member not minimized away (provenance guard padded?): {names:?}"
    );
}

// ========== check-sat-assuming named-core path ==========

/// The user-facing `check-sat-assuming` redirect flows through the same
/// minimization chokepoint: named assertions irrelevant to the conflict must
/// leave the core, and get-unsat-assumptions keeps its subset contract.
#[test]
fn test_check_sat_assuming_named_core_minimized() {
    let outputs = run(r#"
        (set-option :produce-unsat-cores true)
        (set-logic QF_UF)
        (declare-sort U 0)
        (declare-const a U)
        (declare-const b U)
        (declare-const c U)
        (declare-const d U)
        (declare-const e U)
        (assert (! (= a b) :named h1))
        (assert (! (= b c) :named h2))
        (assert (! (= d e) :named irr))
        (check-sat-assuming ((not (= a c))))
        (get-unsat-core)
        (get-unsat-assumptions)
    "#);
    assert_eq!(outputs[0], "unsat");
    let names = core_names(&outputs[1]);
    assert!(
        names.contains(&"h1".to_string()) && names.contains(&"h2".to_string()),
        "load-bearing members missing from core: {names:?}"
    );
    assert!(
        !names.contains(&"irr".to_string()),
        "irrelevant member not minimized away: {names:?}"
    );
    // get-unsat-assumptions: subset of the user literals only.
    assert!(
        outputs[2].contains("not") && !outputs[2].contains("irr"),
        "unsat-assumptions must stay within the user literals: {}",
        outputs[2]
    );
}
