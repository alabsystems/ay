// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `set.card` refutations must be certifiable, not merely correct.
//!
//! `--self-check` is the observable: it WITHHOLDS a verdict AY cannot certify,
//! so `unsat` there means the refutation passed strict validation end to end.
//!
//! Note that grepping the emitted `.alethe` for `:rule hole` is NOT the right
//! criterion. The Alethe printer renders any kind the external checker cannot
//! implement as `hole` by design -- carcara has no `set_card_non_negative`
//! rule, exactly as it has none for `array_default_const` -- so the exported
//! certificate keeps a `hole` even when AY's own checker is satisfied.

use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

use ntest::timeout;

struct CleanupGuard(PathBuf);

impl Drop for CleanupGuard {
    fn drop(&mut self) {
        let _ = std::fs::remove_file(&self.0);
    }
}

fn solve(args: &[&str], script: &str) -> String {
    static ID: AtomicUsize = AtomicUsize::new(0);
    let path = std::env::temp_dir().join(format!(
        "ay_set_card_cert_{}_{}.smt2",
        std::process::id(),
        ID.fetch_add(1, Ordering::Relaxed)
    ));
    std::fs::write(&path, script).unwrap();
    let _guard = CleanupGuard(path.clone());

    let output = Command::new(env!("CARGO_BIN_EXE_ay"))
        .args(args)
        .arg(&path)
        .output()
        .expect("failed to spawn ay");
    String::from_utf8_lossy(&output.stdout).into_owned()
}

const CARD_IS_NEGATIVE: &str = "(set-logic ALL)\n\
     (declare-const s (Set Int))\n\
     (assert (< (set.card s) 0))\n\
     (check-sat)\n";

/// The refutation rests on `(<= 0 (set.card s))`, a bridge axiom AY injects
/// rather than one the user wrote. Being solver-generated it cannot stay an
/// `Assume`, and it reached publication as a `Step{Trust}` -- which the whole
/// funnel treats as "believe the solver, no derivation", so the verdict was
/// withheld even though every other step (`la_generic`, resolution) checked.
#[test]
#[timeout(30_000)]
fn a_cardinality_refutation_is_strictly_certified() {
    assert_eq!(
        solve(&[], CARD_IS_NEGATIVE).trim(),
        "unsat",
        "cardinality is never negative"
    );
    assert_eq!(
        solve(&["--self-check"], CARD_IS_NEGATIVE).trim(),
        "unsat",
        "the refutation must pass strict certification, not just be correct"
    );
}

/// The soundness direction: the axiom licenses `card >= 0` and NOTHING more.
/// A set whose cardinality is merely unconstrained is satisfiable, and the
/// bridge axiom must not let that be refuted.
#[test]
#[timeout(30_000)]
fn the_bridge_axiom_does_not_refute_a_satisfiable_cardinality() {
    let satisfiable = "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (set.card s) 2))\n\
         (check-sat)\n";
    assert_eq!(
        solve(&[], satisfiable).trim(),
        "sat",
        "a set of cardinality 2 plainly exists"
    );
}

/// The membership lower bound, the second axiom shape: a set with a known
/// member has at least one element, so `card = 0` refutes.
#[test]
#[timeout(30_000)]
fn a_membership_lower_bound_refutation_is_strictly_certified() {
    let script = "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (set.card s) 0))\n\
         (assert (set.member 1 s))\n\
         (check-sat)\n";
    assert_eq!(solve(&[], script).trim(), "unsat");
    assert_eq!(
        solve(&["--self-check"], script).trim(),
        "unsat",
        "the membership lower bound must be certified, not trusted"
    );
}

/// Soundness control for that shape: a member and a cardinality that ACCOMMODATES
/// it must stay satisfiable. The axiom licenses `|s| >= 1`, never `|s| = 1`.
#[test]
#[timeout(30_000)]
fn a_member_with_room_in_the_cardinality_stays_satisfiable() {
    let script = "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (set.card s) 3))\n\
         (assert (set.member 1 s))\n\
         (check-sat)\n";
    assert_eq!(solve(&[], script).trim(), "sat");
}

/// The empty set's cardinality, the third axiom shape. Covered only in its
/// SYNTACTIC form: a set that is empty by assertion needs problem context the
/// theory-lemma checker does not receive.
#[test]
#[timeout(30_000)]
fn an_empty_set_cardinality_refutation_is_strictly_certified() {
    let script = "(set-logic ALL)\n\
         (assert (= (set.card (as set.empty (Set Int))) 2))\n\
         (check-sat)\n";
    assert_eq!(solve(&[], script).trim(), "unsat");
    assert_eq!(
        solve(&["--self-check"], script).trim(),
        "unsat",
        "the empty set plainly has cardinality 0, and that must be certified"
    );
}

/// Soundness control: the axiom fixes the EMPTY set's cardinality at 0 and
/// says nothing about any other set, so a cardinality of 2 elsewhere is fine.
#[test]
#[timeout(30_000)]
fn a_non_empty_set_keeps_its_own_cardinality() {
    let script = "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (set.card s) 2))\n\
         (assert (= (set.card (as set.empty (Set Int))) 0))\n\
         (check-sat)\n";
    assert_eq!(solve(&[], script).trim(), "sat");
}

/// The counted-membership tree, the fourth axiom shape: two distinct members
/// force `|s| >= 2`, refuting `card = 1`.
#[test]
#[timeout(30_000)]
fn a_counted_membership_refutation_is_strictly_certified() {
    let script = "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (set.card s) 1))\n\
         (assert (set.member 1 s))\n\
         (assert (set.member 2 s))\n\
         (check-sat)\n";
    assert_eq!(solve(&[], script).trim(), "unsat");
    assert_eq!(
        solve(&["--self-check"], script).trim(),
        "unsat",
        "the counted-membership bound must be certified, not trusted"
    );
}

/// Soundness control: the bound is `|s| >= k`, never `|s| = k`, so a
/// cardinality with room for both members stays satisfiable.
#[test]
#[timeout(30_000)]
fn two_members_with_room_stay_satisfiable() {
    let script = "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (set.card s) 5))\n\
         (assert (set.member 1 s))\n\
         (assert (set.member 2 s))\n\
         (check-sat)\n";
    assert_eq!(solve(&[], script).trim(), "sat");
}

/// The fifth shape, and the only one that is NOT a tautology: the set is empty
/// only because the problem SAYS so, so the checker decides it against a
/// registry built from the problem's top-level asserted equalities.
#[test]
#[timeout(30_000)]
fn an_empty_by_assertion_refutation_is_strictly_certified() {
    let script = "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (set.card s) 2))\n\
         (assert (= s (as set.empty (Set Int))))\n\
         (check-sat)\n";
    assert_eq!(solve(&[], script).trim(), "unsat");
    assert_eq!(
        solve(&["--self-check"], script).trim(),
        "unsat",
        "an asserted-empty set's cardinality must be certified, not trusted"
    );
}

/// Soundness control: WITHOUT the emptiness assertion the same cardinality is
/// satisfiable, so the registry must not invent emptiness.
#[test]
#[timeout(30_000)]
fn a_set_never_asserted_empty_keeps_its_cardinality() {
    let script = "(set-logic ALL)\n\
         (declare-const s (Set Int))\n\
         (assert (= (set.card s) 2))\n\
         (check-sat)\n";
    assert_eq!(solve(&[], script).trim(), "sat");
}
