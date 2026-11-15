// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `aci_simp` scan: every shape pinned Carcara was measured accepting
//! falsely is flagged, and the true conclusions AY prints are not.

use super::aci_simp::{aci_simp_equality_is_ac_identity, aci_simp_steps_pinned_carcara_misjudges};
use super::{
    pinned_carcara_can_judge, FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM,
    FALSE_VALID_ACI_SIMP_CONTROL_PROOF,
};

/// The one `aci_simp` step concluding `(= left right)`.
fn step(left: &str, right: &str) -> String {
    format!("(step t1 (cl (= {left} {right})) :rule aci_simp)")
}

/// The flagged steps of `problem` and a proof whose only step concludes
/// `(= left right)` by `aci_simp`.
fn flagged(problem: &str, left: &str, right: &str) -> Vec<String> {
    let proof = format!(
        "(assume h1 (not (= {left} {right})))\n{}\n",
        step(left, right)
    );
    aci_simp_steps_pinned_carcara_misjudges(problem, &proof)
        .into_iter()
        .map(str::to_string)
        .collect()
}

/// Every false equality pinned Carcara printed `valid` for (module comment),
/// including repeats spelled apart that it parses as one term.
#[test]
fn every_measured_false_aci_simp_conclusion_is_flagged() {
    for (left, right) in [
        ("(bvmul a a)", "a"),
        ("(bvadd a a)", "a"),
        ("(bvxor a a)", "a"),
        ("(+ x x)", "x"),
        ("(* x x)", "x"),
        ("(+ r r)", "r"),
        ("(* r r)", "r"),
        ("a", "(bvadd a a)"),
        ("(bvmul a b a)", "(bvmul a b)"),
        ("(bvmul a (bvmul a b))", "(bvmul a b)"),
        ("(concat a a b)", "(concat a b b)"),
        ("(bvmul a #x02 #b00000010)", "(bvmul a #x02)"),
        ("(bvmul a #x02 (_ bv2 8))", "(bvmul a #x02)"),
        ("(bvmul a |a|)", "a"),
        ("(* r 2.0 2.00)", "(* r 2.0)"),
        ("(let ((k a)) (bvmul k a))", "a"),
        ("(bvmul (! a :named q) a)", "a"),
        // `|bvmul|` is Carcara's `bvmul` too.
        ("(|bvmul| a a)", "a"),
        // No repeat as written: Carcara's cross-side cache makes one.
        ("(bvadd a #x00)", "(bvmul a (bvadd a #x00))"),
    ] {
        assert_eq!(
            flagged("", left, right),
            vec![step(left, right)],
            "{left} = {right}"
        );
    }
}

/// A name Carcara expands before any rule runs: a problem `:named` label
/// over a deduplicated operator, a proof `define-fun` aliasing an argument,
/// and a label aliasing one.
#[test]
fn a_repeat_reached_through_an_expanded_name_is_flagged() {
    let label = "(declare-const a (_ BitVec 8))\n(declare-fun g ((_ BitVec 8)) (_ BitVec 8))\n\
                 (assert (= (g a) (! (bvmul a a) :named m)))\n";
    assert_eq!(flagged(label, "m", "a"), vec![step("m", "a")]);
    let alias = "(declare-const a (_ BitVec 8))\n(declare-fun g ((_ BitVec 8)) (_ BitVec 8))\n\
                 (assert (= (g a) (! (bvadd a #x01) :named m)))\n";
    assert_eq!(
        flagged(alias, "(bvmul m (bvadd a #x01))", "m"),
        vec![step("(bvmul m (bvadd a #x01))", "m")]
    );
    let proof = "(define-fun k () (_ BitVec 8) a)\n\
                 (assume h1 (not (= (bvmul a a) a)))\n\
                 (step t1 (cl (= (bvmul k a) a)) :rule aci_simp)\n";
    assert_eq!(
        aci_simp_steps_pinned_carcara_misjudges("", proof),
        vec!["(step t1 (cl (= (bvmul k a) a)) :rule aci_simp)"]
    );
    // A proof-local definition over `bvmul`, used by a step that names none
    // of the six operators itself.
    let proof = "(define-fun sq () (_ BitVec 8) (bvmul a a))\n\
                 (step t1 (cl (= sq a)) :rule aci_simp)\n";
    assert_eq!(
        aci_simp_steps_pinned_carcara_misjudges("", proof),
        vec!["(step t1 (cl (= sq a)) :rule aci_simp)"]
    );
}

/// NEGATIVE twins: the true conclusions are never flagged. Binary swaps (the
/// only `aci_simp` AY prints), a true swap with a repeated operand, flattened
/// regrouping, an identical pair, and a conclusion over idempotent operators
/// only (Carcara deduplicates those soundly).
#[test]
fn true_aci_simp_conclusions_are_not_flagged() {
    for (left, right) in [
        ("(bvmul a b)", "(bvmul b a)"),
        ("(* 16 c)", "(* c 16)"),
        ("(* a b)", "(* b a)"),
        ("(* (* x y) x)", "(* x (* x y))"),
        ("(bvadd a (bvadd b c))", "(bvadd (bvadd c b) a)"),
        ("(concat a (concat b c))", "(concat (concat a b) c)"),
        ("(bvmul a a)", "(bvmul a a)"),
        ("(bvand a a)", "a"),
        ("(bvor a a)", "a"),
        ("(and p p)", "p"),
        ("(or p (or q p))", "(or q p)"),
        ("(bvand x y)", "(bvand y x)"),
    ] {
        assert!(flagged("", left, right).is_empty(), "{left} = {right}");
    }
    // Another rule over `bvmul`, and a comment or quoted symbol spelling the
    // rule, are not `aci_simp` steps.
    let proof = "; :rule aci_simp\n(step t1 (cl (= (bvmul a a) a)) :rule |not aci_simp|)\n\
                 (step t2 (cl (= (bvmul a #x01) a)) :rule bv_simplify)\n";
    assert!(aci_simp_steps_pinned_carcara_misjudges("", proof).is_empty());
    assert!(aci_simp_steps_pinned_carcara_misjudges("", "").is_empty());
}

/// A quoted symbol is not its unquoted spelling: `|#x02|`, `|2|`, `|2.0|` and
/// `|_|` are symbols, `#x02`, `2`, `2.0` and `_` a literal, numerals and a
/// reserved word, and pinned Carcara keeps them apart, so a repeat count split
/// between the two spellings is no AC identity. Measured 2026-10-07: Carcara
/// prints `valid` for the one-step refutation of each of the first five rows,
/// all SATISFIABLE (at `|#x02| = a = #x01`, `|2| = x = 1`, `|#x02| = #x01`,
/// `|2.0| = 1.0`, `(|_| bv2 8) = #x01`). Any quoting difference refuses, even
/// the true last row; the same quoting on both sides does not.
#[test]
fn a_quoted_symbol_is_not_read_as_its_unquoted_spelling() {
    for (left, right) in [
        ("(bvmul |#x02| |#x02| #x02 a)", "(bvmul |#x02| #x02 #x02 a)"),
        ("(* |2| |2| 2 x)", "(* |2| 2 2 x)"),
        ("(bvmul #x02 #x02 |#x02|)", "(bvmul |#x02| |#x02| #x02)"),
        ("(+ 2.0 2.0 |2.0|)", "(+ |2.0| |2.0| 2.0)"),
        (
            "(bvmul (_ bv2 8) (_ bv2 8) (|_| bv2 8))",
            "(bvmul (|_| bv2 8) (|_| bv2 8) (_ bv2 8))",
        ),
        ("(bvmul |a| b)", "(bvmul b a)"),
    ] {
        assert_eq!(
            flagged("", left, right),
            vec![step(left, right)],
            "{left} = {right}"
        );
        assert!(
            !aci_simp_equality_is_ac_identity(left, right),
            "{left} = {right}"
        );
    }
    assert!(aci_simp_equality_is_ac_identity(
        "(bvmul |a| b)",
        "(bvmul b |a|)"
    ));
}

/// The AC-identity check itself: associativity and commutativity only, no
/// idempotence, `concat` kept in order, and anything malformed refused.
#[test]
fn an_ac_identity_is_flattening_and_permutation_only() {
    assert!(aci_simp_equality_is_ac_identity("(* 16 c)", "(* c 16)"));
    assert!(aci_simp_equality_is_ac_identity("x", "x"));
    assert!(aci_simp_equality_is_ac_identity(
        "(+ (f a) (g b))",
        "(+ (g b) (f a))"
    ));
    assert!(!aci_simp_equality_is_ac_identity("(bvmul a a)", "a"));
    assert!(!aci_simp_equality_is_ac_identity("(bvand a a)", "a"));
    assert!(!aci_simp_equality_is_ac_identity(
        "(concat a b)",
        "(concat b a)"
    ));
    assert!(!aci_simp_equality_is_ac_identity(
        "(bvadd a b)",
        "(bvmul b a)"
    ));
    assert!(!aci_simp_equality_is_ac_identity(
        "(bvsub a b)",
        "(bvsub b a)"
    ));
    assert!(!aci_simp_equality_is_ac_identity("(* a b)", "(* a c)"));
    assert!(!aci_simp_equality_is_ac_identity("(* a b) c", "(* b a)"));
    assert!(!aci_simp_equality_is_ac_identity("(* a b", "(* b a)"));
    assert!(!aci_simp_equality_is_ac_identity("(f |a b|)", "(f a b)"));
}

/// A deep chain is read with explicit stacks: no recursion, no overflow.
#[test]
fn a_deep_operator_chain_does_not_recurse() {
    // `(bvadd x0 (bvadd x1 .. z))` against `(bvadd (bvadd (bvadd z x0) x1) ..)`.
    let depth = 20_000;
    let mut left = String::new();
    let mut right = "(bvadd ".repeat(depth);
    for index in 0..depth {
        left.push_str(&format!("(bvadd x{index} "));
    }
    left.push('z');
    left.push_str(&")".repeat(depth));
    right.push('z');
    for index in 0..depth {
        right.push_str(&format!(" x{index})"));
    }
    assert!(aci_simp_equality_is_ac_identity(&left, &right));
    assert!(!aci_simp_equality_is_ac_identity(
        &left,
        &format!("(bvadd x0 {right})")
    ));
}

/// The shared control pair is refused through the entry point every runner
/// calls, naming its false step.
#[test]
fn the_false_valid_aci_simp_control_is_refused() {
    let refused = pinned_carcara_can_judge(
        FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM,
        FALSE_VALID_ACI_SIMP_CONTROL_PROOF,
    )
    .expect_err("the false aci_simp step");
    assert_eq!(
        refused.aci_simp_steps,
        vec!["(step t1 (cl (= (bvmul a a) a)) :rule aci_simp)".to_string()]
    );
    assert!(refused.evaluate_steps.is_empty() && refused.binders.is_empty());
    assert!(refused.to_string().contains("is not evidence"), "{refused}");
    let swapped = FALSE_VALID_ACI_SIMP_CONTROL_PROOF
        .replace("(cl (= (bvmul a a) a))", "(cl (= (bvmul a a) (bvmul a a)))");
    assert_eq!(
        pinned_carcara_can_judge(FALSE_VALID_ACI_SIMP_CONTROL_PROBLEM, &swapped),
        Ok(())
    );
}
