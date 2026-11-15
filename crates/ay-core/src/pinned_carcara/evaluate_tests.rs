// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The `evaluate` scan on its own. The real-checker control behind it is
//! `a_valid_verdict_resting_on_a_misjudged_evaluate_is_not_evidence` in the
//! ay-dpll `carcara_external_check` tests.

use super::evaluate::evaluate_steps_pinned_carcara_misjudges;
use super::lexer::{alethe_commands, command_atoms, step_rule_of};

#[test]
fn alethe_commands_skip_comments_quoted_symbols_and_strings() {
    let document = "; (step t9 (cl) :rule evaluate)\n\
                    (assume t0 (= x |a) :rule evaluate|))\n\
                    (step t1 (cl (not (= x |a) :rule evaluate|)))\n  :rule resolution :premises (t0))\n\
                    (step t2 (cl (= s \"q\"\")\")) :rule refl) ; trailing (comment\n\
                    (step t3 (cl) :rule hole)\n";
    let commands = alethe_commands(document);
    assert_eq!(commands.len(), 4, "{commands:?}");
    assert!(commands[1].ends_with(":premises (t0))"), "{}", commands[1]);
    let rules: Vec<Option<&str>> = commands
        .iter()
        .map(|command| step_rule_of(&command_atoms(command)))
        .collect();
    assert_eq!(
        rules,
        vec![None, Some("resolution"), Some("refl"), Some("hole")]
    );
    assert_eq!(
        step_rule_of(&command_atoms("(anchor :step t4 :args ((x Int)))")),
        None
    );
    assert_eq!(step_rule_of(&command_atoms("(step t5 (cl p) :rule)")), None);
}

#[test]
fn only_evaluate_steps_over_misjudged_operators_are_flagged() {
    let document = "(step t0 (cl (= (bvsge #xf #xe) false)) :rule evaluate)\n\
                    (step t1 (cl (= (bvadd #x01 #x01) #x02)) :rule evaluate)\n\
                    (step t2 (cl (= ((_ extract 3 0) #x1f) #xf)) :rule evaluate)\n\
                    (step t3 (cl (= (bvsub a b) (bvadd a (bvneg b)))) :rule poly_simp)\n\
                    (step t4 (cl (= (|bvsub| #x1 #x2) #xf)) :rule evaluate)\n\
                    (define-fun d0 () (_ BitVec 4) (bvsub #x1 #x2))\n\
                    (define-fun d1 () (_ BitVec 4) (bvnot d0))\n\
                    (step t5 (cl (= d1 #x0)) :rule evaluate)\n\
                    (step t6 (cl (= (bvnot #x0) #xf)) :rule evaluate)\n\
                    ; (step t7 (cl (= (bvslt #x0 #x1) true)) :rule evaluate)\n\
                    (step t8\n  (cl (= (bvslt #x0 #x1) true))\n  :rule evaluate)\n";
    let flagged = evaluate_steps_pinned_carcara_misjudges("", document);
    let ids: Vec<&str> = flagged
        .iter()
        .map(|command| command_atoms(command)[1].1)
        .collect();
    // t4: `|bvsub|` IS `bvsub` (see `symbol_name`).
    assert_eq!(ids, vec!["t0", "t2", "t4", "t5", "t8"]);
}

/// Measured 2026-09-25 with pinned Carcara: it prints `valid` for the
/// `evaluate` refutation of the satisfiable `(assert (! (bvsge #xf #xe)
/// :named n))` through `(step t1 (cl (= n false)) :rule evaluate)`, and
/// likewise when the label sits on the proof's `assume`, when the step
/// spells `|n|`, and when it names its rule `|evaluate|`.
#[test]
fn evaluate_steps_through_labels_and_quoted_symbols_are_flagged() {
    let problem = "(assert (! (bvsge #xf #xe) :named n))\n\
                   (assert (! (bvult #x1 #x2) :named u))\n";
    let proof = "(assume t0 (! (= (bvsub #x1 #x2) #xf) :named |m|))\n\
                 (step t1 (cl (= n false)) :rule evaluate)\n\
                 (step t2 (cl (= m true)) :rule evaluate)\n\
                 (step t3 (cl (= u true)) :rule evaluate)\n\
                 (step t4 (cl (= |n| false)) :rule evaluate)\n\
                 (step t5 (cl (= (bvsge #xf #xe) false)) :rule |evaluate|)\n\
                 (step t6 (cl (= (bvsge #xf #xe) false)) :rule equiv_simp)\n";
    let flagged = evaluate_steps_pinned_carcara_misjudges(problem, proof);
    let ids: Vec<&str> = flagged
        .iter()
        .map(|command| command_atoms(command)[1].1)
        .collect();
    assert_eq!(ids, vec!["t1", "t2", "t4", "t5"]);
}

/// Measured 2026-09-25 with pinned Carcara: each of these false evaluations
/// prints `valid` inside an `evaluate` refutation of a problem z3 answers
/// `sat` (`(div (- 7) 2)` is -4, `(mod (- 7) 2)` is 1, and
/// `((_ rotate_left 4) #b001)` is `#b010`).
#[test]
fn integer_division_and_over_rotation_evaluate_steps_are_flagged() {
    let document = "(step t0 (cl (= (= (div (- 7) 2) (- 4)) false)) :rule evaluate)\n\
                    (step t1 (cl (= (= (mod (- 7) 2) 1) false)) :rule evaluate)\n\
                    (step t2 (cl (= (= ((_ rotate_left 4) #b001) #b010) false)) :rule evaluate)\n\
                    (step t3 (cl (= (+ 1 2) 3)) :rule evaluate)\n\
                    (step t4 (cl (= ((_ rotate_right 4) #b001) #b100)) :rule evaluate)\n";
    let flagged = evaluate_steps_pinned_carcara_misjudges("", document);
    let ids: Vec<&str> = flagged
        .iter()
        .map(|command| command_atoms(command)[1].1)
        .collect();
    assert_eq!(ids, vec!["t0", "t1", "t2"]);
}
