// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn verdicts_do_not_confuse_sat_and_unsat() {
    assert_eq!(
        verdicts_of("sat\nunsat\n"),
        vec![Verdict::Sat, Verdict::Unsat]
    );
    assert_eq!(verdicts_of("unsat"), vec![Verdict::Unsat]);
    assert_eq!(verdicts_of("((x 5))\nsat"), vec![Verdict::Sat]);
    assert_eq!(verdicts_of("(error \"boom\")"), Vec::<Verdict>::new());
    // Responses that carry a verdict word but are not check-sat answers.
    let z3 = "sat\n(:reason-unknown \"\")\n((is_sat true))\n(\n  (define-fun unsat_x () Int\n    1)\n)\n";
    assert_eq!(verdicts_of(z3), vec![Verdict::Sat]);
}

#[test]
fn textual_error_invalidates_partial_verdict() {
    let output = "(error \"unknown constant set.card\")\nsat\n";
    assert!(has_error_response(output));
    let ay = Outcome::Verdicts(vec![Verdict::Unsat]);
    let z3 = Outcome::Error;
    assert_eq!(categorize(&ay, &z3), Category::SolverError);
}

#[test]
fn disagreement_is_flagged() {
    let ay = Outcome::Verdicts(vec![Verdict::Unsat]);
    let z3 = Outcome::Verdicts(vec![Verdict::Sat]);
    assert_eq!(categorize(&ay, &z3), Category::Disagree);
}

#[test]
fn ay_unknown_is_incomplete_not_a_bug() {
    let ay = Outcome::Verdicts(vec![Verdict::Unknown]);
    let z3 = Outcome::Verdicts(vec![Verdict::Sat]);
    assert_eq!(categorize(&ay, &z3), Category::AyIncomplete);
}

#[test]
fn matching_verdicts_agree() {
    let ay = Outcome::Verdicts(vec![Verdict::Sat]);
    let z3 = Outcome::Verdicts(vec![Verdict::Sat]);
    assert_eq!(categorize(&ay, &z3), Category::AgreeSat);
}

// --- declared-status oracle -------------------------------------------

#[test]
fn declared_status_parses_whole_word() {
    assert_eq!(
        declared_status_of("(set-info :status unsat)\n(check-sat)"),
        Some(Verdict::Unsat)
    );
    assert_eq!(
        declared_status_of("(set-info :status sat)"),
        Some(Verdict::Sat)
    );
    // `unknown` and absent are both "no usable oracle".
    assert_eq!(declared_status_of("(set-info :status unknown)"), None);
    assert_eq!(declared_status_of("(check-sat)"), None);
}

#[test]
fn declared_wrong_when_ay_contradicts_status() {
    // AY sat, file declares unsat = the shipped wrong-SAT class.
    let ay = Outcome::Verdicts(vec![Verdict::Sat]);
    assert_eq!(
        categorize_declared(Some(Verdict::Unsat), &ay),
        DeclaredCategory::Wrong
    );
    // AY unsat, file declares sat = a spurious-conflict wrong answer.
    let ay = Outcome::Verdicts(vec![Verdict::Unsat]);
    assert_eq!(
        categorize_declared(Some(Verdict::Sat), &ay),
        DeclaredCategory::Wrong
    );
}

#[test]
fn declared_correct_and_incomplete_and_no_oracle() {
    let ay_sat = Outcome::Verdicts(vec![Verdict::Sat]);
    assert_eq!(
        categorize_declared(Some(Verdict::Sat), &ay_sat),
        DeclaredCategory::Correct
    );
    // AY unknown where the file decided = tolerated incompleteness.
    let ay_unk = Outcome::Verdicts(vec![Verdict::Unknown]);
    assert_eq!(
        categorize_declared(Some(Verdict::Unsat), &ay_unk),
        DeclaredCategory::Incomplete
    );
    // No decided :status = nothing to judge against.
    assert_eq!(
        categorize_declared(None, &ay_sat),
        DeclaredCategory::NoOracle
    );
}
