// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

const PROBLEM: &str = "(declare-const p Bool) (declare-const q Bool) \
                       (assert p) (assert (not p))";
const PREFIX: &str = "(assume a p)\n(assume b (not p))\n";
const SUFFIX: &str = "(step end (cl) :rule resolution :premises (a b))\n";

fn check(text: &str) -> Result<AletheDocumentReport, AletheDefect> {
    check_alethe_document(text, &ProblemScope::from_smtlib_source(PROBLEM))
}

#[test]
fn drup_empty_argument_clause_round_trips() {
    let text = format!("{PREFIX}(step end (cl) :rule drup :premises (a b) :args ((cl)))\n");
    let report = check(&text).expect("ordinary RUP refutation has a clause argument");
    assert_eq!((report.assumes, report.steps), (2, 1));
}

#[test]
fn drat_empty_argument_clause_round_trips() {
    let text = format!("{PREFIX}(step end (cl) :rule drat :premises (a b) :args ((cl)))\n");
    assert_eq!(check(&text).expect("DRAT clause argument").steps, 1);
}

#[test]
fn drup_nonempty_and_multiple_argument_clauses_round_trip() {
    let text = format!(
        "{PREFIX}\
        (step copy (cl p q) :rule drup :premises (a) :args ((cl p) (cl p q)))\n\
        {SUFFIX}"
    );
    assert_eq!(
        check(&text)
            .expect("multiple ordinary clause arguments")
            .steps,
        2
    );
}

#[test]
fn shared_boolean_literal_in_one_premise_drup_keeps_its_scope() {
    let text = "(define-fun shared () Bool (or p q))\n\
        (assume a p)\n(assume b (not p))\n\
        (step one (cl shared (not p)) :rule or_neg :args (0))\n\
        (step unit (cl shared) :rule resolution :premises (one a))\n\
        (step two (cl shared) :rule drup :premises (unit) :args ((cl shared)))\n\
        (step end (cl) :rule resolution :premises (a b))\n";
    // This is only syntax/scope coverage; the real Boolean emitter control
    // checks its generated command, and independent replay checks semantics.
    assert_eq!(
        check(text)
            .expect("defined Boolean clause literal")
            .define_funs,
        1
    );
}

#[test]
fn clause_argument_undefined_symbols_are_not_ignored() {
    let text = format!("{PREFIX}(step c (cl) :rule drup :premises (a b) :args ((cl missing)))");
    assert!(
        matches!(check(&text), Err(AletheDefect::UndefinedSymbol { name, .. }) if name == "missing")
    );
}

#[test]
fn clause_arguments_retain_binder_scope() {
    let text = format!(
        "{PREFIX}\
        (anchor :step sub :args ((local Bool)))\n\
        (assume h local)\n\
        (step cp (cl local) :rule drup :premises (h) :args ((cl local)))\n\
        (step sub (cl (not local) local) :rule subproof :discharge (h))\n\
        {SUFFIX}"
    );
    assert_eq!(
        check(&text).expect("anchor-bound clause literal").anchors,
        1
    );
    let escaped = format!("{text}(step bad (cl) :rule drup :premises (a b) :args ((cl local)))");
    assert!(
        matches!(check(&escaped), Err(AletheDefect::UndefinedSymbol { name, .. }) if name == "local")
    );
}

#[test]
fn nested_clause_literals_remain_rejected_for_rup_rules() {
    for rule in ["drup", "drat"] {
        for argument in ["(cl (cl p))", "(cl (not (cl)))", "(cl (or p (cl q)))"] {
            let text =
                format!("{PREFIX}(step c (cl) :rule {rule} :premises (a b) :args ({argument}))");
            assert!(
                matches!(check(&text), Err(AletheDefect::UnexpectedToken { .. })),
                "{text}"
            );
        }
    }
}

#[test]
fn clause_terms_remain_rejected_outside_rup_arguments() {
    for command in [
        "(step c (cl (cl p)) :rule drup :args ((cl)))",
        "(step c (cl) :rule resolution :premises (a b) :args ((cl)))",
        "(assume c (cl p))",
        "(define-fun x () Bool (cl p))",
    ] {
        assert!(
            matches!(
                check(&format!("{PREFIX}{command}")),
                Err(AletheDefect::UnexpectedToken { .. })
            ),
            "{command}"
        );
    }
}

#[test]
fn malformed_clause_argument_sequences_remain_rejected() {
    for arguments in ["()", "(p)", "((or p q))", "((|cl| p))", "((cl) p)"] {
        let text = format!("{PREFIX}(step c (cl) :rule drup :premises (a b) :args {arguments})");
        assert!(check(&text).is_err(), "{text}");
    }
}

#[test]
fn ordinary_rule_argument_terms_keep_their_existing_grammar() {
    let text = format!("{PREFIX}(step one (cl (or p q) (not p)) :rule or_neg :args (0))\n{SUFFIX}");
    assert_eq!(check(&text).expect("ordinary argument numeral").steps, 2);
}

#[test]
fn rup_arguments_cannot_hide_missing_premises_or_reordered_attributes() {
    for command in [
        "(step c (cl) :rule drup :premises (missing) :args ((cl)))",
        "(step c (cl) :args ((cl)) :rule drup :premises (a b))",
        "(step c (cl) :rule drup :args ((cl)) :premises (a b))",
    ] {
        assert!(check(&format!("{PREFIX}{command}")).is_err(), "{command}");
    }
}

#[test]
fn drup_clause_arguments_are_streamed_without_partial_acceptance() {
    let text = format!("{PREFIX}(step end (cl) :rule drup :premises (a b) :args ((cl)))\n");
    for chunk in [1, 2, 3, 7, text.len()] {
        let mut checker = AletheDocumentChecker::new(ProblemScope::from_smtlib_source(PROBLEM));
        for bytes in text.as_bytes().chunks(chunk) {
            checker.push_bytes(bytes).expect("actual streamed clauses");
        }
        assert_eq!(checker.finish().expect("complete stream").steps, 1);
    }
    let prefix = text
        .trim_end()
        .strip_suffix(')')
        .expect("last command close");
    assert!(
        check(prefix).is_err(),
        "partial final command is never accepted"
    );
}

#[test]
fn rup_clause_literal_depth_is_still_bounded() {
    let term = format!(
        "{}p{}",
        "(not ".repeat(MAX_TERM_DEPTH + 2),
        ")".repeat(MAX_TERM_DEPTH + 2)
    );
    let text = format!("{PREFIX}(step c (cl) :rule drup :premises (a b) :args ((cl {term})))");
    assert!(matches!(
        check(&text),
        Err(AletheDefect::TermTooDeep { .. })
    ));
}
