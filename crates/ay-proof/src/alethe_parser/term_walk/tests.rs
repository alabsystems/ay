// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

fn document(term: &str) -> String {
    format!("(step s (cl {term}) :rule hole)\n(step end (cl) :rule hole)\n")
}

fn parse_on_small_stack(text: String) -> Result<AletheDocumentReport, AletheDefect> {
    // This is deliberately SMALLER than libtest's normal worker stack.
    // Increasing the stack would conceal the original crashing regression.
    std::thread::Builder::new()
        .stack_size(256 * 1024)
        .spawn(move || {
            check_alethe_document(
                &text,
                &ProblemScope::from_smtlib_source("(declare-const p Bool)"),
            )
        })
        .expect("bounded-stack parser worker")
        .join()
        .expect("parser must return a defect, never abort or unwind")
}

fn nest(prefix: &str, suffix: &str, atom: &str, count: usize) -> String {
    format!("{}{atom}{}", prefix.repeat(count), suffix.repeat(count))
}

#[test]
fn applications_accept_exact_original_depth_on_small_native_stack() {
    assert!(parse_on_small_stack(document(&nest("(not ", ")", "p", MAX_TERM_DEPTH))).is_ok());
}

#[test]
fn applications_refuse_one_beyond_original_depth_without_aborting() {
    assert!(matches!(
        parse_on_small_stack(document(&nest("(not ", ")", "p", MAX_TERM_DEPTH + 1))),
        Err(AletheDefect::TermTooDeep { .. })
    ));
}

#[test]
fn parallel_let_body_uses_the_same_nonrecursive_continuation() {
    let term = nest("(let ((x p)) ", ")", "x", MAX_TERM_DEPTH);
    assert!(parse_on_small_stack(document(&term)).is_ok());
    let deep = format!("(let ((y p)) {term})");
    assert!(matches!(
        parse_on_small_stack(document(&deep)),
        Err(AletheDefect::TermTooDeep { .. })
    ));
}

#[test]
fn quantified_body_uses_the_same_nonrecursive_continuation() {
    let term = nest("(forall ((x Bool)) ", ")", "x", MAX_TERM_DEPTH);
    assert!(parse_on_small_stack(document(&term)).is_ok());
    let deep = format!("(exists ((y Bool)) {term})");
    assert!(matches!(
        parse_on_small_stack(document(&deep)),
        Err(AletheDefect::TermTooDeep { .. })
    ));
}

#[test]
fn annotated_body_uses_the_same_nonrecursive_continuation() {
    let term = nest("(! ", " :named label)", "p", MAX_TERM_DEPTH);
    assert!(parse_on_small_stack(document(&term)).is_ok());
    let deep = format!("(! {term} :named outer)");
    assert!(matches!(
        parse_on_small_stack(document(&deep)),
        Err(AletheDefect::TermTooDeep { .. })
    ));
}

#[test]
fn nested_sort_constructors_cannot_escape_stack_safety() {
    for depth in [MAX_TERM_DEPTH, MAX_TERM_DEPTH + 1] {
        let sort = nest("(Seq ", ")", "Bool", depth);
        let result = parse_on_small_stack(document(&format!("(forall ((x {sort})) p)")));
        if depth == MAX_TERM_DEPTH {
            assert!(result.is_ok(), "{result:?}");
        } else {
            assert!(matches!(result, Err(AletheDefect::TermTooDeep { .. })));
        }
    }
}

#[test]
fn nested_qualified_identifiers_cannot_escape_depth_accounting() {
    let head = nest("(as ", " Bool)", "p", MAX_TERM_DEPTH + 2);
    assert!(matches!(
        parse_on_small_stack(document(&format!("({head} p)"))),
        Err(AletheDefect::TermTooDeep { .. })
    ));
}

#[test]
fn deep_rup_clause_preserves_the_original_term_depth_contract() {
    let root = nest("(not ", ")", "p", MAX_TERM_DEPTH);
    let text =
        format!("(assume a p)\n(step end (cl) :rule drup :premises (a) :args ((cl {root})))");
    assert!(parse_on_small_stack(text).is_ok());
    // Document acceptance is not semantic RUP acceptance.
    let deep = nest("(not ", ")", "p", MAX_TERM_DEPTH + 1);
    let text =
        format!("(assume a p)\n(step end (cl) :rule drup :premises (a) :args ((cl {deep})))");
    assert!(matches!(
        parse_on_small_stack(text),
        Err(AletheDefect::TermTooDeep { .. })
    ));
}

#[test]
fn let_rhs_remains_parallel_and_local_bindings_cannot_escape() {
    for term in [
        "(let ((x p) (y x)) y)",
        "(and (let ((x p)) x) x)",
        "(and (forall ((x Bool)) x) x)",
    ] {
        assert!(
            matches!(
                parse_on_small_stack(document(term)),
                Err(AletheDefect::UndefinedSymbol { name, .. }) if name == "x"
            ),
            "{term}"
        );
    }
    assert!(parse_on_small_stack(document("(let ((x p)) (let ((x x) (y x)) (and x y)))")).is_ok());
}

#[test]
fn qualified_lambda_binders_end_before_the_application_arguments() {
    assert!(parse_on_small_stack(document("((lambda ((x Bool)) x) p)")).is_ok());
    assert!(matches!(
        parse_on_small_stack(document("((lambda ((x Bool)) x) x)")),
        Err(AletheDefect::UndefinedSymbol { name, .. }) if name == "x"
    ));
}

#[test]
fn parser_errors_restore_the_callers_original_binder_slice() {
    for term in [
        "(forall ((x Bool)) missing)",
        "(let ((x p)) (forall ((y Bool)) missing))",
        "(forall ((x Bool) (y MissingSort)) x)",
        "(forall ((x Bool)) (let ((y missing)) y))",
    ] {
        let mut checker =
            AletheDocumentChecker::new(ProblemScope::from_smtlib_source("(declare-const p Bool)"));
        let mut binders = vec!["outer".to_string()];
        let mut lexer = Lexer::new(term, 0, 0);
        let (token, pos) = lexer.next_token().expect("opening token");
        assert!(checker
            .parse_term_from(&mut lexer, token, pos, &mut binders, 0)
            .is_err());
        assert_eq!(binders, ["outer"], "{term}");
    }
}

#[test]
fn applications_still_enforce_shadowing_proof_definition_arity() {
    let text = format!("(define-fun f () Bool p)\n{}", document("(f p)"));
    assert!(
        matches!(parse_on_small_stack(text), Err(AletheDefect::UnexpectedToken { expected, .. })
        if expected == "the declared arity of a proof define-fun")
    );
    let text = format!("(define-fun f ((x Bool)) Bool x)\n{}", document("(f p)"));
    assert!(parse_on_small_stack(text).is_ok());
}

#[test]
fn qualified_indexed_heads_and_sort_diagnostics_remain_checked() {
    for term in [
        "((_ extract 0 0) #b1)",
        "((as const (Array Int Bool)) p)",
        "(as p Bool)",
    ] {
        assert!(parse_on_small_stack(document(term)).is_ok(), "{term}");
    }
    for term in [
        "((as const (Array Int MissingSort)) p)",
        "(forall ((x (_ MissingSort 8))) p)",
    ] {
        assert!(
            matches!(
                parse_on_small_stack(document(term)),
                Err(AletheDefect::UndefinedSort { .. })
            ),
            "{term}"
        );
    }
}

#[test]
fn nonterm_clause_and_forbidden_heads_are_not_newly_admitted() {
    for term in [
        "(not (cl p))",
        "(cl)",
        "(let () p)",
        "(forall () p)",
        "(! p :named)",
        "(not p",
    ] {
        assert!(parse_on_small_stack(document(term)).is_err(), "{term}");
    }
    for term in ["(match p)", "(par p)"] {
        assert!(
            matches!(
                parse_on_small_stack(document(term)),
                Err(AletheDefect::ForbiddenConstruct { .. })
            ),
            "{term}"
        );
    }
}
