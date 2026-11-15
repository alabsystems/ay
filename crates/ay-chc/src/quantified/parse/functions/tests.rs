// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::unwrap_used)]

use super::*;
use crate::ClauseHead;

mod resources;

fn parsed(source: &str) -> QuantifiedChcProblem {
    QuantifiedChcProblem::parse_smtlib(source).unwrap()
}

fn refuses(source: &str) {
    assert!(
        matches!(
            QuantifiedChcProblem::parse_smtlib(source),
            Err(ChcError::Parse(_))
        ),
        "{source}"
    );
}

fn head(problem: &QuantifiedChcProblem, index: usize) -> &[ChcExpr] {
    let ClauseHead::Predicate(_, args) = &problem.source_problem().clauses()[index].head else {
        panic!("predicate head")
    };
    args
}

fn app(expr: &ChcExpr) -> (&str, &ChcSort, &[Arc<ChcExpr>]) {
    let ChcExpr::FuncApp(name, sort, args) = expr else {
        panic!("source function application, not a variable")
    };
    (name, sort, args)
}

#[test]
fn fixedpoint_functions_are_neutral_ordered_and_include_unused_nullary_globals() {
    let source = "(declare-fun f ((_ BitVec 8) Bool) (_ BitVec 136))
      (declare-var x (_ BitVec 8))
      (declare-fun global () (_ BitVec 136))
      (declare-rel P ((_ BitVec 136)))
      (declare-fun unused ((_ BitVec 136)) (_ BitVec 8))
      (rule (P (f x true))) (query (P global))";
    let problem = parsed(source);
    assert_eq!(
        problem
            .function_declarations()
            .iter()
            .map(|f| f.name())
            .collect::<Vec<_>>(),
        ["f", "global", "unused"]
    );
    let f = &problem.function_declarations()[0];
    assert_eq!(f.arg_sorts(), [ChcSort::BitVec(8), ChcSort::Bool]);
    assert_eq!(f.result_sort(), &ChcSort::BitVec(136));
    assert_eq!(app(&head(&problem, 0)[0]).0, "f");
    let query = &problem.source_problem().clauses()[1];
    let (name, sort, args) = app(&query.body.predicates[0].1[0]);
    assert_eq!(name, "global");
    assert_eq!(sort, &ChcSort::BitVec(136));
    assert!(args.is_empty());
    assert!(problem
        .source_smtlib()
        .contains("(declare-fun unused ((_ BitVec 136)) (_ BitVec 8))"));
}

#[test]
fn horn_boolean_declarations_stay_relations_and_bv_declarations_stay_functions() {
    let problem = parsed(
        "(declare-fun P ((_ BitVec 8)) Bool)
      (declare-fun f ((_ BitVec 8)) (_ BitVec 8))
      (declare-fun global () (_ BitVec 8))
      (assert (forall ((x (_ BitVec 8))) (P (f x))))
      (assert (=> (P global) false)) (check-sat)",
    );
    assert_eq!(problem.source_problem().predicates().len(), 1);
    assert_eq!(problem.source_problem().predicates()[0].name, "P");
    assert_eq!(problem.function_declarations().len(), 2);
    assert_eq!(app(&head(&problem, 0)[0]).0, "f");
    assert!(problem.source_problem().clauses()[1].is_query());
    let roundtrip = parsed(problem.source_smtlib());
    // The canonical output's fresh binder name is itself reserved on reparse;
    // compare authenticated declarations and retained binding shape, not the
    // incidental second alpha-renaming's bytes.
    assert_eq!(
        roundtrip.function_declarations(),
        problem.function_declarations()
    );
    assert_eq!(roundtrip.source_problem().clauses().len(), 2);
    let (name, sort, arguments) = app(&head(&roundtrip, 0)[0]);
    assert_eq!(name, "f");
    assert_eq!(sort, &ChcSort::BitVec(8));
    assert!(matches!(arguments[0].as_ref(), ChcExpr::Var(var) if var.sort == ChcSort::BitVec(8)));
    assert_eq!(
        app(&roundtrip.source_problem().clauses()[1].body.predicates[0].1[0]).0,
        "global"
    );
}

#[test]
fn functions_used_only_in_grouped_premises_keep_every_binder_and_declaration() {
    let problem = parsed(
        "(declare-fun f ((_ BitVec 8) Bool) (_ BitVec 8))
      (declare-fun global () (_ BitVec 8)) (declare-rel P ())
      (rule (=> (forall ((i (_ BitVec 8)) (j (_ BitVec 8)))
        (= (f i (= i j)) global)) P)) (query P)",
    );
    assert_eq!(problem.function_declarations().len(), 2);
    let premise = &problem.premises()[0][0];
    assert_eq!(premise.binder_count(), 2);
    let ChcExpr::Op(crate::ChcOp::Eq, args) = premise.matrix() else {
        panic!("raw equality")
    };
    let (_, _, args_f) = app(&args[0]);
    let ChcExpr::Var(var) = args_f[0].as_ref() else {
        panic!("lexical argument")
    };
    assert_eq!(var.name, premise.binder().name);
    assert_eq!(app(&args[1]).0, "global");
    assert!(app(&args[1]).2.is_empty());
}

#[test]
fn aliases_preserve_resolved_arguments_and_fresh_names_avoid_unused_functions() {
    let problem = parsed(
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
      (declare-fun ay!source!0 () (_ BitVec 8))
      (declare-var x (_ BitVec 8)) (declare-rel P ((_ BitVec 8) (_ BitVec 8)))
      (rule (let ((saved (f x)))
        (let ((x #x02)) (P saved (f x)))))
      (rule (forall ((x (_ BitVec 8))) (P (f x) ay!source!0)))
      (query (P #x00 #x00))",
    );
    let first = head(&problem, 0);
    assert!(matches!(app(&first[0]).2[0].as_ref(), ChcExpr::Var(var) if var.name == "x"));
    assert_eq!(app(&first[1]).2[0].as_ref(), &ChcExpr::BitVec(2, 8));
    let second = head(&problem, 1);
    let ChcExpr::Var(var) = app(&second[0]).2[0].as_ref() else {
        panic!("outer binder")
    };
    assert_ne!(var.name, "ay!source!0");
    assert_eq!(app(&second[1]).0, "ay!source!0");
}

#[test]
fn nested_wide_applications_and_scalar_signature_order_are_preserved() {
    let problem = parsed(
        "(declare-fun f (Bool (_ BitVec 136)) (_ BitVec 136))
      (declare-fun leaf () (_ BitVec 136)) (declare-rel P ((_ BitVec 136)))
      (rule (P (f true (f false leaf)))) (query (P leaf))",
    );
    let (_, sort, outer) = app(&head(&problem, 0)[0]);
    assert_eq!(sort, &ChcSort::BitVec(136));
    assert_eq!(outer[0].as_ref(), &ChcExpr::Bool(true));
    let (_, _, inner) = app(&outer[1]);
    assert_eq!(inner[0].as_ref(), &ChcExpr::Bool(false));
    assert_eq!(app(&inner[1]).0, "leaf");
}

#[test]
fn undeclared_arity_sort_and_qualifier_near_misses_refuse() {
    for term in [
        "unknown",
        "(unknown #x00)",
        "f",
        "(f)",
        "(f #x00 #x00)",
        "(f true)",
        "(f #b0)",
        "(f ((as const (Array (_ BitVec 8) Bool)) true))",
        "((as f (_ BitVec 8)) #x00)",
    ] {
        refuses(&format!(
            "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))
          (declare-rel P ((_ BitVec 8))) (rule (P {term})) (query (P #x00))"
        ));
    }
    refuses(
        "(declare-fun global () (_ BitVec 8))(declare-rel P ((_ BitVec 8)))
      (rule (P (global true))) (query (P #x00))",
    );
}

#[test]
fn non_scalar_malformed_and_oversized_function_signatures_refuse_even_unused() {
    for argument in [
        "Int",
        "Real",
        "Missing",
        "(_ BitVec 0)",
        "(_ BitVec 1048577)",
        "(Array (_ BitVec 8) Bool)",
    ] {
        refuses(&format!(
            "(declare-fun unused ({argument}) (_ BitVec 8))
          (declare-rel error ()) (query error)"
        ));
    }
    for result in [
        "Int",
        "Real",
        "Missing",
        "(_ BitVec 0)",
        "(_ BitVec 1048577)",
        "(_ BitVec 8 1)",
        "(Bool)",
        "(Array (_ BitVec 8) Bool)",
    ] {
        refuses(&format!(
            "(declare-fun unused () {result})(declare-rel error ())(query error)"
        ));
    }
    refuses(
        "(declare-datatype Row ((mkRow (value Bool))))
      (declare-fun f (Row) (_ BitVec 8))(declare-rel error ())(query error)",
    );
    refuses(
        "(declare-datatype Row ((mkRow (value Bool))))
      (declare-fun f () Row)(declare-rel error ())(query error)",
    );
}

#[test]
fn all_global_namespace_collisions_refuse_in_both_declaration_orders() {
    let function = "(declare-fun f () (_ BitVec 8))";
    for conflicting in [
        "(declare-fun f () (_ BitVec 8))",
        "(declare-fun f ((_ BitVec 8)) (_ BitVec 16))",
        "(declare-var f (_ BitVec 8))",
        "(declare-rel f ())",
        "(declare-datatype f ((mk (field Bool))))",
        "(declare-datatype Row ((f (field Bool))))",
        "(declare-datatype Row ((mk (f Bool))))",
    ] {
        for prefix in [
            format!("{function}{conflicting}"),
            format!("{conflicting}{function}"),
        ] {
            refuses(&format!("{prefix}(declare-rel error ())(query error)"));
        }
    }
    for prefix in [
        "(declare-fun f () (_ BitVec 8))(declare-fun f () Bool)",
        "(declare-fun f () Bool)(declare-fun f () (_ BitVec 8))",
    ] {
        refuses(&format!("{prefix}(assert false)(check-sat)"));
    }
}

#[test]
fn function_names_cannot_be_let_or_forall_binders_even_when_unused() {
    for body in [
        "(let ((f #x00)) P)",
        "(let ((f #x00) (unused #x01)) P)",
        "(forall ((f (_ BitVec 8))) P)",
        "(=> (forall ((f (_ BitVec 8))) (= f #x00)) P)",
    ] {
        refuses(&format!(
            "(declare-fun f () (_ BitVec 8))(declare-rel P ())
          (rule {body})(query P)"
        ));
    }
}

#[test]
fn function_declarations_do_not_relax_phase_dialect_or_builtin_rules() {
    for source in [
        "(declare-fun f () (_ BitVec 8))(declare-var x Bool)(assert false)(check-sat)",
        "(declare-fun P () Bool)(declare-fun f () (_ BitVec 8))(rule P)(query P)",
        "(declare-rel P ())(rule P)(declare-fun f () (_ BitVec 8))(query P)",
        "(declare-fun bvadd () (_ BitVec 8))(declare-rel error ())(query error)",
        "(declare-fun |select| () (_ BitVec 8))(declare-rel error ())(query error)",
    ] {
        refuses(source);
    }
}
