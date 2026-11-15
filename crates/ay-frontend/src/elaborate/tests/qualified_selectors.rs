// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Qualified selectors share direct-constructor folding, not a new rewrite pass.

use super::*;
use crate::command::Command;

fn context(script: &str) -> Context {
    let mut context = Context::new();
    for command in parse(script).unwrap() {
        context.process_command(&command).unwrap();
    }
    context
}

fn term(context: &mut Context, text: &str) -> Result<TermId> {
    let commands = parse(&format!("(get-value ({text}))")).unwrap();
    let [Command::GetValue(terms)] = commands.as_slice() else {
        panic!("expected one parsed term container");
    };
    assert_eq!(terms.len(), 1);
    // Elaborate the actual parsed term; no model lookup or solver invocation.
    context.elaborate_term(&terms[0].1, &HashMap::default())
}

#[test]
fn nested_qualified_selectors_match_bare_expanded_record_fields() {
    let mut context = context(
        "(declare-datatypes ((MCVecIntoIter 0) (MCVec 0))
          (((mkIter (fld_vec MCVec) (fld_pos (_ BitVec 64))))
           ((mkVec (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
             (fld_cap (_ BitVec 64))
             (fld_data (Array (_ BitVec 64) (_ BitVec 8)))))))
         (declare-const w MCVecIntoIter)",
    );
    let record = term(&mut context, "w").unwrap();
    assert!(matches!(context.terms.get(record), TermData::App(..)));
    let bare = term(&mut context, "(fld_vec w)").unwrap();
    let qualified = term(&mut context, "((as fld_vec MCVec) w)").unwrap();
    assert_eq!(qualified, bare);
    assert!(matches!(context.terms.get(qualified), TermData::App(..)));
    for (bare, qualified) in [
        ("(fld_len (fld_vec w))", "(fld_len ((as fld_vec MCVec) w))"),
        (
            "(fld_len (fld_vec w))",
            "((as fld_len (_ BitVec 64)) ((as fld_vec MCVec) w))",
        ),
        (
            "(fld_data (fld_vec w))",
            "((as fld_data (Array (_ BitVec 64) (_ BitVec 8))) ((as fld_vec MCVec) w))",
        ),
    ] {
        let expected = term(&mut context, bare).unwrap();
        let actual = term(&mut context, qualified).unwrap();
        assert_eq!(actual, expected, "{qualified}");
        assert!(matches!(context.terms.get(actual), TermData::Var(..)));
    }
}

#[test]
fn qualified_scalar_and_array_selectors_return_constructor_arguments() {
    let mut context = context(
        "(declare-datatype Rec
           ((mkRec (flag Bool) (byte (_ BitVec 8))
             (data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-const a (Array (_ BitVec 64) (_ BitVec 8)))",
    );
    for (selector, sort, expected) in [
        ("flag", "Bool", "true"),
        ("byte", "(_ BitVec 8)", "#x07"),
        ("data", "(Array (_ BitVec 64) (_ BitVec 8))", "a"),
    ] {
        let bare = term(&mut context, &format!("({selector} (mkRec true #x07 a))")).unwrap();
        let qualified = term(
            &mut context,
            &format!("((as {selector} {sort}) (mkRec true #x07 a))"),
        )
        .unwrap();
        let expected = term(&mut context, expected).unwrap();
        assert_eq!(bare, expected);
        assert_eq!(qualified, expected);
    }
}

#[test]
fn qualified_selectors_keep_wrong_constructor_and_opaque_records_unfolded() {
    let mut context = context(
        "(declare-datatype Choice
           ((own (payload (_ BitVec 8))) (other (noise (_ BitVec 8)))))
         (declare-const unknown Choice)
         (declare-const rows (Array (_ BitVec 8) Choice))",
    );
    let unknown = term(&mut context, "unknown").unwrap();
    assert!(matches!(context.terms.get(unknown), TermData::Var(..)));
    let value = term(&mut context, "#x07").unwrap();
    assert_eq!(
        term(&mut context, "((as payload (_ BitVec 8)) (own #x07))").unwrap(),
        value
    );
    for scrutinee in ["(other #x07)", "unknown", "(select rows #x00)"] {
        let input = term(&mut context, scrutinee).unwrap();
        let bare = term(&mut context, &format!("(payload {scrutinee})")).unwrap();
        let qualified = term(
            &mut context,
            &format!("((as payload (_ BitVec 8)) {scrutinee})"),
        )
        .unwrap();
        assert_eq!(qualified, bare);
        assert_ne!(qualified, value);
        let TermData::App(head, args) = context.terms.get(qualified) else {
            panic!("an unspecified or unknown field must remain opaque");
        };
        assert_eq!(head.name(), "payload");
        assert_eq!(args.as_slice(), &[input]);
        assert_eq!(context.terms.sort(qualified), context.terms.sort(value));
    }
}

#[test]
fn qualified_selector_over_ite_remains_opaque() {
    let mut context = context(
        "(declare-datatype Rec ((mkRec (payload (_ BitVec 8)))))
         (declare-const choose Bool)",
    );
    let input = term(&mut context, "(ite choose (mkRec #x07) (mkRec #x09))").unwrap();
    assert!(matches!(context.terms.get(input), TermData::Ite(..)));
    let qualified = term(
        &mut context,
        "((as payload (_ BitVec 8)) (ite choose (mkRec #x07) (mkRec #x09)))",
    )
    .unwrap();
    let TermData::App(head, args) = context.terms.get(qualified) else {
        panic!("this direct-constructor repair does not traverse ITE branches");
    };
    assert_eq!(head.name(), "payload");
    assert_eq!(args.as_slice(), &[input]);
    let bare = term(
        &mut context,
        "(payload (ite choose (mkRec #x07) (mkRec #x09)))",
    )
    .unwrap();
    let folded = term(&mut context, "(ite choose #x07 #x09)").unwrap();
    assert_eq!(bare, folded, "the pre-existing bare path is unchanged");
    assert_ne!(qualified, folded);
    assert_eq!(context.terms.sort(qualified), context.terms.sort(folded));
}

#[test]
fn qualified_overloaded_selectors_use_selected_internal_identity() {
    let mut context = context(
        "(declare-datatypes ((A 0) (B 0))
          (((mkA (shared (_ BitVec 8)))) ((mkB (shared (_ BitVec 8))))))",
    );
    // Same result sort: only the domain distinguishes these selector overloads.
    for (constructor, literal) in [("mkA", "#x07"), ("mkB", "#x09")] {
        let expected = term(&mut context, literal).unwrap();
        let bare = term(&mut context, &format!("(shared ({constructor} {literal}))")).unwrap();
        let qualified = term(
            &mut context,
            &format!("((as shared (_ BitVec 8)) ({constructor} {literal}))"),
        )
        .unwrap();
        assert_eq!(bare, expected);
        assert_eq!(qualified, expected);
    }
}

#[test]
fn qualified_parametric_selectors_keep_instances_distinct() {
    let mut context = context(
        "(declare-datatypes ((Box 1))
          ((par (T) ((box (value T) (tag (_ BitVec 8)))))))
         (declare-const int_box (Box Int))
         (declare-const bool_box (Box Bool))",
    );
    for (sort, value, tag) in [("Int", "3", "#x07"), ("Bool", "true", "#x09")] {
        let constructor = format!("((as box (Box {sort})) {value} {tag})");
        let record = term(&mut context, &constructor).unwrap();
        let TermData::App(head, _) = context.terms.get(record) else {
            panic!("parametric constructor application");
        };
        assert_ne!(head.name(), "box", "instance identity must be retained");
        for (selector, result_sort, expected) in
            [("value", sort, value), ("tag", "(_ BitVec 8)", tag)]
        {
            let expected = term(&mut context, expected).unwrap();
            let bare = term(&mut context, &format!("({selector} {constructor})")).unwrap();
            let qualified = term(
                &mut context,
                &format!("((as {selector} {result_sort}) {constructor})"),
            )
            .unwrap();
            assert_eq!(bare, expected);
            assert_eq!(qualified, expected);
        }
    }
}

#[test]
fn qualified_selector_signature_errors_are_rejected() {
    let mut context = context(
        "(declare-datatype Rec ((mkRec (payload (_ BitVec 8)))))
         (declare-datatype Other ((mkOther (field (_ BitVec 8)))))",
    );
    for invalid in [
        "((as payload Bool) (mkRec #x07))",
        "((as payload (_ BitVec 8)) #x07)",
        "((as payload (_ BitVec 8)) (mkOther #x07))",
        "(as payload (_ BitVec 8))",
        "((as payload (_ BitVec 8)) (mkRec #x07) (mkRec #x09))",
    ] {
        let error =
            term(&mut context, invalid).expect_err("signature must be checked before folding");
        assert!(
            matches!(
                error,
                ElaborateError::InvalidConstant(_) | ElaborateError::SortMismatch { .. }
            ),
            "{invalid}: {error:?}"
        );
    }
    assert!(context.assertions.is_empty());
}

#[test]
fn qualified_unary_ordinary_function_remains_opaque() {
    let mut context = context(
        "(declare-datatype Rec ((mkRec (payload (_ BitVec 8)))))
         (declare-fun ordinary (Rec) (_ BitVec 8))",
    );
    let input = term(&mut context, "(mkRec #x07)").unwrap();
    let bare = term(&mut context, "(ordinary (mkRec #x07))").unwrap();
    let qualified = term(&mut context, "((as ordinary (_ BitVec 8)) (mkRec #x07))").unwrap();
    assert_eq!(qualified, bare);
    let TermData::App(head, args) = context.terms.get(qualified) else {
        panic!("ordinary unary functions have no selector authority");
    };
    assert_eq!(head.name(), "ordinary");
    assert_eq!(args.as_slice(), &[input]);
    let field = term(&mut context, "#x07").unwrap();
    assert_ne!(qualified, field);
}
