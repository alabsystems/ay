// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn record_declaration_shapes_and_field_theories_refuse_without_unused_definition_bypass() {
    for declaration in [
        "(declare-datatype A ((a)))",
        "(declare-datatype A ((a (x Bool)) (b (y Bool))))",
        "(declare-datatype A ((a (x A))))",
        "(declare-datatype A ((a (x Int))))",
        "(declare-datatype A ((a (x (_ BitVec 1048577)))))",
        "(declare-datatype A ((a (x (Array Bool Bool)))))",
        "(declare-datatype A ((a (x (Array (_ BitVec 8) (Array (_ BitVec 8) (Array (_ BitVec 8) Bool)))))))",
        "(declare-datatype A ((a (x Bool) (x Bool))))",
        "(declare-datatype A ((a (a Bool))))",
        "(declare-datatypes ((A 1)) (((a (x Bool)))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (x Bool)))))",
        "(declare-datatypes ((A 0) (A 0)) (((a (x Bool))) ((b (y Bool)))))",
        "(declare-datatype A ((a (x Bool))))(declare-var a Bool)",
        "(declare-var x Bool)(declare-datatype A ((a (x Bool))))",
    ] {
        fixtures::refuses(&format!("{declaration}(declare-rel error ())(query error)"));
    }
    fixtures::refuses(
        "(declare-rel error ())(rule error)(declare-datatype A ((a (x Bool))))(query error)",
    );
}

#[test]
fn malformed_record_operations_refuse_even_in_unused_let_rhs() {
    for expression in [
        "(mkVec)",
        "(mkVec true true true true)",
        "(fld_len)",
        "(fld_len #x00)",
        "(fld_len v v)",
        "(unknown_field v)",
        "(= v #x00)",
        "(ite #x00 v v)",
        "(ite true v #x00)",
        "(bvadd v v)",
        "(select v #x00)",
        "((_ is mkVec) v)",
        "((as fld_len Vec) v)",
        "((as mkVec Bool) (_ bv0 64) (_ bv0 64) (_ bv0 64) (fld_data v))",
        "((as unknown Vec) (_ bv0 64))",
        "((as const (Array (_ BitVec 8) (Array (_ BitVec 8) Vec))) v)",
    ] {
        fixtures::refuses(&format!(
            "{}(declare-var v Vec)(declare-rel error ())
            (rule (let ((unused {expression})) error))(query error)",
            fixtures::record()
        ));
    }
    fixtures::refuses(&format!(
        "{}(declare-var a (Array (_ BitVec 8) (Array (_ BitVec 8) Vec)))
        (declare-rel error ())(query error)",
        fixtures::record()
    ));
    fixtures::refuses(&format!(
        "{}(declare-var v Vec)(declare-rel error ())
        (rule (=> (forall ((w Vec)) (= w v)) error))(query error)",
        fixtures::record()
    ));
}

fn group(count: usize) -> String {
    let names = (0..count)
        .map(|n| format!("(R{n} 0)"))
        .collect::<Vec<_>>()
        .join(" ");
    let definitions = (0..count)
        .map(|n| format!("((mkR{n} (field{n} Bool)))"))
        .collect::<Vec<_>>()
        .join(" ");
    format!("(declare-datatypes ({names}) ({definitions}))(declare-rel error ())(query error)")
}

#[test]
fn record_count_and_field_budgets_refuse_atomically_with_fresh_retry() {
    let count = crate::quantified::records::MAX_RECORDS;
    assert_eq!(
        parsed(&group(count)).source_problem().datatype_defs().len(),
        count
    );
    assert!(
        matches!(QuantifiedChcProblem::parse_smtlib(&group(count + 1)),
        Err(ChcError::Parse(message)) if message.contains("record declaration group size"))
    );
    let fields = (0..=crate::quantified::records::MAX_FIELDS)
        .map(|n| format!("(field{n} Bool)"))
        .collect::<Vec<_>>()
        .join(" ");
    let input = format!("(declare-datatype A ((mkA {fields})))(declare-rel error ())(query error)");
    assert!(matches!(QuantifiedChcProblem::parse_smtlib(&input),
        Err(ChcError::Parse(message)) if message.contains("record field count limit")));
    assert_eq!(parsed(&group(1)).source_problem().datatype_defs().len(), 1);
}

#[test]
fn aggregate_record_names_are_debited_before_the_second_definition_is_owned() {
    // Each spelling fits lexical admission; the aggregate source registry cap
    // is independent of the 8 MiB script and 32 MiB parser-copy allowances.
    let declarations = (0..2)
        .map(|record| {
            let fields = (0..64)
                .map(|field| format!("(f{record}_{field}_{} Bool)", "n".repeat(9_000)))
                .collect::<Vec<_>>()
                .join(" ");
            format!("(declare-datatype R{record} ((mkR{record} {fields})))")
        })
        .collect::<Vec<_>>()
        .join(" ");
    let input = format!("{declarations}(declare-rel error ())(query error)");
    super::super::super::preflight::check(&input).expect("lexically bounded input");
    assert!(matches!(QuantifiedChcProblem::parse_smtlib(&input),
        Err(ChcError::Parse(message)) if message.contains("record metadata limit")));
    assert_eq!(parsed(&group(1)).source_problem().datatype_defs().len(), 1);
}
