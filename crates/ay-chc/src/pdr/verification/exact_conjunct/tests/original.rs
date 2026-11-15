// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact recorded original-clause implication, not full R29 acceptance.

use super::*;
use crate::{ChcParser, InvariantModel};
use sha2::{Digest, Sha256};

const INPUT: &str = include_str!("clause21.smt2");

pub(super) fn parse(input: &str) -> (ChcExpr, ChcExpr) {
    let declarations = input
        .lines()
        .filter(|line| line.starts_with("(declare-rel "))
        .collect::<Vec<_>>()
        .join("\n");
    let problem = ChcParser::parse(&format!("(set-logic HORN)\n{declarations}\n")).unwrap();
    // The capture contains both problem declarations and model definitions.
    // Supply each parser its own surface; in particular a declare-rel's sort
    // list is not a Spacer model wrapper. Preserve every definition/formula.
    let definitions = super::surface::model_definitions(input);
    let model = InvariantModel::parse_smtlib(&definitions, &problem).unwrap();
    let mut formulas = [ChcExpr::Bool(false), ChcExpr::Bool(false)];
    for (i, name) in ["captured_body", "captured_head"].into_iter().enumerate() {
        let id = problem.lookup_predicate(name).unwrap();
        let interpretation = model.get(&id).unwrap();
        assert_eq!(
            interpretation
                .vars
                .iter()
                .map(|var| var.sort.clone())
                .collect::<Vec<_>>(),
            problem.get_predicate(id).unwrap().arg_sorts
        );
        for variable in interpretation.formula.vars() {
            assert!(
                interpretation
                    .vars
                    .iter()
                    .any(|formal| { formal.name == variable.name && formal.sort == variable.sort }),
                "captured {name} contains undeclared or differently typed variable {variable:?}"
            );
        }
        formulas[i] =
            super::surface::restore_conjunct_occurrences(input, name, &interpretation.formula);
    }
    let [body, head] = formulas;
    (body, head)
}

fn conjuncts(expr: &ChcExpr) -> &[Arc<ChcExpr>] {
    match expr {
        ChcExpr::Op(ChcOp::And, args) => args,
        _ => panic!("original conjunction"),
    }
}

#[test]
fn r29_clause21_exact_capture_proves_all_69_original_head_conjuncts() {
    assert_eq!(INPUT.len(), 34_054);
    assert_eq!(
        format!("{:x}", Sha256::digest(INPUT.as_bytes())),
        "c4073a638f344719c84562386a87db062b5758435f1b1c507554d3004e87a631"
    );
    let expressions: Vec<_> = INPUT
        .lines()
        .filter(|line| line.starts_with("(and "))
        .collect();
    assert_eq!(expressions.len(), 2);
    assert_eq!(
        format!("{:x}", Sha256::digest(expressions[0].as_bytes())),
        "71492abbd9a195481393ac0f2f2d741646bcc300128f43dcf37c218c0ad90ec7"
    );
    assert_eq!(
        format!("{:x}", Sha256::digest(expressions[1].as_bytes())),
        "215420107fdd8a2c87f84330967a614375394a63cdf4e9ce7e4d6d20683b268f"
    );
    let (body, head) = parse(INPUT);
    assert_eq!(conjuncts(&body).len(), 67);
    assert_eq!(conjuncts(&head).len(), 69);
    assert_eq!(prove(&body, &head), Ok(true));
    // Check every original conclusion, not just the first failed array atom.
    for conjunct in conjuncts(&head) {
        assert_eq!(prove(&body, conjunct), Ok(true));
    }
}

#[test]
fn original_array_default_and_scalar_head_mutations_are_not_accepted() {
    let offset = INPUT.find("(define-fun captured_head").unwrap();
    let (prefix, head) = INPUT.split_at(offset);
    for (before, after) in [
        ("Bool)) true)", "Bool)) false)"),
        ("(_ bv42 32)", "(_ bv43 32)"),
    ] {
        let mutated = format!("{prefix}{}", head.replacen(before, after, 1));
        assert_ne!(mutated, INPUT);
        let (body, head) = parse(&mutated);
        assert_eq!(prove(&body, &head), Ok(false));
    }
}
