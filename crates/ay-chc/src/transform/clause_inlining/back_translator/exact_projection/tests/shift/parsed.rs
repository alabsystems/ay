// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn parsed_division_rules_reach_projection_as_correlated_logical_shifts() {
    let input = r#"
        (set-logic HORN)
        (declare-var x (_ BitVec 4))
        (declare-var a (_ BitVec 4))
        (declare-var b (_ BitVec 4))
        (declare-var flag Bool)
        (declare-rel observed ((_ BitVec 4) (_ BitVec 4) Bool))
        (rule (=> (and (= a (bvudiv x #x2))
                       (= (bvudiv x #x2) b) flag)
                  (observed a b flag)))
        (query observed)
    "#;
    let problem = crate::ChcParser::parse(input).unwrap();
    let clause = &problem.clauses()[0];
    assert!(clause.body.predicates.is_empty());
    let formula = clause.body.constraint.as_ref().unwrap();
    assert_eq!(operation_count(formula, ChcOp::BvUDiv), 0);
    assert_eq!(operation_count(formula, ChcOp::BvLShr), 2);
    let crate::ClauseHead::Predicate(_, args) = &clause.head else {
        panic!("parsed fact head")
    };
    let keep: Vec<_> = args
        .iter()
        .map(|arg| {
            let ChcExpr::Var(var) = arg else {
                panic!("plain parsed formal")
            };
            var.clone()
        })
        .collect();
    let projected = closed(formula, &keep);
    for a in 0..16 {
        for b in 0..16 {
            for flag in 0..2 {
                let expected = (0..16).any(|x| a == x / 2 && b == x / 2 && flag == 1);
                assert_eq!(
                    oracle::truth(&projected, &[("a", a), ("b", b), ("flag", flag)]),
                    expected
                );
            }
        }
    }
}
