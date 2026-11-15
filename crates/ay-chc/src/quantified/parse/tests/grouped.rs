// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn direct_group_preserves_order_sorts_and_both_array_read_indices() {
    let source = parsed(
        "(declare-var a (Array (_ BitVec 1) (_ BitVec 2)))
         (declare-var b (Array (_ BitVec 2) (_ BitVec 2)))
         (declare-rel P ((Array (_ BitVec 1) (_ BitVec 2)) (Array (_ BitVec 2) (_ BitVec 2))))
         (declare-rel error ())
         (rule (=> (forall ((r (_ BitVec 1)) (c (_ BitVec 2)))
                     (= (select a r) (select b c))) (P a b)))
         (query error)",
    );
    let premise = &source.premises()[0][0];
    let binders: Vec<_> = premise.binders().collect();
    assert_eq!(binders.len(), 2);
    assert_eq!(binders[0].sort, ChcSort::BitVec(1));
    assert_eq!(binders[1].sort, ChcSort::BitVec(2));
    assert_ne!(binders[0].name, binders[1].name);
    let ChcExpr::Op(ChcOp::Eq, equality) = premise.matrix() else {
        panic!("raw equality")
    };
    for (read, binder) in equality.iter().zip(&binders) {
        let ChcExpr::Op(ChcOp::Select, arguments) = read.as_ref() else {
            panic!("read")
        };
        assert!(matches!(arguments[1].as_ref(), ChcExpr::Var(actual) if actual == *binder));
    }
    assert_eq!(source.premises()[0].len(), 1);
    assert_eq!(source.source_smtlib().matches("(forall").count(), 2);
}

#[test]
fn simultaneous_let_aliases_survive_both_shadowing_group_binders() {
    let source = parsed(
        "(declare-var r (_ BitVec 2))(declare-var c (_ BitVec 2))
         (declare-rel P ((_ BitVec 2) (_ BitVec 2)))(declare-rel error ())
         (rule (let ((r #b00) (saved_r r) (saved_c c))
           (=> (forall ((r (_ BitVec 2)) (c (_ BitVec 2)))
                 (and (= r saved_r) (= c saved_c))) (P saved_r saved_c))))
         (query error)",
    );
    let premise = &source.premises()[0][0];
    let binders: Vec<_> = premise.binders().collect();
    let ClauseHead::Predicate(_, outer) = &source.source_problem().clauses()[0].head else {
        panic!("P head")
    };
    let ChcExpr::Op(ChcOp::And, equalities) = premise.matrix() else {
        panic!("raw conjunction")
    };
    for ((equality, binder), outer) in equalities.iter().zip(binders).zip(outer) {
        let ChcExpr::Op(ChcOp::Eq, args) = equality.as_ref() else {
            panic!("raw equality")
        };
        assert!(matches!(args[0].as_ref(), ChcExpr::Var(actual) if actual == binder));
        assert_eq!(args[1].as_ref(), outer);
        assert!(matches!(outer, ChcExpr::Var(var) if var.name != binder.name));
    }
}

#[test]
fn repeated_group_aliases_remain_distinct_complete_premises() {
    let source = parsed(
        "(declare-rel P ())(declare-rel error ())
         (rule (let ((joint (forall ((r (_ BitVec 1)) (c (_ BitVec 1))) (= r c))))
                   (=> (and joint joint) P)))
         (query error)",
    );
    let groups = &source.premises()[0];
    assert_eq!(groups.len(), 2);
    assert_eq!(groups[0].binder_count(), 2);
    assert_eq!(
        groups[0].binders().collect::<Vec<_>>(),
        groups[1].binders().collect::<Vec<_>>()
    );
    assert_eq!(groups[0].matrix(), groups[1].matrix());
    assert_eq!(source.source_smtlib().matches("(forall").count(), 2);
    assert!(source.source_smtlib().contains("(and (forall"));
}

#[test]
fn grouped_admission_has_exact_eight_bound_and_preserves_other_refusals() {
    let script = |binders: &str| {
        format!(
            "(declare-rel P ())(declare-rel error ())
         (rule (=> (forall ({binders}) true) P))(query error)"
        )
    };
    let eight = (0..8)
        .map(|i| format!("(i{i} (_ BitVec 64))"))
        .collect::<Vec<_>>()
        .join(" ");
    assert_eq!(parsed(&script(&eight)).premises()[0][0].binder_count(), 8);
    for binders in [
        String::new(),
        format!("{eight} (ninth (_ BitVec 64))"),
        "(i (_ BitVec 1)) (i (_ BitVec 1))".into(),
        "(i (_ BitVec 1)) (i (_ BitVec 2))".into(),
        "(i (_ BitVec 1)) (j Bool)".into(),
        "(i (_ BitVec 1)) (j (_ BitVec 65))".into(),
        "(i (_ BitVec 1)) (j (Array (_ BitVec 1) Bool))".into(),
    ] {
        assert!(matches!(
            QuantifiedChcProblem::parse_smtlib(&script(&binders)),
            Err(ChcError::Parse(_))
        ));
    }
    let nested_arrays =
        "(declare-var a (Array (_ BitVec 1) (Array (_ BitVec 1) (Array (_ BitVec 1) Bool))))
        (declare-rel error ())(query error)";
    assert!(QuantifiedChcProblem::parse_smtlib(nested_arrays).is_err());
    assert_eq!(parsed(&script(&eight)).premises()[0][0].binder_count(), 8);
}

#[test]
fn grouped_canonical_roundtrip_keeps_joint_scope_and_raw_query_positions() {
    let source = parsed(
        "(declare-fun P () Bool)
         (assert (=> (forall ((i (_ BitVec 1)) (j (_ BitVec 2))) (= j #b00)) P))
         (assert (=> false false))
         (assert (=> (and P (forall ((x (_ BitVec 2)) (y (_ BitVec 1))) (= x #b01))) false))
         (check-sat)",
    );
    let roundtrip = parsed(source.source_smtlib());
    assert_eq!(roundtrip.source_problem().clauses().len(), 3);
    assert_eq!(roundtrip.source_problem().pruned_false_query_count(), 0);
    assert_eq!(
        roundtrip.source_problem().clauses()[1].source_query_ordinal,
        Some(0)
    );
    assert_eq!(
        roundtrip.source_problem().clauses()[2].source_query_ordinal,
        Some(1)
    );
    for (before, after) in source.premises().iter().zip(roundtrip.premises()) {
        assert_eq!(before.len(), after.len());
        for (before, after) in before.iter().zip(after) {
            assert_eq!(
                before.binders().map(|b| &b.sort).collect::<Vec<_>>(),
                after.binders().map(|b| &b.sort).collect::<Vec<_>>()
            );
        }
    }
    assert_eq!(roundtrip.source_smtlib().matches("(forall").count(), 2);
}
