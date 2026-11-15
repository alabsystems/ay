// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

#[test]
fn projection_renames_every_group_binder_without_capturing_fields_or_outer_names() {
    let original = QuantifiedChcProblem::parse_smtlib(
        "(declare-datatype R ((mkR (flag Bool) (data (Array (_ BitVec 8) Bool)))))
         (declare-var r R)(declare-var i (_ BitVec 8))
         (declare-var ay!record!2 (_ BitVec 8))
         (declare-rel P (R (_ BitVec 8) (_ BitVec 8)))(declare-rel error ())
         (rule (=> (forall ((i (_ BitVec 8)) (j (_ BitVec 8)) (unused (_ BitVec 8)))
           (= (select (data r) i) (select (data r) j))) (P r i ay!record!2)))
         (query error)",
    )
    .unwrap();
    let token = CancellationToken::new();
    let control = SourceControl::new(deadline(), &token);
    let projection = RecordProjection::new(&original, &control).unwrap();
    let projected = projection.project(&original, &control).unwrap();
    let original_group = &original.premises()[0][0];
    let group = &projected.premises()[0][0];
    assert_eq!(group.binder_count(), 3);
    let binders: Vec<_> = group.binders().collect();
    for (index, binder) in binders.iter().enumerate() {
        assert!(!original_group.binders().any(|old| old.name == binder.name));
        assert!(!["i", "ay!record!2"].contains(&binder.name.as_str()));
        assert!(binders[..index]
            .iter()
            .all(|other| other.name != binder.name));
    }
    let ClauseHead::Predicate(_, args) = &projected.source_problem().clauses()[0].head else {
        panic!("projected head")
    };
    assert_eq!(args.len(), 4);
    assert!(matches!(&args[2], ChcExpr::Var(var) if var.name == "i"));
    assert!(matches!(&args[3], ChcExpr::Var(var) if var.name == "ay!record!2"));
    let ChcExpr::Op(ChcOp::Eq, sides) = group.matrix() else {
        panic!("matrix equality")
    };
    for (side, binder) in sides.iter().zip(&binders[..2]) {
        let ChcExpr::Op(ChcOp::Select, read) = side.as_ref() else {
            panic!("matrix read")
        };
        assert_eq!(read[0].as_ref(), &args[1]);
        assert!(matches!(read[1].as_ref(), ChcExpr::Var(var) if var == *binder));
    }
    assert_eq!(projected.premises()[1].len(), 0);
}
