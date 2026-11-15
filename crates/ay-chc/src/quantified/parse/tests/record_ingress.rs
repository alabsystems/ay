// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod boundaries;
mod fixtures;
mod nested;
mod scopes;

#[test]
fn four_field_vec_resize_keeps_records_symbolic_guards_and_conditional_backing() {
    let problem = parsed(&fixtures::resize());
    let source = problem.source_problem();
    let fields = &source.datatype_defs()["Vec"][0].1;
    assert_eq!(
        fields
            .iter()
            .map(|(name, _)| name.as_str())
            .collect::<Vec<_>>(),
        vec!["fld_ptr", "fld_len", "fld_cap", "fld_data"]
    );
    assert_eq!(fields[0].1, ChcSort::BitVec(64));
    assert_eq!(
        fields[3].1,
        ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::BitVec(8)))
    );
    assert!(
        matches!(&source.predicates()[0].arg_sorts[0], ChcSort::Datatype { name, .. } if name == "Vec")
    );
    assert_eq!(source.clauses().len(), 3);
    assert_eq!(
        problem.premises().iter().map(Vec::len).collect::<Vec<_>>(),
        vec![1, 0, 0]
    );
    let premise = &problem.premises()[0][0];
    let matrix = crate::InvariantModel::expr_to_smtlib(premise.matrix());
    let index = &premise.binder().name;
    assert!(matrix.contains(&format!("(bvult {index} (fld_len v))")));
    assert!(matrix.contains(&format!("(bvuge {index} (fld_len v))")));
    assert!(matrix.contains(&format!("(bvult {index} new)")));
    assert!(matrix.contains(&format!("(select (fld_data v) {index})")));
    let text = crate::InvariantModel::expr_to_smtlib(
        source.clauses()[0].body.constraint.as_ref().unwrap(),
    );
    assert!(text.contains(
        "((as mkVec Vec) (fld_ptr v) new (fld_cap v) (ite (bvult (fld_len v) new) fresh_data (fld_data v)))"
    ));
    assert!(text.starts_with("(= out ((as mkVec Vec)"));
    let query = crate::InvariantModel::expr_to_smtlib(
        source.clauses()[1].body.constraint.as_ref().unwrap(),
    );
    assert!(query.contains("(select (fld_data out) j)"));
    assert!(query.contains("(_ bv32 64)"));
    assert!(!source.has_stripped_body_forall());
    let roundtrip = parsed(problem.source_smtlib());
    assert_eq!(
        roundtrip.source_problem().datatype_defs(),
        source.datatype_defs()
    );
    assert_eq!(roundtrip.source_problem().clauses().len(), 3);
    assert_eq!(roundtrip.premises()[0].len(), 1);
}

#[test]
fn declaration_groups_and_selector_overloads_resolve_full_record_signatures() {
    let problem = parsed(
        "(declare-datatypes ((A 0) (B 0))
          (((mkA (payload (_ BitVec 8)))) ((mkB (payload Bool)))))
         (declare-var a A)(declare-var b B)(declare-rel error ())
         (rule (=> (and (= (payload a) #x07) (payload b)
                        (= a (ite true (mkA #x07) a))
                        (distinct b (mkB false))) error))
         (query error)",
    );
    let constraint = problem.source_problem().clauses()[0]
        .body
        .constraint
        .as_ref()
        .unwrap();
    let text = crate::InvariantModel::expr_to_smtlib(constraint);
    assert!(text.contains("(payload a)"));
    assert!(text.contains("(payload b)"));
    assert!(text.contains("(ite true ((as mkA A) (_ bv7 8)) a)"));
    let ChcExpr::Op(ChcOp::And, parts) = constraint else {
        panic!("raw conjunction")
    };
    let ChcExpr::Op(ChcOp::Eq, equality) = parts[0].as_ref() else {
        panic!("BV equality")
    };
    assert!(
        matches!(equality[0].as_ref(), ChcExpr::FuncApp(name, ChcSort::BitVec(8), _) if name == "payload")
    );
    assert!(
        matches!(parts[1].as_ref(), ChcExpr::FuncApp(name, ChcSort::Bool, _) if name == "payload")
    );
}

#[test]
fn unused_record_definitions_are_part_of_canonical_source_identity() {
    let baseline = parsed("(declare-rel error ())(query error)");
    let with_record = parsed(&format!(
        "{}(declare-rel error ())(query error)",
        fixtures::record()
    ));
    assert_ne!(baseline.source_smtlib(), with_record.source_smtlib());
    for declaration in [
        fixtures::record().replace("fld_cap (_ BitVec 64)", "fld_cap (_ BitVec 32)"),
        fixtures::record().replace("mkVec", "otherVec"),
        fixtures::record().replace("fld_cap", "other_cap"),
    ] {
        let changed = parsed(&format!("{declaration}(declare-rel error ())(query error)"));
        assert_ne!(with_record.source_smtlib(), changed.source_smtlib());
    }
    let decorated = parsed(&format!(
        "; same declaration\n{}\n(declare-rel error ())(query error)",
        fixtures::record()
    ));
    assert_eq!(with_record.source_smtlib(), decorated.source_smtlib());
}
