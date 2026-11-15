// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![cfg(test)]

use super::*;

mod resources;

fn wrapper() -> &'static str {
    "(declare-datatype Wrapper ((mkWrapper (items Vec) (tag Bool))))"
}

fn script(declarations: &str) -> String {
    format!(
        "{declarations}
        (declare-var w Wrapper)(declare-var out Wrapper)
        (declare-var fresh_data (Array (_ BitVec 64) (_ BitVec 8)))
        (declare-var new (_ BitVec 64))(declare-var fill (_ BitVec 8))
        (declare-rel P (Wrapper))(declare-rel error ())
        (rule (=> (and
          (forall ((i (_ BitVec 64)))
            (and (=> (bvult i (fld_len (items w)))
                     (= (select fresh_data i) (select (fld_data (items w)) i)))
                 (=> (and (bvuge i (fld_len (items w))) (bvult i new))
                     (= (select fresh_data i) fill))))
          (= out (mkWrapper
             (mkVec (fld_ptr (items w)) new (fld_cap (items w)) fresh_data)
             (tag w)))) (P out)))
        (query error)"
    )
}

#[test]
fn nested_struct_resize_retains_selector_chain_constructor_and_original_sibling() {
    let input = script(&format!("{}{}", fixtures::record(), wrapper()));
    let problem = parsed(&input);
    let fields = &problem.source_problem().datatype_defs()["Wrapper"][0].1;
    assert_eq!(fields[0].0, "items");
    assert!(matches!(&fields[0].1, ChcSort::Datatype { name, .. } if name == "Vec"));
    assert_eq!(fields[1], ("tag".into(), ChcSort::Bool));
    let premise = &problem.premises()[0][0];
    let matrix = crate::InvariantModel::expr_to_smtlib(premise.matrix());
    assert!(matrix.contains("(fld_len ((as items Vec) w))"));
    assert!(matrix.contains("(select (fld_data ((as items Vec) w))"));
    let constraint = problem.source_problem().clauses()[0]
        .body
        .constraint
        .as_ref()
        .unwrap();
    let text = crate::InvariantModel::expr_to_smtlib(constraint);
    assert!(text.contains("((as mkWrapper Wrapper) ((as mkVec Vec)"));
    assert!(text.contains("fresh_data) (tag w)"));
    let roundtrip = parsed(problem.source_smtlib());
    assert_eq!(
        roundtrip.source_problem().datatype_defs(),
        problem.source_problem().datatype_defs()
    );
    assert_eq!(roundtrip.premises()[0].len(), 1);
    assert_eq!(roundtrip.source_problem().clauses().len(), 2);
}

#[test]
fn simultaneous_forward_references_match_dependency_ordered_declarations() {
    let group = "(declare-datatypes ((Wrapper 0) (Vec 0))
        (((mkWrapper (items Vec) (tag Bool)))
         ((mkVec (fld_ptr (_ BitVec 64)) (fld_len (_ BitVec 64))
                 (fld_cap (_ BitVec 64))
                 (fld_data (Array (_ BitVec 64) (_ BitVec 8)))))))";
    let sequential = parsed(&script(&format!("{}{}", fixtures::record(), wrapper())));
    let forward = parsed(&script(group));
    assert_eq!(sequential.source_smtlib(), forward.source_smtlib());
    // Sharing a child declaration in two field positions is not recursion;
    // duplicate dependency edges must not trigger an active-stack false cycle.
    let diamond = parsed(
        "(declare-datatypes ((Top 0) (Left 0) (Right 0) (Leaf 0))
        (((top (left Left) (right Right))) ((left_mk (value Leaf)))
         ((right_mk (value Leaf))) ((leaf (flag Bool)))))
        (declare-rel error ())(query error)",
    );
    assert_eq!(diamond.source_problem().datatype_defs().len(), 4);
}

#[test]
fn cycles_undeclared_sorts_and_unsupported_nested_leaves_refuse_the_whole_group() {
    for declarations in [
        "(declare-datatype A ((a (self A))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (next B))) ((b (next A)))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (next B))) ((b (next Missing)))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (next B))) ((b (x Int)))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (next B))) ((b (x (_ BitVec 1048577))))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (next B))) ((b0 (x Bool)) (b1 (y Bool)))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (data (Array Bool B)))) ((b (x Bool)))))",
        "(declare-datatype A ((a (next B))))(declare-datatype B ((b (x Bool))))",
    ] {
        fixtures::refuses(&format!(
            "{declarations}(declare-rel error ())(query error)"
        ));
    }
    let group = "(declare-datatypes ((A 0) (B 0)) (((a (next B))) ((b (flag Bool)))))";
    assert_eq!(
        parsed(&format!("{group}(declare-rel error ())(query error)"))
            .source_problem()
            .datatype_defs()
            .len(),
        2
    );
}

#[test]
fn qualified_nested_selectors_authenticate_result_sort_and_lexical_scope() {
    let declarations = format!("{}{}", fixtures::record(), wrapper());
    let source = parsed(&format!(
        "{declarations}(declare-fun P (Vec) Bool)
        (assert (forall ((w Wrapper)) (let ((saved ((as items Vec) w)))
          (forall ((w Wrapper)) (=> (= (fld_len saved) (fld_len (items w))) (P saved))))))
        (assert false)(check-sat)"
    ));
    let clause = &source.source_problem().clauses()[0];
    let Some(ChcExpr::Op(ChcOp::Eq, equality)) = &clause.body.constraint else {
        panic!("retained equality")
    };
    let left = equality[0].vars();
    let right = equality[1].vars();
    assert_eq!(left.len(), 1);
    assert_eq!(right.len(), 1);
    assert_ne!(left[0].name, right[0].name);
    for expr in [
        "((as items Wrapper) w)",
        "((as unknown Vec) w)",
        "(let ((items true)) ((as items Vec) w))",
    ] {
        fixtures::refuses(&format!(
            "{declarations}(declare-var w Wrapper)(declare-rel error ())
            (rule (let ((unused {expr})) error))(query error)"
        ));
    }
}
