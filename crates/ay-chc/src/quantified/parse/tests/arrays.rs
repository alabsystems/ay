// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
#![cfg(test)]

use super::*;

fn declarations() -> &'static str {
    "(declare-datatypes ((Outer 0) (|Inner cell| 0))
      (((mkOuter (cells (Array (_ BitVec 64) |Inner cell|))))
       ((|mk inner| (len (_ BitVec 64)) (data (Array (_ BitVec 64) (_ BitVec 8)))))))"
}

#[test]
fn array_wrapped_forward_records_and_both_select_axes_remain_in_source() {
    let source = parsed(&format!(
        "{}(declare-var outer Outer)(declare-var replacement |Inner cell|)
         (declare-var fresh (Array (_ BitVec 64) |Inner cell|))
         (declare-var fill (_ BitVec 8))(declare-var condition Bool)
         (declare-rel P (Outer (_ BitVec 8)))(declare-rel error ())
         (rule (=> (and
           (= (cells outer) (store fresh (_ bv33 64)
               (ite condition replacement (|mk inner| (_ bv64 64)
                  ((as const (Array (_ BitVec 64) (_ BitVec 8))) fill)))))
           (forall ((row (_ BitVec 64)) (column (_ BitVec 64)))
             (= (select (data (select (cells outer) row)) column) fill)))
           (P outer fill)))
         (query error)",
        declarations()
    ));
    assert_eq!(source.source_problem().datatype_defs().len(), 2);
    let premise = &source.premises()[0][0];
    assert_eq!(premise.binder_count(), 2);
    let text = source.source_smtlib();
    assert!(text.contains("(cells (Array (_ BitVec 64) |Inner cell|))"));
    assert!(text.contains("(store fresh (_ bv33 64) (ite condition replacement"));
    let indices: Vec<_> = premise.binders().map(|v| v.name.as_str()).collect();
    assert!(text.contains(&format!(
        "(select (data (select (cells outer) {})) {})",
        indices[0], indices[1]
    )));
    assert!(text.contains("((as const (Array (_ BitVec 64) (_ BitVec 8))) fill)"));
    let roundtrip = parsed(text);
    assert_eq!(roundtrip.premises()[0][0].binder_count(), 2);
    assert_eq!(roundtrip.source_problem().clauses().len(), 2);
}

#[test]
fn constant_record_and_nested_scalar_arrays_use_declared_cell_sorts_without_folding() {
    let source = parsed(&format!(
        "{}(declare-var cell |Inner cell|)(declare-var fill (_ BitVec 8))
         (declare-rel P ((Array (_ BitVec 64) |Inner cell|)
            (Array (_ BitVec 1) (Array (_ BitVec 64) (_ BitVec 8)))))
         (declare-rel error ())
         (rule (P ((as const (Array (_ BitVec 64) |Inner cell|)) cell)
           ((as const (Array (_ BitVec 1) (Array (_ BitVec 64) (_ BitVec 8))))
             ((as const (Array (_ BitVec 64) (_ BitVec 8))) fill))))
         (query error)",
        declarations()
    ));
    let ClauseHead::Predicate(_, args) = &source.source_problem().clauses()[0].head else {
        panic!("P head")
    };
    assert!(
        matches!(&args[0], ChcExpr::ConstArray(ChcSort::BitVec(64), value)
        if matches!(value.as_ref(), ChcExpr::Var(var) if var.name == "cell"))
    );
    assert!(
        matches!(&args[1], ChcExpr::ConstArray(ChcSort::BitVec(1), value)
        if matches!(value.as_ref(), ChcExpr::ConstArray(ChcSort::BitVec(64), _)))
    );
    assert!(source
        .source_smtlib()
        .contains("((as const (Array (_ BitVec 64) |Inner cell|)) cell)"));
    // No record registry is needed for pure nested scalar arrays.
    let pure = parsed(
        "(declare-var a (Array (_ BitVec 1) (Array (_ BitVec 2) Bool)))
        (declare-var row (Array (_ BitVec 2) Bool))(declare-rel error ())
        (rule (=> (distinct (select (store a #b1 row) #b0) row) error))(query error)",
    );
    assert!(pure
        .source_smtlib()
        .contains("(distinct (select (store a (_ bv1 1) row) (_ bv0 1)) row)"));
}

#[test]
fn array_dependency_cycles_missing_cells_and_rank_three_refuse_atomically() {
    for declarations in [
        "(declare-datatype A ((a (next (Array (_ BitVec 8) A)))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (next (Array (_ BitVec 8) B)))) ((b (next A)))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (next (Array (_ BitVec 8) B)))) ((b (next Missing)))))",
        "(declare-datatype A ((a (data (Array (_ BitVec 8) (Array (_ BitVec 8) (Array (_ BitVec 8) Bool)))))))",
        "(declare-datatypes ((A 0) (B 0)) (((a (next (Array (_ BitVec 8) B)))) ((b (data (Array (_ BitVec 8) (Array (_ BitVec 8) Bool)))))))",
        "(declare-datatype A ((a (data (Array Bool Bool)))))",
        "(declare-datatype A ((a (data (Array (_ BitVec 8) Int)))))",
    ] {
        assert!(QuantifiedChcProblem::parse_smtlib(&format!("{declarations}(declare-rel error ())(query error)")).is_err());
    }
    assert!(QuantifiedChcProblem::parse_smtlib(&format!(
        "{}(declare-var too_deep (Array (_ BitVec 64) Outer))(declare-rel error ())(query error)",
        declarations()
    ))
    .is_err());
    let fresh = parsed(&format!(
        "{}(declare-rel error ())(query error)",
        declarations()
    ));
    assert_eq!(fresh.source_problem().datatype_defs().len(), 2);
}

#[test]
fn malformed_nested_operations_are_checked_even_in_unused_let_values() {
    for expression in [
        "(select a #b0)",
        "(store a (_ bv0 64) #x00)",
        "(store a (_ bv0 64) outer)",
        "(ite true a cell)",
        "(= a cell)",
        "((as const (Array (_ BitVec 64) |Inner cell|)) outer)",
        "((as const (Array (_ BitVec 64) |Inner cell|)) cell cell)",
        "((as const (Array (_ BitVec 64) Missing)) cell)",
        "(unknown_operation a)",
        "(bvadd a a)",
    ] {
        let input = format!(
            "{}(declare-var a (Array (_ BitVec 64) |Inner cell|))
            (declare-var cell |Inner cell|)(declare-var outer Outer)(declare-rel error ())
            (rule (let ((unused {expression})) error))(query error)",
            declarations()
        );
        assert!(
            QuantifiedChcProblem::parse_smtlib(&input).is_err(),
            "{expression}"
        );
    }
}

#[test]
fn array_cell_metadata_copy_limits_charge_before_clone_and_fresh_retry() {
    let source = parsed(&format!(
        "{}(declare-rel P ((Array (_ BitVec 64) |Inner cell|)))
        (declare-rel error ())(query error)",
        declarations()
    ));
    let sort = &source.source_problem().predicates()[0].arg_sorts[0];
    let bytes = crate::quantified::records::sort_bytes(sort).unwrap();
    let work = 1 + bytes / 64;
    let mut exact = Budget {
        bytes: MAX_COPY_BYTES - bytes,
        work: MAX_WORK - work,
    };
    assert!(exact.sort_copy(sort).is_ok());
    assert_eq!((exact.bytes, exact.work), (MAX_COPY_BYTES, MAX_WORK));
    for (bytes, work) in [(MAX_COPY_BYTES - bytes + 1, 0), (0, MAX_WORK - work + 1)] {
        assert!(Budget { bytes, work }.sort_copy(sort).is_err());
    }
    let mut fresh = Budget::default();
    assert!(fresh.sort_copy(sort).is_ok());
    assert_eq!((fresh.bytes, fresh.work), (bytes, work));
    let legacy = ChcSort::Array(Box::new(ChcSort::BitVec(64)), Box::new(ChcSort::Bool));
    let mut unchanged = Budget::default();
    assert!(unchanged.sort_copy(&legacy).is_ok());
    assert_eq!((unchanged.bytes, unchanged.work), (0, 0));
}
