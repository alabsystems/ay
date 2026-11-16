// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct Fixture {
    pub exec: Executor,
    pub rows: TermId,
    pub outer: TermId,
    pub row: TermId,
    pub empty: TermId,
    pub row_sort: Sort,
    pub rows_sort: Sort,
    pub row_ctor: String,
    pub outer_ctor: String,
}

pub(super) fn app(exec: &mut Executor, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    exec.ctx
        .terms
        .mk_app(Symbol::Named(name.into()), args, sort)
}

pub(super) fn word(value: u64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: value.into(),
        width,
    }
}

pub(super) fn fixture() -> Fixture {
    let mut exec = Executor::new();
    let commands = ay_frontend::parse(
        "(set-logic ALL)
        (declare-datatype Row ((row (len (_ BitVec 64))
          (data (Array (_ BitVec 64) (_ BitVec 8))))))
        (declare-datatype Outer ((outer (rows (Array (_ BitVec 64) Row)))))",
    )
    .unwrap();
    assert_eq!(exec.execute_all(&commands).unwrap(), [] as [String; 0]);
    let info = exec.ctx.exact_datatype_member_info("row").unwrap();
    let row_sort = info.sort.clone();
    let row_ctor = exec.ctx.symbol_identity_name("row", info).to_string();
    let info = exec.ctx.exact_datatype_member_info("outer").unwrap();
    let outer_sort = info.sort.clone();
    let outer_ctor = exec.ctx.symbol_identity_name("outer", info).to_string();
    let bytes_sort = Sort::array(Sort::bitvec(64), Sort::bitvec(8));
    let rows_sort = Sort::array(Sort::bitvec(64), row_sort.clone());
    let zero8 = exec.ctx.terms.mk_bitvec(0.into(), 8);
    let seven = exec.ctx.terms.mk_bitvec(7.into(), 8);
    let nine = exec.ctx.terms.mk_bitvec(9.into(), 8);
    let zero64 = exec.ctx.terms.mk_bitvec(0.into(), 64);
    let key = exec.ctx.terms.mk_bitvec(33.into(), 64);
    let far_key = exec.ctx.terms.mk_bitvec(64.into(), 64);
    let length = exec.ctx.terms.mk_bitvec(65.into(), 64);
    let zeros = app(&mut exec, "const-array", vec![zero8], bytes_sort.clone());
    let sevens = app(&mut exec, "const-array", vec![seven], bytes_sort.clone());
    let bytes = app(&mut exec, "store", vec![sevens, far_key, nine], bytes_sort);
    let empty = app(&mut exec, &row_ctor, vec![zero64, zeros], row_sort.clone());
    let row = app(&mut exec, &row_ctor, vec![length, bytes], row_sort.clone());
    let base = app(&mut exec, "const-array", vec![empty], rows_sort.clone());
    let rows = app(&mut exec, "store", vec![base, key, row], rows_sort.clone());
    let outer = app(&mut exec, &outer_ctor, vec![rows], outer_sort);
    Fixture {
        exec,
        rows,
        outer,
        row,
        empty,
        row_sort,
        rows_sort,
        row_ctor,
        outer_ctor,
    }
}

pub(super) fn value(exec: &Executor, model: &Model, term: TermId) -> Option<ModelValue> {
    exec.exact_constructor_source_value(
        model,
        term,
        exec.ctx.terms.sort(term),
        &mut 0,
        &mut TypedArrayParseBudget::new(),
    )
}

pub(super) fn expected_row(ctor: &str, populated: bool) -> ModelValue {
    ModelValue::Datatype {
        ctor: ctor.into(),
        args: vec![
            word(if populated { 65 } else { 0 }, 64),
            ModelValue::Array(Box::new(ArrayValue {
                default: word(if populated { 7 } else { 0 }, 8),
                store: if populated {
                    vec![(word(64, 64), word(9, 8))]
                } else {
                    vec![]
                },
            })),
        ],
    }
}

pub(super) fn expected_rows(ctor: &str) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: expected_row(ctor, false),
        store: vec![(word(33, 64), expected_row(ctor, true))],
    }))
}

pub(super) fn same(left: &ModelValue, right: &ModelValue) -> bool {
    super::super::super::same_datatype_array_value(left, right)
}
