// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

pub(super) struct Fixture {
    pub exec: Executor,
    pub model: Model,
    pub receiver: TermId,
    pub length: TermId,
    pub stored: TermId,
    pub default: TermId,
    pub row_sort: Sort,
    pub row_ctor: String,
    pub len_name: String,
    pub source_classes: Vec<(TermId, Sort, ModelValue)>,
}

pub(super) fn app(exec: &mut Executor, name: &str, args: &[TermId], sort: Sort) -> TermId {
    exec.ctx
        .terms
        .mk_app(Symbol::named(name), args.to_vec(), sort)
}

fn member(exec: &Executor, name: &str) -> (String, Sort) {
    let info = exec.ctx.exact_datatype_member_info(name).unwrap();
    (
        exec.ctx.symbol_identity_name(name, info).to_string(),
        info.sort.clone(),
    )
}

pub(super) fn word(value: u64, width: u32) -> ModelValue {
    ModelValue::BitVec {
        value: value.into(),
        width,
    }
}

pub(super) fn row_value(ctor: &str, length: u64) -> ModelValue {
    ModelValue::Datatype {
        ctor: ctor.into(),
        args: vec![
            word(length, 64),
            ModelValue::Array(Box::new(ArrayValue {
                default: word(7, 8),
                store: vec![(word(64, 64), word(9, 8))],
            })),
        ],
    }
}

pub(super) fn fixture() -> Fixture {
    let mut exec = Executor::new();
    for command in ay_frontend::parse(
        "(set-logic ALL)
         (declare-datatype Row ((row (len (_ BitVec 64))
           (data (Array (_ BitVec 64) (_ BitVec 8))))))
         (declare-datatype Outer ((outer (rows (Array (_ BitVec 64) Row)))))",
    )
    .unwrap()
    {
        exec.ctx.process_command(&command).unwrap();
    }
    let (row_ctor, row_sort) = member(&exec, "row");
    let (outer_ctor, outer_sort) = member(&exec, "outer");
    let (len_name, _) = member(&exec, "len");
    let (data_name, bytes_sort) = member(&exec, "data");
    let (rows_name, rows_sort) = member(&exec, "rows");
    let zero8 = exec.ctx.terms.mk_bitvec(0.into(), 8);
    let seven = exec.ctx.terms.mk_bitvec(7.into(), 8);
    let nine = exec.ctx.terms.mk_bitvec(9.into(), 8);
    let zero64 = exec.ctx.terms.mk_bitvec(0.into(), 64);
    let key = exec.ctx.terms.mk_bitvec(33.into(), 64);
    let far_key = exec.ctx.terms.mk_bitvec(64.into(), 64);
    let length = exec.ctx.terms.mk_bitvec(65.into(), 64);
    let zeros = exec.ctx.terms.mk_const_array(Sort::bitvec(64), zero8);
    let sevens = exec.ctx.terms.mk_const_array(Sort::bitvec(64), seven);
    let bytes = app(
        &mut exec,
        "store",
        &[sevens, far_key, nine],
        bytes_sort.clone(),
    );
    let empty = app(&mut exec, &row_ctor, &[zero64, zeros], row_sort.clone());
    let row = app(&mut exec, &row_ctor, &[length, bytes], row_sort.clone());
    let base = exec.ctx.terms.mk_const_array(Sort::bitvec(64), empty);
    let rows = app(&mut exec, "store", &[base, key, row], rows_sort.clone());
    let outer = app(&mut exec, &outer_ctor, &[rows], outer_sort.clone());
    let rows = app(&mut exec, &rows_name, &[outer], rows_sort);
    let receiver = app(&mut exec, "select", &[rows, key], row_sort.clone());
    let length = app(&mut exec, &len_name, &[receiver], Sort::bitvec(64));
    let data = app(&mut exec, &data_name, &[receiver], bytes_sort);
    let stored = app(&mut exec, "select", &[data, far_key], Sort::bitvec(8));
    let default = app(&mut exec, "select", &[data, zero64], Sort::bitvec(8));
    // Author the complete class values independently of the interpreter under
    // test. A self-check-ok assignment must not leave constructor classes to
    // legacy scalar rendering, which cannot carry their array-valued fields.
    let empty_value = ModelValue::Datatype {
        ctor: row_ctor.clone(),
        args: vec![
            word(0, 64),
            ModelValue::Array(Box::new(ArrayValue {
                default: word(0, 8),
                store: vec![],
            })),
        ],
    };
    let populated_value = row_value(&row_ctor, 65);
    let outer_value = ModelValue::Datatype {
        ctor: outer_ctor,
        args: vec![ModelValue::Array(Box::new(ArrayValue {
            default: empty_value.clone(),
            store: vec![(word(33, 64), populated_value.clone())],
        }))],
    };
    let source_classes = vec![
        (empty, row_sort.clone(), empty_value),
        (row, row_sort.clone(), populated_value),
        (outer, outer_sort, outer_value),
    ];
    Fixture {
        exec,
        model: Model::empty(),
        receiver,
        length,
        stored,
        default,
        row_sort,
        row_ctor,
        len_name,
        source_classes,
    }
}

pub(super) fn requests(f: &Fixture) -> Vec<(String, TermId)> {
    vec![
        ("len".into(), f.length),
        ("stored".into(), f.stored),
        ("default".into(), f.default),
        ("len-again".into(), f.length),
    ]
}

pub(super) fn rendered(exec: &Executor, value: u64, width: u32) -> String {
    exec.format_gate_model_value(&word(value, width), &Sort::bitvec(width))
        .unwrap()
}

pub(super) fn assignment(term: TermId, value: String, coherent: bool) -> DtEgraphAssignment {
    let mut assignment = DtEgraphAssignment {
        dtm: ay_dt::DtModel::default(),
        class_value: Default::default(),
        class_fields: Default::default(),
        class_ctor: Default::default(),
        poisoned: Default::default(),
        diseq_incoherent: Default::default(),
        self_check_ok: coherent,
    };
    assignment.class_value.insert(term, value);
    if !coherent {
        assignment.poisoned.insert(term);
        assignment.diseq_incoherent.insert(term);
    }
    assignment
}
