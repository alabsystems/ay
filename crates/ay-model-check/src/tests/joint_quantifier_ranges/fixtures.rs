// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

fn bv(value: u64) -> ModelValue {
    ModelValue::bitvec(BigInt::from(value), 64)
}

fn assert_bv(outcome: EvalOutcome, expected: u64) {
    assert!(matches!(
        outcome,
        EvalOutcome::Value(ModelValue::BitVec { value, width: 64 })
            if value == BigInt::from(expected)
    ));
}

fn cells(default: bool, changes: &[(u64, bool)]) -> ModelValue {
    ModelValue::Array(Box::new(ArrayValue {
        default: ModelValue::Bool(default),
        store: changes
            .iter()
            .map(|(index, value)| (bv(*index), ModelValue::Bool(*value)))
            .collect(),
    }))
}

fn row_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "JointRow",
        vec![DatatypeConstructor::new(
            "mkJointRow",
            vec![
                DatatypeField::new("row_len", Sort::bitvec(64)),
                DatatypeField::new("row_data", Sort::array(Sort::bitvec(64), Sort::Bool)),
            ],
        )],
    ))
}

fn outer_sort() -> Sort {
    Sort::Datatype(DatatypeSort::new(
        "JointOuter",
        vec![DatatypeConstructor::new(
            "mkJointOuter",
            vec![
                DatatypeField::new("outer_len", Sort::bitvec(64)),
                DatatypeField::new("outer_data", Sort::array(Sort::bitvec(64), row_sort())),
            ],
        )],
    ))
}

fn row(len: u64, data: ModelValue) -> ModelValue {
    ModelValue::Datatype {
        ctor: "mkJointRow".to_string(),
        args: vec![bv(len), data],
    }
}

fn outer(len: u64, default: ModelValue, rows: Vec<(u64, ModelValue)>) -> ModelValue {
    ModelValue::Datatype {
        ctor: "mkJointOuter".to_string(),
        args: vec![
            bv(len),
            ModelValue::Array(Box::new(ArrayValue {
                default,
                store: rows
                    .into_iter()
                    .map(|(index, row)| (bv(index), row))
                    .collect(),
            })),
        ],
    }
}

fn bindings() -> Vec<(String, Sort)> {
    vec![
        ("r".to_string(), Sort::bitvec(64)),
        ("c".to_string(), Sort::bitvec(64)),
    ]
}

fn quantified_pair(terms: &mut TermStore, guard: TermId, property: TermId) -> (TermId, TermId) {
    let all = app(terms, "=>", &[guard, property], Sort::Bool);
    let bad = terms.mk_not(property);
    let some_bad = app(terms, "and", &[guard, bad], Sort::Bool);
    (
        terms.mk_forall(bindings(), all),
        terms.mk_exists(bindings(), some_bad),
    )
}

struct Matrix {
    outer: TermId,
    r: TermId,
    c: TermId,
    guard: TermId,
    read: TermId,
    all: TermId,
    some_bad: TermId,
}

// Authored composition of the producer's Vec selector/array vocabulary, not
// a claim that MODEL_CHECKER_CONSUMER exported this exact grouped two-binder formula.
fn matrix(terms: &mut TermStore) -> Matrix {
    let outer = terms.mk_var("outer", outer_sort());
    let r = terms.mk_var("r", Sort::bitvec(64));
    let c = terms.mk_var("c", Sort::bitvec(64));
    let len = app(terms, "outer_len", &[outer], Sort::bitvec(64));
    let data = app(
        terms,
        "outer_data",
        &[outer],
        Sort::array(Sort::bitvec(64), row_sort()),
    );
    let selected_row = app(terms, "select", &[data, r], row_sort());
    let row_len = app(terms, "row_len", &[selected_row], Sort::bitvec(64));
    let row_data = app(
        terms,
        "row_data",
        &[selected_row],
        Sort::array(Sort::bitvec(64), Sort::Bool),
    );
    let read = app(terms, "select", &[row_data, c], Sort::Bool);
    let r_bound = app(terms, "bvult", &[r, len], Sort::Bool);
    let c_bound = app(terms, "bvult", &[c, row_len], Sort::Bool);
    let guard = app(terms, "and", &[r_bound, c_bound], Sort::Bool);
    let (all, some_bad) = quantified_pair(terms, guard, read);
    Matrix {
        outer,
        r,
        c,
        guard,
        read,
        all,
        some_bad,
    }
}

fn matrix_value(bad: bool) -> ModelValue {
    outer(
        3,
        row(0, cells(false, &[])),
        vec![
            (0, row(2, cells(true, &[(2, false)]))),
            // No cell of this row is in scope, despite its false default.
            (1, row(0, cells(false, &[]))),
            (2, row(3, cells(true, &[(1, !bad), (3, false)]))),
            (3, row(1, cells(false, &[]))),
        ],
    )
}
