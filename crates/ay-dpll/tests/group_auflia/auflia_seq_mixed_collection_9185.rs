// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#![allow(clippy::panic)]

use ay_dpll::{
    ApiSolver as Solver, ApiSort as Sort, DatatypeConstructor, DatatypeField, DatatypeSort, Logic,
    UnknownReason,
};
use ntest::timeout;

#[test]
#[timeout(60_000)]
fn seq_array_row_conflict_uses_mixed_auflia_route() {
    let mut solver = Solver::try_new(Logic::QfAuflia).unwrap();

    let elem = solver.int_const(7);
    let unit = solver.try_seq_unit(elem).unwrap();
    let len = solver.try_seq_len(unit).unwrap();
    let one_len = solver.int_const(1);
    let len_is_one = solver.try_eq(len, one_len).unwrap();
    solver.try_assert_term(len_is_one).unwrap();

    let array_sort = Sort::array(Sort::Int, Sort::Int);
    let array = solver.declare_const("a", array_sort);
    let i = solver.declare_const("i", Sort::Int);
    let j = solver.declare_const("j", Sort::Int);
    let i_eq_j = solver.try_eq(i, j).unwrap();
    solver.try_assert_term(i_eq_j).unwrap();

    let stored_value = solver.int_const(1);
    let stored = solver.try_store(array, i, stored_value).unwrap();
    let read = solver.try_select(stored, j).unwrap();
    let expected = solver.int_const(1);
    let row_conflict = solver.try_neq(read, expected).unwrap();
    solver.try_assert_term(row_conflict).unwrap();

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat(),
        "Seq terms must not route the AUFLIA row conflict away from arrays: {details:?}"
    );
}

#[test]
#[timeout(60_000)]
fn seq_datatype_mixed_fragment_no_longer_reports_unsupported_collection() {
    let mut solver = Solver::try_new(Logic::All).unwrap();

    let option_int = DatatypeSort {
        name: "WorkerCSeqDatatypeOption".to_string(),
        constructors: vec![
            DatatypeConstructor {
                name: "None".to_string(),
                fields: vec![],
            },
            DatatypeConstructor {
                name: "Some".to_string(),
                fields: vec![DatatypeField {
                    name: "value".to_string(),
                    sort: Sort::Int,
                }],
            },
        ],
    };
    solver.try_declare_datatype(&option_int).unwrap();

    let x = solver.declare_const("x", Sort::Datatype(option_int.clone()));
    let zero = solver.int_const(0);
    let some_zero = solver
        .try_datatype_constructor(&option_int, "Some", &[zero])
        .unwrap();
    let x_is_some_zero = solver.try_eq(x, some_zero).unwrap();
    solver.try_assert_term(x_is_some_zero).unwrap();

    let seq = solver.declare_const("s", Sort::seq(Sort::Int));
    let seq_len = solver.try_seq_len(seq).unwrap();
    let zero_len = solver.int_const(0);
    let seq_len_zero = solver.try_eq(seq_len, zero_len).unwrap();
    solver.try_assert_term(seq_len_zero).unwrap();

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() || details.result.is_unknown(),
        "Seq+datatype mixed fragment should solve or fail closed after DT+Seq+AUFLIA routing: {details:?}"
    );
    assert_ne!(
        details.unknown_reason,
        Some(UnknownReason::UnsupportedMixedCollection)
    );
    assert_ne!(
        solver.unknown_reason(),
        Some(UnknownReason::UnsupportedMixedCollection)
    );
    assert_ne!(
        solver.reason_unknown_smtlib().as_deref(),
        Some("(unsupported mixed-collection)")
    );
    assert!(
        !details
            .statistics
            .extra
            .contains_key("mixed_vc.collection.unsupported_fragment"),
        "mixed collection route should not be rejected: {:?}",
        details.statistics.extra
    );
}

#[test]
#[timeout(60_000)]
fn unused_datatype_declaration_does_not_block_seq_route() {
    let mut solver = Solver::try_new(Logic::All).unwrap();

    let marker = DatatypeSort {
        name: "WorkerCUnusedDatatype".to_string(),
        constructors: vec![DatatypeConstructor {
            name: "Marker".to_string(),
            fields: vec![],
        }],
    };
    solver.try_declare_datatype(&marker).unwrap();

    let elem = solver.int_const(9);
    let unit = solver.try_seq_unit(elem).unwrap();
    let len = solver.try_seq_len(unit).unwrap();
    let one = solver.int_const(1);
    let len_is_one = solver.try_eq(len, one).unwrap();
    solver.try_assert_term(len_is_one).unwrap();

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat(),
        "unused datatype declarations should not trigger mixed collection unknown: {details:?}"
    );
    assert_ne!(
        details.unknown_reason,
        Some(UnknownReason::UnsupportedMixedCollection)
    );
}
