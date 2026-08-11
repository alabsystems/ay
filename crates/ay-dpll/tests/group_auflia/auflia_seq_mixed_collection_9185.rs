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

/// Cross-theory model extraction can discover only after the LIA model is
/// merged that two rows of a Seq-returning UF have the same argument tuple.
/// The result tokens are opaque EUF representatives, so the collision repair
/// must unify them just as it does Array-result tokens instead of discarding
/// the otherwise-valid model as an unrepresentable compound conflict.
#[test]
#[timeout(60_000)]
fn seq_result_uf_rows_congruent_after_lia_merge_never_report_unsat() {
    let mut solver = Solver::try_new(Logic::Auflia).unwrap();
    let seq_sort = Sort::seq(Sort::Int);
    let push = solver
        .try_declare_fun(
            "seq_push_back",
            &[seq_sort.clone(), Sort::Int],
            seq_sort.clone(),
        )
        .unwrap();
    let len = solver
        .try_declare_fun("seq_len", std::slice::from_ref(&seq_sort), Sort::Int)
        .unwrap();

    // Keep the reducer on verification-consumer's quantified AUFLIA lane: its Seq carrier
    // is native, but all operations are UFs tied together by length axioms.
    let bound_seq = solver.fresh_var("seq_result_bound", seq_sort.clone());
    let bound_len = solver.try_apply(&len, &[bound_seq]).unwrap();
    let zero = solver.int_const(0);
    let nonnegative = solver.try_ge(bound_len, zero).unwrap();
    let nonnegative_axiom = solver
        .try_forall_with_triggers(&[bound_seq], nonnegative, &[&[bound_len]])
        .unwrap();
    solver.try_assert_term(nonnegative_axiom).unwrap();
    let one = solver.int_const(1);

    let empty = solver.declare_const("seq_empty", seq_sort.clone());
    let x = solver.declare_const("seq_result_x", Sort::Int);
    let seven = solver.int_const(7);
    let at_x = solver.try_apply(&push, &[empty, x]).unwrap();
    let at_seven = solver.try_apply(&push, &[empty, seven]).unwrap();
    let empty_len = solver.try_apply(&len, &[empty]).unwrap();
    let at_x_len = solver.try_apply(&len, &[at_x]).unwrap();
    let at_seven_len = solver.try_apply(&len, &[at_seven]).unwrap();

    let x_is_seven = solver.try_eq(x, seven).unwrap();
    let empty_is_empty = solver.try_eq(empty_len, zero).unwrap();
    let at_x_is_unit_len = solver.try_eq(at_x_len, one).unwrap();
    let at_seven_is_unit_len = solver.try_eq(at_seven_len, one).unwrap();
    solver.try_assert_term(x_is_seven).unwrap();
    solver.try_assert_term(empty_is_empty).unwrap();
    solver.try_assert_term(at_x_is_unit_len).unwrap();
    solver.try_assert_term(at_seven_is_unit_len).unwrap();

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_sat() || details.result.is_unknown(),
        "congruent Seq-result UF rows are satisfiable and must never be refuted: {details:?}"
    );
    if details.result.is_sat() {
        assert!(
            details.result.was_model_validated() && details.verification.sat_model_validated,
            "any emitted SAT must pass the full validation funnel: {details:?}"
        );
    }
}

/// The Seq-token repair is recover-only: an explicit disequality between the
/// now-congruent results is real evidence and must never be erased by choosing
/// one opaque representative. The solver may prove UNSAT directly or fail
/// closed if the cross-theory contradiction reaches only model validation.
#[test]
#[timeout(60_000)]
fn seq_result_uf_rows_keep_explicit_disequality_fail_closed() {
    let mut solver = Solver::try_new(Logic::Auflia).unwrap();
    let seq_sort = Sort::seq(Sort::Int);
    let push = solver
        .try_declare_fun(
            "seq_push_back",
            &[seq_sort.clone(), Sort::Int],
            seq_sort.clone(),
        )
        .unwrap();

    let empty = solver.declare_const("seq_empty", seq_sort.clone());
    let x = solver.declare_const("seq_result_diseq_x", Sort::Int);
    let seven = solver.int_const(7);
    let at_x = solver.try_apply(&push, &[empty, x]).unwrap();
    let at_seven = solver.try_apply(&push, &[empty, seven]).unwrap();
    let x_is_seven = solver.try_eq(x, seven).unwrap();
    let results_differ = solver.try_neq(at_x, at_seven).unwrap();
    solver.try_assert_term(x_is_seven).unwrap();
    solver.try_assert_term(results_differ).unwrap();

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat() || details.result.is_unknown(),
        "explicitly disequal results at one UF point must never validate SAT: {details:?}"
    );
    assert!(
        !details.result.was_model_validated() && !details.verification.sat_model_validated,
        "the explicit-disequality conflict must not mint SAT validation evidence: {details:?}"
    );
}

/// Repairing congruent Seq-returning rows changes the model value used as an
/// argument to downstream UFs. Their table keys were extracted before that
/// repair, so the final function graph must be checked again: two observations
/// of the now-identical Seq value cannot retain contradictory Int results.
#[test]
#[timeout(60_000)]
fn seq_result_repair_keeps_downstream_uf_congruence_fail_closed() {
    let mut solver = Solver::try_new(Logic::Auflia).unwrap();
    let seq_sort = Sort::seq(Sort::Int);
    let push = solver
        .try_declare_fun(
            "seq_push_back",
            &[seq_sort.clone(), Sort::Int],
            seq_sort.clone(),
        )
        .unwrap();
    let len = solver
        .try_declare_fun("seq_len", std::slice::from_ref(&seq_sort), Sort::Int)
        .unwrap();

    // Match the quantified AUFLIA route whose late LIA merge exposes the
    // collision. The operations themselves remain UFs.
    let bound_seq = solver.fresh_var("seq_result_conflict_bound", seq_sort.clone());
    let bound_len = solver.try_apply(&len, &[bound_seq]).unwrap();
    let zero = solver.int_const(0);
    let nonnegative = solver.try_ge(bound_len, zero).unwrap();
    let nonnegative_axiom = solver
        .try_forall_with_triggers(&[bound_seq], nonnegative, &[&[bound_len]])
        .unwrap();
    solver.try_assert_term(nonnegative_axiom).unwrap();

    let empty = solver.declare_const("seq_conflict_empty", seq_sort.clone());
    let x = solver.declare_const("seq_result_conflict_x", Sort::Int);
    let seven = solver.int_const(7);
    let at_x = solver.try_apply(&push, &[empty, x]).unwrap();
    let at_seven = solver.try_apply(&push, &[empty, seven]).unwrap();
    let at_x_len = solver.try_apply(&len, &[at_x]).unwrap();
    let at_seven_len = solver.try_apply(&len, &[at_seven]).unwrap();
    let one = solver.int_const(1);
    let two = solver.int_const(2);

    let x_is_seven = solver.try_eq(x, seven).unwrap();
    let at_x_is_one = solver.try_eq(at_x_len, one).unwrap();
    let at_seven_is_two = solver.try_eq(at_seven_len, two).unwrap();
    solver.try_assert_term(x_is_seven).unwrap();
    solver.try_assert_term(at_x_is_one).unwrap();
    solver.try_assert_term(at_seven_is_two).unwrap();

    let details = solver.check_sat_with_details();
    assert!(
        details.result.is_unsat() || details.result.is_unknown(),
        "downstream observations of congruent Seq results must never validate SAT: {details:?}"
    );
    assert!(
        !details.result.was_model_validated() && !details.verification.sat_model_validated,
        "a transitive Seq-result congruence conflict must not mint SAT evidence: {details:?}"
    );
}

/// Congruent Seq-result rows may be unified only as an opaque model
/// completion. Native sequence structure remains authoritative: repairing the
/// row table must not erase incompatible contents or lengths, including on
/// the quantified AUFLIA route where the generic non-string-Seq fail-close is
/// intentionally narrower.
#[test]
#[timeout(60_000)]
fn seq_result_uf_row_repair_preserves_native_sequence_conflicts() {
    #[derive(Clone, Copy, Debug)]
    enum NativeConflict {
        DistinctUnits,
        UnitVsEmpty,
    }

    for conflict in [NativeConflict::DistinctUnits, NativeConflict::UnitVsEmpty] {
        let mut solver = Solver::try_new(Logic::Auflia).unwrap();
        let seq_sort = Sort::seq(Sort::Int);
        let push = solver
            .try_declare_fun(
                "native_seq_result",
                &[seq_sort.clone(), Sort::Int],
                seq_sort.clone(),
            )
            .unwrap();
        let opaque_len = solver
            .try_declare_fun(
                "native_seq_result_len",
                std::slice::from_ref(&seq_sort),
                Sort::Int,
            )
            .unwrap();

        // Preserve the quantified AUFLIA routing shape from the positive
        // regression while constraining the result rows with native Seq terms.
        let bound_seq = solver.fresh_var("native_seq_bound", seq_sort.clone());
        let bound_len = solver.try_apply(&opaque_len, &[bound_seq]).unwrap();
        let zero = solver.int_const(0);
        let nonnegative = solver.try_ge(bound_len, zero).unwrap();
        let axiom = solver
            .try_forall_with_triggers(&[bound_seq], nonnegative, &[&[bound_len]])
            .unwrap();
        solver.try_assert_term(axiom).unwrap();

        let input = solver.declare_const("native_seq_input", seq_sort);
        let x = solver.declare_const("native_seq_key", Sort::Int);
        let seven = solver.int_const(7);
        let at_x = solver.try_apply(&push, &[input, x]).unwrap();
        let at_seven = solver.try_apply(&push, &[input, seven]).unwrap();
        let one = solver.int_const(1);
        let two = solver.int_const(2);
        let unit_one = solver.try_seq_unit(one).unwrap();
        let incompatible = match conflict {
            NativeConflict::DistinctUnits => solver.try_seq_unit(two).unwrap(),
            NativeConflict::UnitVsEmpty => solver.seq_empty(Sort::Int),
        };

        let keys_coincide = solver.try_eq(x, seven).unwrap();
        let first_value = solver.try_eq(at_x, unit_one).unwrap();
        let second_value = solver.try_eq(at_seven, incompatible).unwrap();
        solver.try_assert_term(keys_coincide).unwrap();
        solver.try_assert_term(first_value).unwrap();
        solver.try_assert_term(second_value).unwrap();

        let details = solver.check_sat_with_details();
        assert!(
            details.result.is_unsat() || details.result.is_unknown(),
            "native Seq conflict {conflict:?} at one UF point must never validate SAT: \
             {details:?}"
        );
        assert!(
            !details.result.was_model_validated() && !details.verification.sat_model_validated,
            "native Seq conflict {conflict:?} must not mint SAT validation evidence: {details:?}"
        );
    }
}
