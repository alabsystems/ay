// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

#[test]
fn joint_independent_bv64_ranges_include_off_diagonal_pairs() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::bitvec(64));
    let c = terms.mk_var("c", Sort::bitvec(64));
    let two = terms.mk_bitvec(int(2), 64);
    let r_bound = app(&mut terms, "bvult", &[r, two], Sort::Bool);
    let c_bound = app(&mut terms, "bvult", &[c, two], Sort::Bool);
    let guard = app(&mut terms, "and", &[r_bound, c_bound], Sort::Bool);
    let diagonal = app(&mut terms, "=", &[r, c], Sort::Bool);
    let (all_diagonal, some_off_diagonal) = quantified_pair(&mut terms, guard, diagonal);
    assert_violates(&verdict(&terms, &StubModel::new(), &[all_diagonal]));
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[some_off_diagonal]));
    let yes = terms.mk_bool(true);
    let (all, no_bad) = quantified_pair(&mut terms, guard, yes);
    assert_confirmed(&verdict(&terms, &StubModel::new(), &[all]));
    assert_violates(&verdict(&terms, &StubModel::new(), &[no_bad]));
}

#[test]
fn joint_dependent_row_ranges_check_every_cell_and_exclude_both_tails() {
    let mut terms = TermStore::new();
    let fixture = matrix(&mut terms);
    let good = StubModel::new().with(fixture.outer, matrix_value(false));
    let bad = StubModel::new().with(fixture.outer, matrix_value(true));
    assert_confirmed(&verdict(&terms, &good, &[fixture.all]));
    assert_violates(&verdict(&terms, &good, &[fixture.some_bad]));
    assert_violates(&verdict(&terms, &bad, &[fixture.all]));
    assert_confirmed(&verdict(&terms, &bad, &[fixture.some_bad]));
    // The bad cell is (r=2,c=1), not an equal-index diagonal. Both models
    // deliberately contain false cells just past inner and outer endpoints.
    let diagonal = app(&mut terms, "=", &[fixture.r, fixture.c], Sort::Bool);
    let guard = app(&mut terms, "and", &[fixture.guard, diagonal], Sort::Bool);
    let (diagonal_only, _) = quantified_pair(&mut terms, guard, fixture.read);
    assert_confirmed(&verdict(&terms, &bad, &[diagonal_only]));
}

#[test]
fn joint_empty_outer_and_empty_inner_rows_have_exact_quantifier_identities() {
    let mut terms = TermStore::new();
    let fixture = matrix(&mut terms);
    for value in [
        outer(0, row(5, cells(false, &[])), vec![]),
        outer(3, row(0, cells(false, &[])), vec![]),
    ] {
        let model = StubModel::new().with(fixture.outer, value);
        assert_confirmed(&verdict(&terms, &model, &[fixture.all]));
        assert_violates(&verdict(&terms, &model, &[fixture.some_bad]));
    }
}

#[test]
fn joint_bv64_dependent_ranges_reach_beyond_the_producers_32_ground_hints() {
    let mut terms = TermStore::new();
    let fixture = matrix(&mut terms);
    for bad in [false, true] {
        let value = outer(
            34,
            row(0, cells(false, &[])),
            vec![(33, row(65, cells(true, &[(64, !bad), (65, false)])))],
        );
        let model = StubModel::new().with(fixture.outer, value);
        if bad {
            assert_violates(&verdict(&terms, &model, &[fixture.all]));
            assert_confirmed(&verdict(&terms, &model, &[fixture.some_bad]));
        } else {
            assert_confirmed(&verdict(&terms, &model, &[fixture.all]));
            assert_violates(&verdict(&terms, &model, &[fixture.some_bad]));
        }
    }
}

#[test]
fn single_binder_struct_resize_path_uses_nested_selector_length() {
    // Producer vocabulary: codegen_call_vec_ops_struct_resize.rs applies
    // field selections to an owner before obtaining the nested Vec's len.
    let mut terms = TermStore::new();
    let owner_sort = Sort::Datatype(DatatypeSort::new(
        "Owner",
        vec![DatatypeConstructor::new(
            "mkOwner",
            vec![DatatypeField::new("fld_marks", row_sort())],
        )],
    ));
    let owner = terms.mk_var("owner", owner_sort);
    let vector = app(&mut terms, "fld_marks", &[owner], row_sort());
    let len = app(&mut terms, "row_len", &[vector], Sort::bitvec(64));
    let data = app(
        &mut terms,
        "row_data",
        &[vector],
        Sort::array(Sort::bitvec(64), Sort::Bool),
    );
    let i = terms.mk_var("i", Sort::bitvec(64));
    let read = app(&mut terms, "select", &[data, i], Sort::Bool);
    let all = compound_endpoint_forall(&mut terms, i, len, read);
    for (len, expected) in [(2, true), (3, false)] {
        let model = StubModel::new().with(
            owner,
            ModelValue::Datatype {
                ctor: "mkOwner".to_string(),
                args: vec![row(len, cells(true, &[(2, false)]))],
            },
        );
        if expected {
            assert_confirmed(&verdict(&terms, &model, &[all]));
        } else {
            assert_violates(&verdict(&terms, &model, &[all]));
        }
    }
}
