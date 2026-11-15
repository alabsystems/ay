// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

#[test]
fn exact_extensionality_root_requires_current_provenance_and_polarity() {
    let mut fixture = build_fixture();
    let roots = fixture
        .executor
        .authenticated_datatype_array_extensionality_roots(&fixture.model)
        .expect("current exact extensionality provenance authenticates");
    let entry = fixture
        .executor
        .array_ext_shadow
        .emitted
        .first()
        .expect("fixture emitted the outer extensionality witness")
        .clone();
    assert!(roots.contains(&entry.not_sel_eq));

    let mut missing = fixture.model.clone();
    missing.term_to_var.remove(&entry.eq_term);
    assert!(fixture
        .executor
        .authenticated_datatype_array_extensionality_roots(&missing)
        .is_none());
    let mut wrong = fixture.model.clone();
    let eq_var = *wrong
        .term_to_var
        .get(&entry.eq_term)
        .expect("outer equality has a SAT variable") as usize;
    wrong.sat_model[eq_var] = true;
    assert!(fixture
        .executor
        .authenticated_datatype_array_extensionality_roots(&wrong)
        .is_none());

    reject_forged_and_oversized_shadow(&mut fixture, &entry);
    reject_reincarnated_shadow_entry(&mut fixture);
}

#[test]
fn undemanded_emission_grants_neither_roots_nor_cells() {
    let fixture = build_fixture();
    let entry = fixture.executor.array_ext_shadow.emitted[0].clone();
    for assigned_true in [false, true] {
        let mut model = fixture.model.clone();
        if assigned_true {
            let variable = model.term_to_var[&entry.eq_term] as usize;
            model.sat_model[variable] = true;
        } else {
            model.term_to_var.remove(&entry.eq_term);
        }
        // The requested-witness validator keeps its existing strict contract.
        assert!(fixture
            .executor
            .authenticated_datatype_array_extensionality(&model)
            .is_none());
        let evidence = fixture
            .executor
            .collect_demanded_datatype_array_extensionality(&model)
            .expect("unselected emission contributes no evidence");
        assert!(evidence.roots.is_empty());
        assert!(evidence.cells.is_empty());
    }
}

fn append_unassigned_emission(
    fixture: &mut Fixture,
    label: &str,
) -> crate::executor::array_ext_shadow::ArrayExtShadowEntry {
    let sort = Sort::array(
        fixture.outer_sort.index_sort.clone(),
        fixture.outer_sort.element_sort.clone(),
    );
    let lhs = fixture
        .executor
        .ctx
        .terms
        .mk_var(&format!("{label}-left"), sort.clone());
    let rhs = fixture
        .executor
        .ctx
        .terms
        .mk_var(&format!("{label}-right"), sort);
    let equality = fixture.executor.ctx.terms.mk_eq(lhs, rhs);
    // The maintained eager producer scans syntactic negations even when they
    // are not asserted or encoded into this model. Use that real producer,
    // including its fresh witness/cache binding and birth-stamped ledger.
    let _syntactic_negation = fixture.executor.ctx.terms.mk_not(equality);
    fixture.executor.add_array_extensionality_axioms();
    let entry = fixture
        .executor
        .array_ext_shadow
        .emitted
        .iter()
        .find(|entry| entry.eq_term == equality)
        .expect("the maintained producer emitted this syntactic pair")
        .clone();
    assert!(entry.is_current(&fixture.executor.ctx.terms));
    assert!(!fixture.model.term_to_var.contains_key(&equality));
    entry
}

#[test]
fn demanded_collection_retains_active_evidence_and_excludes_mixed_undemanded_rows() {
    let mut fixture = build_fixture();
    let expected = fixture
        .executor
        .authenticated_datatype_array_extensionality(&fixture.model)
        .unwrap();
    let unassigned = append_unassigned_emission(&mut fixture, "unassigned-emission");
    let assigned_true = append_unassigned_emission(&mut fixture, "true-emission");
    let variable = u32::try_from(fixture.model.sat_model.len()).unwrap();
    fixture.model.sat_model.push(true);
    fixture
        .model
        .term_to_var
        .insert(assigned_true.eq_term, variable);
    let evidence = fixture
        .executor
        .collect_demanded_datatype_array_extensionality(&fixture.model)
        .expect("current active evidence survives unrelated eager emissions");
    assert_eq!(evidence.roots, expected.roots);
    assert_eq!(evidence.cells.len(), expected.cells.len());
    for (actual, expected) in evidence.cells.iter().zip(&expected.cells) {
        assert_eq!(actual.term, expected.term);
        assert_eq!(actual.stamp, expected.stamp);
        assert_eq!(actual.cell_sort, expected.cell_sort);
    }
    assert!(!evidence.roots.contains(&unassigned.not_sel_eq));
    assert!(!evidence.roots.contains(&assigned_true.not_sel_eq));
    assert!(fixture
        .executor
        .authenticated_datatype_array_extensionality(&fixture.model)
        .is_none());
}

#[test]
fn demanded_collection_rejects_active_missing_or_wrong_child_polarity_atomically() {
    let fixture = build_fixture();
    let entry = fixture.executor.array_ext_shadow.emitted[0].clone();
    let TermData::Not(cell_equality) = fixture.executor.ctx.terms.get(entry.not_sel_eq) else {
        panic!("fixture owns an exact negative witness literal");
    };
    let cell_equality = *cell_equality;
    for case in [
        "missing-negative",
        "false-negative",
        "missing-cell",
        "true-cell",
    ] {
        let mut model = fixture.model.clone();
        match case {
            "missing-negative" => {
                model.term_to_var.remove(&entry.not_sel_eq);
                model.term_to_var.remove(&cell_equality);
            }
            "false-negative" => {
                let variable = u32::try_from(model.sat_model.len()).unwrap();
                model.sat_model.push(false);
                model.term_to_var.insert(entry.not_sel_eq, variable);
            }
            _ => {
                let variable = u32::try_from(model.sat_model.len()).unwrap();
                model.sat_model.push(true);
                model.term_to_var.insert(entry.not_sel_eq, variable);
                if case == "missing-cell" {
                    model.term_to_var.remove(&cell_equality);
                } else {
                    let variable = u32::try_from(model.sat_model.len()).unwrap();
                    model.sat_model.push(true);
                    model.term_to_var.insert(cell_equality, variable);
                }
            }
        }
        let grant = model.seal_quantified_grant_model();
        let assignments = model.sat_model.clone();
        let mapping = model.term_to_var.clone();
        let roots = fixture.executor.ctx.assertions.clone();
        let terms = fixture.executor.ctx.terms.snapshot_stamp();
        let cache = fixture.executor.dt_egraph_assignment.borrow().clone();
        assert!(fixture
            .executor
            .collect_demanded_datatype_array_extensionality(&model)
            .is_none());
        assert_eq!(model.sat_model, assignments);
        assert_eq!(model.term_to_var, mapping);
        assert_eq!(fixture.executor.ctx.assertions, roots);
        assert_eq!(fixture.executor.ctx.terms.snapshot_stamp(), terms);
        assert!(model.carries_quantified_grant_model(&grant));
        match (
            cache,
            fixture.executor.dt_egraph_assignment.borrow().as_ref(),
        ) {
            (Some(before), Some(after)) => assert!(std::sync::Arc::ptr_eq(&before, after)),
            (None, None) => {}
            _ => panic!("read-only refusal changed the derived cache"),
        }
    }
}

#[test]
fn undemanded_rows_still_require_current_shape_and_a_bounded_ledger() {
    let mut fixture = build_fixture();
    let entry = append_unassigned_emission(&mut fixture, "undemanded-shape");
    let original = fixture.executor.array_ext_shadow.clone();
    let true_term = fixture.executor.ctx.terms.true_term();
    fixture.executor.array_ext_shadow.clear();
    assert!(fixture.executor.array_ext_shadow.record(
        &fixture.executor.ctx.terms,
        true_term,
        entry.eq_term,
        entry.lhs,
        entry.rhs,
        entry.not_sel_eq,
    ));
    assert!(fixture
        .executor
        .collect_demanded_datatype_array_extensionality(&fixture.model)
        .is_none());
    fixture.executor.array_ext_shadow = original.clone();
    fixture.executor.array_ext_shadow.emitted = vec![
        entry;
        super::super::super::super::dt_construct_budget::MAX_OPAQUE_DT_COLLECTION_ROOTS
            + 1
    ];
    assert!(fixture
        .executor
        .collect_demanded_datatype_array_extensionality(&fixture.model)
        .is_none());
    fixture.executor.array_ext_shadow = original;
    let checkpoint = fixture.executor.ctx.terms.rollback_checkpoint();
    let stale = fixture
        .executor
        .ctx
        .terms
        .mk_var("undemanded-stale", Sort::Bool);
    fixture.executor.array_ext_shadow.clear();
    assert!(fixture.executor.array_ext_shadow.record(
        &fixture.executor.ctx.terms,
        stale,
        stale,
        stale,
        stale,
        stale,
    ));
    fixture.executor.ctx.terms.rollback_to(checkpoint);
    assert!(fixture
        .executor
        .collect_demanded_datatype_array_extensionality(&fixture.model)
        .is_none());
}

fn reject_forged_and_oversized_shadow(
    fixture: &mut Fixture,
    entry: &crate::executor::array_ext_shadow::ArrayExtShadowEntry,
) {
    let original = fixture.executor.array_ext_shadow.clone();
    let true_term = fixture.executor.ctx.terms.true_term();
    fixture.executor.array_ext_shadow.clear();
    assert!(fixture.executor.array_ext_shadow.record(
        &fixture.executor.ctx.terms,
        true_term,
        entry.eq_term,
        entry.lhs,
        entry.rhs,
        entry.not_sel_eq,
    ));
    assert!(fixture
        .executor
        .authenticated_datatype_array_extensionality_roots(&fixture.model)
        .is_none());

    fixture.executor.array_ext_shadow = original.clone();
    fixture.executor.array_ext_shadow.emitted = vec![
        entry.clone();
        super::super::super::super::dt_construct_budget::MAX_OPAQUE_DT_COLLECTION_ROOTS
            + 1
    ];
    assert!(fixture
        .executor
        .authenticated_datatype_array_extensionality_roots(&fixture.model)
        .is_none());
    fixture.executor.array_ext_shadow = original;
}

fn reject_reincarnated_shadow_entry(fixture: &mut Fixture) {
    let checkpoint = fixture.executor.ctx.terms.rollback_checkpoint();
    let scratch = fixture
        .executor
        .ctx
        .terms
        .mk_var("w6-stale-shadow", Sort::Bool);
    fixture.executor.array_ext_shadow.clear();
    assert!(fixture.executor.array_ext_shadow.record(
        &fixture.executor.ctx.terms,
        scratch,
        scratch,
        scratch,
        scratch,
        scratch,
    ));
    fixture.executor.ctx.terms.rollback_to(checkpoint);
    assert!(fixture
        .executor
        .authenticated_datatype_array_extensionality_roots(&fixture.model)
        .is_none());
}
