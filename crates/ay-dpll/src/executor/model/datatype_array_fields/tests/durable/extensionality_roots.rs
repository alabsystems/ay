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
