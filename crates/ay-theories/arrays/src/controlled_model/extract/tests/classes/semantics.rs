// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn real_asserted_completed_merge_history_matches_all_legacy_model_fields() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let mut solver = fixture.solver();
    let values = fixture.values();
    let original = owner(end, 1_000_000, 128 << 20);
    let before = (
        solver.array_var_merge_log.len(),
        solver.equiv_class_cache_version,
    );
    let output = controlled(&solver, &values, &original);
    assert_eq!(
        (
            solver.array_var_merge_log.len(),
            solver.equiv_class_cache_version
        ),
        before
    );
    same(&output, &solver.extract_model(&values));
    assert!(output.array_values.contains_key(&fixture.arrays[2]));
    assert!(output.store_chain_class_candidate.is_none());
    drop(output);
    original.check().unwrap();
}

#[test]
fn fresh_lifo_class_order_and_last_rank_tie_match_the_legacy_winner() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let mut solver = fixture.solver();
    let values = fixture.values();
    solver.equiv_class_cache_version = None;
    let original = owner(end, 1_000_000, 128 << 20);
    let output = controlled(&solver, &values, &original);
    assert!(solver.equiv_class_cache_version.is_none());
    let legacy = solver.extract_model(&values);
    same(&output, &legacy);
    let class = solver
        .equiv_classes
        .iter()
        .find(|c| c.contains(&fixture.arrays[2]))
        .unwrap();
    let winner = *class
        .iter()
        .filter(|&&t| t == fixture.arrays[0] || t == fixture.arrays[1])
        .last()
        .unwrap();
    assert_eq!(
        output.array_values[&fixture.arrays[2]],
        output.array_values[&winner]
    );
    assert_ne!(
        output.array_values[&fixture.arrays[0]],
        output.array_values[&fixture.arrays[1]]
    );
    drop(output);
    original.check().unwrap();
}

#[test]
fn version_current_cached_member_order_is_preserved_without_rebuilding_it() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let mut solver = fixture.solver();
    solver.build_equiv_class_cache();
    let saved = solver.equiv_classes.clone();
    let values = fixture.values();
    let original = owner(end, 1_000_000, 128 << 20);
    let output = controlled(&solver, &values, &original);
    assert_eq!(solver.equiv_classes, saved);
    same(&output, &solver.extract_model(&values));
    assert_eq!(solver.equiv_classes, saved);
    drop(output);
    original.check().unwrap();
}

#[test]
fn uniformly_present_defaults_and_unvalued_members_keep_exact_data() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    for &default in &fixture.defaults[..2] {
        // default_cache ignores empty scalar values, so use nonempty defaults
        // here. The existing class-free Some(empty) control remains unchanged.
        values.insert(default, "else".into());
    }
    let original = owner(end, 1_000_000, 128 << 20);
    let output = controlled(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert_eq!(
        output.array_values[&fixture.arrays[2]].default.as_deref(),
        Some("else")
    );
    assert!(!values.contains_key(&fixture.selects[4]));
    drop(output);
    original.check().unwrap();
}

#[test]
fn tracked_const_empty_default_propagates_some_empty_not_none() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let value = terms.mk_var("empty", Sort::Int);
    let constant = terms.mk_const_array(Sort::Int, value);
    let missing = terms.mk_var("missing", Sort::array(Sort::Int, Sort::Int));
    let index = terms.mk_var("i", Sort::Int);
    for array in [constant, missing] {
        terms.mk_app(Symbol::named("select"), [array, index], Sort::Int);
    }
    let equality = terms.mk_eq(constant, missing);
    let mut solver = ArraySolver::new(&terms);
    solver.populate_caches();
    solver.register_atom(equality);
    solver.assert_literal(equality, true);
    let _ = solver.check();
    solver.rebuild_assign_indices();
    let mut values = HashMap::default();
    values.insert(value, String::new());
    values.insert(index, "0".into());
    let original = owner(end, 1_000_000, 128 << 20);
    let output = controlled(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert_eq!(output.array_values[&constant].default.as_deref(), Some(""));
    assert_eq!(output.array_values[&missing].default.as_deref(), Some(""));
    drop(output);
    original.check().unwrap();
}

#[test]
fn prepaid_flat_plan_retains_every_legacy_lifo_member_in_exact_order() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let mut solver = fixture.solver();
    solver.build_equiv_class_cache();
    let expected = solver.equiv_classes.clone();
    solver.equiv_class_cache_version = None;
    let original = owner(end, 1_000_000, 128 << 20);
    original
        .with_work(|work| {
            let plan = super::super::super::classes::prepare(&solver, work)?;
            let mut begin = 0;
            for (&end, class) in plan.ends.iter().zip(&expected) {
                assert_eq!(&plan.members[begin..end], class.as_slice());
                begin = end;
            }
            assert_eq!(plan.ends.len(), expected.len());
            assert_eq!(begin, plan.members.len());
            // The legacy oracle ran during fixture preparation, before this adapter.
            plan.finish(work)
        })
        .unwrap();
    original.check().unwrap();
}

#[test]
fn read_poison_flags_stay_local_while_missing_class_members_receive_data() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let mut solver = fixture.solver();
    let mut values = fixture.values();
    values.insert(fixture.indices[1], "0".into());
    for (&select, value) in fixture.selects[..4]
        .iter()
        .zip(["bad1", "bad2", "good", "good"])
    {
        values.insert(select, value.into());
    }
    let original = owner(end, 1_000_000, 128 << 20);
    let output = controlled(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert!(output.read_conflicted.contains(&fixture.arrays[0]));
    assert!(!output.read_conflicted.contains(&fixture.arrays[2]));
    assert!(output.array_values[&fixture.arrays[0]].stores.is_empty());
    assert_eq!(
        output.array_values[&fixture.arrays[2]],
        output.array_values[&fixture.arrays[1]]
    );
    drop(output);
    original.check().unwrap();
}

#[test]
fn classes_without_any_interpretation_do_not_publish_empty_tracked_arrays() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let mut solver = fixture.solver();
    let values = HashMap::default();
    let original = owner(end, 1_000_000, 128 << 20);
    let output = controlled(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert!(output.array_values.is_empty());
    assert!(output.read_conflicted.is_empty());
    drop(output);
    original.check().unwrap();
}

#[test]
fn mixed_present_and_missing_defaults_refuse_instead_of_running_completion() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let solver = fixture.solver();
    let mut values = fixture.values();
    values.insert(fixture.defaults[0], "else".into());
    let original = owner(end, 1_000_000, 128 << 20);
    assert!(original
        .with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w))
        .is_err());
    assert!(original.clone().check().is_err());
    assert_eq!(values[&fixture.defaults[0]], "else");
}

#[test]
fn store_classes_and_unapplied_merge_or_registration_state_are_terminally_refused() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let values = fixture.values();
    for kind in 0..4 {
        let mut solver = fixture.solver();
        match kind {
            0 => {
                solver.store_cache.insert(
                    fixture.arrays[0],
                    (fixture.arrays[1], fixture.indices[0], fixture.selects[0]),
                );
            }
            1 => {
                solver.array_var_merge_undo.pop();
            }
            2 => {
                solver
                    .pending_registered_equalities
                    .push(fixture.equalities[0]);
            }
            _ => {
                solver.var_layer_dirty = true;
            }
        }
        let original = owner(end, 1_000_000, 128 << 20);
        assert!(original
            .with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w))
            .is_err());
        assert!(original.clone().check().is_err());
    }
}

#[test]
fn nested_class_sorts_are_refused_without_guessing_congruence_names() {
    let end = Instant::now() + Duration::from_secs(20);
    let mut terms = TermStore::new();
    let inner = Sort::array(Sort::Int, Sort::Int);
    let outer = Sort::array(Sort::Int, inner.clone());
    let a = terms.mk_var("a", outer.clone());
    let b = terms.mk_var("b", outer);
    let i = terms.mk_var("i", Sort::Int);
    for array in [a, b] {
        terms.mk_app(Symbol::named("select"), [array, i], inner.clone());
    }
    let equality = terms.mk_eq(a, b);
    let mut solver = ArraySolver::new(&terms);
    solver.populate_caches();
    solver.register_atom(equality);
    solver.assert_literal(equality, true);
    let _ = solver.check();
    solver.rebuild_assign_indices();
    let original = owner(end, 1_000_000, 128 << 20);
    let values = HashMap::default();
    assert!(original
        .with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w))
        .is_err());
    assert!(original.clone().check().is_err());
    assert!(values.is_empty());
}

#[test]
fn malformed_nonarray_class_or_duplicate_cached_member_is_refused_before_publication() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = ClassFixture::new();
    let values = fixture.values();
    for cached in [false, true] {
        let mut solver = fixture.solver();
        if cached {
            solver.build_equiv_class_cache();
            let duplicate = solver.equiv_classes[0][0];
            solver.equiv_classes[0].push(duplicate);
        } else {
            solver.eq_adj.insert(fixture.indices[0], Vec::new());
            solver.equiv_class_cache_version = None;
        }
        let original = owner(end, 1_000_000, 128 << 20);
        assert!(original
            .with_work(|w| solver.try_extract_prepared_model_with_budget(&values, w))
            .is_err());
        assert!(original.clone().check().is_err());
    }
}
