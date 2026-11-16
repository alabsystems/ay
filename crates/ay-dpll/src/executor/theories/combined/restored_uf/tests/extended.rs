// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn a_popped_disequality_has_no_authority_in_a_later_recovery() {
    let mut fixture = Nested::new();
    let distinct = app(
        &mut fixture.ctx,
        "distinct",
        &[fixture.left, fixture.right],
        Sort::Bool,
    );
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.roots[1], true)]);
    live.push();
    live.assert_literal(distinct, true);
    assert!(matches!(live.check(), TheoryResult::Sat));
    let mut pushed = live.extract_model();
    let mut pushed_lia = fixture.candidate(&mut pushed);
    let old = pushed.clone();
    let old_lia = pushed_lia.clone();
    assert_eq!(
        run(
            &fixture.ctx,
            &live,
            &fixture.roots,
            &mut pushed,
            &mut pushed_lia,
            &mut unlimited
        ),
        Err(Refusal::Conflict)
    );
    same_candidate(&pushed, &old, &pushed_lia, &old_lia);
    live.pop();
    assert!(matches!(live.check(), TheoryResult::Sat));
    let mut popped = live.extract_model();
    let mut popped_lia = fixture.candidate(&mut popped);
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut popped,
        &mut popped_lia,
        &mut unlimited,
    )
    .unwrap();
    assert_eq!(popped.int_values[&fixture.outer_left], BigInt::from(0));
}

#[test]
fn shared_arithmetic_disequality_is_not_lost_when_no_false_equality_atom_exists() {
    let fixture = Nested::new();
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.roots[1], true)]);
    live.assert_shared_disequality(fixture.left, fixture.right, &[]);
    assert!(matches!(live.check(), TheoryResult::Sat));
    let mut model = live.extract_model();
    let mut lia = fixture.candidate(&mut model);
    let old = model.clone();
    let old_lia = lia.clone();
    assert_eq!(
        run(
            &fixture.ctx,
            &live,
            &fixture.roots,
            &mut model,
            &mut lia,
            &mut unlimited
        ),
        Err(Refusal::Conflict)
    );
    same_candidate(&model, &old, &lia, &old_lia);
}

#[test]
fn a_coherent_sparse_model_does_not_pay_for_an_unneeded_whole_snapshot() {
    let fixture = Nested::new();
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.roots[1], true)]);
    let mut model = live.extract_model();
    let mut lia = fixture.candidate(&mut model);
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    let mut bytes = 0usize;
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut model,
        &mut lia,
        &mut |_, amount| {
            bytes = bytes.checked_add(amount).unwrap();
            Ok(())
        },
    )
    .unwrap();
    model.term_values.reserve(65_536);
    model.function_tables.reserve(65_536);
    let old = model.clone();
    let old_lia = lia.clone();
    let mut remaining = bytes.checked_add(4096).unwrap();
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut model,
        &mut lia,
        &mut |_, amount| {
            remaining = remaining
                .checked_sub(amount)
                .ok_or(UnknownOrigin::MemoryBudget)?;
            Ok(())
        },
    )
    .unwrap();
    same_candidate(&model, &old, &lia, &old_lia);
}

#[test]
fn nested_integer_change_rekeys_arithmetic_ite_then_a_dependent_uf_point() {
    let mut fixture = Nested::new();
    for command in ay_frontend::parse("(declare-fun h (Int) U) (declare-fun k (U) Int)").unwrap() {
        fixture.ctx.process_command(&command).unwrap();
    }
    let one = fixture.ctx.terms.mk_int(1.into());
    let positive = app(
        &mut fixture.ctx,
        ">",
        &[fixture.outer_left, fixture.zero],
        Sort::Bool,
    );
    let predecessor = app(&mut fixture.ctx, "-", &[fixture.outer_left, one], Sort::Int);
    let clipped = fixture
        .ctx
        .terms
        .mk_ite_raw(positive, predecessor, fixture.outer_left);
    let h_left = app(
        &mut fixture.ctx,
        "h",
        &[clipped],
        Sort::Uninterpreted("U".into()),
    );
    let h_right = app(
        &mut fixture.ctx,
        "h",
        &[fixture.zero],
        Sort::Uninterpreted("U".into()),
    );
    let k_left = app(&mut fixture.ctx, "k", &[h_left], Sort::Int);
    let k_right = app(&mut fixture.ctx, "k", &[h_right], Sort::Int);
    let include_left = eq(&mut fixture.ctx, k_left, k_left);
    let pin_right = eq(&mut fixture.ctx, k_right, fixture.zero);
    fixture.roots.extend([include_left, pin_right]);
    let mut live = checked_live(
        &fixture.ctx,
        &fixture.roots,
        &[(fixture.roots[1], true), (pin_right, true)],
    );
    let mut model = live.extract_model();
    let mut lia = fixture.candidate(&mut model);
    for (term, value) in [(h_left, "@U!1"), (h_right, "@U!2")] {
        model.term_values.insert(term, value.into());
    }
    // These fabricated compound readings are deliberately WRONG. They may not
    // become point keys or stability pins; exact current leaves determine them.
    for term in [predecessor, clipped] {
        model.term_values.insert(term, "99".into());
        model.int_values.insert(term, 99.into());
        model.speculative_int_terms.insert(term);
    }
    model.term_values.insert(k_left, "6".into());
    model.int_values.insert(k_left, 6.into());
    model.speculative_int_terms.insert(k_left);
    model.func_app_const_terms.remove(&k_left);
    model.term_values.insert(k_right, "0".into());
    model.int_values.insert(k_right, 0.into());
    model.speculative_int_terms.remove(&k_right);
    model.func_app_const_terms.insert(k_right, fixture.zero);
    lia.as_mut().unwrap().values.insert(k_right, 0.into());
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    assert_eq!(model.int_values[&fixture.outer_left], BigInt::from(0));
    assert_eq!(model.int_values[&predecessor], BigInt::from(-1));
    assert_eq!(model.int_values[&clipped], BigInt::from(0));
    assert_eq!(model.term_values[&h_left], model.term_values[&h_right]);
    assert_eq!(model.int_values[&k_left], BigInt::from(0));
    assert_eq!(model.int_values[&k_right], BigInt::from(0));
    assert!(!model.speculative_int_terms.contains(&k_left));
}

#[test]
fn separate_actual_function_identities_do_not_merge_equal_argument_vectors() {
    let mut fixture = Nested::new();
    for command in ay_frontend::parse("(declare-fun independent (U) U)").unwrap() {
        fixture.ctx.process_command(&command).unwrap();
    }
    let independent = app(
        &mut fixture.ctx,
        "independent",
        &[fixture.a],
        Sort::Uninterpreted("U".into()),
    );
    let root = eq(&mut fixture.ctx, independent, independent);
    fixture.roots.push(root);
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.roots[1], true)]);
    let mut model = live.extract_model();
    let mut lia = fixture.candidate(&mut model);
    model.term_values.insert(independent, "@U!2".into());
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    assert_eq!(model.term_values[&independent], "@U!2");
    assert_ne!(
        model.term_values[&independent],
        model.term_values[&fixture.left]
    );
    assert_eq!(model.int_values[&fixture.outer_left], BigInt::from(0));
}

#[test]
fn identical_term_numbers_from_another_live_context_cannot_supply_facts() {
    let fixture = Nested::new();
    let other = Nested::new();
    let mut other_live = checked_live(&other.ctx, &other.roots, &[(other.roots[1], true)]);
    let mut model = other_live.extract_model();
    let mut lia = fixture.candidate(&mut model);
    let old = model.clone();
    let old_lia = lia.clone();
    assert_eq!(
        run(
            &fixture.ctx,
            &other_live,
            &fixture.roots,
            &mut model,
            &mut lia,
            &mut unlimited
        ),
        Err(Refusal::Unsupported)
    );
    same_candidate(&model, &old, &lia, &old_lia);
}

#[test]
fn unwinding_a_late_admission_callback_cannot_publish_a_partial_model() {
    let fixture = Nested::new();
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.roots[1], true)]);
    let mut original = live.extract_model();
    let original_lia = fixture.candidate(&mut original);
    let mut counted = original.clone();
    let mut counted_lia = original_lia.clone();
    let mut calls = 0usize;
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut counted,
        &mut counted_lia,
        &mut |_, _| {
            calls += 1;
            Ok(())
        },
    )
    .unwrap();
    let mut model = original.clone();
    let mut lia = original_lia.clone();
    let mut current = 0usize;
    let caught = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        let _ = run(
            &fixture.ctx,
            &live,
            &fixture.roots,
            &mut model,
            &mut lia,
            &mut |_, _| {
                current += 1;
                assert!(
                    current != calls,
                    "owned late admission unwind discriminator"
                );
                Ok(())
            },
        );
    }));
    assert!(caught.is_err());
    same_candidate(&model, &original, &lia, &original_lia);
}

#[test]
fn an_out_of_range_direct_pin_refuses_before_the_first_candidate_dereference() {
    let fixture = Nested::new();
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.roots[1], true)]);
    let mut model = live.extract_model();
    let mut lia = fixture.candidate(&mut model);
    // Remove the earlier value routes so capture must inspect this direct pin
    // before reaching its later whole-map pin validation pass.
    assert!(model.int_values.remove(&fixture.outer_left).is_some());
    assert!(!lia
        .as_ref()
        .unwrap()
        .values
        .contains_key(&fixture.outer_left));
    let invalid = TermId(u32::try_from(fixture.ctx.terms.len()).unwrap());
    model
        .func_app_const_terms
        .insert(fixture.outer_left, invalid);
    model
        .function_table_conflicts
        .insert("preserve_existing_conflict".into());
    model.array_read_pins_repaired = true;
    let old = model.clone();
    let old_lia = lia.clone();
    assert_eq!(
        run(
            &fixture.ctx,
            &live,
            &fixture.roots,
            &mut model,
            &mut lia,
            &mut unlimited
        ),
        Err(Refusal::Unsupported)
    );
    same_candidate(&model, &old, &lia, &old_lia);
}
