// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Completion controls using real Context declarations and checked live EUF.
//! Only the extracted candidate DATA is changed. These tests do not publish a
//! model, assert recovery equalities, or bypass the outer model-validation gate.

use super::*;

struct Predicate {
    ctx: Context,
    a: TermId,
    b: TermId,
    left: TermId,
    right: TermId,
    roots: Vec<TermId>,
}

impl Predicate {
    fn new() -> Self {
        let mut ctx = context(
            "(declare-sort U 0) (declare-const a U) (declare-const b U)
             (declare-fun p (U) Bool)",
        );
        let a = constant(&ctx, "a");
        let b = constant(&ctx, "b");
        let left = app(&mut ctx, "p", &[a], Sort::Bool);
        let right = app(&mut ctx, "p", &[b], Sort::Bool);
        // Reflexive source equalities retain both occurrences without
        // asserting either predicate or the equality of their arguments.
        let roots = vec![eq(&mut ctx, left, left), eq(&mut ctx, right, right)];
        Self {
            ctx,
            a,
            b,
            left,
            right,
            roots,
        }
    }

    fn missing(&self, model: &mut EufModel) {
        model.sort_elements.insert("U".into(), vec!["@U!0".into()]);
        model.term_values.insert(self.a, "@U!0".into());
        model.term_values.insert(self.b, "@U!0".into());
        model.term_values.remove(&self.left);
        model.term_values.remove(&self.right);
        model.function_tables.remove("p");
        model.function_table_terms.remove("p");
    }
}

#[test]
fn an_absent_unassigned_predicate_is_completed_even_without_a_value_merge() {
    let fixture = Predicate::new();
    let roots = &fixture.roots[..1];
    let mut live = checked_live(&fixture.ctx, roots, &[]);
    let mut model = live.extract_model();
    fixture.missing(&mut model);
    let mut lia = None;
    assert!(!model.term_values.contains_key(&fixture.left));
    run(
        &fixture.ctx,
        &live,
        roots,
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    // A soft default must be actually committed even when it was already the
    // provisional closure value: this is not the old cheap no-op case.
    assert_eq!(model.term_values[&fixture.left], "false");
    assert!(!model.term_values.contains_key(&fixture.right));
    assert_eq!(
        model.function_tables["p"],
        vec![(vec!["@U!0".into()], "false".into())]
    );
    assert_eq!(model.function_table_terms["p"], vec![fixture.left]);
    assert!(model.func_app_const_terms.get(&fixture.left).is_none());
    assert!(!live.are_equal(fixture.a, fixture.b));
}

#[test]
fn a_current_hard_true_peer_overrides_only_the_missing_soft_proposal() {
    let fixture = Predicate::new();
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.right, true)]);
    let mut model = live.extract_model();
    fixture.missing(&mut model);
    let mut lia = None;
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    assert_eq!(model.term_values[&fixture.left], "true");
    assert_eq!(model.term_values[&fixture.right], "true");
    assert_eq!(
        model.function_tables["p"],
        vec![(vec!["@U!0".into()], "true".into())]
    );
    assert_eq!(model.function_table_terms["p"].len(), 1);
    assert!(!live.are_equal(fixture.a, fixture.b));
    assert!(!live.are_equal(fixture.left, fixture.right));
}

#[test]
fn opposite_current_predicate_commitments_refuse_the_entire_transaction() {
    let mut fixture = Predicate::new();
    let sentinel = fixture.ctx.terms.mk_int(41.into());
    let mut live = checked_live(
        &fixture.ctx,
        &fixture.roots,
        &[(fixture.left, true), (fixture.right, false)],
    );
    let mut model = live.extract_model();
    fixture.missing(&mut model);
    model
        .function_table_conflicts
        .insert("unrelated_conflict".into());
    model.array_read_pins_repaired = true;
    let old = model.clone();
    let mut lia = Some(LiaModel {
        values: [(sentinel, 41.into())].into_iter().collect(),
    });
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
        Err(Refusal::Conflict),
    );
    same_candidate(&model, &old, &lia, &old_lia);
}

#[test]
fn an_inherited_live_boolean_constant_pin_wins_without_an_own_raw_value() {
    let mut fixture = Predicate::new();
    let truth = fixture.ctx.terms.mk_bool(true);
    let class_pin = eq(&mut fixture.ctx, fixture.left, truth);
    let mut live = checked_live(&fixture.ctx, &fixture.roots[..1], &[(class_pin, true)]);
    assert!(live.are_equal(fixture.left, truth));
    let mut model = live.extract_model();
    fixture.missing(&mut model);
    let mut lia = None;
    run(
        &fixture.ctx,
        &live,
        &fixture.roots[..1],
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    assert_eq!(model.term_values[&fixture.left], "true");
    assert_eq!(model.function_tables["p"][0].1, "true");
}

#[test]
fn a_predicate_in_a_satisfied_guard_is_never_turned_into_a_hard_false_fact() {
    let mut fixture = Predicate::new();
    let gate = fixture.ctx.terms.mk_var("gate", Sort::Bool);
    let guarded = app(&mut fixture.ctx, "or", &[gate, fixture.left], Sort::Bool);
    let roots = [guarded, fixture.roots[1]];
    let mut live = checked_live(&fixture.ctx, &roots, &[(gate, true)]);
    let mut model = live.extract_model();
    fixture.missing(&mut model);
    let mut lia = None;
    run(
        &fixture.ctx,
        &live,
        &roots,
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    assert_eq!(model.term_values[&fixture.left], "false");
    assert!(model.func_app_const_terms.get(&fixture.left).is_none());
    // Reuse that completed candidate under a genuine later live assignment.
    // If completion invented a hard false, this second transaction would fail.
    live.push();
    live.assert_literal(fixture.left, true);
    assert!(matches!(live.check(), TheoryResult::Sat));
    // Keep the first completed false value, while making its same-point peer
    // genuinely absent again so the second run must perform completion too.
    assert_eq!(model.term_values[&fixture.left], "false");
    model.term_values.remove(&fixture.right);
    run(
        &fixture.ctx,
        &live,
        &roots,
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    assert_eq!(model.term_values[&fixture.left], "true");
    assert_eq!(model.function_tables["p"][0].1, "true");
    live.pop();
}

#[test]
fn malformed_present_boolean_data_is_not_treated_as_an_absent_predicate() {
    let fixture = Predicate::new();
    let mut live = checked_live(&fixture.ctx, &fixture.roots[..1], &[]);
    let mut original = live.extract_model();
    fixture.missing(&mut original);
    for bad in ["", "TRUE", "@Bool!0", "neither_true_nor_false"] {
        let mut model = original.clone();
        model.term_values.insert(fixture.left, bad.into());
        let old = model.clone();
        let mut lia = None;
        assert_eq!(
            run(
                &fixture.ctx,
                &live,
                &fixture.roots[..1],
                &mut model,
                &mut lia,
                &mut unlimited
            ),
            Err(Refusal::Unsupported),
            "malformed present raw={bad:?}",
        );
        same_candidate(&model, &old, &lia, &None);
    }
    // The otherwise identical absent-raw candidate is an admissible completion.
    let mut model = original;
    let mut lia = None;
    run(
        &fixture.ctx,
        &live,
        &fixture.roots[..1],
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    assert_eq!(model.term_values[&fixture.left], "false");
}

#[test]
fn existing_actual_truth_pin_keeps_priority_over_a_malformed_stale_raw_spelling() {
    let fixture = Predicate::new();
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.left, true)]);
    let mut model = live.extract_model();
    fixture.missing(&mut model);
    model
        .term_values
        .insert(fixture.left, "stale-non-boolean-data".into());
    let mut lia = None;
    // The second genuinely absent point requires a transaction; the old hard
    // truth priority on the first point must still govern this writeback.
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut model,
        &mut lia,
        &mut unlimited,
    )
    .unwrap();
    assert_eq!(model.term_values[&fixture.left], "true");
    assert_eq!(model.term_values[&fixture.right], "true");
}

#[test]
fn stop_or_budget_failure_during_completion_preserves_every_incumbent_field() {
    let mut fixture = Predicate::new();
    let sentinel = fixture.ctx.terms.mk_int(41.into());
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[]);
    let mut original = live.extract_model();
    fixture.missing(&mut original);
    original
        .function_table_conflicts
        .insert("unrelated_conflict".into());
    original.array_read_pins_repaired = true;
    let original_lia = Some(LiaModel {
        values: [(sentinel, 41.into())].into_iter().collect(),
    });
    let mut successful = original.clone();
    let mut successful_lia = original_lia.clone();
    let mut calls = 0usize;
    run(
        &fixture.ctx,
        &live,
        &fixture.roots,
        &mut successful,
        &mut successful_lia,
        &mut |_, _| {
            calls += 1;
            Ok(())
        },
    )
    .unwrap();
    assert!(calls > 10);
    assert_eq!(successful.term_values[&fixture.left], "false");
    for origin in [
        UnknownOrigin::DeterministicResourceBudget,
        UnknownOrigin::InterruptFlag,
    ] {
        for limit in [0, 1, calls / 2, calls - 1] {
            let mut model = original.clone();
            let mut lia = original_lia.clone();
            let mut attempted = 0usize;
            let mut refused = false;
            let result = run(
                &fixture.ctx,
                &live,
                &fixture.roots,
                &mut model,
                &mut lia,
                &mut |_, _| {
                    if refused || attempted == limit {
                        refused = true;
                        return Err(origin);
                    }
                    attempted += 1;
                    Ok(())
                },
            );
            assert_eq!(result, Err(Refusal::Stopped(origin)));
            assert!(refused);
            same_candidate(&model, &original, &lia, &original_lia);
        }
    }
}

#[test]
fn missing_predicate_outputs_do_not_borrow_authority_from_failed_signatures() {
    for malformed in 0..3 {
        let mut ctx = context(
            "(declare-sort U 0) (declare-sort V 0) (declare-const a U)
             (declare-const v V) (declare-fun p (U) Bool) (declare-fun integer_p (U) Int)",
        );
        let a = constant(&ctx, "a");
        let v = constant(&ctx, "v");
        let bad = match malformed {
            0 => app(&mut ctx, "p", &[a, a], Sort::Bool),
            1 => app(&mut ctx, "p", &[v], Sort::Bool),
            _ => app(&mut ctx, "integer_p", &[a], Sort::Bool),
        };
        let root = eq(&mut ctx, bad, bad);
        let mut live = checked_live(&ctx, &[root], &[]);
        let mut model = live.extract_model();
        model.sort_elements.insert("U".into(), vec!["@U!0".into()]);
        model.sort_elements.insert("V".into(), vec!["@V!0".into()]);
        model.term_values.insert(a, "@U!0".into());
        model.term_values.insert(v, "@V!0".into());
        model.term_values.remove(&bad);
        let old = model.clone();
        let mut lia = None;
        assert_eq!(
            run(&ctx, &live, &[root], &mut model, &mut lia, &mut unlimited),
            Err(Refusal::Unsupported),
            "malformed signature={malformed}"
        );
        same_candidate(&model, &old, &lia, &None);
    }
}

#[test]
fn a_missing_bare_boolean_variable_is_not_an_admitted_predicate_output() {
    let mut ctx = context("(declare-const flag Bool)");
    let flag = constant(&ctx, "flag");
    let root = eq(&mut ctx, flag, flag);
    let mut live = checked_live(&ctx, &[root], &[]);
    let mut model = live.extract_model();
    model.term_values.remove(&flag);
    let old = model.clone();
    let mut lia = None;
    assert_eq!(
        run(&ctx, &live, &[root], &mut model, &mut lia, &mut unlimited),
        Err(Refusal::Unsupported)
    );
    same_candidate(&model, &old, &lia, &None);
}

#[test]
fn an_adopted_or_defined_predicate_does_not_become_a_free_completion_point() {
    for adopted in [false, true] {
        let mut ctx = context(if adopted {
            "(declare-sort U 0) (declare-const a U) (declare-fun p (U) Bool)"
        } else {
            "(declare-sort U 0) (declare-const a U) (define-fun p ((x U)) Bool true)"
        });
        if adopted {
            let body = ctx.terms.mk_bool(true);
            assert!(ctx.try_register_native_adopted_macro_interp(
                "p",
                &[("x".into(), Sort::Uninterpreted("U".into()))],
                body,
                false
            ));
            assert!(ctx.adopted_macro_interp("p").is_some());
        }
        let a = constant(&ctx, "a");
        // Deliberately build a raw occurrence rather than expand the actual
        // definition. It must not acquire UF authority from its spelling.
        let raw = app(&mut ctx, "p", &[a], Sort::Bool);
        let root = eq(&mut ctx, raw, raw);
        let mut live = checked_live(&ctx, &[root], &[]);
        let mut model = live.extract_model();
        model.sort_elements.insert("U".into(), vec!["@U!0".into()]);
        model.term_values.insert(a, "@U!0".into());
        model.term_values.remove(&raw);
        model.function_tables.remove("p");
        model.function_table_terms.remove("p");
        let old = model.clone();
        let mut lia = None;
        assert_eq!(
            run(&ctx, &live, &[root], &mut model, &mut lia, &mut unlimited),
            Err(Refusal::Unsupported),
            "adopted={adopted}"
        );
        same_candidate(&model, &old, &lia, &None);
    }
}

#[test]
fn an_interpreted_boolean_application_is_evaluated_without_a_fake_uf_row() {
    let mut ctx = context("");
    let truth = ctx.terms.mk_bool(true);
    let native_not = app(&mut ctx, "not", &[truth], Sort::Bool);
    let root = eq(&mut ctx, native_not, native_not);
    let mut live = checked_live(&ctx, &[root], &[]);
    let mut model = live.extract_model();
    model.term_values.remove(&native_not);
    model.function_tables.remove("not");
    model.function_table_terms.remove("not");
    let old = model.clone();
    let mut lia = None;
    run(&ctx, &live, &[root], &mut model, &mut lia, &mut unlimited).unwrap();
    // This exact built-in needs no model-completion output or table.
    same_candidate(&model, &old, &lia, &None);
}

#[test]
fn equal_raw_labels_in_distinct_nominal_domains_never_merge_predicate_families() {
    let mut ctx = context(
        "(declare-sort U 0) (declare-sort V 0) (declare-const a U)
         (declare-const v V) (declare-fun p (U) Bool) (declare-fun q (V) Bool)",
    );
    let a = constant(&ctx, "a");
    let v = constant(&ctx, "v");
    let pa = app(&mut ctx, "p", &[a], Sort::Bool);
    let qv = app(&mut ctx, "q", &[v], Sort::Bool);
    let roots = [eq(&mut ctx, pa, pa), eq(&mut ctx, qv, qv)];
    let mut live = checked_live(&ctx, &roots, &[(qv, true)]);
    let mut model = live.extract_model();
    for sort in ["U", "V"] {
        model
            .sort_elements
            .insert(sort.into(), vec!["@same-token".into()]);
    }
    model.term_values.insert(a, "@same-token".into());
    model.term_values.insert(v, "@same-token".into());
    for (term, name) in [(pa, "p"), (qv, "q")] {
        model.term_values.remove(&term);
        model.function_tables.remove(name);
        model.function_table_terms.remove(name);
    }
    let mut lia = None;
    run(&ctx, &live, &roots, &mut model, &mut lia, &mut unlimited).unwrap();
    assert_eq!(model.term_values[&pa], "false");
    assert_eq!(model.term_values[&qv], "true");
    assert_eq!(model.function_table_terms["p"], vec![pa]);
    assert_eq!(model.function_table_terms["q"], vec![qv]);
    assert_eq!(model.function_tables["p"][0].1, "false");
    assert_eq!(model.function_tables["q"][0].1, "true");
}
