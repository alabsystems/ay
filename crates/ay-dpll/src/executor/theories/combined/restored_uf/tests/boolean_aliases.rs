// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original-root Boolean equations recover values, not new independent
//! defaults or assertions. These controls use the existing real Context/live
//! EUF harness and alter only candidate DATA. No test publishes a model.

use super::*;

fn declarations(ctx: &mut Context, text: &str) {
    for command in ay_frontend::parse(text).expect("fixture declarations parse") {
        ctx.process_command(&command)
            .expect("fixture declarations elaborate");
    }
}

struct Alias {
    ctx: Context,
    a: TermId,
    predicate: TermId,
    flag: TermId,
    rhs: TermId,
    roots: Vec<TermId>,
}

impl Alias {
    fn new() -> Self {
        let mut ctx = context(
            "(declare-sort U 0) (declare-const a U) (declare-const flag Bool)
             (declare-fun p (U) Bool)",
        );
        let a = constant(&ctx, "a");
        let flag = constant(&ctx, "flag");
        let predicate = app(&mut ctx, "p", &[a], Sort::Bool);
        let truth = ctx.terms.mk_bool(true);
        let rhs = app(&mut ctx, "and", &[predicate, truth], Sort::Bool);
        let roots = vec![eq(&mut ctx, flag, rhs)];
        Self {
            ctx,
            a,
            predicate,
            flag,
            rhs,
            roots,
        }
    }

    fn candidate(&self, model: &mut EufModel, flag_raw: Option<&str>) {
        model.sort_elements.insert("U".into(), vec!["@U!0".into()]);
        model.term_values.insert(self.a, "@U!0".into());
        // Predicate truth comes from the actual live fixture assignment,
        // not from either this old own spelling or a sampled table row.
        model.term_values.insert(self.predicate, "false".into());
        model.term_values.remove(&self.rhs);
        if let Some(raw) = flag_raw {
            model.term_values.insert(self.flag, raw.into());
        } else {
            model.term_values.remove(&self.flag);
        }
    }
}

#[test]
fn a_missing_unconditionally_defined_boolean_materializes_without_any_uf_merge() {
    let fixture = Alias::new();
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.predicate, true)]);
    let mut model = live.extract_model();
    fixture.candidate(&mut model, None);
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
    assert_eq!(model.term_values[&fixture.flag], "true");
    assert_eq!(model.term_values[&fixture.predicate], "true");
    assert!(model.func_app_const_terms.get(&fixture.flag).is_none());
    assert!(!live.are_equal(fixture.flag, fixture.rhs));
}

#[test]
fn a_present_soft_boolean_equation_recomputes_without_becoming_a_hard_fact() {
    let fixture = Alias::new();
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.predicate, true)]);
    let mut model = live.extract_model();
    fixture.candidate(&mut model, Some("false"));
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
    assert_eq!(model.term_values[&fixture.flag], "true");
    assert!(model.func_app_const_terms.get(&fixture.flag).is_none());
    assert!(!live.are_equal(fixture.flag, fixture.rhs));
}

#[test]
fn boolean_equations_follow_current_nested_uf_values_after_congruence() {
    for old_value in [None, Some("false")] {
        let mut fixture = Nested::new();
        declarations(&mut fixture.ctx, "(declare-const saved_guard Bool)");
        let flag = constant(&fixture.ctx, "saved_guard");
        let one = fixture.ctx.terms.mk_int(1.into());
        let rhs = app(
            &mut fixture.ctx,
            "<",
            &[fixture.outer_left, one],
            Sort::Bool,
        );
        let definition = eq(&mut fixture.ctx, flag, rhs);
        fixture.roots.push(definition);
        let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.roots[1], true)]);
        let mut model = live.extract_model();
        let mut lia = fixture.candidate(&mut model);
        if let Some(raw) = old_value {
            model.term_values.insert(flag, raw.into());
        } else {
            model.term_values.remove(&flag);
        }
        // This comparison cache agrees with the old speculative 6, and is
        // deliberately stale after the nested hard-point recovery yields 0.
        model.term_values.insert(rhs, "false".into());
        assert_eq!(model.int_values[&fixture.outer_left], BigInt::from(6));
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
        assert_eq!(model.int_values[&fixture.outer_right], BigInt::from(0));
        assert_eq!(model.term_values[&flag], "true", "old={old_value:?}");
        assert_eq!(
            model.term_values[&fixture.left],
            model.term_values[&fixture.right]
        );
        assert!(model.func_app_const_terms.get(&flag).is_none());
    }
}

#[test]
fn actual_hard_boolean_truth_cannot_be_overwritten_by_a_defining_expression() {
    let fixture = Alias::new();
    let mut live = checked_live(
        &fixture.ctx,
        &fixture.roots,
        &[(fixture.predicate, true), (fixture.flag, false)],
    );
    let mut model = live.extract_model();
    fixture.candidate(&mut model, None);
    let old = model.clone();
    let mut lia = None;
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
    same_candidate(&model, &old, &lia, &None);
}

#[test]
fn inherited_boolean_class_pins_are_constraints_even_without_an_own_raw_value() {
    for truth in [false, true] {
        let mut fixture = Alias::new();
        let literal = fixture.ctx.terms.mk_bool(truth);
        let pin = eq(&mut fixture.ctx, fixture.flag, literal);
        let mut live = checked_live(
            &fixture.ctx,
            &fixture.roots,
            &[(fixture.predicate, true), (pin, true)],
        );
        assert!(live.are_equal(fixture.flag, literal));
        let mut model = live.extract_model();
        fixture.candidate(&mut model, None);
        let old = model.clone();
        let mut lia = None;
        let result = run(
            &fixture.ctx,
            &live,
            &fixture.roots,
            &mut model,
            &mut lia,
            &mut unlimited,
        );
        if truth {
            result.unwrap();
            assert_eq!(model.term_values[&fixture.flag], "true");
        } else {
            assert_eq!(result, Err(Refusal::Conflict));
            same_candidate(&model, &old, &lia, &None);
        }
    }
}

#[test]
fn every_unconditional_definition_is_retained_including_conflicting_duplicates() {
    let mut ctx = context("(declare-const flag Bool)");
    let flag = constant(&ctx, "flag");
    let yes = ctx.terms.mk_bool(true);
    let no = ctx.terms.mk_bool(false);
    let roots = [eq(&mut ctx, flag, yes), eq(&mut ctx, flag, no)];
    let mut live = checked_live(&ctx, &roots, &[]);
    let mut model = live.extract_model();
    model.term_values.remove(&flag);
    let old = model.clone();
    let mut lia = None;
    assert_eq!(
        run(&ctx, &live, &roots, &mut model, &mut lia, &mut unlimited),
        Err(Refusal::Conflict)
    );
    same_candidate(&model, &old, &lia, &None);
}

#[test]
fn a_missing_variable_chain_needs_an_actual_noncyclic_value_anchor() {
    let mut ctx = context("(declare-const x Bool) (declare-const y Bool) (declare-const z Bool)");
    let x = constant(&ctx, "x");
    let y = constant(&ctx, "y");
    let z = constant(&ctx, "z");
    let truth = ctx.terms.mk_bool(true);
    let roots = [
        eq(&mut ctx, x, y),
        eq(&mut ctx, y, z),
        eq(&mut ctx, z, truth),
    ];
    let mut live = checked_live(&ctx, &roots, &[]);
    let mut model = live.extract_model();
    for term in [x, y, z] {
        model.term_values.remove(&term);
    }
    let mut lia = None;
    run(&ctx, &live, &roots, &mut model, &mut lia, &mut unlimited).unwrap();
    for term in [x, y, z] {
        assert_eq!(model.term_values[&term], "true");
    }
}

#[test]
fn cycles_self_only_equations_and_unanchored_boolean_inputs_stay_unsupported() {
    for shape in 0..3 {
        let mut ctx =
            context("(declare-const x Bool) (declare-const y Bool) (declare-fun p (Bool) Bool)");
        let x = constant(&ctx, "x");
        let y = constant(&ctx, "y");
        let roots = match shape {
            0 => vec![eq(&mut ctx, x, x)],
            1 => {
                let not_y = ctx.terms.mk_not_raw(y);
                let not_x = ctx.terms.mk_not_raw(x);
                vec![eq(&mut ctx, x, not_y), eq(&mut ctx, y, not_x)]
            }
            _ => {
                let predicate = app(&mut ctx, "p", &[x], Sort::Bool);
                vec![eq(&mut ctx, predicate, predicate)]
            }
        };
        let mut live = checked_live(&ctx, &roots, &[]);
        let mut model = live.extract_model();
        model.term_values.remove(&x);
        model.term_values.remove(&y);
        let old = model.clone();
        let mut lia = None;
        assert_eq!(
            run(&ctx, &live, &roots, &mut model, &mut lia, &mut unlimited),
            Err(Refusal::Unsupported),
            "shape={shape}"
        );
        same_candidate(&model, &old, &lia, &None);
    }
}

#[test]
fn an_equation_under_a_satisfied_guard_does_not_define_an_unassigned_variable() {
    let mut fixture = Alias::new();
    let gate = fixture.ctx.terms.mk_var("gate", Sort::Bool);
    let guarded = app(
        &mut fixture.ctx,
        "or",
        &[gate, fixture.roots[0]],
        Sort::Bool,
    );
    let roots = [guarded];
    let mut live = checked_live(
        &fixture.ctx,
        &roots,
        &[(gate, true), (fixture.predicate, true)],
    );
    let mut model = live.extract_model();
    fixture.candidate(&mut model, None);
    let old = model.clone();
    let mut lia = None;
    assert_eq!(
        run(
            &fixture.ctx,
            &live,
            &roots,
            &mut model,
            &mut lia,
            &mut unlimited
        ),
        Err(Refusal::Unsupported)
    );
    same_candidate(&model, &old, &lia, &None);
}

#[test]
fn an_unsupported_interpreted_rhs_never_becomes_a_cached_value_or_a_default() {
    let mut ctx = context("(declare-const flag Bool) (declare-const x Int) (declare-const y Int)");
    let flag = constant(&ctx, "flag");
    let x = constant(&ctx, "x");
    let y = constant(&ctx, "y");
    let product = app(&mut ctx, "*", &[x, y], Sort::Int);
    let rhs = eq(&mut ctx, product, x);
    let definition = eq(&mut ctx, flag, rhs);
    let mut live = checked_live(&ctx, &[definition], &[]);
    let mut model = live.extract_model();
    model.term_values.remove(&flag);
    // Cached interpreted results are candidate DATA and cannot turn the
    // current exact evaluator's unsupported multiplication into authority.
    model.term_values.insert(rhs, "true".into());
    model.term_values.insert(product, "2".into());
    model.int_values.insert(product, 2.into());
    model.speculative_int_terms.insert(product);
    for (term, value) in [(x, 2), (y, 3)] {
        model.term_values.insert(term, value.to_string());
        model.int_values.insert(term, value.into());
    }
    let old = model.clone();
    let mut lia = None;
    assert_eq!(
        run(
            &ctx,
            &live,
            &[definition],
            &mut model,
            &mut lia,
            &mut unlimited
        ),
        Err(Refusal::Unsupported)
    );
    same_candidate(&model, &old, &lia, &None);
}

#[test]
fn malformed_present_alias_data_refuses_unless_actual_truth_already_has_priority() {
    for hard_truth in [false, true] {
        let fixture = Alias::new();
        let mut literals = vec![(fixture.predicate, true)];
        if hard_truth {
            literals.push((fixture.flag, true));
        }
        let mut live = checked_live(&fixture.ctx, &fixture.roots, &literals);
        let mut model = live.extract_model();
        fixture.candidate(&mut model, Some("@not-a-boolean"));
        let old = model.clone();
        let mut lia = None;
        let result = run(
            &fixture.ctx,
            &live,
            &fixture.roots,
            &mut model,
            &mut lia,
            &mut unlimited,
        );
        if hard_truth {
            // Existing direct actual truth priority may already provide the
            // value. Do not require an unrelated no-op to rewrite raw data.
            result.unwrap();
        } else {
            assert_eq!(result, Err(Refusal::Unsupported));
            same_candidate(&model, &old, &lia, &None);
        }
    }
}

#[test]
fn cancelled_or_exhausted_alias_materialization_preserves_all_candidate_fields() {
    let mut fixture = Alias::new();
    let sentinel = fixture.ctx.terms.mk_int(43.into());
    let mut live = checked_live(&fixture.ctx, &fixture.roots, &[(fixture.predicate, true)]);
    let mut original = live.extract_model();
    fixture.candidate(&mut original, None);
    original.array_read_pins_repaired = true;
    original
        .function_table_conflicts
        .insert("unrelated_conflict".into());
    let original_lia = Some(LiaModel {
        values: [(sentinel, 43.into())].into_iter().collect(),
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
    assert_eq!(successful.term_values[&fixture.flag], "true");
    for origin in [
        UnknownOrigin::InterruptFlag,
        UnknownOrigin::DeterministicResourceBudget,
        UnknownOrigin::MemoryBudget,
    ] {
        for limit in [0, 1, calls / 2, calls - 1] {
            let mut model = original.clone();
            let mut lia = original_lia.clone();
            let mut index = 0usize;
            let mut stopped = false;
            let result = run(
                &fixture.ctx,
                &live,
                &fixture.roots,
                &mut model,
                &mut lia,
                &mut |_, _| {
                    if stopped || index == limit {
                        stopped = true;
                        return Err(origin);
                    }
                    index += 1;
                    Ok(())
                },
            );
            assert_eq!(result, Err(Refusal::Stopped(origin)));
            assert!(stopped);
            same_candidate(&model, &original, &lia, &original_lia);
        }
    }
}

#[test]
fn alias_equations_cannot_hide_wrong_function_signatures_or_nominal_domains() {
    for malformed in [false, true] {
        let mut ctx = context(
            "(declare-sort U 0) (declare-sort V 0) (declare-const a U) (declare-const v V)
             (declare-const up Bool) (declare-const vp Bool)
             (declare-fun p (U) Bool) (declare-fun q (V) Bool)",
        );
        let a = constant(&ctx, "a");
        let v = constant(&ctx, "v");
        let up = constant(&ctx, "up");
        let vp = constant(&ctx, "vp");
        let p = app(&mut ctx, "p", &[if malformed { v } else { a }], Sort::Bool);
        let q = app(&mut ctx, "q", &[v], Sort::Bool);
        let roots = [eq(&mut ctx, up, p), eq(&mut ctx, vp, q)];
        let mut live = checked_live(&ctx, &roots, &[(q, true)]);
        let mut model = live.extract_model();
        for name in ["U", "V"] {
            model
                .sort_elements
                .insert(name.into(), vec!["@same-token".into()]);
        }
        model.term_values.insert(a, "@same-token".into());
        model.term_values.insert(v, "@same-token".into());
        for term in [up, vp, p, q] {
            model.term_values.remove(&term);
        }
        let old = model.clone();
        let mut lia = None;
        let result = run(&ctx, &live, &roots, &mut model, &mut lia, &mut unlimited);
        if malformed {
            assert_eq!(result, Err(Refusal::Unsupported));
            same_candidate(&model, &old, &lia, &None);
        } else {
            result.unwrap();
            assert_eq!(model.term_values[&up], "false");
            assert_eq!(model.term_values[&vp], "true");
            assert_eq!(model.function_tables["p"][0].1, "false");
            assert_eq!(model.function_tables["q"][0].1, "true");
        }
    }
}
