// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

// Boolean folding, reflexivity, and propagation-stamp regressions.
// Textually included by `proof_propagated_rewrite::tests` to preserve test FQNs.

// ---- Boolean-constant negation folds (#4751) ----

/// GREEN: `(not p)` whose body folds to `true` is stored as literal `false`.
/// The congruence slice cannot state that (its conclusion would name a
/// `(not true)` node the store never mints), so before `plan_not_constant_fold`
/// the whole plan declined. The strict checker re-derives the propositional
/// chain that replaces it.
#[test]
fn not_true_fold_derives_false_and_strict_checks() {
    let mut terms = TermStore::new();
    let p = bool_fun(&mut terms, "pp", 0);
    let other = bool_fun(&mut terms, "po", 0);
    let true_term = terms.true_term();
    let false_term = terms.false_term();
    let not_p = terms.mk_not_raw(p);
    let before = terms.mk_app(Symbol::named("or"), [not_p, other], Sort::Bool);
    let p_def = terms.mk_app(Symbol::named("="), [p, true_term], Sort::Bool);
    assert_eq!(
        terms.mk_not(true_term),
        false_term,
        "fixture must exercise the constant fold"
    );
    let after = terms.mk_app(Symbol::named("or"), [false_term, other], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, p_def], terms);
    fixture.entry(p, true_term, p_def, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// GREEN: the dual direction — `(not p)` whose body folds to `false` is
/// stored as literal `true`.
#[test]
fn not_false_fold_derives_true_and_strict_checks() {
    let mut terms = TermStore::new();
    let p = bool_fun(&mut terms, "pp", 0);
    let other = bool_fun(&mut terms, "po", 0);
    let true_term = terms.true_term();
    let false_term = terms.false_term();
    let not_p = terms.mk_not_raw(p);
    let before = terms.mk_app(Symbol::named("or"), [not_p, other], Sort::Bool);
    let p_def = terms.mk_app(Symbol::named("="), [p, false_term], Sort::Bool);
    let after = terms.mk_app(Symbol::named("or"), [true_term, other], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, p_def], terms);
    fixture.entry(p, false_term, p_def, 1);
    fixture.record(before, true_term, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// GUARD: a candidate whose recorded `after` is a literal Boolean constant is
/// a preprocessing-time REFUTATION, not a rewritten problem assertion. The
/// constant-fold bridges refuse to conclude it, so the existing
/// `rebuild_trust_leaf_proof_from_original_assertions` lane still produces the
/// refutation WITH its theory certificates
/// (`native_replay_with_proofs_checks_lia_equality_against_negated_bound`
/// asserts a Farkas certificate survives in the exported artifact).
#[test]
fn constant_target_candidate_is_left_to_the_original_assertion_rebuild() {
    let mut terms = TermStore::new();
    let p = bool_fun(&mut terms, "pp", 0);
    let true_term = terms.true_term();
    let false_term = terms.false_term();
    let before = terms.mk_not_raw(p);
    let p_def = terms.mk_app(Symbol::named("="), [p, true_term], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, p_def], terms);
    fixture.entry(p, true_term, p_def, 1);
    fixture.record(before, false_term, 1);
    assert!(
        fixture.plan_with_constant_target(false_term).is_none(),
        "a literal-constant target must stay with the original-assertion rebuild"
    );
}

/// GREEN, the real #4751 shape: a disjunction whose members collapse under
/// substitution to DUPLICATES and to literal `false`, rebuilt structurally by
/// `VariableSubstitution` (`mk_app`, which keeps every argument). The
/// negation fold is what unblocks the enclosing `or` congruence.
#[test]
fn or_with_duplicate_and_false_members_derives_through_congruence() {
    let mut terms = TermStore::new();
    let p = bool_fun(&mut terms, "pp", 0);
    let q = bool_fun(&mut terms, "pq", 0);
    let r = bool_fun(&mut terms, "pr", 0);
    let shared = bool_fun(&mut terms, "ps", 0);
    let true_term = terms.true_term();
    let false_term = terms.false_term();
    // `(or (not p) (not q) r)`: p and q both fold to `true` (so both members
    // become `false`), r folds to `shared`.
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);
    let before = terms.mk_app(Symbol::named("or"), [not_p, not_q, r], Sort::Bool);
    let p_def = terms.mk_app(Symbol::named("="), [p, true_term], Sort::Bool);
    let q_def = terms.mk_app(Symbol::named("="), [q, true_term], Sort::Bool);
    let r_def = terms.mk_app(Symbol::named("="), [r, shared], Sort::Bool);
    // The structural rebuild `VariableSubstitution` stores: arity preserved,
    // literal `false` members kept.
    let after = terms.mk_app(
        Symbol::named("or"),
        [false_term, false_term, shared],
        Sort::Bool,
    );

    let mut fixture = Fixture::new(vec![before, p_def, q_def, r_def], terms);
    fixture.entry(p, true_term, p_def, 1);
    fixture.entry(q, true_term, q_def, 1);
    fixture.entry(r, shared, r_def, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// NEGATIVE (guard: `rebuilt` must be the OPPOSITE constant): a forged record
/// claiming the negated member became `true` — the polarity a dropped guard
/// would admit — must decline. Stated inside a disjunction so the forged
/// target is not the trivially-derivable `(cl true)`.
#[test]
fn not_constant_fold_declines_wrong_polarity() {
    let mut terms = TermStore::new();
    let p = bool_fun(&mut terms, "pp", 0);
    let r = bool_fun(&mut terms, "pr", 0);
    let shared = bool_fun(&mut terms, "ps", 0);
    let true_term = terms.true_term();
    let false_term = terms.false_term();
    let not_p = terms.mk_not_raw(p);
    let before = terms.mk_app(Symbol::named("or"), [not_p, r], Sort::Bool);
    let p_def = terms.mk_app(Symbol::named("="), [p, true_term], Sort::Bool);
    let r_def = terms.mk_app(Symbol::named("="), [r, shared], Sort::Bool);
    let honest = terms.mk_app(Symbol::named("or"), [false_term, shared], Sort::Bool);
    let forged = terms.mk_app(Symbol::named("or"), [true_term, shared], Sort::Bool);
    assert_ne!(honest, forged);

    let mut fixture = Fixture::new(vec![before, p_def, r_def], terms);
    fixture.entry(p, true_term, p_def, 1);
    fixture.entry(r, shared, r_def, 1);
    fixture.record(before, forged, 1);
    assert!(
        fixture.plan(forged).is_none(),
        "`(not p)` with `p = true` folds to `false`, never to `true`"
    );
}

/// NEGATIVE (guard: the fold is only for BOOLEAN CONSTANTS): a double
/// negation still declines, so the pre-existing fail-closed behaviour for
/// every non-constant `mk_not` fold is unchanged.
#[test]
fn not_constant_fold_declines_double_negation() {
    let mut terms = TermStore::new();
    let p = bool_fun(&mut terms, "pp", 0);
    let q = bool_fun(&mut terms, "pq", 0);
    let not_q = terms.mk_not_raw(q);
    let before = terms.mk_not_raw(p);
    // `p ↦ (not q)` makes `mk_not` collapse the rebuild to `q`.
    let p_def = terms.mk_app(Symbol::named("="), [p, not_q], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, p_def], terms);
    fixture.entry(p, not_q, p_def, 1);
    fixture.record(before, q, 1);
    assert!(
        fixture.plan(q).is_none(),
        "a double-negation collapse is not a constant fold and must decline"
    );
}

// ---- reflexivity folds (#4751) ----

/// GREEN: two distinct variables substituted to the SAME term collapse an
/// equality atom to `true`. The `refl` + `equiv_neg1` lift is re-derived by
/// the untouched strict checker.
#[test]
fn eq_refl_fold_derives_true_and_strict_checks() {
    let mut terms = TermStore::new();
    let f = terms.mk_var("f".to_owned(), Sort::Int);
    let g = terms.mk_var("g".to_owned(), Sort::Int);
    let b = terms.mk_var("b".to_owned(), Sort::Int);
    let other = bool_fun(&mut terms, "po", 0);
    let true_term = terms.true_term();
    let eq_fg = terms.mk_app(Symbol::named("="), [f, g], Sort::Bool);
    let before = terms.mk_app(Symbol::named("or"), [eq_fg, other], Sort::Bool);
    let f_def = terms.mk_app(Symbol::named("="), [f, b], Sort::Bool);
    let g_def = terms.mk_app(Symbol::named("="), [g, b], Sort::Bool);
    let after = terms.mk_app(Symbol::named("or"), [true_term, other], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, f_def, g_def], terms);
    fixture.entry(f, b, f_def, 1);
    fixture.entry(g, b, g_def, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// GREEN, the composed #4751 shape: the reflexivity fold feeds the negation
/// fold, which feeds the enclosing `or` congruence — the exact three-step
/// chain the CHC route needs, end to end under the strict checker.
#[test]
fn negated_reflexive_equality_folds_to_false_inside_a_disjunction() {
    let mut terms = TermStore::new();
    let f = terms.mk_var("f".to_owned(), Sort::Int);
    let g = terms.mk_var("g".to_owned(), Sort::Int);
    let b = terms.mk_var("b".to_owned(), Sort::Int);
    let other = bool_fun(&mut terms, "po", 0);
    let false_term = terms.false_term();
    let eq_fg = terms.mk_app(Symbol::named("="), [f, g], Sort::Bool);
    let not_eq = terms.mk_not_raw(eq_fg);
    let before = terms.mk_app(Symbol::named("or"), [not_eq, other], Sort::Bool);
    let f_def = terms.mk_app(Symbol::named("="), [f, b], Sort::Bool);
    let g_def = terms.mk_app(Symbol::named("="), [g, b], Sort::Bool);
    // `VariableSubstitution` rebuilds the `or` structurally, so the `false`
    // member is KEPT and the arity is preserved.
    let after = terms.mk_app(Symbol::named("or"), [false_term, other], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, f_def, g_def], terms);
    fixture.entry(f, b, f_def, 1);
    fixture.entry(g, b, g_def, 1);
    fixture.record(before, after, 1);
    fixture.assert_plan_is_strictly_checkable(after);
}

/// NEGATIVE (guard: the rebuilt arguments must be the SAME node): a forged
/// record claiming a NON-reflexive equality folded to `true` must decline.
/// Stated inside a disjunction so the forged target is not the trivially
/// derivable `(cl true)`.
#[test]
fn eq_refl_fold_declines_non_reflexive_equality() {
    let mut terms = TermStore::new();
    let f = terms.mk_var("f".to_owned(), Sort::Int);
    let g = terms.mk_var("g".to_owned(), Sort::Int);
    let b = terms.mk_var("b".to_owned(), Sort::Int);
    let c = terms.mk_var("c".to_owned(), Sort::Int);
    let other = bool_fun(&mut terms, "po", 0);
    let true_term = terms.true_term();
    let eq_fg = terms.mk_app(Symbol::named("="), [f, g], Sort::Bool);
    let before = terms.mk_app(Symbol::named("or"), [eq_fg, other], Sort::Bool);
    let f_def = terms.mk_app(Symbol::named("="), [f, b], Sort::Bool);
    let g_def = terms.mk_app(Symbol::named("="), [g, c], Sort::Bool);
    let forged = terms.mk_app(Symbol::named("or"), [true_term, other], Sort::Bool);

    let mut fixture = Fixture::new(vec![before, f_def, g_def], terms);
    fixture.entry(f, b, f_def, 1);
    fixture.entry(g, c, g_def, 1);
    fixture.record(before, forged, 1);
    assert!(
        fixture.plan(forged).is_none(),
        "`(= b c)` is not reflexive and must not fold to `true`"
    );
}

/// #4751 — consecutive merged rounds must leave a FREE stamp value between them.
///
/// [`Executor::extend_eq_diffvar_provenance`] files its records at
/// `watermark + 1`, and that value only exists as an unused slot if merged
/// rounds are spaced. With consecutive integers `watermark + 1` IS the next
/// round's stamp, so the fold channel ties with the `VariableSubstitution`
/// round instead of the unit-propagation round — the same collision in the
/// other direction (measured on `dillig12_m`: 76-78 premiseless `Trust` against
/// a 53 baseline, i.e. strictly worse than leaving it alone).
///
/// Asserted on `merge_propagation_records` directly rather than through a solve,
/// because the property is about the axis, not about any one fixture.
#[test]
fn consecutive_merged_rounds_leave_a_free_stamp_between_them() {
    let mut exec = Executor::new();
    let before = exec.ctx.terms.mk_var("before".to_owned(), Sort::Bool);
    let after = exec.ctx.terms.mk_var("after".to_owned(), Sort::Bool);
    for _ in 0..3 {
        exec.merge_propagation_records(PropagationRecords {
            rewrites: vec![crate::preprocess::PropagatedRewriteRecord {
                before,
                after,
                stamp: 1,
            }],
            ..PropagationRecords::default()
        });
    }
    let stamps: Vec<u32> = exec
        .propagated_value_provenance
        .rewrites
        .iter()
        .map(|record| record.stamp)
        .collect();
    assert_eq!(stamps.len(), 3, "each merge must file its own record");
    for pair in stamps.windows(2) {
        assert!(
            pair[1] >= pair[0] + 2,
            "consecutive rounds landed at {pair:?}, leaving no value for a channel \
             that runs between them"
        );
    }
}

/// #4751 — and the spacing must not disturb the ORDER the replay reads.
///
/// Eligibility is `entry.stamp <= target.stamp` and both sides come from this
/// one axis, so what the replay actually depends on is that the stamps are
/// strictly increasing round over round and constant within a round. Pin both.
#[test]
fn the_spaced_axis_is_still_strictly_increasing_round_over_round() {
    let mut exec = Executor::new();
    let before = exec.ctx.terms.mk_var("before".to_owned(), Sort::Bool);
    let after = exec.ctx.terms.mk_var("after".to_owned(), Sort::Bool);
    let value = exec.ctx.terms.mk_bool(true);
    let mut expected_rounds: Vec<Vec<u32>> = Vec::new();
    for _ in 0..3 {
        // Two records with DIFFERENT in-batch stamps, as `PropagateValues`
        // produces across its own `apply` calls.
        exec.merge_propagation_records(PropagationRecords {
            rewrites: vec![
                crate::preprocess::PropagatedRewriteRecord {
                    before,
                    after,
                    stamp: 1,
                },
                crate::preprocess::PropagatedRewriteRecord {
                    before: after,
                    after: before,
                    stamp: 2,
                },
            ],
            entries: vec![crate::preprocess::PropagatedEntrySource {
                expr: before,
                value,
                source_assertion: after,
                stamp: 1,
            }],
            ..PropagationRecords::default()
        });
        expected_rounds.push(
            exec.propagated_value_provenance
                .rewrites
                .iter()
                .map(|record| record.stamp)
                .collect(),
        );
    }
    let stamps = expected_rounds.last().expect("three rounds were merged");
    assert_eq!(stamps.len(), 6);
    // Within a round the two in-batch stamps stay ordered…
    for round in 0..3 {
        assert!(
            stamps[round * 2] < stamps[round * 2 + 1],
            "in-batch order must be preserved: {stamps:?}"
        );
    }
    // …and every later round is strictly above every earlier one.
    for round in 1..3 {
        assert!(
            stamps[round * 2] > stamps[round * 2 - 1],
            "a later round must be strictly above the previous one: {stamps:?}"
        );
    }
}
