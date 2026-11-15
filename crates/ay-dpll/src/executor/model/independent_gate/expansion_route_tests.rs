// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The expansion route in isolation: it confirms only a TRUE conjunct of the
//! emitted model, never through a forged hint, a Skolem shared across
//! instances, a subformula memoized in another environment, a Boolean
//! connective walked at the wrong polarity, or for a false model; it reads
//! only hints bound to the current query, and runs after every other route.

use std::cell::Cell;

use ay_core::term::{Symbol, TermData};
use ay_core::{Sort, TermId};
use ay_frontend::parse;
use num_bigint::BigInt;
use num_rational::BigRational;

use super::super::{Executor, QuantifiedModelCheck};
use crate::executor::expansion::{ExpansionHints, InstanceHints};
use crate::executor::QueryAuthorityEpoch;

/// An executor whose emitted model sets the Real constant `c` to `value`.
fn model_with_c(value: i64) -> Executor {
    let script =
        format!("(set-logic LRA)(declare-fun c () Real)(assert (= c {value}.0))(check-sat)");
    let commands = parse(&script).expect("valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec.execute_all(&commands).expect("execute succeeds");
    assert_eq!(outputs.last().map(String::as_str), Some("sat"));
    assert!(exec.last_model.is_some(), "the fixture emits a model");
    exec
}

fn rat(exec: &mut Executor, num: i64, den: i64) -> TermId {
    exec.ctx
        .terms
        .mk_rational(BigRational::new(BigInt::from(num), BigInt::from(den)))
}

fn real(exec: &mut Executor, name: &str) -> TermId {
    exec.ctx.terms.mk_var(name, Sort::Real)
}

fn bound(name: &str) -> Vec<(String, Sort)> {
    vec![(name.to_string(), Sort::Real)]
}

/// `∀x ∃y. x < y < x + c` (true iff `c > 0`), and its `∃y` subterm.
fn open_interval(exec: &mut Executor) -> (TermId, TermId) {
    let (x, y, c) = (real(exec, "x"), real(exec, "y"), real(exec, "c"));
    let terms = &mut exec.ctx.terms;
    let above = terms.mk_gt(y, x);
    let top = terms.mk_add(vec![x, c]);
    let below = terms.mk_lt(y, top);
    let body = terms.mk_and(vec![above, below]);
    let inner = terms.mk_exists(bound("y"), body);
    (terms.mk_forall(bound("x"), inner), inner)
}

/// `x + num/den`, spelled over the enclosing binder `x`.
fn shifted_x(exec: &mut Executor, num: i64, den: i64) -> TermId {
    let (x, delta) = (real(exec, "x"), rat(exec, num, den));
    exec.ctx.terms.mk_add(vec![x, delta])
}

fn install(exec: &mut Executor, key: TermId, tuples: Vec<Vec<TermId>>) {
    let mut hints = InstanceHints::default();
    hints.insert(key, tuples);
    exec.qlra_lane.expansion_hints = Some(Box::new(ExpansionHints {
        epoch: exec.query_authority_epoch.clone(),
        roots: exec.independent_gate_query_roots().unwrap(),
        stamp: exec.ctx.terms.snapshot_stamp(),
        tuples: hints,
        consulted: Cell::new(0),
        confirmed: Cell::new(0),
    }));
}

fn consulted(exec: &Executor) -> u32 {
    exec.qlra_lane
        .expansion_hints
        .as_deref()
        .map_or(0, |hints| hints.consulted.get())
}

fn confirms(exec: &mut Executor, conjunct: TermId) -> bool {
    matches!(
        exec.quantified_gate_expansion_check(conjunct),
        Some(QuantifiedModelCheck::Confirmed)
    )
}

#[test]
fn a_true_conjunct_is_confirmed_through_its_hinted_witness() {
    let mut exec = model_with_c(1);
    let (root, inner) = open_interval(&mut exec);
    let witness = shifted_x(&mut exec, 1, 2);
    install(&mut exec, inner, vec![vec![witness]]);
    assert!(confirms(&mut exec, root));
}

#[test]
fn a_hint_for_a_false_model_is_refused() {
    // c = 0: the open interval is empty, so the conjunct is FALSE in the
    // model; the witness that is right for every c > 0 cannot confirm it.
    for value in [0, -1] {
        let mut exec = model_with_c(value);
        let (root, inner) = open_interval(&mut exec);
        let witness = shifted_x(&mut exec, 1, 2);
        install(&mut exec, inner, vec![vec![witness]]);
        assert!(!confirms(&mut exec, root), "c = {value}");
    }
}

#[test]
fn a_forged_hint_gives_no_confirmation() {
    let mut exec = model_with_c(1);
    let (root, inner) = open_interval(&mut exec);
    let (past, zero) = (shifted_x(&mut exec, 5, 1), rat(&mut exec, 0, 1));
    install(&mut exec, inner, vec![vec![past], vec![zero]]);
    assert!(!confirms(&mut exec, root));
    // Keyed on the wrong subterm: nothing expands the existential.
    let mut exec = model_with_c(1);
    let (root, _) = open_interval(&mut exec);
    let witness = shifted_x(&mut exec, 1, 2);
    install(&mut exec, root, vec![vec![witness]]);
    assert!(!confirms(&mut exec, root));
}

#[test]
fn hints_of_another_query_are_ignored() {
    let mut exec = model_with_c(1);
    let (root, inner) = open_interval(&mut exec);
    let witness = shifted_x(&mut exec, 1, 2);
    install(&mut exec, inner, vec![vec![witness]]);
    if let Some(hints) = exec.qlra_lane.expansion_hints.as_deref_mut() {
        hints.epoch = QueryAuthorityEpoch::fresh();
    }
    assert!(!confirms(&mut exec, root));
    assert_eq!(consulted(&exec), 0, "stale hints are never read");
    install(&mut exec, inner, vec![vec![witness]]);
    if let Some(hints) = exec.qlra_lane.expansion_hints.as_deref_mut() {
        hints.roots.push(root);
    }
    assert!(
        !confirms(&mut exec, root),
        "hints for other roots are ignored"
    );
}

/// ROUTE ORDER: a conjunct an existing route decides never reaches the
/// expansion route — a confirmation stays the prefix route's and a
/// refutation is never overridden — and an undecided one reaches it last.
#[test]
fn the_route_runs_only_after_every_existing_route() {
    let mut exec = model_with_c(1);
    let (x, c) = (real(&mut exec, "x"), real(&mut exec, "c"));
    let (open, inner) = open_interval(&mut exec);
    let witness = shifted_x(&mut exec, 1, 2);
    let terms = &mut exec.ctx.terms;
    let shifted = terms.mk_add(vec![x, c]);
    let valid_body = terms.mk_ge(shifted, x);
    let valid = terms.mk_forall(bound("x"), valid_body);
    let false_body = terms.mk_gt(x, c);
    let refuted = terms.mk_forall(bound("x"), false_body);
    let mut hints = InstanceHints::default();
    hints.insert(inner, vec![vec![witness]]);
    for key in [valid, refuted] {
        hints.insert(key, vec![vec![witness]]);
    }
    install(&mut exec, inner, vec![vec![witness]]);
    if let Some(installed) = exec.qlra_lane.expansion_hints.as_deref_mut() {
        installed.tuples = hints;
    }

    let outcome = exec.check_quantified_conjunct_against_model(valid);
    assert!(matches!(outcome, QuantifiedModelCheck::Confirmed));
    assert_eq!(consulted(&exec), 0, "the prefix route decided it first");
    let outcome = exec.check_quantified_conjunct_against_model(refuted);
    assert!(matches!(outcome, QuantifiedModelCheck::Refuted { .. }));
    assert_eq!(consulted(&exec), 0, "a refutation is never re-opened");
    let outcome = exec.check_quantified_conjunct_against_model(open);
    assert!(matches!(outcome, QuantifiedModelCheck::Confirmed));
    assert_eq!(
        consulted(&exec),
        1,
        "undecided by every route: consulted last"
    );

    exec.qlra_lane.expansion_hints = None;
    let outcome = exec.check_quantified_conjunct_against_model(open);
    assert!(
        !matches!(outcome, QuantifiedModelCheck::Confirmed),
        "without hints no existing route confirms the ∀∃ open interval"
    );
}

/// The route's own Skolem constants stay FREE: `∀x ∃y. (x < y < x + c) ∨
/// x = 0` is false when `c = 0` (take x = 1), and its expansion
/// `¬((sk < sk + ½ < sk + c) ∨ sk = 0)` is refutable only if `sk` were
/// pinned to a default value 0.
#[test]
fn the_gate_skolems_are_never_pinned() {
    let mut exec = model_with_c(0);
    let (x, y, c) = (
        real(&mut exec, "x"),
        real(&mut exec, "y"),
        real(&mut exec, "c"),
    );
    let zero = rat(&mut exec, 0, 1);
    let witness = shifted_x(&mut exec, 1, 2);
    let terms = &mut exec.ctx.terms;
    let above = terms.mk_gt(y, x);
    let top = terms.mk_add(vec![x, c]);
    let below = terms.mk_lt(y, top);
    let interval = terms.mk_and(vec![above, below]);
    let at_zero = terms.mk_eq(x, zero);
    let body = terms.mk_or(vec![interval, at_zero]);
    let inner = terms.mk_exists(bound("y"), body);
    let root = terms.mk_forall(bound("x"), inner);
    install(&mut exec, inner, vec![vec![witness]]);
    assert!(!confirms(&mut exec, root));
}

/// Each instance environment gets its OWN Skolems: `∃x ∀y. y < x ∨ y > x`
/// is FALSE (take y = x), and with hints x := 0 and x := 1 its expansion
/// `(y₀ = 0) ∧ (y₁ = 1)` is satisfiable. One Skolem shared across both
/// instances would turn it into the refutable `y = 0 ∧ y = 1` and confirm
/// the false conjunct.
#[test]
fn skolems_are_per_instance() {
    let mut exec = model_with_c(1);
    let (x, y) = (real(&mut exec, "x"), real(&mut exec, "y"));
    let (zero, one) = (rat(&mut exec, 0, 1), rat(&mut exec, 1, 1));
    let terms = &mut exec.ctx.terms;
    let lt = terms.mk_lt(y, x);
    let gt = terms.mk_gt(y, x);
    let body = terms.mk_or(vec![lt, gt]);
    let inner = terms.mk_forall(bound("y"), body);
    let root = terms.mk_exists(bound("x"), inner);
    install(&mut exec, root, vec![vec![zero], vec![one]]);
    assert!(!confirms(&mut exec, root), "a false conjunct confirmed");
}

/// End to end through the whole conjunct check: with the open interval
/// EMPTY in the model (c ≤ 0) no route — the expansion route included, fed
/// the witness that is right for every c > 0 plus forged ones — confirms.
#[test]
fn the_full_gate_never_confirms_a_false_conjunct_through_hints() {
    for value in [0, -1] {
        let mut exec = model_with_c(value);
        let (root, inner) = open_interval(&mut exec);
        let witness = shifted_x(&mut exec, 1, 2);
        let forged = shifted_x(&mut exec, 5, 1);
        let zero = rat(&mut exec, 0, 1);
        install(
            &mut exec,
            inner,
            vec![vec![witness], vec![forged], vec![zero]],
        );
        let outcome = exec.check_quantified_conjunct_against_model(root);
        assert!(
            !matches!(outcome, QuantifiedModelCheck::Confirmed),
            "c = {value}: a false conjunct must never be confirmed"
        );
    }
}

/// `∀x. x > y` — FALSE for every `y` — with the hint `x := y − 1` that
/// refutes its universal reading; returns the subterm and the hint.
fn nowhere_above(exec: &mut Executor) -> (TermId, Vec<Vec<TermId>>) {
    let (x, y, one) = (real(exec, "x"), real(exec, "y"), rat(exec, 1, 1));
    let terms = &mut exec.ctx.terms;
    let above = terms.mk_gt(x, y);
    let below = terms.mk_sub(vec![y, one]);
    (terms.mk_forall(bound("x"), above), vec![vec![below]])
}

/// `c > 0` and `c ≤ 0`: TRUE and FALSE in the `c = 1` model.
fn signs(exec: &mut Executor) -> (TermId, TermId) {
    let (c, zero) = (real(exec, "c"), rat(exec, 0, 1));
    let terms = &mut exec.ctx.terms;
    (terms.mk_gt(c, zero), terms.mk_le(c, zero))
}

fn app(exec: &mut Executor, name: &str, args: Vec<TermId>) -> TermId {
    exec.ctx.terms.mk_app(Symbol::named(name), args, Sort::Bool)
}

fn is_app(exec: &Executor, term: TermId, name: &str) -> bool {
    matches!(exec.ctx.terms.get(term), TermData::App(symbol, _) if symbol.name() == name)
}

/// `∀y. body`, installed with the hint for the `nowhere_above` subterm.
fn confirms_under_hint(
    exec: &mut Executor,
    key: TermId,
    hint: Vec<Vec<TermId>>,
    body: TermId,
) -> bool {
    let root = exec.ctx.terms.mk_forall(bound("y"), body);
    install(exec, key, hint);
    confirms(exec, root)
}

/// The Bool `ite` CONDITION occurs at both polarities: `¬ite(q, a, b)` is
/// `(q ∧ ¬a) ∨ (¬q ∧ ¬b)`. With `q = ∀x. x > y` (false everywhere),
/// `∀y. ite(q, c > 0, c ≤ 0)` is FALSE at `c = 1`; its expansion keeps the
/// Skolemized `¬q` arm satisfiable, so it is never confirmed. Walking the
/// else arm's condition POSITIVELY expands both arms' `q` at the refuting
/// hint and confirms the false conjunct. The twin with swapped arms is TRUE
/// and is confirmed, so the refusal is not a shape decline.
#[test]
fn a_bool_ite_condition_keeps_both_polarities() {
    for (swapped, expect) in [(false, false), (true, true)] {
        let mut exec = model_with_c(1);
        let (cond, hint) = nowhere_above(&mut exec);
        let (pos, nonpos) = signs(&mut exec);
        let (then, other) = if swapped {
            (nonpos, pos)
        } else {
            (pos, nonpos)
        };
        let body = exec.ctx.terms.mk_ite(cond, then, other);
        assert!(
            matches!(exec.ctx.terms.get(body), TermData::Ite(..)),
            "the Bool ite reaches the walker as an ite"
        );
        let verdict = confirms_under_hint(&mut exec, cond, hint, body);
        assert_eq!(verdict, expect, "swapped arms: {swapped}");
    }
}

/// The Bool equivalence family through `equiv`, each at the polarity that
/// reaches its ⊕ or its ⟺ arm. With `q = ∀x. x > y` (false everywhere) and
/// `c = 1`, every FALSE shape below must be refused and its TRUE twin
/// confirmed; swapping the two arms of either `equiv` branch confirms a
/// false conjunct.
#[test]
fn bool_equivalences_keep_their_polarity() {
    // (operator, wrap in `not`, second operand is `c > 0`, conjunct TRUE)
    let cases = [
        ("=", false, true, false),
        ("=", false, false, true),
        ("=", true, false, false),
        ("=", true, true, true),
        ("xor", false, false, false),
        ("xor", false, true, true),
        ("xor", true, true, false),
        ("xor", true, false, true),
        ("distinct", false, false, false),
        ("distinct", false, true, true),
        ("distinct", true, true, false),
        ("distinct", true, false, true),
    ];
    for (op, negated, positive, expect) in cases {
        let mut exec = model_with_c(1);
        let (q, hint) = nowhere_above(&mut exec);
        let (pos, nonpos) = signs(&mut exec);
        let other = if positive { pos } else { nonpos };
        let inner = app(&mut exec, op, vec![q, other]);
        assert!(is_app(&exec, inner, op));
        let body = if negated {
            let not = exec.ctx.terms.mk_not(inner);
            assert!(matches!(exec.ctx.terms.get(not), TermData::Not(t) if *t == inner));
            not
        } else {
            inner
        };
        let verdict = confirms_under_hint(&mut exec, q, hint, body);
        assert_eq!(
            verdict,
            expect,
            "({op} q {}) negated={negated}",
            if positive { "c>0" } else { "c<=0" }
        );
    }
}

/// `=>` arrives desugared from the frontend, but the walker's arm must still
/// flip its premises: `∀y. (c > 0) ⇒ (∀x. x > y)` is FALSE at `c = 1` and
/// never confirmed; `∀y. (c ≤ 0) ⇒ (∀x. x > y)` is TRUE and confirmed.
#[test]
fn an_implication_flips_its_premises() {
    for (premise_true, expect) in [(true, false), (false, true)] {
        let mut exec = model_with_c(1);
        let (q, hint) = nowhere_above(&mut exec);
        let (pos, nonpos) = signs(&mut exec);
        let premise = if premise_true { pos } else { nonpos };
        let body = app(&mut exec, "=>", vec![premise, q]);
        assert!(is_app(&exec, body, "=>"));
        let verdict = confirms_under_hint(&mut exec, q, hint, body);
        assert_eq!(verdict, expect, "premise c>0: {premise_true}");
    }
}

/// A memoized subformula is reused only in ITS OWN environment. The binder
/// `c` shadows the model constant `c = 1`, so `T = ∃y. 0 < y < c` is the
/// same term at the root (about the constant) and under `∃c` (about the
/// binder). `R = (T ∧ c ≤ 0) ∨ ∃c. (T ∧ c < 0)` is FALSE (T needs c > 0);
/// with hints `y := c/2` and `c := −1` its expansion `(¬T[½] ∨ c > 0) ∧
/// (¬T[−½] ∨ −1 ≥ 0)` is satisfiable. Reusing the root's `¬T[½]` (false)
/// under `c := −1` refutes it and confirms the false conjunct; the TRUE twin
/// `(T ∧ c > 0) ∨ …` is confirmed, so the shadowing is not a shape decline.
#[test]
fn a_memoized_subformula_is_reused_only_in_its_own_environment() {
    for (root_sign_true, expect) in [(false, false), (true, true)] {
        let mut exec = model_with_c(1);
        let (y, c) = (real(&mut exec, "y"), real(&mut exec, "c"));
        let (zero, half, minus_one) = (
            rat(&mut exec, 0, 1),
            rat(&mut exec, 1, 2),
            rat(&mut exec, -1, 1),
        );
        let terms = &mut exec.ctx.terms;
        let positive = terms.mk_gt(y, zero);
        let below = terms.mk_lt(y, c);
        let window = terms.mk_and(vec![positive, below]);
        let t = terms.mk_exists(bound("y"), window);
        let root_sign = if root_sign_true {
            terms.mk_gt(c, zero)
        } else {
            terms.mk_le(c, zero)
        };
        let at_root = terms.mk_and(vec![t, root_sign]);
        let negative = terms.mk_lt(c, zero);
        let inner_body = terms.mk_and(vec![t, negative]);
        let inner = terms.mk_exists(bound("c"), inner_body);
        let root = terms.mk_or(vec![at_root, inner]);
        let witness = terms.mk_mul(vec![c, half]);
        let mut hints = InstanceHints::default();
        hints.insert(t, vec![vec![witness]]);
        hints.insert(inner, vec![vec![minus_one]]);
        install(&mut exec, t, Vec::new());
        if let Some(installed) = exec.qlra_lane.expansion_hints.as_deref_mut() {
            installed.tuples = hints;
        }
        let verdict = confirms(&mut exec, root);
        assert_eq!(verdict, expect, "root sign c > 0: {root_sign_true}");
    }
}
