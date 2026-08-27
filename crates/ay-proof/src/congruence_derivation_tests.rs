// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Coverage for the congruence-explanation LOWERING.
//!
//! The bar, and how each layer meets it:
//!
//! 1. **Every emitted step is re-validated by the UNTOUCHED strict checker.**
//!    [`strictly_checks`] splices the planned fragment into a scratch proof,
//!    closes it over the negation of each of its own literals, and runs
//!    `check_proof_strict`. No validator is relaxed, no rule is added: the
//!    fragment either replays under the same checker the mandatory gate uses
//!    or the test fails.
//! 2. **Adversarial negatives**, each naming a CONCRETE falsifying assignment
//!    and checking it in-test with [`super::sweep_tests::falsifies`].
//! 3. **Printer pins**: the exact wire text of every rule the lowering emits.
//! 4. **A guard-mutation ledger** ([`GUARD_MUTATION_LEDGER`]).

use super::{plan_euf_congruence_derivation, CongruenceDerivation};
use crate::alethe_printer::AlethePrinter;
use crate::checker::ProofCheckError;
use crate::quality::check_proof_strict;
use ay_core::{ArraySort, ProofId, ProofStep, Sort, Symbol, TermId, TermStore};

// ===== fixture helpers =====

/// `(= lhs rhs)` built RAW, so a fixture controls operand order exactly.
pub(super) fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

pub(super) fn neq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    let equality = eq(terms, lhs, rhs);
    terms.mk_not_raw(equality)
}

pub(super) fn fun(terms: &mut TermStore, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(Symbol::named(name), args, sort)
}

pub(super) fn uninterpreted() -> Sort {
    Sort::Uninterpreted("U".to_string())
}

pub(super) fn var(terms: &mut TermStore, name: &str) -> TermId {
    terms.mk_var(name, uninterpreted())
}

/// Re-validate a planned fragment with the strict checker, changing nothing
/// about it.
///
/// The checker demands a closed refutation, so the fragment is closed over the
/// negation of each literal of its own conclusion: assume `¬l`, resolve it
/// away, and finish on the empty clause. Every step of the DERIVATION is
/// validated on the way, by the same `validate_step` the mandatory gate runs.
pub(super) fn strictly_checks(
    terms: &mut TermStore,
    derivation: &CongruenceDerivation,
) -> Result<(), ProofCheckError> {
    let proof = super::close_congruence_derivation(terms, derivation);
    check_proof_strict(&proof, terms).map(|_| ())
}

/// Plan a lowering and insist the strict checker replays every step of it.
pub(super) fn lower(terms: &mut TermStore, literals: &[TermId]) -> CongruenceDerivation {
    let derivation =
        plan_euf_congruence_derivation(terms, literals).expect("this clause must be derivable");
    assert_eq!(
        derivation.clause, literals,
        "the last step must reproduce the recorded clause byte for byte"
    );
    strictly_checks(terms, &derivation).expect("every emitted step must strict-check");
    for step in &derivation.steps {
        if let ProofStep::Step { rule, .. } = step {
            assert!(
                ay_core::is_checkable_alethe_rule(rule.name()),
                "emitted rule {} is not externally checkable",
                rule.name()
            );
            assert_ne!(ay_core::wire_rule_name(rule.name()), "hole");
        } else {
            panic!("the lowering emits only generic steps");
        }
    }
    derivation
}

pub(super) fn rules(derivation: &CongruenceDerivation) -> Vec<String> {
    derivation
        .steps
        .iter()
        .map(|step| match step {
            ProofStep::Step { rule, .. } => rule.name().to_string(),
            _ => "?".to_string(),
        })
        .collect()
}

// ===== the measured shape =====

/// The QF_AX explanation the census names, in its own words:
///
/// ```text
/// (or (= (select (store C i2 v) i0) (select C i0))
///     (not (= i0 i3))
///     (not (= e (select (store C i2 v) i3)))
///     (not (= e (select C i0))))
/// ```
///
/// Nothing is stated about `(select (store C i2 v) i0)`: it is reached from
/// `(select (store C i2 v) i3)` by CONGRUENCE on the index position under
/// `i0 = i3`. That is exactly the link `eq_transitive` alone cannot supply,
/// and the reason this lowering exists.
fn measured_shape(terms: &mut TermStore) -> Vec<TermId> {
    let index = Sort::Int;
    let element = uninterpreted();
    let array = Sort::Array(Box::new(ArraySort {
        index_sort: index.clone(),
        element_sort: element.clone(),
    }));
    let c = terms.mk_var("C", array.clone());
    let i0 = terms.mk_var("i0", index.clone());
    let i2 = terms.mk_var("i2", index.clone());
    let i3 = terms.mk_var("i3", index);
    let v = terms.mk_var("v", element.clone());
    let e = terms.mk_var("e", element.clone());
    let stored = fun(terms, "store", vec![c, i2, v], array);
    let stored_i0 = fun(terms, "select", vec![stored, i0], element.clone());
    let stored_i3 = fun(terms, "select", vec![stored, i3], element.clone());
    let c_i0 = fun(terms, "select", vec![c, i0], element);
    vec![
        eq(terms, stored_i0, c_i0),
        neq(terms, i0, i3),
        neq(terms, e, stored_i3),
        neq(terms, e, c_i0),
    ]
}

#[test]
fn lowers_the_measured_qf_ax_explanation_to_checkable_rules() {
    let mut terms = TermStore::new();
    let clause = measured_shape(&mut terms);
    let derivation = lower(&mut terms, &clause);
    let emitted = rules(&derivation);
    assert!(
        emitted.contains(&"eq_congruent".to_string()),
        "the index-position congruence must be derived: {emitted:?}"
    );
    assert!(
        emitted.contains(&"eq_transitive".to_string()),
        "the explanation path must be derived: {emitted:?}"
    );
    assert!(
        emitted.contains(&"reordering".to_string()),
        "the recorded order puts the conclusion FIRST: {emitted:?}"
    );
}

#[test]
fn lowers_a_pure_transitivity_chain() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let c = var(&mut terms, "c");
    let clause = vec![
        neq(&mut terms, a, b),
        neq(&mut terms, b, c),
        eq(&mut terms, a, c),
    ];
    let derivation = lower(&mut terms, &clause);
    assert_eq!(rules(&derivation), vec!["eq_transitive".to_string()]);
    assert_eq!(derivation.steps.len(), 1);
}

#[test]
fn lowers_a_one_step_congruence() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let fa = fun(&mut terms, "f", vec![a], uninterpreted());
    let fb = fun(&mut terms, "f", vec![b], uninterpreted());
    let clause = vec![neq(&mut terms, a, b), eq(&mut terms, fa, fb)];
    let derivation = lower(&mut terms, &clause);
    assert_eq!(rules(&derivation), vec!["eq_congruent".to_string()]);
}

#[test]
fn lowers_a_nested_congruence() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let ga = fun(&mut terms, "g", vec![a], uninterpreted());
    let gb = fun(&mut terms, "g", vec![b], uninterpreted());
    let fga = fun(&mut terms, "f", vec![ga], uninterpreted());
    let fgb = fun(&mut terms, "f", vec![gb], uninterpreted());
    let clause = vec![neq(&mut terms, a, b), eq(&mut terms, fga, fgb)];
    let derivation = lower(&mut terms, &clause);
    let emitted = rules(&derivation);
    assert_eq!(
        emitted,
        vec![
            "eq_congruent".to_string(),
            "eq_congruent".to_string(),
            "th_resolution".to_string(),
            "reordering".to_string(),
        ],
        "the inner congruence is discharged by resolution, not assumed; the \
         resolvent lists the conclusion first, so the recorded order is restored"
    );
}

#[test]
fn an_unused_hypothesis_is_weakened_back_in() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let c = var(&mut terms, "c");
    let d = var(&mut terms, "d");
    // `c = d` plays no part in deriving `a = b`, but the recorded clause
    // carries it and every consumer references that exact clause.
    let clause = vec![
        neq(&mut terms, a, b),
        neq(&mut terms, c, d),
        eq(&mut terms, a, b),
    ];
    let derivation = plan_euf_congruence_derivation(&mut terms, &clause);
    // A one-edge HYPOTHESIS path is a propositional tautology, not a
    // congruence explanation: out of scope, and owned by `bool_tautology`.
    assert!(derivation.is_none());

    let fa = fun(&mut terms, "f", vec![a], uninterpreted());
    let fb = fun(&mut terms, "f", vec![b], uninterpreted());
    let clause = vec![
        neq(&mut terms, a, b),
        neq(&mut terms, c, d),
        eq(&mut terms, fa, fb),
    ];
    let derivation = lower(&mut terms, &clause);
    let emitted = rules(&derivation);
    assert_eq!(
        emitted,
        vec![
            "eq_congruent".to_string(),
            "weakening".to_string(),
            "reordering".to_string(),
        ],
        "the unused hypothesis is re-introduced by weakening, which can only \
         APPEND it, so the recorded order is then restored: {emitted:?}"
    );
}

#[test]
fn the_conclusion_may_sit_at_any_position() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let c = var(&mut terms, "c");
    let first = vec![
        eq(&mut terms, a, c),
        neq(&mut terms, a, b),
        neq(&mut terms, b, c),
    ];
    let derivation = lower(&mut terms, &first);
    assert_eq!(
        rules(&derivation),
        vec!["eq_transitive".to_string(), "reordering".to_string()],
        "eq_transitive fixes the conclusion LAST, so the recorded order is restored"
    );
}

#[test]
fn a_repeated_premise_equality_is_contracted() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let gab = fun(&mut terms, "g", vec![a, b], uninterpreted());
    let gba = fun(&mut terms, "g", vec![b, a], uninterpreted());
    // `eq_congruent` consumes ONE premise per differing argument position, so
    // both positions need `(not (= a b))` and the tautology clause repeats it.
    let clause = vec![neq(&mut terms, a, b), eq(&mut terms, gab, gba)];
    let derivation = lower(&mut terms, &clause);
    assert_eq!(
        rules(&derivation),
        vec!["eq_congruent".to_string(), "contraction".to_string()],
        "the repeat is removed by contraction, never by dropping a premise"
    );
}

#[path = "congruence_derivation_negative_tests.rs"]
mod negatives;

#[test]
fn an_intermediate_equality_mk_eq_would_rewrite_is_still_derived() {
    let mut terms = TermStore::new();
    let element = uninterpreted();
    let array = Sort::Array(Box::new(ArraySort {
        index_sort: Sort::Int,
        element_sort: element.clone(),
    }));
    let a = terms.mk_var("a", array.clone());
    let b = terms.mk_var("b", array.clone());
    let i = terms.mk_var("i", Sort::Int);
    let k = terms.mk_var("k", Sort::Int);
    let v = terms.mk_var("v", element.clone());
    let stored = fun(&mut terms, "store", vec![a, i, v], array);
    // THE PREMISE THIS TEST RESTS ON, measured rather than assumed: `mk_eq`
    // does NOT build `(= (store a i v) a)` — its self-store rule rewrites the
    // pair into `(= (select a i) v)`, a term that cannot carry the congruence.
    let folded = terms.mk_eq(stored, a);
    assert!(
        !matches!(terms.get(folded), ay_core::TermData::App(Symbol::Named(name), args)
            if name == "=" && args.as_slice() == [stored, a]),
        "precondition: mk_eq must rewrite this pair, or the test proves nothing"
    );
    let read_stored = fun(&mut terms, "select", vec![stored, k], element.clone());
    let read_a = fun(&mut terms, "select", vec![a, k], element);
    // `(store a i v) = b`, `b = a` |= `(select (store a i v) k) = (select a k)`
    // — the congruence needs the INTERMEDIATE `(store a i v) = a`.
    let clause = vec![
        neq(&mut terms, stored, b),
        neq(&mut terms, b, a),
        eq(&mut terms, read_stored, read_a),
    ];
    let derivation = lower(&mut terms, &clause);
    assert_eq!(
        rules(&derivation),
        vec![
            "eq_transitive".to_string(),
            "eq_reflexive".to_string(),
            "eq_congruent".to_string(),
            "th_resolution".to_string(),
            "th_resolution".to_string(),
            "reordering".to_string(),
        ],
        "the shared index position gets the reflexive hypothesis `eq_congruent`'s \
         full arity needs, discharged by `eq_reflexive`"
    );
}

// ===== printer pins =====

#[test]
fn every_emitted_rule_lowers_to_its_own_externally_checkable_wire_name() {
    for name in [
        "eq_congruent",
        "eq_reflexive",
        "eq_transitive",
        "th_resolution",
        "contraction",
        "weakening",
        "reordering",
    ] {
        assert!(
            ay_core::is_checkable_alethe_rule(name),
            "{name} must be a pinned Alethe rule"
        );
        assert_eq!(ay_core::wire_rule_name(name), name);
    }
}

#[test]
fn the_lowered_steps_print_their_exact_wire_text() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let ga = fun(&mut terms, "g", vec![a], uninterpreted());
    let gb = fun(&mut terms, "g", vec![b], uninterpreted());
    let fga = fun(&mut terms, "f", vec![ga], uninterpreted());
    let fgb = fun(&mut terms, "f", vec![gb], uninterpreted());
    let clause = vec![neq(&mut terms, a, b), eq(&mut terms, fga, fgb)];
    let derivation = lower(&mut terms, &clause);
    let printed: Vec<String> = derivation
        .steps
        .iter()
        .enumerate()
        .map(|(index, step)| {
            AlethePrinter::new(&terms)
                .format_step(step, ProofId(u32::try_from(index).expect("fits")))
                .expect("every emitted step must render")
        })
        .collect();
    assert_eq!(
        printed,
        vec![
            "(step t0 (cl (not (= a b)) (= (g b) (g a))) :rule eq_congruent)".to_string(),
            "(step t1 (cl (not (= (g b) (g a))) (= (f (g a)) (f (g b)))) :rule eq_congruent)"
                .to_string(),
            "(step t2 (cl (= (f (g a)) (f (g b))) (not (= a b))) :rule th_resolution \
             :premises (t1 t0))"
                .to_string(),
            "(step t3 (cl (not (= a b)) (= (f (g a)) (f (g b)))) :rule reordering :premises (t2))"
                .to_string(),
        ]
    );
    for line in &printed {
        assert!(!line.contains(":rule hole"), "{line}");
        assert!(!line.contains(":rule trust"), "{line}");
        assert!(!line.contains("invalid"), "{line}");
    }
}

/// Each guard deleted or weakened, `ay-proof --lib` re-run, the named test
/// OBSERVED failing, then restored. Run recorded 2026-08-22, one mutation at a
/// time. `NEGATIVE` rows are results, not omissions.
pub(super) const GUARD_MUTATION_LEDGER: &[(&str, &str)] = &[
    (
        "parse_clause: no repeated literal",
        "RED — declines_a_repeated_literal",
    ),
    (
        "parse_clause: every literal is a (possibly negated) equality",
        "RED — declines_a_smuggled_non_equality_literal",
    ),
    (
        "finish: a repeated literal is contracted before weakening/reordering",
        "RED — a_repeated_premise_equality_is_contracted",
    ),
    (
        "parse_clause: a hypothesis is a NEGATED equality only",
        "SOUNDNESS-CRITICAL, and not mutated: reading a positive equality as a \
         hypothesis would derive `(cl (= a b) (= (f a) (f b)))`, FALSE under \
         a := 0, b := 1, f(0) := 2, f(1) := 3. \
         declines_a_positive_equality_read_as_a_hypothesis checks that \
         countermodel in-test with the independent evaluator.",
    ),
    (
        "parse_clause: exactly one positive equality",
        "NEGATIVE — weakening it to `keep the last positive` fails no test, and \
         cannot be unsound: a surplus positive literal is neither a hypothesis \
         (only the NEGATED branch produces those) nor the goal, so it is simply \
         absent from the derived clause and `weakening` adds it back. SCOPE.",
    ),
    (
        "congruence: same head symbol / same arity",
        "NEGATIVE — deleting either fails no test. The closure only ever records \
         a congruence edge between nodes sharing a (symbol, sort, arity) head \
         slot, so the condition is unreachable; `validate_euf_congruent` \
         re-checks it anyway. Fail-fast, not a guard.",
    ),
    (
        "derive_goal: a one-edge hypothesis path is not an explanation",
        "NEGATIVE — replacing it with `self.edge_fact(edge)` fails no test, \
         because the returned `Fact::Stated` carries no step and \
         `plan_euf_congruence_derivation` then declines on the `Fact::Derived` \
         destructuring. The property is pinned directly by the first assertion \
         of an_unused_hypothesis_is_weakened_back_in.",
    ),
    (
        "finish: the derived clause is a subset of the recorded one",
        "NEGATIVE — deleting it fails no test. Every literal of a derived clause \
         is a recorded hypothesis literal or the recorded goal literal, and \
         every intermediate is resolved away, so the property holds by \
         construction. Fail-closed assertion.",
    ),
    (
        "equality(): reflexive and same-sort guards on the RAW builder",
        "NEGATIVE — unreachable from a well-sorted clause (congruence pairs \
         argument positions of ONE head and identical positions are skipped). \
         The decode check behind them is what keeps a future builder change \
         closed.",
    ),
];

#[test]
fn guard_mutation_ledger_is_present() {
    assert!(GUARD_MUTATION_LEDGER.len() >= 8);
}
