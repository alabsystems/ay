// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #dt-enum-pigeonhole-false-lemma.
//!
//! `add_finite_enum_pigeonhole_conflict` used to conclude its clique argument
//! by pushing the Bool constant `false` through
//! `push_array_axiom_assertion_site`, which `record_array_axiom_proof` then
//! recorded as `TheoryLemma { kind: Generic, clause: [false] }`.
//!
//! A theory lemma asserts a clause valid in EVERY model of the theory.
//! `(cl false)` is valid in NONE — it is the strongest possible claim, and it
//! was wearing a theory lemma's label, so no recognizer, discharge lane or
//! reader could tell it apart from a real one.
//!
//! What the pass actually establishes is the PIGEONHOLE TAUTOLOGY over the
//! `k + 1` clique members of a sort with exactly `k` inhabitants: two of them
//! must be equal. That disjunction is what the producer now asserts, and the
//! `true` return — not the `false` assertion — is what carries UNSAT to the
//! caller (every caller skips the ground solve on `true`).
//!
//! Corpus measurement (`benchmarks/**/*.smt2`, 639 files, `--no-proof -T:10`,
//! 10-way, 30 s wall): the `false` push fired **3 times in 1 file**
//! (`soundness_qf_dt_derived_terms/bug3_enum_card_ite_distinct.smt2`) and
//! exactly **one** of those steps survived into a strict-checked proof, in
//! three independent BEFORE arms; **0** in two AFTER arms, with **0 verdict
//! differences** across all five.

use super::super::*;
use ay_core::{ProofStep, Symbol};

fn enum_context(script: &str) -> Executor {
    let commands = ay_frontend::parse(script).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    exec.proof_tracker.enable();
    exec.execute_all(&commands)
        .expect("invariant: execute succeeds");
    exec
}

/// Four pairwise-distinct terms of a THREE-inhabitant enum: `4 > 3`, so the
/// pigeonhole fires. All four edges are unconditional, which is the shape the
/// producer's own clique search reads directly.
const FOUR_IN_THREE: &str = r#"
    (set-logic QF_UFDT)
    (declare-datatypes ((Enum 0)) (((c0) (c1) (c2))))
    (declare-const w Enum)
    (declare-const x Enum)
    (declare-const y Enum)
    (declare-const z Enum)
    (assert (distinct w x y z))
"#;

/// The exact `bug3_enum_card_ite_distinct.smt2` text, so the verdict this fix
/// must not cost is pinned against the real producer path (its edges come from
/// the Shannon-lifted `ite` recovery, which is why the checkable bounded proof
/// declines on it and the `false` step was reached at all).
const BUG3: &str = r#"
    (set-logic QF_UFDT)
    (declare-datatypes ((Enum 0)) (((c0) (c1) (c2))))
    (declare-fun f (Enum) Enum)
    (declare-const v1 Enum)(declare-const v2 Enum)(declare-const a Enum)(declare-const b Enum)
    (declare-const p Bool)
    (assert (distinct (ite p v1 v2) (f a) a b))
    (check-sat)
"#;

fn recorded_lemmas(exec: &mut Executor) -> Vec<(TheoryLemmaKind, Vec<TermId>)> {
    exec.proof_tracker
        .take_proof()
        .steps
        .iter()
        .filter_map(|step| match step {
            ProofStep::TheoryLemma { kind, clause, .. } => Some((*kind, clause.clone())),
            _ => None,
        })
        .collect()
}

// ===== the INDEPENDENT finite-carrier evaluator =====
//
// Every atom of the clause is assigned a value in `0..carrier`; `=` is value
// equality and the Boolean connectives are the obvious ones. It re-derives the
// semantics from term structure and shares no code with the producer, with the
// clique search, or with any validator.

fn atoms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut seen: Vec<TermId> = Vec::new();
    let mut out: Vec<TermId> = Vec::new();
    let mut stack: Vec<TermId> = roots.iter().rev().copied().collect();
    while let Some(term) = stack.pop() {
        if seen.contains(&term) {
            continue;
        }
        seen.push(term);
        match terms.get(term) {
            TermData::App(_, args) => {
                let args = args.clone();
                for arg in args.into_iter().rev() {
                    stack.push(arg);
                }
            }
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(cond, then_branch, else_branch) => {
                stack.push(*cond);
                stack.push(*then_branch);
                stack.push(*else_branch);
            }
            _ => out.push(term),
        }
    }
    out
}

/// `Some(true)`/`Some(false)`, or `None` when the model cannot decide the term
/// — which is a FAILURE to refute and never evidence of validity.
fn holds(terms: &TermStore, term: TermId, binding: &[(TermId, usize)]) -> Option<bool> {
    match terms.get(term) {
        TermData::Const(ay_core::term::Constant::Bool(value)) => Some(*value),
        TermData::Not(inner) => holds(terms, *inner, binding).map(|value| !value),
        TermData::Ite(cond, then_branch, else_branch) => {
            if holds(terms, *cond, binding)? {
                holds(terms, *then_branch, binding)
            } else {
                holds(terms, *else_branch, binding)
            }
        }
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => {
            let left = value_of(terms, args[0], binding)?;
            let right = value_of(terms, args[1], binding)?;
            Some(left == right)
        }
        TermData::App(sym, args) if sym.name() == "or" => {
            let mut any = false;
            for &arg in args {
                any |= holds(terms, arg, binding)?;
            }
            Some(any)
        }
        TermData::App(sym, args) if sym.name() == "and" => {
            let mut all = true;
            for &arg in args {
                all &= holds(terms, arg, binding)?;
            }
            Some(all)
        }
        _ => {
            // A Bool-sorted atom carries its own truth value from the binding.
            let value = binding.iter().find(|(id, _)| *id == term)?.1;
            (*terms.sort(term) == Sort::Bool).then_some(value != 0)
        }
    }
}

fn value_of(_terms: &TermStore, term: TermId, binding: &[(TermId, usize)]) -> Option<usize> {
    binding
        .iter()
        .find(|(id, _)| *id == term)
        .map(|(_, value)| *value)
}

/// Whether `term` holds under EVERY assignment of `atoms` into `0..carrier`.
/// Returns `None` if the model cannot decide even one assignment.
fn valid_over(terms: &TermStore, term: TermId, carrier: usize) -> Option<bool> {
    let variables = atoms(terms, &[term]);
    let total = carrier.checked_pow(u32::try_from(variables.len()).ok()?)?;
    for index in 0..total {
        let mut rest = index;
        let binding: Vec<(TermId, usize)> = variables
            .iter()
            .map(|&variable| {
                let value = rest % carrier;
                rest /= carrier;
                (variable, value)
            })
            .collect();
        if !holds(terms, term, &binding)? {
            return Some(false);
        }
    }
    Some(true)
}

/// The single assertion the pass adds, i.e. the step this fix is about.
fn emitted_conclusion(before: &[TermId], after: &[TermId]) -> TermId {
    let added: Vec<TermId> = after
        .iter()
        .copied()
        .filter(|term| !before.contains(term))
        .collect();
    assert_eq!(added.len(), 1, "the pass must add exactly one assertion");
    added[0]
}

/// THE ADVERSARIAL NEGATIVE, with a named assignment checked in-test: the step
/// the producer used to emit is FALSE at `w = x = y = z = c0`, and — being the
/// constant `false` — at every other assignment too. A complete refutation.
#[test]
fn a_theory_lemma_concluding_false_is_refuted_by_every_assignment() {
    let exec = enum_context(FOUR_IN_THREE);
    let terms = &exec.ctx.terms;
    let false_term = terms.false_term();
    let named: Vec<(TermId, usize)> = Vec::new();
    assert_eq!(
        holds(terms, false_term, &named),
        Some(false),
        "`(cl false)` must be FALSE at the all-c0 assignment"
    );
    assert_eq!(
        valid_over(terms, false_term, 3),
        Some(false),
        "`(cl false)` must be refuted over the whole carrier"
    );
}

/// THE FIX'S CLAIM: the disjunction the producer asserts instead is valid in
/// every model of a 3-inhabitant carrier — exhaustively, all 3^4 assignments.
#[test]
fn the_emitted_pigeonhole_disjunction_is_valid_over_the_whole_carrier() {
    let mut exec = enum_context(FOUR_IN_THREE);
    let before = exec.ctx.assertions.clone();
    assert!(
        exec.add_finite_enum_pigeonhole_conflict(),
        "the pigeonhole must still fire on four pairwise-distinct terms of a 3-enum"
    );
    let conclusion = emitted_conclusion(&before, &exec.ctx.assertions);

    assert_ne!(
        conclusion,
        exec.ctx.terms.false_term(),
        "the pass must never assert the Bool constant `false` again"
    );
    assert_ne!(conclusion, exec.ctx.terms.true_term());
    assert!(
        matches!(
            exec.ctx.terms.get(conclusion),
            TermData::App(Symbol::Named(name), args) if name == "or" && args.len() == 6
        ),
        "the conclusion must be the complete equality graph over the 4 clique members"
    );
    assert_eq!(
        valid_over(&exec.ctx.terms, conclusion, 3),
        Some(true),
        "the emitted pigeonhole disjunction must hold in EVERY 3-inhabitant model"
    );
}

/// SENSITIVITY CONTROL on the evaluator: drop to THREE terms over the same
/// 3-inhabitant carrier and the same disjunction shape becomes FALSIFIABLE, at
/// the named assignment `w = c0, x = c1, y = c2`. Without this, an evaluator
/// that said "valid" about everything would read identically above.
#[test]
fn three_terms_in_three_holes_are_not_forced_to_collide() {
    let mut exec = enum_context(FOUR_IN_THREE);
    let w = exec
        .ctx
        .terms
        .mk_var("w", Sort::Uninterpreted("Enum".to_string()));
    let x = exec
        .ctx
        .terms
        .mk_var("x", Sort::Uninterpreted("Enum".to_string()));
    let y = exec
        .ctx
        .terms
        .mk_var("y", Sort::Uninterpreted("Enum".to_string()));
    let wx = exec.ctx.terms.mk_eq(w, x);
    let wy = exec.ctx.terms.mk_eq(w, y);
    let xy = exec.ctx.terms.mk_eq(x, y);
    let three = exec.ctx.terms.mk_or(vec![wx, wy, xy]);

    let named = vec![(w, 0), (x, 1), (y, 2)];
    assert_eq!(
        holds(&exec.ctx.terms, three, &named),
        Some(false),
        "3 pigeons in 3 holes need not collide — at w=c0, x=c1, y=c2 nothing is equal"
    );
    assert_eq!(valid_over(&exec.ctx.terms, three, 3), Some(false));
    // POSITIVE CONTROL: the SAME clause over a 2-inhabitant carrier IS valid.
    assert_eq!(
        valid_over(&exec.ctx.terms, three, 2),
        Some(true),
        "3 pigeons in 2 holes must collide — otherwise the evaluator is broken"
    );
}

/// THE PROOF SIDE: no step of the recorded proof concludes `false`, and the
/// recorded clause is the COMPLETE EQUALITY GRAPH — the disjuncts of the
/// asserted disjunction, not the packed `(or ..)` literal.
///
/// The flattened shape is load-bearing, not cosmetic:
/// `proof::rebuild_finite_enum_pigeonhole_refutation` matches this stub literal
/// by literal against the member pairs it re-authenticates, and the packed form
/// makes it decline — which costs the four-member QF_DT clique of
/// `api::tests::test_proof_artifact` its `unsat` outright.
#[test]
fn no_recorded_theory_lemma_concludes_false() {
    let mut exec = enum_context(FOUR_IN_THREE);
    let before = exec.ctx.assertions.clone();
    assert!(exec.add_finite_enum_pigeonhole_conflict());
    let conclusion = emitted_conclusion(&before, &exec.ctx.assertions);
    let TermData::App(_, disjuncts) = exec.ctx.terms.get(conclusion) else {
        panic!("the asserted conclusion must be the pigeonhole disjunction");
    };
    let mut disjuncts = disjuncts.clone();
    disjuncts.sort_unstable();
    let false_term = exec.ctx.terms.false_term();
    let true_term = exec.ctx.terms.true_term();

    let lemmas = recorded_lemmas(&mut exec);
    assert!(
        !lemmas
            .iter()
            .any(|(_, clause)| clause.contains(&false_term) || clause.contains(&true_term)),
        "no theory lemma may mention a Bool constant, got {lemmas:?}"
    );
    assert!(
        lemmas.iter().any(|(_, clause)| {
            let mut sorted = clause.clone();
            sorted.sort_unstable();
            sorted == disjuncts
        }),
        "the recorded clause must be the pigeonhole graph's six literals, got {lemmas:?}"
    );
    assert!(
        !lemmas
            .iter()
            .any(|(_, clause)| clause.as_slice() == [conclusion]),
        "the PACKED one-literal form disables the checkable rebuild, got {lemmas:?}"
    );
}

/// PRINTER PIN on the emitted conclusion's exact wire text.
#[test]
fn the_emitted_pigeonhole_disjunction_prints_exactly() {
    let mut exec = enum_context(FOUR_IN_THREE);
    let before = exec.ctx.assertions.clone();
    assert!(exec.add_finite_enum_pigeonhole_conflict());
    let conclusion = emitted_conclusion(&before, &exec.ctx.assertions);
    assert_eq!(
        format!(
            "(cl {})",
            ay_proof::format_term_alethe(&exec.ctx.terms, conclusion)
        ),
        "(cl (or (= w x) (= w y) (= w z) (= x y) (= x z) (= y z)))",
        "the producer's pigeonhole wire text changed"
    );
}

/// THE VERDICT THIS FIX MUST NOT COST. `bug3_enum_card_ite_distinct.smt2` is
/// the one corpus file that reached the `false` step; it must still publish
/// `unsat`.
#[test]
fn bug3_enum_card_ite_distinct_is_still_unsat() {
    let commands = ay_frontend::parse(BUG3).expect("invariant: valid SMT-LIB input");
    let mut exec = Executor::new();
    let outputs = exec
        .execute_all(&commands)
        .expect("invariant: execute succeeds");
    assert_eq!(outputs[0], "unsat");
}

/// SCOPE GUARD: the pass must stay SILENT when the clique does not exceed the
/// carrier, so nothing above is an artifact of a pass that fires unconditionally.
#[test]
fn three_pairwise_distinct_terms_of_a_three_enum_fire_nothing() {
    let mut exec = enum_context(
        r#"
        (set-logic QF_UFDT)
        (declare-datatypes ((Enum 0)) (((c0) (c1) (c2))))
        (declare-const w Enum)
        (declare-const x Enum)
        (declare-const y Enum)
        (assert (distinct w x y))
    "#,
    );
    let before = exec.ctx.assertions.clone();
    assert!(
        !exec.add_finite_enum_pigeonhole_conflict(),
        "3 pigeons in 3 holes is not a pigeonhole conflict"
    );
    assert_eq!(
        exec.ctx.assertions, before,
        "a declining pass must assert nothing"
    );
}
