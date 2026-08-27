// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exhaustive sweeps over bounded alphabets, with an INDEPENDENT evaluator.
//!
//! [`falsifies`] shares no code with the lowering: where the emitter saturates
//! a congruence closure and walks a proof forest, this ENUMERATES every
//! quotient of the clause's sub-term set and reports the first one that
//! falsifies every literal. A ground equality clause is valid exactly when no
//! such quotient exists, because a partition satisfying the realizability
//! condition below IS realized by a structure — take the blocks as the domain
//! and read each symbol's table off the applications.
//!
//! Every ACCEPT in the sweeps is re-checked three ways: the clause must be
//! VALID by that evaluator, the emitted fragment must replay under the
//! untouched strict checker, and the last step must reproduce the recorded
//! clause byte for byte.

use super::plan_euf_congruence_derivation;
use super::tests::{eq, fun, neq, strictly_checks, uninterpreted, var};
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

// ===== the independent evaluator =====

/// One decoded literal: `(polarity, lhs, rhs)` where `polarity` is `true` for
/// a POSITIVE equality.
fn decode(terms: &TermStore, literal: TermId) -> (bool, TermId, TermId) {
    let (inner, positive) = match terms.get(literal) {
        TermData::Not(inner) => (*inner, false),
        _ => (literal, true),
    };
    match terms.get(inner) {
        TermData::App(Symbol::Named(name), args) if name == "=" && args.len() == 2 => {
            (positive, args[0], args[1])
        }
        other => panic!("the independent evaluator models equality literals only, got {other:?}"),
    }
}

/// Every sub-term of `roots`, deduplicated, children before parents.
fn subterms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    fn walk(terms: &TermStore, term: TermId, out: &mut Vec<TermId>) {
        if out.contains(&term) {
            return;
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                for &arg in &args.clone() {
                    walk(terms, arg, out);
                }
            }
            TermData::Var(..) | TermData::Const(_) => {}
            other => {
                panic!("the independent evaluator models applications and leaves, got {other:?}")
            }
        }
        out.push(term);
    }
    let mut out = Vec::new();
    for &root in roots {
        walk(terms, root, &mut out);
    }
    out
}

/// The head key of an application: symbol AND arity, so `f/1` and `f/2` are
/// different functions.
fn head(terms: &TermStore, term: TermId) -> Option<(String, Vec<TermId>)> {
    match terms.get(term) {
        TermData::App(symbol, args) => Some((format!("{symbol:?}/{}", args.len()), args.clone())),
        _ => None,
    }
}

/// Visit every partition of `n` elements as a restricted-growth string.
fn partitions(n: usize, visit: &mut impl FnMut(&[usize]) -> bool) {
    fn walk(
        position: usize,
        n: usize,
        blocks: usize,
        assignment: &mut Vec<usize>,
        visit: &mut impl FnMut(&[usize]) -> bool,
    ) -> bool {
        if position == n {
            return visit(assignment);
        }
        for block in 0..=blocks {
            assignment.push(block);
            let keep_going = walk(position + 1, n, blocks.max(block + 1), assignment, visit);
            assignment.pop();
            if !keep_going {
                return false;
            }
        }
        true
    }
    let mut assignment = Vec::with_capacity(n);
    walk(0, n, 0, &mut assignment, visit);
}

/// The first quotient model falsifying every literal, or `None` when the
/// clause is VALID.
pub(crate) fn falsifies(terms: &TermStore, literals: &[TermId]) -> Option<Vec<(TermId, usize)>> {
    let decoded: Vec<(bool, TermId, TermId)> = literals.iter().map(|&l| decode(terms, l)).collect();
    let roots: Vec<TermId> = decoded
        .iter()
        .flat_map(|&(_, lhs, rhs)| [lhs, rhs])
        .collect();
    let nodes = subterms(terms, &roots);
    let position = |term: TermId| {
        nodes
            .iter()
            .position(|&other| other == term)
            .expect("interned")
    };
    let applications: Vec<(usize, String, Vec<usize>)> = nodes
        .iter()
        .enumerate()
        .filter_map(|(index, &term)| {
            head(terms, term)
                .map(|(key, args)| (index, key, args.into_iter().map(position).collect()))
        })
        .collect();
    let mut witness = None;
    partitions(nodes.len(), &mut |blocks| {
        for (left_index, (left, left_key, left_args)) in applications.iter().enumerate() {
            for (right, right_key, right_args) in applications.iter().skip(left_index + 1) {
                if left_key != right_key {
                    continue;
                }
                if left_args
                    .iter()
                    .zip(right_args.iter())
                    .all(|(&a, &b)| blocks[a] == blocks[b])
                    && blocks[*left] != blocks[*right]
                {
                    return true; // not realizable; keep searching
                }
            }
        }
        for &(positive, lhs, rhs) in &decoded {
            let same = blocks[position(lhs)] == blocks[position(rhs)];
            if same == positive {
                return true; // this literal is TRUE; not a countermodel
            }
        }
        witness = Some(
            nodes
                .iter()
                .copied()
                .zip(blocks.iter().copied())
                .collect::<Vec<_>>(),
        );
        false
    });
    witness
}

#[test]
fn the_independent_evaluator_agrees_with_hand_computed_cases() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let c = var(&mut terms, "c");
    let fa = fun(&mut terms, "f", vec![a], uninterpreted());
    let fc = fun(&mut terms, "f", vec![c], uninterpreted());
    let valid = vec![
        neq(&mut terms, a, b),
        neq(&mut terms, b, c),
        eq(&mut terms, a, c),
    ];
    assert!(falsifies(&terms, &valid).is_none());
    let congruence = vec![neq(&mut terms, a, c), eq(&mut terms, fa, fc)];
    assert!(falsifies(&terms, &congruence).is_none());
    let invalid = vec![neq(&mut terms, a, b), eq(&mut terms, a, c)];
    assert!(falsifies(&terms, &invalid).is_some());
}

// ===== the sweeps =====

struct Tally {
    clauses: usize,
    lowered: usize,
    /// Declined although VALID, because the conclusion is STATED by one of the
    /// hypotheses — a propositional tautology, which the intrinsic battery
    /// recognizes as `bool_tautology` long before this kind is reached.
    declined_stated: usize,
    /// Declined although VALID for any OTHER reason. The sweeps pin this at
    /// zero: over these alphabets the lowering is complete for every clause
    /// that is not already someone else's.
    declined_other: usize,
    declined_invalid: usize,
}

/// Sweep every clause of up to `max_hypotheses` hypotheses plus one
/// conclusion over the pairs of `alphabet`, checking every ACCEPT three ways.
fn sweep(terms: &mut TermStore, alphabet: &[TermId], max_hypotheses: usize) -> Tally {
    let mut pairs: Vec<(TermId, TermId)> = Vec::new();
    for (index, &lhs) in alphabet.iter().enumerate() {
        for &rhs in alphabet.iter().skip(index + 1) {
            pairs.push((lhs, rhs));
        }
    }
    let mut tally = Tally {
        clauses: 0,
        lowered: 0,
        declined_stated: 0,
        declined_other: 0,
        declined_invalid: 0,
    };
    let mut chosen: Vec<usize> = Vec::new();
    sweep_choose(
        &mut chosen,
        0,
        max_hypotheses,
        pairs.len(),
        &mut |selection: &[usize]| {
            if selection.is_empty() {
                return;
            }
            for (goal_lhs, goal_rhs) in pairs.clone() {
                let mut clause: Vec<TermId> = selection
                    .iter()
                    .map(|&index| {
                        let (lhs, rhs) = pairs[index];
                        neq(terms, lhs, rhs)
                    })
                    .collect();
                let goal = eq(terms, goal_lhs, goal_rhs);
                if clause.contains(&goal) {
                    continue;
                }
                clause.push(goal);
                tally.clauses += 1;
                match plan_euf_congruence_derivation(terms, &clause) {
                    Some(derivation) => {
                        assert_eq!(
                            derivation.clause, clause,
                            "an accepted lowering must reproduce the recorded clause"
                        );
                        assert!(
                            falsifies(terms, &clause).is_none(),
                            "the independent evaluator found a countermodel for a LOWERED clause: \
                             {clause:?}"
                        );
                        strictly_checks(terms, &derivation)
                            .expect("every emitted step must strict-check");
                        tally.lowered += 1;
                    }
                    None => {
                        if falsifies(terms, &clause).is_some() {
                            tally.declined_invalid += 1;
                        } else if selection.iter().any(|&index| {
                            let (lhs, rhs) = pairs[index];
                            (lhs, rhs) == (goal_lhs, goal_rhs) || (rhs, lhs) == (goal_lhs, goal_rhs)
                        }) {
                            tally.declined_stated += 1;
                        } else {
                            tally.declined_other += 1;
                        }
                    }
                }
            }
        },
    );
    tally
}

/// Enumerate every subset of `0..available` of size at most `remaining`.
fn sweep_choose(
    chosen: &mut Vec<usize>,
    next: usize,
    remaining: usize,
    available: usize,
    visit: &mut impl FnMut(&[usize]),
) {
    visit(chosen);
    if remaining == 0 {
        return;
    }
    for index in next..available {
        chosen.push(index);
        sweep_choose(chosen, index + 1, remaining - 1, available, visit);
        chosen.pop();
    }
}

#[test]
fn sweep_every_accept_reproduces_the_recorded_clause() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let c = var(&mut terms, "c");
    let fa = fun(&mut terms, "f", vec![a], uninterpreted());
    let fb = fun(&mut terms, "f", vec![b], uninterpreted());
    let fc = fun(&mut terms, "f", vec![c], uninterpreted());
    let alphabet = vec![a, b, c, fa, fb, fc];
    let tally = sweep(&mut terms, &alphabet, 3);
    assert!(
        tally.clauses > 500,
        "the sweep must be wide: {}",
        tally.clauses
    );
    assert!(
        tally.lowered > 0,
        "the sweep must exercise the lowering, not only its declines"
    );
    assert_eq!(
        tally.declined_invalid + tally.declined_stated + tally.declined_other + tally.lowered,
        tally.clauses
    );
    assert_eq!(
        tally.declined_other, 0,
        "every VALID clause whose conclusion is not itself a hypothesis must lower"
    );
    eprintln!(
        "unary sweep: {} clauses, {} lowered, {} declined-stated, {} declined-other, {} \
         declined-invalid",
        tally.clauses,
        tally.lowered,
        tally.declined_stated,
        tally.declined_other,
        tally.declined_invalid
    );
}

#[test]
fn sweep_a_binary_head_exercises_multi_position_congruence() {
    let mut terms = TermStore::new();
    let a = var(&mut terms, "a");
    let b = var(&mut terms, "b");
    let sort = uninterpreted();
    let gab = fun(&mut terms, "g", vec![a, b], sort.clone());
    let gba = fun(&mut terms, "g", vec![b, a], sort.clone());
    let gaa = fun(&mut terms, "g", vec![a, a], sort);
    let alphabet = vec![a, b, gab, gba, gaa];
    let tally = sweep(&mut terms, &alphabet, 2);
    assert!(tally.lowered > 0);
    assert_eq!(
        tally.declined_other, 0,
        "a repeated premise equality — `(= (g a b) (g b a))` under `a = b` — is \
         contracted, not declined"
    );
    eprintln!(
        "binary sweep: {} clauses, {} lowered, {} declined-stated, {} declined-other, {} \
         declined-invalid",
        tally.clauses,
        tally.lowered,
        tally.declined_stated,
        tally.declined_other,
        tally.declined_invalid
    );
}

#[test]
fn sweep_a_sorted_alphabet_never_lowers_an_invalid_clause() {
    let mut terms = TermStore::new();
    let element = uninterpreted();
    let array = Sort::Array(Box::new(ay_core::ArraySort {
        index_sort: Sort::Int,
        element_sort: element.clone(),
    }));
    let arr = terms.mk_var("arr", array.clone());
    let i = terms.mk_var("i", Sort::Int);
    let j = terms.mk_var("j", Sort::Int);
    let v = terms.mk_var("v", element.clone());
    let stored = fun(&mut terms, "store", vec![arr, i, v], array);
    let read_i = fun(&mut terms, "select", vec![stored, i], element.clone());
    let read_j = fun(&mut terms, "select", vec![stored, j], element.clone());
    let base_j = fun(&mut terms, "select", vec![arr, j], element);
    let alphabet = vec![read_i, read_j, base_j, v];
    let tally = sweep(&mut terms, &alphabet, 2);
    eprintln!(
        "array sweep: {} clauses, {} lowered, {} declined-stated, {} declined-other, {} \
         declined-invalid",
        tally.clauses,
        tally.lowered,
        tally.declined_stated,
        tally.declined_other,
        tally.declined_invalid
    );
    assert_eq!(
        tally.declined_invalid + tally.declined_stated + tally.declined_other + tally.lowered,
        tally.clauses
    );
    assert_eq!(tally.declined_other, 0);
}
