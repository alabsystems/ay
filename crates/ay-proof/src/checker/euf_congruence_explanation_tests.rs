// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-mode coverage for the EUF congruence-closure explanation validator.
//!
//! Three layers, in the order the soundness argument needs them:
//!
//! 1. **Adversarial negatives.** Every one names a CONCRETE falsifying
//!    assignment and checks it in-test with [`falsifying_quotient`] (or, where
//!    the clause contains a former the independent evaluator deliberately does
//!    not model, with a hand-written structure spelled out in plain Rust).
//! 2. **Exhaustive sweeps** over two bounded term alphabets. Every ACCEPT is
//!    re-checked for validity by [`falsifying_quotient`], an INDEPENDENT
//!    decision procedure that shares no code with the recognizer: it
//!    ENUMERATES every quotient model of the clause's sub-term set and reports
//!    the first countermodel, where the recognizer SATURATES a congruence
//!    closure. Rejects are checked in the same sweep, so the two agree on the
//!    whole box, not just on the accepts.
//! 3. **A guard-mutation ledger** ([`GUARD_MUTATION_LEDGER`]) naming, for each
//!    guard in the validator, the test that goes red when it is deleted — plus
//!    the guards for which that is honestly recorded as a NEGATIVE result.

use super::{recognize_euf_congruence_explanation, validate_euf_congruence_explanation, MAX_NODES};
use crate::checker::{
    recognize_euf_congruent, recognize_euf_transitive, validate_step, ProofCheckError,
};
use ay_core::{ArraySort, ProofId, ProofStep, Sort, TermId, TermStore, TheoryLemmaKind};

// ===== fixture helpers =====

fn mk_eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(ay_core::Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

fn mk_fun(terms: &mut TermStore, name: &str, args: Vec<TermId>, sort: Sort) -> TermId {
    terms.mk_app(ay_core::Symbol::named(name), args, sort)
}

fn mk_or(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(ay_core::Symbol::named("or"), args, Sort::Bool)
}

fn neq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    let eq = mk_eq(terms, lhs, rhs);
    terms.mk_not_raw(eq)
}

/// Run the clause through the STRICT checker, exactly as
/// `check_proof_strict` would for a recorded `TheoryLemma` of this kind.
fn strict(terms: &TermStore, clause: Vec<TermId>) -> Result<(), ProofCheckError> {
    let step = ProofStep::TheoryLemma {
        theory: "EUF".to_string(),
        clause,
        farkas: None,
        kind: TheoryLemmaKind::EufCongruenceExplanation,
        lia: None,
    };
    let mut derived = Vec::new();
    validate_step(terms, &mut derived, ProofId(0), &step, true, None)
}

fn accepts(terms: &TermStore, clause: &[TermId]) -> bool {
    let via_recognizer = recognize_euf_congruence_explanation(terms, clause);
    // The recognizer and the strict dispatch must never disagree: recognition
    // IS the validator, and the classifier that uses it would otherwise label
    // a clause the checker then refuses.
    assert_eq!(
        via_recognizer,
        strict(terms, clause.to_vec()).is_ok(),
        "recognizer and strict dispatch disagree on the same clause"
    );
    via_recognizer
}

// ===== the independent evaluator =====
//
// A ground equality clause `L_1 ∨ .. ∨ L_k` is INVALID exactly when some
// structure falsifies every literal. Over the clause's own sub-terms a
// structure is fully described by the PARTITION it induces on them, subject to
// one realizability condition: two applications of the same symbol at the same
// arity whose arguments land in the same blocks must themselves land in the
// same block (otherwise no function realizes the assignment). Any partition
// meeting that condition IS realized — take the blocks as the domain and read
// each symbol's table off the applications, extending arbitrarily elsewhere.
//
// So enumerating every partition of the sub-term set and testing the condition
// decides validity. That is a completely different procedure from the
// recognizer's bottom-up saturation, and it shares no code with it: no
// union-find, no signature table, no `flatten_or_clause`, no `strip_not`.
//
// Non-`App` nodes (variables, constants, `not`, `ite`, binders) are treated as
// LEAVES. That gives the evaluator a SUPERSET of the real structures, so
// "no countermodel found" still implies validity — the direction every ACCEPT
// is re-checked in. Tests that need the converse (a REJECT really is invalid)
// use alphabets built only from variables and applications, where the two
// classes of structure coincide.
//
// The evaluator reads a symbol UNSORTED — one function per `(name, arity)` —
// which is a SUBSET of the many-sorted structures when a symbol is overloaded
// across result sorts. No alphabet handed to it does that; the one test that
// needs an overloaded symbol
// (`a_symbol_overloaded_at_two_sorts_is_not_merged`) spells its countermodel
// out by hand instead.

/// One literal of a ground equality clause, decoded independently of
/// `strip_not` / `decode_eq`.
struct Lit {
    positive: bool,
    lhs: TermId,
    rhs: TermId,
}

fn decode_literals(terms: &TermStore, literals: &[TermId]) -> Vec<Lit> {
    literals
        .iter()
        .map(|&literal| {
            let mut current = literal;
            let mut positive = true;
            while let ay_core::TermData::Not(inner) = terms.get(current) {
                current = *inner;
                positive = !positive;
            }
            let ay_core::TermData::App(symbol, args) = terms.get(current) else {
                panic!("the independent evaluator only decodes equality literals");
            };
            assert!(
                symbol.name() == "=" && args.len() == 2,
                "the independent evaluator only decodes equality literals"
            );
            Lit {
                positive,
                lhs: args[0],
                rhs: args[1],
            }
        })
        .collect()
}

/// `(symbol name, arity, argument sub-terms)` for an application node; `None`
/// for every node the evaluator treats as a leaf.
fn application(terms: &TermStore, term: TermId) -> Option<(String, Vec<TermId>)> {
    match terms.get(term) {
        ay_core::TermData::App(symbol, args) => Some((symbol.name().to_string(), args.clone())),
        _ => None,
    }
}

fn collect_subterms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut order = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    fn walk(
        terms: &TermStore,
        term: TermId,
        seen: &mut std::collections::BTreeSet<TermId>,
        order: &mut Vec<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let Some((_, args)) = application(terms, term) {
            for arg in args {
                walk(terms, arg, seen, order);
            }
        }
        order.push(term);
    }
    for &root in roots {
        walk(terms, root, &mut seen, &mut order);
    }
    order
}

/// Enumerate every partition of `0..n` as a restricted growth string.
fn for_each_partition(n: usize, mut visit: impl FnMut(&[usize]) -> bool) {
    fn rec(
        index: usize,
        n: usize,
        used: usize,
        blocks: &mut Vec<usize>,
        visit: &mut impl FnMut(&[usize]) -> bool,
    ) -> bool {
        if index == n {
            return visit(blocks);
        }
        for block in 0..=used {
            blocks.push(block);
            let keep_going = rec(
                index + 1,
                n,
                if block == used { used + 1 } else { used },
                blocks,
                visit,
            );
            blocks.pop();
            if !keep_going {
                return false;
            }
        }
        true
    }
    let mut blocks = Vec::with_capacity(n);
    rec(0, n, 0, &mut blocks, &mut visit);
}

/// The first countermodel of the clause, as a `(sub-term, block)` listing, or
/// `None` when the clause is valid over this (super)class of structures.
fn falsifying_quotient(terms: &TermStore, literals: &[TermId]) -> Option<Vec<(TermId, usize)>> {
    let lits = decode_literals(terms, literals);
    let mut roots = Vec::new();
    for lit in &lits {
        roots.push(lit.lhs);
        roots.push(lit.rhs);
    }
    let subterms = collect_subterms(terms, &roots);
    let position: std::collections::BTreeMap<TermId, usize> = subterms
        .iter()
        .enumerate()
        .map(|(index, &term)| (term, index))
        .collect();
    // Pre-decode each application once, as positions.
    let apps: Vec<Option<(String, Vec<usize>)>> = subterms
        .iter()
        .map(|&term| {
            application(terms, term)
                .map(|(name, args)| (name, args.iter().map(|arg| position[arg]).collect()))
        })
        .collect();
    let mut found = None;
    for_each_partition(subterms.len(), |blocks| {
        // Realizability: same symbol, same arity, argument blocks equal =>
        // the results must share a block.
        for i in 0..apps.len() {
            let Some((name_i, args_i)) = &apps[i] else {
                continue;
            };
            for j in (i + 1)..apps.len() {
                let Some((name_j, args_j)) = &apps[j] else {
                    continue;
                };
                if name_i != name_j || args_i.len() != args_j.len() {
                    continue;
                }
                let same_args = args_i
                    .iter()
                    .zip(args_j.iter())
                    .all(|(&a, &b)| blocks[a] == blocks[b]);
                if same_args && blocks[i] != blocks[j] {
                    return true; // not a structure; skip
                }
            }
        }
        let any_literal_true = lits.iter().any(|lit| {
            let equal = blocks[position[&lit.lhs]] == blocks[position[&lit.rhs]];
            if lit.positive {
                equal
            } else {
                !equal
            }
        });
        if any_literal_true {
            return true;
        }
        found = Some(
            subterms
                .iter()
                .enumerate()
                .map(|(index, &term)| (term, blocks[index]))
                .collect(),
        );
        false
    });
    found
}

fn is_valid(terms: &TermStore, literals: &[TermId]) -> bool {
    falsifying_quotient(terms, literals).is_none()
}

// ===== positives: the shapes the census actually measured =====

/// The measured QF_AX shape the existing validators all reject: the link
/// between the two conclusion sides is produced BY CONGRUENCE on the index
/// position, and is not stated anywhere in the clause.
#[test]
fn accepts_the_measured_congruence_explanation_shape() {
    let mut terms = TermStore::new();
    let array = Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)));
    let base = terms.mk_var("C", array.clone());
    let i0 = terms.mk_var("i0", Sort::Int);
    let i2 = terms.mk_var("i2", Sort::Int);
    let i3 = terms.mk_var("i3", Sort::Int);
    let v = terms.mk_var("v", Sort::Int);
    let e = terms.mk_var("e", Sort::Int);
    let stored = mk_fun(&mut terms, "store", vec![base, i2, v], array);
    let sel_stored_i0 = mk_fun(&mut terms, "select", vec![stored, i0], Sort::Int);
    let sel_stored_i3 = mk_fun(&mut terms, "select", vec![stored, i3], Sort::Int);
    let sel_base_i0 = mk_fun(&mut terms, "select", vec![base, i0], Sort::Int);
    let conclusion = mk_eq(&mut terms, sel_stored_i0, sel_base_i0);
    let h1 = neq(&mut terms, i0, i3);
    let h2 = neq(&mut terms, e, sel_stored_i3);
    let h3 = neq(&mut terms, e, sel_base_i0);
    let clause = vec![conclusion, h1, h2, h3];

    // The three existing EUF validators all decline this clause, in the
    // recorded order AND with the conclusion moved last.
    let mut conclusion_last = vec![h1, h2, h3, conclusion];
    assert!(!recognize_euf_transitive(&terms, &clause));
    assert!(!recognize_euf_congruent(&terms, &clause));
    assert!(!recognize_euf_transitive(&terms, &conclusion_last));
    assert!(!recognize_euf_congruent(&terms, &conclusion_last));
    conclusion_last.rotate_left(0);

    assert!(accepts(&terms, &clause));
    assert!(
        is_valid(&terms, &clause),
        "the independent evaluator must agree the accepted clause is valid"
    );
}

/// The same clause packed into the single-literal `(cl (or ..))` form the
/// demotion pass actually records.
#[test]
fn accepts_the_packed_or_form_of_the_same_explanation() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fb = mk_fun(&mut terms, "f", vec![b], Sort::Int);
    let conclusion = mk_eq(&mut terms, fa, fb);
    let hypothesis = neq(&mut terms, a, b);
    let packed = mk_or(&mut terms, vec![conclusion, hypothesis]);
    assert!(accepts(&terms, &[packed]));
    assert!(is_valid(&terms, &[conclusion, hypothesis]));
}

/// Order-freedom is the whole reason this kind exists as a separate rule: the
/// producer relabels a leaf IN PLACE and must not permute the clause its
/// consumers already reference.
#[test]
fn the_verdict_is_independent_of_literal_order() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let fc = mk_fun(&mut terms, "f", vec![c], Sort::Int);
    let conclusion = mk_eq(&mut terms, fa, fc);
    let h1 = neq(&mut terms, a, b);
    let h2 = neq(&mut terms, b, c);
    let base = [conclusion, h1, h2];
    let mut seen = 0usize;
    for i in 0..3 {
        for j in 0..3 {
            for k in 0..3 {
                if i == j || j == k || i == k {
                    continue;
                }
                let clause = vec![base[i], base[j], base[k]];
                assert!(accepts(&terms, &clause), "permutation {i}{j}{k} rejected");
                seen += 1;
            }
        }
    }
    assert_eq!(seen, 6, "all six permutations must be exercised");
}

// ===== adversarial negatives =====

/// A chain with a BROKEN LINK. `a — b` and `c — d` do not connect `a` to `d`.
#[test]
fn rejects_a_chain_with_a_broken_link() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let d = terms.mk_var("d", Sort::Int);
    let h1 = neq(&mut terms, a, b);
    let h2 = neq(&mut terms, c, d);
    let conclusion = mk_eq(&mut terms, a, d);
    let clause = vec![h1, h2, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying assignment: a := b := 0, c := d := 1. Both hypotheses hold,
    // so both negated literals are false, and a != d makes the conclusion
    // false — the clause is FALSE.
    let countermodel = falsifying_quotient(&terms, &clause)
        .expect("a broken chain must have a concrete countermodel");
    let block = |t: TermId| countermodel.iter().find(|(x, _)| *x == t).unwrap().1;
    assert_eq!(block(a), block(b));
    assert_eq!(block(c), block(d));
    assert_ne!(block(a), block(d));
}

/// A congruence step with MISMATCHED FUNCTION SYMBOLS.
#[test]
fn rejects_a_congruence_step_with_mismatched_function_symbols() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let gb = mk_fun(&mut terms, "g", vec![b], Sort::Int);
    let hypothesis = neq(&mut terms, a, b);
    let conclusion = mk_eq(&mut terms, fa, gb);
    let clause = vec![hypothesis, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying assignment: a := b := 0, f(0) := 0, g(0) := 1. The hypothesis
    // holds and `f a != g b`, so the clause is FALSE.
    let countermodel = falsifying_quotient(&terms, &clause)
        .expect("distinct function symbols must have a concrete countermodel");
    let block = |t: TermId| countermodel.iter().find(|(x, _)| *x == t).unwrap().1;
    assert_eq!(block(a), block(b));
    assert_ne!(block(fa), block(gb));
}

/// A congruence step with MISMATCHED ARITY: the same NAME at two arities is
/// two different functions in any structure.
#[test]
fn rejects_a_congruence_step_with_mismatched_arity() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let unary = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let binary = mk_fun(&mut terms, "f", vec![b, b], Sort::Int);
    let hypothesis = neq(&mut terms, a, b);
    let conclusion = mk_eq(&mut terms, unary, binary);
    let clause = vec![hypothesis, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying assignment: a := b := 0, f/1(0) := 0, f/2(0,0) := 1.
    let countermodel = falsifying_quotient(&terms, &clause)
        .expect("an arity mismatch must have a concrete countermodel");
    let block = |t: TermId| countermodel.iter().find(|(x, _)| *x == t).unwrap().1;
    assert_eq!(block(a), block(b));
    assert_ne!(block(unary), block(binary));
}

/// A CONCLUSION THAT DOES NOT FOLLOW from the stated chain.
#[test]
fn rejects_a_conclusion_the_hypotheses_do_not_entail() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let fa = mk_fun(&mut terms, "f", vec![a], Sort::Int);
    let hypothesis = neq(&mut terms, a, b);
    let conclusion = mk_eq(&mut terms, fa, c);
    let clause = vec![hypothesis, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying assignment: a := b := 0, f(0) := 0, c := 1.
    let countermodel = falsifying_quotient(&terms, &clause)
        .expect("an unentailed conclusion must have a concrete countermodel");
    let block = |t: TermId| countermodel.iter().find(|(x, _)| *x == t).unwrap().1;
    assert_eq!(block(a), block(b));
    assert_ne!(block(fa), block(c));
}

/// A NON-EQUALITY LITERAL smuggled in as a hypothesis. `(not (or (= a b)
/// (= b c)))` is not an equality, and reading the disjunction's equalities as
/// hypotheses would accept a clause that is FALSE.
#[test]
fn rejects_a_negated_disjunction_smuggled_in_as_hypotheses() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let b = terms.mk_var("b", Sort::Int);
    let c = terms.mk_var("c", Sort::Int);
    let eq_ab = mk_eq(&mut terms, a, b);
    let eq_bc = mk_eq(&mut terms, b, c);
    let packed = mk_or(&mut terms, vec![eq_ab, eq_bc]);
    let smuggled = terms.mk_not_raw(packed);
    let conclusion = mk_eq(&mut terms, a, c);
    let clause = vec![smuggled, conclusion];
    assert!(!accepts(&terms, &clause));
    // Falsifying assignment: a := b := 0, c := 1. Then `(= a b)` holds, so the
    // negated disjunction is FALSE, and `a != c` makes the conclusion false —
    // the clause is FALSE. (Checked by hand rather than by the enumerator,
    // which decodes equality literals only.)
    let eq_ab_holds = true; // a and b share a block
    let eq_bc_holds = false;
    let smuggled_holds = !(eq_ab_holds || eq_bc_holds);
    let conclusion_holds = false; // a != c
    assert!(!(smuggled_holds || conclusion_holds));
}

include!("euf_congruence_explanation_tests/remaining_tests.rs");
