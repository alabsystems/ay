// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! `ArrayRowChain`: skipping a store entry whose index is a CONSTANT distinct
//! from the read index.
//!
//! Sub-schema (B) walks a `store` chain under an array equality, but it could
//! only SKIP an entry when the clause carried the positive `(= j i)` literal it
//! gets to assume false. The census population
//! (`smt/chc_loop_alloc_multi_pred`, `smt/regression/soundness_fuzz_round3_…`)
//! writes and reads at INTERPRETED CONSTANTS, so the disequality is ground and
//! no clause literal exists to carry it:
//!
//! ```text
//! (cl (or (not (= m (store (as const (Array Int Int)) 0 66))) (= 0 (select m 8))))
//! ```
//!
//! Unlike the extensionality direction, these clauses ARE theorems, and the
//! sweeps below re-check every ACCEPT against an INDEPENDENT bounded model
//! written in this file: it re-derives the McCarthy semantics from the term
//! structure, enumerates every array value over a small integer universe, and
//! shares no code with the validator.

use crate::checker::array_axiom::distinct_interpreted_indices;
use crate::checker::*;
use ay_core::{
    ArraySort, Constant, Proof, ProofId, ProofStep, Sort, Symbol, TermData, TermId, TermStore,
    TheoryLemmaKind,
};

// ===== fixtures =====

fn int_array_sort() -> Sort {
    Sort::Array(Box::new(ArraySort::new(Sort::Int, Sort::Int)))
}

fn int(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(num_bigint::BigInt::from(value))
}

/// A RAW `(store a i v)`: `mk_store` collapses store-over-store and commutes
/// concrete indices, so the fixtures cannot use it.
fn store(terms: &mut TermStore, base: TermId, index: TermId, value: TermId) -> TermId {
    let sort = terms.sort(base).clone();
    terms.mk_app(Symbol::named("store"), vec![base, index, value], sort)
}

/// A RAW `(select a i)`: `mk_select` performs the very fold under test.
fn select(terms: &mut TermStore, array: TermId, index: TermId) -> TermId {
    terms.mk_app(Symbol::named("select"), vec![array, index], Sort::Int)
}

fn eq(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), vec![lhs, rhs], Sort::Bool)
}

fn or(terms: &mut TermStore, lits: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("or"), lits, Sort::Bool)
}

/// `(cl (or (not (= root chain)) (= value (select root read))))`, packed into
/// the single-literal `or` the producer emits, with its flat literals.
fn chain_read_clause(
    terms: &mut TermStore,
    root: TermId,
    chain: TermId,
    read: TermId,
    value: TermId,
) -> (Vec<TermId>, Vec<TermId>) {
    let premise_eq = eq(terms, root, chain);
    let premise = terms.mk_not(premise_eq);
    let read_term = select(terms, root, read);
    let conclusion = eq(terms, value, read_term);
    let packed = or(terms, vec![premise, conclusion]);
    (vec![packed], vec![premise, conclusion])
}

#[cfg(test)]
#[path = "array_chain_const_index_model.rs"]
mod model;
use model::*;

/// The UNTOUCHED strict checker, on the clause closed into a self-contained
/// refutation: the lemma, the assumed negation of each literal, the resolution.
fn strict_checks(terms: &mut TermStore, clause: &[TermId]) -> bool {
    let negations: Vec<TermId> = clause.iter().map(|&lit| terms.mk_not_raw(lit)).collect();
    let mut proof = Proof::new();
    proof.steps.push(ProofStep::TheoryLemma {
        theory: "arrays".to_string(),
        clause: clause.to_vec(),
        farkas: None,
        kind: TheoryLemmaKind::ArrayRowChain,
        lia: None,
    });
    let mut premises = vec![ProofId(0)];
    let mut next_id: u32 = 1;
    for negated in negations {
        proof.steps.push(ProofStep::Assume(negated));
        premises.push(ProofId(next_id));
        next_id += 1;
    }
    proof.steps.push(ProofStep::Step {
        rule: AletheRule::Resolution,
        clause: Vec::new(),
        premises,
        args: Vec::new(),
    });
    crate::check_proof_strict(&proof, terms).is_ok()
}

/// The whole bar for one ACCEPT: recognized, strict-checked, and UNFALSIFIABLE
/// under the independent model — which must also be able to decide it.
fn accepted(terms: &mut TermStore, clause: &[TermId], literals: &[TermId]) {
    assert!(
        recognize_array_theory_lemma(terms, clause) == Some(TheoryLemmaKind::ArrayRowChain),
        "the row-chain schema must recognize this clause"
    );
    assert!(
        decidable(terms, literals),
        "the model could not interpret the clause, so its silence is not evidence"
    );
    assert!(
        falsify(terms, literals).is_none(),
        "the INDEPENDENT model falsified an ACCEPTED clause"
    );
    assert!(
        strict_checks(terms, clause),
        "the untouched strict checker refused an ACCEPTED clause"
    );
}

/// The whole bar for one DECLINE: refused, and refutable at a NAMED point that
/// is checked literal by literal.
fn refuted_and_declined(
    terms: &TermStore,
    clause: &[TermId],
    literals: &[TermId],
    named: &[(TermId, Val)],
) {
    assert!(
        recognize_array_theory_lemma(terms, clause) != Some(TheoryLemmaKind::ArrayRowChain),
        "the row-chain schema accepted a REFUTABLE clause"
    );
    assert!(decidable(terms, literals), "the model must decide it");
    for &lit in literals {
        assert_eq!(
            holds(terms, lit, named),
            Some(false),
            "the NAMED assignment must falsify every literal"
        );
    }
    assert!(
        falsify(terms, literals).is_some(),
        "the enumeration must agree that the clause is refutable"
    );
}

// ===== the two corpus clauses =====

#[test]
fn the_const_array_corpus_clause_is_accepted() {
    // `smt/chc_loop_alloc_multi_pred`:
    // `(cl (or (not (= m (store (const 0) 0 66))) (= 0 (select m 2))))`
    // (the corpus reads at 8; the model's universe is 3, and the read index
    // only has to be a constant DIFFERENT from the written one).
    let mut terms = TermStore::new();
    let zero = int(&mut terms, 0);
    let written = int(&mut terms, 1);
    let write_at = int(&mut terms, 0);
    let read_at = int(&mut terms, 2);
    let base = terms.mk_const_array(Sort::Int, zero);
    let root = terms.mk_var("m", int_array_sort());
    let chain = store(&mut terms, base, write_at, written);
    let (clause, literals) = chain_read_clause(&mut terms, root, chain, read_at, zero);
    accepted(&mut terms, &clause, &literals);
}

#[test]
fn the_two_store_corpus_clause_is_accepted() {
    // `smt/regression/soundness_fuzz_round3_…`:
    // `(cl (or (not (= os (store (store (const 0) 0 4) 1 2))) (= 4 (select os 0))))`
    // — the OUTER write is skipped by `1 != 0` and the inner one hits.
    let mut terms = TermStore::new();
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let base = terms.mk_const_array(Sort::Int, zero);
    let root = terms.mk_var("os", int_array_sort());
    let inner = store(&mut terms, base, zero, two);
    let chain = store(&mut terms, inner, one, one);
    let (clause, literals) = chain_read_clause(&mut terms, root, chain, zero, two);
    accepted(&mut terms, &clause, &literals);
}

// ===== negatives, each with a checked falsifying assignment =====

#[test]
fn a_read_at_the_written_constant_must_take_the_written_value() {
    // The chain writes `1` at index `0` and the clause claims `select(m, 0)`
    // is the const-array default `0`.
    // FALSIFYING ASSIGNMENT: `m = [1, 0, 0]`, which IS the chain, so the
    // premise is FALSE; and `select(m, 0) = 1 != 0`, so the conclusion is
    // FALSE too.
    let mut terms = TermStore::new();
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let base = terms.mk_const_array(Sort::Int, zero);
    let root = terms.mk_var("m", int_array_sort());
    let chain = store(&mut terms, base, zero, one);
    let (clause, literals) = chain_read_clause(&mut terms, root, chain, zero, zero);
    let binding = vec![(root, Val::Arr(vec![1, 0, 0]))];
    refuted_and_declined(&terms, &clause, &literals, &binding);
}

#[test]
fn a_skip_over_a_symbolic_index_with_no_guard_literal_is_declined() {
    // The written index is a VARIABLE, so `i != 2` is not ground and the clause
    // carries no `(= 2 i)` literal to discharge it.
    // FALSIFYING ASSIGNMENT: `i = 2`, `m = [0, 0, 1]` — which IS
    // `store(const(0), 2, 1)`, so the premise is FALSE; and
    // `select(m, 2) = 1 != 0`, so the conclusion is FALSE.
    let mut terms = TermStore::new();
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let base = terms.mk_const_array(Sort::Int, zero);
    let write_at = terms.mk_var("i", Sort::Int);
    let root = terms.mk_var("m", int_array_sort());
    let chain = store(&mut terms, base, write_at, one);
    let (clause, literals) = chain_read_clause(&mut terms, root, chain, two, zero);
    let binding = vec![(root, Val::Arr(vec![0, 0, 1])), (write_at, Val::Num(2))];
    refuted_and_declined(&terms, &clause, &literals, &binding);
}

#[test]
fn a_skip_that_reaches_the_wrong_const_array_default_is_declined() {
    // The skip is legitimate (`0 != 2`) but the claimed value is not the base's
    // fill.
    // FALSIFYING ASSIGNMENT: `m = [1, 0, 0] = store(const(0), 0, 1)`, so the
    // premise is FALSE; `select(m, 2) = 0 != 1`, so the conclusion is FALSE.
    let mut terms = TermStore::new();
    let zero = int(&mut terms, 0);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let base = terms.mk_const_array(Sort::Int, zero);
    let root = terms.mk_var("m", int_array_sort());
    let chain = store(&mut terms, base, zero, one);
    let (clause, literals) = chain_read_clause(&mut terms, root, chain, two, one);
    let binding = vec![(root, Val::Arr(vec![1, 0, 0]))];
    refuted_and_declined(&terms, &clause, &literals, &binding);
}

#[test]
fn two_bitvector_constants_of_different_widths_are_never_distinct() {
    // A same-VALUE, different-WIDTH pair is not an index pair at all (the sorts
    // differ), and the guard must not treat two `BitVec` constants as distinct
    // on their numeric values alone.
    let mut terms = TermStore::new();
    let narrow = terms.mk_bitvec(num_bigint::BigInt::from(1), 8);
    let wide = terms.mk_bitvec(num_bigint::BigInt::from(1), 16);
    assert!(!distinct_interpreted_indices(&terms, narrow, wide));
    let other = terms.mk_bitvec(num_bigint::BigInt::from(2), 8);
    assert!(distinct_interpreted_indices(&terms, narrow, other));
    assert!(!distinct_interpreted_indices(&terms, narrow, narrow));
    let int_one = int(&mut terms, 1);
    assert!(!distinct_interpreted_indices(&terms, int_one, narrow));
    let symbol = terms.mk_var("s", Sort::Int);
    let int_two = int(&mut terms, 2);
    assert!(!distinct_interpreted_indices(&terms, symbol, int_two));
}

// ===== EXHAUSTIVE sweep: every constant chain over the universe =====

#[test]
fn sweep_constant_chains_accept_exactly_the_true_reads() {
    // Every one- and two-store chain over `const-array(fill)` with constant
    // indices and values in `0..3`, read at every constant index, claiming
    // every constant value: 3 (fill) x 3 x 3 (inner) x 3 x 3 (outer) x 3 (read)
    // x 3 (claim) = 2187 clauses. Ground truth is computed by the INDEPENDENT
    // model, never by the recognizer.
    let mut accepts = 0usize;
    let mut checked = 0usize;
    for fill in 0..UNIVERSE {
        for inner_at in 0..UNIVERSE {
            for inner_val in 0..UNIVERSE {
                for outer_at in 0..UNIVERSE {
                    for outer_val in 0..UNIVERSE {
                        for read_at in 0..UNIVERSE {
                            for claim in 0..UNIVERSE {
                                let mut terms = TermStore::new();
                                let fill_t = int(&mut terms, fill as i64);
                                let base = terms.mk_const_array(Sort::Int, fill_t);
                                let inner_at_t = int(&mut terms, inner_at as i64);
                                let inner_val_t = int(&mut terms, inner_val as i64);
                                let outer_at_t = int(&mut terms, outer_at as i64);
                                let outer_val_t = int(&mut terms, outer_val as i64);
                                let read_t = int(&mut terms, read_at as i64);
                                let claim_t = int(&mut terms, claim as i64);
                                let root = terms.mk_var("m", int_array_sort());
                                let inner = store(&mut terms, base, inner_at_t, inner_val_t);
                                let chain = store(&mut terms, inner, outer_at_t, outer_val_t);
                                let (clause, literals) =
                                    chain_read_clause(&mut terms, root, chain, read_t, claim_t);
                                let got = recognize_array_theory_lemma(&terms, &clause)
                                    == Some(TheoryLemmaKind::ArrayRowChain);
                                // Ground truth: the clause is valid iff the
                                // read really denotes the claimed value.
                                let truth = if read_at == outer_at {
                                    outer_val
                                } else if read_at == inner_at {
                                    inner_val
                                } else {
                                    fill
                                };
                                let valid = truth == claim;
                                assert!(
                                    decidable(&terms, &literals),
                                    "the model must decide every sweep clause"
                                );
                                assert_eq!(
                                    falsify(&terms, &literals).is_none(),
                                    valid,
                                    "the model and the ground truth must agree"
                                );
                                if got {
                                    assert!(
                                        valid,
                                        "ACCEPTED a clause the independent model refutes: \
                                         fill={fill} inner=({inner_at},{inner_val}) \
                                         outer=({outer_at},{outer_val}) read={read_at} \
                                         claim={claim}"
                                    );
                                    accepts += 1;
                                }
                                checked += 1;
                            }
                        }
                    }
                }
            }
        }
    }
    assert_eq!(checked, 3usize.pow(7));
    assert!(
        accepts > 0,
        "the sweep must exercise the new arm, not just decline everything"
    );
}
