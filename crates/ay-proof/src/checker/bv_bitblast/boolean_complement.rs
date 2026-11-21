// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact two-literal excluded middle through bounded raw negation chains.
//!
//! This rule opens only Boolean `Not` nodes. A chain with parity `b` denotes
//! the final atom when `b` is false and its complement otherwise. Therefore
//! two chains with the same exact atom and opposite parities form a tautology
//! under every interpretation of the atom, without inspecting its theory.

use ay_core::{Sort, TermData, TermId, TermStore};

use super::{semantic_control, ProofCheckError};

const MAX_NEGATIONS: usize = 64;

fn atom(
    terms: &TermStore,
    mut term: TermId,
    poll: semantic_control::Poll<'_>,
) -> Result<Option<(TermId, bool)>, ProofCheckError> {
    let mut negative = false;
    for depth in 0..=MAX_NEGATIONS {
        poll()?;
        if terms.entry_stamp(term).is_none() || terms.sort(term) != &Sort::Bool {
            return Ok(None);
        }
        match terms.get(term) {
            TermData::Not(inner) if depth < MAX_NEGATIONS => {
                negative = !negative;
                term = *inner;
            }
            TermData::Not(_) => return Ok(None),
            _ => return Ok(Some((term, negative))),
        }
    }
    Ok(None)
}

pub(super) fn holds(
    terms: &TermStore,
    clause: &[TermId],
    poll: semantic_control::Poll<'_>,
) -> Result<bool, ProofCheckError> {
    let [left, right] = clause else {
        return Ok(false);
    };
    let Some((left, left_negative)) = atom(terms, *left, poll)? else {
        return Ok(false);
    };
    let Some((right, right_negative)) = atom(terms, *right, poll)? else {
        return Ok(false);
    };
    Ok(left == right && left_negative != right_negative)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{ProofId, Symbol};

    fn negations(terms: &mut TermStore, mut term: TermId, count: usize) -> TermId {
        for _ in 0..count {
            term = terms.mk_not_raw(term);
        }
        term
    }

    fn opaque_atom(terms: &mut TermStore, name: &str) -> TermId {
        let index = terms.mk_var("index", Sort::Int);
        terms.mk_app(Symbol::named(name), [index], Sort::Bool)
    }

    #[test]
    fn boolean_complement_checks_the_actual_closed_int2bv_fold_strip() {
        let mut terms = TermStore::new();
        let one = terms.mk_int(1.into());
        let converted = terms.mk_app(Symbol::indexed("int2bv", vec![64]), [one], Sort::bitvec(64));
        let bv_one = terms.mk_bitvec(1u64.into(), 64);
        let equality = terms.mk_app(Symbol::named("="), [converted, bv_one], Sort::Bool);
        let triple = negations(&mut terms, equality, 3);
        super::super::validate_bool_tautology(&terms, ProofId(0), &[triple, equality])
            .expect("the fold's double-negation strip is independent of int2bv evaluation");
    }

    #[test]
    fn boolean_complement_accepts_both_orders_and_bounded_depths_over_opaque_atoms() {
        let mut terms = TermStore::new();
        let p = opaque_atom(&mut terms, "predicate");
        let array = terms.mk_var("array", Sort::array(Sort::Int, Sort::Bool));
        let index = terms.mk_int(0.into());
        let read = terms.mk_app(Symbol::named("select"), [array, index], Sort::Bool);
        for atom in [p, read] {
            for left_depth in [0, 2, 16, 64] {
                for right_depth in [1, 3, 17, 63] {
                    let left = negations(&mut terms, atom, left_depth);
                    let right = negations(&mut terms, atom, right_depth);
                    for clause in [[left, right], [right, left]] {
                        super::super::validate_bool_tautology(&terms, ProofId(0), &clause)
                            .expect("exact opposite parity is a theory-independent tautology");
                    }
                }
            }
        }
    }

    #[test]
    fn boolean_complement_refuses_same_polarity_other_atoms_and_malformed_chains() {
        let mut terms = TermStore::new();
        let p = opaque_atom(&mut terms, "p");
        let q = opaque_atom(&mut terms, "q");
        let not_p = negations(&mut terms, p, 3);
        let same_p = negations(&mut terms, p, 2);
        let too_deep = negations(&mut terms, p, MAX_NEGATIONS + 1);
        let integer = terms.mk_int(1.into());
        for clause in [[not_p, q], [same_p, p], [too_deep, p], [integer, p]] {
            assert!(!holds(&terms, &clause, &mut || Ok(())).unwrap());
        }
        for clause in [[not_p, q], [same_p, p]] {
            assert!(super::super::validate_bool_tautology(&terms, ProofId(0), &clause).is_err());
        }
        assert!(!holds(&terms, &[p, TermId(u32::MAX)], &mut || Ok(())).unwrap());
        // The producer builder correctly refuses this shape, so exercise the
        // checker boundary with an explicitly malformed read-only snapshot.
        let mut entries = terms.entries_snapshot();
        let bad = TermId(u32::try_from(entries.len()).unwrap());
        entries.push((TermData::Not(integer), Sort::Bool));
        let malformed = TermStore::from_entries(entries, None, None, 0);
        assert!(!holds(&malformed, &[bad, p], &mut || Ok(())).unwrap());
    }

    #[test]
    fn boolean_complement_honors_cancellation_during_parity_walk() {
        let mut terms = TermStore::new();
        let p = opaque_atom(&mut terms, "p");
        let not_p = negations(&mut terms, p, 31);
        let mut calls = 0;
        let result = super::super::validate_bool_tautology_with_progress(
            &terms,
            ProofId(0),
            &[not_p, p],
            &mut |_, _| {
                calls += 1;
                calls < 12
            },
        );
        assert_eq!(result, Err(ProofCheckError::ResourceLimit));
        assert_eq!(calls, 12);
    }
}
