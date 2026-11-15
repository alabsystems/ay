// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

#![cfg(test)]

use super::super::term::Sort;
use super::*;

mod legacy;
mod projection;
mod resources;

fn state(k: usize, bits: usize) -> Vec<bool> {
    (0..k).map(|j| (bits >> j) & 1 != 0).collect()
}

fn reachable(k: usize, mask: usize) -> HashSet<Vec<bool>> {
    (0..1usize << k)
        .filter(|bits| (mask >> bits) & 1 != 0)
        .map(|bits| state(k, bits))
        .collect()
}

fn new_proof() -> Proof<'static> {
    Proof::new("membership.".into(), "@membership".into())
}

#[test]
fn exact_membership_matches_legacy_for_every_small_reachable_set() {
    let p = new_proof();
    for k in 0..=3 {
        for mask in 0..1usize << (1usize << k) {
            let reach = reachable(k, mask);
            let ordered: Vec<_> = reach.iter().collect();
            for bits in 0..1usize << k {
                let s = state(k, bits);
                let expected = Some((mask >> bits) & 1 != 0);
                assert_eq!(covered_state(&p, &reach, &[], &s), expected);
                assert_eq!(legacy::covered_state(&p, &ordered, &[], &s), expected);
            }
        }
    }
}

#[test]
fn exact_membership_preserves_every_small_chosen_clause_combination() {
    let p = new_proof();
    let candidates: Vec<_> = small_clauses(2, 1)
        .into_iter()
        .chain(small_clauses(2, 2))
        .collect();
    for mask in 0..16 {
        let reach = reachable(2, mask);
        let ordered: Vec<_> = reach.iter().collect();
        for selection in 0..1usize << candidates.len() {
            let chosen: Vec<_> = candidates
                .iter()
                .enumerate()
                .filter(|(i, _)| (selection >> i) & 1 != 0)
                .map(|(_, c)| c.clone())
                .collect();
            for bits in 0..4 {
                let s = state(2, bits);
                let expected = (mask >> bits) & 1 != 0
                    || chosen.iter().any(|c| c.iter().all(|&(j, v)| s[j] != v));
                assert_eq!(covered_state(&p, &reach, &chosen, &s), Some(expected));
                assert_eq!(
                    legacy::covered_state(&p, &ordered, &chosen, &s),
                    Some(expected)
                );
            }
        }
        // An empty chosen clause blocks every absent state, as before.
        for bits in 0..4 {
            let s = state(2, bits);
            assert_eq!(covered_state(&p, &reach, &[vec![]], &s), Some(true));
        }
    }
}

fn premise_fixture(p: &mut Proof, k: usize, reach: &HashSet<Vec<bool>>) -> (Vec<T>, Vec<Prem>) {
    let atoms: Vec<_> = (0..k)
        .map(|j| p.t.var(&format!("s{j}"), Sort::Bool))
        .collect();
    let mut premises = Vec::new();
    // Full blocking clauses describe exactly this reachable set. Their only
    // assumptions are the corresponding disjunctions; `or` splits each one.
    for bits in 0..1usize << k {
        let s = state(k, bits);
        if reach.contains(&s) {
            continue;
        }
        let clause: Vec<_> = atoms
            .iter()
            .zip(s)
            .map(|(&a, v)| if v { p.t.not(a) } else { a })
            .collect();
        let disjunction = p.t.or(&clause);
        let assumption = p.assume(disjunction);
        premises.push(Prem::Step(p.emit(&clause, "or", &[assumption], &[])));
    }
    (atoms, premises)
}

#[test]
fn invariant_clauses_and_proof_bytes_match_legacy_exhaustively() {
    for k in 1..=3 {
        for mask in 0..1usize << (1usize << k) {
            let reach = reachable(k, mask);
            let mut old = new_proof();
            let (old_atoms, old_premises) = premise_fixture(&mut old, k, &reach);
            let old_steps =
                legacy::invariant(&mut old, &old_atoms, &reach, &old_premises, &old_atoms)
                    .expect("blocking clauses entail the exact invariant");
            let mut new = new_proof();
            let (atoms, premises) = premise_fixture(&mut new, k, &reach);
            let steps = invariant(&mut new, &atoms, &reach, &premises, &atoms)
                .expect("membership preserves every derivable invariant");
            assert_eq!(steps, old_steps, "k={k}, reachable mask={mask}");
            for (&actual, &expected) in steps.iter().zip(&old_steps) {
                assert_eq!(new.clause(actual), old.clause(expected));
            }
            assert_eq!(new.out, old.out, "k={k}, reachable mask={mask}");
            assert_eq!(
                new.budget, old.budget,
                "local refutation credit is unchanged"
            );
        }
    }
}
