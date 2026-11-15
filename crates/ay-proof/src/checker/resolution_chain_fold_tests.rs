// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The incremental fold is the search's semantics, differentially: random
//! argument-free chains over a few atoms are judged by the checker and by the
//! search alone (the pre-fold algorithm, reproduced verbatim), and the two
//! must agree on every chain, accepting and rejecting alike.

use super::super::parity::{chain_resolve_candidates, clause_as_set};
use super::super::validate_chain_resolution_rule;
use ay_core::{AletheRule, ProofId, Sort, TermId, TermStore};

/// The chain validator as it was before the fold: the all-unit-tail set
/// subtraction, then the bounded search from the first premise.
fn search_only(terms: &TermStore, clause: &[TermId], premises: &[&[TermId]]) -> bool {
    let target = clause_as_set(terms, clause);
    if premises[1..].iter().all(|premise| premise.len() == 1) {
        let mut accumulator = clause_as_set(terms, premises[0]);
        for premise in &premises[1..] {
            let unit = clause_as_set(terms, premise)[0];
            let Some(position) = accumulator
                .iter()
                .position(|literal| *literal == unit.negated())
            else {
                return false;
            };
            accumulator.remove(position);
        }
        return accumulator == target;
    }
    let mut budget = premises.len() * 4 + 256;
    let mut stack = vec![(1usize, clause_as_set(terms, premises[0]))];
    while let Some((index, accumulator)) = stack.pop() {
        if index == premises.len() {
            if accumulator == target {
                return true;
            }
            continue;
        }
        if budget == 0 {
            break;
        }
        budget -= 1;
        let next = clause_as_set(terms, premises[index]);
        for resolvent in chain_resolve_candidates(&accumulator, &next, 8) {
            stack.push((index + 1, resolvent));
        }
    }
    false
}

/// One clause the chain does resolve to (the first full path the search
/// finds), spelled back as terms, so the differential sees many accepting
/// chains and not only random rejections.
fn some_resolvent(terms: &mut TermStore, premises: &[&[TermId]]) -> Option<Vec<TermId>> {
    let mut stack = vec![(1usize, clause_as_set(terms, premises[0]))];
    while let Some((index, accumulator)) = stack.pop() {
        if index == premises.len() {
            return Some(
                accumulator
                    .into_iter()
                    .map(|literal| {
                        if literal.positive {
                            literal.atom
                        } else {
                            terms.mk_not_raw(literal.atom)
                        }
                    })
                    .collect(),
            );
        }
        let next = clause_as_set(terms, premises[index]);
        for resolvent in chain_resolve_candidates(&accumulator, &next, 8) {
            stack.push((index + 1, resolvent));
        }
    }
    None
}

struct Lcg(u64);

impl Lcg {
    fn below(&mut self, bound: u64) -> u64 {
        self.0 = self
            .0
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (self.0 >> 33) % bound
    }
}

fn random_clause(rng: &mut Lcg, literals: &[TermId]) -> Vec<TermId> {
    let width = 1 + rng.below(3) as usize;
    (0..width)
        .map(|_| literals[rng.below(literals.len() as u64) as usize])
        .collect()
}

#[test]
fn the_fold_and_the_search_agree_on_random_chains() {
    let mut terms = TermStore::new();
    let atoms: Vec<TermId> = (0..4)
        .map(|index| terms.mk_var(format!("fold_atom_{index}"), Sort::Bool))
        .collect();
    let mut literals = atoms.clone();
    literals.extend(atoms.iter().map(|&atom| terms.mk_not_raw(atom)));
    let mut rng = Lcg(0x5eed_f01d);
    let (mut accepted, mut rejected) = (0usize, 0usize);
    for _ in 0..20_000 {
        let links = 1 + rng.below(5) as usize;
        let premises: Vec<Vec<TermId>> = (0..=links)
            .map(|_| random_clause(&mut rng, &literals))
            .collect();
        let premise_refs: Vec<&[TermId]> = premises.iter().map(Vec::as_slice).collect();
        let clause = match rng.below(3) {
            0 => Vec::new(),
            1 => random_clause(&mut rng, &literals),
            _ => some_resolvent(&mut terms, &premise_refs)
                .unwrap_or_else(|| random_clause(&mut rng, &literals)),
        };
        let reference = search_only(&terms, &clause, &premise_refs);
        let checked = validate_chain_resolution_rule(
            &terms,
            ProofId(0),
            &AletheRule::ThResolution,
            &clause,
            &premise_refs,
            &mut |_, _| true,
        )
        .is_ok();
        assert_eq!(
            checked, reference,
            "fold and search disagree on {premises:?} |- {clause:?}"
        );
        if checked {
            accepted += 1;
        } else {
            rejected += 1;
        }
    }
    assert!(accepted > 100 && rejected > 100, "{accepted} / {rejected}");
}

/// A projection fan of `k` links folds in work linear in `k`: the meter sees
/// one charge per link, each the size of that link's premise.
#[test]
fn a_projection_fan_is_charged_linearly() {
    let mut terms = TermStore::new();
    let to = terms.mk_var("fold_to", Sort::Bool);
    let from_atoms: Vec<TermId> = (0..1_000)
        .map(|index| terms.mk_var(format!("fold_f_{index}"), Sort::Bool))
        .collect();
    let from = terms.mk_var("fold_from", Sort::Bool);
    let not_from = terms.mk_not_raw(from);
    let mut gate = vec![not_from];
    gate.extend(from_atoms.iter().copied());
    let projections: Vec<Vec<TermId>> = from_atoms
        .iter()
        .map(|&atom| vec![to, terms.mk_not_raw(atom)])
        .collect();
    let mut premises: Vec<&[TermId]> = vec![gate.as_slice()];
    premises.extend(projections.iter().map(Vec::as_slice));
    let mut charged = 0usize;
    validate_chain_resolution_rule(
        &terms,
        ProofId(0),
        &AletheRule::ThResolution,
        &[not_from, to],
        &premises,
        &mut |work, _| {
            charged += work;
            true
        },
    )
    .expect("the fan resolves to (cl (not from) to)");
    assert!(
        charged <= 3 * premises.len(),
        "{charged} work units for {} premises",
        premises.len()
    );
}
