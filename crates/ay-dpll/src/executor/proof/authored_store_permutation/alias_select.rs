// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::alias_index::AuthoredIndex;
use super::*;

const MAX_ALIAS_CANDIDATES: usize = 512;
const MAX_STORE_CHAIN_DEPTH: usize = 32;

#[derive(Clone, Copy)]
enum PairDischarge {
    Authored(TermId),
    Endpoint {
        disequality: TermId,
        refutation: EndpointRefutation,
    },
}

#[derive(Clone, Copy)]
struct IndexPair {
    equality: TermId,
    discharge: PairDischarge,
}

struct SelectConflict {
    root: TermId,
    equality: TermId,
    left_alias: TermId,
    right_alias: TermId,
}

#[derive(Clone, Copy)]
pub(super) struct ArrayBindingSupport {
    pub(super) root: TermId,
    pub(super) chain: TermId,
    pub(super) assume: ProofId,
}

pub(super) fn try_reconstruct(
    exec: &mut Executor,
    proof: &mut Proof,
    authored: &[TermId],
    authored_index: &AuthoredIndex,
) -> bool {
    let mut candidate_count = 0_usize;
    for &root in authored {
        let Some(conflict) = decode_select_conflict(&exec.ctx.terms, root) else {
            continue;
        };
        let Some(left) = authored_index.array_bindings(conflict.left_alias) else {
            continue;
        };
        let Some(right) = authored_index.array_bindings(conflict.right_alias) else {
            continue;
        };
        for &(left_root, left_chain) in left {
            for &(right_root, right_chain) in right {
                if left_root == right_root {
                    continue;
                }
                candidate_count = candidate_count.saturating_add(1);
                if candidate_count > MAX_ALIAS_CANDIDATES {
                    return false;
                }
                let roots = (left_root, right_root);
                let chains = (left_chain, right_chain);
                let Some(candidate) =
                    build_candidate(exec, authored_index, &conflict, roots, chains)
                else {
                    continue;
                };
                if exec.commit_if_strictly_checked(proof, candidate, authored) {
                    return true;
                }
            }
        }
    }
    false
}

fn select_parts(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "select" && args.len() == 2 => {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn decode_select_conflict(terms: &TermStore, root: TermId) -> Option<SelectConflict> {
    let TermData::Not(equality) = terms.get(root) else {
        return None;
    };
    let equality = *equality;
    let (left_select, right_select) = decode_eq_local(terms, equality)?;
    if terms.sort(left_select) != terms.sort(right_select) {
        return None;
    }
    let (left_alias, left_index) = select_parts(terms, left_select)?;
    let (right_alias, right_index) = select_parts(terms, right_select)?;
    if left_index != right_index || left_alias == right_alias {
        return None;
    }
    Some(SelectConflict {
        root,
        equality,
        left_alias,
        right_alias,
    })
}

fn build_candidate(
    exec: &mut Executor,
    authored_index: &AuthoredIndex,
    conflict: &SelectConflict,
    roots: (TermId, TermId),
    chains: (TermId, TermId),
) -> Option<Proof> {
    let (left_root, right_root) = roots;
    let (left_chain, right_chain) = chains;
    let mut candidate = Proof::new();
    let left_assume = candidate.add_assume(left_root, None);
    let right_assume = candidate.add_assume(right_root, None);
    let select_assume = candidate.add_assume(conflict.root, None);
    let (alias_equality, alias) = add_array_alias_support(
        exec,
        &mut candidate,
        authored_index,
        (conflict.left_alias, conflict.right_alias),
        [
            ArrayBindingSupport {
                root: left_root,
                chain: left_chain,
                assume: left_assume,
            },
            ArrayBindingSupport {
                root: right_root,
                chain: right_chain,
                assume: right_assume,
            },
        ],
    )?;
    finish_select_refutation(
        exec,
        candidate,
        conflict,
        alias_equality,
        alias,
        select_assume,
    )
}

pub(super) fn add_array_alias_support(
    exec: &mut Executor,
    candidate: &mut Proof,
    authored_index: &AuthoredIndex,
    aliases: (TermId, TermId),
    bindings: [ArrayBindingSupport; 2],
) -> Option<(TermId, ProofId)> {
    let chain_support = if bindings[0].chain == bindings[1].chain {
        None
    } else {
        Some(add_permutation_support(
            exec,
            candidate,
            authored_index,
            bindings[0].chain,
            bindings[1].chain,
        )?)
    };
    let alias_equality =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [aliases.0, aliases.1], Sort::Bool);
    let mut supports = vec![(bindings[0].root, bindings[0].assume)];
    if let Some(support) = chain_support {
        supports.push(support);
    }
    supports.push((bindings[1].root, bindings[1].assume));
    let alias = add_transitivity(&mut exec.ctx.terms, candidate, alias_equality, &supports)?;
    Some((alias_equality, alias))
}

fn store_chain(terms: &TermStore, term: TermId) -> Option<(TermId, Vec<(TermId, TermId)>)> {
    let Sort::Array(_) = terms.sort(term) else {
        return None;
    };
    let mut current = term;
    let mut entries = Vec::new();
    while let TermData::App(Symbol::Named(name), args) = terms.get(current) {
        if name != "store" || args.len() != 3 {
            break;
        }
        if entries.len() == MAX_STORE_CHAIN_DEPTH {
            return None;
        }
        let (base, index, value) = (args[0], args[1], args[2]);
        let Sort::Array(array_sort) = terms.sort(base) else {
            return None;
        };
        if terms.sort(current) != terms.sort(base)
            || terms.sort(index) != &array_sort.index_sort
            || terms.sort(value) != &array_sort.element_sort
        {
            return None;
        }
        entries.push((index, value));
        current = base;
    }
    Some((current, entries))
}

fn permutation_shape(
    terms: &TermStore,
    left_chain: TermId,
    right_chain: TermId,
) -> Option<(TermId, Vec<TermId>)> {
    let (left_base, left_entries) = store_chain(terms, left_chain)?;
    let (right_base, right_entries) = store_chain(terms, right_chain)?;
    if left_base != right_base
        || left_entries.len() < 2
        || left_entries.len() != right_entries.len()
    {
        return None;
    }
    let mut left_pairs = left_entries.clone();
    let mut right_pairs = right_entries;
    left_pairs.sort_unstable();
    right_pairs.sort_unstable();
    if left_pairs != right_pairs {
        return None;
    }
    let mut indices: Vec<_> = left_entries.iter().map(|&(index, _)| index).collect();
    indices.sort_unstable();
    indices.dedup();
    (indices.len() == left_entries.len()).then_some((left_base, indices))
}

fn add_permutation_support(
    exec: &mut Executor,
    candidate: &mut Proof,
    authored_index: &AuthoredIndex,
    left_chain: TermId,
    right_chain: TermId,
) -> Option<(TermId, ProofId)> {
    let (_, indices) = permutation_shape(&exec.ctx.terms, left_chain, right_chain)?;
    let chain_equality =
        exec.ctx
            .terms
            .mk_app(Symbol::named("="), [left_chain, right_chain], Sort::Bool);
    let mut pairs = Vec::new();
    for (position, &left) in indices.iter().enumerate() {
        for &right in &indices[position + 1..] {
            pairs.push(index_pair_support(exec, authored_index, left, right)?);
        }
    }
    let expected = indices.len() * (indices.len() - 1) / 2;
    if pairs.len() != expected {
        return None;
    }
    resolve_permutation(candidate, chain_equality, &pairs, &exec.ctx.terms)
}

fn index_pair_support(
    exec: &mut Executor,
    authored_index: &AuthoredIndex,
    left: TermId,
    right: TermId,
) -> Option<IndexPair> {
    if let Some((root, equality)) = authored_index.pair(left, right) {
        return Some(IndexPair {
            equality,
            discharge: PairDischarge::Authored(root),
        });
    }
    let equality = exec
        .ctx
        .terms
        .mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let disequality = exec.ctx.terms.mk_not_raw(equality);
    let refutation = Executor::endpoint_refutation_for(&exec.ctx.terms, left, right, disequality)?;
    Some(IndexPair {
        equality,
        discharge: PairDischarge::Endpoint {
            disequality,
            refutation,
        },
    })
}

fn resolve_permutation(
    candidate: &mut Proof,
    chain_equality: TermId,
    pairs: &[IndexPair],
    terms: &TermStore,
) -> Option<(TermId, ProofId)> {
    let authored_assumes: Vec<_> = pairs
        .iter()
        .map(|pair| match pair.discharge {
            PairDischarge::Authored(root) => Some(candidate.add_assume(root, None)),
            PairDischarge::Endpoint { .. } => None,
        })
        .collect();
    let mut clause: Vec<_> = pairs.iter().map(|pair| pair.equality).collect();
    clause.push(chain_equality);
    if ay_proof::recognize_array_theory_lemma(terms, &clause)
        != Some(TheoryLemmaKind::ArrayStorePermutation)
    {
        return None;
    }
    let mut current = candidate.add_theory_lemma_with_kind(
        "array",
        clause.clone(),
        TheoryLemmaKind::ArrayStorePermutation,
    );
    let mut residual = clause;
    for (pair, authored_assume) in pairs.iter().zip(authored_assumes) {
        let equality = pair.equality;
        let support = match (pair.discharge, authored_assume) {
            (PairDischarge::Authored(_), Some(assume)) => assume,
            (
                PairDischarge::Endpoint {
                    disequality,
                    refutation,
                },
                None,
            ) => Executor::add_endpoint_refutation_lemma(candidate, refutation, disequality),
            _ => return None,
        };
        let position = residual.iter().position(|&literal| literal == equality)?;
        let _ = residual.remove(position);
        current = candidate.add_resolution(residual.clone(), equality, current, support);
    }
    (residual == vec![chain_equality]).then_some((chain_equality, current))
}

pub(super) fn add_transitivity(
    terms: &mut TermStore,
    candidate: &mut Proof,
    conclusion: TermId,
    supports: &[(TermId, ProofId)],
) -> Option<ProofId> {
    let mut clause: Vec<_> = supports
        .iter()
        .map(|&(equality, _)| terms.mk_not_raw(equality))
        .collect();
    clause.push(conclusion);
    let mut current =
        candidate.add_theory_lemma_with_kind("euf", clause.clone(), TheoryLemmaKind::EufTransitive);
    let mut residual = clause;
    for &(equality, support) in supports {
        let negated = terms.mk_not_raw(equality);
        let position = residual.iter().position(|&literal| literal == negated)?;
        let _ = residual.remove(position);
        current = candidate.add_resolution(residual.clone(), equality, current, support);
    }
    (residual == vec![conclusion]).then_some(current)
}

pub(super) fn add_select_congruence(
    exec: &mut Executor,
    candidate: &mut Proof,
    array_equality: TermId,
    array_support: ProofId,
    select_equality: TermId,
) -> Option<ProofId> {
    let not_array = exec.ctx.terms.mk_not_raw(array_equality);
    let select_clause = vec![not_array, select_equality];
    if ay_proof::recognize_array_theory_lemma(&exec.ctx.terms, &select_clause)
        != Some(TheoryLemmaKind::ArrayRowChain)
    {
        return None;
    }
    let row = candidate.add_theory_lemma_with_kind(
        "array",
        select_clause,
        TheoryLemmaKind::ArrayRowChain,
    );
    Some(candidate.add_resolution(vec![select_equality], array_equality, row, array_support))
}

fn finish_select_refutation(
    exec: &mut Executor,
    mut candidate: Proof,
    conflict: &SelectConflict,
    alias_equality: TermId,
    alias: ProofId,
    select_assume: ProofId,
) -> Option<Proof> {
    let selected = add_select_congruence(
        exec,
        &mut candidate,
        alias_equality,
        alias,
        conflict.equality,
    )?;
    candidate.add_resolution(Vec::new(), conflict.equality, selected, select_assume);
    Some(candidate)
}
