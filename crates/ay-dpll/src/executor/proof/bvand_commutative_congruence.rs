// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::DetHashMap;
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofId, Sort, Symbol, TermId, TermStore, TheoryLemmaKind};

const MAX_CONGRUENCE_NODES: usize = 256;

/// Build an exact equality proof when two terms differ only by one or more
/// binary `bvand` operand swaps below otherwise identical applications/ites.
///
/// Every commutativity leaf is first admitted by `ay-proof`'s independent
/// proof-producing BV recognizer (bit-blast + surfaced LRAT replay at wide
/// widths). Ordinary `cong` steps then lift those checked equalities through
/// the exact raw source tree. This is intentionally not a normalization
/// assumption: the original, unnormalized assertion remains the proof's
/// `assume`, and every rewrite edge is explicit and checker-replayed.
pub(super) fn add_bvand_commutative_congruence_proof(
    terms: &mut TermStore,
    proof: &mut Proof,
    left: TermId,
    right: TermId,
) -> Option<ProofId> {
    let initial_step_count = proof.steps.len();
    let mut memo = DetHashMap::default();
    let mut visited = 0;
    let result = recurse(terms, proof, left, right, &mut memo, &mut visited);
    if result.is_none() {
        // Keep the caller's candidate transactional: a valid swap proved in an
        // early argument must not survive when a later differing argument
        // falls outside this exact lane.
        proof.steps.truncate(initial_step_count);
    }
    result
}

fn recurse(
    terms: &mut TermStore,
    proof: &mut Proof,
    left: TermId,
    right: TermId,
    memo: &mut DetHashMap<(TermId, TermId), ProofId>,
    visited: &mut usize,
) -> Option<ProofId> {
    if left == right {
        return None;
    }
    if let Some(&step) = memo.get(&(left, right)) {
        return Some(step);
    }
    *visited = visited.checked_add(1)?;
    if *visited > MAX_CONGRUENCE_NODES || terms.sort(left) != terms.sort(right) {
        return None;
    }

    let left_data = terms.get(left).clone();
    let right_data = terms.get(right).clone();
    if let (TermData::App(left_symbol, left_args), TermData::App(right_symbol, right_args)) =
        (&left_data, &right_data)
    {
        if matches!(left_symbol, Symbol::Named(name) if name == "bvand")
            && matches!(right_symbol, Symbol::Named(name) if name == "bvand")
            && left_args.len() == 2
            && right_args.as_slice() == [left_args[1], left_args[0]]
            && matches!(terms.sort(left), Sort::BitVec(_))
        {
            let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
            if !ay_proof::recognize_bv_bitblast(terms, &[equality]) {
                return None;
            }
            let step =
                proof.add_theory_lemma_with_kind("bv", vec![equality], TheoryLemmaKind::BvBitBlast);
            memo.insert((left, right), step);
            return Some(step);
        }
    }

    let (left_args, right_args) = match (left_data, right_data) {
        (TermData::App(left_symbol, left_args), TermData::App(right_symbol, right_args))
            if left_symbol == right_symbol && left_args.len() == right_args.len() =>
        {
            (left_args, right_args)
        }
        (
            TermData::Ite(left_condition, left_then, left_else),
            TermData::Ite(right_condition, right_then, right_else),
        ) => (
            vec![left_condition, left_then, left_else],
            vec![right_condition, right_then, right_else],
        ),
        _ => return None,
    };

    let mut premises = Vec::new();
    for (left_arg, right_arg) in left_args.into_iter().zip(right_args) {
        if left_arg == right_arg {
            continue;
        }
        premises.push(recurse(terms, proof, left_arg, right_arg, memo, visited)?);
    }
    if premises.is_empty() {
        return None;
    }
    let equality = terms.mk_app(Symbol::named("="), [left, right], Sort::Bool);
    let step = proof.add_rule_step(AletheRule::Cong, vec![equality], premises, Vec::new());
    memo.insert((left, right), step);
    Some(step)
}
