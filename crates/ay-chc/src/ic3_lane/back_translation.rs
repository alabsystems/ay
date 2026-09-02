// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact reconstruction of bit-level IC3 clauses at the word level.

use std::collections::HashMap;
use std::sync::Arc;

use ay_sat::Literal;

use crate::pdr::model::{InvariantModel, PredicateInterpretation};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar, PredicateId};

use super::LatchMeaning;

#[cfg(test)]
mod tests;

/// Translate the bit-level inductive invariant (CNF over current-state latches)
/// into a word-level candidate. Structurally complementary implication clauses
/// are reconstructed as one exact `Iff`; every other clause stays in CNF.
pub(super) fn back_translate(
    pred: PredicateId,
    params: &[ChcVar],
    latches: &[LatchMeaning],
    clauses: &[Vec<Literal>],
) -> Option<InvariantModel> {
    let partners = exact_iff_partners(clauses);
    let mut conjuncts = Vec::with_capacity(clauses.len());
    for (index, clause) in clauses.iter().enumerate() {
        match partners[index] {
            Some(partner) if partner < index => continue,
            Some(_) => conjuncts.push(translate_iff(clause, params, latches)?),
            None => conjuncts.push(translate_clause(clause, params, latches)?),
        }
    }

    let formula = match conjuncts.len() {
        0 => ChcExpr::Bool(true),
        1 => conjuncts.pop()?,
        _ => ChcExpr::Op(ChcOp::And, conjuncts.into_iter().map(Arc::new).collect()),
    };
    let mut model = InvariantModel::new();
    model.set(pred, PredicateInterpretation::new(params.to_vec(), formula));
    Some(model)
}

/// Canonical key for exactly one implication clause `(!low | high)` or
/// `(low | !high)`. Same-sign pairs (the XOR encoding) and repeated variables
/// deliberately have no key.
fn binary_implication_key(clause: &[Literal]) -> Option<(usize, usize, bool)> {
    let [left, right] = clause else {
        return None;
    };
    let left_var = left.variable().index();
    let right_var = right.variable().index();
    if left_var == right_var || left.is_positive() == right.is_positive() {
        return None;
    }
    if left_var < right_var {
        Some((left_var, right_var, left.is_positive()))
    } else {
        Some((right_var, left_var, right.is_positive()))
    }
}

/// Pair only structural `(!a | b)` / `(a | !b)` complements. Lookup order is
/// deterministic; the map is never iterated, and duplicate clauses pair LIFO.
fn exact_iff_partners(clauses: &[Vec<Literal>]) -> Vec<Option<usize>> {
    let mut partners = vec![None; clauses.len()];
    let mut pending: HashMap<(usize, usize, bool), Vec<usize>> = HashMap::new();
    for (index, clause) in clauses.iter().enumerate() {
        let Some((low, high, low_positive)) = binary_implication_key(clause) else {
            continue;
        };
        let complement = (low, high, !low_positive);
        if let Some(prior) = pending.get_mut(&complement).and_then(Vec::pop) {
            partners[prior] = Some(index);
            partners[index] = Some(prior);
        } else {
            pending
                .entry((low, high, low_positive))
                .or_default()
                .push(index);
        }
    }
    partners
}

fn translate_iff(
    clause: &[Literal],
    params: &[ChcVar],
    latches: &[LatchMeaning],
) -> Option<ChcExpr> {
    let (low, high, _) = binary_implication_key(clause)?;
    let low_meaning = latches.get(low)?;
    let high_meaning = latches.get(high)?;
    if let Some(equality) = bool_int_bit_equality(low_meaning, high_meaning, params) {
        return Some(equality);
    }
    let low_atom = latch_to_expr(low_meaning, params)?;
    let high_atom = latch_to_expr(high_meaning, params)?;
    Some(ChcExpr::Op(
        ChcOp::Iff,
        vec![Arc::new(low_atom), Arc::new(high_atom)],
    ))
}

/// Exact arithmetic form of `bool <-> (int_bit == 1)`. The bit value is always
/// zero or one, so this avoids a nested Boolean equality without changing the
/// candidate: `bit = ite(bool, 1, 0)` is the same two-row truth table.
fn bool_int_bit_equality(
    first: &LatchMeaning,
    second: &LatchMeaning,
    params: &[ChcVar],
) -> Option<ChcExpr> {
    let orientations = [(first, second), (second, first)];
    for (bool_meaning, int_meaning) in orientations {
        let bool_param = params.get(bool_meaning.arg)?;
        if bool_meaning.bit.is_some() || !matches!(&bool_param.sort, ChcSort::Bool) {
            continue;
        }
        let int_param = params.get(int_meaning.arg)?;
        let Some(bit) = int_meaning.bit else {
            continue;
        };
        if !matches!(&int_param.sort, ChcSort::Int) {
            continue;
        }
        let bit_value = int_bit_value(int_param, bit);
        let indicator = ChcExpr::ite(
            ChcExpr::Var(bool_param.clone()),
            ChcExpr::Int(1),
            ChcExpr::Int(0),
        );
        return Some(ChcExpr::eq(bit_value, indicator));
    }
    None
}

fn translate_clause(
    clause: &[Literal],
    params: &[ChcVar],
    latches: &[LatchMeaning],
) -> Option<ChcExpr> {
    let mut disjuncts = Vec::with_capacity(clause.len());
    for literal in clause {
        let atom = latch_to_expr(latches.get(literal.variable().index())?, params)?;
        disjuncts.push(if literal.is_positive() {
            atom
        } else {
            ChcExpr::Op(ChcOp::Not, vec![Arc::new(atom)])
        });
    }
    Some(match disjuncts.len() {
        0 => ChcExpr::Bool(false),
        1 => disjuncts.pop()?,
        _ => ChcExpr::Op(ChcOp::Or, disjuncts.into_iter().map(Arc::new).collect()),
    })
}

/// Word-level Boolean atom for a single latch.
fn latch_to_expr(meaning: &LatchMeaning, params: &[ChcVar]) -> Option<ChcExpr> {
    let param = params.get(meaning.arg)?;
    match (meaning.bit, &param.sort) {
        (None, _) => Some(ChcExpr::Var(param.clone())),
        (Some(bit), ChcSort::BitVec(_)) => {
            let ext = ChcExpr::Op(
                ChcOp::BvExtract(bit as u32, bit as u32),
                vec![Arc::new(ChcExpr::Var(param.clone()))],
            );
            Some(ChcExpr::Op(
                ChcOp::Eq,
                vec![Arc::new(ext), Arc::new(ChcExpr::BitVec(1, 1))],
            ))
        }
        (Some(bit), _) => {
            let modulo = int_bit_value(param, bit);
            Some(ChcExpr::Op(
                ChcOp::Eq,
                vec![Arc::new(modulo), Arc::new(ChcExpr::Int(1))],
            ))
        }
    }
}

fn int_bit_value(param: &ChcVar, bit: usize) -> ChcExpr {
    let var = ChcExpr::Var(param.clone());
    let shifted = if bit == 0 {
        var
    } else {
        ChcExpr::Op(
            ChcOp::Div,
            vec![Arc::new(var), Arc::new(ChcExpr::Int(1i128 << bit))],
        )
    };
    ChcExpr::Op(
        ChcOp::Mod,
        vec![Arc::new(shifted), Arc::new(ChcExpr::Int(2))],
    )
}
