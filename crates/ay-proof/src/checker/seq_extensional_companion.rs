// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact strict theorem for symbolic-sequence extensional companions.

use std::collections::HashSet;

use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::Zero;

use super::ProofCheckError;

const ROOT_COUNT: usize = 5;
const PAIR_WORK_LIMIT: usize = 4096;

fn invalid(step: ProofId, reason: impl Into<String>) -> ProofCheckError {
    ProofCheckError::InvalidTheoryLemma {
        step,
        reason: format!("SeqExtensionalCompanionContradiction: {}", reason.into()),
    }
}

fn app<'a>(terms: &'a TermStore, term: TermId, name: &str, arity: usize) -> Option<&'a [TermId]> {
    match terms.get(term) {
        TermData::App(Symbol::Named(actual), args) if actual == name && args.len() == arity => {
            Some(args)
        }
        _ => None,
    }
}

fn strip_not(terms: &TermStore, term: TermId) -> Option<TermId> {
    match terms.get(term) {
        TermData::Not(inner) => Some(*inner),
        _ => None,
    }
}

fn match_lower(terms: &TermStore, root: TermId) -> Option<TermId> {
    let args = app(terms, root, "<=", 2)?;
    let zero = matches!(
        terms.get(args[0]),
        TermData::Const(Constant::Int(value)) if value == &BigInt::zero()
    );
    (zero && terms.sort(args[1]) == &Sort::Int && matches!(terms.get(args[1]), TermData::Var(..)))
        .then_some(args[1])
}

fn match_pin(terms: &TermStore, root: TermId, lower: TermId, len: TermId) -> Option<(TermId, u32)> {
    let disjuncts = app(terms, root, "or", 2)?;
    for (&guard, &equality) in [
        (&disjuncts[0], &disjuncts[1]),
        (&disjuncts[1], &disjuncts[0]),
    ] {
        let Some(actual_guard) = strip_not(terms, guard) else {
            continue;
        };
        if actual_guard != lower {
            continue;
        }
        let eq = app(terms, equality, "=", 2)?;
        let nat = if eq[0] == len {
            eq[1]
        } else if eq[1] == len {
            eq[0]
        } else {
            continue;
        };
        let nat_args = app(terms, nat, "bv2nat", 1)?;
        if terms.sort(nat) != &Sort::Int || !matches!(terms.get(nat_args[0]), TermData::Var(..)) {
            continue;
        }
        let Sort::BitVec(width) = terms.sort(nat_args[0]) else {
            continue;
        };
        if width.width > 0 && width.width <= 64 {
            return Some((nat_args[0], width.width));
        }
    }
    None
}

struct Positive<'a> {
    equality: TermId,
    tail: TermId,
    bindings: &'a [(String, Sort)],
    body: TermId,
    triggers: &'a [Vec<TermId>],
}

fn match_positive(terms: &TermStore, root: TermId) -> Option<Positive<'_>> {
    let conjuncts = app(terms, root, "and", 3)?;
    let quantified: Vec<usize> = conjuncts
        .iter()
        .enumerate()
        .filter_map(|(index, &part)| {
            matches!(terms.get(part), TermData::Forall(bindings, _, _) if bindings.len() == 1)
                .then_some(index)
        })
        .collect();
    let tails: Vec<usize> = conjuncts
        .iter()
        .enumerate()
        .filter_map(|(index, &part)| match_tail(terms, part).is_some().then_some(index))
        .collect();
    let ([quantified], [tail]) = (quantified.as_slice(), tails.as_slice()) else {
        return None;
    };
    if quantified == tail {
        return None;
    }
    let equality = (0..3).find(|index| index != quantified && index != tail)?;
    let (bindings, body, triggers) = match terms.get(conjuncts[*quantified]) {
        TermData::Forall(bindings, body, triggers) => {
            (bindings.as_slice(), *body, triggers.as_slice())
        }
        _ => return None,
    };
    Some(Positive {
        equality: conjuncts[equality],
        tail: conjuncts[*tail],
        bindings,
        body,
        triggers,
    })
}

struct Negative<'a> {
    not_equality: TermId,
    positive_len: TermId,
    not_tail_equality: TermId,
    bindings: &'a [(String, Sort)],
    body: TermId,
    triggers: &'a [Vec<TermId>],
}

fn match_negative(terms: &TermStore, root: TermId) -> Option<Negative<'_>> {
    let outer = app(terms, root, "or", 3)?;
    let quantified: Vec<usize> = outer
        .iter()
        .enumerate()
        .filter_map(|(index, &part)| {
            strip_not(terms, part)
                .is_some_and(|inner| {
                    matches!(terms.get(inner), TermData::Forall(bindings, _, _) if bindings.len() == 1)
                })
                .then_some(index)
        })
        .collect();
    let tails: Vec<usize> = outer
        .iter()
        .enumerate()
        .filter_map(|(index, &part)| match_tail_dual(terms, part).is_some().then_some(index))
        .collect();
    let ([quantified], [tail]) = (quantified.as_slice(), tails.as_slice()) else {
        return None;
    };
    if quantified == tail {
        return None;
    }
    let equality = (0..3).find(|index| index != quantified && index != tail)?;
    let equality = strip_not(terms, outer[equality])?;
    let (positive_len, tail_equality) = match_tail_dual(terms, outer[*tail])?;
    let quantified = strip_not(terms, outer[*quantified])?;
    let (bindings, body, triggers) = match terms.get(quantified) {
        TermData::Forall(bindings, body, triggers) if bindings.len() == 1 => {
            (bindings.as_slice(), *body, triggers.as_slice())
        }
        _ => return None,
    };
    Some(Negative {
        not_equality: equality,
        positive_len,
        not_tail_equality: tail_equality,
        bindings,
        body,
        triggers,
    })
}

fn match_tail(terms: &TermStore, tail: TermId) -> Option<(TermId, TermId)> {
    let disjuncts = app(terms, tail, "or", 2)?;
    for (&maybe_not_guard, &equality) in [
        (&disjuncts[0], &disjuncts[1]),
        (&disjuncts[1], &disjuncts[0]),
    ] {
        if let Some(positive_len) = strip_not(terms, maybe_not_guard) {
            if app(terms, equality, "=", 2).is_some() {
                return Some((positive_len, equality));
            }
        }
    }
    None
}

fn match_tail_dual(terms: &TermStore, tail: TermId) -> Option<(TermId, TermId)> {
    let conjuncts = app(terms, tail, "and", 2)?;
    for (&positive_len, &maybe_not_equality) in [
        (&conjuncts[0], &conjuncts[1]),
        (&conjuncts[1], &conjuncts[0]),
    ] {
        let Some(equality) = strip_not(terms, maybe_not_equality) else {
            continue;
        };
        if app(terms, equality, "=", 2).is_some() {
            return Some((positive_len, equality));
        }
    }
    None
}

fn match_pointwise(
    terms: &TermStore,
    body: TermId,
    binder: &str,
    companion: TermId,
) -> Option<(TermId, TermId, TermId)> {
    let disjuncts = app(terms, body, "or", 2)?;
    let (equality, bound) = [(disjuncts[0], disjuncts[1]), (disjuncts[1], disjuncts[0])]
        .into_iter()
        .find_map(|(equality, maybe_not_bound)| {
            let bound = strip_not(terms, maybe_not_bound)?;
            (app(terms, equality, "=", 2).is_some() && app(terms, bound, "bvult", 2).is_some())
                .then_some((equality, bound))
        })?;
    let bound_args = app(terms, bound, "bvult", 2)?;
    if bound_args[1] != companion {
        return None;
    }
    let TermData::Var(name, _) = terms.get(bound_args[0]) else {
        return None;
    };
    if name != binder {
        return None;
    }
    let equality = app(terms, equality, "=", 2)?;
    let left = app(terms, equality[0], "select", 2)?;
    let right = app(terms, equality[1], "select", 2)?;
    if left[1] != bound_args[0] || right[1] != bound_args[0] {
        return None;
    }
    Some((left[0], right[0], bound_args[0]))
}

fn equivalent_under_exact_substitution(
    terms: &TermStore,
    left: TermId,
    right: TermId,
    binder_left: TermId,
    binder_right: TermId,
    companion_left: TermId,
    companion_right: TermId,
) -> bool {
    let mut work = 0usize;
    let mut seen = HashSet::new();
    let mut pending = vec![(left, right)];
    while let Some((a, b)) = pending.pop() {
        work += 1;
        if work > PAIR_WORK_LIMIT || !seen.insert((a, b)) {
            if work > PAIR_WORK_LIMIT {
                return false;
            }
            continue;
        }
        if a == binder_left {
            if b != binder_right {
                return false;
            }
            continue;
        }
        if b == binder_right {
            return false;
        }
        if a == companion_left {
            if b != companion_right {
                return false;
            }
            continue;
        }
        if b == companion_right {
            return false;
        }
        if terms.sort(a) != terms.sort(b) {
            return false;
        }
        match (terms.get(a), terms.get(b)) {
            (TermData::Const(ca), TermData::Const(cb)) if ca == cb => {}
            (TermData::Var(..), TermData::Var(..)) if a == b => {}
            (TermData::App(sa, aa), TermData::App(sb, ab)) if sa == sb && aa.len() == ab.len() => {
                pending.extend(aa.iter().copied().zip(ab.iter().copied()));
            }
            (TermData::Not(aa), TermData::Not(ab)) => pending.push((*aa, *ab)),
            (TermData::Ite(ca, ta, ea), TermData::Ite(cb, tb, eb)) => {
                pending.extend([(*ca, *cb), (*ta, *tb), (*ea, *eb)]);
            }
            // Additional binders and lets are not admitted by this theorem.
            _ => return false,
        }
    }
    true
}

fn triggers_are_exact_renamings(
    terms: &TermStore,
    left: &[Vec<TermId>],
    right: &[Vec<TermId>],
    binder_left: TermId,
    binder_right: TermId,
    companion_left: TermId,
    companion_right: TermId,
) -> bool {
    if left.len() != right.len() || left.len() > PAIR_WORK_LIMIT {
        return false;
    }
    let mut trigger_terms = 0usize;
    left.iter().zip(right).all(|(left_group, right_group)| {
        if left_group.is_empty() || left_group.len() != right_group.len() {
            return false;
        }
        let Some(next) = trigger_terms.checked_add(left_group.len()) else {
            return false;
        };
        trigger_terms = next;
        trigger_terms <= PAIR_WORK_LIMIT
            && left_group.iter().zip(right_group).all(|(&left, &right)| {
                equivalent_under_exact_substitution(
                    terms,
                    left,
                    right,
                    binder_left,
                    binder_right,
                    companion_left,
                    companion_right,
                )
            })
    })
}

/// Validate one five-literal exact symbolic-sequence contradiction.
pub(super) fn validate(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
) -> Result<(), ProofCheckError> {
    if clause.len() != ROOT_COUNT {
        return Err(invalid(
            step,
            "clause must negate exactly five source roots",
        ));
    }
    if clause
        .iter()
        .any(|literal| literal.index() >= terms.len() || terms.sort(*literal) != &Sort::Bool)
    {
        return Err(invalid(step, "every literal must be a live Boolean term"));
    }
    let roots: Vec<TermId> = clause
        .iter()
        .map(|&literal| strip_not(terms, literal))
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| invalid(step, "every literal must be one outer negation"))?;
    let roots: [TermId; ROOT_COUNT] = roots
        .try_into()
        .map_err(|_| invalid(step, "clause must negate exactly five source roots"))?;
    if roots
        .iter()
        .any(|root| root.index() >= terms.len() || terms.sort(*root) != &Sort::Bool)
    {
        return Err(invalid(
            step,
            "every recovered source root must be live and Boolean",
        ));
    }
    validate_roots(terms, step, &roots)
}

fn validate_roots(
    terms: &TermStore,
    step: ProofId,
    roots: &[TermId; ROOT_COUNT],
) -> Result<(), ProofCheckError> {
    if roots.iter().copied().collect::<HashSet<_>>().len() != ROOT_COUNT {
        return Err(invalid(step, "the five source roots must be distinct"));
    }
    let len = match_lower(terms, roots[0]).ok_or_else(|| invalid(step, "invalid lower guard"))?;
    let (c1, width1) = match_pin(terms, roots[1], roots[0], len)
        .ok_or_else(|| invalid(step, "invalid first guarded companion pin"))?;
    let (c2, width2) = match_pin(terms, roots[2], roots[0], len)
        .ok_or_else(|| invalid(step, "invalid second guarded companion pin"))?;
    if c1 == c2 || width1 != width2 {
        return Err(invalid(
            step,
            "companions must be distinct and have one width",
        ));
    }
    let positive = match_positive(terms, roots[3])
        .ok_or_else(|| invalid(step, "invalid positive extensional conjunction"))?;
    let negative = match_negative(terms, roots[4])
        .ok_or_else(|| invalid(step, "invalid normalized extensional negation"))?;
    if negative.not_equality != positive.equality {
        return Err(invalid(step, "length equality complement does not align"));
    }
    let (positive_len, tail_equality) = match_tail(terms, positive.tail)
        .ok_or_else(|| invalid(step, "invalid positive tail implication"))?;
    if positive_len != negative.positive_len || tail_equality != negative.not_tail_equality {
        return Err(invalid(step, "tail dual does not align exactly"));
    }
    let [(binder1, sort1)] = positive.bindings else {
        return Err(invalid(step, "positive quantifier must bind one variable"));
    };
    let [(binder2, sort2)] = negative.bindings else {
        return Err(invalid(step, "negative quantifier must bind one variable"));
    };
    if sort1 != sort2 || sort1 != &Sort::bitvec(width1) {
        return Err(invalid(step, "quantifier and companion widths differ"));
    }
    let (left1, right1, bound1) = match_pointwise(terms, positive.body, binder1, c1)
        .ok_or_else(|| invalid(step, "invalid positive pointwise body"))?;
    let (left2, right2, bound2) = match_pointwise(terms, negative.body, binder2, c2)
        .ok_or_else(|| invalid(step, "invalid negative pointwise body"))?;
    if [c1, c2].contains(&bound1) || [c1, c2].contains(&bound2) {
        return Err(invalid(step, "quantifier binder shadows a companion"));
    }
    if left1 != left2 || right1 != right2 {
        return Err(invalid(step, "pointwise arrays differ"));
    }
    if !equivalent_under_exact_substitution(
        terms,
        positive.body,
        negative.body,
        bound1,
        bound2,
        c1,
        c2,
    ) || !triggers_are_exact_renamings(
        terms,
        positive.triggers,
        negative.triggers,
        bound1,
        bound2,
        c1,
        c2,
    ) {
        return Err(invalid(
            step,
            "quantifier bodies and triggers are not exact renamings",
        ));
    }
    Ok(())
}

/// Find the exact five public roots certified by this theorem. Search order is
/// deterministic; every candidate is revalidated through the strict clause
/// checker, so this selector carries no independent semantic authority.
pub fn recognize(terms: &TermStore, public_roots: &[TermId]) -> Option<[TermId; ROOT_COUNT]> {
    if public_roots.len() > super::bv_lia_query::MAX_BV_LIA_QUERY_ROOTS
        || public_roots
            .iter()
            .any(|root| root.index() >= terms.len() || terms.sort(*root) != &Sort::Bool)
    {
        return None;
    }
    let mut work = 0usize;
    for &lower in public_roots {
        let Some(len) = match_lower(terms, lower) else {
            continue;
        };
        let pins: Vec<TermId> = public_roots
            .iter()
            .copied()
            .filter(|&root| match_pin(terms, root, lower, len).is_some())
            .collect();
        for (index, &first) in pins.iter().enumerate() {
            for &second in &pins[index + 1..] {
                for &positive in public_roots {
                    if match_positive(terms, positive).is_none() {
                        continue;
                    }
                    for &negative in public_roots {
                        for (first, second) in [(first, second), (second, first)] {
                            work = work.checked_add(1)?;
                            if work > PAIR_WORK_LIMIT {
                                return None;
                            }
                            let roots = [lower, first, second, positive, negative];
                            if validate_roots(terms, ProofId(0), &roots).is_ok() {
                                return Some(roots);
                            }
                        }
                    }
                }
            }
        }
    }
    None
}

#[cfg(test)]
#[path = "seq_extensional_companion_tests.rs"]
mod tests;
