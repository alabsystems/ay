// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact source theorem for bounded integer existentials over one Boolean UF.
//!
//! This checker recognizes two deliberately small refutations:
//!
//! - an existential whose authored integer bounds have an empty intersection;
//! - `forall v. P(v) = (v = c)` paired with a positive or negated bounded
//!   existential whose only matrix atoms are its bounds and `P(x)`.
//!
//! The latter sentence is reduced by syntax, not by a solver result: the
//! existential is true exactly when `c` lies in the complete authored range.

use std::collections::HashSet;

use ay_core::term::{Constant, Symbol, TermData};
use ay_core::{Sort, TermId, TermStore};
use ay_frontend::{Context, ProjectionBindingRequest};
use num_bigint::BigInt;

const MAX_WORK: usize = 256;
const MAX_INTEGER_BITS: u64 = 4096;

#[derive(Clone)]
struct BoundedPredicate {
    negated: bool,
    lower: BigInt,
    upper: BigInt,
    predicate: Symbol,
}

struct PointwiseDefinition {
    predicate: Symbol,
    point: BigInt,
}

pub(super) fn exact_bounded_bool_uf_is_unsat(ctx: &Context, roots: &[TermId]) -> bool {
    if let [root] = roots {
        if empty_bounded_existential(&ctx.terms, *root) {
            return true;
        }
    }
    if exact_pinned_existential_roots_are_unsat(&ctx.terms, roots) {
        return true;
    }
    let [first, second] = roots else {
        return false;
    };
    checked_definition_pair_is_unsat(ctx, *first, *second)
        || checked_definition_pair_is_unsat(ctx, *second, *first)
}

fn checked_definition_pair_is_unsat(
    ctx: &Context,
    definition_root: TermId,
    existential_root: TermId,
) -> bool {
    let Some(definition) = parse_pointwise_definition(&ctx.terms, definition_root) else {
        return false;
    };
    let Some(existential) =
        parse_exact_bounded_predicate(&ctx.terms, existential_root, &definition.predicate)
    else {
        return false;
    };
    let request = ProjectionBindingRequest {
        symbol: definition.predicate.clone(),
        parameter_sorts: vec![Sort::Int],
        result_sort: Sort::Bool,
    };
    let Ok(binding) = ctx.check_projection_declaration(&request) else {
        return false;
    };
    if binding.symbol() != &existential.predicate {
        return false;
    }

    let point_is_in_range =
        existential.lower <= definition.point && definition.point <= existential.upper;
    point_is_in_range == existential.negated
}

/// Frontend pointwise-definition propagation can turn
/// `forall v. P(v) = (v = c)` into `forall v. true` and replace `P(x)` in the
/// sibling existential by `x = c` before the public query epoch is frozen.
/// Authenticate that exact post-propagation theorem directly: one bounded
/// pinned existential is false at the relevant polarity, and every sibling is
/// a literal source tautology.
fn exact_pinned_existential_roots_are_unsat(terms: &TermStore, roots: &[TermId]) -> bool {
    let mut found_refutation = false;
    for &root in roots {
        if let Some((negated, lower, upper, point)) = parse_exact_bounded_pin(terms, root) {
            if found_refutation {
                return false;
            }
            let point_is_in_range = lower <= point && point <= upper;
            if point_is_in_range != negated {
                return false;
            }
            found_refutation = true;
        } else if !source_tautology(terms, root) {
            return false;
        }
    }
    found_refutation
}

fn parse_exact_bounded_pin(
    terms: &TermStore,
    root: TermId,
) -> Option<(bool, BigInt, BigInt, BigInt)> {
    let negated = matches!(live_term(terms, root)?, TermData::Not(_));
    let (quantifier, body) = existential_parts(terms, root, true)?;
    let TermData::Exists(vars, _, triggers) = live_term(terms, quantifier)? else {
        return None;
    };
    let [(binder, Sort::Int)] = vars.as_slice() else {
        return None;
    };
    if !triggers.is_empty() || contains_quantifier_bounded(terms, body) {
        return None;
    }
    let bound = unique_named_int_var(terms, body, binder)?;
    let atoms = exact_conjuncts(terms, body)?;
    let mut lower = None;
    let mut upper = None;
    let mut point = None;
    for atom in atoms {
        if let Some(bound_kind) = literal_bound(terms, atom, bound) {
            merge_bound(&mut lower, &mut upper, bound_kind);
            continue;
        }
        let (left, right) = binary_app(terms, atom, "=", &Sort::Bool)?;
        let value = if left == bound {
            int_literal(terms, right)?
        } else if right == bound {
            int_literal(terms, left)?
        } else {
            return None;
        };
        if point.replace(value).is_some() {
            return None;
        }
    }
    Some((negated, lower?, upper?, point?))
}

fn source_tautology(terms: &TermStore, root: TermId) -> bool {
    require_sort(terms, root, &Sort::Bool).is_some()
        && match live_term(terms, root) {
            Some(TermData::Const(Constant::Bool(true))) => true,
            Some(TermData::Forall(vars, body, _)) => {
                !vars.is_empty()
                    && vars
                        .iter()
                        .map(|(name, _)| name)
                        .collect::<HashSet<_>>()
                        .len()
                        == vars.len()
                    && require_sort(terms, *body, &Sort::Bool).is_some()
                    && matches!(
                        live_term(terms, *body),
                        Some(TermData::Const(Constant::Bool(true)))
                    )
            }
            _ => false,
        }
}

fn empty_bounded_existential(terms: &TermStore, root: TermId) -> bool {
    let Some((_, body)) = existential_parts(terms, root, false) else {
        return false;
    };
    let TermData::Exists(vars, _, triggers) = terms.get(root) else {
        return false;
    };
    let [(binder, Sort::Int)] = vars.as_slice() else {
        return false;
    };
    if !triggers.is_empty() || contains_quantifier_bounded(terms, body) {
        return false;
    }
    let Some(bound) = unique_named_int_var(terms, body, binder) else {
        return false;
    };
    let Some((lower, upper)) = collect_literal_bounds(terms, body, bound, false) else {
        return false;
    };
    lower > upper
}

fn parse_pointwise_definition(terms: &TermStore, root: TermId) -> Option<PointwiseDefinition> {
    require_sort(terms, root, &Sort::Bool)?;
    let TermData::Forall(vars, body, triggers) = live_term(terms, root)? else {
        return None;
    };
    let [(binder, Sort::Int)] = vars.as_slice() else {
        return None;
    };
    if !triggers.is_empty() || contains_quantifier_bounded(terms, *body) {
        return None;
    }
    let bound = unique_named_int_var(terms, *body, binder)?;
    let (left, right) = binary_app(terms, *body, "=", &Sort::Bool)?;
    parse_definition_sides(terms, left, right, bound)
        .or_else(|| parse_definition_sides(terms, right, left, bound))
}

fn parse_definition_sides(
    terms: &TermStore,
    predicate_side: TermId,
    point_side: TermId,
    bound: TermId,
) -> Option<PointwiseDefinition> {
    let predicate = unary_bool_predicate(terms, predicate_side, bound)?;
    let (left, right) = binary_app(terms, point_side, "=", &Sort::Bool)?;
    let point = if left == bound {
        int_literal(terms, right)?
    } else if right == bound {
        int_literal(terms, left)?
    } else {
        return None;
    };
    Some(PointwiseDefinition { predicate, point })
}

fn parse_exact_bounded_predicate(
    terms: &TermStore,
    root: TermId,
    expected_predicate: &Symbol,
) -> Option<BoundedPredicate> {
    let negated = matches!(live_term(terms, root)?, TermData::Not(_));
    let (quantifier, body) = existential_parts(terms, root, true)?;
    let TermData::Exists(vars, _, triggers) = live_term(terms, quantifier)? else {
        return None;
    };
    let [(binder, Sort::Int)] = vars.as_slice() else {
        return None;
    };
    if !triggers.is_empty() || contains_quantifier_bounded(terms, body) {
        return None;
    }
    let bound = unique_named_int_var(terms, body, binder)?;
    let atoms = exact_conjuncts(terms, body)?;
    let mut lower = None;
    let mut upper = None;
    let mut predicate = None;
    for atom in atoms {
        if let Some(bound_kind) = literal_bound(terms, atom, bound) {
            merge_bound(&mut lower, &mut upper, bound_kind);
            continue;
        }
        let symbol = unary_bool_predicate(terms, atom, bound)?;
        if &symbol != expected_predicate || predicate.replace(symbol).is_some() {
            return None;
        }
    }
    Some(BoundedPredicate {
        negated,
        lower: lower?,
        upper: upper?,
        predicate: predicate?,
    })
}

fn existential_parts(
    terms: &TermStore,
    root: TermId,
    allow_negated: bool,
) -> Option<(TermId, TermId)> {
    require_sort(terms, root, &Sort::Bool)?;
    let quantifier = match live_term(terms, root)? {
        TermData::Exists(..) => root,
        TermData::Not(inner) if allow_negated => *inner,
        _ => return None,
    };
    require_sort(terms, quantifier, &Sort::Bool)?;
    let TermData::Exists(_, body, _) = live_term(terms, quantifier)? else {
        return None;
    };
    require_sort(terms, *body, &Sort::Bool)?;
    Some((quantifier, *body))
}

fn exact_conjuncts(terms: &TermStore, body: TermId) -> Option<Vec<TermId>> {
    let TermData::App(Symbol::Named(operator), atoms) = live_term(terms, body)? else {
        return None;
    };
    if operator != "and" || atoms.len() < 2 || atoms.len() > MAX_WORK {
        return None;
    }
    atoms
        .iter()
        .copied()
        .map(|atom| require_sort(terms, atom, &Sort::Bool).map(|()| atom))
        .collect()
}

fn collect_literal_bounds(
    terms: &TermStore,
    body: TermId,
    bound: TermId,
    require_all_atoms: bool,
) -> Option<(BigInt, BigInt)> {
    let atoms = exact_conjuncts(terms, body)?;
    let mut lower = None;
    let mut upper = None;
    for atom in atoms {
        if let Some(bound_kind) = literal_bound(terms, atom, bound) {
            merge_bound(&mut lower, &mut upper, bound_kind);
        } else if require_all_atoms {
            return None;
        }
    }
    Some((lower?, upper?))
}

enum LiteralBound {
    Lower(BigInt),
    Upper(BigInt),
}

fn literal_bound(terms: &TermStore, atom: TermId, bound: TermId) -> Option<LiteralBound> {
    require_sort(terms, atom, &Sort::Bool)?;
    let TermData::App(Symbol::Named(operator), args) = live_term(terms, atom)? else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    require_sort(terms, *left, &Sort::Int)?;
    require_sort(terms, *right, &Sort::Int)?;
    match (operator.as_str(), *left == bound, *right == bound) {
        ("<=", false, true) => Some(LiteralBound::Lower(int_literal(terms, *left)?)),
        ("<=", true, false) => Some(LiteralBound::Upper(int_literal(terms, *right)?)),
        ("<", false, true) => Some(LiteralBound::Lower(checked_int(
            int_literal(terms, *left)? + 1,
        )?)),
        ("<", true, false) => Some(LiteralBound::Upper(checked_int(
            int_literal(terms, *right)? - 1,
        )?)),
        (">=", true, false) => Some(LiteralBound::Lower(int_literal(terms, *right)?)),
        (">=", false, true) => Some(LiteralBound::Upper(int_literal(terms, *left)?)),
        (">", true, false) => Some(LiteralBound::Lower(checked_int(
            int_literal(terms, *right)? + 1,
        )?)),
        (">", false, true) => Some(LiteralBound::Upper(checked_int(
            int_literal(terms, *left)? - 1,
        )?)),
        _ => None,
    }
}

fn merge_bound(lower: &mut Option<BigInt>, upper: &mut Option<BigInt>, bound: LiteralBound) {
    match bound {
        LiteralBound::Lower(value) => {
            *lower = Some(lower.take().map_or(value.clone(), |old| old.max(value)));
        }
        LiteralBound::Upper(value) => {
            *upper = Some(upper.take().map_or(value.clone(), |old| old.min(value)));
        }
    }
}

fn unary_bool_predicate(
    terms: &TermStore,
    term: TermId,
    expected_argument: TermId,
) -> Option<Symbol> {
    require_sort(terms, term, &Sort::Bool)?;
    let TermData::App(symbol @ Symbol::Named(_), args) = live_term(terms, term)? else {
        return None;
    };
    let [argument] = args.as_slice() else {
        return None;
    };
    (*argument == expected_argument && terms.sort(*argument) == &Sort::Int).then(|| symbol.clone())
}

fn binary_app(
    terms: &TermStore,
    term: TermId,
    expected_operator: &str,
    expected_sort: &Sort,
) -> Option<(TermId, TermId)> {
    require_sort(terms, term, expected_sort)?;
    let TermData::App(Symbol::Named(operator), args) = live_term(terms, term)? else {
        return None;
    };
    let [left, right] = args.as_slice() else {
        return None;
    };
    (operator == expected_operator).then_some((*left, *right))
}

fn int_literal(terms: &TermStore, term: TermId) -> Option<BigInt> {
    require_sort(terms, term, &Sort::Int)?;
    match live_term(terms, term)? {
        TermData::Const(Constant::Int(value)) => checked_int(value.clone()),
        TermData::App(Symbol::Named(operator), args) if operator == "-" => {
            let [inner] = args.as_slice() else {
                return None;
            };
            checked_int(-int_literal(terms, *inner)?)
        }
        _ => None,
    }
}

fn checked_int(value: BigInt) -> Option<BigInt> {
    (value.bits() <= MAX_INTEGER_BITS).then_some(value)
}

fn unique_named_int_var(terms: &TermStore, root: TermId, name: &str) -> Option<TermId> {
    let mut stack = vec![root];
    let mut seen = HashSet::new();
    let mut found = None;
    let mut remaining = MAX_WORK;
    while let Some(term) = stack.pop() {
        if remaining == 0 {
            return None;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        match live_term(terms, term)? {
            TermData::Var(candidate, _) if candidate == name => {
                if terms.sort(term) != &Sort::Int || found.is_some_and(|prior| prior != term) {
                    return None;
                }
                found = Some(term);
            }
            TermData::Var(_, _) | TermData::Const(_) => {}
            TermData::App(_, args) => stack.extend(args.iter().copied()),
            TermData::Not(inner) => stack.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                stack.extend([*condition, *then_term, *else_term]);
            }
            _ => return None,
        }
    }
    found
}

fn contains_quantifier_bounded(terms: &TermStore, root: TermId) -> bool {
    let mut stack = vec![root];
    let mut seen = HashSet::new();
    let mut remaining = MAX_WORK;
    while let Some(term) = stack.pop() {
        if remaining == 0 || live_term(terms, term).is_none() {
            return true;
        }
        remaining -= 1;
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Forall(..) | TermData::Exists(..) => return true,
            _ => stack.extend(terms.children(term)),
        }
    }
    false
}

fn live_term(terms: &TermStore, term: TermId) -> Option<&TermData> {
    terms.entry_stamp(term)?;
    Some(terms.get(term))
}

fn require_sort(terms: &TermStore, term: TermId, expected: &Sort) -> Option<()> {
    terms.entry_stamp(term)?;
    (terms.sort(term) == expected).then_some(())
}
