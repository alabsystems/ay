// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An INDEPENDENT, op-counting mirror of `validate_and_pos`.
//!
//! It shares no code with `crates/ay-proof/src/checker/boolean.rs` — it is
//! written from that module's stated behaviour — and
//! [`the_mirror_agrees_with_the_real_validator`] checks that its VERDICT matches
//! the real `validate_and_pos` on a sweep containing accepts AND rejects. That
//! agreement is what licenses the bound tests reading its counter as a lower
//! bound on the validator's own work.
//!
//! One "primitive" is one `TermStore::get`, one name comparison, one `TermId`
//! comparison, one length comparison, or one `matched`-bitmap probe — the same
//! granularity `AND_POS_SHALLOW_WORK_FACTOR`'s derivation counts in.
//!
//! Split from `metering_and_pos.rs` so each file stays inside the repository's
//! 500-line ceiling.

use super::metering_and_pos::{and_pos_step, app, validate_one};
use super::*;

fn mirror_strip_not(terms: &TermStore, term: TermId, ops: &mut usize) -> Option<TermId> {
    *ops += 1;
    match terms.get(term) {
        TermData::Not(inner) => Some(*inner),
        _ => None,
    }
}

fn mirror_app<'a>(
    terms: &'a TermStore,
    term: TermId,
    name: &str,
    ops: &mut usize,
) -> Option<&'a [TermId]> {
    *ops += 2;
    match terms.get(term) {
        TermData::App(Symbol::Named(found), args) if found == name => Some(args),
        _ => None,
    }
}

fn mirror_ite(
    terms: &TermStore,
    term: TermId,
    ops: &mut usize,
) -> Option<(TermId, TermId, TermId)> {
    *ops += 2;
    match terms.get(term) {
        TermData::Ite(c, t, e) => Some((*c, *t, *e)),
        TermData::App(Symbol::Named(name), args) if name == "ite" && args.len() == 3 => {
            Some((args[0], args[1], args[2]))
        }
        _ => None,
    }
}

pub(super) fn mirror_negation(
    terms: &TermStore,
    lit: TermId,
    term: TermId,
    ops: &mut usize,
) -> bool {
    let stripped = mirror_strip_not(terms, lit, ops);
    *ops += 1;
    if stripped == Some(term) {
        return true;
    }
    if let Some((condition, then_term, else_term)) = mirror_ite(terms, term, ops) {
        return match mirror_ite(terms, lit, ops) {
            Some((lit_condition, lit_then, lit_else)) => {
                *ops += 1;
                lit_condition == condition
                    && mirror_negation(terms, lit_then, then_term, ops)
                    && mirror_negation(terms, lit_else, else_term, ops)
            }
            None => false,
        };
    }
    *ops += 1;
    match terms.get(term) {
        TermData::Not(inner) => mirror_positive(terms, lit, *inner, ops),
        TermData::App(Symbol::Named(name), args) if name == "and" => {
            match mirror_app(terms, lit, "or", ops) {
                Some(disjuncts) => {
                    *ops += 1;
                    disjuncts.len() == args.len() && mirror_components(terms, disjuncts, args, ops)
                }
                None => false,
            }
        }
        TermData::App(Symbol::Named(name), args) if name == "or" => {
            match mirror_app(terms, lit, "and", ops) {
                Some(conjuncts) => {
                    *ops += 1;
                    conjuncts.len() == args.len() && mirror_components(terms, conjuncts, args, ops)
                }
                None => false,
            }
        }
        _ => false,
    }
}

fn mirror_positive(terms: &TermStore, lit: TermId, term: TermId, ops: &mut usize) -> bool {
    *ops += 1;
    if lit == term {
        return true;
    }
    *ops += 2;
    if !matches!(terms.get(term), TermData::App(Symbol::Named(name), _) if name == "and") {
        return false;
    }
    match mirror_strip_not(terms, lit, ops) {
        Some(inner) => mirror_negation(terms, inner, term, ops),
        None => false,
    }
}

fn mirror_components(
    terms: &TermStore,
    items: &[TermId],
    expected: &[TermId],
    ops: &mut usize,
) -> bool {
    *ops += 1;
    if items.len() != expected.len() {
        return false;
    }
    let mut matched = vec![false; expected.len()];
    for &item in items {
        let Some(index) = (0..expected.len()).find(|index| {
            *ops += 1;
            !matched[*index] && mirror_negation(terms, item, expected[*index], ops)
        }) else {
            return false;
        };
        matched[index] = true;
    }
    true
}

/// The mirror of `validate_and_pos` itself: its verdict and its primitive count.
pub(super) fn mirror_and_pos(
    terms: &TermStore,
    clause: &[TermId],
    position: u32,
    source: Option<TermId>,
) -> (bool, usize) {
    let mut ops = 1_usize;
    if clause.len() != 2 {
        return (false, ops);
    }
    // `decode_and_source`: the source term first, then the clause fallbacks.
    let args = source
        .and_then(|term| mirror_app(terms, term, "and", &mut ops))
        .or_else(|| {
            clause
                .iter()
                .copied()
                .find_map(|lit| mirror_app(terms, lit, "and", &mut ops))
        })
        .or_else(|| {
            clause.iter().copied().find_map(|lit| {
                let inner = mirror_strip_not(terms, lit, &mut ops)?;
                mirror_app(terms, inner, "and", &mut ops)
            })
        });
    let Some(args) = args else {
        return (false, ops);
    };
    let index = position as usize;
    ops += 1;
    if index >= args.len() {
        return (false, ops);
    }
    let has_gate = clause.iter().copied().any(|lit| {
        if source.is_some_and(|term| mirror_negation(terms, lit, term, &mut ops)) {
            return true;
        }
        let Some(inner) = mirror_strip_not(terms, lit, &mut ops) else {
            return false;
        };
        let Some(inner_args) = mirror_app(terms, inner, "and", &mut ops) else {
            return false;
        };
        ops += 1 + inner_args.len();
        inner_args == args
    });
    let has_conjunct = clause
        .iter()
        .copied()
        .any(|lit| mirror_positive(terms, lit, args[index], &mut ops));
    ops += 1;
    (has_gate && has_conjunct, ops)
}

/// The mirror is only evidence while it answers the same question the checker
/// does. Every case here is put to BOTH, and the two verdicts must agree —
/// including the rejecting ones, so the mirror cannot be a function that says
/// "valid" to everything.
#[test]
fn the_mirror_agrees_with_the_real_validator() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("mirror_a", Sort::Bool);
    let b = terms.mk_var("mirror_b", Sort::Bool);
    let c = terms.mk_var("mirror_c", Sort::Bool);
    let not_a = terms.mk_not_raw(a);
    let not_b = terms.mk_not_raw(b);
    let plain = app(&mut terms, "and", vec![a, b]);
    let not_plain = terms.mk_not_raw(plain);
    let disjunction = app(&mut terms, "or", vec![a, b]);
    let nested = app(&mut terms, "and", vec![disjunction, c]);
    let not_nested = terms.mk_not_raw(nested);
    let dual = app(&mut terms, "and", vec![not_a, not_b]);
    let half_dual = app(&mut terms, "and", vec![not_a, b]);
    let de_morgan = app(&mut terms, "or", vec![not_a, not_b]);

    let cases: Vec<(&str, TermId, u32, Vec<TermId>)> = vec![
        ("emitted shape, position 0", plain, 0, vec![not_plain, a]),
        ("emitted shape, position 1", plain, 1, vec![not_plain, b]),
        ("reordered clause", plain, 1, vec![b, not_plain]),
        ("de morgan gate", plain, 0, vec![de_morgan, a]),
        ("wrong conjunct", plain, 0, vec![not_plain, c]),
        ("no gate at all", plain, 0, vec![a, b]),
        ("index out of range", plain, 7, vec![not_plain, a]),
        ("wrong clause arity", plain, 0, vec![not_plain, a, b]),
        (
            "nested source, dual conjunct",
            nested,
            0,
            vec![not_nested, dual],
        ),
        (
            "nested source, half dual",
            nested,
            0,
            vec![not_nested, half_dual],
        ),
        (
            "nested source, plain conjunct",
            nested,
            1,
            vec![not_nested, c],
        ),
    ];

    let mut accepted = 0_usize;
    let mut rejected = 0_usize;
    for (label, source, position, clause) in cases {
        let step = and_pos_step(clause.clone(), position, source);
        let real = validate_one(&terms, &step).is_ok();
        let (mirrored, _) = mirror_and_pos(&terms, &clause, position, Some(source));
        assert_eq!(real, mirrored, "{label}: checker={real} mirror={mirrored}");
        if real {
            accepted += 1;
        } else {
            rejected += 1;
        }
    }
    assert!(accepted >= 3, "the sweep must contain ACCEPTS");
    assert!(rejected >= 3, "and REJECTS, or the agreement is vacuous");
}
