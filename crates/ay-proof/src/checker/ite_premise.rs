// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Structural recognition of Boolean-ITE branch implications
//! (#ite-expansion-authority).
//!
//! The executor's `rewrite_assertion_bool_ites` pass replaces a top-level
//! Bool-sorted assertion `(ite c t e)` with
//! `(and (=> c t) (=> (not c) e))`, and `FlattenAnd` then asserts the two
//! implications separately. Their activation units are not authored terms and
//! not `and`-conjuncts of authored terms, so both the strict checker's
//! premise validator and the exact-fragment builder need to recognize them as
//! ENTAILED premises of the authored ITE.
//!
//! This module is that recognition, shared by both consumers so classifier
//! and checker cannot drift. It is purely structural — it never interns a
//! term — and matches the exact canonical forms `mk_implies`/`mk_or`/`mk_not`
//! produce:
//!
//! * then-form: `(or (not g_1) .. (not g_k) T_1 .. T_m)` where
//!   `g_1 .. g_k` are the conjuncts of `c` (`[c]` itself when `c` is not an
//!   `and`) and `T_1 .. T_m` is the or-flattening of `t`;
//! * else-form: `(or c E_1 .. E_m)` with `E_1 .. E_m` the or-flattening of
//!   `e` (a conjunctive `c` stays one literal — `mk_or` does not flatten
//!   `and`);
//! * the combined pre-`FlattenAnd` form `(and then-form else-form)`.
//!
//! SOUNDNESS. Acceptance demands SET EQUALITY between the assumed term's
//! or-literals and the expected literal set — never a subset, which would be
//! a STRONGER (unentailed) clause. Under that equality the assumed term is a
//! consequence of the ITE in every model: if `c` holds, the ITE entails `t`,
//! so some `T_i` holds (then-form) / the literal `c` holds (else-form); if
//! `c` fails, some `(not g_i)` holds (then-form) / the ITE entails `e`, so
//! some `E_i` holds (else-form). Assuming an entailed premise in a
//! refutation of the authored problem is sound. Everything else — absorbed
//! literals, non-`and` condition rewrites (`mk_not` of an `or` condition
//! De Morgans into an `and` literal this matcher does not model), foreign
//! scrutinees — fails closed to non-recognition.

use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

/// Bounded or-flattening of a term into its disjunct set. `mk_or` interns
/// flat, sorted, deduplicated disjunctions, so one level is the common case;
/// the recursion is still bounded to be robust against hand-built terms.
fn flatten_or_into(terms: &TermStore, term: TermId, out: &mut Vec<TermId>, depth: usize) {
    if depth < 8 {
        if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
            if name == "or" {
                for &arg in args {
                    flatten_or_into(terms, arg, out, depth + 1);
                }
                return;
            }
        }
    }
    out.push(term);
}

/// The conjunct view of an ITE condition: the `and`-args for a conjunctive
/// condition, the condition itself otherwise.
fn condition_conjuncts(terms: &TermStore, cond: TermId) -> Vec<TermId> {
    if let TermData::App(Symbol::Named(name), args) = terms.get(cond) {
        if name == "and" && !args.is_empty() {
            return args.clone();
        }
    }
    vec![cond]
}

/// Whether `literals` is EXACTLY `{not g | g in conjuncts}` ∪ `flatten(branch)`
/// as a set. Every literal must be consumed and every expected member present.
fn matches_branch_form(
    terms: &TermStore,
    literals: &[TermId],
    negated_conjuncts_of: Option<&[TermId]>,
    positive_literal: Option<TermId>,
    branch: TermId,
) -> bool {
    let mut expected: Vec<TermId> = Vec::new();
    if let Some(pos) = positive_literal {
        expected.push(pos);
    }
    flatten_or_into(terms, branch, &mut expected, 0);
    // Guard literals are matched STRUCTURALLY: a literal `l` covers conjunct
    // `g` when `l` is `Not(g)` — no interning of the negation is needed.
    let conjuncts = negated_conjuncts_of.unwrap_or(&[]);

    let mut expected_used = vec![false; expected.len()];
    let mut conjunct_used = vec![false; conjuncts.len()];
    for &literal in literals {
        let mut consumed = false;
        for (slot, &candidate) in expected.iter().enumerate() {
            if !expected_used[slot] && candidate == literal {
                expected_used[slot] = true;
                consumed = true;
                break;
            }
        }
        if consumed {
            continue;
        }
        if let TermData::Not(inner) = terms.get(literal) {
            for (slot, &conjunct) in conjuncts.iter().enumerate() {
                if !conjunct_used[slot] && conjunct == *inner {
                    conjunct_used[slot] = true;
                    consumed = true;
                    break;
                }
            }
        }
        if !consumed {
            return false;
        }
    }
    // Set semantics: `mk_or` deduplicates, so a duplicated expected member can
    // be represented once. Require every expected disjunct and every guard to
    // be covered by SOME literal (checking coverage against the literal set
    // again, so a member consumed under one role still counts for a duplicate
    // slot of the same term).
    for (slot, &candidate) in expected.iter().enumerate() {
        if !expected_used[slot] && !literals.contains(&candidate) {
            return false;
        }
    }
    for (slot, &conjunct) in conjuncts.iter().enumerate() {
        if conjunct_used[slot] {
            continue;
        }
        let covered = literals
            .iter()
            .any(|&l| matches!(terms.get(l), TermData::Not(inner) if *inner == conjunct));
        if !covered {
            return false;
        }
    }
    true
}

/// Whether `assumed` is the then-implication, else-implication, or combined
/// `and` of both, for one of `authored_bool_ites` (each `(cond, then, else)`).
#[must_use]
pub fn assumed_is_authored_bool_ite_consequence(
    terms: &TermStore,
    assumed: TermId,
    authored_bool_ites: &[(TermId, TermId, TermId)],
) -> bool {
    if authored_bool_ites.is_empty() {
        return false;
    }
    // Combined `(and then-form else-form)` (pre-FlattenAnd shape).
    if let TermData::App(Symbol::Named(name), args) = terms.get(assumed) {
        if name == "and" && args.len() == 2 {
            let (a, b) = (args[0], args[1]);
            for &(cond, then_term, else_term) in authored_bool_ites {
                let ite = [(cond, then_term, else_term)];
                let a_then = assumed_is_single_branch(terms, a, &ite);
                let b_then = assumed_is_single_branch(terms, b, &ite);
                if let (Some(a_is_then), Some(b_is_then)) = (a_then, b_then) {
                    if a_is_then != b_is_then {
                        return true;
                    }
                }
            }
            // Fall through: a 2-arg `and` may still be a single branch form
            // in degenerate cases; the branch matcher below handles it.
        }
    }
    authored_bool_ites
        .iter()
        .any(|&(cond, then_term, else_term)| {
            assumed_is_single_branch(terms, assumed, &[(cond, then_term, else_term)]).is_some()
        })
}

/// `Some(true)` when `assumed` matches the then-implication of one supplied
/// ITE, `Some(false)` for the else-implication, `None` for neither.
fn assumed_is_single_branch(
    terms: &TermStore,
    assumed: TermId,
    authored_bool_ites: &[(TermId, TermId, TermId)],
) -> Option<bool> {
    let literals: Vec<TermId> = match terms.get(assumed) {
        TermData::App(Symbol::Named(name), args) if name == "or" => args.clone(),
        // `mk_or` collapses a single surviving disjunct to the disjunct
        // itself; treat any non-`or` as a one-literal clause.
        _ => vec![assumed],
    };
    for &(cond, then_term, else_term) in authored_bool_ites {
        if terms.sort(then_term) != &Sort::Bool {
            continue;
        }
        let conjuncts = condition_conjuncts(terms, cond);
        if matches_branch_form(terms, &literals, Some(&conjuncts), None, then_term) {
            return Some(true);
        }
        if matches_branch_form(terms, &literals, None, Some(cond), else_term) {
            return Some(false);
        }
    }
    None
}
