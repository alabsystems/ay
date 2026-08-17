// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Differential and complexity coverage for the packed-clausification
//! recognizer's disjunct index.
//!
//! `is_packed_clausification_tautology` decides, structurally, whether a UNIT
//! `BoolTautology` clause is one of the Tseitin shapes (`and_pos`, `or_pos`,
//! `and_neg`, `or_neg`, or a bare self-complement). It used to answer every
//! membership question with a linear `Vec` scan, which made it
//! `O(D^2 + D * sum(M))` in the unit's payload — quadratic, and therefore
//! impossible to charge linearly. It now indexes the top-level disjuncts once.
//!
//! Because this recognizer is an ACCEPT path (a match returns `Ok` without
//! evaluating anything), the rewrite must be exactly semantics preserving. The
//! reference implementation below is the pre-rewrite predicate, verbatim; the
//! differential test drives both over an exhaustive family of packed shapes and
//! near-misses.

use super::*;

/// The pre-rewrite predicate, verbatim, as the differential oracle.
fn reference_is_packed_clausification_tautology(terms: &TermStore, term: TermId) -> bool {
    let TermData::App(symbol, disjuncts) = terms.get(term) else {
        return false;
    };
    if symbol.name() != "or" || disjuncts.len() < 2 {
        return false;
    }
    if disjuncts
        .iter()
        .any(|&disjunct| terms.sort(disjunct) != &Sort::Bool)
    {
        return false;
    }
    for &negated in disjuncts {
        let TermData::Not(inner) = terms.get(negated) else {
            continue;
        };
        if terms.sort(*inner) != &Sort::Bool {
            continue;
        }
        if disjuncts.contains(inner) {
            return true;
        }
        let TermData::App(join_symbol, members) = terms.get(*inner) else {
            continue;
        };
        if members
            .iter()
            .any(|&member| terms.sort(member) != &Sort::Bool)
        {
            continue;
        }
        match join_symbol.name() {
            "and"
                if disjuncts
                    .iter()
                    .any(|other| *other != negated && members.contains(other)) =>
            {
                return true;
            }
            "or" if !members.is_empty()
                && members.iter().all(|member| {
                    disjuncts
                        .iter()
                        .any(|other| *other != negated && other == member)
                }) =>
            {
                return true;
            }
            _ => {}
        }
    }
    for &positive in disjuncts {
        let TermData::App(join_symbol, members) = terms.get(positive) else {
            continue;
        };
        if members.is_empty() || members.iter().any(|&m| terms.sort(m) != &Sort::Bool) {
            continue;
        }
        let complement_present = |member: TermId| {
            disjuncts.iter().any(|&other| {
                other != positive
                    && (matches!(terms.get(other), TermData::Not(inner) if *inner == member)
                        || matches!(terms.get(member), TermData::Not(inner) if *inner == other))
            })
        };
        match join_symbol.name() {
            "and" if members.iter().all(|&m| complement_present(m)) => return true,
            "or" if members.iter().any(|&m| complement_present(m)) => return true,
            _ => {}
        }
    }
    false
}

fn mk_or(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("or"), args, Sort::Bool)
}

fn mk_and(terms: &mut TermStore, args: Vec<TermId>) -> TermId {
    terms.mk_app(Symbol::named("and"), args, Sort::Bool)
}

fn bool_vars(terms: &mut TermStore, count: usize) -> Vec<TermId> {
    (0..count)
        .map(|i| terms.mk_var(format!("p{i}"), Sort::Bool))
        .collect()
}

/// Every packed shape, its duals, and a spread of near-misses, in one pool.
///
/// Each entry is a candidate UNIT term. `agree_with_reference` asserts the
/// indexed recognizer and the pre-rewrite oracle return the SAME verdict for
/// every one of them, so an accept can neither be gained nor lost.
fn candidate_units(terms: &mut TermStore) -> Vec<TermId> {
    let vars = bool_vars(terms, 6);
    let (p, q, r, s, t, u) = (vars[0], vars[1], vars[2], vars[3], vars[4], vars[5]);
    let not_p = terms.mk_not_raw(p);
    let not_q = terms.mk_not_raw(q);
    let not_r = terms.mk_not_raw(r);
    let not_s = terms.mk_not_raw(s);
    let and_pq = mk_and(terms, vec![p, q]);
    let and_pqr = mk_and(terms, vec![p, q, r]);
    let or_pq = mk_or(terms, vec![p, q]);
    let or_pqr = mk_or(terms, vec![p, q, r]);
    let not_and_pq = terms.mk_not_raw(and_pq);
    let not_and_pqr = terms.mk_not_raw(and_pqr);
    let not_or_pq = terms.mk_not_raw(or_pq);
    let not_or_pqr = terms.mk_not_raw(or_pqr);
    let and_empty = mk_and(terms, Vec::new());
    let not_and_empty = terms.mk_not_raw(and_empty);
    let or_empty = mk_or(terms, Vec::new());
    let not_or_empty = terms.mk_not_raw(or_empty);
    let double_not_p = terms.mk_not_raw(not_p);

    let mut units = Vec::new();
    let mut push = |terms: &mut TermStore, args: Vec<TermId>| {
        let term = mk_or(terms, args);
        units.push(term);
    };

    // self-complement, both orders, with and without padding
    push(terms, vec![p, not_p]);
    push(terms, vec![not_p, p]);
    push(terms, vec![q, p, not_p, r]);
    push(terms, vec![p, not_q]); // near-miss: complement of a DIFFERENT variable
                                 // and_pos: (or child (not (and .. child ..)))
    push(terms, vec![p, not_and_pq]);
    push(terms, vec![q, not_and_pq]);
    push(terms, vec![r, not_and_pq]); // near-miss: r is not a conjunct
    push(terms, vec![not_and_pqr, r]);
    // or_pos: (or l1 .. ln (not (or l1 .. ln)))
    push(terms, vec![p, q, not_or_pq]);
    push(terms, vec![q, p, not_or_pq]);
    push(terms, vec![p, not_or_pq]); // near-miss: q missing
    push(terms, vec![p, q, r, not_or_pqr]);
    push(terms, vec![p, q, not_or_pqr]); // near-miss: r missing
                                         // and_neg: (or (and t1 .. tn) (not t1) .. (not tn))
    push(terms, vec![and_pq, not_p, not_q]);
    push(terms, vec![and_pq, not_q, not_p]);
    push(terms, vec![and_pq, not_p]); // near-miss: (not q) missing
    push(terms, vec![and_pqr, not_p, not_q, not_r]);
    push(terms, vec![and_pqr, not_p, not_q, not_s]); // near-miss
                                                     // or_neg: (or (or t1 .. tn) (not ti))
    push(terms, vec![or_pq, not_p]);
    push(terms, vec![or_pq, not_q]);
    push(terms, vec![or_pq, not_r]); // near-miss: r is not a member
    push(terms, vec![or_pqr, not_r]);
    // degenerate joins
    push(terms, vec![p, not_and_empty]);
    push(terms, vec![p, not_or_empty]);
    push(terms, vec![and_empty, not_p]);
    push(terms, vec![or_empty, not_p]);
    // the negated-member direction: member itself is a `(not x)` whose x is a
    // sibling disjunct
    push(terms, vec![and_pq, not_p, not_q, s]);
    push(terms, vec![or_pq, not_p, t]);
    let and_notp_notq = mk_and(terms, vec![not_p, not_q]);
    push(terms, vec![and_notp_notq, p, q]);
    let or_notp = mk_or(terms, vec![not_p, u]);
    push(terms, vec![or_notp, p]);
    // double negation and unrelated padding
    push(terms, vec![double_not_p, not_p]);
    push(terms, vec![double_not_p, p]);
    push(terms, vec![s, t, u, not_s]);
    push(terms, vec![s, t, u]); // no complement at all
    push(terms, vec![not_r, not_s]);
    // duplicated disjuncts (the index deduplicates; membership must not change)
    push(terms, vec![p, p, not_p]);
    push(terms, vec![not_and_pq, p, p]);
    push(terms, vec![and_pq, not_p, not_p, not_q]);
    units
}

#[test]
fn indexed_recognizer_agrees_with_the_prerewrite_predicate() {
    let mut terms = TermStore::new();
    let units = candidate_units(&mut terms);
    assert!(units.len() >= 30, "the pool must actually cover the shapes");
    let mut accepted = 0_usize;
    for unit in units {
        let indexed = is_packed_clausification_tautology(&terms, unit);
        let reference = reference_is_packed_clausification_tautology(&terms, unit);
        assert_eq!(
            indexed, reference,
            "indexed recognizer diverged from the pre-rewrite predicate on {unit:?}"
        );
        accepted += usize::from(indexed);
    }
    assert!(
        accepted > 0,
        "the pool must contain accepted shapes, else agreement is vacuous"
    );
}

/// A non-`or` root, a one-disjunct `or`, and a non-Bool disjunct are all
/// rejected before the index is built.
#[test]
fn non_packed_roots_are_rejected_without_indexing() {
    let mut terms = TermStore::new();
    let p = terms.mk_var("p", Sort::Bool);
    let not_p = terms.mk_not_raw(p);
    let and_root = mk_and(&mut terms, vec![p, not_p]);
    assert!(!is_packed_clausification_tautology(&terms, and_root));
    let single = mk_or(&mut terms, vec![p]);
    assert!(!is_packed_clausification_tautology(&terms, single));
    let bv = terms.mk_var("b", Sort::bitvec(4));
    let mixed = mk_or(&mut terms, vec![p, bv]);
    assert!(!is_packed_clausification_tautology(&terms, mixed));
    for root in [and_root, single, mixed] {
        assert_eq!(
            is_packed_clausification_tautology(&terms, root),
            reference_is_packed_clausification_tautology(&terms, root)
        );
    }
}

/// The point of the index: a WIDE unit is recognized without a quadratic scan.
///
/// The pre-rewrite predicate answered `or_pos` by scanning all `D` disjuncts for
/// each of the `M` members — `D * M` comparisons at `D = M = 4_000`, i.e. 16M
/// per candidate. The indexed form answers each in O(1). This asserts the
/// verdict is unchanged at a width the old scan could not be charged for
/// linearly; it deliberately does not assert a wall-clock bound.
#[test]
fn wide_packed_units_are_recognized_at_scale() {
    const WIDTH: usize = 4_000;
    let mut terms = TermStore::new();
    let vars = bool_vars(&mut terms, WIDTH);
    let disjunction = mk_or(&mut terms, vars.clone());
    let negated = terms.mk_not_raw(disjunction);
    let mut args = vars.clone();
    args.push(negated);
    let unit = mk_or(&mut terms, args);
    assert!(is_packed_clausification_tautology(&terms, unit));
    assert!(reference_is_packed_clausification_tautology(&terms, unit));

    // Same width, one member missing: still rejected.
    let mut truncated = vars.clone();
    truncated.pop();
    truncated.push(negated);
    let near_miss = mk_or(&mut terms, truncated);
    assert_eq!(
        is_packed_clausification_tautology(&terms, near_miss),
        reference_is_packed_clausification_tautology(&terms, near_miss)
    );
}
