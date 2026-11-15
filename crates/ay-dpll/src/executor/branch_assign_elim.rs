// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rewrite two-branch assignment blocks into unconditional `ite` definitions.
//!
//! Path-sensitive encodings (loop unrollings, VCGen output) state a
//! conditional update as a disjunction of two conjunctions:
//!
//! ```text
//! (or (and G  (= p1 (+ p0 1)) (= a1 (store a0 p0 u0)))
//!     (and Gc (= p1 p0)       (= a1 a0)))
//! ```
//!
//! where `Gc` is the complement of `G`. Left as a disjunction, the array
//! equalities become Boolean atoms the DPLL search decides blind; on
//! multi-step chains the search thrashes (measured: a two-step pointer
//! shape burns 220k+ decisions without a verdict, while the definitional
//! form below decides `sat` in ~1.2k). When both branches assign the SAME
//! set of variables by equalities and the guards are complementary, the
//! block is logically equivalent to one unconditional definition per
//! variable:
//!
//! ```text
//! (= p1 (ite G (+ p0 1) p0))
//! (= a1 (ite G (store a0 p0 u0) a0))
//! ```
//!
//! The equivalence is pure propositional/`ite` rewriting: under `G` the
//! first disjunct is exactly the first column of equalities, under `Gc`
//! the second; the guards are exhaustive, so both directions hold for
//! arbitrary right-hand sides. The rewrite fires only when at least one
//! assigned variable is Array-sorted (the measured starvation family);
//! purely arithmetic blocks are left to the existing lanes.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

/// The conjuncts of one branch: the arguments of a top-level `and`, or the
/// branch itself when it is a single formula.
fn branch_conjuncts(terms: &TermStore, branch: TermId) -> Vec<TermId> {
    if let TermData::App(sym, args) = terms.get(branch) {
        if sym.name() == "and" {
            return args.clone();
        }
    }
    vec![branch]
}

/// A comparison atom canonicalized to `x OP y` form. The elaborator
/// already normalizes some spellings (e.g. `(>= a b)` arrives as
/// `(<= b a)`), so complement detection must see through operand order.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum Comparison {
    Lt(TermId, TermId),
    Le(TermId, TermId),
    Eq(TermId, TermId),
    Ne(TermId, TermId),
}

fn canonical_comparison(terms: &TermStore, guard: TermId) -> Option<Comparison> {
    let TermData::App(sym, args) = terms.get(guard) else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (x, y) = (args[0], args[1]);
    match sym.name() {
        "<" => Some(Comparison::Lt(x, y)),
        "<=" => Some(Comparison::Le(x, y)),
        ">" => Some(Comparison::Lt(y, x)),
        ">=" => Some(Comparison::Le(y, x)),
        "=" => Some(Comparison::Eq(x, y)),
        "distinct" => Some(Comparison::Ne(x, y)),
        _ => None,
    }
}

/// True when `g2` is the complement of `g1`: a syntactic `not`, or a
/// complementary comparison pair (`¬(x<y)` is `y<=x`, `¬(x<=y)` is
/// `y<x`, `¬(x=y)` is `x≠y`).
fn guards_complementary(terms: &TermStore, g1: TermId, g2: TermId) -> bool {
    if let TermData::Not(inner) = terms.get(g2) {
        if *inner == g1 {
            return true;
        }
    }
    if let TermData::Not(inner) = terms.get(g1) {
        if *inner == g2 {
            return true;
        }
    }
    let (Some(c1), Some(c2)) = (
        canonical_comparison(terms, g1),
        canonical_comparison(terms, g2),
    ) else {
        return false;
    };
    match (c1, c2) {
        (Comparison::Lt(x, y), Comparison::Le(y2, x2))
        | (Comparison::Le(x, y), Comparison::Lt(y2, x2)) => x == x2 && y == y2,
        (Comparison::Eq(x, y), Comparison::Ne(x2, y2))
        | (Comparison::Ne(x, y), Comparison::Eq(x2, y2)) => {
            (x == x2 && y == y2) || (x == y2 && y == x2)
        }
        _ => false,
    }
}

/// Parse an equality conjunct as an unordered pair with at least one
/// variable side. The sides are NOT yet oriented: elaboration
/// canonically orders equality operands, so an authored `(= p1 p0)`
/// assignment arrives as `(= p0 p1)` and the assigned variable cannot
/// be read off the side when both sides are variables.
fn parse_equality_pair(terms: &TermStore, conjunct: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(sym, args) = terms.get(conjunct) else {
        return None;
    };
    if sym.name() != "=" || args.len() != 2 {
        return None;
    }
    let (lhs, rhs) = (args[0], args[1]);
    if matches!(terms.get(lhs), TermData::Var(..)) || matches!(terms.get(rhs), TermData::Var(..)) {
        Some((lhs, rhs))
    } else {
        None
    }
}

/// A branch's non-guard conjuncts as equality pairs, or `None` unless
/// every one parses.
fn branch_pairs(
    terms: &TermStore,
    conjuncts: &[TermId],
    guard_index: usize,
) -> Option<Vec<(TermId, TermId)>> {
    let mut pairs = Vec::new();
    for (index, &conjunct) in conjuncts.iter().enumerate() {
        if index == guard_index {
            continue;
        }
        pairs.push(parse_equality_pair(terms, conjunct)?);
    }
    if pairs.is_empty() || pairs.len() > 10 {
        return None;
    }
    Some(pairs)
}

fn is_var(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Var(..))
}

/// Depth-first orientation of `pairs`: choose one variable side per pair
/// as the assigned variable, all distinct. With `target`, the chosen
/// variables must cover exactly that set. Complete orientations are
/// appended to `out` (capped), each as `(var, rhs)` pairs.
fn orient_rec(
    terms: &TermStore,
    pairs: &[(TermId, TermId)],
    index: usize,
    target: Option<&[TermId]>,
    chosen: &mut Vec<(TermId, TermId)>,
    out: &mut Vec<Vec<(TermId, TermId)>>,
) {
    if out.len() >= 64 {
        return;
    }
    if index == pairs.len() {
        if let Some(target) = target {
            if chosen.len() != target.len()
                || !target.iter().all(|v| chosen.iter().any(|(c, _)| c == v))
            {
                return;
            }
        }
        out.push(chosen.clone());
        return;
    }
    let (lhs, rhs) = pairs[index];
    for (var, other) in [(lhs, rhs), (rhs, lhs)] {
        if !is_var(terms, var) {
            continue;
        }
        if chosen.iter().any(|(seen, _)| *seen == var) {
            continue;
        }
        if let Some(target) = target {
            if !target.contains(&var) {
                continue;
            }
        }
        chosen.push((var, other));
        orient_rec(terms, pairs, index + 1, target, chosen, out);
        chosen.pop();
        if lhs == rhs {
            break;
        }
    }
}

/// Orient both branches over one shared assigned-variable set. An
/// orientation is a labeling only — `(= x y)` means the same whichever
/// side is labeled — so any consistent choice preserves the equivalence
/// (under the guard, the definitions collapse to the branch's own
/// equality set). Distinctness within a branch and one shared set
/// across branches are the real requirements.
fn orient_branches(
    terms: &TermStore,
    pairs1: &[(TermId, TermId)],
    pairs2: &[(TermId, TermId)],
) -> Option<(Vec<(TermId, TermId)>, Vec<(TermId, TermId)>)> {
    if pairs1.len() != pairs2.len() {
        return None;
    }
    let mut candidates1 = Vec::new();
    orient_rec(terms, pairs1, 0, None, &mut Vec::new(), &mut candidates1);
    for assign1 in candidates1 {
        let target: Vec<TermId> = assign1.iter().map(|(var, _)| *var).collect();
        let mut candidates2 = Vec::new();
        orient_rec(
            terms,
            pairs2,
            0,
            Some(&target),
            &mut Vec::new(),
            &mut candidates2,
        );
        if let Some(assign2) = candidates2.into_iter().next() {
            return Some((assign1, assign2));
        }
    }
    None
}

/// If `assertion` is a two-branch assignment block (see the module docs),
/// return the equivalent unconditional `ite` definitions, one per assigned
/// variable. The caller substitutes these for the original assertion.
pub(crate) fn rewrite_branch_assignment_block(
    terms: &mut TermStore,
    assertion: TermId,
) -> Option<Vec<TermId>> {
    let TermData::App(sym, args) = terms.get(assertion).clone() else {
        return None;
    };
    if sym.name() != "or" || args.len() != 2 {
        return None;
    }

    let conjuncts1 = branch_conjuncts(terms, args[0]);
    let conjuncts2 = branch_conjuncts(terms, args[1]);

    for (i, &g1) in conjuncts1.iter().enumerate() {
        for (j, &g2) in conjuncts2.iter().enumerate() {
            if !guards_complementary(terms, g1, g2) {
                continue;
            }
            let Some(pairs1) = branch_pairs(terms, &conjuncts1, i) else {
                continue;
            };
            let Some(pairs2) = branch_pairs(terms, &conjuncts2, j) else {
                continue;
            };
            let Some((assign1, assign2)) = orient_branches(terms, &pairs1, &pairs2) else {
                continue;
            };
            let rhs2: HashMap<TermId, TermId> = assign2.iter().copied().collect();
            let assigns_array = assign1
                .iter()
                .any(|(var, _)| matches!(terms.sort(*var), Sort::Array(_)));
            if !assigns_array {
                return None;
            }
            let mut definitions = Vec::with_capacity(assign1.len());
            for (var, rhs1) in assign1 {
                let ite = terms.mk_ite(g1, rhs1, rhs2[&var]);
                definitions.push(terms.mk_eq(var, ite));
            }
            return Some(definitions);
        }
    }
    None
}
