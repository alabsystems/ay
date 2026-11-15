// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Elimination of array equalities that define an otherwise unused array.
//!
//! # The shape
//!
//! The frontend expands a constant of a single-constructor datatype into one
//! fresh constant per field, so a slice `s = (Slice_mk ptr len data)` whose
//! `data` field is an array becomes `(= data s!fld_data)`. A field that
//! nothing reads leaves exactly that equality behind: `s!fld_data` occurs in
//! one atom and nowhere else. The array-read elimination of this lane
//! ([`super::plan`]) then refuses the whole window, because an array occurs
//! outside `select`, and an FP query that only ever reads the array at
//! constant indices answers `unknown (unsupported)`.
//!
//! # The rewrite
//!
//! Let `X` be an array-sorted declared constant that occurs exactly once in
//! the window, as one side of `(= X t)` (either order), and let every
//! occurrence of that atom have positive polarity: it is reached from an
//! assertion through `and`, `or`, the consequent of `=>` and the branches of a
//! Boolean `ite` only, never under `not`, an antecedent, an `ite` condition, a
//! Boolean `=`/`xor`, or any other operator. The atom is replaced by `true`.
//!
//! Removing an atom removes its edges into `X` and `t`, so a constant of `t`
//! can drop to one occurrence and qualify in turn. Each round keeps the
//! occurrence counts exact as it removes atoms (a term left with no parent
//! releases its own children), so a definition chain `(= X Y)`, `(= Y t)`, or
//! an unread memory SSA chain `(= m2 (store m1 i v))`, `(= m1 (store m0 j w))`,
//! unwinds within one round however long it is. Polarity is not recomputed
//! inside a round: a removal only drops paths through the removed array terms,
//! and every Boolean term below those already carries both polarities, so no
//! atom qualifies on a stale bit. A later round's fresh scan picks up an atom a
//! removal left purely positive.
//!
//! # Soundness: an equivalence for satisfiability
//!
//! Let `φ` be the window and `φ'` the rewrite.
//!
//! * **`φ'` is a weakening of `φ`.** The atom occurs only positively, so
//!   replacing it by `true` can only enlarge the set of models. An `unsat`
//!   verdict on `φ'` is therefore an `unsat` verdict on `φ`.
//! * **Every model of `φ'` extends to a model of `φ`.** Given `M'` with
//!   `M' ⊨ φ'`, set `M = M'[X := M'(t)]`. `X` occurs in no other term and not
//!   in `t` (it occurs once in total), so every other subterm of `φ` has the
//!   same value under `M` and `M'`, and the atom now evaluates to `true`,
//!   which is the value `φ'` already gave it. Hence `M ⊨ φ`.
//!
//! Rounds compose: each round is such an equivalence over the window the
//! previous round produced. An earlier round's `t` may mention a constant a
//! later round eliminates (round one drops `(= X Y)`, round two `(= Y t)`),
//! never the other way round, so the definitions are reconstructed in reverse
//! elimination order.
//!
//! The caller owns the model half of the argument: it must give every
//! eliminated `X` the value of its `t` before any model is published, and fail
//! closed when it cannot. No verdict is ever inferred from the rewrite alone.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{Sort, TermId, TermStore};

use super::rewrite::rewrite;

/// Rounds of elimination per window. A round removes every atom that
/// qualifies or comes to qualify through occurrence counts, so only an atom
/// whose polarity a removal changes needs another; past the cap the remaining
/// equalities stay in the window and the lane behaves as before.
const MAX_ROUNDS: usize = 64;

const POSITIVE: u8 = 1;
const NEGATIVE: u8 = 2;
const BOTH: u8 = POSITIVE | NEGATIVE;

/// The rewritten window and the definitions it dropped.
#[derive(Debug, Clone)]
pub(in crate::executor::theories::fp) struct UnreadArrayElimination {
    /// The window with every eliminated atom replaced by `true`.
    pub(in crate::executor::theories::fp) assertions: Vec<TermId>,
    /// `(X, t)` for every eliminated `(= X t)`, in elimination order.
    pub(in crate::executor::theories::fp) definitions: Vec<(TermId, TermId)>,
}

/// Occurrence counts and polarities over one window.
struct WindowScan {
    /// Number of parent edges into each reachable term.
    occurrences: HashMap<TermId, u32>,
    /// Polarity bits of each Boolean term reachable through connectives.
    polarity: HashMap<TermId, u8>,
}

fn flip(polarity: u8) -> u8 {
    ((polarity & POSITIVE) << 1) | ((polarity & NEGATIVE) >> 1)
}

/// Children of `term`, or `None` for a shape this pass does not walk
/// (quantifiers, `let`, an unclassified variant). `let` abstains even with no
/// bindings: `rewrite` treats it as a leaf, so an atom below it could be
/// counted here but never replaced there.
fn children(terms: &TermStore, term: TermId) -> Option<Vec<TermId>> {
    Some(match terms.get(term) {
        TermData::App(_, args) => args.clone(),
        TermData::Not(inner) => vec![*inner],
        TermData::Ite(c, t, e) => vec![*c, *t, *e],
        TermData::Const(_) | TermData::Var(_, _) => Vec::new(),
        _ => return None,
    })
}

fn scan(terms: &TermStore, roots: &[TermId]) -> Option<WindowScan> {
    let mut occurrences: HashMap<TermId, u32> = HashMap::default();
    let mut visited: HashSet<TermId> = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !visited.insert(term) {
            continue;
        }
        for child in children(terms, term)? {
            *occurrences.entry(child).or_default() += 1;
            stack.push(child);
        }
    }

    let mut polarity: HashMap<TermId, u8> = HashMap::default();
    let mut work: Vec<(TermId, u8)> = roots.iter().map(|&root| (root, POSITIVE)).collect();
    while let Some((term, pol)) = work.pop() {
        let seen = polarity.entry(term).or_default();
        if *seen & pol == pol {
            continue;
        }
        *seen |= pol;
        match terms.get(term) {
            TermData::Not(inner) => work.push((*inner, flip(pol))),
            TermData::App(sym, args) => match sym.name() {
                "and" | "or" => work.extend(args.iter().map(|&a| (a, pol))),
                "=>" if !args.is_empty() => {
                    let (last, antecedents) = args.split_last()?;
                    work.extend(antecedents.iter().map(|&a| (a, flip(pol))));
                    work.push((*last, pol));
                }
                _ => work.extend(args.iter().map(|&a| (a, BOTH))),
            },
            TermData::Ite(c, t, e) => {
                let branch = if matches!(terms.sort(term), Sort::Bool) {
                    pol
                } else {
                    BOTH
                };
                work.extend([(*c, BOTH), (*t, branch), (*e, branch)]);
            }
            _ => {}
        }
    }
    Some(WindowScan {
        occurrences,
        polarity,
    })
}

/// The array sorts the caller can give a model value: a bitvector index and a
/// bitvector element, the sorts the read elimination itself publishes.
fn has_reconstructible_sort(terms: &TermStore, term: TermId) -> bool {
    match terms.sort(term) {
        Sort::Array(arr) => {
            matches!(arr.index_sort, Sort::BitVec(_)) && matches!(arr.element_sort, Sort::BitVec(_))
        }
        _ => false,
    }
}

/// `(X, t)` when `atom` is `(= X t)` or `(= t X)` with `X` eliminable.
fn eliminable_side(terms: &TermStore, scan: &WindowScan, atom: TermId) -> Option<(TermId, TermId)> {
    let TermData::App(sym, args) = terms.get(atom) else {
        return None;
    };
    if sym.name() != "=" || args.len() != 2 || args[0] == args[1] {
        return None;
    }
    let qualifies = |side: TermId| {
        is_definable_constant(terms, side) && scan.occurrences.get(&side) == Some(&1)
    };
    if qualifies(args[0]) {
        Some((args[0], args[1]))
    } else if qualifies(args[1]) {
        Some((args[1], args[0]))
    } else {
        None
    }
}

/// A declared constant of a sort the caller can reconstruct.
fn is_definable_constant(terms: &TermStore, side: TermId) -> bool {
    matches!(terms.get(side), TermData::Var(_, _)) && has_reconstructible_sort(terms, side)
}

/// The constants `atom` could define, were each to occur once: the definable
/// sides of a two-sided `=`.
fn definable_sides(terms: &TermStore, atom: TermId) -> Vec<TermId> {
    match terms.get(atom) {
        TermData::App(sym, args) if sym.name() == "=" && args.len() == 2 => args
            .iter()
            .copied()
            .filter(|&side| is_definable_constant(terms, side))
            .collect(),
        _ => Vec::new(),
    }
}

/// One round over `window`: every positive atom that qualifies, then every
/// one a removal makes qualify, each with its `(X, t)`, in removal order.
///
/// A removed atom's edges are released from `scan.occurrences`; a non-root
/// term left with no parent releases its own children. The counts therefore
/// stay exactly those of the window with the removed atoms replaced, so an
/// eliminated `X` (count zero) is never inside a later `t`, and the reverse
/// reconstruction order holds within the round as well as across rounds.
fn eliminate_round(
    terms: &TermStore,
    window: &[TermId],
    scan: &mut WindowScan,
) -> Vec<(TermId, (TermId, TermId))> {
    let roots: HashSet<TermId> = window.iter().copied().collect();
    let mut positive: Vec<TermId> = scan
        .polarity
        .iter()
        .filter(|&(_, &pol)| pol == POSITIVE)
        .map(|(&atom, _)| atom)
        .collect();
    positive.sort_unstable();
    let mut by_side: HashMap<TermId, Vec<TermId>> = HashMap::default();
    for &atom in &positive {
        for side in definable_sides(terms, atom) {
            by_side.entry(side).or_default().push(atom);
        }
    }
    // Pop in ascending id order; atoms a removal exposes go on top.
    let mut work: Vec<TermId> = positive.into_iter().rev().collect();
    let mut removed: HashSet<TermId> = HashSet::default();
    let mut round = Vec::new();
    while let Some(atom) = work.pop() {
        if removed.contains(&atom) {
            continue;
        }
        let Some(definition) = eliminable_side(terms, scan, atom) else {
            continue;
        };
        removed.insert(atom);
        round.push((atom, definition));
        let mut released = children(terms, atom).unwrap_or_default();
        while let Some(child) = released.pop() {
            let left = scan.occurrences.get(&child).copied().unwrap_or(0);
            let left = left.saturating_sub(1);
            scan.occurrences.insert(child, left);
            if left == 0 && !roots.contains(&child) {
                released.extend(children(terms, child).unwrap_or_default());
            } else if left == 1 {
                if let Some(atoms) = by_side.get(&child) {
                    work.extend(atoms.iter().copied());
                }
            }
        }
    }
    round
}

/// Run the rewrite, or return `None` when no atom qualifies.
pub(in crate::executor::theories::fp) fn eliminate_unread_array_equalities(
    terms: &mut TermStore,
    assertions: &[TermId],
) -> Option<UnreadArrayElimination> {
    let mut window = assertions.to_vec();
    let mut definitions = Vec::new();
    let truth = terms.true_term();
    for _ in 0..MAX_ROUNDS {
        let mut scan = scan(terms, &window)?;
        let round = eliminate_round(terms, &window, &mut scan);
        if round.is_empty() {
            break;
        }
        let mut subst: HashMap<TermId, TermId> = HashMap::default();
        for (atom, definition) in round {
            definitions.push(definition);
            subst.insert(atom, truth);
        }
        let mut memo: HashMap<TermId, TermId> = HashMap::default();
        window = window
            .iter()
            .map(|&root| rewrite(terms, root, &subst, &mut memo))
            .collect();
    }
    if definitions.is_empty() {
        return None;
    }
    Some(UnreadArrayElimination {
        assertions: window,
        definitions,
    })
}

#[cfg(test)]
mod tests;
