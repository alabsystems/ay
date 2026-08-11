// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shared data and bounded scans for authored proof reconstructions.

use super::select_parts_local;
use ay_core::{ProofId, TermData, TermId, TermStore, TheoryLemmaKind};

/// One `subject -> value` rewrite licensed by an exact authored equality, used
/// by `Executor::replace_with_exact_authored_ground_substitution_refutation`.
///
/// `value` is GROUND (every leaf a constant) and `subject` is a leaf, so
/// applying the rewrite is a plain occurrence replacement and each replacement
/// is licensed by `root` — an authored assertion the rebuilt proof `assume`s.
#[derive(Clone, Copy)]
pub(super) struct GroundBinding {
    /// The declared symbol or variable being replaced.
    pub(super) subject: TermId,
    /// The ground term it is pinned to.
    pub(super) value: TermId,
    /// The exact authored equality licensing the replacement.
    pub(super) root: TermId,
}

/// A unit clause `(cl literal)` derived inside a candidate proof, together with
/// the EXACT literal term that clause contains.
///
/// Callers resolve against the RETURNED term rather than one they intern
/// themselves: an authored premise may carry either orientation (`(= i j)` vs
/// `(= j i)`) and those are distinct `TermId`s that would not cancel.
#[derive(Debug, Clone, Copy)]
pub(super) struct DerivedUnit {
    /// The step proving the unit clause.
    pub(super) step: ProofId,
    /// The single literal that step's clause contains.
    pub(super) literal: TermId,
}

/// How one length fact in
/// `Executor::replace_with_exact_authored_string_length_arith_refutation`
/// becomes a unit clause.
#[derive(Clone, Copy)]
pub(super) enum StringLengthFactProvenance {
    /// An exact authored root; emitted as an `assume`.
    Authored,
    /// A universally-valid `str.len` theorem; emitted as a unit
    /// `StringLengthLemma`.
    Tautology,
    /// A consequence of an authored `root`, licensed by the length theorem
    /// `or_term` = `(or (not root) fact)`; emitted as that lemma, clausified by
    /// `AletheRule::Or`, then resolved against `root`.
    FromRoot { root: TermId, or_term: TermId },
    /// A consequence of an authored `root`, licensed by the FLAT two-literal
    /// theory lemma `(cl (not root) fact)` of `kind`; emitted as that lemma and
    /// resolved directly against `root`, with no `or` clausification.
    FromRootClause { root: TermId, kind: TheoryLemmaKind },
}

/// String-theory subterms of the authored scope that the length-arithmetic
/// reconstruction can build certified facts from.
#[derive(Default)]
pub(super) struct StringRelevantSubterms {
    /// `str.++` applications of arity >= 2.
    pub(super) concats: Vec<TermId>,
    /// String-constant subterms.
    pub(super) string_constants: Vec<TermId>,
    /// Every string-sorted subterm (candidate `str.len` subject).
    pub(super) length_subjects: Vec<TermId>,
    /// `(predicate, contained, container)` for containment predicates.
    pub(super) containments: Vec<(TermId, TermId, TermId)>,
    /// `(equality, left, right)` for String-sorted equalities.
    pub(super) string_equalities: Vec<(TermId, TermId, TermId)>,
}

/// The OTHER side of an equality's argument pair, when `side` is one of them.
pub(super) fn pair_other_side_local(lhs: TermId, rhs: TermId, side: TermId) -> Option<TermId> {
    if lhs == side {
        Some(rhs)
    } else if rhs == side {
        Some(lhs)
    } else {
        None
    }
}

/// Every `select` application reachable from `roots`, in a deterministic order
/// and under a fixed traversal budget.
pub(super) fn collect_select_terms_local(
    terms: &TermStore,
    roots: &[TermId],
    limit: usize,
) -> Vec<TermId> {
    /// Traversal budget. A problem whose authored term DAG is larger than this
    /// simply contributes fewer candidates, leaving the verdict as it is.
    const MAX_VISITED_NODES: usize = 4096;

    let mut found: Vec<TermId> = Vec::new();
    let mut visited: ay_core::kani_compat::DetHashSet<TermId> =
        ay_core::kani_compat::DetHashSet::default();
    let mut pending: Vec<TermId> = roots.iter().rev().copied().collect();
    while let Some(term) = pending.pop() {
        if visited.len() >= MAX_VISITED_NODES {
            break;
        }
        if !visited.insert(term) {
            continue;
        }
        if select_parts_local(terms, term).is_some() {
            if found.len() >= limit {
                break;
            }
            found.push(term);
        }
        match terms.get(term) {
            TermData::App(_, args) => pending.extend(args.iter().rev().copied()),
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(condition, then_branch, else_branch) => {
                pending.extend([*else_branch, *then_branch, *condition]);
            }
            _ => {}
        }
    }
    found
}
