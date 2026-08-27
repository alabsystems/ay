// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What COUNTS as a fresh-definition candidate, and how a candidate atom may be
//! read as a definition.
//!
//! Split out of [`super`] so that "which `trust` leaves are candidates" and
//! "which candidates are promoted" are separately readable. The admission test
//! itself, its two stages and its soundness argument live with the promotion in
//! the parent module.

use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep, TermId};

use crate::executor::Executor;

/// Bound on how many definitions one proof may promote. Well past the
/// `EqDiffVar` pass's own `MAX_DIFF_VARS` (1024) doubled, so it never binds in
/// practice; it exists so a pathological proof cannot make this lane's
/// traversals unbounded.
const MAX_PROMOTED_BOUNDS: usize = 4096;

/// Which fresh-definition rule a candidate would be promoted to.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub(super) enum DefKind {
    /// `(<= d lin)` / `(<= lin d)` → [`AletheRule::FreshDefBound`].
    Bound,
    /// `(= d expr)` → [`AletheRule::FreshDefEq`].
    Eq,
}

impl DefKind {
    pub(super) fn rule(self) -> AletheRule {
        match self {
            Self::Bound => AletheRule::FreshDefBound,
            Self::Eq => AletheRule::FreshDefEq,
        }
    }
}

/// One way of reading a candidate atom as a definition.
///
/// A `<=` atom admits exactly one; `(= v1 v2)` over two variables admits two,
/// and stage A picks the eligible one. Keeping both here rather than guessing
/// at collection time is what lets a rewritten assertion like
/// `(= TRUE (bool p))` be classified by the PROBLEM rather than by position.
pub(super) struct Orientation {
    pub(super) definiendum: TermId,
    pub(super) definiens: TermId,
    pub(super) name: String,
}

/// One candidate `trust` step, with every reading it admits.
pub(super) struct Candidate {
    pub(super) step: usize,
    pub(super) kind: DefKind,
    pub(super) orientations: Vec<Orientation>,
}

impl Executor {
    /// Premiseless unit `trust` steps whose clause is a definitional bound or
    /// equality.
    pub(super) fn collect_fresh_def_candidates(&self, proof: &Proof) -> Vec<Candidate> {
        let mut candidates = Vec::new();
        for (index, step) in proof.steps.iter().enumerate() {
            if candidates.len() >= MAX_PROMOTED_BOUNDS {
                break;
            }
            let ProofStep::Step {
                rule: AletheRule::Trust,
                clause,
                premises,
                args,
            } = step
            else {
                continue;
            };
            if !premises.is_empty() || !args.is_empty() {
                continue;
            }
            let [atom] = clause.as_slice() else {
                continue;
            };
            let (kind, orientations) = if let Some(reading) = self.fresh_def_bound_operands(*atom) {
                (DefKind::Bound, self.orientations(&[reading]))
            } else if let Some(readings) = self.fresh_def_eq_operands(*atom) {
                (DefKind::Eq, self.orientations(&readings))
            } else {
                continue;
            };
            if orientations.is_empty() {
                continue;
            }
            candidates.push(Candidate {
                step: index,
                kind,
                orientations,
            });
        }
        candidates
    }

    /// Name each `(definiendum, definiens)` reading, dropping any whose
    /// definiendum is not an atomic variable.
    fn orientations(&self, readings: &[(TermId, TermId)]) -> Vec<Orientation> {
        readings
            .iter()
            .filter_map(|&(definiendum, definiens)| {
                let TermData::Var(name, _) = self.ctx.terms.get(definiendum) else {
                    return None;
                };
                Some(Orientation {
                    definiendum,
                    definiens,
                    name: name.clone(),
                })
            })
            .collect()
    }

    /// Split `(= a b)` into the one or two `(definiendum, definiens)` readings
    /// it admits.
    ///
    /// Unlike `<=`, `=` is SYMMETRIC and `mk_eq` canonicalises its operands by
    /// `TermId`, so the term itself says nothing about which side is defined.
    /// Both sides are therefore offered and stage A decides, using the PROBLEM
    /// rather than a positional convention; `orientations` then drops whichever
    /// side is not an atomic variable.
    ///
    /// Sort equality is checked here and again by the checker's recognizer: it
    /// is what guarantees `d := expr` is an assignment `d` can take at all.
    fn fresh_def_eq_operands(&self, atom: TermId) -> Option<[(TermId, TermId); 2]> {
        let TermData::App(sym, operands) = self.ctx.terms.get(atom) else {
            return None;
        };
        if sym.name() != "=" || operands.len() != 2 {
            return None;
        }
        let (lhs, rhs) = (operands[0], operands[1]);
        if self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
            return None;
        }
        Some([(lhs, rhs), (rhs, lhs)])
    }

    /// Split `(<= a b)` into `(definiendum, definiens)` when EXACTLY one side is
    /// an atomic variable at the other side's sort.
    ///
    /// Sort equality is checked here and again by the checker's recognizer: it
    /// is what guarantees `d := lin` is an assignment `d` can take at all. An
    /// `Int` symbol pinned between two `Real` bounds would instead force that
    /// term to be integral, which constrains the problem's own variables.
    pub(super) fn fresh_def_bound_operands(&self, atom: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(sym, operands) = self.ctx.terms.get(atom) else {
            return None;
        };
        if sym.name() != "<=" || operands.len() != 2 {
            return None;
        }
        let (lhs, rhs) = (operands[0], operands[1]);
        let lhs_var = matches!(self.ctx.terms.get(lhs), TermData::Var(_, _));
        let rhs_var = matches!(self.ctx.terms.get(rhs), TermData::Var(_, _));
        let (definiendum, definiens) = match (lhs_var, rhs_var) {
            (true, false) => (lhs, rhs),
            (false, true) => (rhs, lhs),
            _ => return None,
        };
        (self.ctx.terms.sort(definiendum) == self.ctx.terms.sort(definiens))
            .then_some((definiendum, definiens))
    }
}
