// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shape recognition for one bound of a FRESH-symbol definitional extension.
//!
//! A preprocessing pass may introduce a symbol the problem never mentions and
//! define it by a term over the problem's own symbols. AY's `EqDiffVar` pass
//! does exactly this: it mints a fresh `d` and asserts the pair
//! `(<= d lin)` / `(>= d lin)` — which canonicalizes to `(<= d lin)` and
//! `(<= lin d)` — so that multi-variable equality atoms fold to var-CONST
//! atoms over `d`.
//!
//! Those two assertions are NOT tautologies, so no theory-lemma kind can carry
//! them, and they are not authored, so presenting them as `assume` would claim
//! authority the problem never granted. They are instead sound because `d` is
//! FRESH, which is a property OF THE PROBLEM and therefore checkable — see
//! `ay_proof`'s `FreshDefRegistry` for the whole-proof conditions and the
//! soundness proof.
//!
//! This module owns only the LOCAL half: given one step, decide whether it has
//! the shape `(cl (<= d lin))` or `(cl (<= lin d))` with `:args (d)`, and say
//! which side `d` is on. It deliberately knows nothing about freshness — a
//! recognizer that guessed freshness from a name prefix would be exactly the
//! forgery surface the registry exists to close.

use crate::term::TermData;
use crate::{Sort, TermId, TermStore};

/// Which side of the `<=` the defined symbol sits on.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum FreshDefBoundSide {
    /// `(<= d lin)` — `lin` bounds `d` from above.
    Upper,
    /// `(<= lin d)` — `lin` bounds `d` from below.
    Lower,
}

/// A well-formed fresh-definition bound step, decomposed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FreshDefBoundShape {
    /// The defined symbol: an atomic [`TermData::Var`].
    pub definiendum: TermId,
    /// The defining term.
    pub definiens: TermId,
    /// Which side `definiendum` occupies.
    pub side: FreshDefBoundSide,
    /// The bound atom itself (the step's single clause literal).
    pub atom: TermId,
}

/// Why a candidate step is not a fresh-definition bound.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FreshDefBoundShapeError {
    /// The step carries premises; a definition is derived from nothing.
    HasPremises,
    /// The step does not carry exactly one `:args` term.
    ArgArity(usize),
    /// The clause is not exactly one literal.
    ClauseArity(usize),
    /// The literal is not a binary `<=` application.
    NotBinaryLe,
    /// The `:args` term is not an atomic variable.
    DefiniendumNotVariable,
    /// Neither `<=` operand is the declared definiendum, or both are.
    DefiniendumNotAnOperand,
    /// The definiendum and the definiens have different sorts.
    SortMismatch(Sort, Sort),
}

impl std::fmt::Display for FreshDefBoundShapeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::HasPremises => write!(f, "a fresh-definition bound must have no premises"),
            Self::ArgArity(n) => write!(
                f,
                "a fresh-definition bound must name its defined symbol in exactly one `:args` \
                 term, got {n}"
            ),
            Self::ClauseArity(n) => write!(
                f,
                "a fresh-definition bound must conclude exactly one literal, got {n}"
            ),
            Self::NotBinaryLe => write!(
                f,
                "a fresh-definition bound's literal must be a binary `<=` application"
            ),
            Self::DefiniendumNotVariable => write!(
                f,
                "a fresh-definition bound's defined symbol must be an atomic variable"
            ),
            Self::DefiniendumNotAnOperand => write!(
                f,
                "a fresh-definition bound must have the defined symbol as EXACTLY one of the two \
                 `<=` operands"
            ),
            Self::SortMismatch(d, l) => write!(
                f,
                "a fresh-definition bound must define a symbol at the definiens' own sort, got \
                 {d:?} := {l:?}"
            ),
        }
    }
}

/// Decompose one candidate `fresh_def_bound` step.
///
/// # Errors
///
/// Returns the first structural condition the step fails. Every condition is
/// local: freshness, uniqueness of the definiens, and the absence of introduced
/// symbols inside a definiens are whole-proof properties and are NOT decided
/// here.
pub fn recognize_fresh_def_bound(
    terms: &TermStore,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<FreshDefBoundShape, FreshDefBoundShapeError> {
    if premise_count != 0 {
        return Err(FreshDefBoundShapeError::HasPremises);
    }
    let [definiendum] = args else {
        return Err(FreshDefBoundShapeError::ArgArity(args.len()));
    };
    let [atom] = clause else {
        return Err(FreshDefBoundShapeError::ClauseArity(clause.len()));
    };
    if !matches!(terms.get(*definiendum), TermData::Var(_, _)) {
        return Err(FreshDefBoundShapeError::DefiniendumNotVariable);
    }
    let TermData::App(sym, operands) = terms.get(*atom) else {
        return Err(FreshDefBoundShapeError::NotBinaryLe);
    };
    if sym.name() != "<=" || operands.len() != 2 {
        return Err(FreshDefBoundShapeError::NotBinaryLe);
    }
    let (lhs, rhs) = (operands[0], operands[1]);
    // EXACTLY one operand may be the definiendum. `(<= d d)` cannot describe a
    // definition (and `mk_le` folds it to `true` anyway), and a step whose
    // declared symbol appears on neither side declares nothing.
    let side = match (lhs == *definiendum, rhs == *definiendum) {
        (true, false) => FreshDefBoundSide::Upper,
        (false, true) => FreshDefBoundSide::Lower,
        _ => return Err(FreshDefBoundShapeError::DefiniendumNotAnOperand),
    };
    let definiens = if side == FreshDefBoundSide::Upper {
        rhs
    } else {
        lhs
    };
    // SORT is load-bearing, not hygiene: the whole soundness argument is
    // "assign `d` the value of `lin`", and that assignment must exist. An
    // `Int` symbol bounded by a `Real` term instead forces `lin` to be
    // integral — a genuine constraint on the problem's own variables.
    let definiendum_sort = terms.sort(*definiendum).clone();
    let definiens_sort = terms.sort(definiens).clone();
    if definiendum_sort != definiens_sort {
        return Err(FreshDefBoundShapeError::SortMismatch(
            definiendum_sort,
            definiens_sort,
        ));
    }
    Ok(FreshDefBoundShape {
        definiendum: *definiendum,
        definiens,
        side,
        atom: *atom,
    })
}
