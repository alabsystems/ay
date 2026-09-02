// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Shape recognition for a FRESH-symbol definitional EQUALITY.
//!
//! Several AY preprocessing passes introduce a symbol the problem never
//! mentions and define it OUTRIGHT by a term over the problem's own symbols.
//! `purify_bool_args` (`ay-dpll`) is the measured producer on this corpus: to
//! restore congruence over `f(b)` for a COMPOUND Boolean argument `b`, it mints
//! a fresh Boolean variable `p` and asserts `(= p b)`. Its own module docs
//! state the property this module exists to CHECK rather than trust — "the
//! rewrite is equisatisfiable (`p` is fresh and fully defined by `p = b`)".
//!
//! Such an assertion is not a tautology, so no theory-lemma kind can carry it,
//! and it is not authored, so presenting it as `assume` would claim authority
//! the problem never granted. It is instead sound because `p` is FRESH, which
//! is a property OF THE PROBLEM and therefore checkable — see `ay_proof`'s
//! `FreshDefRegistry` for the whole-proof conditions and the soundness proof.
//!
//! # Why this is a SIBLING of `fresh_def_bound` rather than a widening of it
//!
//! The two rules share a registry and a soundness argument but not a shape:
//!
//! * `<=` is arithmetic; `=` is not. The measured population here is `Bool`,
//!   and the corpus also carries `Array` and `String` equalities. A recognizer
//!   keyed on `"<="` cannot see them.
//! * The wire name would become a lie. `fresh_def_bound` says "one bound of a
//!   definition"; this step asserts the definition itself.
//! * `mk_eq` CANONICALISES its operands by `TermId` order, so `(= d e)` and
//!   `(= e d)` are the same term. There is no `Upper`/`Lower` distinction to
//!   report, and the `:args` term is the ONLY thing that says which operand is
//!   the definiendum — which makes the `:args` gate load-bearing here in a way
//!   it is not for a bound.
//!
//! This module owns only the LOCAL half: given one step, decide whether it has
//! the shape `(cl (= d expr))` with `:args (d)`. It deliberately knows nothing
//! about freshness — a recognizer that guessed freshness from a name prefix
//! would be exactly the forgery surface the registry exists to close.

use crate::term::TermData;
use crate::{Sort, TermId, TermStore};

/// A well-formed fresh-definition equality step, decomposed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct FreshDefEqShape {
    /// The defined symbol: an atomic [`TermData::Var`].
    pub definiendum: TermId,
    /// The defining term.
    pub definiens: TermId,
    /// The equality atom itself (the step's single clause literal).
    pub atom: TermId,
}

/// Why a candidate step is not a fresh-definition equality.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum FreshDefEqShapeError {
    /// The step carries premises; a definition is derived from nothing.
    HasPremises,
    /// The step does not carry exactly one `:args` term.
    ArgArity(usize),
    /// The clause is not exactly one literal.
    ClauseArity(usize),
    /// The literal is not a binary `=` application.
    NotBinaryEq,
    /// The `:args` term is not an atomic variable.
    DefiniendumNotVariable,
    /// Neither `=` operand is the declared definiendum, or both are.
    DefiniendumNotAnOperand,
    /// The definiendum and the definiens have different sorts.
    SortMismatch(Sort, Sort),
}

impl std::fmt::Display for FreshDefEqShapeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::HasPremises => write!(f, "a fresh-definition equality must have no premises"),
            Self::ArgArity(n) => write!(
                f,
                "a fresh-definition equality must name its defined symbol in exactly one `:args` \
                 term, got {n}"
            ),
            Self::ClauseArity(n) => write!(
                f,
                "a fresh-definition equality must conclude exactly one literal, got {n}"
            ),
            Self::NotBinaryEq => write!(
                f,
                "a fresh-definition equality's literal must be a binary `=` application"
            ),
            Self::DefiniendumNotVariable => write!(
                f,
                "a fresh-definition equality's defined symbol must be an atomic variable"
            ),
            Self::DefiniendumNotAnOperand => write!(
                f,
                "a fresh-definition equality must have the defined symbol as EXACTLY one of the \
                 two `=` operands"
            ),
            Self::SortMismatch(d, l) => write!(
                f,
                "a fresh-definition equality must define a symbol at the definiens' own sort, got \
                 {d:?} := {l:?}"
            ),
        }
    }
}

/// Decompose one candidate `fresh_def_eq` step.
///
/// # Errors
///
/// Returns the first structural condition the step fails. Every condition is
/// local: freshness, uniqueness of the definiens, and the absence of introduced
/// symbols inside a definiens are whole-proof properties and are NOT decided
/// here.
pub fn recognize_fresh_def_eq(
    terms: &TermStore,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> Result<FreshDefEqShape, FreshDefEqShapeError> {
    if premise_count != 0 {
        return Err(FreshDefEqShapeError::HasPremises);
    }
    let [definiendum] = args else {
        return Err(FreshDefEqShapeError::ArgArity(args.len()));
    };
    let [atom] = clause else {
        return Err(FreshDefEqShapeError::ClauseArity(clause.len()));
    };
    if !matches!(terms.get(*definiendum), TermData::Var(_, _)) {
        return Err(FreshDefEqShapeError::DefiniendumNotVariable);
    }
    let TermData::App(sym, operands) = terms.get(*atom) else {
        return Err(FreshDefEqShapeError::NotBinaryEq);
    };
    // Arity is checked as well as the head. `mk_eq` only ever builds the binary
    // form, but a step's clause can be any interned term, and an n-ary `=`
    // would leave "which operand is the definiens" undefined.
    if sym.name() != "=" {
        return Err(FreshDefEqShapeError::NotBinaryEq);
    }
    let &[lhs, rhs] = operands.as_slice() else {
        return Err(FreshDefEqShapeError::NotBinaryEq);
    };
    // EXACTLY one operand may be the definiendum. `(= d d)` cannot describe a
    // definition (and `mk_eq` folds it to `true` anyway), and a step whose
    // declared symbol appears on neither side declares nothing — that step's
    // clause would be an ordinary equation between problem terms, which is NOT
    // conservative: `(= x y)` is false at `x = 1, y = 0`.
    let definiens = match (lhs == *definiendum, rhs == *definiendum) {
        (true, false) => rhs,
        (false, true) => lhs,
        _ => return Err(FreshDefEqShapeError::DefiniendumNotAnOperand),
    };
    // SORT is load-bearing, not hygiene: the whole soundness argument is
    // "assign `d` the value of `expr`", and that assignment must exist. An
    // `Int` symbol equated to a `Real` term instead forces `expr` to be
    // integral — a genuine constraint on the problem's own variables.
    let definiendum_sort = terms.sort(*definiendum).clone();
    let definiens_sort = terms.sort(definiens).clone();
    if definiendum_sort != definiens_sort {
        return Err(FreshDefEqShapeError::SortMismatch(
            definiendum_sort,
            definiens_sort,
        ));
    }
    Ok(FreshDefEqShape {
        definiendum: *definiendum,
        definiens,
        atom: *atom,
    })
}
