// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Borrowed complete typed source, never an unquantified solver skeleton.

use super::{QuantifiedChcFunction, QuantifiedChcProblem, UniversalPremise};
use crate::{ChcExpr, ChcSort, ClauseHead, HornClause, Predicate, PredicateId};

/// Allocation-free inspection of one immutable, authenticated source.
///
/// Declarations include unused entries; clause views keep every original
/// universally quantified premise attached to its antecedent. The view is not
/// a safety verdict or a proof capability and cannot be converted into a
/// quantifier-free `ChcProblem`. Canonical source order is not the caller's
/// original textual declaration order.
///
/// The view cannot outlive its source:
///
/// ```compile_fail
/// use ay_chc::quantified::{QuantifiedChcProblem, QuantifiedChcSourceView};
/// fn escape(problem: QuantifiedChcProblem) -> QuantifiedChcSourceView<'static> {
///     problem.source_view()
/// }
/// ```
///
/// A caller cannot fabricate a view:
///
/// ```compile_fail
/// use ay_chc::quantified::QuantifiedChcSourceView;
/// let fabricated = QuantifiedChcSourceView {};
/// ```
#[derive(Debug, Clone, Copy)]
pub struct QuantifiedChcSourceView<'a> {
    problem: &'a QuantifiedChcProblem,
}

/// One complete clause antecedent and head in immutable canonical source order.
///
/// Its semantics are the conjunction of [`Self::body_predicates`], the optional
/// [`Self::constraint`] and every [`Self::premises`] implying [`Self::head`].
/// Matrix-only free variables belong to the clause scope; each premise's full
/// binder group scopes only its own matrix. Accessors never clone or allocate.
/// There is no standalone quantifier-free clause conversion.
///
/// The borrowed premise inventory cannot be mutated:
///
/// ```compile_fail
/// use ay_chc::quantified::{QuantifiedChcClauseView, UniversalPremise};
/// fn replace(view: QuantifiedChcClauseView<'_>, premise: UniversalPremise) {
///     view.premises()[0] = premise;
/// }
/// ```
#[derive(Debug, Clone, Copy)]
pub struct QuantifiedChcClauseView<'a> {
    index: usize,
    clause: &'a HornClause,
    premises: &'a [UniversalPremise],
}

impl QuantifiedChcProblem {
    /// Borrow the complete typed source, including every scoped premise.
    /// No parsing, copying, solving or proof validation occurs.
    pub fn source_view(&self) -> QuantifiedChcSourceView<'_> {
        QuantifiedChcSourceView { problem: self }
    }
}

impl<'a> QuantifiedChcSourceView<'a> {
    /// Complete predicate declarations in retained order, with stable IDs.
    pub fn predicates(&self) -> &'a [Predicate] {
        self.problem.source.predicates()
    }

    /// Borrow the declaration with this source-local ID, or `None` if absent.
    pub fn predicate(&self, id: PredicateId) -> Option<&'a Predicate> {
        self.predicates()
            .get(id.index())
            .filter(|predicate| predicate.id == id)
    }

    /// All record declarations, including unused records, in canonical emitted
    /// name order. Every constructor and nested field sort is retained. This is
    /// not the original textual order of `declare-datatype` commands.
    pub fn datatype_declarations(&self) -> &'a [ChcSort] {
        &self.problem.datatype_declarations
    }

    /// All ordinary functions in retained declaration order, including unused
    /// and nullary functions. These are signatures, not function models.
    pub fn function_declarations(&self) -> &'a [QuantifiedChcFunction] {
        self.problem.function_declarations()
    }

    /// Complete canonical source identity, including declarations and premises.
    pub fn source_smtlib(&self) -> &'a str {
        self.problem.source_smtlib()
    }

    /// Whether the source used fixedpoint rather than HORN result polarity.
    pub fn is_fixedpoint_format(&self) -> bool {
        self.problem.source.is_fixedpoint_format()
    }

    /// Borrow one complete clause, or `None` for an out-of-range source index.
    pub fn clause(&self, index: usize) -> Option<QuantifiedChcClauseView<'a>> {
        Some(QuantifiedChcClauseView {
            index,
            clause: self.problem.source.clauses().get(index)?,
            premises: self.problem.premises.get(index)?,
        })
    }

    /// Borrow all complete clauses in exact retained order, including duplicate
    /// and false-body queries. No simplification or premise flattening occurs.
    pub fn clauses(
        &self,
    ) -> impl ExactSizeIterator<Item = QuantifiedChcClauseView<'a>> + DoubleEndedIterator + Clone + 'a
    {
        self.problem
            .source
            .clauses()
            .iter()
            .zip(&self.problem.premises)
            .enumerate()
            .map(|(index, (clause, premises))| QuantifiedChcClauseView {
                index,
                clause,
                premises,
            })
    }
}

impl<'a> QuantifiedChcClauseView<'a> {
    /// Index in this source's exact clause sequence, not a derivation occurrence
    /// index. A query slice has its own local clause indices.
    pub fn index(&self) -> usize {
        self.index
    }

    /// Ordered relation applications in the antecedent. Universal premises are
    /// additional conjuncts available through [`Self::premises`].
    pub fn body_predicates(&self) -> &'a [(PredicateId, Vec<ChcExpr>)] {
        &self.clause.body.predicates
    }

    /// Original background constraint; `None` means true. Literal false and
    /// unsimplified compound syntax are preserved exactly.
    pub fn constraint(&self) -> Option<&'a ChcExpr> {
        self.clause.body.constraint.as_ref()
    }

    /// Ordered complete universal premises, with independent lexical scopes.
    pub fn premises(&self) -> &'a [UniversalPremise] {
        self.premises
    }

    /// Original relation or false head.
    pub fn head(&self) -> &'a ClauseHead {
        &self.clause.head
    }

    /// Ordinal among this source's false-head clauses, or `None` for a rule.
    /// Query slicing preserves aggregate identity separately in its query ID.
    pub fn source_query_ordinal(&self) -> Option<usize> {
        self.clause.source_query_ordinal
    }
}

#[cfg(test)]
mod tests;
