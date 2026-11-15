// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Immutable original CHC source with explicitly scoped universal premises.
//! Construction authenticates a bounded record/scalar-array fragment; it proves no
//! safety property and does not expose an unquantified solver problem publicly.

use crate::{ChcExpr, ChcProblem, ChcResult, ChcVar, HornClause};

mod complete_solve;
mod counterexample;
pub(crate) mod functions;
mod parse;
mod queries;
pub(crate) mod records;
mod solve;
pub use complete_solve::QuantifiedChcCompleteResult;
mod range_write;
mod source;
pub use range_write::{ArrayRange, ArrayRangeValue, ArrayRangeWrite};
mod view;
pub use counterexample::{
    QuantifiedChcCompleteTrace, QuantifiedChcCompleteTraceBinding, QuantifiedChcCompleteValue,
    QuantifiedChcCounterexample, QuantifiedChcTrace, QuantifiedChcTraceArtifactError,
    QuantifiedChcTraceBinding, QuantifiedChcTraceLiftError, QuantifiedChcTraceStepView,
    QuantifiedChcTraceView, QuantifiedChcValidatedCompleteTraceArtifact,
    QuantifiedChcValidatedTraceArtifact,
};
pub use functions::QuantifiedChcFunction;
pub use queries::{QuantifiedChcClauseOrigin, QuantifiedChcQueryId, QuantifiedChcQueryObligation};
pub use solve::{QuantifiedChcResult, QuantifiedChcSafety};
pub use view::{QuantifiedChcClauseView, QuantifiedChcSourceView};
#[cfg(test)]
mod source_tests;

pub(super) const MAX_PREMISE_BINDERS: usize = 8;

/// One universally quantified Boolean premise with an ordered binder group.
/// All binders scope only this matrix, not the clause or sibling premises.
/// This record is not validated until QuantifiedChcProblem construction.
#[derive(Debug, Clone)]
pub struct UniversalPremise {
    binder: ChcVar,
    additional_binders: Vec<ChcVar>,
    matrix: ChcExpr,
}

impl UniversalPremise {
    /// Record a lexical binder and matrix without checking or rewriting either.
    pub fn new(binder: ChcVar, matrix: ChcExpr) -> Self {
        Self {
            binder,
            additional_binders: Vec::new(),
            matrix,
        }
    }

    /// Record a nonempty joint binder group without rewriting its matrix.
    /// Only emptiness is rejected here; problem construction authenticates the
    /// complete group, including its sorts, unique names and fixed size limit.
    pub fn with_binders(binders: Vec<ChcVar>, matrix: ChcExpr) -> ChcResult<Self> {
        let mut binders = binders.into_iter();
        let binder = binders.next().ok_or_else(|| {
            crate::ChcError::Verification("quantified premise: empty binder group".into())
        })?;
        Ok(Self {
            binder,
            additional_binders: binders.collect(),
            matrix,
        })
    }

    /// First binder, retained for legacy single-binder callers.
    /// Consumers of a general premise must use `binders()` instead.
    pub fn binder(&self) -> &ChcVar {
        &self.binder
    }

    /// Every jointly scoped binder in original declaration order.
    pub fn binders(&self) -> impl Iterator<Item = &ChcVar> + Clone {
        std::iter::once(&self.binder).chain(self.additional_binders.iter())
    }

    /// Number of jointly scoped binders (always nonzero).
    pub fn binder_count(&self) -> usize {
        1 + self.additional_binders.len()
    }

    /// Original matrix, including its unnormalized literal guards.
    pub fn matrix(&self) -> &ChcExpr {
        &self.matrix
    }
}

/// A raw Horn clause whose antecedent includes ordered, scoped premises.
#[derive(Debug, Clone)]
pub struct QuantifiedHornClause {
    clause: HornClause,
    premises: Vec<UniversalPremise>,
}

impl QuantifiedHornClause {
    /// Retain a raw clause and conjoin universal premises with its body.
    pub fn new(clause: HornClause, premises: Vec<UniversalPremise>) -> Self {
        Self { clause, premises }
    }

    /// The original clause, before problem insertion or simplification.
    pub fn clause(&self) -> &HornClause {
        &self.clause
    }

    /// Independently scoped universal premises in original order.
    pub fn premises(&self) -> &[UniversalPremise] {
        &self.premises
    }
}

/// Validated immutable source, not an invariant or a proof capability.
///
/// The declaration input must contain no clauses, retained pruned queries or
/// stripped quantifiers. Original clause order, literal syntax and each lexical
/// binder are retained. Bounds cover source work and output, not total RSS or
/// response latency. Nonrecursive single-constructor records preserve their
/// complete declared nested fields. Arrays have BV indices and rank at most
/// two along every path, including paths through record fields. Enums,
/// recursive records and action metadata are not admitted. Ordinary functions
/// have scalar Bool/BV arguments and non-Boolean BV results. Names shadowing the
/// emitted theory vocabulary, record operations or ordinary functions refuse.
#[derive(Debug, Clone)]
pub struct QuantifiedChcProblem {
    source: ChcProblem,
    premises: Vec<Vec<UniversalPremise>>,
    smtlib: String,
    functions: functions::Functions,
    /// Canonical declaration order, moved from the admitted source registry.
    datatype_declarations: Vec<crate::ChcSort>,
}

impl QuantifiedChcProblem {
    /// Parse a bounded original-source HORN or fixedpoint script.
    ///
    /// Retains universal antecedents and raw clauses without the ordinary CHC
    /// parser's quantifier stripping, simplification or relational rewriting.
    /// Lexical lets are resolved simultaneously; explicit binders are freshly
    /// renamed to avoid capture. `source_smtlib()` is the resulting canonical
    /// typed source, not a byte-for-byte copy of the input. Unsupported syntax,
    /// incremental/mixed scripts and resource excess return an error, never an
    /// unquantified fallback.
    ///
    /// Supports ASCII Bool/BV/rank-two array scripts and bounded acyclic
    /// single-constructor records, outer universal clause binders and direct
    /// conjunctive universal premises with one to eight BV1..64 binders. QF
    /// state, array keys/cells and intermediates use `MAX_BITVECTOR_WIDTH`,
    /// with aggregate work/copy budgets. HORN uses
    /// Bool-returning `declare-fun`, `assert` and terminal `check-sat`, and must
    /// contain a false/theory consequent query. Fixedpoint uses `declare-var`,
    /// `declare-rel`, `rule` and one terminal relation `query`. Declarations
    /// precede clauses; only `exit` may follow the terminal command. Ordinary
    /// scalar functions use non-Boolean `declare-fun` signatures; general
    /// datatypes, options, annotations and incremental commands refuse.
    /// Input is capped at 8 MiB, nesting at 64 and charged tokens at 65,536;
    /// expanded work/copies and the typed source have additional fixed caps.
    pub fn parse_smtlib(input: &str) -> ChcResult<Self> {
        parse::parse(input)
    }

    /// Authenticate declarations and complete raw source without simplification.
    ///
    /// Accepts Bool, BV widths through `MAX_BITVECTOR_WIDTH`, BV-indexed arrays and declared acyclic
    /// single-constructor records. Every structural path ends in Bool/BV and
    /// crosses at most two arrays, even across record fields. Records admit
    /// at most 64 direct fields, 256 expanded scalar leaves
    /// and sort-edge depth 64, with separate aggregate work/name/copy caps.
    /// Record metadata and every constructor/selector use must
    /// agree with the complete declaration registry. Every premise jointly binds
    /// one to eight uniquely named BV1..64 variables. Free variables are scoped to
    /// each clause; a matrix binder may
    /// shadow a differently sorted outer name but not a record operation.
    pub fn new(declarations: ChcProblem, clauses: Vec<QuantifiedHornClause>) -> ChcResult<Self> {
        Self::new_with_functions(declarations, Vec::new(), clauses)
    }

    /// Authenticate complete ordinary function declarations and raw source.
    ///
    /// Arguments are scalar Bool/BV and results are BV1..MAX_BITVECTOR_WIDTH,
    /// including nullary functions. Names are unique across functions, Horn
    /// relations and record operations; clause variables and premise binders
    /// cannot shadow them. Every application must match its declared signature.
    /// Unused declarations and their order remain part of source identity.
    /// All declarations and source occurrences share the existing source limits.
    /// Admitting a UF does not prove that a model is a concrete callee execution.
    pub fn new_with_functions(
        declarations: ChcProblem,
        functions: Vec<QuantifiedChcFunction>,
        clauses: Vec<QuantifiedHornClause>,
    ) -> ChcResult<Self> {
        source::construct(declarations, functions, clauses)
    }

    /// Complete ordinary function declarations in original order, including
    /// declarations unused by every clause or premise.
    pub fn function_declarations(&self) -> &[QuantifiedChcFunction] {
        self.functions.declarations()
    }

    /// Complete canonical SMT-LIB HORN source, including every forall premise.
    /// This string is source identity, not a certificate or a solved verdict.
    pub fn source_smtlib(&self) -> &str {
        &self.smtlib
    }

    pub(crate) fn source_problem(&self) -> &ChcProblem {
        &self.source
    }

    pub(crate) fn premises(&self) -> &[Vec<UniversalPremise>] {
        &self.premises
    }
}
