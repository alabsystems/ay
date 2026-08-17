// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact symbolic interpretations for independently checked projection UFs.
//!
//! A projection interpretation denotes the total function
//! `lambda (x_0 .. x_n). x_i`. Unlike an extracted EUF function table, it is
//! valid at every argument tuple, including tuples that never occurred in the
//! ground solve. The exact core [`Symbol`] and complete signature travel with
//! the projection so overloads and future indexed symbols cannot alias.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::{Sort, Symbol, TermId, TermStore};
use ay_model_check::CheckedProjectionImplication;

use super::{eval_memo_clear, Executor, Model};
use crate::executor::quantified_sat::CheckedProjectionSatEvidence;

/// Maximum consecutive symbolic projection links evaluated in one model read.
pub(super) const MAX_PROJECTION_PEELS: usize = 4096;

/// A fail-closed error while following exact symbolic projection links.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(super) enum ProjectionUfReadError {
    /// An adversarial post-solve term exceeded the bounded symbolic walk.
    #[error("projection model value exceeds the {limit}-link evaluation limit")]
    LinkLimitExceeded { limit: usize },
    /// Private model state violated the checked-construction invariant.
    #[error(
        "projection UF {symbol} selects argument {projected_argument}, but the application arity is {arity}"
    )]
    MalformedInterpretation {
        symbol: Symbol,
        projected_argument: usize,
        arity: usize,
    },
    /// The selected application argument cannot inhabit the result sort.
    #[error(
        "projection UF {symbol} selects argument {projected_argument} of sort {selected_sort:?}, but the application result sort is {result_sort:?}"
    )]
    MalformedSort {
        symbol: Symbol,
        projected_argument: usize,
        selected_sort: Sort,
        result_sort: Sort,
    },
    /// A symbolic interpretation owns this exact symbol, so a read at another
    /// signature cannot fall through to an unrelated finite interpretation.
    #[error(
        "projection UF {symbol} is installed at signature ({installed_argument_sorts:?}) -> {installed_result_sort:?}, but the model read requested ({observed_argument_sorts:?}) -> {observed_result_sort:?}"
    )]
    SignatureConflict {
        symbol: Symbol,
        installed_argument_sorts: Vec<Sort>,
        installed_result_sort: Sort,
        observed_argument_sorts: Vec<Sort>,
        observed_result_sort: Sort,
    },
}

/// One immutable, total projection interpretation.
///
/// This type is private and can be constructed in production only by copying
/// the independently checker's sealed evidence. Raw construction remains
/// test-only for model-consumer fault injection.
#[derive(Debug, Clone, PartialEq, Eq)]
struct ProjectionUfInterpretation {
    symbol: Symbol,
    argument_sorts: Vec<Sort>,
    result_sort: Sort,
    projected_argument: usize,
}

impl ProjectionUfInterpretation {
    /// Copy and locally recheck one definition exposed by the sealed checker.
    fn from_checked_parts(
        symbol: Symbol,
        argument_sorts: Vec<Sort>,
        result_sort: Sort,
        projected_argument: usize,
    ) -> Result<Self, ProjectionUfModelError> {
        match &symbol {
            Symbol::Named(name) if name.is_empty() => {
                return Err(ProjectionUfModelError::EmptyNamedSymbol);
            }
            Symbol::Named(_) => {}
            _ => return Err(ProjectionUfModelError::NonNamedSymbol(symbol)),
        }
        let Some(projected_sort) = argument_sorts.get(projected_argument) else {
            return Err(ProjectionUfModelError::ProjectionOutOfBounds {
                symbol,
                projected_argument,
                arity: argument_sorts.len(),
            });
        };
        if projected_sort != &result_sort {
            return Err(ProjectionUfModelError::ProjectionSortMismatch {
                symbol,
                projected_argument,
                argument_sort: projected_sort.clone(),
                result_sort,
            });
        }
        Ok(Self {
            symbol,
            argument_sorts,
            result_sort,
            projected_argument,
        })
    }
}

/// A frozen set of projection interpretations attached to one solver result.
#[derive(Debug, Clone, Default)]
pub(in crate::executor) struct ProjectionUfModel {
    by_symbol: HashMap<Symbol, ProjectionUfInterpretation>,
}

impl ProjectionUfModel {
    /// Copy the exact definitions exposed by a semantically checked result.
    ///
    /// Candidate data cannot cross this boundary without first becoming the
    /// checker's sealed, non-`Clone` evidence type. Only checked accessors are
    /// read; no producer-owned declaration or index is accepted directly. This
    /// constructs model data only: future SAT steering also requires positive
    /// source/declaration conformance and dispatch evidence.
    pub(in crate::executor) fn from_checked(
        checked: &CheckedProjectionImplication,
    ) -> Result<Self, ProjectionUfModelError> {
        Self::from_checked_parts(checked.definitions().iter().map(|definition| {
            (
                definition.symbol().clone(),
                definition.parameter_sorts().to_vec(),
                definition.result_sort().clone(),
                definition.projected_parameter(),
            )
        }))
    }

    /// Test-only construction for evaluator/printer fault-injection tests.
    #[cfg(test)]
    pub(super) fn from_test_definitions(
        definitions: impl IntoIterator<Item = (Symbol, Vec<Sort>, Sort, usize)>,
    ) -> Result<Self, ProjectionUfModelError> {
        Self::from_checked_parts(definitions)
    }

    /// Deliberately violate the private construction invariant so output tests
    /// can prove that the final formatting boundary still fails closed.
    #[cfg(test)]
    pub(super) fn from_malformed_test_definition_unchecked(
        symbol: Symbol,
        argument_sorts: Vec<Sort>,
        result_sort: Sort,
        projected_argument: usize,
    ) -> Self {
        let interpretation = ProjectionUfInterpretation {
            symbol: symbol.clone(),
            argument_sorts,
            result_sort,
            projected_argument,
        };
        let mut by_symbol = HashMap::default();
        by_symbol.insert(symbol, interpretation);
        Self { by_symbol }
    }

    fn from_checked_parts(
        definitions: impl IntoIterator<Item = (Symbol, Vec<Sort>, Sort, usize)>,
    ) -> Result<Self, ProjectionUfModelError> {
        let mut by_symbol = HashMap::default();
        for (symbol, argument_sorts, result_sort, projected_argument) in definitions {
            let interpretation = ProjectionUfInterpretation::from_checked_parts(
                symbol.clone(),
                argument_sorts,
                result_sort,
                projected_argument,
            )?;
            if by_symbol.insert(symbol.clone(), interpretation).is_some() {
                return Err(ProjectionUfModelError::DuplicateSymbol(symbol));
            }
        }
        Ok(Self { by_symbol })
    }

    /// Verify that this immutable model is exactly the checked definition set.
    ///
    /// This post-installation comparison prevents a future model-construction
    /// refactor from silently dropping, changing, or adding an interpretation
    /// while retaining the original SAT authority.
    pub(in crate::executor) fn matches_checked(
        &self,
        checked: &CheckedProjectionImplication,
    ) -> bool {
        self.by_symbol.len() == checked.definitions().len()
            && checked.definitions().iter().all(|definition| {
                self.by_symbol
                    .get(definition.symbol())
                    .is_some_and(|entry| {
                        entry.symbol == *definition.symbol()
                            && entry.argument_sorts == definition.parameter_sorts()
                            && entry.result_sort == *definition.result_sort()
                            && entry.projected_argument == definition.projected_parameter()
                    })
            })
    }

    /// Return the projected argument for this exact declaration signature.
    pub(super) fn projected_argument_for_signature(
        &self,
        symbol: &Symbol,
        argument_sorts: &[Sort],
        result_sort: &Sort,
    ) -> Result<Option<usize>, ProjectionUfReadError> {
        let Some(interpretation) = self.by_symbol.get(symbol) else {
            return Ok(None);
        };
        debug_assert_eq!(&interpretation.symbol, symbol);
        if interpretation.argument_sorts != argument_sorts
            || &interpretation.result_sort != result_sort
        {
            return Err(ProjectionUfReadError::SignatureConflict {
                symbol: symbol.clone(),
                installed_argument_sorts: interpretation.argument_sorts.clone(),
                installed_result_sort: interpretation.result_sort.clone(),
                observed_argument_sorts: argument_sorts.to_vec(),
                observed_result_sort: result_sort.clone(),
            });
        }
        Ok(Some(interpretation.projected_argument))
    }

    /// Return the projected argument for an application only on an exact
    /// symbol-and-signature match.
    pub(super) fn projected_argument_for_application(
        &self,
        symbol: &Symbol,
        terms: &TermStore,
        arguments: &[TermId],
        result_sort: &Sort,
    ) -> Result<Option<usize>, ProjectionUfReadError> {
        let Some(interpretation) = self.by_symbol.get(symbol) else {
            return Ok(None);
        };
        debug_assert_eq!(&interpretation.symbol, symbol);
        if &interpretation.result_sort != result_sort
            || interpretation.argument_sorts.len() != arguments.len()
            || !interpretation
                .argument_sorts
                .iter()
                .zip(arguments)
                .all(|(expected, argument)| expected == terms.sort(*argument))
        {
            let observed_argument_sorts = arguments
                .iter()
                .map(|argument| terms.sort(*argument).clone())
                .collect();
            return Err(ProjectionUfReadError::SignatureConflict {
                symbol: symbol.clone(),
                installed_argument_sorts: interpretation.argument_sorts.clone(),
                installed_result_sort: interpretation.result_sort.clone(),
                observed_argument_sorts,
                observed_result_sort: result_sort.clone(),
            });
        }
        Ok(Some(interpretation.projected_argument))
    }

    /// Follow consecutive exact projection applications to their selected
    /// argument before any TermId-keyed model source is consulted.
    ///
    /// `Ok(None)` means `term` is not a projection application. `Ok(Some(t))`
    /// returns the final selected term after at least one projection link.
    /// Resource exhaustion and an impossible malformed private entry both fail
    /// closed instead of allowing a lower-priority finite-table or pin lookup.
    pub(super) fn peel_application_chain(
        &self,
        terms: &TermStore,
        term: TermId,
    ) -> Result<Option<TermId>, ProjectionUfReadError> {
        let mut current = term;
        let mut peels = 0usize;
        loop {
            let result_sort = terms.sort(current);
            let TermData::App(symbol, arguments) = terms.get(current) else {
                break;
            };
            let Some(projected_argument) =
                self.projected_argument_for_application(symbol, terms, arguments, result_sort)?
            else {
                break;
            };
            if peels == MAX_PROJECTION_PEELS {
                return Err(ProjectionUfReadError::LinkLimitExceeded {
                    limit: MAX_PROJECTION_PEELS,
                });
            }
            let Some(&selected) = arguments.get(projected_argument) else {
                return Err(ProjectionUfReadError::MalformedInterpretation {
                    symbol: symbol.clone(),
                    projected_argument,
                    arity: arguments.len(),
                });
            };
            let selected_sort = terms.sort(selected);
            if selected_sort != result_sort {
                return Err(ProjectionUfReadError::MalformedSort {
                    symbol: symbol.clone(),
                    projected_argument,
                    selected_sort: selected_sort.clone(),
                    result_sort: result_sort.clone(),
                });
            }
            current = selected;
            peels += 1;
        }
        Ok((peels > 0).then_some(current))
    }
}

impl Executor {
    /// Atomically install the exact total model carried by combined SAT
    /// evidence.
    ///
    /// All query, source, declaration, and semantic snapshots are rechecked
    /// before model construction, immediately before the state mutation, and
    /// once more after installation. The method never derives authority from
    /// the candidate or from the shape of the live assertion alone.
    pub(in crate::executor) fn install_authorized_projection_model(
        &mut self,
        evidence: &CheckedProjectionSatEvidence,
    ) -> Result<(), ProjectionUfModelError> {
        if evidence.roots() != self.ctx.assertions.as_slice() {
            return Err(ProjectionUfModelError::LiveQueryMismatch);
        }
        if !evidence
            .semantics()
            .matches_snapshot(&self.ctx.terms, evidence.roots())
        {
            return Err(ProjectionUfModelError::SnapshotMismatch);
        }
        if !evidence.source_is_current(&self.ctx) {
            return Err(ProjectionUfModelError::SourceBindingMismatch);
        }
        if !evidence.is_current(self) {
            return Err(ProjectionUfModelError::AuthoredQueryMismatch);
        }

        let projection_ufs = ProjectionUfModel::from_checked(evidence.semantics())?;
        if !projection_ufs.matches_checked(evidence.semantics()) {
            return Err(ProjectionUfModelError::InstalledModelMismatch);
        }
        // No fallible or callback-driven work may occur between the final
        // currentness check and revoking the predecessor result.
        if !evidence.is_current(self) {
            return Err(ProjectionUfModelError::AuthoredQueryMismatch);
        }

        self.last_result = None;
        self.last_model_validated = false;
        self.last_sat_certificate = None;
        let mut model = Model::empty();
        model.projection_ufs = projection_ufs;
        self.last_model = Some(model);
        eval_memo_clear();

        let installed_matches = self
            .last_model
            .as_ref()
            .is_some_and(|model| model.projection_ufs.matches_checked(evidence.semantics()));
        if !installed_matches || !evidence.is_current(self) {
            self.last_model = None;
            self.last_model_validated = false;
            self.last_sat_certificate = None;
            return Err(if installed_matches {
                ProjectionUfModelError::AuthoredQueryMismatch
            } else {
                ProjectionUfModelError::InstalledModelMismatch
            });
        }
        Ok(())
    }

    /// Atomically attach a semantically checked symbolic projection model.
    ///
    /// This dormant installer is exercised only by model-consumer tests and is
    /// not a SAT-authority path. Building the immutable model can fail without
    /// touching solver state. The supplied roots must be the executor's exact
    /// current hard query as well as the checker's frozen snapshot.
    ///
    /// Once construction succeeds, the prior solver verdict, model-validation
    /// state, and SAT-funnel evidence are revoked before the model is installed.
    /// The v1 checker accepts exactly one universal and no ground roots, so
    /// installation always replaces any prior theory/table state with a fresh
    /// empty base model; retaining it would mix a new certificate with a stale
    /// result.
    #[cfg(test)]
    pub(in crate::executor) fn install_checked_projection_model(
        &mut self,
        checked: &CheckedProjectionImplication,
        roots: &[TermId],
    ) -> Result<(), ProjectionUfModelError> {
        if roots != self.ctx.assertions.as_slice() {
            return Err(ProjectionUfModelError::LiveQueryMismatch);
        }
        if !checked.matches_snapshot(&self.ctx.terms, roots) {
            return Err(ProjectionUfModelError::SnapshotMismatch);
        }
        let projection_ufs = ProjectionUfModel::from_checked(checked)?;

        self.last_result = None;
        self.last_model_validated = false;
        self.last_sat_certificate = None;
        let mut model = Model::empty();
        model.projection_ufs = projection_ufs;
        self.last_model = Some(model);
        eval_memo_clear();
        Ok(())
    }
}

/// A malformed or ambiguous checked projection-model entry.
#[derive(Debug, Clone, PartialEq, Eq, thiserror::Error)]
pub(in crate::executor) enum ProjectionUfModelError {
    /// The caller-supplied roots are not the executor's exact live hard query.
    #[error("projection UF certificate roots do not match the live hard query")]
    LiveQueryMismatch,
    /// The checked frozen term graph or exact root vector is not current.
    #[error("projection UF certificate does not match the current term snapshot and roots")]
    SnapshotMismatch,
    /// The positive source/declaration evidence no longer describes the live
    /// context.
    #[error("projection UF source/declaration binding is no longer current")]
    SourceBindingMismatch,
    /// The authored public-query capability no longer denotes this solve.
    #[error("projection UF authored-query authority is no longer current")]
    AuthoredQueryMismatch,
    /// The installed immutable model differs from the checked definitions.
    #[error("installed projection UF model differs from checked semantic evidence")]
    InstalledModelMismatch,
    /// A v1 projection definition must use a nonempty named core symbol.
    #[error("projection UF has an empty named symbol")]
    EmptyNamedSymbol,
    /// Indexed and future symbol variants are outside the v1 model format.
    #[error("projection UF symbol is not named: {0:?}")]
    NonNamedSymbol(Symbol),
    /// The selected argument does not exist.
    #[error(
        "projection UF {symbol} selects argument {projected_argument}, but its arity is {arity}"
    )]
    ProjectionOutOfBounds {
        symbol: Symbol,
        projected_argument: usize,
        arity: usize,
    },
    /// A projection can return an argument only at the argument's exact sort.
    #[error(
        "projection UF {symbol} selects argument {projected_argument} of sort {argument_sort:?}, but returns {result_sort:?}"
    )]
    ProjectionSortMismatch {
        symbol: Symbol,
        projected_argument: usize,
        argument_sort: Sort,
        result_sort: Sort,
    },
    /// One exact core symbol may have exactly one interpretation.
    #[error("duplicate projection UF symbol {0}")]
    DuplicateSymbol(Symbol),
}

#[cfg(test)]
mod tests;
