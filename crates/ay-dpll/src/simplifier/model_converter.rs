// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The model-converter half of the pipeline contract.
//!
//! A pass that removes a symbol from the problem, or introduces one the input
//! does not have, records here how a model of its OUTPUT becomes a model of its
//! INPUT (z3's `model_converter`, `reference/z3/src/ast/converters/`):
//!
//! * [`ConverterEntry::Fresh`] — a symbol minted by the pass (a Skolem
//!   witness). It is not part of the input signature; reconstruction drops it.
//! * [`ConverterEntry::Define`] — a function symbol eliminated by a macro
//!   definition `f(x̄) := body`. Reconstruction interprets `f` as that lambda,
//!   evaluated in the output model. Bodies are kept closed with respect to
//!   every symbol eliminated LATER in the same run (a later macro is expanded
//!   inside earlier bodies when it is found), so the entries can be applied in
//!   any order.
//!
//! Equivalence-preserving passes (NNF, DER, qe-lite, unused-variable
//! elimination, value propagation) record nothing: a model of their output is
//! a model of their input over the same signature.

use ay_core::{Sort, TermId, TermStore};

use super::terms::mentions_head;

/// One reconstruction step.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) enum ConverterEntry {
    /// A symbol the pass introduced; drop it from reconstructed models.
    Fresh {
        /// The minted symbol's spelling (a `Var` name or an application head).
        name: String,
    },
    /// A function symbol eliminated by a macro: `name(params) := body`.
    Define {
        /// The eliminated symbol.
        name: String,
        /// Formal parameters, in argument order; `body` mentions them as `Var`s.
        params: Vec<(String, Sort)>,
        /// The defining term over `params` and surviving symbols.
        body: TermId,
    },
}

/// Ordered reconstruction steps for one pipeline run.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub(crate) struct ModelConverter {
    entries: Vec<ConverterEntry>,
}

impl ModelConverter {
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Record a symbol the pipeline minted.
    pub(super) fn fresh(&mut self, name: String) {
        if !self
            .entries
            .iter()
            .any(|e| matches!(e, ConverterEntry::Fresh { name: n } if *n == name))
        {
            self.entries.push(ConverterEntry::Fresh { name });
        }
    }

    /// Record a macro elimination.
    pub(super) fn define(&mut self, name: String, params: Vec<(String, Sort)>, body: TermId) {
        self.entries
            .push(ConverterEntry::Define { name, params, body });
    }

    /// Rewrite every recorded macro body with `expand` (used when a later macro
    /// eliminates a symbol an earlier body still mentions). Returns `false` if
    /// `expand` refused a body; the caller then abandons the later macro.
    pub(super) fn expand_bodies(
        &mut self,
        mut expand: impl FnMut(TermId) -> Option<TermId>,
    ) -> bool {
        let mut rewritten = Vec::with_capacity(self.entries.len());
        for entry in &self.entries {
            match entry {
                ConverterEntry::Define { body, .. } => match expand(*body) {
                    Some(new_body) => rewritten.push(Some(new_body)),
                    None => return false,
                },
                ConverterEntry::Fresh { .. } => rewritten.push(None),
            }
        }
        for (entry, new_body) in self.entries.iter_mut().zip(rewritten) {
            if let (ConverterEntry::Define { body, .. }, Some(new_body)) = (entry, new_body) {
                *body = new_body;
            }
        }
        true
    }

    /// The recorded steps, in the order they were taken.
    pub(crate) fn entries(&self) -> &[ConverterEntry] {
        &self.entries
    }

    /// Whether no pass recorded anything.
    #[cfg(test)]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    /// The macro definition for `name`, if the pipeline eliminated it.
    #[cfg(test)]
    pub(crate) fn definition(&self, name: &str) -> Option<(&[(String, Sort)], TermId)> {
        self.entries.iter().find_map(|e| match e {
            ConverterEntry::Define {
                name: n,
                params,
                body,
            } if n == name => Some((params.as_slice(), *body)),
            _ => None,
        })
    }

    /// Contract check: no recorded body mentions a symbol this converter
    /// eliminated. Holds by construction (see [`Self::expand_bodies`]); kept as
    /// a checked invariant for tests and debug builds.
    pub(crate) fn bodies_are_closed(&self, terms: &TermStore) -> bool {
        let eliminated: Vec<&str> = self
            .entries
            .iter()
            .filter_map(|e| match e {
                ConverterEntry::Define { name, .. } => Some(name.as_str()),
                ConverterEntry::Fresh { .. } => None,
            })
            .collect();
        self.entries.iter().all(|e| match e {
            ConverterEntry::Define { body, .. } => eliminated
                .iter()
                .all(|name| !mentions_head(terms, *body, name)),
            ConverterEntry::Fresh { .. } => true,
        })
    }
}
