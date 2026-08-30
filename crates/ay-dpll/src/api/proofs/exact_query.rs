// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Same-solver authentication for portable exact-query proof bundles.

use ay_core::kani_compat::DetHashSet;
use ay_frontend::SourceContextStamp;

use crate::api::{Solver, SolverCacheToken, Term};

/// Opaque same-solver binding for one exact, plain SMT-LIB parse delta.
///
/// Minted only by [`Solver::parse_smtlib2_with_exact_query_binding`]. Its
/// private solver generation, source/declaration context, and ordered
/// authenticated assertion handles prevent a proof bundle from being rebound
/// to a sibling solver, a later query, or a mutated context.
#[derive(Debug, Clone)]
#[must_use = "the binding must be consumed when exporting exact-query proof evidence"]
pub struct ExactSmtlibQueryBinding {
    pub(crate) solver: SolverCacheToken,
    pub(crate) source_context: SourceContextStamp,
    pub(crate) assertions: Vec<Term>,
}

impl ExactSmtlibQueryBinding {
    /// Authenticated canonical assertion handles in exact parse order.
    #[must_use]
    pub fn assertions(&self) -> &[Term] {
        &self.assertions
    }
}

impl Solver {
    /// Export a strict bundle bound to one exact SMT-LIB parse on this solver.
    ///
    /// This is the external-query-authenticating twin of
    /// [`Self::export_last_unsat_bundle`]. The opaque `binding` must have been
    /// minted by this solver's exact parse call, and the solver's declaration,
    /// assertion, source-context, and public-query epochs must still match it.
    /// Internally AY authenticates source-rebuilt proof premises (which may have
    /// different raw ids from folded canonical parse roots), validates every
    /// checked `Assume` against that exact source closure, narrows the returned
    /// obligation inventory to the actually used assumptions, and performs a
    /// second independent strict recheck after narrowing.
    ///
    /// Returns `None` on a foreign/stale binding, any intervening mutation, a
    /// non-plain query epoch, a missing/incomplete proof, an empty assumption
    /// set, or any assumption outside the exact authenticated source closure.
    #[must_use]
    pub fn export_last_unsat_bundle_for_exact_query(
        &self,
        binding: &ExactSmtlibQueryBinding,
    ) -> Option<ay_proof::SerializableProofBundle> {
        if !binding.solver.is_current() || binding.solver != self.cache_token {
            return None;
        }
        let exact_roots = self
            .resolve_terms(
                "export_last_unsat_bundle_for_exact_query",
                &binding.assertions,
            )
            .ok()?;
        if exact_roots.is_empty() {
            return None;
        }
        let source_closure = self
            .executor
            .exact_plain_query_source_closure(&exact_roots, &binding.source_context)?;
        let source_closure: DetHashSet<_> = source_closure.into_iter().collect();

        let mut bundle = self.export_last_unsat_bundle()?;
        let checked = ay_proof::re_check_bundle_strict(&bundle).ok()?;
        if !checked.quality.is_complete()
            || checked.assume_terms.is_empty()
            || checked
                .assume_terms
                .iter()
                .any(|assumption| !source_closure.contains(assumption))
        {
            return None;
        }

        let mut seen = DetHashSet::default();
        bundle.obligation_assertions = checked
            .assume_terms
            .iter()
            .copied()
            .filter(|assumption| seen.insert(*assumption))
            .collect();
        let rebound = ay_proof::re_check_bundle_strict(&bundle).ok()?;
        if !rebound.quality.is_complete()
            || rebound.assume_terms.is_empty()
            || rebound
                .assume_terms
                .iter()
                .any(|assumption| !seen.contains(assumption))
        {
            return None;
        }
        Some(bundle)
    }
}
