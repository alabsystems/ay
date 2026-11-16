// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Standalone, source-checked common-store definitions. Not a preprocessing pass.
//!
//! Given an asserted cover `g || h` and `g => a = store(c,k,v)`,
//! `h => a = store(c,k,w)`, derive `a = store(c,k,ite(g,v,w))`.
//! The guards need not be exclusive: both original branch constraints remain
//! necessary. Source hints never license an equality without strict replay.

use ay_core::{Proof, ProofId, Sort, Symbol, TermData, TermId, TermStore};

pub(crate) mod batch;
mod emit;
mod shape;
#[cfg(test)]
mod tests;

type Progress<'a> = &'a mut dyn FnMut(usize, usize) -> bool;

#[derive(Clone, Copy, Debug)]
pub(crate) struct GuardedStoreCase {
    pub(crate) guard: TermId,
    pub(crate) source: TermId,
    pub(crate) store: TermId,
}

#[derive(Clone, Copy, Debug)]
pub(crate) struct GuardedStoreRequest {
    pub(crate) variable: TermId,
    pub(crate) cases: [GuardedStoreCase; 2],
    pub(crate) cover_source: TermId,
    /// An asserted literal activating a guarded cover, not a guessed value.
    pub(crate) activation: Option<TermId>,
}

/// A checked consequence for the supplied original roots and term identities.
/// This is neither a refutation nor a model/SAT certificate. Like the proof
/// itself, it must be reauthenticated after replacing its source or term store.
#[derive(Debug)]
pub(crate) struct GuardedStoreDefinition {
    #[cfg(test)]
    variable: TermId,
    #[cfg(test)]
    replacement: TermId,
    definition: TermId,
    proof: Proof,
    conclusion: ProofId,
}

impl GuardedStoreDefinition {
    #[cfg(test)]
    pub(crate) fn variable(&self) -> TermId {
        self.variable
    }

    #[cfg(test)]
    pub(crate) fn replacement(&self) -> TermId {
        self.replacement
    }

    #[cfg(test)]
    pub(crate) fn definition(&self) -> TermId {
        self.definition
    }

    #[cfg(test)]
    pub(crate) fn proof(&self) -> (&Proof, ProofId) {
        (&self.proof, self.conclusion)
    }
}

/// Derive and authenticate one definition without changing any assertion.
///
/// Planning and the complete source-bound proof check share `progress`.
/// Refusal may leave harmless interned scratch terms, never a partial license.
/// The initial scope is scalar-index/scalar-cell arrays and two distinct Bool
/// variable guards. No carrier enumeration or bitvector arithmetic is needed.
pub(crate) fn derive(
    terms: &mut TermStore,
    original_roots: &[TermId],
    request: GuardedStoreRequest,
    progress: Progress<'_>,
) -> Option<GuardedStoreDefinition> {
    // Fixed metadata/identity checks precede every shape or payload walk.
    if !progress(64, 0) {
        return None;
    }
    let stores = shape::validate(terms, request, progress)?;
    let then_path = shape::case_path(terms, request.variable, request.cases[0], progress)?;
    let else_path = shape::case_path(terms, request.variable, request.cases[1], progress)?;
    let cover_path = shape::cover_path(terms, request, progress)?;
    // Prepay the fixed proof suffix and its raw nodes, symbols, clauses and
    // small scalar-array sorts. Source path scans/emission are charged apart.
    if !progress(128, 32 * 1024) {
        return None;
    }
    let value = terms.mk_ite_raw(request.cases[0].guard, stores[0][2], stores[1][2]);
    let array_sort = terms.sort(request.variable).clone();
    let replacement = terms.mk_app(
        Symbol::named("store"),
        [stores[0][0], stores[0][1], value],
        array_sort,
    );
    let definition = raw_eq(terms, request.variable, replacement);
    let (proof, conclusion) = emit::build(
        terms,
        request,
        [then_path, else_path],
        cover_path,
        replacement,
        definition,
        progress,
    )?;
    let authenticated = ay_proof::authenticate_premise_clauses_strict_with_context_and_progress(
        &proof,
        terms,
        None,
        None,
        original_roots,
        progress,
    )
    .ok()?;
    if authenticated.clause(conclusion)? != [definition] || !progress(0, 0) {
        return None;
    }
    Some(GuardedStoreDefinition {
        #[cfg(test)]
        variable: request.variable,
        #[cfg(test)]
        replacement,
        definition,
        proof,
        conclusion,
    })
}

fn raw_eq(terms: &mut TermStore, left: TermId, right: TermId) -> TermId {
    terms.mk_app(Symbol::named("="), [left, right], Sort::Bool)
}
