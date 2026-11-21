// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Immutable native input identity for a later checked external proof scope.
//! Capturing this input grants no proof or subset authority.

use ay_core::term::TermEntryStamp;
use ay_core::{Sort, Symbol, TermId};
use ay_frontend::{DeclarationId, SourceContextStamp};

use crate::executor::{AuthoredPlainHardQueryPermit, Executor, QueryAuthorityEpoch};

mod codec;
mod datatype_context;
mod lexical_variables;
mod retained_source;
#[cfg(test)]
mod tests;

pub(crate) const MAX_NATIVE_SOURCE_ROOTS: usize = 16_384;
const MAX_SOURCE_TERMS: usize = 262_144;
const MAX_SOURCE_DECLARATIONS: usize = 4_096;
const MAX_SOURCE_WORK: usize = 2_000_000;
const MAX_SOURCE_BYTES: usize = 32 * 1024 * 1024;
const MAX_SOURCE_STORE_BYTES: usize = 256 * 1024 * 1024;

/// One exact live ordinary declaration, rather than a grouping by spelling.
#[derive(Clone, Debug)]
pub(crate) struct NativeDeclarationBinding {
    pub(crate) name: String,
    pub(crate) symbol: Symbol,
    pub(crate) identity: DeclarationId,
    pub(crate) domain: Box<[Sort]>,
    pub(crate) range: Sort,
    pub(crate) constant: Option<(TermId, TermEntryStamp)>,
}

#[derive(Clone, Debug)]
pub(crate) struct NativeFreeVariableBinding {
    pub(crate) term: TermId,
    pub(crate) entry: TermEntryStamp,
    pub(crate) sort: Sort,
}

/// A private pre-solve capture of the complete ordered authored native query.
/// Digests describe its typed contents; current opaque epochs and immutable
/// term/declaration identities are the authority checked by consumers.
#[derive(Clone, Debug)]
pub(crate) struct NativeProofSourceScope {
    query_epoch: QueryAuthorityEpoch,
    source_context: SourceContextStamp,
    roots: Box<[TermId]>,
    root_entries: Box<[TermEntryStamp]>,
    source_entries: Box<[(TermId, TermEntryStamp)]>,
    declarations: Box<[NativeDeclarationBinding]>,
    datatypes: datatype_context::NativeDatatypeContext,
    free_variables: Box<[NativeFreeVariableBinding]>,
    checker_metadata_generation: u64,
    scope_depth: usize,
    full_typed_query_sha256: [u8; 32],
    declaration_context_sha256: [u8; 32],
}

impl NativeProofSourceScope {
    pub(in crate::executor) fn capture(
        executor: &Executor,
        permit: &AuthoredPlainHardQueryPermit,
    ) -> Option<Self> {
        let original = ay_core::resource::current_check_stop().ok()?;
        let guard = ay_core::resource::current_guard();
        let mut stopped = false;
        Self::capture_with_progress(executor, permit, &mut |_, _| {
            stopped |= executor.term_memory_exceeded()
                || executor.solve_interrupt_is_set()
                || executor.certification_stop().is_some()
                || original.as_ref().is_some_and(|stop| stop())
                || guard.as_ref().is_some_and(|guard| guard.poll().is_some());
            !stopped
        })
    }

    fn capture_with_progress(
        executor: &Executor,
        permit: &AuthoredPlainHardQueryPermit,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<Self> {
        let mut control = codec::Control::new(progress);
        control.charge(0, 0)?;
        if executor.ctx.assertions.len() > MAX_NATIVE_SOURCE_ROOTS
            || executor.ctx.terms.len() > MAX_SOURCE_TERMS
            || executor.ctx.terms.true_memory_bytes() > MAX_SOURCE_STORE_BYTES
            || !permit.is_current(executor)
        {
            return None;
        }
        control.charge(
            executor.ctx.assertions.len(),
            executor
                .ctx
                .assertions
                .len()
                .checked_mul(std::mem::size_of::<TermId>())?,
        )?;
        let roots = executor
            .ctx
            .native_authored_assertion_terms_aligned_bounded(MAX_NATIVE_SOURCE_ROOTS)?;
        if roots.as_slice() != permit.roots() {
            return None;
        }
        if roots
            .iter()
            .any(|&root| executor.ctx.terms.sort(root) != &Sort::Bool)
        {
            return None;
        }
        let (epoch, source_context, epoch_roots) =
            executor.bounded_plain_unsat_query_scope(MAX_NATIVE_SOURCE_ROOTS)?;
        if epoch_roots != roots
            || &source_context != permit.source_context_stamp()
            || executor
                .proof_problem_assertion_provenance
                .as_ref()?
                .original_problem_assertions
                != roots
        {
            return None;
        }
        control.charge(
            roots.len(),
            roots
                .len()
                .checked_mul(std::mem::size_of::<TermEntryStamp>())?,
        )?;
        let entries: Option<Vec<_>> = roots
            .iter()
            .map(|&root| executor.ctx.terms.entry_stamp(root))
            .collect();
        let datatypes = datatype_context::NativeDatatypeContext::capture(executor, &mut control)?;
        let (declarations, declaration_context_sha256) =
            codec::declarations(executor, &datatypes, &mut control)?;
        let (full_typed_query_sha256, source_entries) = codec::query_digest(
            executor,
            &roots,
            declaration_context_sha256,
            &datatypes,
            &mut control,
        )?;
        let free_variables = lexical_variables::collect(executor, &roots, &mut control)?;
        control.charge(0, 0)?;
        Some(Self {
            query_epoch: epoch,
            source_context,
            roots: roots.into_boxed_slice(),
            root_entries: entries?.into_boxed_slice(),
            source_entries: source_entries.into_boxed_slice(),
            declarations: declarations.into_boxed_slice(),
            datatypes,
            free_variables: free_variables.into_boxed_slice(),
            checker_metadata_generation: executor.ctx.terms.checker_visible_metadata_generation(),
            scope_depth: executor.ctx.scope_depth(),
            full_typed_query_sha256,
            declaration_context_sha256,
        })
    }

    pub(crate) fn roots(&self) -> &[TermId] {
        &self.roots
    }

    pub(crate) fn root_entries(&self) -> &[TermEntryStamp] {
        &self.root_entries
    }

    pub(crate) fn query_epoch(&self) -> &QueryAuthorityEpoch {
        &self.query_epoch
    }

    pub(crate) fn source_context(&self) -> &SourceContextStamp {
        &self.source_context
    }

    pub(crate) fn full_typed_query_sha256(&self) -> [u8; 32] {
        self.full_typed_query_sha256
    }

    pub(crate) fn declaration_context_sha256(&self) -> [u8; 32] {
        self.declaration_context_sha256
    }

    pub(crate) fn declarations(&self) -> &[NativeDeclarationBinding] {
        &self.declarations
    }

    pub(crate) fn free_variables(&self) -> &[NativeFreeVariableBinding] {
        &self.free_variables
    }

    pub(crate) fn checker_metadata_generation(&self) -> u64 {
        self.checker_metadata_generation
    }

    pub(crate) fn scope_depth(&self) -> usize {
        self.scope_depth
    }

    pub(crate) fn is_current_after_proof_growth(&self, executor: &Executor) -> bool {
        let Some((epoch, source, roots)) =
            executor.bounded_plain_unsat_query_scope(MAX_NATIVE_SOURCE_ROOTS)
        else {
            return false;
        };
        self.query_epoch.is_same_epoch(&epoch)
            && self.checker_metadata_generation
                == executor.ctx.terms.checker_visible_metadata_generation()
            && self.source_context == source
            && self.scope_depth == executor.ctx.scope_depth()
            && self.roots.as_ref() == roots
            && self.root_entries.iter().copied().eq(roots
                .iter()
                .filter_map(|&root| executor.ctx.terms.entry_stamp(root)))
            && self
                .source_entries
                .iter()
                .all(|&(term, entry)| executor.ctx.terms.entry_stamp(term) == Some(entry))
            && self.free_variables.iter().all(|variable| {
                executor.ctx.terms.entry_stamp(variable.term) == Some(variable.entry)
                    && executor.ctx.terms.sort(variable.term) == &variable.sort
            })
            && executor
                .proof_problem_assertion_provenance
                .as_ref()
                .is_some_and(|provenance| {
                    provenance.original_problem_assertions.as_slice() == roots
                })
            && self.datatypes.is_current(executor)
            && codec::declarations_are_current(executor, &self.declarations, &self.datatypes)
    }

    /// Diagnostic evidence survives result revocation only as data for the
    /// same actual issued attempt. This does not restore the revoked result,
    /// its proof accessor, or its public-query admission permit.
    fn captured_input_is_current(&self, executor: &Executor) -> bool {
        self.query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context == executor.ctx.source_context_stamp()
            && self.checker_metadata_generation
                == executor.ctx.terms.checker_visible_metadata_generation()
            && self.scope_depth == executor.ctx.scope_depth()
            && self
                .source_entries
                .iter()
                .all(|&(term, entry)| executor.ctx.terms.entry_stamp(term) == Some(entry))
            && self.free_variables.iter().all(|variable| {
                executor.ctx.terms.entry_stamp(variable.term) == Some(variable.entry)
                    && executor.ctx.terms.sort(variable.term) == &variable.sort
            })
            && self.datatypes.is_current(executor)
            && codec::declarations_are_current(executor, &self.declarations, &self.datatypes)
    }

    /// Admit the captured payload and the live lookup scans before checking
    /// currency. This grants no new source ownership and refreshes no epoch.
    pub(crate) fn is_current_with_progress(
        &self,
        executor: &Executor,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<bool> {
        let mut control = codec::Control::new(progress);
        let symbol_bound = executor.ctx.symbols_iter().size_hint().1?;
        let fanout = self
            .declarations
            .len()
            .checked_add(self.datatypes.signatures().len())?
            .checked_add(1)?;
        control.charge(
            symbol_bound
                .checked_mul(fanout)?
                .checked_add(self.source_entries.len())?
                .checked_add(self.roots.len())?,
            0,
        )?;
        for binding in &self.declarations {
            control.charge(
                binding
                    .name
                    .len()
                    .checked_add(binding.symbol.name().len())?,
                0,
            )?;
            codec::validate_sort(&binding.range, 32, false, &mut control)?;
            for sort in &binding.domain {
                codec::validate_sort(sort, 32, false, &mut control)?;
            }
        }
        for signature in self.datatypes.signatures() {
            control.charge(signature.identity.len(), 0)?;
            codec::validate_sort(&signature.result_sort, 32, false, &mut control)?;
            for sort in &signature.argument_sorts {
                codec::validate_sort(sort, 32, false, &mut control)?;
            }
        }
        let current = self.captured_input_is_current(executor);
        control.charge(0, 0)?;
        Some(current)
    }

    /// Portable native evidence cannot invent an undeclared function or adopt
    /// a spelling as a datatype member. Existing subset presentation keeps its
    /// own admission path; this check is specific to full native transport.
    pub(crate) fn diagnostic_applications_are_declared_with_progress(
        &self,
        executor: &Executor,
        progress: &mut dyn FnMut(usize, usize) -> bool,
    ) -> Option<bool> {
        let mut control = codec::Control::new(progress);
        control.charge(1, 0)?;
        // v3/v4 term snapshots do not retain these native interpretation
        // switches. Do not let a fresh checker silently reinterpret an old
        // shadowed conversion as its builtin counterpart.
        if executor.ctx.terms.to_real_is_shadowed() || executor.ctx.terms.is_int_is_shadowed() {
            return Some(false);
        }
        for &(term, entry) in &self.source_entries {
            control.charge(1, 0)?;
            if executor.ctx.terms.entry_stamp(term) != Some(entry) {
                return Some(false);
            }
            if !self.diagnostic_application_matches(
                executor,
                executor.ctx.terms.get(term),
                executor.ctx.terms.sort(term),
                |child| {
                    executor
                        .ctx
                        .terms
                        .entry_stamp(child)
                        .map(|_| executor.ctx.terms.sort(child))
                },
                &mut control,
            )? {
                return Some(false);
            }
        }
        control.charge(0, 0)?;
        Some(true)
    }
}
