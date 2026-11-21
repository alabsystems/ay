// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One cumulative owner for the immutable input/proof observations of a check.

use super::*;
use crate::api::{NativeReplayExportError, NativeReplayMetadata};
use ay_core::{term::TermEntryStamp, TermId};
use ay_frontend::SourceContextStamp;

struct IssuedInput {
    json: String,
    context: SourceContextStamp,
    roots: Vec<TermId>,
    entries: Vec<TermEntryStamp>,
    scope_depth: usize,
}

impl IssuedInput {
    fn capture(
        solver: &Solver,
        budget: &mut NativeReplayExportBudget,
        control: &mut Control<'_>,
    ) -> Result<Option<Self>, ProofCheckError> {
        let ctx = solver.executor.context();
        let count = ctx.assertions.len();
        if count == 0 || count > crate::executor::MAX_NATIVE_SOURCE_ROOTS {
            return Ok(None);
        }
        let bytes = count
            .checked_mul(std::mem::size_of::<TermId>() + std::mem::size_of::<TermEntryStamp>())
            .ok_or(ProofCheckError::ResourceLimit)?;
        // Validate insertion provenance through borrows, then reserve before
        // copying the complete aligned stack. No unbounded Vec::clone path.
        control.charge(count, bytes)?;
        if !ctx.native_authored_originals_match_bounded(&ctx.assertions, count) {
            return Ok(None);
        }
        let mut roots = Vec::new();
        roots
            .try_reserve_exact(count)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        roots.extend_from_slice(&ctx.assertions);
        let mut entries = Vec::new();
        entries
            .try_reserve_exact(count)
            .map_err(|_| ProofCheckError::ResourceLimit)?;
        for &root in &roots {
            control.charge(1, 0)?;
            let Some(entry) = ctx.terms.entry_stamp(root) else {
                return Ok(None);
            };
            entries.push(entry);
        }
        let context = ctx.source_context_stamp();
        let scope_depth = ctx.scope_depth();
        let json = match solver.try_export_native_replay_input_json(
            &NativeReplayMetadata::default(),
            budget,
            &mut |w, b| control.charge(w, b).is_ok(),
        ) {
            Ok(json) => json,
            Err(
                NativeReplayExportError::Limit { .. }
                | NativeReplayExportError::Cancelled
                | NativeReplayExportError::Allocation,
            ) => return Err(ProofCheckError::ResourceLimit),
            // Unsupported/malformed input is not given diagnostic custody.
            Err(_) => return Ok(None),
        };
        control.charge(count, 0)?;
        if ctx.source_context_stamp() != context
            || ctx.scope_depth() != scope_depth
            || !roots
                .iter()
                .zip(&entries)
                .all(|(&id, &entry)| ctx.terms.entry_stamp(id) == Some(entry))
        {
            return Ok(None);
        }
        Ok(Some(Self {
            json,
            context,
            roots,
            entries,
            scope_depth,
        }))
    }

    fn matches(
        &self,
        source: &NativeProofSourceScope,
        control: &mut Control<'_>,
    ) -> Result<bool, ProofCheckError> {
        control.charge(self.roots.len(), 0)?;
        Ok(self.context == *source.source_context()
            && self.scope_depth == source.scope_depth()
            && self.roots == source.roots()
            && self.entries == source.root_entries())
    }
}

pub(super) struct Transaction<'c, 'p, 'b> {
    token: SolverCacheToken,
    deadline: Instant,
    budget: &'b mut NativeReplayExportBudget,
    control: &'c mut Control<'p>,
    input: Option<Result<Option<IssuedInput>, ProofCheckError>>,
    pending: Option<Result<Option<NativeQueryProofEnvelope>, ProofCheckError>>,
}

impl<'c, 'p, 'b> Transaction<'c, 'p, 'b> {
    pub(super) fn new(
        token: SolverCacheToken,
        deadline: Instant,
        budget: &'b mut NativeReplayExportBudget,
        control: &'c mut Control<'p>,
    ) -> Self {
        Self {
            token,
            deadline,
            budget,
            control,
            input: None,
            pending: None,
        }
    }

    pub(super) fn finish(self) -> Result<Option<NativeQueryProofEnvelope>, ProofCheckError> {
        // Input refusal stays final even when no native refutation was produced.
        if let Some(Err(error)) = self.input {
            return Err(error);
        }
        self.pending.transpose().map(Option::flatten)
    }

    fn retain(
        &mut self,
        executor: &crate::executor::Executor,
        input: IssuedInput,
    ) -> Result<Option<NativeQueryProofEnvelope>, ProofCheckError> {
        let Some(snapshot) =
            executor.capture_native_diagnostic_snapshot_with_progress(&mut |w, b| {
                self.control.charge(w, b).is_ok()
            })?
        else {
            return Ok(None);
        };
        if !input.matches(&snapshot.source, self.control)? {
            return Ok(None);
        }
        let binding = NativeQueryBinding {
            solver: self.token.clone(),
            source: snapshot.source,
        };
        let capture = capture_strict_retained_bundle_with_resource_control(
            snapshot.proof,
            self.deadline,
            &mut |w, b| self.control.charge(w, b).is_ok(),
        )?;
        let first = capture.first_check();
        if !first.quality.is_complete()
            || first.assume_terms.is_empty()
            || !self
                .control
                .all_ids_in(&first.assume_terms, binding.source.roots())?
            || !binding
                .source
                .is_current_with_progress(executor, &mut |w, b| self.control.charge(w, b).is_ok())
                .ok_or(ProofCheckError::ResourceLimit)?
        {
            return Ok(None);
        }
        let (proof, second) = capture
            .finish_exact_with_resource_control(&mut |w, b| self.control.charge(w, b).is_ok())?;
        if !second.quality.is_complete()
            || second.assume_terms.is_empty()
            || !self
                .control
                .all_ids_in(&second.assume_terms, proof.obligation_assertions())?
            || !self
                .control
                .all_ids_in(proof.obligation_assertions(), &second.assume_terms)?
            || !binding
                .source
                .is_current_with_progress(executor, &mut |w, b| self.control.charge(w, b).is_ok())
                .ok_or(ProofCheckError::ResourceLimit)?
        {
            return Ok(None);
        }
        Ok(Some(NativeQueryProofEnvelope {
            binding,
            proof,
            input_json: Some(input.json),
        }))
    }
}

impl NativeQueryObservation for Transaction<'_, '_, '_> {
    fn deadline(&self) -> Instant {
        self.deadline
    }

    fn input(&mut self, solver: &Solver) {
        if self.input.is_some() || self.pending.is_some() {
            self.pending = Some(Err(ProofCheckError::ResourceLimit));
            return;
        }
        self.input = Some(IssuedInput::capture(solver, self.budget, self.control));
    }

    fn proof(&mut self, executor: &crate::executor::Executor) {
        if self.pending.is_some() {
            return;
        }
        let result = match self.input.take() {
            Some(Ok(Some(input))) => self.retain(executor, input),
            Some(Err(error)) => Err(error),
            _ => Ok(None),
        };
        self.pending = Some(result);
    }
}
