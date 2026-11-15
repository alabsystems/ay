// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Ordinary 1UIP conflict analysis, shared with original-owner admission.

use super::*;
#[cfg(test)]
use crate::kani_compat::det_hash_set_new;

pub(in crate::solver) mod admitted;
mod counted;

// Soundness-triage antecedents retain their existing per-thread recorder.
pub(super) fn triage_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().ab_triage_clause.is_some())
}
thread_local! {
    pub(super) static TRIAGE_ANTECEDENTS: std::cell::RefCell<Vec<u32>> =
        const { std::cell::RefCell::new(Vec::new()) };
}

impl Solver {
    fn standard_otfs_asserting_literal(forced: Option<Literal>) -> Literal {
        forced.expect("BUG: OTFS Branch B: no current-level literal found")
    }

    /// The normal route keeps its selected native/scalar, chrono, OTFS and
    /// finalization behavior. A semantic bailout still requests level zero.
    pub(super) fn analyze_conflict(&mut self, conflict_ref: ClauseRef) -> Option<ConflictResult> {
        match admitted::run(
            self,
            conflict_ref,
            &conflict_analysis_finalize::admitted::Ordinary,
        ) {
            Ok(result) => result,
            Err(never) => match never {},
        }
    }

    #[cfg(feature = "jit")]
    pub(in crate::solver) fn standard_native_available(&self) -> bool {
        self.jit_conflict_processor
            .as_ref()
            .is_some_and(|processor| processor.capacity() >= self.var_data.len())
    }

    #[cfg(feature = "jit")]
    fn process_standard_native<P: admitted::Policy>(
        &mut self,
        offset: usize,
        pivot: Option<Literal>,
        _policy: &P,
    ) -> Result<(), P::Error> {
        let Some(processor) = self.jit_conflict_processor.as_ref() else {
            return Ok(());
        };
        let lits = self.arena.literals(offset);
        let skip = pivot.map_or(u32::MAX, |lit| lit.0);
        // SAFETY: ordinary analysis supplies valid arena literals and VarData/
        // vals buffers; the counted policy additionally checks every index and
        // the compiled/output capacities before this same kernel is called.
        // The exclusive solver borrow forbids concurrent buffer mutation.
        #[allow(unsafe_code)]
        unsafe {
            processor.process_literals(
                bytemuck::cast_slice(lits),
                self.var_data.as_mut_ptr().cast::<u8>(),
                self.decision_level,
                skip,
                &mut self.jit_conflict_output,
                self.vals.as_ptr(),
            );
        }
        self.stats.sat_conflict_analysis_native_applications = self
            .stats
            .sat_conflict_analysis_native_applications
            .saturating_add(1);
        #[cfg(debug_assertions)]
        self.crosscheck_standard_native(offset, skip, _policy)?;
        Ok(())
    }

    #[cfg(all(feature = "jit", debug_assertions))]
    fn crosscheck_standard_native<P: admitted::Policy>(
        &mut self,
        offset: usize,
        skip: u32,
        policy: &P,
    ) -> Result<(), P::Error> {
        let seen = self.jit_conflict_output.seen_count() as usize;
        self.cold.debug_jit_flags_buf.clear();
        for at in 0..seen {
            policy.analysis_debug_flag(self)?;
            let var = self.jit_conflict_output.seen_var(at) as usize;
            let flags = self.var_data[var].flags;
            self.cold.debug_jit_flags_buf.push((var, flags));
            self.var_data[var].flags = flags & !VarData::FLAG_SEEN_PUB;
        }
        let num_vars = self.var_data.len();
        if self.cold.debug_interp_output.capacity() < num_vars {
            self.cold.debug_interp_output.resize(num_vars);
        } else {
            self.cold.debug_interp_output.reset();
        }
        // SAFETY: this is the original debug cross-check of the same valid
        // arena literals and exclusive VarData/vals buffers. The interpreter
        // output is sized above before any writes; counted admission reserves
        // and pays that actual resize before entering the native transaction.
        #[allow(unsafe_code)]
        unsafe {
            ay_jit::conflict_jit::process_literals_interpreter(
                bytemuck::cast_slice(self.arena.literals(offset)),
                self.var_data.as_mut_ptr().cast::<u8>(),
                self.decision_level,
                skip,
                &mut self.cold.debug_interp_output,
                self.vals.as_ptr(),
            );
        }
        debug_assert_eq!(
            self.jit_conflict_output.counter(),
            self.cold.debug_interp_output.counter(),
            "BUG(#8550): JIT/interpreter counter mismatch",
        );
        debug_assert_eq!(
            self.jit_conflict_output.learned_count(),
            self.cold.debug_interp_output.learned_count(),
            "BUG(#8550): JIT/interpreter learned_count mismatch",
        );
        debug_assert_eq!(
            self.jit_conflict_output.resolvent_size(),
            self.cold.debug_interp_output.resolvent_size(),
            "BUG(#8550): JIT/interpreter resolvent_size mismatch",
        );
        Ok(())
    }

    /// IDs in the original range still require original-ledger membership.
    #[inline(always)]
    pub(super) fn mark_streaming_core(&mut self, clause_ref: ClauseRef) {
        let num_originals = self.cold.streaming_core_num_originals;
        if num_originals == 0 {
            return;
        }
        let id = self.clause_id(clause_ref);
        if id > 0 && id <= num_originals && self.is_original_clause_id(id) {
            if let Some(ref mut bitmap) = self.cold.streaming_core {
                bitmap[(id - 1) as usize] = true;
            }
        }
    }
}

#[cfg(test)]
#[path = "conflict_analysis_tests.rs"]
mod tests;
