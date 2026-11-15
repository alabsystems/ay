// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use crate::counted_storage::try_reserve;

impl admitted::Policy for finalize::Counted<'_> {
    fn analysis_entry(&self, _: &Solver) -> AdmissionResult<()> {
        self.0.admit(8, 0)
    }

    fn analysis_clause(&self, s: &mut Solver, offset: usize) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        if s.arena.is_empty_clause(offset) {
            return Err(invalid(
                self.0,
                "counted ordinary analysis has an empty antecedent",
            ));
        }
        for &lit in s.arena.literals(offset) {
            self.analysis_literal(s, lit)?;
        }
        Ok(())
    }

    fn analysis_literal(&self, s: &Solver, lit: Literal) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        let Some(data) = s.var_data.get(lit.variable().index()) else {
            return Err(invalid(
                self.0,
                "counted ordinary literal is outside VarData",
            ));
        };
        if lit.0 as usize >= s.vals.len() || data.level as usize > s.num_vars {
            return Err(invalid(
                self.0,
                "counted ordinary literal/level is out of bounds",
            ));
        }
        Ok(())
    }

    fn analysis_mark(&self, s: &mut Solver, level: u32) -> AdmissionResult<()> {
        s.conflict.prepare_counted_ic3_seen(self.0)?;
        if level == 0 {
            return Ok(());
        }
        self.0.admit(2, 0)?;
        let required = level as usize + 1;
        let growth = required.saturating_sub(s.min.level_seen.len());
        if growth > 0 {
            self.0.admit(growth, 0)?;
            try_reserve(self.0, &mut s.min.level_seen, growth)?;
        }
        let count = s
            .min
            .level_seen
            .get(level as usize)
            .map_or(0, |entry| entry.count);
        if count == u32::MAX {
            return Err(invalid(
                self.0,
                "counted ordinary level occurrence overflow",
            ));
        }
        if count == 0 {
            self.0.admit(2, 0)?;
            try_reserve(self.0, &mut s.min.level_seen_to_clear, 1)?;
        }
        Ok(())
    }

    fn analysis_learned(&self, s: &mut Solver) -> AdmissionResult<()> {
        s.conflict.prepare_counted_ic3_learned(self.0)
    }

    fn analysis_bump(&self, s: &mut Solver, reference: ClauseRef) -> AdmissionResult<()> {
        side_effects::prepare_bump(s, reference, self.0)
    }

    fn analysis_otfs(&self) -> AdmissionResult<()> {
        Err(invalid(
            self.0,
            "selected ordinary OTFS mutation needs same-owner arena/watch/proof admission",
        ))
    }

    fn analysis_clear(&self, s: &mut Solver) -> AdmissionResult<()> {
        // Semantic bailout owns only retired results. Avoid the ordinary
        // residual-seen diagnostic callback during quiet counted retirement.
        self.0.admit(
            s.var_data
                .len()
                .saturating_add(s.min.level_seen_to_clear.len()),
            0,
        )?;
        s.conflict.retire_counted_standard(&mut s.var_data);
        s.clear_level_seen();
        Ok(())
    }

    fn analysis_resolution(&self, resolved: u32) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        if resolved == u32::MAX {
            return Err(invalid(
                self.0,
                "counted ordinary resolution counter overflow",
            ));
        }
        Ok(())
    }

    fn analysis_chain(
        &self,
        s: &mut Solver,
        id: u64,
        pivot: Option<Literal>,
    ) -> AdmissionResult<()> {
        s.conflict.prepare_counted_standard_chain(self.0)?;
        if let Some(pivot) = pivot {
            s.conflict.add_to_chain_with_pivot(id, pivot);
        } else {
            s.conflict.add_to_chain(id);
        }
        Ok(())
    }

    #[cfg(feature = "jit")]
    fn analysis_native(&self, s: &mut Solver, offset: usize) -> AdmissionResult<()> {
        self.0.admit(1, 0)?;
        let Some(native) = s.jit_conflict_processor.as_ref() else {
            return Err(invalid(
                self.0,
                "selected ordinary native processor disappeared",
            ));
        };
        if native.capacity() < s.num_vars || native.capacity() != s.jit_conflict_output.capacity() {
            return Err(invalid(
                self.0,
                "counted ordinary native output/compiled layout mismatch",
            ));
        }
        // Pay the actual selected native pass and constant header writes before
        // entering its non-callback transaction; Rust bookkeeping stays separate.
        let work = s
            .arena
            .len_of(offset)
            .checked_add(8)
            .ok_or_else(|| self.0.refuse(CountedAdmissionError::WorkExhausted))?;
        self.0.admit(work, 0)?;
        #[cfg(debug_assertions)]
        {
            self.0.admit(s.arena.len_of(offset).saturating_add(8), 0)?;
            if s.cold.debug_interp_output.capacity() < s.num_vars {
                s.cold
                    .debug_interp_output
                    .prepare_counted_resize(s.num_vars, self.0)?;
            }
        }
        Ok(())
    }

    #[cfg(all(feature = "jit", debug_assertions))]
    fn analysis_debug_flag(&self, s: &mut Solver) -> AdmissionResult<()> {
        self.0.admit(3, 0)?; // save/clear and eventual retained-entry disposal
        try_reserve(self.0, &mut s.cold.debug_jit_flags_buf, 1)
    }
}
