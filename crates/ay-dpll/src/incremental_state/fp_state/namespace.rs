// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked frontiers for the fixed-offset, interleaved persistent namespace.

use super::{IncrementalFpState, UnknownOrigin};

const LIMIT: u32 = i32::MAX as u32;
const REFUSAL: UnknownOrigin = UnknownOrigin::DeterministicResourceBudget;

struct Frontiers {
    tseitin: u32,
    fp: u32,
    offset: u32,
    has_offset: bool,
    sat: u32,
}

impl Frontiers {
    fn total(&self) -> Result<u32, UnknownOrigin> {
        let tseitin = self.tseitin.checked_sub(1).ok_or(REFUSAL)?;
        let fp = self.fp.checked_sub(1).ok_or(REFUSAL)?;
        let fp_end = self.offset.checked_add(fp).ok_or(REFUSAL)?;
        let total = tseitin.max(fp_end).max(self.sat);
        if total > LIMIT {
            return Err(REFUSAL);
        }
        Ok(total)
    }

    fn sync_tseitin(&mut self) -> Result<(), UnknownOrigin> {
        self.total()?;
        let mut next = self.tseitin.max(self.sat.checked_add(1).ok_or(REFUSAL)?);
        if self.has_offset {
            next = next.max(self.offset.checked_add(self.fp).ok_or(REFUSAL)?);
        }
        self.tseitin = next;
        self.total()?;
        Ok(())
    }

    fn sync_fp(&mut self) -> Result<(), UnknownOrigin> {
        self.total()?;
        // Subtraction is clamped at one because a low Tseitin/selector
        // frontier may lie entirely below the frozen offset.
        let above_tseitin = self.tseitin.saturating_sub(self.offset).max(1);
        let above_sat = self
            .sat
            .checked_add(1)
            .ok_or(REFUSAL)?
            .saturating_sub(self.offset)
            .max(1);
        self.fp = self.fp.max(above_tseitin).max(above_sat);
        self.total()?;
        Ok(())
    }
}

impl IncrementalFpState {
    fn frontiers(&self, solver_total: usize) -> Result<Frontiers, UnknownOrigin> {
        if let Some(origin) = self.pending_namespace_refusal {
            return Err(origin);
        }
        // Both cache and mirror must be valid, even when max would hide zero.
        self.next_fp_var.checked_sub(1).ok_or(REFUSAL)?;
        self.fp_cache.next_var.checked_sub(1).ok_or(REFUSAL)?;
        let offset = u32::try_from(self.fp_var_offset.unwrap_or(0)).map_err(|_| REFUSAL)?;
        let owned_total = self
            .persistent_sat
            .as_ref()
            .map_or(0, |sat| sat.total_num_vars());
        let sat = u32::try_from(solver_total.max(owned_total)).map_err(|_| REFUSAL)?;
        let frontiers = Frontiers {
            tseitin: self.tseitin_state.next_var,
            fp: self.next_fp_var.max(self.fp_cache.next_var),
            offset,
            has_offset: self.fp_var_offset.is_some(),
            sat,
        };
        frontiers.total()?;
        Ok(frontiers)
    }

    /// Current combined occupied count INCLUDING `additional_selectors`.
    /// Use zero for SAT allocation; use pending pushes only for preflight,
    /// since each subsequent SAT push allocates its own selector.
    pub(crate) fn checked_total_vars(
        &self,
        solver_total: usize,
        additional_selectors: usize,
    ) -> Result<usize, UnknownOrigin> {
        let total = self.frontiers(solver_total)?.total()? as usize;
        let total = total.checked_add(additional_selectors).ok_or(REFUSAL)?;
        if total > LIMIT as usize {
            return Err(REFUSAL);
        }
        Ok(total)
    }

    /// Run first: jump above actual SAT selectors and the fixed-offset FP
    /// range. Failure leaves all state frontiers untouched.
    pub(crate) fn sync_tseitin_next_var(&mut self) -> Result<(), UnknownOrigin> {
        let mut next = self.frontiers(0)?;
        next.sync_tseitin()?;
        self.tseitin_state.next_var = next.tseitin;
        Ok(())
    }

    /// Run second: subtract the fixed offset to retain the tight fixed point,
    /// rather than adding that offset again on every check-sat.
    pub(crate) fn sync_next_fp_var(&mut self) -> Result<(), UnknownOrigin> {
        let mut next = self.frontiers(0)?;
        next.sync_fp()?;
        self.next_fp_var = next.fp;
        self.fp_cache.next_var = next.fp;
        Ok(())
    }

    /// Atomically resynchronize both frontiers against a temporarily detached
    /// SAT solver's actual total, including its freshly allocated selectors.
    pub(crate) fn sync_with_solver_total(&mut self, total: usize) -> Result<(), UnknownOrigin> {
        let mut next = self.frontiers(total)?;
        next.sync_tseitin()?;
        next.sync_fp()?;
        self.tseitin_state.next_var = next.tseitin;
        self.next_fp_var = next.fp;
        self.fp_cache.next_var = next.fp;
        Ok(())
    }
}
