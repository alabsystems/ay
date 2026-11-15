// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(in crate::solver) fn prepare_scope(
    s: &mut Solver,
    owner: &CountedAdmission,
) -> AdmissionResult<()> {
    owner.admit(80, 0)?; // fixed quiet cleanup, including every Reap bucket
    if s.min.minimize_flags.len() < s.num_vars
        || s.min.minimize_level_seen.len() <= s.decision_level as usize
        || !s.min.minimize_to_clear.is_empty()
        || !s.min.minimize_levels_to_clear.is_empty()
        || !s.conflict.clause_buf_mut().is_empty()
        || !s.ws_shrink_entries.is_empty()
        || !s.ws_shrink_result.is_empty()
        || !s.ws_shrink_block_lits.is_empty()
        || !s.ws_shrink_chain.is_empty()
        || !s.min.shrink_walked.is_empty()
        || !s.reap.is_empty()
        || !s.bump_order_sort_buf.is_empty()
        || !s.min.lrat_to_clear.is_empty()
    {
        return Err(invalid(
            owner,
            "ordinary finalization requires retired bounded scratch",
        ));
    }
    owner.admit(s.min.minimize_flags.len(), 0)?;
    if s.min.minimize_flags.iter().any(|&value| value != 0) {
        return Err(invalid(owner, "untracked ordinary minimization flags"));
    }
    owner.admit(s.min.minimize_level_seen.len(), 0)?;
    if s.min
        .minimize_level_seen
        .iter()
        .any(|&value| value != minimization_state::LevelSeen::EMPTY)
    {
        return Err(invalid(owner, "untracked ordinary minimization levels"));
    }
    Ok(())
}

impl Policy for Counted<'_> {
    fn root_phase(&self, s: &mut Solver, uip: Literal, roots: &[usize]) -> AdmissionResult<()> {
        conflict_analysis_lrat_unit_chain::admitted::finalize_roots(
            s,
            uip,
            roots,
            &conflict_analysis_minimize_lrat::root::Counted(self.0),
        )
    }
    fn enter_finalize(&self, s: &mut Solver, _roots: &[usize]) -> AdmissionResult<()> {
        self.0.admit(8, 0)?;
        if s.veripb_hints_active() {
            return Err(invalid(
                self.0,
                "ordinary counted VeriPB hint collection is not admitted",
            ));
        }
        s.conflict
            .learned_count()
            .checked_add(1)
            .ok_or_else(|| self.0.refuse(CountedAdmissionError::StorageExhausted))?;
        Ok(())
    }
    fn removed_snapshot(&self) -> AdmissionResult<()> {
        Err(invalid(
            self.0,
            "ordinary counted LRAT removal augmentation is not admitted",
        ))
    }
    fn reason_frame(&self) -> AdmissionResult<()> {
        self.0.admit(
            8,
            std::mem::size_of::<(Literal, u32, usize, usize, VarData)>(),
        )
    }
    fn analysis_seen(&self, conflict: &mut ConflictAnalyzer) -> AdmissionResult<()> {
        conflict.prepare_counted_ic3_seen(self.0)
    }
    fn scale(&self, value: usize, factor: usize, add: usize) -> AdmissionResult<usize> {
        self.0.admit(1, 0)?;
        value
            .checked_mul(factor)
            .and_then(|v| v.checked_add(add))
            .ok_or_else(|| invalid(self.0, "ordinary analysis counter overflow"))
    }
    fn activity(&self, s: &mut Solver, stage: ActivityStage) -> AdmissionResult<()> {
        let vars = s.conflict.analyzed_vars();
        s.vsids
            .analysis_activity_counted(vars, &s.vals, &s.bump_order_sort_buf, stage, self.0)
    }
    fn prepare_bump_order(&self, s: &mut Solver) -> AdmissionResult<()> {
        let count = s.conflict.analyzed_vars().len();
        self.0.admit(count, 0)?;
        // The ordinary extend has an exact-size iterator and reserves once.
        s.bump_order_sort_buf.clear();
        try_reserve(self.0, &mut s.bump_order_sort_buf, count)
    }
    fn sort_bumps(&self, values: &mut [(u64, usize)]) -> AdmissionResult<()> {
        sort::prepay_unstable(values.len(), self.0)?;
        <Ordinary as Policy>::sort_bumps(&Ordinary, values).map_err(|never| match never {})
    }
    fn result(&self, s: &mut Solver) -> AdmissionResult<()> {
        let len = s.conflict.learned_count();
        // Fused scan, debug tracked scan, independent debug backtrack scan,
        // watch reference scan and eventual private-result retirement.
        let scans = if cfg!(debug_assertions) { 7 } else { 2 };
        self.0.admit(self.scale(len, scans, 8)?, 0)?;
        s.conflict.prepare_counted_finalize_result(self.0)
    }
    fn learned_order(&self, values: &mut [Literal], data: &[VarData]) -> AdmissionResult<()> {
        sort::stable_by_level(values, data, self.0)
    }
    fn diagnostics(&self, len: usize) -> AdmissionResult<()> {
        #[cfg(debug_assertions)]
        {
            let pairs = self.scale(len, len, 0)?;
            self.0.admit(self.scale(len, 4, pairs)?, 0)?;
        }
        #[cfg(not(debug_assertions))]
        let _ = len;
        Ok(())
    }
    #[cfg(debug_assertions)]
    fn debug_copy(&self, values: &[Literal]) -> AdmissionResult<Vec<Literal>> {
        self.0.admit(values.len(), 0)?;
        let mut copy = crate::counted_storage::try_reserved_exact(self.0, values.len())?;
        copy.extend_from_slice(values);
        Ok(copy)
    }
}
