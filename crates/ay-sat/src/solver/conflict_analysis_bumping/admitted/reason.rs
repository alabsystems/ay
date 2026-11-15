// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Solver {
    pub(in crate::solver) fn add_reason_literals_admitted<P: Policy>(
        &mut self,
        lit: Literal,
        depth: u32,
        added: &mut usize,
        limit: usize,
        p: &P,
    ) -> Result<(), P::Error> {
        p.reason_frame()?;
        if depth == 0 || *added >= limit {
            return Ok(());
        }
        let var = lit.variable().index();
        // Preserve ordinary chronological ghost handling BEFORE stale reasons.
        if !self.var_is_assigned(var) {
            return Ok(());
        }
        if let ReasonKind::BinaryLiteral(other) = self.var_reason_kind(var) {
            if self.cold.bump_reasons_kissat
                || ay_core::sat_ab_switches().bump_binary_reasons == Some(true)
            {
                self.bump_binary_reason_admitted(other, depth, added, limit, p)?;
            }
            return Ok(());
        }
        let Some(reason) = self.var_reason(var) else {
            return Ok(());
        };
        let offset = reason.0 as usize;
        if !self.cold.analysis_ticks_kissat || self.arena.len_of(offset) > 2 {
            let mode = usize::from(self.stable_mode);
            p.counter(self.search_ticks[mode], 1)?;
            self.search_ticks[mode] += 1;
        }
        if depth == 1 {
            return self.bump_leaf_reason_admitted(lit, offset, added, p);
        }
        for index in 0..self.arena.len_of(offset) {
            p.work(1)?;
            let reason_lit = self.arena.literal(offset, index);
            if reason_lit == lit || self.lit_val(reason_lit) >= 0 {
                continue;
            }
            let var = reason_lit.variable().index();
            let vd = self.var_data[var];
            if vd.is_seen() || vd.level == 0 {
                continue;
            }
            p.counter(*added as u64, 1)?;
            p.analysis_seen(&mut self.conflict)?;
            self.conflict.mark_seen(var, &mut self.var_data);
            *added += 1;
            if *added < limit {
                self.add_reason_literals_admitted(
                    reason_lit.negated(),
                    depth - 1,
                    added,
                    limit,
                    p,
                )?;
            }
        }
        Ok(())
    }

    fn bump_leaf_reason_admitted<P: Policy>(
        &mut self,
        lit: Literal,
        offset: usize,
        added: &mut usize,
        p: &P,
    ) -> Result<(), P::Error> {
        let Self {
            ref arena,
            ref mut conflict,
            ref mut var_data,
            ref vals,
            ..
        } = *self;
        // Preserve the actual slice walk and its deliberate lack of a
        // mid-clause analyzed-limit break (CaDiCaL analyze.cpp:342-381).
        for &reason in arena.literals(offset) {
            p.work(1)?;
            if reason == lit || ay_prefetch::val_at(vals, reason.index()) >= 0 {
                continue;
            }
            let var = reason.variable().index();
            let vd = var_data[var];
            if vd.is_seen() || vd.level == 0 {
                continue;
            }
            p.counter(*added as u64, 1)?;
            p.analysis_seen(conflict)?;
            conflict.mark_seen(var, var_data);
            *added += 1;
        }
        Ok(())
    }

    fn bump_binary_reason_admitted<P: Policy>(
        &mut self,
        other: Literal,
        depth: u32,
        added: &mut usize,
        limit: usize,
        p: &P,
    ) -> Result<(), P::Error> {
        p.work(4)?;
        if !self.cold.bump_reasons_kissat && !self.cold.analysis_ticks_kissat {
            let mode = usize::from(self.stable_mode);
            p.counter(self.search_ticks[mode], 1)?;
            self.search_ticks[mode] += 1;
        }
        if self.lit_val(other) >= 0 {
            return Ok(());
        }
        let var = other.variable().index();
        let vd = self.var_data[var];
        if vd.is_seen() || vd.level == 0 {
            return Ok(());
        }
        p.counter(*added as u64, 1)?;
        p.analysis_seen(&mut self.conflict)?;
        self.conflict.mark_seen(var, &mut self.var_data);
        *added += 1;
        if depth > 1 && *added < limit {
            self.add_reason_literals_admitted(other.negated(), depth - 1, added, limit, p)?;
        }
        Ok(())
    }
}
