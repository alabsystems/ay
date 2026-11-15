// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn scan<P: Policy>(
    s: &mut Solver,
    w: &mut Walk,
    p: &P,
) -> Result<Option<Literal>, P::Error> {
    p.work(1)?;
    w.index = w.index.min(s.trail.len());
    while w.index > 0 {
        p.work(1)?;
        w.index -= 1;
        let lit = s.trail[w.index];
        p.analysis_literal(s, lit)?;
        let var = lit.variable().index();
        if s.conflict.is_seen(var, &s.var_data) && s.var_data[var].level == s.decision_level {
            w.pivot = Some(lit);
            return Ok(Some(lit));
        }
    }
    Ok(None)
}

pub(super) fn bailout<P: Policy>(
    s: &mut Solver,
    w: Walk,
    p: &P,
) -> Result<Option<ConflictResult>, P::Error> {
    p.counter(s.stats.trail_exhaustion_bailouts, 1)?;
    s.stats.trail_exhaustion_bailouts += 1;
    p.analysis_clear(s)?;
    s.cold.lrat_level0_vars_buf = w.level0;
    Ok(None)
}

pub(super) fn resolve<P: Policy>(
    s: &mut Solver,
    w: &mut Walk,
    pivot: Literal,
    p: &P,
) -> Result<bool, P::Error> {
    p.work(1)?;
    debug_assert!(s.lit_val(pivot) > 0);
    match s.var_reason_kind(pivot.variable().index()) {
        ReasonKind::Decision | ReasonKind::LazyTheory(_) => return Ok(false),
        ReasonKind::BinaryLiteral(lit) => {
            process::scalar_literal(s, w, lit, p, process::LiteralOrigin::BinaryReason)?;
            ticks(s, 1, p)?;
            p.analysis_resolution(w.resolved)?;
            w.resolved += 1;
            w.last_reason = None;
            w.resolvent_size = w.resolvent_size.saturating_sub(1);
            w.len = 0;
        }
        ReasonKind::Clause(reference) => {
            p.analysis_clause(s, reference.0 as usize)?;
            p.work(s.arena.len_of(reference.0 as usize))?;
            debug_assert!(
                s.arena.literals(reference.0 as usize).contains(&pivot)
                    || s.stats.otfs_strengthened > 0
            );
            debug_assert!(!s.arena.is_empty_clause(reference.0 as usize));
            debug_assert!(s.arena.len_of(reference.0 as usize) >= 1);
            p.analysis_bump(s, reference)?;
            if triage_enabled() {
                TRIAGE_ANTECEDENTS.with(|buf| buf.borrow_mut().push(reference.0));
            }
            s.mark_streaming_core(reference);
            ticks(s, 1, p)?;
            if s.cold.lrat_enabled {
                let id = s.clause_id(reference);
                if id != 0 {
                    p.analysis_chain(s, id, Some(pivot))?;
                }
            }
            p.analysis_resolution(w.resolved)?;
            w.resolved += 1;
            w.last_reason = Some(reference);
            w.resolvent_size = w.resolvent_size.saturating_sub(1);
            w.offset = reference.0 as usize;
            w.len = s.arena.len_of(w.offset);
        }
    }
    Ok(true)
}
