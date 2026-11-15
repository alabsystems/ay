// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Preserve ordinary OTFS selection, branch B, and branch C exactly.
//! Counted continuation refuses before the selected mutation transaction.

use super::*;

pub(super) fn attempt<P: Policy>(
    s: &mut Solver,
    w: &mut Walk,
    p: &P,
) -> Result<Progress, P::Error> {
    let Some(reason) = w.last_reason else {
        return Ok(Progress::Continue);
    };
    if s.cold.lrat_enabled
        || w.resolved == 0
        || w.antecedent_size <= 2
        || w.resolvent_size >= w.antecedent_size
        || (w.ghost_dropped && s.proof_manager.is_some())
    {
        return Ok(Progress::Continue);
    }
    p.counter(s.stats.otfs_candidates, 1)?;
    s.stats.otfs_candidates += 1;
    let Some(pivot) = w.pivot else {
        return Ok(Progress::Continue);
    };
    let lits = s.arena.literals(reason.0 as usize);
    p.work(lits.len())?;
    let open = lits
        .iter()
        .filter(|lit| {
            lit.variable() != pivot.variable()
                && s.var_data[lit.variable().index()].level == s.decision_level
        })
        .count();
    let watch_ok = lits.len() < 2 || s.lit_val(lits[0]) > 0 || s.lit_val(lits[1]) > 0;
    if open == 0 || !watch_ok {
        if open == 0 {
            p.counter(s.stats.otfs_blocked_open0, 1)?;
            s.stats.otfs_blocked_open0 += 1;
        }
        if !watch_ok {
            p.counter(s.stats.otfs_blocked_watch, 1)?;
            s.stats.otfs_blocked_watch += 1;
        }
        return Ok(Progress::Continue);
    }
    // No change to the configured/default heuristic. An unsupported selected
    // transaction is a terminal typed refusal, never an OTFS-off fallback.
    p.analysis_otfs()?;
    if !s.otfs_strengthen_from(w.conflict, reason, pivot) {
        s.stats.otfs_blocked_strengthen += 1;
        return Ok(Progress::Continue);
    }
    s.stats.otfs_subsumed += 1;
    if w.resolved == 1
        && w.conflict_size >= 2
        && w.resolvent_size < w.conflict_size
        && w.conflict != reason
    {
        s.stats.otfs_clause_subsumed += 1;
        s.otfs_subsume(reason, w.conflict);
    }
    w.conflict = reason;
    if open == 1 {
        // Branch B completes analysis; observe its seen set before retiring it.
        sample_decision_relevance(s, p)?;
        return Ok(Progress::Complete(asserting(s, w, reason)));
    }
    debug_assert!(open > 1);
    restart(s, w, reason);
    Ok(Progress::Restart)
}

fn asserting(s: &mut Solver, w: &mut Walk, reason: ClauseRef) -> ConflictResult {
    s.stats.otfs_branch_b += 1;
    let mut forced = None;
    let mut backtrack = 0;
    for &lit in s.arena.literals(reason.0 as usize) {
        let level = s.var_data[lit.variable().index()].level;
        if level == s.decision_level {
            debug_assert!(forced.is_none());
            forced = Some(lit);
        } else if level > backtrack {
            backtrack = level;
        }
    }
    // open==1 was computed over this strengthened clause; ordinary OTFS
    // guarantees exactly one asserting literal in branch B.
    let asserting = Solver::standard_otfs_asserting_literal(forced);
    debug_assert_eq!(
        s.var_data[asserting.variable().index()].level,
        s.decision_level
    );
    s.conflict.clear(&mut s.var_data);
    s.clear_level_seen();
    s.conflict.set_asserting_literal(asserting);
    for at in 0..s.arena.len_of(reason.0 as usize) {
        let lit = s.arena.literal_at(reason.0 as usize, at);
        if lit.variable() != asserting.variable() {
            s.conflict.add_to_learned(lit);
        }
    }
    let lbd = s.conflict.compute_lbd(&s.var_data);
    let mut result = s.conflict.get_result(backtrack, lbd);
    crate::conflict::reorder_for_watches(&mut result.learned_clause, &s.var_data, backtrack);
    result.otfs_driving_clause = Some(reason);
    s.cold.lrat_level0_vars_buf = std::mem::take(&mut w.level0);
    result
}

fn restart(s: &mut Solver, w: &mut Walk, reason: ClauseRef) {
    s.stats.otfs_branch_c += 1;
    s.conflict.clear(&mut s.var_data);
    s.clear_level_seen();
    w.counter = 0;
    w.pivot = None;
    w.index = s.trail.len();
    w.resolved = 0;
    w.resolvent_size = 0;
    w.level0.clear();
    w.last_reason = None;
    s.bump_clause(reason);
    s.mark_streaming_core(reason);
    if s.cold.lrat_enabled {
        let id = s.clause_id(reason);
        if id != 0 {
            s.conflict.add_to_chain(id);
        }
    }
    w.offset = reason.0 as usize;
    w.len = s.arena.len_of(w.offset);
}
