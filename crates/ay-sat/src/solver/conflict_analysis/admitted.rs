// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! The actual ordinary first-UIP walk (CaDiCaL analyze.cpp:944-1136).
//! Fallible hooks precede selected work; ordinary policy is infallible.

use super::*;
use crate::solver::conflict_analysis_finalize::admitted as finalize;
use crate::solver_log::solver_log;
use std::convert::Infallible;

mod cursor;
mod otfs;
mod process;
mod reasons;

pub(super) trait Policy: finalize::Policy {
    fn analysis_entry(&self, s: &Solver) -> Result<(), Self::Error>;
    fn analysis_clause(&self, s: &mut Solver, offset: usize) -> Result<(), Self::Error>;
    fn analysis_literal(&self, s: &Solver, lit: Literal) -> Result<(), Self::Error>;
    fn analysis_mark(&self, s: &mut Solver, level: u32) -> Result<(), Self::Error>;
    fn analysis_learned(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn analysis_bump(&self, s: &mut Solver, reference: ClauseRef) -> Result<(), Self::Error>;
    fn analysis_otfs(&self) -> Result<(), Self::Error>;
    fn analysis_clear(&self, s: &mut Solver) -> Result<(), Self::Error>;
    fn analysis_resolution(&self, resolved: u32) -> Result<(), Self::Error>;
    fn analysis_chain(
        &self,
        s: &mut Solver,
        id: u64,
        pivot: Option<Literal>,
    ) -> Result<(), Self::Error>;
    #[cfg(feature = "jit")]
    fn analysis_native(&self, s: &mut Solver, offset: usize) -> Result<(), Self::Error>;
    #[cfg(all(feature = "jit", debug_assertions))]
    fn analysis_debug_flag(&self, s: &mut Solver) -> Result<(), Self::Error>;
}

impl Policy for finalize::Ordinary {
    fn analysis_entry(&self, _: &Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn analysis_clause(&self, _: &mut Solver, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    fn analysis_literal(&self, _: &Solver, _: Literal) -> Result<(), Infallible> {
        Ok(())
    }
    fn analysis_mark(&self, _: &mut Solver, _: u32) -> Result<(), Infallible> {
        Ok(())
    }
    fn analysis_learned(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
    fn analysis_bump(&self, s: &mut Solver, reference: ClauseRef) -> Result<(), Infallible> {
        s.bump_clause(reference);
        Ok(())
    }
    fn analysis_otfs(&self) -> Result<(), Infallible> {
        Ok(())
    }
    fn analysis_clear(&self, s: &mut Solver) -> Result<(), Infallible> {
        s.conflict.clear(&mut s.var_data);
        s.clear_level_seen();
        Ok(())
    }
    fn analysis_resolution(&self, _: u32) -> Result<(), Infallible> {
        Ok(())
    }
    fn analysis_chain(
        &self,
        s: &mut Solver,
        id: u64,
        pivot: Option<Literal>,
    ) -> Result<(), Infallible> {
        if let Some(pivot) = pivot {
            s.conflict.add_to_chain_with_pivot(id, pivot);
        } else {
            s.conflict.add_to_chain(id);
        }
        Ok(())
    }
    #[cfg(feature = "jit")]
    fn analysis_native(&self, _: &mut Solver, _: usize) -> Result<(), Infallible> {
        Ok(())
    }
    #[cfg(all(feature = "jit", debug_assertions))]
    fn analysis_debug_flag(&self, _: &mut Solver) -> Result<(), Infallible> {
        Ok(())
    }
}

pub(super) struct Walk {
    counter: u32,
    ghost_dropped: bool,
    invalid_cursor: bool,
    pivot: Option<Literal>,
    index: usize,
    resolved: u32,
    resolvent_size: u32,
    antecedent_size: u32,
    last_reason: Option<ClauseRef>,
    conflict_size: u32,
    conflict: ClauseRef,
    offset: usize,
    len: usize,
    level0: Vec<usize>,
}

enum Progress {
    Continue,
    Restart,
    Complete(ConflictResult),
}

pub(super) fn run<P: Policy>(
    s: &mut Solver,
    reference: ClauseRef,
    policy: &P,
) -> Result<Option<ConflictResult>, P::Error> {
    policy.analysis_entry(s)?;
    solver_log!(s, "analyze conflict clause {}", reference.0);
    policy.counter(s.stats.trail_at_conflict_sum, s.trail.len() as u64)?;
    policy.counter(s.stats.level_at_conflict_sum, u64::from(s.decision_level))?;
    s.stats.trail_at_conflict_sum += s.trail.len() as u64;
    s.stats.level_at_conflict_sum += u64::from(s.decision_level);
    if s.cold.lazy_materialization_failed {
        policy.counter(s.stats.trail_exhaustion_bailouts, 1)?;
        s.stats.trail_exhaustion_bailouts += 1;
        s.cold.lazy_materialization_failed = false;
        return Ok(None);
    }
    s.conflict.clear(&mut s.var_data);
    s.min.level_seen_flag_valid = s.min.level_seen_to_clear.is_empty();
    s.min.level_seen_repeated_non_uip = false;
    debug_assert_eq!(s.conflict.learned_count(), 0);
    debug_assert!(s.decision_level > 0);
    attribute(s, reference, policy)?;
    let mut state = initialize(s, reference, policy)?;
    loop {
        policy.work(1)?;
        state.antecedent_size = 1;
        process::clause(s, &mut state, policy)?;
        if state.invalid_cursor {
            return reasons::bailout(s, state, policy);
        }
        debug_assert_eq!(
            state.resolvent_size,
            state.counter + s.conflict.learned_count() as u32
        );
        if state.resolved == 0 {
            state.conflict_size = state.antecedent_size.saturating_sub(1);
        }
        match otfs::attempt(s, &mut state, policy)? {
            Progress::Continue => (),
            Progress::Restart => continue,
            Progress::Complete(result) => return Ok(Some(result)),
        }
        let Some(pivot) = reasons::scan(s, &mut state, policy)? else {
            return reasons::bailout(s, state, policy);
        };
        if state.counter == 0 {
            return reasons::bailout(s, state, policy);
        }
        state.counter -= 1;
        if state.counter == 0 {
            solver_log!(s, "1UIP: {}", pivot.to_dimacs());
            break;
        }
        if state.index == 0
            || !reasons::resolve(s, &mut state, pivot, policy)?
            || state.invalid_cursor
        {
            return reasons::bailout(s, state, policy);
        }
    }
    if state.ghost_dropped && s.proof_manager.is_some() {
        policy.counter(s.stats.trail_exhaustion_bailouts, 1)?;
        s.stats.trail_exhaustion_bailouts += 1;
        s.cold.lrat_level0_vars_buf = state.level0;
        return Ok(None);
    }
    let Some(uip) = state.pivot else {
        return reasons::bailout(s, state, policy);
    };
    sample_decision_relevance(s, policy)?;
    s.finalize_conflict_analysis_admitted(uip.negated(), state.level0, policy)
        .map(Some)
}

/// Sampled decision relevance: every 1024th conflict, count trail decisions
/// (one per decision level, at `trail_lim[level - 1]`) and how many of their
/// variables the analysis marked seen. Read-only measurement: it observes
/// trail/var_data state at analysis completion (before backtracking) and
/// writes only its own counters. Ordinary search choices are unchanged;
/// counted analysis prepays the O(level) scan before reading the trail.
/// Sampling limits that scan to once per 1024 conflicts. Split by mode
/// because focused/stable decisions-per-conflict
/// differ by more than 2x on trajectory-wall instances.
fn sample_decision_relevance<P: Policy>(s: &mut Solver, policy: &P) -> Result<(), P::Error> {
    if !s.num_conflicts.is_multiple_of(1024) {
        return Ok(());
    }
    // Admit the decision-level scan before its first trail/VarData/VSIDS read.
    policy.work(s.decision_level as usize)?;
    /// Bump-stamp age below which a decision variable counts as recently
    /// promoted by the branching heuristic (see solver_stats fields).
    const RECENT_BUMP_AGE: u64 = 4096;
    let mut decisions = 0u64;
    let mut relevant = 0u64;
    let mut decisions_recent = 0u64;
    let mut relevant_recent = 0u64;
    for level in 1..=s.decision_level {
        let pos = s.trail_lim[(level - 1) as usize];
        let lit = s.trail[pos];
        let var = lit.variable().index();
        decisions += 1;
        let seen = s.var_data[var].is_seen();
        if seen {
            relevant += 1;
        }
        if s.vsids.bump_age(lit.variable()) < RECENT_BUMP_AGE {
            decisions_recent += 1;
            relevant_recent += u64::from(seen);
        }
    }
    let decisions_stale = decisions - decisions_recent;
    let relevant_stale = relevant - relevant_recent;
    let analyzed = s.conflict.analyzed_vars().len() as u64;
    // Trail composition: admit the O(trail) scan before reading it.
    policy.work(s.trail.len())?;
    let trail_len = s.trail.len() as u64;
    let mut target_set = 0u64;
    let mut target_agree = 0u64;
    for lit in &s.trail {
        let target = s.target_phase[lit.variable().index()];
        if target != 0 {
            target_set += 1;
            target_agree += u64::from((target > 0) == lit.is_positive());
        }
    }
    if s.stable_mode {
        policy.counter(s.stats.sampled_conflicts_stable, 1)?;
        policy.counter(s.stats.sampled_decisions_stable, decisions)?;
        policy.counter(s.stats.sampled_relevant_stable, relevant)?;
        policy.counter(s.stats.sampled_decisions_recent_stable, decisions_recent)?;
        policy.counter(s.stats.sampled_relevant_recent_stable, relevant_recent)?;
        policy.counter(s.stats.sampled_decisions_stale_stable, decisions_stale)?;
        policy.counter(s.stats.sampled_relevant_stale_stable, relevant_stale)?;
        policy.counter(s.stats.sampled_analyzed_stable, analyzed)?;
        policy.counter(s.stats.sampled_trail_len_stable, trail_len)?;
        policy.counter(s.stats.sampled_target_set_stable, target_set)?;
        policy.counter(s.stats.sampled_target_agree_stable, target_agree)?;
        s.stats.sampled_conflicts_stable += 1;
        s.stats.sampled_decisions_stable += decisions;
        s.stats.sampled_relevant_stable += relevant;
        s.stats.sampled_decisions_recent_stable += decisions_recent;
        s.stats.sampled_relevant_recent_stable += relevant_recent;
        s.stats.sampled_decisions_stale_stable += decisions_stale;
        s.stats.sampled_relevant_stale_stable += relevant_stale;
        s.stats.sampled_analyzed_stable += analyzed;
        s.stats.sampled_trail_len_stable += trail_len;
        s.stats.sampled_target_set_stable += target_set;
        s.stats.sampled_target_agree_stable += target_agree;
    } else {
        policy.counter(s.stats.sampled_conflicts_focused, 1)?;
        policy.counter(s.stats.sampled_decisions_focused, decisions)?;
        policy.counter(s.stats.sampled_relevant_focused, relevant)?;
        policy.counter(s.stats.sampled_decisions_recent_focused, decisions_recent)?;
        policy.counter(s.stats.sampled_relevant_recent_focused, relevant_recent)?;
        policy.counter(s.stats.sampled_decisions_stale_focused, decisions_stale)?;
        policy.counter(s.stats.sampled_relevant_stale_focused, relevant_stale)?;
        policy.counter(s.stats.sampled_analyzed_focused, analyzed)?;
        policy.counter(s.stats.sampled_trail_len_focused, trail_len)?;
        policy.counter(s.stats.sampled_target_set_focused, target_set)?;
        policy.counter(s.stats.sampled_target_agree_focused, target_agree)?;
        s.stats.sampled_conflicts_focused += 1;
        s.stats.sampled_decisions_focused += decisions;
        s.stats.sampled_relevant_focused += relevant;
        s.stats.sampled_decisions_recent_focused += decisions_recent;
        s.stats.sampled_relevant_recent_focused += relevant_recent;
        s.stats.sampled_decisions_stale_focused += decisions_stale;
        s.stats.sampled_relevant_stale_focused += relevant_stale;
        s.stats.sampled_analyzed_focused += analyzed;
        s.stats.sampled_trail_len_focused += trail_len;
        s.stats.sampled_target_set_focused += target_set;
        s.stats.sampled_target_agree_focused += target_agree;
    }
    Ok(())
}

fn attribute<P: Policy>(s: &mut Solver, reference: ClauseRef, p: &P) -> Result<(), P::Error> {
    p.work(2)?;
    if s.cold.incremental_solve_count > 0 {
        let birth = s
            .cold
            .clause_birth_solve
            .get(reference.0 as usize)
            .copied()
            .unwrap_or(0);
        if u64::from(birth) < s.cold.incremental_solve_count {
            p.counter(s.stats.conflicts_from_prior_solve_clauses, 1)?;
            s.stats.conflicts_from_prior_solve_clauses += 1;
        }
    }
    if s.cold.active_assumption_count > 0 && s.decision_level <= s.cold.active_assumption_count {
        p.counter(s.stats.assumption_level_conflicts, 1)?;
        s.stats.assumption_level_conflicts += 1;
    }
    Ok(())
}

fn initialize<P: Policy>(s: &mut Solver, reference: ClauseRef, p: &P) -> Result<Walk, P::Error> {
    p.work(12)?;
    s.cold.lrat_level0_vars_buf.clear();
    let level0 = std::mem::take(&mut s.cold.lrat_level0_vars_buf);
    p.analysis_bump(s, reference)?;
    if triage_enabled() {
        TRIAGE_ANTECEDENTS.with(|buf| {
            let mut buf = buf.borrow_mut();
            buf.clear();
            buf.push(reference.0);
        });
    }
    s.note_analysis_conflict(reference);
    if s.cold.lrat_enabled {
        let id = s.clause_id(reference);
        if id != 0 {
            p.analysis_chain(s, id, None)?;
        }
    }
    let offset = reference.0 as usize;
    debug_assert!(s.arena.len_of(offset) >= 2);
    ticks(s, 1, p)?;
    Ok(Walk {
        counter: 0,
        ghost_dropped: false,
        invalid_cursor: false,
        pivot: None,
        index: s.trail.len(),
        resolved: 0,
        resolvent_size: 0,
        antecedent_size: 0,
        last_reason: None,
        conflict_size: 0,
        conflict: reference,
        offset,
        len: s.arena.len_of(offset),
        level0,
    })
}

fn ticks<P: Policy>(s: &mut Solver, amount: u64, p: &P) -> Result<(), P::Error> {
    p.work(1)?;
    if !s.cold.analysis_ticks_kissat {
        p.counter(s.search_ticks[usize::from(s.stable_mode)], amount)?;
    }
    s.charge_resolution_ticks(amount);
    Ok(())
}
