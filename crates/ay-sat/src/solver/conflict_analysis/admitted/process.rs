// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) enum LiteralOrigin {
    Antecedent,
    BinaryReason,
}

pub(super) fn clause<P: Policy>(s: &mut Solver, w: &mut Walk, p: &P) -> Result<(), P::Error> {
    p.analysis_clause(s, w.offset)?;
    #[cfg(feature = "jit")]
    if s.standard_native_available() {
        p.analysis_native(s, w.offset)?;
        s.process_standard_native(w.offset, w.pivot, p)?;
        native_bookkeeping(s, w, p)?;
        return Ok(());
    }
    ticks(s, w.len as u64, p)?;
    for at in 0..w.len {
        p.work(1)?;
        let lit = s.arena.literal_at(w.offset, at);
        if Some(lit) == w.pivot {
            continue;
        }
        scalar_literal(s, w, lit, p, LiteralOrigin::Antecedent)?;
    }
    Ok(())
}

// The binary-reason route shares classification, but does not contribute to
// antecedent_size: the following iteration is the ordinary empty-clause step.
pub(super) fn scalar_literal<P: Policy>(
    s: &mut Solver,
    w: &mut Walk,
    lit: Literal,
    p: &P,
    origin: LiteralOrigin,
) -> Result<(), P::Error> {
    p.analysis_literal(s, lit)?;
    let var = lit.variable().index();
    if s.ghost_guard_needed && s.lit_val(lit) >= 0 {
        w.ghost_dropped = true;
        return Ok(());
    }
    let level = s.var_data[var].level;
    debug_assert!(!s.ghost_guard_needed || s.lit_val(lit) < 0);
    if matches!(origin, LiteralOrigin::Antecedent) && level > 0 {
        w.antecedent_size += 1;
    }
    if !s.conflict.is_seen(var, &s.var_data) {
        p.analysis_mark(s, level)?;
        s.conflict.mark_seen(var, &mut s.var_data);
        debug_assert!(level <= s.decision_level);
        if level > 0 {
            s.track_level_seen(level, var);
        }
        if level == s.decision_level {
            w.counter += 1;
            cursor::extend(s, w, var, p)?;
        } else if level > 0 {
            p.analysis_learned(s)?;
            s.conflict.add_to_learned_tracked(lit, level);
        } else if s.cold.lrat_enabled {
            p.work(2)?;
            p.reserve(&mut w.level0, 1)?;
            w.level0.push(var);
        }
        if level > 0 {
            w.resolvent_size += 1;
        }
    }
    Ok(())
}

#[cfg(feature = "jit")]
fn native_bookkeeping<P: Policy>(s: &mut Solver, w: &mut Walk, p: &P) -> Result<(), P::Error> {
    p.work(3)?;
    w.counter += s.jit_conflict_output.counter();
    w.resolvent_size += s.jit_conflict_output.resolvent_size();
    let mut skipped = 0;
    for at in 0..s.jit_conflict_output.learned_count() as usize {
        p.work(1)?;
        let lit = Literal(s.jit_conflict_output.learned_lit(at));
        let var = lit.variable().index();
        if !s.var_is_assigned(var) {
            continue;
        }
        if s.lit_val(lit) >= 0 {
            skipped += 1;
            s.var_data[var].set_seen(false);
            continue;
        }
        p.analysis_learned(s)?;
        s.conflict
            .add_to_learned_tracked(lit, s.var_data[var].level);
    }
    w.resolvent_size = w.resolvent_size.saturating_sub(skipped);
    for at in 0..s.jit_conflict_output.seen_count() as usize {
        p.work(1)?;
        let var = s.jit_conflict_output.seen_var(at) as usize;
        if !s.var_is_assigned(var) || !s.var_data[var].is_seen() {
            continue;
        }
        let level = s.var_data[var].level;
        #[cfg(debug_assertions)]
        p.work(s.conflict.analyzed_vars().len())?;
        p.analysis_mark(s, level)?;
        s.conflict.register_jit_seen(var);
        debug_assert!(level <= s.decision_level);
        if level > 0 {
            s.track_level_seen(level, var);
        } else if s.cold.lrat_enabled {
            p.work(2)?;
            p.reserve(&mut w.level0, 1)?;
            w.level0.push(var);
        }
        if level == s.decision_level {
            cursor::extend(s, w, var, p)?;
        }
    }
    #[cfg(debug_assertions)]
    for at in 0..s.jit_conflict_output.seen_count() as usize {
        p.work(1)?;
        let var = s.jit_conflict_output.seen_var(at) as usize;
        p.work(s.conflict.analyzed_vars().len())?;
        debug_assert!(s.var_is_assigned(var));
        s.conflict
            .debug_assert_jit_seen_bookkeeping(var, &s.var_data);
    }
    ticks(s, w.len as u64, p)?;
    for at in 0..s.arena.len_of(w.offset) {
        p.work(1)?;
        let lit = s.arena.literal_at(w.offset, at);
        if Some(lit) == w.pivot {
            continue;
        }
        if s.ghost_guard_needed && s.lit_val(lit) >= 0 {
            w.ghost_dropped = true;
            continue;
        }
        if s.var_data[lit.variable().index()].level > 0 {
            w.antecedent_size += 1;
        }
    }
    Ok(())
}
