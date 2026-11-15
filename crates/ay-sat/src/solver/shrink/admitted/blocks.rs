// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn apply<P: Policy>(
    scratch: &mut Scratch<'_>,
    start: usize,
    end: usize,
    level: u32,
    removed_lits: &mut Option<&mut Vec<Literal>>,
    p: &P,
) -> Result<(), P::Error> {
    let s = &mut *scratch.s;
    debug_assert!(start < end && level <= s.decision_level);
    if end - start == 1 {
        let lit = s.conflict.learned_at(scratch.entries[start].2);
        mark(s, lit.variable().index(), MIN_KEEP, p)?;
        return push(&mut scratch.result, lit, p);
    }
    p.counter(s.stats.shrink_block_attempts, 1)?;
    s.stats.shrink_block_attempts += 1;
    scratch.block.clear();
    for &(_, _, index) in &scratch.entries[start..end] {
        p.work(1)?;
        push(&mut scratch.block, s.conflict.learned_at(index), p)?;
    }
    if let Some(uip) = walk::find(s, &scratch.block, level, p)? {
        success(s, &scratch.block, uip, level, removed_lits, p)?;
        push(&mut scratch.result, uip, p)?;
    } else {
        for &(_, _, index) in &scratch.entries[start..end] {
            p.work(1)?;
            let lit = s.conflict.learned_at(index);
            if s.redundant_admitted(lit, 0, p)? {
                removed(removed_lits, lit, p)?;
                p.counter(s.stats.shrink_lits_fallback_removed, 1)?;
                s.min.minimize_flags[lit.variable().index()] &= !MIN_VISITED;
                s.stats.shrink_lits_fallback_removed += 1;
            } else {
                mark(s, lit.variable().index(), MIN_KEEP, p)?;
                push(&mut scratch.result, lit, p)?;
            }
        }
    }
    Ok(())
}

fn success<P: Policy>(
    s: &mut Solver,
    block: &[Literal],
    uip: Literal,
    level: u32,
    removed_lits: &mut Option<&mut Vec<Literal>>,
    p: &P,
) -> Result<(), P::Error> {
    p.counter(s.stats.shrink_block_successes, 1)?;
    p.counter(s.stats.shrink_lits_block_removed, block.len() as u64 - 1)?;
    s.stats.shrink_block_successes += 1;
    s.stats.shrink_lits_block_removed += block.len() as u64 - 1;
    for index in 0..s.ws_shrink_chain.len() {
        p.work(1)?;
        let id = s.ws_shrink_chain[index];
        p.chain(s, id)?;
    }
    let var = uip.variable().index();
    // Reserve before either KEEP or SEEN becomes visible to unwind cleanup.
    mark(s, var, MIN_KEEP, p)?;
    if s.cold.shrink_bump_uip_kissat {
        p.seen(s)?;
        s.conflict.mark_seen(var, &mut s.var_data);
    }
    for &lit in block {
        p.work(1)?;
        let old_var = lit.variable().index();
        if old_var != var {
            removed(removed_lits, lit, p)?;
            // Not an in-clause base case any more; the block UIP implies it.
            s.min.minimize_flags[old_var] &= !MIN_VISITED;
            s.min.minimize_flags[old_var] |= MIN_REMOVABLE;
        }
    }
    if s.cold.shrink_removable_kissat {
        promote(s, var, level, p)?;
    }
    Ok(())
}

pub(in crate::solver::shrink) fn promote<P: Policy>(
    s: &mut Solver,
    uip_var: usize,
    block_level: u32,
    p: &P,
) -> Result<(), P::Error> {
    p.work(3)?;
    let uip_pos = s.var_data[uip_var].trail_pos;
    for index in 0..s.min.shrink_walked.len() {
        p.work(1)?;
        let var = s.min.shrink_walked[index];
        if var == uip_var {
            continue;
        }
        let flags = s.min.minimize_flags[var];
        if flags == 0 {
            p.mark(s)?;
            s.min.minimize_to_clear.push(var);
        }
        s.min.minimize_flags[var] = flags | MIN_REMOVABLE;
    }
    let level = block_level as usize;
    for seen in [&mut s.min.level_seen, &mut s.min.minimize_level_seen] {
        if let Some(entry) = seen.get_mut(level).filter(|entry| entry.count > 0) {
            entry.trail = entry.trail.min(uip_pos);
        }
    }
    Ok(())
}
