// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

pub(super) fn entries<P: Policy>(
    scratch: &mut Scratch<'_>,
    count: usize,
    p: &P,
) -> Result<bool, P::Error> {
    let s = &mut *scratch.s;
    for index in 0..count {
        p.work(1)?;
        let lit = s.conflict.learned_at(index);
        p.literal(s, lit)?;
        mark(s, lit.variable().index(), 0, p)?;
    }
    let uip = s.conflict.asserting_literal();
    p.literal(s, uip)?;
    mark(s, uip.variable().index(), 0, p)?;
    for index in 0..count {
        p.work(1)?;
        let lit = s.conflict.learned_at(index);
        level(s, lit, p)?;
    }
    level(s, uip, p)?;
    scratch.entries.clear();
    for index in 0..count {
        p.work(1)?;
        let lit = s.conflict.learned_at(index);
        let data = s.var_data[lit.variable().index()];
        debug_assert!(s.lit_val(lit) < 0 && data.level > 0);
        let position = data.trail_pos as usize;
        if position >= s.trail.len() {
            return Ok(false);
        }
        push(&mut scratch.entries, (data.level, position, index), p)?;
    }
    Ok(true)
}

fn level<P: Policy>(s: &mut Solver, lit: Literal, p: &P) -> Result<(), P::Error> {
    p.work(1)?;
    let data = s.var_data[lit.variable().index()];
    let level = data.level as usize;
    if level >= s.min.minimize_level_seen.len() {
        let additional = level + 1 - s.min.minimize_level_seen.len();
        p.work(additional)?;
        p.reserve(&mut s.min.minimize_level_seen, additional)?;
        s.min
            .minimize_level_seen
            .resize(level + 1, minimization_state::LevelSeen::EMPTY);
    }
    p.level(s, level)?;
    let entry = &mut s.min.minimize_level_seen[level];
    if entry.count == 0 {
        s.min.minimize_levels_to_clear.push(level as u32);
    }
    entry.count += 1;
    entry.trail = entry.trail.min(data.trail_pos);
    Ok(())
}
