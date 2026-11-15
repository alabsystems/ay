// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

struct Block {
    level: u32,
    stamp: u32,
    open: u32,
    max_position: usize,
    last_distance: u32,
}

pub(in crate::solver::shrink) fn find<P: Policy>(
    s: &mut Solver,
    literals: &[Literal],
    level: u32,
    p: &P,
) -> Result<Option<Literal>, P::Error> {
    p.work(40)?;
    debug_assert!(literals.len() >= 2);
    if s.shrink_stamp_counter == u32::MAX {
        p.work(s.shrink_stamp.len())?;
        s.shrink_stamp.fill(0);
        s.shrink_stamp_counter = 0;
    }
    s.shrink_stamp_counter += 1;
    s.ws_shrink_chain.clear();
    s.min.shrink_walked.clear();
    s.reap.clear();
    let mut block = Block {
        level,
        stamp: s.shrink_stamp_counter,
        open: 0,
        max_position: 0,
        last_distance: 0,
    };
    if !seed(s, literals, &mut block, p)? {
        return Ok(None);
    }
    loop {
        p.work(1)?;
        if s.reap.is_empty() {
            return Ok(None);
        }
        let distance = p.pop(&mut s.reap)?;
        block.last_distance = distance;
        let Some(position) = block.max_position.checked_sub(distance as usize) else {
            return Ok(None);
        };
        let Some(&uip) = s.trail.get(position) else {
            return Ok(None);
        };
        p.literal(s, uip.negated())?;
        if s.cold.shrink_removable_kissat {
            push(&mut s.min.shrink_walked, uip.variable().index(), p)?;
        }
        let Some(open) = block.open.checked_sub(1) else {
            return Ok(None);
        };
        block.open = open;
        if open == 0 {
            debug_assert_eq!(s.var_data[uip.variable().index()].level, level);
            debug_assert!(s.lit_val(uip) > 0);
            return Ok(Some(uip.negated()));
        }
        if !resolve(s, uip, &mut block, p)? {
            return Ok(None);
        }
    }
}

fn seed<P: Policy>(
    s: &mut Solver,
    literals: &[Literal],
    block: &mut Block,
    p: &P,
) -> Result<bool, P::Error> {
    for &lit in literals {
        p.work(1)?;
        p.literal(s, lit)?;
        let var = lit.variable().index();
        debug_assert_eq!(s.var_data[var].level, block.level);
        debug_assert!(s.lit_val(lit) < 0);
        stamp_capacity(s, var, p)?;
        p.open(block.open)?;
        s.shrink_stamp[var] = block.stamp;
        block.open += 1;
        let position = s.var_data[var].trail_pos as usize;
        if position >= s.trail.len() {
            return Ok(false);
        }
        block.max_position = block.max_position.max(position);
    }
    for &lit in literals {
        p.work(1)?;
        let position = s.var_data[lit.variable().index()].trail_pos as usize;
        p.push(&mut s.reap, (block.max_position - position) as u32)?;
    }
    Ok(true)
}

fn resolve<P: Policy>(
    s: &mut Solver,
    pivot: Literal,
    block: &mut Block,
    p: &P,
) -> Result<bool, P::Error> {
    p.work(1)?;
    let var = pivot.variable().index();
    debug_assert_eq!(s.var_data[var].level, block.level);
    let reason = match s.var_reason_kind(var) {
        ReasonKind::Clause(reason) => reason,
        ReasonKind::BinaryLiteral(other) => {
            debug_assert!(!s.cold.lrat_enabled);
            tick(s, 2, p)?;
            return antecedent(s, other, pivot, block, p);
        }
        ReasonKind::Decision | ReasonKind::LazyTheory(_) => {
            p.counter(s.stats.shrink_fail_decision, 1)?;
            s.stats.shrink_fail_decision += 1;
            return Ok(false);
        }
    };
    if s.cold.lrat_enabled {
        let id = s.clause_id(reason);
        if id != 0 {
            push(&mut s.ws_shrink_chain, id, p)?;
        }
    }
    let offset = reason.0 as usize;
    p.clause(s, pivot.negated(), offset)?;
    let len = s.arena.len_of(offset);
    tick(s, len, p)?;
    for index in 0..len {
        p.work(1)?;
        let lit = s.arena.literal(offset, index);
        if lit.variable().index() != var && !antecedent(s, lit, pivot, block, p)? {
            return Ok(false);
        }
    }
    Ok(true)
}

fn antecedent<P: Policy>(
    s: &mut Solver,
    lit: Literal,
    pivot: Literal,
    block: &mut Block,
    p: &P,
) -> Result<bool, P::Error> {
    p.work(1)?;
    p.antecedent(s, lit, pivot.negated())?;
    // Preserve the ordinary chrono ghost guard. The counted IC3 policy instead
    // validates that its non-chrono reason has a real earlier false assignment.
    if s.lit_val(lit) >= 0 {
        return Ok(true);
    }
    let var = lit.variable().index();
    let level = s.var_data[var].level;
    if level == block.level {
        stamp_capacity(s, var, p)?;
        if s.shrink_stamp[var] != block.stamp {
            p.open(block.open)?;
            s.shrink_stamp[var] = block.stamp;
            block.open += 1;
            let position = s.var_data[var].trail_pos as usize;
            if position > block.max_position {
                return Ok(false);
            }
            let distance = (block.max_position - position) as u32;
            if distance < block.last_distance {
                return Ok(false);
            }
            p.push(&mut s.reap, distance)?;
        }
    } else if level != 0 && !removable(s, lit, p)? {
        p.counter(s.stats.shrink_fail_lower, 1)?;
        s.stats.shrink_fail_lower += 1;
        return Ok(false);
    }
    Ok(true)
}

pub(in crate::solver::shrink) fn removable<P: Policy>(
    s: &mut Solver,
    lit: Literal,
    p: &P,
) -> Result<bool, P::Error> {
    p.work(1)?;
    p.literal(s, lit)?;
    let var = lit.variable().index();
    debug_assert!(s.lit_val(lit) < 0);
    if s.var_data[var].level == 0 {
        return Ok(true);
    }
    let flags = s.min.minimize_flags[var];
    if flags & (MIN_REMOVABLE | MIN_KEEP) != 0 {
        return Ok(true);
    }
    if flags & MIN_POISON != 0 || s.var_data[var].reason == NO_REASON {
        return Ok(false);
    }
    // VISITED alone is NOT a removable lower-level dependency.
    s.redundant_admitted(lit, 1, p)
}

fn stamp_capacity<P: Policy>(s: &mut Solver, var: usize, p: &P) -> Result<(), P::Error> {
    if var >= s.shrink_stamp.len() {
        let additional = var + 1 - s.shrink_stamp.len();
        p.work(additional)?;
        p.reserve(&mut s.shrink_stamp, additional)?;
        s.shrink_stamp.resize(var + 1, 0);
    }
    Ok(())
}

fn tick<P: Policy>(s: &mut Solver, len: usize, p: &P) -> Result<(), P::Error> {
    if !s.cold.analysis_ticks_kissat || len > 2 {
        let ticks = &mut s.search_ticks[usize::from(s.stable_mode)];
        p.counter(*ticks, 1)?;
        *ticks += 1;
    }
    Ok(())
}
