// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--sat-sweep-env-kissat`: Kissat 4.0.4's sweeping environment (sweep.c).
//! Default off; nothing here runs unless the switch is on.
//!
//! - The limits grow with every completed pass (`init_sweeper`,
//!   sweep.c:107-137): `256 << c` variables up to 8192, `1024 << c` clauses
//!   up to 32768 and depth `2 + c` up to 3, where `c` counts the completed
//!   passes (capped at 32 for the shifts). AY's own environment is fixed at
//!   48 variables, 4096 clauses and depth 4.
//! - The sweep order takes the variables whose polarities each occur in
//!   between 1 and `clauses` clauses, fewest occurrences first
//!   (sweep.c:1478-1529).
//! - The search checks the clause limit before it expands a variable, and
//!   stops altogether once a clause brings the variable count to the limit
//!   (sweep.c:1298-1350).
//! - A call remembers what it proved. A variable proved a backbone is not
//!   swept or offered again, and a later environment offers one literal per
//!   proved equivalence class (Kissat substitutes at once and keeps
//!   representatives only, sweep.c:253-309, 474-492, 1273-1277). AY rewrites
//!   the clauses at the end of the call, so a later environment may still
//!   hold a merged variable's clauses; that variable is offered there when
//!   no other literal of its class is.

use super::Sweeper;
use crate::clause_arena::ClauseArena;
use crate::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use crate::literal::Literal;
use crate::occ_list::OccList;

/// Kissat 4.0.4 `sweepvars` and `sweepmaxvars` (options.h:149, 147).
const SWEEP_VARS: u64 = 256;
const SWEEP_MAX_VARS: u64 = 8192;
/// Kissat 4.0.4 `sweepclauses` and `sweepmaxclauses` (options.h:140, 145).
const SWEEP_CLAUSES: u64 = 1024;
const SWEEP_MAX_CLAUSES: u64 = 32_768;
/// Kissat 4.0.4 `sweepdepth` and `sweepmaxdepth` (options.h:142, 146).
const SWEEP_DEPTH: u64 = 2;
const SWEEP_MAX_DEPTH: u64 = 3;
/// `max_completed` in `init_sweeper` (sweep.c:108-110).
const MAX_COMPLETED: u64 = 32;

/// One call's environment limits.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(super) struct EnvLimits {
    pub(super) vars: usize,
    pub(super) clauses: usize,
    pub(super) depth: u32,
}

impl EnvLimits {
    /// Kissat's limits after `completed` completed passes. Nothing shrinks,
    /// and a call that does not complete its pass leaves them as they are.
    pub(super) fn kissat(completed: u64) -> Self {
        let shift = completed.min(MAX_COMPLETED) as u32;
        let vars = (SWEEP_VARS << shift).min(SWEEP_MAX_VARS);
        let clauses = (SWEEP_CLAUSES << shift).min(SWEEP_MAX_CLAUSES);
        let depth = SWEEP_DEPTH.saturating_add(completed).min(SWEEP_MAX_DEPTH);
        Self {
            vars: vars as usize,
            clauses: clauses as usize,
            depth: depth as u32,
        }
    }
}

/// What the current call has proved so far (Kissat's `reprs` and root
/// units), consulted when a later environment of the call picks its
/// candidates. Cleared at the start of every call.
#[derive(Default)]
pub(super) struct KissatCall {
    /// The representative of each merged literal, both polarities; a
    /// literal without an entry represents itself.
    reprs: HashMap<u32, u32>,
    /// Variables proved a backbone.
    fixed: HashSet<usize>,
    /// Representative variables already offered by the current environment.
    taken: HashSet<u32>,
}

impl KissatCall {
    pub(super) fn begin_call(&mut self) {
        self.reprs.clear();
        self.fixed.clear();
        self.taken.clear();
    }

    pub(super) fn begin_environment(&mut self) {
        self.taken.clear();
    }

    pub(super) fn is_fixed(&self, var: usize) -> bool {
        self.fixed.contains(&var)
    }

    pub(super) fn fix(&mut self, var: usize) {
        self.fixed.insert(var);
    }

    /// The representative of `lit` under the equivalences proved so far.
    /// Every entry points to a smaller literal, so the walk ends.
    fn repr(&self, lit: u32) -> u32 {
        let mut repr = lit;
        while let Some(&next) = self.reprs.get(&repr) {
            repr = next;
        }
        repr
    }

    /// Record `a ≡ b`, the smaller representative representing both classes
    /// (sweep.c:1249-1262). A pair that would join a class to its own
    /// negation is left to the end-of-call union-find, which reports the
    /// contradiction.
    pub(super) fn merge(&mut self, a: u32, b: u32) {
        let (ra, rb) = (self.repr(a), self.repr(b));
        if ra == rb || ra == (rb ^ 1) {
            return;
        }
        let (repr, other) = if ra < rb { (ra, rb) } else { (rb, ra) };
        self.reprs.insert(other, repr);
        self.reprs.insert(other ^ 1, repr ^ 1);
    }

    /// Offer `lit` as a candidate of the current environment unless its
    /// variable is fixed or a literal of its class, in either polarity, was
    /// offered already.
    pub(super) fn offer(&mut self, lit: u32) -> bool {
        if self.is_fixed((lit >> 1) as usize) {
            return false;
        }
        let class = self.repr(lit) >> 1;
        self.taken.insert(class)
    }
}

impl Sweeper {
    /// This call's sweep order (Kissat's `schedule_sweeping`,
    /// sweep.c:1478-1610): the unassigned, unfrozen variables not yet swept
    /// in this pass whose polarities each occur in between 1 and
    /// `limits.clauses` clauses, fewest occurrences first and ties by index.
    /// Kissat keeps the rest of its queue across calls; here the pass marks
    /// do, and the rest is ranked again by its current occurrences.
    pub(super) fn kissat_schedule(
        &self,
        occ: &OccList,
        vals: &[i8],
        frozen: &[u32],
        limits: EnvLimits,
    ) -> Vec<usize> {
        let mut ranked: Vec<(usize, usize)> = Vec::new();
        for var in 0..self.num_vars {
            let positive = var * 2;
            if vals.get(positive) != Some(&0) || frozen.get(var).is_some_and(|&count| count > 0) {
                continue;
            }
            if self.swept_in_pass.get(var) == Some(&self.sweep_pass) {
                continue;
            }
            let pos_occs = occ.count(Literal(positive as u32));
            let neg_occs = occ.count(Literal(positive as u32 + 1));
            if pos_occs == 0 || neg_occs == 0 {
                continue;
            }
            if pos_occs > limits.clauses || neg_occs > limits.clauses {
                continue;
            }
            ranked.push((pos_occs + neg_occs, var));
        }
        ranked.sort_unstable();
        ranked.into_iter().map(|(_, var)| var).collect()
    }

    /// Kissat's environment of `start_var` (`sweep_variable`,
    /// sweep.c:1287-1350). Returns the number of clauses fed to kitten.
    pub(super) fn build_coi_kissat(
        &mut self,
        start_var: usize,
        arena: &ClauseArena,
        occ: &OccList,
        vals: &[i8],
        limits: EnvLimits,
    ) -> usize {
        self.kitten.clear();
        self.coi_vars.clear();
        self.coi_clauses.clear();
        self.coi_depths[start_var] = 1;
        self.coi_vars.push(start_var);

        let mut lits: Vec<u32> = Vec::new();
        let mut expand = 0;
        let mut next = 1;
        let mut depth: u32 = 1;
        let mut encoded: usize = 0;
        'search: loop {
            if encoded >= limits.clauses {
                break;
            }
            if expand == next {
                if depth >= limits.depth {
                    break;
                }
                next = self.coi_vars.len();
                if expand == next {
                    break;
                }
                depth += 1;
            }
            let var = self.coi_vars[expand];
            for sign in 0..2u32 {
                for &clause_idx in occ.get(Literal(var as u32 * 2 + sign)) {
                    if self.feed_kissat_clause(clause_idx, arena, vals, depth, &mut lits) {
                        encoded += 1;
                    }
                    if self.coi_vars.len() >= limits.vars {
                        break 'search;
                    }
                }
            }
            expand += 1;
        }
        encoded
    }

    /// Feed the clause at `clause_idx` to kitten unless it is dead, a learned
    /// clause longer than two, already in the environment or satisfied at
    /// level 0; its false literals are dropped, and its new unassigned
    /// variables join the next layer. Returns whether it was fed.
    fn feed_kissat_clause(
        &mut self,
        clause_idx: usize,
        arena: &ClauseArena,
        vals: &[i8],
        depth: u32,
        lits: &mut Vec<u32>,
    ) -> bool {
        if arena.is_dead(clause_idx)
            || (arena.is_learned(clause_idx) && arena.len_of(clause_idx) > 2)
            || self.coi_clauses.contains(&clause_idx)
        {
            return false;
        }
        lits.clear();
        for &lit in arena.literals(clause_idx) {
            match vals.get(lit.index()) {
                Some(&value) if value > 0 => return false,
                Some(&value) if value < 0 => {}
                _ => lits.push(lit.0),
            }
        }
        self.coi_clauses.insert(clause_idx);
        self.kitten
            .add_clause_with_id(clause_idx as u32, lits.as_slice(), u32::MAX);
        for &lit in arena.literals(clause_idx) {
            let var = lit.variable().index();
            if var < self.coi_depths.len()
                && self.coi_depths[var] == 0
                && vals.get(var * 2) == Some(&0)
            {
                self.coi_depths[var] = depth + 1;
                self.coi_vars.push(var);
            }
        }
        true
    }
}
