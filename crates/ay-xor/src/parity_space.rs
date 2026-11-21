// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Find a model of a CNF whose clauses are mostly a parity (XOR) system by
//! walking the affine solution space of that system (AY-SAT-2).
//!
//! Gauss-Jordan elimination over GF(2) brings the recovered XOR system to
//! reduced row-echelon form. Every solution of the system is then fixed by the
//! values of its free columns: a system of rank `r` over `c` variables has
//! `2^(c - r)` solutions. When that dimension is small, the walk visits every
//! solution in Gray-code order (one free column flips per step) and completes
//! each against the clauses that are not part of an XOR (the residual) by unit
//! propagation. When it is larger (up to [`FILTERED_SCAN_MAX_DIMENSION`]) the
//! walk runs only if probing shows that the residual, as a function of the XOR
//! variables it mentions, admits exactly the assignments with at most `k`
//! variables true (or false): a cardinality bound over parities, as in
//! minimum-disagreement parity problems. The walk then keeps the values of
//! those interface variables as a bit vector, one XOR per step, and completes
//! only the points whose weight is within the bound.
//!
//! Nothing here claims unsatisfiability. Every model returned has been checked
//! against every input clause; an inconsistent system, a walk that finds no
//! model, a dimension outside the bounds or a stop request all answer
//! [`ParitySpaceOutcome::Declined`], and the caller hands the formula on to the
//! ordinary search. The probe and the greedy completion are heuristics: they
//! can only make the walk miss a model, never accept a wrong one.

use ay_sat::{Literal, Variable};

use crate::finder::XorFinder;
use crate::VarId;

/// Largest dimension walked without a residual filter: every point is
/// completed against the residual.
pub const FULL_SCAN_MAX_DIMENSION: u32 = 16;

/// Largest dimension walked with a weight filter: 2^32 steps of one word each
/// take a few seconds.
pub const FILTERED_SCAN_MAX_DIMENSION: u32 = 32;

/// Bound on the elimination work, in 64-bit word operations
/// (`rows * columns * words`): about a tenth of a second.
const MAX_GAUSS_WORK: u64 = 1 << 27;

/// Bound on the full scan, in residual literal visits (`2^dimension *
/// residual literals`).
const MAX_FULL_SCAN_WORK: u64 = 1 << 28;

/// Largest interface (XOR variables the residual mentions) the weight probe
/// considers.
const FILTER_MAX_INTERFACE: usize = 256;

/// Samples per weight in the probe.
const PROBE_SAMPLES: usize = 8;

/// Bound on the probe, in residual literal visits.
const MAX_PROBE_WORK: u64 = 1 << 28;

/// Points of a filtered walk completed against the residual before it gives up.
const MAX_FILTERED_CANDIDATES: u64 = 1 << 12;

/// The walk asks the caller whether to stop once per this many steps (a
/// step is one word operation, so this is well under a millisecond). Every
/// point completed against the residual polls as well, and so does every
/// probe sample.
const STOP_CHECK_INTERVAL: u64 = 1 << 16;

/// Why [`solve_parity_space`] returned no model. None of these is a claim
/// about the formula.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ParitySpaceDecline {
    /// The formula contains an empty clause.
    EmptyClause,
    /// The finder recovered no XOR constraint.
    NoXor,
    /// Fewer than half of the clauses encode XOR constraints.
    ResidualDominant,
    /// Elimination would exceed its work bound.
    SystemTooLarge,
    /// The XOR system has no solution. Left to the ordinary search, which can
    /// certify it; this route writes no proof.
    Inconsistent,
    /// The solution space has this many dimensions, more than the walk takes
    /// (or more than [`FULL_SCAN_MAX_DIMENSION`] without a weight filter).
    TooManyDimensions(u32),
    /// The walk ended, or reached its candidate bound, without a model.
    NoModelFound,
    /// The caller asked the walk to stop.
    Stopped,
}

/// Result of [`solve_parity_space`].
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ParitySpaceOutcome {
    /// A total assignment, indexed by variable id, that satisfies every input
    /// clause (checked).
    Model(Vec<bool>),
    /// No model; nothing is claimed.
    Declined(ParitySpaceDecline),
}

/// What [`solve_parity_space`] saw and did.
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct ParitySpaceStats {
    /// XOR constraints recovered.
    pub xors: usize,
    /// Clauses outside the XOR encodings.
    pub residual_clauses: usize,
    /// Variables of the XOR system.
    pub columns: usize,
    /// Rank of the XOR system.
    pub rank: usize,
    /// Dimension of its solution space (`columns - rank`).
    pub dimension: u32,
    /// The weight filter the probe established: `(counts_true, max_weight)`.
    pub weight_filter: Option<(bool, usize)>,
    /// Points of the solution space visited.
    pub points: u64,
    /// Points completed against the residual.
    pub candidates: u64,
}

/// Look for a model of `clauses` in the affine solution space of their XOR
/// part. `num_vars` is the declared variable count; the model covers it and
/// every variable the clauses mention. `should_stop` is polled once the XORs
/// are recovered, before every point completed against the residual, once per
/// 65,536 steps of the walk and once per probe sample; when it
/// answers true the result is [`ParitySpaceDecline::Stopped`].
pub fn solve_parity_space(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    should_stop: &dyn Fn() -> bool,
) -> (ParitySpaceOutcome, ParitySpaceStats) {
    let mut stats = ParitySpaceStats::default();
    let outcome = match solve(num_vars, clauses, should_stop, &mut stats) {
        Ok(model) => ParitySpaceOutcome::Model(model),
        Err(decline) => ParitySpaceOutcome::Declined(decline),
    };
    (outcome, stats)
}

fn solve(
    num_vars: usize,
    clauses: &[Vec<Literal>],
    should_stop: &dyn Fn() -> bool,
    stats: &mut ParitySpaceStats,
) -> Result<Vec<bool>, ParitySpaceDecline> {
    if clauses.iter().any(Vec::is_empty) {
        return Err(ParitySpaceDecline::EmptyClause);
    }
    let num_vars = clauses
        .iter()
        .flatten()
        .map(|lit| lit.variable().index() + 1)
        .max()
        .unwrap_or(0)
        .max(num_vars);
    let mut finder = XorFinder::new();
    let (xors, used) = finder.find_xors_with_indices(clauses);
    if xors.is_empty() {
        return Err(ParitySpaceDecline::NoXor);
    }
    stats.xors = xors.len();
    if should_stop() {
        return Err(ParitySpaceDecline::Stopped);
    }
    let residual: Vec<&[Literal]> = clauses
        .iter()
        .enumerate()
        .filter(|(index, _)| !used.contains(index))
        .map(|(_, clause)| clause.as_slice())
        .collect();
    stats.residual_clauses = residual.len();
    if residual.len() > used.len() {
        return Err(ParitySpaceDecline::ResidualDominant);
    }

    // Columns: the XOR variables in increasing id order.
    let mut column_vars: Vec<VarId> = xors
        .iter()
        .flat_map(|xor| xor.vars.iter().copied())
        .collect();
    column_vars.sort_unstable();
    column_vars.dedup();
    let mut column_of = vec![usize::MAX; num_vars];
    for (column, &var) in column_vars.iter().enumerate() {
        column_of[var as usize] = column;
    }
    let columns = column_vars.len();
    stats.columns = columns;
    // Rank never exceeds the row count, so the dimension is at least this.
    if columns.saturating_sub(xors.len()) > FILTERED_SCAN_MAX_DIMENSION as usize {
        stats.dimension = dimension_u32(columns.saturating_sub(xors.len()));
        return Err(ParitySpaceDecline::TooManyDimensions(stats.dimension));
    }
    let words = columns.div_ceil(64);
    let work = (xors.len() as u64)
        .saturating_mul(columns as u64)
        .saturating_mul(words as u64);
    if work > MAX_GAUSS_WORK {
        return Err(ParitySpaceDecline::SystemTooLarge);
    }

    let mut rows: Vec<Vec<u64>> = Vec::with_capacity(xors.len());
    let mut rhs: Vec<bool> = Vec::with_capacity(xors.len());
    for xor in &xors {
        let mut row = vec![0u64; words];
        for &var in &xor.vars {
            toggle_bit(&mut row, column_of[var as usize]);
        }
        rows.push(row);
        rhs.push(xor.rhs);
    }
    let pivot_columns = reduce_to_row_echelon(&mut rows, &mut rhs);
    let rank = pivot_columns.len();
    stats.rank = rank;
    if rhs[rank..].iter().any(|&bit| bit) {
        return Err(ParitySpaceDecline::Inconsistent);
    }

    let mut is_pivot = vec![false; columns];
    for &column in &pivot_columns {
        is_pivot[column] = true;
    }
    let free_columns: Vec<usize> = (0..columns).filter(|&column| !is_pivot[column]).collect();
    let dimension = free_columns.len();
    stats.dimension = dimension_u32(dimension);
    if dimension > FILTERED_SCAN_MAX_DIMENSION as usize {
        return Err(ParitySpaceDecline::TooManyDimensions(stats.dimension));
    }

    // The solution with every free column 0, and per free column the columns
    // that flip with it: itself and the pivot of every row it occurs in.
    let mut base = vec![0u64; words];
    for (row, &pivot) in pivot_columns.iter().enumerate() {
        if rhs[row] {
            toggle_bit(&mut base, pivot);
        }
    }
    let mut column_masks = vec![0u64; dimension * words];
    for (index, &free) in free_columns.iter().enumerate() {
        let mask = &mut column_masks[index * words..(index + 1) * words];
        toggle_bit(mask, free);
        for (row, &pivot) in pivot_columns.iter().enumerate() {
            if bit(&rows[row], free) {
                toggle_bit(mask, pivot);
            }
        }
    }

    // The interface: XOR variables the residual mentions.
    let mut interface_columns: Vec<usize> = Vec::new();
    let mut in_interface = vec![false; columns];
    for clause in &residual {
        for lit in clause.iter() {
            let column = column_of[lit.variable().index()];
            if column != usize::MAX && !in_interface[column] {
                in_interface[column] = true;
                interface_columns.push(column);
            }
        }
    }
    let interface_vars: Vec<VarId> = interface_columns
        .iter()
        .map(|&column| column_vars[column])
        .collect();
    let residual_literals = residual
        .iter()
        .map(|clause| clause.len() as u64)
        .sum::<u64>();
    let mut evaluator = ResidualEvaluator::new(num_vars, residual);

    // When the residual mentions no XOR variable, every point completes the
    // same way: one point decides.
    let points = if interface_vars.is_empty() {
        1
    } else {
        1u64 << dimension
    };
    let filter = if dimension > FULL_SCAN_MAX_DIMENSION as usize && points > 1 {
        let probe_work = (interface_vars.len() as u64 + 1)
            .saturating_mul(2 * PROBE_SAMPLES as u64)
            .saturating_mul(residual_literals.saturating_add(interface_vars.len() as u64));
        if probe_work > MAX_PROBE_WORK {
            return Err(ParitySpaceDecline::TooManyDimensions(stats.dimension));
        }
        match probe_weight_filter(&mut evaluator, &interface_vars, should_stop)? {
            Some(filter) => Some(filter),
            None => return Err(ParitySpaceDecline::TooManyDimensions(stats.dimension)),
        }
    } else {
        let scan_work = points.saturating_mul(residual_literals.saturating_add(1));
        if scan_work > MAX_FULL_SCAN_WORK {
            return Err(ParitySpaceDecline::TooManyDimensions(stats.dimension));
        }
        None
    };
    stats.weight_filter = filter.map(|filter| (filter.counts_true, filter.max_weight));

    let interface_words = interface_columns.len().div_ceil(64).max(1);
    let mut interface_masks = vec![0u64; dimension * interface_words];
    for index in 0..dimension {
        let mask = &column_masks[index * words..(index + 1) * words];
        let target = &mut interface_masks[index * interface_words..(index + 1) * interface_words];
        for (position, &column) in interface_columns.iter().enumerate() {
            if bit(mask, column) {
                toggle_bit(target, position);
            }
        }
    }
    let mut interface = vec![0u64; interface_words];
    for (position, &column) in interface_columns.iter().enumerate() {
        if bit(&base, column) {
            toggle_bit(&mut interface, position);
        }
    }

    let mut walk = GrayWalk {
        next: 0,
        total: points,
        interface,
        masks: interface_masks,
        words: interface_words,
    };
    let mut values = vec![0u64; words];
    loop {
        let point = match walk.advance(filter, interface_columns.len(), should_stop) {
            Ok(Some(point)) => point,
            Ok(None) => {
                stats.points = walk.next;
                return Err(ParitySpaceDecline::NoModelFound);
            }
            Err(WalkStopped) => {
                stats.points = walk.next;
                return Err(ParitySpaceDecline::Stopped);
            }
        };
        if should_stop() {
            stats.points = walk.next;
            return Err(ParitySpaceDecline::Stopped);
        }
        stats.candidates += 1;
        if filter.is_some() && stats.candidates > MAX_FILTERED_CANDIDATES {
            stats.points = walk.next;
            return Err(ParitySpaceDecline::NoModelFound);
        }
        let gray = point ^ (point >> 1);
        values.copy_from_slice(&base);
        for index in 0..dimension {
            if (gray >> index) & 1 == 1 {
                let mask = &column_masks[index * words..(index + 1) * words];
                for (value, flip) in values.iter_mut().zip(mask) {
                    *value ^= *flip;
                }
            }
        }
        let assigned = evaluator.reset_and_start()
            && interface_columns.iter().all(|&column| {
                evaluator.assign(literal(column_vars[column], bit(&values, column)))
            })
            && evaluator.complete();
        if !assigned {
            continue;
        }
        let mut model = vec![false; num_vars];
        for (column, &var) in column_vars.iter().enumerate() {
            model[var as usize] = bit(&values, column);
        }
        for (var, slot) in model.iter_mut().enumerate() {
            if column_of[var] != usize::MAX {
                continue;
            }
            if let Some(value) = evaluator.value(var) {
                *slot = value;
            }
        }
        if model_satisfies(&model, clauses) {
            stats.points = walk.next;
            return Ok(model);
        }
    }
}

/// Whether `model` satisfies every clause of `clauses`.
pub(crate) fn model_satisfies(model: &[bool], clauses: &[Vec<Literal>]) -> bool {
    clauses.iter().all(|clause| {
        clause.iter().any(|lit| {
            model
                .get(lit.variable().index())
                .is_some_and(|&value| value == lit.is_positive())
        })
    })
}

fn dimension_u32(dimension: usize) -> u32 {
    u32::try_from(dimension).unwrap_or(u32::MAX)
}

fn bit(words: &[u64], index: usize) -> bool {
    (words[index / 64] >> (index % 64)) & 1 == 1
}

fn toggle_bit(words: &mut [u64], index: usize) {
    words[index / 64] ^= 1u64 << (index % 64);
}

fn literal(var: VarId, value: bool) -> Literal {
    if value {
        Literal::positive(Variable::new(var))
    } else {
        Literal::negative(Variable::new(var))
    }
}

/// Gauss-Jordan elimination to reduced row-echelon form: every pivot column is
/// cleared from every other row. Returns the pivot column of each of the first
/// `rank` rows; the remaining rows are zero, with their right-hand sides left
/// for the consistency check.
fn reduce_to_row_echelon(rows: &mut [Vec<u64>], rhs: &mut [bool]) -> Vec<usize> {
    let columns = rows.first().map_or(0, |row| row.len() * 64);
    let mut pivots = Vec::new();
    for column in 0..columns {
        let rank = pivots.len();
        let Some(found) = (rank..rows.len()).find(|&row| bit(&rows[row], column)) else {
            continue;
        };
        rows.swap(rank, found);
        rhs.swap(rank, found);
        let pivot_row = rows[rank].clone();
        let pivot_rhs = rhs[rank];
        for (index, row) in rows.iter_mut().enumerate() {
            if index != rank && bit(row, column) {
                for (word, pivot_word) in row.iter_mut().zip(&pivot_row) {
                    *word ^= *pivot_word;
                }
                rhs[index] ^= pivot_rhs;
            }
        }
        pivots.push(column);
    }
    pivots
}

/// The walk was stopped by the caller.
struct WalkStopped;

/// Gray-code walk over `2^dimension` points that keeps the interface values.
struct GrayWalk {
    /// Index of the next point to visit.
    next: u64,
    total: u64,
    interface: Vec<u64>,
    /// Per free column, the interface bits it flips (`words` words each).
    masks: Vec<u64>,
    words: usize,
}

impl GrayWalk {
    /// Move to the next point the filter admits and return its index (its
    /// free-column values are `index ^ (index >> 1)`), or `None` at the end.
    fn advance(
        &mut self,
        filter: Option<WeightFilter>,
        interface_len: usize,
        should_stop: &dyn Fn() -> bool,
    ) -> Result<Option<u64>, WalkStopped> {
        while self.next < self.total {
            let point = self.next;
            // Polled at point 0 too, so a stop requested before the walk
            // starts is honoured before any step.
            if point & (STOP_CHECK_INTERVAL - 1) == 0 && should_stop() {
                return Err(WalkStopped);
            }
            self.next += 1;
            if point > 0 {
                let flipped = point.trailing_zeros() as usize;
                let mask = &self.masks[flipped * self.words..(flipped + 1) * self.words];
                for (value, flip) in self.interface.iter_mut().zip(mask) {
                    *value ^= *flip;
                }
            }
            let admitted = match filter {
                None => true,
                Some(filter) => filter.admits(&self.interface, interface_len),
            };
            if admitted {
                return Ok(Some(point));
            }
        }
        Ok(None)
    }
}

/// The residual admits an interface assignment iff at most `max_weight` of its
/// variables are true (`counts_true`) or false (otherwise), as probed.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct WeightFilter {
    counts_true: bool,
    max_weight: usize,
}

impl WeightFilter {
    fn admits(self, interface: &[u64], interface_len: usize) -> bool {
        let ones = interface
            .iter()
            .map(|word| word.count_ones() as usize)
            .sum::<usize>();
        let weight = if self.counts_true {
            ones
        } else {
            interface_len.saturating_sub(ones)
        };
        weight <= self.max_weight
    }
}

/// Probe the residual with random interface assignments of every weight. A
/// filter is returned only when every sample of weight `0..=k` is admitted and
/// every sample above `k` refused, for some `k` below the interface size.
/// `Err(Stopped)` when `should_stop` answers true at a sample.
fn probe_weight_filter(
    evaluator: &mut ResidualEvaluator<'_>,
    interface_vars: &[VarId],
    should_stop: &dyn Fn() -> bool,
) -> Result<Option<WeightFilter>, ParitySpaceDecline> {
    let len = interface_vars.len();
    if len == 0 || len > FILTER_MAX_INTERFACE {
        return Ok(None);
    }
    let mut rng = SplitMix64(0x9e37_79b9_7f4a_7c15);
    let mut chosen = vec![false; len];
    let mut order: Vec<usize> = (0..len).collect();
    for counts_true in [true, false] {
        let mut admitted = vec![0usize; len + 1];
        for (weight, count) in admitted.iter_mut().enumerate() {
            for _ in 0..PROBE_SAMPLES {
                if should_stop() {
                    return Err(ParitySpaceDecline::Stopped);
                }
                // Partial Fisher-Yates: the first `weight` entries of `order`.
                chosen.fill(false);
                for slot in 0..weight {
                    let pick = slot + (rng.next_u64() % (len - slot) as u64) as usize;
                    order.swap(slot, pick);
                    chosen[order[slot]] = true;
                }
                let ok = evaluator.reset_and_start()
                    && interface_vars.iter().zip(&chosen).all(|(&var, &picked)| {
                        evaluator.assign(literal(var, picked == counts_true))
                    })
                    && evaluator.complete();
                if ok {
                    *count += 1;
                }
            }
        }
        let below = admitted
            .iter()
            .take_while(|&&count| count == PROBE_SAMPLES)
            .count();
        if below == 0 || below > len {
            continue;
        }
        if admitted[below..].iter().all(|&count| count == 0) {
            return Ok(Some(WeightFilter {
                counts_true,
                max_weight: below - 1,
            }));
        }
    }
    Ok(None)
}

/// SplitMix64: a fixed-seed generator, so the probe is deterministic.
struct SplitMix64(u64);

impl SplitMix64 {
    fn next_u64(&mut self) -> u64 {
        self.0 = self.0.wrapping_add(0x9e37_79b9_7f4a_7c15);
        let mut z = self.0;
        z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
        z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
        z ^ (z >> 31)
    }
}

/// Variable values and the order they were set in.
struct Assignment {
    /// Per variable: 1 true, -1 false, 0 unassigned.
    values: Vec<i8>,
    trail: Vec<u32>,
}

impl Assignment {
    fn lit_value(&self, lit: Literal) -> i8 {
        let value = self.values[lit.variable().index()];
        if lit.is_positive() {
            value
        } else {
            -value
        }
    }

    /// Make `lit` true. False when it is already false.
    fn assign(&mut self, lit: Literal) -> bool {
        match self.lit_value(lit) {
            1 => true,
            -1 => false,
            _ => {
                let var = lit.variable();
                self.values[var.index()] = if lit.is_positive() { 1 } else { -1 };
                self.trail.push(var.id());
                true
            }
        }
    }

    fn clear(&mut self) {
        for &var in &self.trail {
            self.values[var as usize] = 0;
        }
        self.trail.clear();
    }
}

/// Unit propagation over the residual clauses, with a greedy completion.
///
/// One completion costs time linear in the residual: propagation visits the
/// clauses of each falsified literal once, and the greedy choice scans the
/// clauses in order behind a cursor that never moves back, since a clause it
/// passed was satisfied and assignments are only added until the next
/// [`ResidualEvaluator::reset_and_start`].
struct ResidualEvaluator<'a> {
    clauses: Vec<&'a [Literal]>,
    /// Clause indices by literal index (`Literal::index`).
    occurrences: Vec<Vec<u32>>,
    /// The residual's unit clauses.
    units: Vec<Literal>,
    assignment: Assignment,
    head: usize,
    /// Every clause before this index is satisfied.
    cursor: usize,
    /// Clauses the greedy choice has looked at, over the evaluator's life.
    #[cfg(test)]
    scanned: u64,
}

impl<'a> ResidualEvaluator<'a> {
    fn new(num_vars: usize, clauses: Vec<&'a [Literal]>) -> Self {
        let mut occurrences = vec![Vec::new(); 2 * num_vars];
        let mut units = Vec::new();
        for (index, clause) in clauses.iter().enumerate() {
            let index = u32::try_from(index).unwrap_or(u32::MAX);
            for lit in clause.iter() {
                occurrences[lit.index()].push(index);
            }
            if let [unit] = clause {
                units.push(*unit);
            }
        }
        Self {
            clauses,
            occurrences,
            units,
            assignment: Assignment {
                values: vec![0; num_vars],
                trail: Vec::new(),
            },
            head: 0,
            cursor: 0,
            #[cfg(test)]
            scanned: 0,
        }
    }

    fn value(&self, var: usize) -> Option<bool> {
        match self.assignment.values[var] {
            0 => None,
            value => Some(value > 0),
        }
    }

    /// Make `lit` true. False when it is already false.
    fn assign(&mut self, lit: Literal) -> bool {
        self.assignment.assign(lit)
    }

    /// Clear every assignment and assert the residual's unit clauses.
    fn reset_and_start(&mut self) -> bool {
        self.assignment.clear();
        self.head = 0;
        self.cursor = 0;
        for &unit in &self.units {
            if !self.assignment.assign(unit) {
                return false;
            }
        }
        true
    }

    /// Propagate to fixpoint. False on a conflict.
    fn propagate(&mut self) -> bool {
        while self.head < self.assignment.trail.len() {
            let var = Variable::new(self.assignment.trail[self.head]);
            self.head += 1;
            let falsified = if self.assignment.values[var.index()] > 0 {
                Literal::negative(var)
            } else {
                Literal::positive(var)
            };
            for &clause_index in &self.occurrences[falsified.index()] {
                let clause = self.clauses[clause_index as usize];
                let mut unassigned = None;
                let mut open = 0usize;
                let mut satisfied = false;
                for &lit in clause {
                    match self.assignment.lit_value(lit) {
                        1 => {
                            satisfied = true;
                            break;
                        }
                        0 => {
                            open += 1;
                            unassigned = Some(lit);
                        }
                        _ => {}
                    }
                }
                if satisfied {
                    continue;
                }
                match (open, unassigned) {
                    (0, _) => return false,
                    (1, Some(lit)) => {
                        self.assignment.assign(lit);
                    }
                    _ => {}
                }
            }
        }
        true
    }

    /// Propagate, then satisfy each clause still open by one of its
    /// unassigned literals (a negative one first) until none is open. False on
    /// a conflict: the greedy choice may miss a completion, never invent one.
    fn complete(&mut self) -> bool {
        loop {
            if !self.propagate() {
                return false;
            }
            match self.next_open_choice() {
                Err(()) => return false,
                Ok(None) => return true,
                Ok(Some(lit)) => {
                    self.assign(lit);
                }
            }
        }
    }

    /// The literal to make true for the first clause not yet satisfied, or
    /// `Err` for a clause already falsified. Moves the cursor past the
    /// satisfied clauses in front of it.
    fn next_open_choice(&mut self) -> Result<Option<Literal>, ()> {
        while let Some(&clause) = self.clauses.get(self.cursor) {
            #[cfg(test)]
            {
                self.scanned += 1;
            }
            if clause
                .iter()
                .any(|&lit| self.assignment.lit_value(lit) == 1)
            {
                self.cursor += 1;
                continue;
            }
            let mut open = clause
                .iter()
                .copied()
                .filter(|&lit| self.assignment.lit_value(lit) == 0);
            let first = open.next().ok_or(())?;
            let negative = std::iter::once(first)
                .chain(open)
                .find(|lit| !lit.is_positive());
            return Ok(Some(negative.unwrap_or(first)));
        }
        Ok(None)
    }
}

#[cfg(test)]
#[path = "parity_space_tests.rs"]
mod tests;
