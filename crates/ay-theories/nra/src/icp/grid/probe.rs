// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Scoped observation of one grid-search invocation.

use super::super::diagnostics;
use super::super::*;
use super::points::dyadic_grid;

#[derive(Default)]
pub(super) struct GridProbe {
    witness: Vec<BigRational>,
    names: Vec<String>,
    correct: std::cell::RefCell<Vec<bool>>,
    nodes: std::cell::Cell<usize>,
    max_depth: std::cell::Cell<usize>,
    max_prefix: std::cell::Cell<usize>,
    level: std::cell::Cell<usize>,
    per_level: std::cell::RefCell<Vec<usize>>,
    level_prefix: std::cell::Cell<usize>,
    absent_at: std::cell::Cell<isize>,
    refuted_at: std::cell::Cell<isize>,
    candidate_index: std::cell::RefCell<Vec<(usize, isize, usize, bool)>>,
    starved: std::cell::Cell<bool>,
    absent_detail: std::cell::RefCell<String>,
}

impl GridProbe {
    /// Build a probe only when requested and when the supplied witness covers
    /// every variable in traversal order.
    pub(super) fn install(solver: &NraSolver<'_>, order: &[TermId]) -> Option<Self> {
        if !ay_core::misc_cli_flags().nra_grid_probe {
            return None;
        }
        let supplied = diagnostics::witness();
        let mut witness = Vec::with_capacity(order.len());
        let mut names = Vec::with_capacity(order.len());
        for &var in order {
            let ay_core::TermData::Var(name, _) = solver.terms.get(var) else {
                return None;
            };
            witness.push(
                supplied
                    .iter()
                    .find(|entry| entry.0.as_str() == name.as_str())
                    .map(|(_, value)| value.clone())?,
            );
            names.push(name.clone());
        }
        Some(Self {
            witness,
            names,
            correct: std::cell::RefCell::new(vec![false; order.len()]),
            absent_at: std::cell::Cell::new(-1),
            refuted_at: std::cell::Cell::new(-1),
            per_level: std::cell::RefCell::new(vec![0; 2 * (GRID_MAX_LEVEL + 1) + 2]),
            ..Self::default()
        })
    }

    fn prefix_is_correct(&self, depth: usize) -> bool {
        self.correct.borrow()[..depth].iter().all(|value| *value)
    }

    pub(super) fn level_reset(&self, level: usize) {
        self.level.set(level);
        self.level_prefix.set(0);
        self.absent_at.set(-1);
        self.refuted_at.set(-1);
        self.candidate_index.borrow_mut().clear();
        self.absent_detail.borrow_mut().clear();
        self.correct
            .borrow_mut()
            .iter_mut()
            .for_each(|value| *value = false);
    }

    pub(super) fn note_candidates(
        &self,
        depth: usize,
        candidates: &[BigRational],
        interval: &Interval,
    ) {
        if !self.prefix_is_correct(depth) {
            return;
        }
        let index = candidates
            .iter()
            .position(|candidate| *candidate == self.witness[depth]);
        let in_interval = interval_contains(interval, &self.witness[depth]);
        let entry = (
            depth,
            index.map(|value| value as isize).unwrap_or(-1),
            candidates.len(),
            in_interval,
        );
        let mut indices = self.candidate_index.borrow_mut();
        match indices
            .iter_mut()
            .find(|(candidate_depth, ..)| *candidate_depth == depth)
        {
            Some(slot) => *slot = entry,
            None => indices.push(entry),
        }
        if index.is_none() && depth as isize > self.absent_at.get() {
            self.absent_at.set(depth as isize);
        }
        if index.is_none() && in_interval {
            let alphabet = dyadic_grid(GRID_MAX_LEVEL);
            let alphabet_in_interval = alphabet
                .iter()
                .filter(|value| interval_contains(interval, value))
                .count();
            *self.absent_detail.borrow_mut() = format!(
                "d{depth} wit={} iv=[{:?},{:?}] full_alphabet_in_iv={alphabet_in_interval} \
                 offered={:?}",
                self.witness[depth],
                interval.lo,
                interval.hi,
                candidates
                    .iter()
                    .map(ToString::to_string)
                    .collect::<Vec<_>>()
            );
        }
    }

    pub(super) fn pin(&self, depth: usize, value: &BigRational) {
        let prefix_was_correct = self.prefix_is_correct(depth);
        let correct = prefix_was_correct && *value == self.witness[depth];
        self.correct.borrow_mut()[depth] = correct;
        for slot in &mut self.correct.borrow_mut()[depth + 1..] {
            *slot = false;
        }
        if correct {
            self.max_prefix.set(self.max_prefix.get().max(depth + 1));
            self.level_prefix
                .set(self.level_prefix.get().max(depth + 1));
        } else if prefix_was_correct {
            let mut indices = self.candidate_index.borrow_mut();
            match indices
                .iter_mut()
                .find(|(candidate_depth, ..)| *candidate_depth == depth)
            {
                Some(slot) => *slot = (depth, -2, 0, false),
                None => indices.push((depth, -2, 0, false)),
            }
            self.absent_at.set(self.absent_at.get().max(depth as isize));
        }
    }

    pub(super) fn pick(&self, depth: usize, candidate: &BigRational) {
        self.nodes.set(self.nodes.get() + 1);
        if let Some(count) = self.per_level.borrow_mut().get_mut(self.level.get()) {
            *count += 1;
        }
        self.max_depth.set(self.max_depth.get().max(depth + 1));
        let correct = self.prefix_is_correct(depth) && *candidate == self.witness[depth];
        self.correct.borrow_mut()[depth] = correct;
        for slot in &mut self.correct.borrow_mut()[depth + 1..] {
            *slot = false;
        }
        if correct {
            self.max_prefix.set(self.max_prefix.get().max(depth + 1));
            self.level_prefix
                .set(self.level_prefix.get().max(depth + 1));
        }
    }

    pub(super) fn note_refuted(&self, depth: usize) {
        if self.correct.borrow()[depth]
            && self.prefix_is_correct(depth)
            && depth as isize > self.refuted_at.get()
        {
            self.refuted_at.set(depth as isize);
        }
    }

    pub(super) fn starved(&self) {
        self.starved.set(true);
    }

    pub(super) fn report(&self, found: bool, nodes_used: usize, budget_left: usize) {
        let per_level = self
            .per_level
            .borrow()
            .iter()
            .enumerate()
            .filter(|(_, count)| **count > 0)
            .map(|(level, count)| {
                if level > GRID_MAX_LEVEL {
                    format!("p2L{}:{count}", level - GRID_MAX_LEVEL - 1)
                } else {
                    format!("L{level}:{count}")
                }
            })
            .collect::<Vec<_>>();
        let candidates = self
            .candidate_index
            .borrow()
            .iter()
            .map(|(depth, index, count, in_box)| {
                format!(
                    "d{depth}:{index}/{count}{}",
                    if *in_box { "I" } else { "X" }
                )
            })
            .collect::<Vec<_>>();
        diagnostics::emit(format_args!(
            "NRA-GRIDPROBE found={found} nvars={} nodes={} budget_used={nodes_used} \
             budget_left={budget_left} starved={} max_depth={} MAX_PREFIX={}/{} \
             last_level={} LVL_PREFIX={} absent_at={} refuted_at={} \
             per_level=[{}] cand_at_prefix=[{}] order={} ABSENT_DETAIL<<{}>>",
            self.witness.len(),
            self.nodes.get(),
            self.starved.get(),
            self.max_depth.get(),
            self.max_prefix.get(),
            self.witness.len(),
            self.level.get(),
            self.level_prefix.get(),
            self.absent_at.get(),
            self.refuted_at.get(),
            per_level.join(","),
            candidates.join(","),
            self.names.join(">"),
            self.absent_detail.borrow()
        ));
    }
}
