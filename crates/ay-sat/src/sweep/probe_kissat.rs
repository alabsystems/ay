// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Kissat 4.0.4's backbone and equivalence probing of one environment
//! (`sweep_variable`, sweep.c:1356-1445), under `--sat-sweep-env-kissat`.
//!
//! Every SAT answer is used. Before each probe the remaining candidates are
//! flipped on the current model, and a candidate whose flip keeps every
//! clause satisfied is dropped without a solve. Each new model refines the
//! remaining backbone candidates and every candidate class. A solve that runs
//! out of ticks ends the environment, since the call's budget is gone. Each
//! unit and equivalence carries the kitten core lemmas of its UNSAT answers,
//! exactly as on AY's own path (`probe.rs`).

use super::{SweepProofFact, Sweeper};
use crate::clause_arena::ClauseArena;
use crate::kitten::CoreLemmas;
use crate::literal::Literal;

/// Kissat's `sweepfliprounds` (options.h:144).
const FLIP_ROUNDS: usize = 1;
/// Equivalences per call, as on AY's own path (`probe.rs`).
const MAX_EQUIVALENCES: usize = 1000;
/// Kitten's SAT and UNSAT answers.
const SAT: i32 = 10;
const UNSAT: i32 = 20;

/// Candidate classes (Kissat's `partition`). Each holds at least two
/// literals, and the last one is probed first.
type Partition = Vec<Vec<u32>>;

impl Sweeper {
    /// Probe the current environment after its first SAT answer: the
    /// backbone phase, then, unless the budget ran out, the equivalence
    /// phase.
    pub(super) fn probe_kissat(
        &mut self,
        clauses: &ClauseArena,
        vals: &[i8],
        frozen: &[u32],
        new_units: &mut Vec<Literal>,
        equivalences: &mut Vec<(u32, u32)>,
    ) {
        let mut backbone = self.kissat_candidates(frozen);
        let mut partition: Partition = if backbone.len() > 1 {
            vec![backbone.clone()]
        } else {
            Vec::new()
        };
        let mut status = SAT;
        if !self.kissat_backbone_phase(&mut backbone, &mut partition, &mut status, new_units) {
            return;
        }
        #[cfg(debug_assertions)]
        let first_new = equivalences.len();
        self.kissat_equivalence_phase(&mut partition, &mut status, equivalences);
        // Defense in depth, as on AY's own path: each new claim against the
        // whole formula, in debug builds only.
        #[cfg(debug_assertions)]
        {
            for &(rep, lit) in &equivalences[first_new..] {
                debug_assert!(
                    self.debug_verify_equivalence_claim(rep, lit, clauses, vals),
                    "BUG: kitten claimed false equivalence {rep} = {lit}"
                );
            }
        }
        #[cfg(not(debug_assertions))]
        let _ = (clauses, vals);
    }

    /// The `TERMINATED` and `kitten_ticks_limit_hit` checks of Kissat's
    /// `sweep_variable` (sweep.c:1356-1445): this environment's ticks are
    /// spent, or the solver asked to stop.
    fn kissat_limit_hit(&mut self) -> bool {
        self.kitten.ticks_exhausted() || self.kitten.terminated()
    }

    /// Kissat's candidates (`init_backbone_and_partition`, sweep.c:474-492):
    /// for each environment variable, in the order the search found it, the
    /// literal true in kitten's model. Frozen variables, variables fixed
    /// earlier in the call and a second literal of a class proved equivalent
    /// earlier in the call are left out.
    fn kissat_candidates(&mut self, frozen: &[u32]) -> Vec<u32> {
        self.kissat_call.begin_environment();
        let mut candidates = Vec::with_capacity(self.coi_vars.len());
        for &var in &self.coi_vars {
            if frozen.get(var).is_some_and(|&count| count > 0) {
                continue;
            }
            let positive = var as u32 * 2;
            let lit = match self.kitten.value(positive) {
                value if value > 0 => positive,
                value if value < 0 => positive + 1,
                _ => continue,
            };
            if self.kissat_call.offer(lit) {
                candidates.push(lit);
            }
        }
        candidates
    }

    /// Kissat's backbone loop (sweep.c:1369-1391): flip the remaining
    /// candidates on the current model, then refute the negation of the last
    /// one. Returns false when the budget ran out, which also skips the
    /// equivalence phase.
    fn kissat_backbone_phase(
        &mut self,
        backbone: &mut Vec<u32>,
        partition: &mut Partition,
        status: &mut i32,
        new_units: &mut Vec<Literal>,
    ) -> bool {
        while !backbone.is_empty() {
            if self.kissat_limit_hit() {
                return false;
            }
            if *status == SAT {
                self.flip_backbone(backbone);
                if self.kissat_limit_hit() {
                    return false;
                }
            }
            let Some(lit) = backbone.pop() else {
                break;
            };
            self.kissat_backbone_candidate(lit, backbone, partition, status, new_units);
        }
        true
    }

    /// Kissat's `flip_backbone_literals` (sweep.c:623-666): a candidate whose
    /// flip keeps every clause satisfied is no backbone.
    fn flip_backbone(&mut self, backbone: &mut Vec<u32>) {
        for _ in 0..FLIP_ROUNDS {
            let before = backbone.len();
            let kitten = &mut self.kitten;
            backbone.retain(|&lit| !kitten.flip_literal(lit));
            if backbone.len() == before || self.kissat_limit_hit() {
                break;
            }
        }
    }

    /// Kissat's `sweep_backbone_candidate` (sweep.c:668-711). Kissat drops a
    /// candidate fixed at kitten's root; here it is solved like any other, in
    /// both postures: the solve answers at once, and its core names the
    /// lemmas the fixing rests on (see `probe.rs`).
    fn kissat_backbone_candidate(
        &mut self,
        lit: u32,
        backbone: &mut Vec<u32>,
        partition: &mut Partition,
        status: &mut i32,
        new_units: &mut Vec<Literal>,
    ) {
        if *status == SAT && self.kitten.flip_literal(lit) {
            return;
        }
        self.kitten.assume(lit ^ 1);
        *status = self.randomized_kitten_solve();
        if *status == SAT {
            let kitten = &self.kitten;
            backbone.retain(|&candidate| kitten.value(candidate) > 0);
            self.kissat_refine_partition(partition);
        } else if *status == UNSAT {
            new_units.push(Literal(lit));
            self.stats.kitten_backbone += 1;
            self.kissat_call.fix((lit >> 1) as usize);
            if self.want_proof {
                let lemmas = self.kitten.core_lemmas_external();
                self.proof_facts.push(SweepProofFact::Unit { lit, lemmas });
            }
        }
    }

    /// Kissat's `sweep_refine_partition` (sweep.c:500-586) on a new model:
    /// each class splits into its true literals and then its false ones,
    /// and singletons are dropped.
    fn kissat_refine_partition(&mut self, partition: &mut Partition) {
        if partition.is_empty() {
            return;
        }
        self.stats.kitten_partition_refinements += 1;
        let kitten = &self.kitten;
        let mut refined = Partition::with_capacity(partition.len() * 2);
        for class in partition.drain(..) {
            let (positive, negative): (Vec<u32>, Vec<u32>) = class
                .into_iter()
                .filter(|&lit| kitten.value(lit) != 0)
                .partition(|&lit| kitten.value(lit) > 0);
            if positive.len() > 1 {
                refined.push(positive);
            }
            if negative.len() > 1 {
                refined.push(negative);
            }
        }
        *partition = refined;
    }

    /// Kissat's equivalence loop (sweep.c:1406-1433): flip the candidates on
    /// the current model, then test the last two literals of the last class.
    fn kissat_equivalence_phase(
        &mut self,
        partition: &mut Partition,
        status: &mut i32,
        equivalences: &mut Vec<(u32, u32)>,
    ) {
        // The backbones just proved leave their classes (Kissat drops
        // root-assigned literals when it refines, sweep.c:519-520).
        let call = &self.kissat_call;
        for class in partition.iter_mut() {
            class.retain(|&lit| !call.is_fixed((lit >> 1) as usize));
        }
        partition.retain(|class| class.len() > 1);
        while !partition.is_empty() && equivalences.len() < MAX_EQUIVALENCES {
            if self.kissat_limit_hit() {
                return;
            }
            if *status == SAT {
                self.flip_partition(partition);
                if self.kissat_limit_hit() {
                    return;
                }
            }
            let Some((lit, other)) = last_pair(partition) else {
                partition.pop();
                continue;
            };
            if !self.kissat_equivalence_pair(lit, other, partition, status, equivalences) {
                return;
            }
        }
    }

    /// Kissat's `flip_partition_literals` (sweep.c:1080-1136): a literal
    /// whose flip keeps every clause satisfied leaves its class, and a class
    /// left with fewer than two literals is dropped.
    fn flip_partition(&mut self, partition: &mut Partition) {
        for _ in 0..FLIP_ROUNDS {
            let mut flipped = false;
            let kitten = &mut self.kitten;
            partition.retain_mut(|class| {
                let mut size = class.len();
                class.retain(|&lit| {
                    if size < 2 || !kitten.flip_literal(lit) {
                        return true;
                    }
                    flipped = true;
                    size -= 1;
                    false
                });
                size > 1
            });
            if !flipped || self.kissat_limit_hit() {
                break;
            }
        }
    }

    /// Kissat's `sweep_equivalence_candidates` (sweep.c:1138-1268) for the
    /// last two literals `lit` and `other` of the last class. Returns false
    /// when a solve ran out of ticks, which ends the environment.
    fn kissat_equivalence_pair(
        &mut self,
        lit: u32,
        other: u32,
        partition: &mut Partition,
        status: &mut i32,
        equivalences: &mut Vec<(u32, u32)>,
    ) -> bool {
        if *status == SAT && self.kitten.flip_literal(lit) {
            remove_from_last_class(partition, lit);
            return true;
        }
        if *status == SAT && self.kitten.flip_literal(other) {
            remove_from_last_class(partition, other);
            return true;
        }
        // `¬lit ∧ other` UNSAT proves `(lit ∨ ¬other)`.
        let Some(lit_or_not_other) = self.kissat_refute(lit ^ 1, other, partition, status) else {
            return *status == SAT;
        };
        // `lit ∧ ¬other` UNSAT proves `(¬lit ∨ other)`.
        let Some(not_lit_or_other) = self.kissat_refute(lit, other ^ 1, partition, status) else {
            return *status == SAT;
        };
        // The smaller literal represents (sweep.c:1249-1262). The fact's
        // `forward` certifies `merged ∧ ¬rep` UNSAT and its `backward`
        // `¬merged ∧ rep` UNSAT (`SweepProofFact::Equivalence`).
        let (rep, merged, forward, backward) = if lit < other {
            (lit, other, lit_or_not_other, not_lit_or_other)
        } else {
            (other, lit, not_lit_or_other, lit_or_not_other)
        };
        equivalences.push((rep, merged));
        self.stats.kitten_equivalences += 1;
        if self.want_proof {
            self.proof_facts.push(SweepProofFact::Equivalence {
                rep,
                lit: merged,
                forward,
                backward,
            });
        }
        self.kissat_call.merge(rep, merged);
        remove_from_last_class(partition, merged);
        true
    }

    /// Solve under `first ∧ second`, leaving the answer in `status`. UNSAT
    /// returns the core lemmas (empty unless a proof is wanted), taken before
    /// the next solve resets kitten's failing clause. SAT refines the classes
    /// by the model.
    fn kissat_refute(
        &mut self,
        first: u32,
        second: u32,
        partition: &mut Partition,
        status: &mut i32,
    ) -> Option<CoreLemmas> {
        self.kitten.assume(first);
        self.kitten.assume(second);
        *status = self.randomized_kitten_solve();
        if *status == SAT {
            self.kissat_refine_partition(partition);
        }
        if *status != UNSAT {
            return None;
        }
        Some(if self.want_proof {
            self.kitten.core_lemmas_external()
        } else {
            CoreLemmas::default()
        })
    }
}

/// The last two literals of the last class (Kissat's `end[-3]` and
/// `end[-2]`, sweep.c:1424-1427).
fn last_pair(partition: &[Vec<u32>]) -> Option<(u32, u32)> {
    match partition.last()?.as_slice() {
        [.., lit, other] => Some((*lit, *other)),
        _ => None,
    }
}

/// Remove `lit` from the last class, or drop the class when it would be left
/// a singleton (Kissat's `sweep_remove` and the flips of
/// `sweep_equivalence_candidates`, sweep.c:1046-1078, 1153-1184).
fn remove_from_last_class(partition: &mut Partition, lit: u32) {
    if partition.last().is_some_and(|class| class.len() <= 2) {
        partition.pop();
        return;
    }
    let position = partition
        .last()
        .and_then(|class| class.iter().rposition(|&member| member == lit));
    if let (Some(position), Some(class)) = (position, partition.last_mut()) {
        class.remove(position);
    }
}
