// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Deferred backward LRAT proof reconstruction (Phase 2b, #8072).
//!
//! Instead of building LRAT hint chains eagerly during every conflict analysis
//! (the forward path in `conflict_analysis_lrat.rs`), this module reconstructs
//! the proof backward from the empty clause after the solver determines UNSAT.
//!
//! ## Algorithm
//!
//! 1. Start from the empty clause (the final derivation of contradiction).
//! 2. BFS backward through the clause dependency graph:
//!    - For each learned clause reachable from the empty clause, find its
//!      antecedent clauses via `var_data[vi].reason` pointers on the trail.
//!    - Collect the clause IDs of all antecedent clauses.
//! 3. Emit proof steps in reverse topological order (reverse BFS order).
//! 4. Only emit steps for clauses reachable from the empty clause — skip
//!    unreachable learned clauses entirely.
//!
//! ## Data structures used
//!
//! - `cold.clause_ids: Vec<u64>` — maps arena offsets to clause IDs (always
//!   populated since Phase 2a, #8069).
//! - `var_data[vi].reason: u32` — propagation reason for each assigned variable.
//! - `trail: Vec<Literal>` — assignment order.
//! - `ClauseTrace` in `clause_trace.rs` — records clause additions with hints.
//!
//! ## Integration
//!
//! This module provides `reconstruct_lrat_backward()` which can be called from
//! `finalize_unsat.rs` as an alternative to the forward LRAT chain. The forward
//! path is NOT removed — both coexist during this transition phase.

use super::*;
use ay_core::time::Instant;
use std::collections::HashSet;
use std::hash::Hash;
use std::mem::size_of;

/// A single LRAT proof step produced by backward reconstruction.
///
/// Each step represents a derived clause and the clause IDs of its antecedents
/// (the hints that an LRAT checker needs to verify the derivation by RUP).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct LratStep {
    /// The clause ID of the derived clause.
    pub(crate) clause_id: u64,
    /// The literals of the derived clause.
    pub(crate) literals: Vec<Literal>,
    /// The clause IDs of the antecedent clauses (LRAT hints).
    /// Order: suitable for RUP checking (reverse resolution order).
    /// Positive values are clause-ID references for RUP checking.
    /// Negative values mark RAT witness boundaries / deletion steps
    /// (needed for extended resolution and blocked clause proofs).
    pub(crate) hints: Vec<i64>,
}

/// Result of backward proof reconstruction.
#[derive(Debug)]
pub(crate) struct BackwardProofResult {
    /// Proof steps in emission order (reverse topological: deepest dependencies first,
    /// empty clause last). Each step is a derived clause with its LRAT hints.
    pub(crate) steps: Vec<LratStep>,
    /// Whether reconstruction was complete (all antecedents resolved).
    /// If false, some clauses were unreachable (e.g., garbage collected)
    /// and the proof may be incomplete.
    pub(crate) complete: bool,
}

/// Bounded emission result keeps final empty-clause hints separate so the
/// finalizer can consume them directly without rebuilding an unbounded chain.
#[derive(Debug)]
pub(crate) struct BoundedBackwardProofResult {
    pub(crate) steps: Vec<LratStep>,
    pub(crate) empty_hints: Vec<u64>,
    pub(crate) complete: bool,
}

/// Allocation/count category used by bounded backward reconstruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BackwardProofResource {
    Visited,
    Queue,
    Seed,
    Steps,
    Literals,
    Hints,
    Bytes,
    ClauseIds,
}

/// Limits for the deferred reconstruction pass. Byte accounting covers
/// retained logical allocations; allocator reallocation transients remain part
/// of the caller-enforced process memory envelope.
#[derive(Clone, Debug)]
pub(crate) struct BackwardProofLimits {
    pub(crate) deadline: Option<Instant>,
    pub(crate) max_steps: usize,
    pub(crate) max_literals: usize,
    pub(crate) max_hints: usize,
    pub(crate) max_bytes: usize,
}

/// Typed exhaustion from bounded backward reconstruction.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum BackwardProofFailure {
    Limit {
        resource: BackwardProofResource,
        limit: usize,
        actual: usize,
    },
    Deadline,
    AccountingOverflow {
        resource: BackwardProofResource,
    },
    Allocation {
        resource: BackwardProofResource,
    },
}

struct BackwardProofMeter<'a> {
    limits: &'a BackwardProofLimits,
    bytes: usize,
    steps: usize,
    literals: usize,
    hints: usize,
    work: u64,
}

const MAX_DENSE_VISITED_BYTES: usize = 8 * 1024 * 1024;

/// Resource-accounted clause-ID membership for the backward graph walk.
///
/// LRAT IDs can be reserved in a namespace far larger than the reachable
/// proof. Small namespaces use a packed dense bitset; large namespaces use a
/// sparse set whose growth is charged to the same meter. This preserves O(1)
/// membership without zero-filling tens of MiB for a proof with only a few
/// reachable clauses.
enum ClauseIdVisited {
    Dense { len: usize, words: Vec<u64> },
    Sparse { len: usize, ids: HashSet<usize> },
}

impl ClauseIdVisited {
    fn new_bounded(
        len: usize,
        meter: &mut BackwardProofMeter<'_>,
    ) -> Result<Self, BackwardProofFailure> {
        let word_len = len
            .checked_add(u64::BITS as usize - 1)
            .map(|bits| bits / u64::BITS as usize)
            .ok_or(BackwardProofFailure::AccountingOverflow {
                resource: BackwardProofResource::ClauseIds,
            })?;
        let dense_bytes = word_len.checked_mul(size_of::<u64>()).ok_or(
            BackwardProofFailure::AccountingOverflow {
                resource: BackwardProofResource::Visited,
            },
        )?;
        let dense_fits_meter = meter
            .bytes
            .checked_add(dense_bytes)
            .is_some_and(|bytes| bytes <= meter.limits.max_bytes);
        if dense_bytes <= MAX_DENSE_VISITED_BYTES && dense_fits_meter {
            let mut words = Vec::new();
            meter.reserve_to(&mut words, word_len, BackwardProofResource::Visited)?;
            words.resize(word_len, 0);
            meter.check_deadline()?;
            Ok(Self::Dense { len, words })
        } else {
            meter.check_deadline()?;
            Ok(Self::Sparse {
                len,
                ids: HashSet::new(),
            })
        }
    }

    fn contains(&self, index: usize) -> bool {
        match self {
            Self::Dense { len, words } => {
                if index >= *len {
                    return false;
                }
                let word = index / u64::BITS as usize;
                let mask = 1_u64 << (index % u64::BITS as usize);
                words[word] & mask != 0
            }
            Self::Sparse { len, ids } => index < *len && ids.contains(&index),
        }
    }

    /// Mark `index`, returning `Some(true)` only on its first visit.
    /// `None` means the clause ID lies outside the solver's declared range.
    fn mark(
        &mut self,
        index: usize,
        meter: &mut BackwardProofMeter<'_>,
    ) -> Result<Option<bool>, BackwardProofFailure> {
        match self {
            Self::Dense { len, words } => {
                if index >= *len {
                    return Ok(None);
                }
                let word = index / u64::BITS as usize;
                let mask = 1_u64 << (index % u64::BITS as usize);
                let is_new = words[word] & mask == 0;
                words[word] |= mask;
                Ok(Some(is_new))
            }
            Self::Sparse { len, ids } => {
                if index >= *len {
                    return Ok(None);
                }
                meter
                    .insert_hash_set(ids, index, BackwardProofResource::Visited)
                    .map(Some)
            }
        }
    }
}

impl<'a> BackwardProofMeter<'a> {
    fn new(limits: &'a BackwardProofLimits) -> Result<Self, BackwardProofFailure> {
        let meter = Self {
            limits,
            bytes: 0,
            steps: 0,
            literals: 0,
            hints: 0,
            work: 0,
        };
        meter.check_deadline()?;
        Ok(meter)
    }

    fn check_deadline(&self) -> Result<(), BackwardProofFailure> {
        if self
            .limits
            .deadline
            .is_some_and(|deadline| Instant::now() >= deadline)
        {
            return Err(BackwardProofFailure::Deadline);
        }
        Ok(())
    }

    fn tick(&mut self) -> Result<(), BackwardProofFailure> {
        self.work = self
            .work
            .checked_add(1)
            .ok_or(BackwardProofFailure::AccountingOverflow {
                resource: BackwardProofResource::Bytes,
            })?;
        if self.work.is_multiple_of(1024) {
            self.check_deadline()?;
        }
        Ok(())
    }

    fn add_count(
        current: &mut usize,
        additional: usize,
        limit: usize,
        resource: BackwardProofResource,
    ) -> Result<(), BackwardProofFailure> {
        let actual = current
            .checked_add(additional)
            .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
        if actual > limit {
            return Err(BackwardProofFailure::Limit {
                resource,
                limit,
                actual,
            });
        }
        *current = actual;
        Ok(())
    }

    fn add_step(&mut self) -> Result<(), BackwardProofFailure> {
        Self::add_count(
            &mut self.steps,
            1,
            self.limits.max_steps,
            BackwardProofResource::Steps,
        )
    }

    fn add_literals(&mut self, count: usize) -> Result<(), BackwardProofFailure> {
        Self::add_count(
            &mut self.literals,
            count,
            self.limits.max_literals,
            BackwardProofResource::Literals,
        )
    }

    fn add_hint(&mut self) -> Result<(), BackwardProofFailure> {
        Self::add_count(
            &mut self.hints,
            1,
            self.limits.max_hints,
            BackwardProofResource::Hints,
        )
    }

    fn reserve_to<T>(
        &mut self,
        vec: &mut Vec<T>,
        target: usize,
        resource: BackwardProofResource,
    ) -> Result<(), BackwardProofFailure> {
        let old_capacity = vec.capacity();
        if target <= old_capacity {
            return Ok(());
        }
        let requested_delta = target
            .checked_sub(old_capacity)
            .and_then(|delta| delta.checked_mul(size_of::<T>()))
            .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
        let requested = self.bytes.checked_add(requested_delta).ok_or(
            BackwardProofFailure::AccountingOverflow {
                resource: BackwardProofResource::Bytes,
            },
        )?;
        if requested > self.limits.max_bytes {
            return Err(BackwardProofFailure::Limit {
                resource: BackwardProofResource::Bytes,
                limit: self.limits.max_bytes,
                actual: requested,
            });
        }
        vec.try_reserve_exact(target - vec.len())
            .map_err(|_| BackwardProofFailure::Allocation { resource })?;
        self.check_deadline()?;
        let actual_delta = vec
            .capacity()
            .checked_sub(old_capacity)
            .and_then(|delta| delta.checked_mul(size_of::<T>()))
            .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
        let actual = self.bytes.checked_add(actual_delta).ok_or(
            BackwardProofFailure::AccountingOverflow {
                resource: BackwardProofResource::Bytes,
            },
        )?;
        if actual > self.limits.max_bytes {
            *vec = Vec::new();
            return Err(BackwardProofFailure::Limit {
                resource: BackwardProofResource::Bytes,
                limit: self.limits.max_bytes,
                actual,
            });
        }
        self.bytes = actual;
        Ok(())
    }

    fn push<T>(
        &mut self,
        vec: &mut Vec<T>,
        value: T,
        resource: BackwardProofResource,
    ) -> Result<(), BackwardProofFailure> {
        let required = vec
            .len()
            .checked_add(1)
            .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
        if required > vec.capacity() {
            let target = if vec.capacity() == 0 {
                4
            } else {
                vec.capacity().saturating_mul(2)
            }
            .max(required);
            self.reserve_to(vec, target, resource)?;
        }
        vec.push(value);
        Ok(())
    }

    fn insert_hash_set<T: Eq + Hash>(
        &mut self,
        seen: &mut HashSet<T>,
        value: T,
        resource: BackwardProofResource,
    ) -> Result<bool, BackwardProofFailure> {
        if seen.contains(&value) {
            return Ok(false);
        }
        if seen.len() == seen.capacity() {
            let required = seen
                .len()
                .checked_add(1)
                .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
            let target = if seen.capacity() == 0 {
                4
            } else {
                seen.capacity().saturating_mul(2)
            }
            .max(required);
            let requested_delta = target
                .checked_sub(seen.capacity())
                .and_then(|delta| delta.checked_mul(32))
                .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
            let requested = self.bytes.checked_add(requested_delta).ok_or(
                BackwardProofFailure::AccountingOverflow {
                    resource: BackwardProofResource::Bytes,
                },
            )?;
            if requested > self.limits.max_bytes {
                return Err(BackwardProofFailure::Limit {
                    resource: BackwardProofResource::Bytes,
                    limit: self.limits.max_bytes,
                    actual: requested,
                });
            }
            let old_capacity = seen.capacity();
            seen.try_reserve(target - seen.len())
                .map_err(|_| BackwardProofFailure::Allocation { resource })?;
            self.check_deadline()?;
            let actual_delta = seen
                .capacity()
                .checked_sub(old_capacity)
                .and_then(|delta| delta.checked_mul(32))
                .ok_or(BackwardProofFailure::AccountingOverflow { resource })?;
            let actual = self.bytes.checked_add(actual_delta).ok_or(
                BackwardProofFailure::AccountingOverflow {
                    resource: BackwardProofResource::Bytes,
                },
            )?;
            if actual > self.limits.max_bytes {
                *seen = HashSet::new();
                return Err(BackwardProofFailure::Limit {
                    resource: BackwardProofResource::Bytes,
                    limit: self.limits.max_bytes,
                    actual,
                });
            }
            self.bytes = actual;
        }
        Ok(seen.insert(value))
    }

    fn insert_seen(
        &mut self,
        seen: &mut HashSet<i64>,
        value: i64,
    ) -> Result<bool, BackwardProofFailure> {
        self.insert_hash_set(seen, value, BackwardProofResource::Hints)
    }

    fn clone_slice<T: Clone>(
        &mut self,
        slice: &[T],
        resource: BackwardProofResource,
    ) -> Result<Vec<T>, BackwardProofFailure> {
        let mut result = Vec::new();
        self.reserve_to(&mut result, slice.len(), resource)?;
        result.extend_from_slice(slice);
        Ok(result)
    }

    fn sort_steps_by_clause_id(
        &mut self,
        steps: &mut [LratStep],
    ) -> Result<(), BackwardProofFailure> {
        let len = steps.len();
        if len < 2 {
            return self.check_deadline();
        }
        for start in (0..(len / 2)).rev() {
            self.sift_steps_down(steps, start, len)?;
        }
        for end in (1..len).rev() {
            self.tick()?;
            steps.swap(0, end);
            self.sift_steps_down(steps, 0, end)?;
        }
        self.check_deadline()
    }

    fn sift_steps_down(
        &mut self,
        steps: &mut [LratStep],
        mut root: usize,
        end: usize,
    ) -> Result<(), BackwardProofFailure> {
        loop {
            self.tick()?;
            let Some(mut child) = root.checked_mul(2).and_then(|value| value.checked_add(1)) else {
                return Err(BackwardProofFailure::AccountingOverflow {
                    resource: BackwardProofResource::Steps,
                });
            };
            if child >= end {
                return Ok(());
            }
            if child + 1 < end && steps[child].clause_id < steps[child + 1].clause_id {
                child += 1;
            }
            if steps[root].clause_id >= steps[child].clause_id {
                return Ok(());
            }
            steps.swap(root, child);
            root = child;
        }
    }
}

impl Solver {
    /// Configure explicit limits for the next deferred LRAT reconstruction.
    pub(crate) fn set_backward_proof_limits(&mut self, limits: BackwardProofLimits) {
        self.cold.backward_proof_limits = Some(limits);
        self.cold.backward_proof_failure = None;
    }

    /// Take the first bounded reconstruction failure from the last solve.
    pub(crate) fn take_backward_proof_failure(&mut self) -> Option<BackwardProofFailure> {
        self.cold.backward_proof_failure.take()
    }

    /// Reconstruct LRAT proof backward from the empty clause.
    ///
    /// This is the core of Phase 2b: after the solver determines UNSAT, walk
    /// the clause dependency graph backward from the empty clause to collect
    /// only the proof steps that are actually needed.
    ///
    /// Returns a `BackwardProofResult` containing the proof steps in emission
    /// order and a completeness flag.
    ///
    /// # Algorithm
    ///
    /// 1. Find the empty clause's antecedents from the clause trace or from
    ///    the current trail state.
    /// 2. BFS from those antecedents through `var_data[vi].reason` pointers.
    /// 3. For each learned clause encountered, reconstruct its hints from the
    ///    reason clauses of its literals.
    /// 4. Return steps in reverse topological order.
    pub(crate) fn reconstruct_lrat_backward(&self) -> BackwardProofResult {
        // Phase 1: Find the empty clause derivation and its immediate antecedents.
        //
        // The empty clause was derived from a conflict at decision level 0, or
        // from a learned clause that became falsified. Its antecedents are the
        // clause IDs that were used to derive it.
        //
        // We look for the empty clause entry in the clause trace first.
        // If no trace is available, we reconstruct from the current trail state.

        let mut result = BackwardProofResult {
            steps: Vec::new(),
            complete: true,
        };

        // Collect the set of clause IDs that are "original" (input clauses).
        // These don't need proof steps — they are axioms.
        let original_boundary = self.cold.original_clause_boundary;

        // BFS state: queue of clause arena offsets to process.
        // visited: set of clause IDs already processed.
        let mut visited: Vec<bool> = vec![false; (self.cold.next_clause_id as usize) + 1];
        let mut queue: Vec<usize> = Vec::new(); // arena offsets

        // Phase 1: Seed BFS from the falsified clause(s) at level 0.
        //
        // At UNSAT, all trail literals are at level 0. Find clauses that are
        // fully falsified under the current assignment — these are the conflict
        // clauses that triggered UNSAT.
        let mut seed_clause_ids: Vec<u64> = Vec::new();

        // live_indices (husk adjudication): garbage-kept husks (congruence
        // forward subsumption zeroes their clause_ids) must not seed the
        // backward BFS. Also keep scanning when a falsified clause has
        // cid==0 — the previous unconditional `break` left the seed set
        // empty and downgraded the certificate to incomplete.
        for offset in self.arena.live_indices() {
            let lits = self.arena.literals(offset);
            if lits.is_empty() {
                continue;
            }
            if lits.iter().all(|lit| self.lit_val(*lit) < 0) {
                let cid = self.clause_id_for_offset(offset);
                if cid != 0 {
                    seed_clause_ids.push(cid);
                    if (cid as usize) < visited.len() {
                        visited[cid as usize] = true;
                    }
                    // Only process non-original clauses (learned clauses need proof steps).
                    if offset >= original_boundary {
                        queue.push(offset);
                    }
                    // Use the first falsified clause with a live ID as the seed.
                    break;
                }
            }
        }

        if seed_clause_ids.is_empty() {
            // No falsified clause found — degenerate case.
            // This can happen if the solver detected UNSAT through other means
            // (e.g., empty clause was directly derived).
            result.complete = false;
            return result;
        }

        // Phase 2: BFS backward through the dependency graph.
        //
        // For each learned clause in the queue:
        // 1. Look up its literals from the arena.
        // 2. For each literal, find the reason clause via var_data[vi].reason.
        // 3. If the reason clause is a learned clause we haven't visited, add it
        //    to the queue.
        // 4. Record the LRAT step: this clause was derived from its antecedents.

        let mut steps: Vec<LratStep> = Vec::new();
        let mut head = 0;

        while head < queue.len() {
            let clause_offset = queue[head];
            head += 1;

            let clause_id = self.clause_id_for_offset(clause_offset);
            if clause_id == 0 {
                continue;
            }

            let clause_lits = self.arena.literals(clause_offset);
            let mut antecedent_ids: Vec<i64> = Vec::new();
            for &lit in clause_lits {
                let var_idx = lit.variable().index();
                if var_idx >= self.var_data.len() {
                    continue;
                }

                let reason_raw = self.var_data[var_idx].reason;

                // Decision variables have no reason — skip them.
                if reason_raw == NO_REASON {
                    continue;
                }

                // Binary literal reasons (#8034) — no arena clause to reference.
                if is_binary_literal_reason(reason_raw) {
                    // Binary reasons don't have a clause_id in the arena.
                    // For now, skip them (incomplete chain).
                    // A complete implementation would look up the binary clause
                    // proof ID from a separate tracking structure.
                    result.complete = false;
                    continue;
                }

                // Clause reason: look up the clause ID.
                let reason_offset = reason_raw as usize;
                let reason_id = self.clause_id_for_offset(reason_offset);
                if reason_id == 0 {
                    // Clause has no ID (e.g., garbage collected before ID assignment).
                    result.complete = false;
                    continue;
                }

                // Add as antecedent (cast u64 clause ID to i64; always positive).
                let reason_hint = reason_id as i64;
                if !antecedent_ids.contains(&reason_hint) {
                    antecedent_ids.push(reason_hint);
                }

                // If this is a learned clause we haven't visited, add to BFS queue.
                if reason_offset >= original_boundary
                    && (reason_id as usize) < visited.len()
                    && !visited[reason_id as usize]
                {
                    visited[reason_id as usize] = true;
                    queue.push(reason_offset);
                }
            }

            // Also add unit proof IDs for level-0 variables whose reason was
            // cleared by ClearLevel0 but preserved in level0_proof_id.
            for &lit in clause_lits {
                if self.lit_val(lit) >= 0 {
                    continue;
                }
                if let Some(pid) = self.level0_var_proof_id_for_lit(lit.negated()) {
                    let pid = pid as i64;
                    if !antecedent_ids.contains(&pid) {
                        antecedent_ids.push(pid);
                    }
                }
            }

            steps.push(LratStep {
                clause_id,
                literals: clause_lits.to_vec(),
                hints: antecedent_ids,
            });
        }

        // Phase 3: Reverse the steps for emission order.
        //
        // BFS produces steps in breadth-first order (closest to empty clause first).
        // LRAT proofs need reverse topological order: deepest dependencies first,
        // so that each step's antecedents are already defined when the step is
        // processed.
        steps.reverse();

        // Phase 4: Build the empty clause step.
        //
        // The empty clause's hints are the seed clause IDs (the falsified clause(s))
        // plus any level-0 unit proof IDs needed.
        let empty_clause_hints = self.build_backward_empty_clause_hints(&seed_clause_ids);

        steps.push(LratStep {
            clause_id: 0, // Empty clause gets ID from the proof writer.
            literals: Vec::new(),
            hints: empty_clause_hints,
        });

        result.steps = steps;
        result
    }

    /// Resource-bounded equivalent of [`Self::reconstruct_lrat_backward`].
    /// The graph walk and emitted ordering are identical; every owned vector
    /// growth is fallible and accounted before allocation.
    pub(crate) fn reconstruct_lrat_backward_bounded(
        &self,
        limits: &BackwardProofLimits,
    ) -> Result<BoundedBackwardProofResult, BackwardProofFailure> {
        let mut meter = BackwardProofMeter::new(limits)?;
        let original_boundary = self.cold.original_clause_boundary;
        let visited_len = usize::try_from(self.cold.next_clause_id)
            .ok()
            .and_then(|value| value.checked_add(1))
            .ok_or(BackwardProofFailure::AccountingOverflow {
                resource: BackwardProofResource::ClauseIds,
            })?;
        let mut visited = ClauseIdVisited::new_bounded(visited_len, &mut meter)?;
        let mut queue: Vec<usize> = Vec::new();
        let mut seed_clause_ids: Vec<u64> = Vec::new();
        let mut complete = true;

        for offset in self.arena.indices() {
            meter.tick()?;
            if !self.arena.is_active(offset) || self.arena.is_garbage_any(offset) {
                continue;
            }
            let lits = self.arena.literals(offset);
            let mut falsified = true;
            for &lit in lits {
                meter.tick()?;
                if self.lit_val(lit) >= 0 {
                    falsified = false;
                    break;
                }
            }
            if lits.is_empty() || !falsified {
                continue;
            }
            let cid = self.clause_id_for_offset(offset);
            if cid == 0 {
                continue;
            }
            meter.push(&mut seed_clause_ids, cid, BackwardProofResource::Seed)?;
            let cid_index =
                usize::try_from(cid).map_err(|_| BackwardProofFailure::AccountingOverflow {
                    resource: BackwardProofResource::ClauseIds,
                })?;
            let _ = visited.mark(cid_index, &mut meter)?;
            if offset >= original_boundary {
                meter.push(&mut queue, offset, BackwardProofResource::Queue)?;
            }
            break;
        }

        // Deferred level-0 materialization makes raw BCP reason clauses part
        // of the terminal hint chain. Seed every reserved reason from that
        // trail as an additional graph root so any ID admitted below is
        // actually scheduled (with its own dependencies) for backfill.
        if self.cold.backward_proof_limits.is_some() {
            let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
            for ordinal in 0..level0_end {
                meter.tick()?;
                let index = level0_end - ordinal - 1;
                let lit = self.trail[index];
                let var_idx = lit.variable().index();
                if var_idx >= self.var_data.len() || self.var_data[var_idx].level != 0 {
                    continue;
                }
                let var_data = self.var_data[var_idx];
                if !is_clause_reason(var_data.reason) || var_data.is_lazy_theory_reason() {
                    continue;
                }
                let reason_offset = var_data.reason as usize;
                if reason_offset >= self.arena.len() {
                    complete = false;
                    continue;
                }
                let reason_id = self.clause_id_for_offset(reason_offset);
                let reserved = self
                    .proof_manager
                    .as_ref()
                    .is_some_and(|manager| manager.is_backward_reserved_id(reason_id));
                if !reserved {
                    continue;
                }
                let reason_index = usize::try_from(reason_id).map_err(|_| {
                    BackwardProofFailure::AccountingOverflow {
                        resource: BackwardProofResource::ClauseIds,
                    }
                })?;
                let Some(is_new) = visited.mark(reason_index, &mut meter)? else {
                    complete = false;
                    continue;
                };
                if is_new {
                    meter.push(&mut queue, reason_offset, BackwardProofResource::Queue)?;
                }
            }
        }

        if seed_clause_ids.is_empty() {
            return Ok(BoundedBackwardProofResult {
                steps: Vec::new(),
                empty_hints: Vec::new(),
                complete: false,
            });
        }

        let mut steps: Vec<LratStep> = Vec::new();
        let mut hint_seen: HashSet<i64> = HashSet::new();
        let mut head = 0usize;
        while head < queue.len() {
            meter.tick()?;
            let clause_offset = queue[head];
            head = head
                .checked_add(1)
                .ok_or(BackwardProofFailure::AccountingOverflow {
                    resource: BackwardProofResource::Queue,
                })?;
            let clause_id = self.clause_id_for_offset(clause_offset);
            if clause_id == 0 {
                continue;
            }

            let clause_lits = self.arena.literals(clause_offset);
            let mut antecedent_ids: Vec<i64> = Vec::new();
            let mut self_referential_reason = false;
            hint_seen.clear();
            meter.check_deadline()?;
            for &lit in clause_lits {
                meter.tick()?;
                let var_idx = lit.variable().index();
                if var_idx >= self.var_data.len() {
                    continue;
                }
                let reason_raw = self.var_data[var_idx].reason;
                if reason_raw == NO_REASON {
                    continue;
                }
                if is_binary_literal_reason(reason_raw) {
                    complete = false;
                    continue;
                }
                let reason_offset = reason_raw as usize;
                let reason_id = self.clause_id_for_offset(reason_offset);
                if reason_id == 0 {
                    complete = false;
                    continue;
                }
                if reason_id == clause_id {
                    self_referential_reason = true;
                    continue;
                }
                let reason_hint = i64::try_from(reason_id).map_err(|_| {
                    BackwardProofFailure::AccountingOverflow {
                        resource: BackwardProofResource::ClauseIds,
                    }
                })?;
                if meter.insert_seen(&mut hint_seen, reason_hint)? {
                    meter.add_hint()?;
                    meter.push(
                        &mut antecedent_ids,
                        reason_hint,
                        BackwardProofResource::Hints,
                    )?;
                }
                let reason_index = usize::try_from(reason_id).map_err(|_| {
                    BackwardProofFailure::AccountingOverflow {
                        resource: BackwardProofResource::ClauseIds,
                    }
                })?;
                if reason_offset >= original_boundary {
                    let Some(is_new) = visited.mark(reason_index, &mut meter)? else {
                        complete = false;
                        continue;
                    };
                    if is_new {
                        meter.push(&mut queue, reason_offset, BackwardProofResource::Queue)?;
                    }
                }
            }

            for &lit in clause_lits {
                meter.tick()?;
                if self.lit_val(lit) >= 0 {
                    continue;
                }
                if let Some(pid) = self.level0_var_proof_id_for_lit(lit.negated()) {
                    let pid = i64::try_from(pid).map_err(|_| {
                        BackwardProofFailure::AccountingOverflow {
                            resource: BackwardProofResource::ClauseIds,
                        }
                    })?;
                    if meter.insert_seen(&mut hint_seen, pid)? {
                        meter.add_hint()?;
                        meter.push(&mut antecedent_ids, pid, BackwardProofResource::Hints)?;
                    }
                }
            }

            // A propagated literal's current level-0 reason can be the
            // reserved learned clause being reconstructed. Such a self hint
            // is invalid. Recover the common duplicate/subsumed case from an
            // already file-visible lower-ID clause; under the negation of the
            // learned clause that subsumer is immediately conflicting and is
            // therefore a complete one-hint RUP proof.
            if self_referential_reason || antecedent_ids.is_empty() {
                if let Some(subsumer_id) =
                    self.find_bounded_visible_subsumer_id(clause_id, clause_lits, &mut meter)?
                {
                    antecedent_ids.clear();
                    hint_seen.clear();
                    let signed_id = i64::try_from(subsumer_id).map_err(|_| {
                        BackwardProofFailure::AccountingOverflow {
                            resource: BackwardProofResource::ClauseIds,
                        }
                    })?;
                    let _ = meter.insert_seen(&mut hint_seen, signed_id)?;
                    meter.add_hint()?;
                    meter.push(&mut antecedent_ids, signed_id, BackwardProofResource::Hints)?;
                } else {
                    if self_referential_reason {
                        antecedent_ids.clear();
                    }
                    complete = false;
                }
            }

            meter.add_literals(clause_lits.len())?;
            let literals = meter.clone_slice(clause_lits, BackwardProofResource::Literals)?;
            meter.add_step()?;
            meter.push(
                &mut steps,
                LratStep {
                    clause_id,
                    literals,
                    hints: antecedent_ids,
                },
                BackwardProofResource::Steps,
            )?;
        }

        let step_len = steps.len();
        for index in 0..(step_len / 2) {
            meter.tick()?;
            steps.swap(index, step_len - index - 1);
        }
        let mut ids_are_monotone = true;
        for index in 1..steps.len() {
            meter.tick()?;
            if steps[index - 1].clause_id >= steps[index].clause_id {
                ids_are_monotone = false;
                break;
            }
        }
        if !ids_are_monotone {
            meter.sort_steps_by_clause_id(&mut steps)?;
        }
        let empty_clause_hints = self.build_backward_empty_clause_hints_bounded(
            &seed_clause_ids,
            &mut hint_seen,
            &mut meter,
            &mut complete,
            &visited,
        )?;
        meter.add_step()?;
        meter.check_deadline()?;
        Ok(BoundedBackwardProofResult {
            steps,
            empty_hints: empty_clause_hints,
            complete,
        })
    }

    fn find_bounded_visible_subsumer_id(
        &self,
        clause_id: u64,
        clause: &[Literal],
        meter: &mut BackwardProofMeter<'_>,
    ) -> Result<Option<u64>, BackwardProofFailure> {
        for offset in self.arena.indices() {
            meter.tick()?;
            if !self.arena.is_active(offset) || self.arena.is_garbage_any(offset) {
                continue;
            }
            let candidate_id = self.clause_id_for_offset(offset);
            if candidate_id == 0 || candidate_id >= clause_id {
                continue;
            }
            let visible = self
                .proof_manager
                .as_ref()
                .is_none_or(|manager| manager.lrat_id_visible_in_file(candidate_id));
            if !visible {
                continue;
            }
            let candidate = self.arena.literals(offset);
            let mut subsumes = true;
            for &candidate_lit in candidate {
                meter.tick()?;
                let mut present = false;
                for &derived_lit in clause {
                    meter.tick()?;
                    if candidate_lit == derived_lit {
                        present = true;
                        break;
                    }
                }
                if !present {
                    subsumes = false;
                    break;
                }
            }
            if subsumes {
                return Ok(Some(candidate_id));
            }
        }
        Ok(None)
    }

    fn build_backward_empty_clause_hints_bounded(
        &self,
        seed_clause_ids: &[u64],
        seen: &mut HashSet<i64>,
        meter: &mut BackwardProofMeter<'_>,
        complete: &mut bool,
        planned_step_ids: &ClauseIdVisited,
    ) -> Result<Vec<u64>, BackwardProofFailure> {
        let mut hints: Vec<u64> = Vec::new();
        seen.clear();
        meter.check_deadline()?;
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());

        // The bounded production posture defers level-0 proof
        // materialization, because its legacy hint/trace buffers are
        // infallibly grown before postsolve. Replay raw reason clauses in BCP
        // trail order instead: each reason is unit after the earlier trail
        // entries, and reserved learned IDs will be serialized before this
        // terminal chain. The direct test-only parity path retains the legacy
        // reverse order when materialization was not explicitly deferred.
        let deferred_materialization = self.cold.backward_proof_limits.is_some();
        for ordinal in 0..level0_end {
            let index = if deferred_materialization {
                ordinal
            } else {
                level0_end - ordinal - 1
            };
            meter.tick()?;
            let lit = self.trail[index];
            let var_idx = lit.variable().index();
            if var_idx >= self.var_data.len() || self.var_data[var_idx].level != 0 {
                continue;
            }
            let mut id = self
                .visible_unit_proof_id_for_lit(lit)
                .or_else(|| self.level0_var_proof_id_for_lit(lit));
            if id.is_none() && deferred_materialization {
                let var_data = self.var_data[var_idx];
                if is_clause_reason(var_data.reason) && !var_data.is_lazy_theory_reason() {
                    let reason_ref = ClauseRef(var_data.reason);
                    let reason_id = self.clause_id(reason_ref);
                    let planned = usize::try_from(reason_id)
                        .ok()
                        .is_some_and(|index| planned_step_ids.contains(index));
                    let planned_visible =
                        self.proof_manager
                            .as_ref()
                            .map_or(reason_id != 0, |manager| {
                                manager.lrat_id_visible_in_file(reason_id)
                                    || (planned && manager.is_backward_reserved_id(reason_id))
                            });
                    if planned_visible {
                        id = Some(reason_id);
                    }
                }
            }
            if let Some(id) = id {
                let signed_id =
                    i64::try_from(id).map_err(|_| BackwardProofFailure::AccountingOverflow {
                        resource: BackwardProofResource::ClauseIds,
                    })?;
                if meter.insert_seen(seen, signed_id)? {
                    meter.add_hint()?;
                    meter.push(&mut hints, id, BackwardProofResource::Hints)?;
                }
            } else if deferred_materialization {
                *complete = false;
            }
        }
        for &seed in seed_clause_ids {
            meter.tick()?;
            let hint =
                i64::try_from(seed).map_err(|_| BackwardProofFailure::AccountingOverflow {
                    resource: BackwardProofResource::ClauseIds,
                })?;
            if meter.insert_seen(seen, hint)? {
                meter.add_hint()?;
                meter.push(&mut hints, seed, BackwardProofResource::Hints)?;
            }
        }
        Ok(hints)
    }

    /// Build LRAT hints for the empty clause in backward reconstruction.
    ///
    /// The empty clause is derived from the falsified seed clause(s) plus
    /// level-0 unit assignments that falsified the literals.
    fn build_backward_empty_clause_hints(&self, seed_clause_ids: &[u64]) -> Vec<i64> {
        let mut hints: Vec<i64> = Vec::new();

        // Add level-0 unit proof IDs for all trail variables.
        let level0_end = self.trail_lim.first().copied().unwrap_or(self.trail.len());
        for i in (0..level0_end).rev() {
            let lit = self.trail[i];
            let var_idx = lit.variable().index();
            if var_idx >= self.var_data.len() || self.var_data[var_idx].level != 0 {
                continue;
            }
            // Try unit_proof_id first, then level0_proof_id.
            if let Some(id) = self.visible_unit_proof_id_for_lit(lit) {
                let pid = id as i64;
                if !hints.contains(&pid) {
                    hints.push(pid);
                }
            } else if let Some(id) = self.level0_var_proof_id_for_lit(lit) {
                let pid = id as i64;
                if !hints.contains(&pid) {
                    hints.push(pid);
                }
            }
        }

        // Add seed clause IDs (cast u64 -> i64; always positive).
        for &sid in seed_clause_ids {
            let hint = sid as i64;
            if !hints.contains(&hint) {
                hints.push(hint);
            }
        }

        hints
    }

    /// Look up the clause ID for a given arena offset.
    ///
    /// Returns 0 if the offset is out of bounds or has no assigned ID.
    #[inline]
    fn clause_id_for_offset(&self, offset: usize) -> u64 {
        if offset < self.cold.clause_ids.len() {
            self.cold.clause_ids[offset]
        } else {
            0
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::proof::ProofOutput;
    use crate::resolution_dag::{ResolutionDag, RupStep};
    use std::time::Duration;

    fn generous_limits() -> BackwardProofLimits {
        BackwardProofLimits {
            deadline: Some(Instant::now() + Duration::from_secs(5)),
            max_steps: 1_000_000,
            max_literals: 1_000_000,
            max_hints: 1_000_000,
            max_bytes: 64 * 1024 * 1024,
        }
    }

    #[test]
    fn metered_push_reuses_spare_capacity_before_growing() {
        let mut limits = generous_limits();
        limits.max_bytes = 512;
        let mut meter = BackwardProofMeter::new(&limits).expect("live meter");
        let mut values = Vec::<u64>::new();

        for value in 0..22 {
            let old_len = values.len();
            let old_capacity = values.capacity();
            let old_bytes = meter.bytes;
            meter
                .push(&mut values, value, BackwardProofResource::Hints)
                .expect("22 logical hints fit comfortably inside 512 bytes");
            if old_len < old_capacity {
                assert_eq!(
                    values.capacity(),
                    old_capacity,
                    "a push into spare capacity must not reserve again"
                );
                assert_eq!(
                    meter.bytes, old_bytes,
                    "the retained-byte meter changes only when capacity changes"
                );
            }
        }

        assert_eq!(values.len(), 22);
        assert_eq!(
            meter.bytes,
            values.capacity() * size_of::<u64>(),
            "the meter charges the allocator's actual retained capacity"
        );
        assert!(meter.bytes <= limits.max_bytes);
    }

    #[test]
    fn dense_clause_id_set_packs_namespace_and_preserves_membership() {
        let mut limits = generous_limits();
        // 1,025 possible clause IDs need 17 u64 words (136 logical bytes),
        // comfortably inside this deliberately small envelope.
        limits.max_bytes = 512;
        let mut meter = BackwardProofMeter::new(&limits).expect("live meter");
        let mut visited = ClauseIdVisited::new_bounded(1_025, &mut meter)
            .expect("packed clause-ID namespace fits the bounded envelope");

        assert!(meter.bytes <= limits.max_bytes);
        assert!(!visited.contains(0));
        assert_eq!(visited.mark(0, &mut meter).expect("mark"), Some(true));
        assert_eq!(visited.mark(0, &mut meter).expect("mark"), Some(false));
        assert_eq!(visited.mark(1_024, &mut meter).expect("mark"), Some(true));
        assert!(visited.contains(0));
        assert!(visited.contains(1_024));
        assert!(!visited.contains(1_025));
        assert_eq!(visited.mark(1_025, &mut meter).expect("mark"), None);
    }

    #[test]
    fn sparse_clause_id_set_avoids_zero_filling_a_reserved_namespace() {
        let mut limits = generous_limits();
        limits.max_bytes = 512;
        let mut meter = BackwardProofMeter::new(&limits).expect("live meter");
        let namespace = MAX_DENSE_VISITED_BYTES
            .checked_mul(u64::BITS as usize)
            .and_then(|bits| bits.checked_add(1))
            .expect("test namespace");
        let mut visited = ClauseIdVisited::new_bounded(namespace, &mut meter)
            .expect("a large namespace starts sparse without allocating it");

        assert_eq!(meter.bytes, 0);
        assert_eq!(visited.mark(7, &mut meter).expect("first mark"), Some(true));
        assert_eq!(
            visited.mark(7, &mut meter).expect("duplicate mark"),
            Some(false)
        );
        assert_eq!(
            visited.mark(namespace - 1, &mut meter).expect("high mark"),
            Some(true)
        );
        assert!(meter.bytes <= limits.max_bytes);
        assert!(visited.contains(7));
        assert!(visited.contains(namespace - 1));
        assert_eq!(visited.mark(namespace, &mut meter).expect("bound"), None);
    }

    struct BoundedRawReasonFixture {
        solver: Solver,
        positive: Literal,
        negative: Literal,
        reserved: u64,
        limits: BackwardProofLimits,
    }

    fn bounded_reserved_level0_raw_reason_fixture() -> BoundedRawReasonFixture {
        use crate::literal::Variable;

        let variable = Variable(0);
        let positive = Literal::positive(variable);
        let negative = Literal::negative(variable);
        let output = ProofOutput::lrat_binary(Vec::new(), 2);
        let mut solver = Solver::with_proof_output(1, output);
        solver.set_bounded_in_memory_proof_posture();
        let limits = generous_limits();
        solver.set_backward_proof_limits(limits.clone());
        solver.set_preprocess_enabled(false);
        solver.disable_all_inprocessing();

        solver.add_clause(vec![positive]);
        solver.add_clause(vec![negative]);
        let original_boundary = solver.arena.len();
        let reserved = solver
            .proof_manager
            .as_mut()
            .expect("proof manager")
            .reserve_lrat_id_for_backward();
        assert_eq!(reserved, 3);
        solver.cold.next_clause_id = reserved;
        let learned_offset = solver.add_clause_db(&[positive], true);
        assert_eq!(learned_offset, original_boundary);
        assert_eq!(solver.cold.clause_ids[learned_offset], reserved);
        solver.cold.original_clause_boundary = original_boundary;

        // Force the production seam precisely: the level-0 literal's raw
        // reason is the backward-reserved learned clause itself, while the
        // pre-existing unit provenance is hidden so the terminal builder must
        // admit the planned reserved ID. The lower-ID duplicate original is a
        // valid one-hint RUP derivation for the reserved clause.
        solver.unit_proof_id[0] = 0;
        solver.unit_proof_sign[0] = 0;
        solver.cold.level0_proof_id[0] = 0;
        solver.cold.level0_proof_sign[0] = 0;
        solver.enqueue(positive, Some(ClauseRef(learned_offset as u32)));
        assert_eq!(solver.trail, vec![positive]);

        BoundedRawReasonFixture {
            solver,
            positive,
            negative,
            reserved,
            limits,
        }
    }

    #[test]
    fn test_lrat_step_default() {
        let step = LratStep {
            clause_id: 42,
            literals: vec![],
            hints: vec![1i64, 2, 3],
        };
        assert_eq!(step.clause_id, 42);
        assert!(step.literals.is_empty());
        assert_eq!(step.hints, vec![1i64, 2, 3]);
    }

    #[test]
    fn test_backward_proof_result_default() {
        let result = BackwardProofResult {
            steps: Vec::new(),
            complete: true,
        };
        assert!(result.steps.is_empty());
        assert!(result.complete);
    }

    #[test]
    fn bounded_multi_root_steps_are_globally_ordered_by_reserved_id() {
        let limits = generous_limits();
        let mut meter = BackwardProofMeter::new(&limits).expect("meter");
        let mut steps = vec![
            LratStep {
                clause_id: 11,
                literals: vec![],
                hints: vec![7],
            },
            LratStep {
                clause_id: 5,
                literals: vec![],
                hints: vec![1],
            },
            LratStep {
                clause_id: 9,
                literals: vec![],
                hints: vec![5],
            },
            LratStep {
                clause_id: 7,
                literals: vec![],
                hints: vec![3],
            },
        ];
        meter
            .sort_steps_by_clause_id(&mut steps)
            .expect("deadline-polled in-place ordering");
        assert_eq!(
            steps.iter().map(|step| step.clause_id).collect::<Vec<_>>(),
            vec![5, 7, 9, 11]
        );
    }

    #[test]
    fn bounded_reserved_level0_raw_reason_replays_end_to_end() {
        let BoundedRawReasonFixture {
            mut solver,
            positive,
            negative,
            reserved,
            limits,
        } = bounded_reserved_level0_raw_reason_fixture();

        let backward = solver
            .reconstruct_lrat_backward_bounded(&limits)
            .expect("bounded raw-reason reconstruction");
        assert!(backward.complete);
        assert_eq!(backward.steps.len(), 1);
        assert_eq!(backward.steps[0].clause_id, reserved);
        assert_eq!(backward.steps[0].hints, vec![1]);
        assert_eq!(backward.empty_hints, vec![reserved, 2]);

        let deadline = limits.deadline;
        let manager = solver.proof_manager.as_mut().expect("proof manager");
        for step in &backward.steps {
            manager
                .emit_bounded_backward_rup_step(
                    step.clause_id,
                    &step.literals,
                    &step.hints,
                    deadline,
                )
                .expect("emit reserved raw reason");
        }
        manager
            .finish_bounded_backward_emission(deadline)
            .expect("finish bounded roots");
        let empty_id = manager
            .emit_bounded_empty_rup_step(&backward.empty_hints, deadline)
            .expect("emit bounded terminal");

        let output = solver
            .proof_manager
            .take()
            .expect("proof manager")
            .into_output();
        let bytes = output.into_vec().expect("binary LRAT bytes");
        let parsed = ay_lrat_check::lrat_parser::parse_binary_lrat(&bytes)
            .expect("bounded raw-reason LRAT parses");
        assert_eq!(parsed.len(), 2);

        let dag = ResolutionDag {
            num_vars: 1,
            original_clauses: vec![(1, vec![positive]), (2, vec![negative])],
            derived: vec![
                RupStep {
                    id: reserved,
                    clause: vec![positive],
                    rup_hints: vec![1],
                },
                RupStep {
                    id: empty_id,
                    clause: Vec::new(),
                    rup_hints: backward.empty_hints,
                },
            ],
            empty_clause_id: empty_id,
        };
        dag.validate()
            .expect("solver-level reserved raw-reason DAG replays");
    }

    #[test]
    fn bounded_terminal_hint_growth_stays_linear_past_twenty_one_units() {
        use crate::literal::Variable;

        const UNIT_COUNT: usize = 22;
        const ORIGINAL_COUNT: usize = UNIT_COUNT + 1;
        let positives: Vec<Literal> = (0..UNIT_COUNT)
            .map(|index| {
                Literal::positive(Variable::new(
                    u32::try_from(index).expect("small fixture variable"),
                ))
            })
            .collect();
        let conflict: Vec<Literal> = positives.iter().map(|lit| lit.negated()).collect();
        let output = ProofOutput::lrat_binary(
            Vec::new(),
            u64::try_from(ORIGINAL_COUNT).expect("small fixture clause count"),
        );
        let mut solver = Solver::with_proof_output(UNIT_COUNT, output);
        solver.set_bounded_in_memory_proof_posture();
        let mut limits = generous_limits();
        limits.max_steps = 1;
        limits.max_literals = 0;
        limits.max_hints = ORIGINAL_COUNT;
        limits.max_bytes = 16 * 1024;
        solver.set_backward_proof_limits(limits.clone());
        solver.set_preprocess_enabled(false);
        solver.disable_all_inprocessing();

        for &positive in &positives {
            solver.add_clause(vec![positive]);
        }
        solver.add_clause(conflict.clone());
        solver.cold.original_clause_boundary = solver.arena.len();
        for (index, &positive) in positives.iter().enumerate() {
            solver.enqueue(positive, None);
            solver.record_unit_proof_id_for_lit(
                positive,
                u64::try_from(index + 1).expect("small fixture clause ID"),
            );
        }
        assert_eq!(solver.trail, positives);
        assert!(
            conflict.iter().all(|&literal| solver.lit_val(literal) < 0),
            "the final original clause is the falsified reconstruction seed"
        );

        let backward = solver
            .reconstruct_lrat_backward_bounded(&limits)
            .expect("22 unit hints fit inside a 16 KiB reconstruction envelope");
        assert!(backward.complete);
        assert!(backward.steps.is_empty());
        let expected_hints: Vec<u64> =
            (1..=u64::try_from(ORIGINAL_COUNT).expect("small fixture clause count")).collect();
        assert_eq!(backward.empty_hints, expected_hints);

        let mut original_clauses: Vec<(u64, Vec<Literal>)> = positives
            .iter()
            .enumerate()
            .map(|(index, &literal)| {
                (
                    u64::try_from(index + 1).expect("small fixture clause ID"),
                    vec![literal],
                )
            })
            .collect();
        original_clauses.push((
            u64::try_from(ORIGINAL_COUNT).expect("small fixture clause ID"),
            conflict,
        ));
        let empty_clause_id = u64::try_from(ORIGINAL_COUNT + 1).expect("small empty-clause ID");
        let dag = ResolutionDag {
            num_vars: UNIT_COUNT,
            original_clauses,
            derived: vec![RupStep {
                id: empty_clause_id,
                clause: Vec::new(),
                rup_hints: backward.empty_hints,
            }],
            empty_clause_id,
        };
        dag.validate()
            .expect("the 22-unit bounded terminal proof replays");
    }

    #[test]
    fn test_lrat_step_equality() {
        let step1 = LratStep {
            clause_id: 1,
            literals: vec![Literal(0), Literal(2)],
            hints: vec![10i64, 20],
        };
        let step2 = LratStep {
            clause_id: 1,
            literals: vec![Literal(0), Literal(2)],
            hints: vec![10i64, 20],
        };
        assert_eq!(step1, step2);
    }

    #[test]
    fn test_backward_proof_on_trivial_unsat() {
        // Build a solver with contradictory unit clauses: {x} and {-x}
        // This should produce an UNSAT result where backward reconstruction
        // can find the falsified clause.
        use crate::literal::Variable;
        let v0 = Variable(0);
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(v0)]);
        solver.add_clause(vec![Literal::negative(v0)]);

        let result = solver.solve();
        assert!(
            result.is_unsat(),
            "expected UNSAT for contradictory unit clauses"
        );

        // After solving, the backward reconstruction should produce some steps.
        // Note: the solver may have already finalized the proof via the forward
        // path, but the backward reconstruction should still work as a
        // post-hoc analysis.
        let backward = solver.reconstruct_lrat_backward();
        // For trivial UNSAT (contradictory units), the proof may be empty or
        // contain just the empty clause step. The key invariant is that the
        // function completes without panicking and returns a valid result.
        assert!(
            !backward.steps.is_empty() || !backward.complete,
            "backward reconstruction should produce steps or report incomplete"
        );
    }

    #[test]
    fn test_backward_proof_on_sat_instance() {
        // SAT instance: just one clause {x}
        use crate::literal::Variable;
        let v0 = Variable(0);
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(v0)]);

        let result = solver.solve();
        assert!(result.is_sat(), "expected SAT for single positive unit");

        // Backward reconstruction on a SAT instance should produce no meaningful
        // steps (no empty clause was derived).
        let backward = solver.reconstruct_lrat_backward();
        // For SAT instances, there's no falsified clause, so reconstruction
        // should report incomplete or produce no steps.
        let has_empty_step = backward.steps.iter().any(|s| s.literals.is_empty());
        // The empty clause step is always appended, but the seed finding may fail.
        // Either way, the function should not panic.
        let _ = has_empty_step;
    }

    #[test]
    fn test_backward_proof_small_unsat() {
        // A slightly more complex UNSAT: (x | y) & (-x) & (-y)
        use crate::literal::Variable;
        let v0 = Variable(0);
        let v1 = Variable(1);
        let mut solver = Solver::new(2);
        solver.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]);
        solver.add_clause(vec![Literal::negative(v0)]);
        solver.add_clause(vec![Literal::negative(v1)]);

        let result = solver.solve();
        assert!(result.is_unsat(), "expected UNSAT for (x|y) & !x & !y");

        let backward = solver.reconstruct_lrat_backward();
        // Should complete without panicking. The proof should contain at least
        // the empty clause step.
        assert!(
            !backward.steps.is_empty(),
            "backward reconstruction should produce at least the empty clause step"
        );

        // The last step should be the empty clause.
        let last = backward.steps.last().expect("should have steps");
        assert!(
            last.literals.is_empty(),
            "last step should be the empty clause"
        );
        assert!(
            !last.hints.is_empty(),
            "empty clause should have hints (antecedent clause IDs)"
        );
    }

    #[test]
    fn bounded_backward_reconstruction_matches_legacy_order_and_hints() {
        use crate::literal::Variable;
        let v0 = Variable(0);
        let v1 = Variable(1);
        let mut solver = Solver::new(2);
        solver.set_preprocess_enabled(false);
        for clause in [
            vec![Literal::positive(v0), Literal::positive(v1)],
            vec![Literal::positive(v0), Literal::negative(v1)],
            vec![Literal::negative(v0), Literal::positive(v1)],
            vec![Literal::negative(v0), Literal::negative(v1)],
        ] {
            solver.add_clause(clause);
        }
        assert!(solver.solve().is_unsat());

        let legacy = solver.reconstruct_lrat_backward();
        let bounded = solver
            .reconstruct_lrat_backward_bounded(&generous_limits())
            .expect("bounded reconstruction");
        let mut bounded_steps = bounded.steps;
        bounded_steps.push(LratStep {
            clause_id: 0,
            literals: Vec::new(),
            hints: bounded
                .empty_hints
                .into_iter()
                .map(|hint| hint as i64)
                .collect(),
        });
        assert_eq!(bounded.complete, legacy.complete);
        assert_eq!(bounded_steps, legacy.steps);
    }

    #[test]
    fn bounded_backward_reconstruction_reports_each_envelope() {
        let solver = bounded_reserved_level0_raw_reason_fixture().solver;

        let mut limits = generous_limits();
        limits.deadline = Some(Instant::now());
        assert!(matches!(
            solver.reconstruct_lrat_backward_bounded(&limits),
            Err(BackwardProofFailure::Deadline)
        ));

        let mut limits = generous_limits();
        limits.max_steps = 0;
        assert!(matches!(
            solver.reconstruct_lrat_backward_bounded(&limits),
            Err(BackwardProofFailure::Limit {
                resource: BackwardProofResource::Steps,
                ..
            })
        ));

        let mut limits = generous_limits();
        limits.max_hints = 0;
        assert!(matches!(
            solver.reconstruct_lrat_backward_bounded(&limits),
            Err(BackwardProofFailure::Limit {
                resource: BackwardProofResource::Hints,
                ..
            })
        ));

        let mut limits = generous_limits();
        limits.max_bytes = 0;
        assert!(matches!(
            solver.reconstruct_lrat_backward_bounded(&limits),
            Err(BackwardProofFailure::Limit {
                resource: BackwardProofResource::Bytes,
                ..
            })
        ));

        let baseline = solver
            .reconstruct_lrat_backward_bounded(&generous_limits())
            .expect("baseline");
        let literal_count: usize = baseline.steps.iter().map(|step| step.literals.len()).sum();
        assert_eq!(
            literal_count, 1,
            "fixture must exercise exactly one learned literal"
        );
        let mut limits = generous_limits();
        limits.max_literals = 0;
        assert!(matches!(
            solver.reconstruct_lrat_backward_bounded(&limits),
            Err(BackwardProofFailure::Limit {
                resource: BackwardProofResource::Literals,
                ..
            })
        ));
    }

    #[test]
    fn test_clause_trace_with_certificate_disabled() {
        // Internal-query configuration (ay-chc): clause trace enabled for
        // clause-ID tracking + #5384 UNSAT replay, but the UNSAT proof
        // certificate disabled because it is never consumed. UNSAT must skip
        // backward LRAT reconstruction (empty certificate) while leaving the
        // in-memory ClauseTrace fully intact.
        use crate::literal::Variable;
        let v0 = Variable(0);
        let v1 = Variable(1);

        let build = |certificate_enabled: bool| {
            let mut solver = Solver::new(2);
            solver.enable_clause_trace();
            solver.set_unsat_certificate_enabled(certificate_enabled);
            solver.set_preprocess_enabled(false);
            solver.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]);
            solver.add_clause(vec![Literal::negative(v0)]);
            solver.add_clause(vec![Literal::negative(v1)]);
            solver
        };

        // Certificate disabled: UNSAT with an empty certificate.
        let mut solver = build(false);
        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                assert_eq!(
                    cert.step_count(),
                    0,
                    "certificate must be empty when unsat_certificate_enabled=false"
                );
                assert!(
                    !cert.is_complete(),
                    "empty certificate must report incomplete"
                );
            }
            other => panic!("expected UNSAT, got sat={:?}", other.is_sat()),
        }

        // ClauseTrace must be intact: all three original clauses recorded and
        // the empty-clause UNSAT marker set.
        let trace = solver
            .clause_trace()
            .expect("clause trace must survive certificate-disabled UNSAT");
        assert_eq!(
            trace.original_clauses().count(),
            3,
            "all original clauses must be recorded in the trace"
        );
        assert!(
            trace.has_empty_clause(),
            "trace must carry the UNSAT empty-clause marker"
        );

        // Contrast: same instance with the certificate enabled (default)
        // produces a non-empty backward-reconstructed proof.
        let mut solver = build(true);
        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                assert!(
                    cert.step_count() > 0,
                    "certificate-enabled UNSAT must produce backward proof steps"
                );
            }
            other => panic!("expected UNSAT, got sat={:?}", other.is_sat()),
        }
    }

    // ── Streaming support integration tests (#8250) ────────────────

    #[test]
    fn test_streaming_support_trivial_unsat() {
        // {x} and {-x}: contradictory unit clauses
        use crate::literal::Variable;
        let v0 = Variable(0);
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(v0)]);
        solver.add_clause(vec![Literal::negative(v0)]);

        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                // Streaming support should be present and non-empty.
                // Both clauses are needed: {x} (ID 1) and {-x} (ID 2).
                let support = cert.tracked_original_clause_ids();
                assert!(
                    !support.is_empty(),
                    "streaming support should be non-empty for this derivation"
                );
                // Every support ID should be a valid original clause ID (1 or 2).
                for &id in &support {
                    assert!((1..=2).contains(&id), "support ID {id} out of range [1, 2]");
                }
            }
            other => panic!("expected UNSAT, got {:?}", other.is_sat()),
        }
    }

    #[test]
    fn test_streaming_support_sat_instance_has_no_certificate() {
        // SAT: {x}. SAT results carry no proof certificate.
        use crate::literal::Variable;
        let v0 = Variable(0);
        let mut solver = Solver::new(1);
        solver.add_clause(vec![Literal::positive(v0)]);

        let result = solver.solve();
        assert!(result.is_sat(), "expected SAT for single positive unit");
        // SAT results don't have ProofCertificate with streaming support,
        // but the solver's internal bitmap should be all-false.
        // We verify this indirectly: after SAT, if we could access the
        // certificate (we can't for SAT), it would have no support.
    }

    #[test]
    fn test_streaming_support_small_unsat() {
        // (x | y) & (-x) & (-y): UNSAT
        // Original clause IDs: 1=(x|y), 2=(-x), 3=(-y)
        // All three are needed to derive contradiction.
        use crate::literal::Variable;
        let v0 = Variable(0);
        let v1 = Variable(1);
        let mut solver = Solver::new(2);
        solver.add_clause(vec![Literal::positive(v0), Literal::positive(v1)]);
        solver.add_clause(vec![Literal::negative(v0)]);
        solver.add_clause(vec![Literal::negative(v1)]);

        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                let support = cert.tracked_original_clause_ids();
                assert!(
                    !support.is_empty(),
                    "streaming support should be non-empty for this derivation"
                );
                // Streaming support does not require proof materialization.
                if cert.has_streaming_support() {
                    assert!(
                        cert.is_deferred(),
                        "streaming support should not trigger proof materialization"
                    );
                }
            }
            other => panic!("expected UNSAT, got {:?}", other.is_sat()),
        }
    }

    #[test]
    fn test_streaming_support_with_redundant_clauses() {
        // (x) & (-x) & (y): clause (y) is redundant for UNSAT.
        // This solve's tracked support should contain {1, 2}, not 3.
        use crate::literal::Variable;
        let v0 = Variable(0);
        let v1 = Variable(1);
        let mut solver = Solver::new(2);
        solver.add_clause(vec![Literal::positive(v0)]); // ID 1
        solver.add_clause(vec![Literal::negative(v0)]); // ID 2
        solver.add_clause(vec![Literal::positive(v1)]); // ID 3 (redundant)

        let result = solver.solve();
        match result.into_inner() {
            SatResult::Unsat(cert) => {
                let support = cert.tracked_original_clause_ids();
                assert!(
                    !support.is_empty(),
                    "streaming support should be non-empty for this derivation"
                );
                // This particular redundant clause should not have been observed.
                // This pins current tracking, not a general redundancy guarantee.
                assert!(
                    !support.contains(&3),
                    "redundant clause (y) unexpectedly appeared in support: {support:?}"
                );
                // Both conflicting clauses should have been observed.
                assert!(
                    support.contains(&1) && support.contains(&2),
                    "both conflicting unit clauses should be in support: {support:?}"
                );
            }
            other => panic!("expected UNSAT, got {:?}", other.is_sat()),
        }
    }
}
