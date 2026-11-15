// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[derive(Clone, Copy)]
pub(super) enum Lane {
    Compaction,
    Rooted,
    Synthesis,
}

pub(super) struct Fixture {
    pub(super) trace: ClauseTrace,
    originals: Vec<(u64, Vec<Literal>)>,
    target: Vec<Literal>,
    candidates: Vec<u64>,
    pub(super) num_vars: usize,
    pub(super) expected: Vec<u64>,
}

impl Fixture {
    pub(super) fn new(lane: Lane) -> Self {
        let (clauses, target, candidates, num_vars, expected) = match lane {
            Lane::Compaction => (
                vec![vec![pos(0)], vec![neg(0)]],
                vec![],
                vec![1, 2],
                2,
                vec![1, 2],
            ),
            Lane::Rooted => (
                vec![
                    vec![pos(0)],
                    vec![neg(0), neg(1)],
                    vec![pos(1), pos(2)],
                    vec![pos(1), neg(2)],
                ],
                vec![],
                vec![3, 4],
                3,
                vec![1, 2, 3, 4],
            ),
            // The recorded tautology gives no proof. Negating the target
            // opposes a propagated root fact, so rooted repair must decline
            // and independent full synthesis finds the first unit conflict.
            Lane::Synthesis => (
                vec![vec![pos(0)], vec![neg(0)], vec![pos(1), neg(1)]],
                vec![pos(0)],
                vec![3],
                2,
                vec![1],
            ),
        };
        let mut trace = ClauseTrace::new();
        let originals: Vec<_> = clauses
            .into_iter()
            .enumerate()
            .map(|(index, clause)| {
                let id = index as u64 + 1;
                trace.add_clause(id, clause.clone(), true);
                (id, clause)
            })
            .collect();
        trace.add_clause_with_hints(
            originals.len() as u64 + 1,
            target.clone(),
            false,
            candidates.clone(),
        );
        Self {
            trace,
            originals,
            target,
            candidates,
            num_vars,
            expected,
        }
    }

    pub(super) fn state(&self) -> DerivedConversionState {
        DerivedConversionState {
            steps: vec![],
            next_canonical_id: self.originals.len() as u64 + 1,
            empty_clause_id: None,
            widening_hint_slack: 0,
            widening_byte_slack: 0,
            reconstruction_row_bound: self.num_vars + 1,
            root_state: None,
            compaction_scratch: None,
        }
    }

    pub(super) fn repair(
        &self,
        state: &mut DerivedConversionState,
        meter: &mut ConversionMeter<'_>,
    ) -> Result<Option<Vec<u64>>, ResolutionValidationError> {
        let inputs = DerivedConversionInputs {
            entries: self.trace.entries(),
            original_clauses: &self.originals,
            unit_premises: &[],
            terminal_empty_index: None,
            shape: TraceShape {
                compaction_scratch_bytes: CompactionScratch::planned_bytes(self.num_vars)?,
                synthesis_scratch_bytes: planned_synthesis_scratch_bytes(
                    self.num_vars,
                    self.candidates.len(),
                )?,
                root_index_scratch_bytes: usize::MAX,
                candidate_scheduler_bytes: usize::MAX,
                row_hint_budget: self.num_vars + 1,
                max_row_hints: self.candidates.len(),
                ..TraceShape::default()
            },
            num_vars: self.num_vars,
        };
        repair_derived_hints(
            self.trace.entries().get(self.originals.len()).unwrap(),
            &inputs,
            state,
            &self.candidates,
            self.candidates.len(),
            meter,
        )
    }

    pub(super) fn replay(&self, hints: Vec<u64>) {
        let id = self.originals.len() as u64 + 1;
        let mut derived = vec![RupStep {
            id,
            clause: self.target.clone(),
            rup_hints: hints,
        }];
        let empty_clause_id = if self.target.is_empty() {
            id
        } else {
            derived.push(RupStep {
                id: id + 1,
                clause: vec![],
                rup_hints: vec![1, 2],
            });
            id + 1
        };
        ResolutionDag {
            num_vars: self.num_vars,
            original_clauses: self.originals.clone(),
            derived,
            empty_clause_id,
        }
        .validate()
        .unwrap();
    }
}
