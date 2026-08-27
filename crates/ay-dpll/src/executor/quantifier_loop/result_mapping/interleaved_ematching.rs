// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded DPLL(T)-interleaved E-matching refinement.

use ay_core::TermId;

use super::super::super::{Executor, MAX_INTERLEAVED_EMATCHING_ROUNDS};
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::LogicCategory;

use super::super::dispatch::EmatchingRefinementRound;

pub(super) struct InterleavedEmatchingState {
    pub(super) result: Result<SolveResult>,
    pub(super) reached_instantiation_limit: bool,
    pub(super) ematching_added_instantiations: bool,
    pub(super) unsat_from_interleaved: bool,
    pub(super) has_uninstantiated_quantifiers: bool,
    pub(super) ematching_rounds_completed: u64,
    pub(super) ematching_instances_created: u64,
    had_preprocessing_instances: bool,
}

enum RefinementFlow {
    Continue,
    Stop,
}

impl InterleavedEmatchingState {
    fn record_round(&mut self, round: &EmatchingRefinementRound) {
        self.ematching_rounds_completed += 1;
        self.ematching_instances_created += round.instances_created;
        self.reached_instantiation_limit |= round.reached_limit;
        self.has_uninstantiated_quantifiers = round.has_uninstantiated;
    }

    fn record_ground_result(&mut self, result: Result<SolveResult>) -> RefinementFlow {
        match result {
            Ok(SolveResult::Sat) => {
                self.result = result;
                RefinementFlow::Continue
            }
            Ok(SolveResult::Unsat(_)) => {
                self.result = result;
                self.reached_instantiation_limit = false;
                if self.had_preprocessing_instances {
                    self.unsat_from_interleaved = true;
                }
                RefinementFlow::Stop
            }
            other => {
                self.result = other;
                RefinementFlow::Stop
            }
        }
    }
}

struct InterleavedRoundBudget {
    charged_rounds: usize,
    rounds_run: usize,
    hard_cap: usize,
}

impl InterleavedRoundBudget {
    fn new() -> Self {
        let hard_cap = if crate::ematching::relevance_config().enabled {
            MAX_INTERLEAVED_EMATCHING_ROUNDS.saturating_mul(8)
        } else {
            MAX_INTERLEAVED_EMATCHING_ROUNDS
        };
        Self {
            charged_rounds: 0,
            rounds_run: 0,
            hard_cap,
        }
    }

    fn has_capacity(&self) -> bool {
        self.charged_rounds < MAX_INTERLEAVED_EMATCHING_ROUNDS && self.rounds_run < self.hard_cap
    }

    fn begin_round(&mut self) {
        self.rounds_run += 1;
    }

    fn finish_round(&mut self, round: &EmatchingRefinementRound) -> RefinementFlow {
        // A ranked prefix whose remaining suffix was withheld is part of one
        // logical matcher round and does not consume the ordinary four-round
        // budget. The hard cap still bounds it.
        if round.withheld == 0 {
            self.charged_rounds += 1;
        }
        if !self.has_capacity() {
            RefinementFlow::Stop
        } else {
            RefinementFlow::Continue
        }
    }
}

impl Executor {
    /// Re-run E-matching with each fresh EUF model until fixpoint or a hard cap.
    pub(super) fn run_interleaved_ematching(
        &mut self,
        result: Result<SolveResult>,
        refinement_assertions: &Option<Vec<TermId>>,
        cegqi_ce_lemma_ids: &[TermId],
        has_uninstantiated_quantifiers: bool,
        ematching_added_instantiations: bool,
        reached_instantiation_limit: bool,
        ematching_rounds_completed: u64,
        ematching_instances_created: u64,
        category: LogicCategory,
    ) -> InterleavedEmatchingState {
        let mut state = InterleavedEmatchingState {
            result,
            reached_instantiation_limit,
            ematching_added_instantiations,
            unsat_from_interleaved: false,
            has_uninstantiated_quantifiers,
            ematching_rounds_completed,
            ematching_instances_created,
            had_preprocessing_instances: ematching_added_instantiations,
        };
        let original = match (refinement_assertions, &state.result) {
            (Some(original), Ok(SolveResult::Sat)) => original,
            _ => return state,
        };
        if !state.ematching_added_instantiations && !has_uninstantiated_quantifiers {
            return state;
        }

        self.set_active_solve_phase("quantifier-interleaved-ematching", "ematching");
        let should_stop = self.make_should_stop();
        let mut budget = InterleavedRoundBudget::new();
        while budget.has_capacity() {
            budget.begin_round();
            if should_stop() {
                state.reached_instantiation_limit = true;
                break;
            }
            let started_at = std::time::Instant::now();
            let round = self.try_ematching_refinement_round(original, cegqi_ce_lemma_ids);
            self.add_phase_seconds(
                "time.quantifier.ematching_seconds",
                started_at.elapsed().as_secs_f64(),
            );
            let Some(round) = round else {
                break;
            };
            state.record_round(&round);
            if round.added == 0 {
                break;
            }
            state.ematching_added_instantiations = true;
            if matches!(budget.finish_round(&round), RefinementFlow::Stop) {
                state.reached_instantiation_limit = true;
            }

            self.set_active_solve_phase(
                "quantifier-interleaved-resolve",
                format!("theory:{category:?}"),
            );
            let started_at = std::time::Instant::now();
            let ground_result = self.solve_for_category(category);
            self.add_phase_seconds(
                "time.quantifier.ground_resolve_seconds",
                started_at.elapsed().as_secs_f64(),
            );
            if matches!(
                state.record_ground_result(ground_result),
                RefinementFlow::Stop
            ) {
                break;
            }
        }
        state
    }
}
