// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model verification cascade for safety proofs.
//!
//! Tries multiple model-building strategies with budget-aware verification:
//! 1. Fast path (verify_model_fast, 800ms deadline)
//! 2. Filtered model
//! 3. Inductive-only model
//! 4. Entry-inductive model
//! 5. Iterative conjunct weakening

use super::*;

impl PdrSolver {
    /// Try multiple model-building and verification strategies with a total budget.
    ///
    /// Returns `Some(model)` if any strategy produces a verified model, `None` otherwise.
    /// Total cascade budget is 2 seconds; individual verify_model calls get 1.5s.
    ///
    /// TOTAL BUDGET (#3121): When running under a portfolio, the model verification
    /// cascade can consume multiple seconds per verify_model call × 5 strategies = 15+ sec.
    /// This starves the main PDR loop of time.
    ///
    /// The total does not count anchored concrete searches
    /// (`verification::concrete::ConcreteBudget`), as each verifier's own
    /// budget does not: each verifier run spends at most its allowance on them
    /// (200 ms in the fast path, 1 s in the others), and the strategies the
    /// cascade ran before the anchored window existed still run (2026-11-01).
    /// The solve deadline counts them, and stops them.
    pub(super) fn try_model_verification_cascade(
        &mut self,
        model: InvariantModel,
    ) -> Option<InvariantModel> {
        let clock = CascadeClock::start(self);
        let cascade_budget = std::time::Duration::from_secs(2);
        let verify_budget = std::time::Duration::from_millis(1500);

        // Strategy 1: Fast path with tight deadline
        let fast_deadline = clock.after(std::time::Duration::from_millis(800));
        if self.verify_model_fast(&model, fast_deadline) {
            if self.config.verbose {
                safe_eprintln!("PDR: check_invariants_prove_safety: model verified (fast path)");
            }
            return Some(model);
        }

        if self.cascade_out_of_budget(&clock, cascade_budget) {
            return None;
        }

        // Strategy 2: Filtered model
        let filtered = self.build_model_from_frame_filtered(1);
        if self.verify_model_with_budget(&filtered, verify_budget) {
            if self.config.verbose {
                safe_eprintln!("PDR: check_invariants_prove_safety: filtered model verified");
            }
            return Some(filtered);
        }

        if self.cascade_out_of_budget(&clock, cascade_budget) {
            return None;
        }

        // Strategy 3: Inductive-only model
        let inductive_model = self.build_model_from_inductive_lemmas(1);
        if self.verify_model_with_budget(&inductive_model, verify_budget) {
            if self.config.verbose {
                safe_eprintln!("PDR: check_invariants_prove_safety: inductive-only model verified");
            }
            return Some(inductive_model);
        }

        if self.cascade_out_of_budget(&clock, cascade_budget) {
            return None;
        }

        // Strategy 4: Entry-inductive model
        let entry_inductive_model = self.build_model_from_entry_inductive_lemmas(1);
        if self.verify_model_with_budget(&entry_inductive_model, verify_budget) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: entry-inductive model verified"
                );
            }
            return Some(entry_inductive_model);
        }

        if self.cascade_out_of_budget(&clock, cascade_budget) {
            return None;
        }

        // Strategy 5: Iterative conjunct weakening
        if let Some(weakened_model) = self.build_model_with_iterative_weakening(&inductive_model) {
            if self.config.verbose {
                safe_eprintln!(
                    "PDR: check_invariants_prove_safety: iteratively weakened model verified"
                );
            }
            return Some(weakened_model);
        }

        if self.config.verbose {
            safe_eprintln!(
                "PDR: check_invariants_prove_safety: model verification failed, cannot prove safety"
            );
        }
        None
    }

    /// True once the cascade's [`CascadeClock`] has reached `budget`: the
    /// cascade tries no further strategy.
    fn cascade_out_of_budget(&self, clock: &CascadeClock, budget: std::time::Duration) -> bool {
        let elapsed = clock.elapsed(self);
        if elapsed < budget {
            return false;
        }
        if self.config.verbose {
            safe_eprintln!(
                "PDR: check_invariants_prove_safety: cascade budget exhausted ({:?}), skipping remaining models",
                elapsed
            );
        }
        true
    }
}

use clock::CascadeClock;

mod clock {
    use crate::pdr::PdrSolver;
    use ay_core::time::Instant;
    use std::time::Duration;

    /// The model verification cascade's clock: the time since it started,
    /// less the anchored concrete searches its verifier runs recorded since
    /// then (`PdrTelemetry::concrete_anchored_search`). It is the only clock
    /// the cascade reads, and its start is private to this module, so no
    /// step of the cascade can count anchored time against the total without
    /// changing the clock itself (review of b645a840fe, finding B: four
    /// separate reads of the raw time each had to leave it out by hand, and
    /// a test of the helper they called could not tell whether they did).
    pub(super) struct CascadeClock {
        start: Instant,
        anchored_at_start: Duration,
    }

    impl CascadeClock {
        /// The clock of a cascade `solver` starts now.
        pub(super) fn start(solver: &PdrSolver) -> Self {
            Self {
                start: Instant::now(),
                anchored_at_start: solver.telemetry.concrete_anchored_search,
            }
        }

        /// A clock that started at `start`, with `solver`'s anchored time
        /// now as its anchored time at start.
        #[cfg(test)]
        pub(super) fn started_at(solver: &PdrSolver, start: Instant) -> Self {
            Self {
                start,
                anchored_at_start: solver.telemetry.concrete_anchored_search,
            }
        }

        /// The instant `offset` after the cascade started (the fast path's
        /// deadline, which `verify_model_fast` itself moves past its
        /// anchored searches).
        pub(super) fn after(&self, offset: Duration) -> Instant {
            self.start + offset
        }

        /// The cascade's time so far, less the anchored searches `solver`'s
        /// verifier runs recorded since it started.
        pub(super) fn elapsed(&self, solver: &PdrSolver) -> Duration {
            let anchored = solver
                .telemetry
                .concrete_anchored_search
                .saturating_sub(self.anchored_at_start);
            self.start.elapsed().saturating_sub(anchored)
        }
    }
}

#[cfg(test)]
#[allow(clippy::unwrap_used)]
mod tests {
    use super::CascadeClock;
    use crate::pdr::{InvariantModel, PdrConfig, PdrSolver, PredicateInterpretation};
    use crate::{ChcExpr, ChcProblem, ChcSort, ChcVar, ClauseBody, ClauseHead, HornClause};
    use std::time::Duration;

    /// The cascade's 2 s total leaves out the anchored concrete searches its
    /// verifier runs recorded since it started, as each verifier's own budget
    /// does (2026-11-01); time before the cascade started is not subtracted.
    #[test]
    fn the_cascade_total_leaves_out_anchored_concrete_searches() {
        let mut solver = PdrSolver::new(ChcProblem::new(), PdrConfig::default());
        solver.telemetry.add_anchored_search(Duration::from_secs(5));
        let start = ay_core::time::Instant::now()
            .checked_sub(Duration::from_secs(3))
            .unwrap();
        let clock = CascadeClock::started_at(&solver, start);
        assert!(clock.elapsed(&solver) >= Duration::from_secs(3));
        solver.telemetry.add_anchored_search(Duration::from_secs(2));
        let elapsed = clock.elapsed(&solver);
        assert!(
            elapsed >= Duration::from_secs(1) && elapsed < Duration::from_secs(2),
            "3 s less 2 s of anchored search: {elapsed:?}"
        );
        assert!(!solver.cascade_out_of_budget(&clock, Duration::from_secs(2)));
        assert!(solver.cascade_out_of_budget(&clock, Duration::from_secs(1)));
    }

    fn var(name: &str) -> ChcExpr {
        ChcExpr::var(ChcVar::new(name, ChcSort::Int))
    }

    /// `A >= lo /\ B >= lo /\ pad conjuncts /\ A + B <= 2 lo - 1` (no model),
    /// as `concrete/budget_tests.rs` builds it: beyond ±100 its check is an
    /// anchored search whose cost grows with `pad`.
    fn costly_unsat_body(lo: i64, pad: i64) -> ChcExpr {
        let mut conjuncts = vec![
            ChcExpr::ge(var("A"), ChcExpr::int(lo)),
            ChcExpr::ge(var("B"), ChcExpr::int(lo)),
        ];
        for i in 1..=pad {
            conjuncts.push(ChcExpr::ge(
                ChcExpr::add(var("A"), ChcExpr::mul(ChcExpr::int(i), var("B"))),
                ChcExpr::int(i64::MIN / 4),
            ));
        }
        conjuncts.push(ChcExpr::le(
            ChcExpr::add(var("A"), var("B")),
            ChcExpr::int(2 * lo - 1),
        ));
        ChcExpr::and_all(conjuncts)
    }

    /// Review of b645a840fe, finding B: the whole cascade, not only its clock.
    /// The fact `inv(A, B) <- A = 6 /\ B = 3` makes `inv` reachable (so no
    /// strategy builds the valid `false`) and the query `A = 6 /\ B = 3`
    /// unsafe, so every model fails, and `inv := true` (what every strategy
    /// builds with no lemmas) fails at that query, after its verifier run has
    /// spent its whole anchored
    /// allowance on the four costly anchored clauses before it (1 s in each of
    /// strategies 2 to 4, with real SMT; the fast path's 200 ms is not
    /// counted on, since a slow SMT answer can end it first). Read raw, the
    /// cascade's time passes its 2 s after strategy 3 and strategy 4 never
    /// runs (at most 2.2 s of anchored search); with the anchored time left
    /// out every strategy runs, and strategies 2 to 4 alone spend 3 s.
    #[test]
    fn every_cascade_strategy_runs_past_the_anchored_searches() {
        let mut problem = ChcProblem::new();
        let inv = problem.declare_predicate("inv", vec![ChcSort::Int, ChcSort::Int]);
        let mut bodies: Vec<ChcExpr> = (0..4).map(|i| costly_unsat_body(1000 + i, 1000)).collect();
        bodies.push(ChcExpr::and_all(vec![
            ChcExpr::eq(var("A"), ChcExpr::int(6)),
            ChcExpr::eq(var("B"), ChcExpr::int(3)),
        ]));
        for body in bodies {
            problem.add_clause(HornClause::new(
                ClauseBody::new(vec![(inv, vec![var("A"), var("B")])], Some(body)),
                ClauseHead::False,
            ));
        }
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::and_all(vec![
                ChcExpr::eq(var("A"), ChcExpr::int(6)),
                ChcExpr::eq(var("B"), ChcExpr::int(3)),
            ])),
            ClauseHead::Predicate(inv, vec![var("A"), var("B")]),
        ));
        let mut model = InvariantModel::new();
        model.set(
            inv,
            PredicateInterpretation::new(
                vec![
                    ChcVar::new("A", ChcSort::Int),
                    ChcVar::new("B", ChcSort::Int),
                ],
                ChcExpr::Bool(true),
            ),
        );
        let config = PdrConfig {
            verbose: false,
            ..PdrConfig::default()
        };
        let mut solver = PdrSolver::new(problem, config);
        assert!(solver.try_model_verification_cascade(model).is_none());
        let anchored = solver.telemetry.concrete_anchored_search;
        assert!(
            anchored >= Duration::from_secs(3),
            "strategies 2 to 4 each spent their 1 s allowance: {anchored:?}"
        );
    }
}
