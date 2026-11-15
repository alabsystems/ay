// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The counted limits of the whole-problem re-decisions that
//! `Executor::reconfirm_unsat_within` runs: step (4a)'s entailment question
//! and the closed-sentence certificates' refutations, and why step (4)'s
//! re-solve has none (#r30-reconfirm-slices-counted).
//!
//! # Why they needed their own counts
//!
//! A conflict allowance bounds each SAT solve of a nested check, not how many
//! solves its DPLL(T) split loop runs (see the parent module). These
//! re-decisions had the conflict allowance and the backstop and nothing else,
//! so a re-decision of cheap rounds ran until it answered or the backstop
//! stopped it. Measured (debug, `086779f02`): the closed-sentence refutation
//! of `qsat_route_lost_verdicts::qsat_div_mod_of_an_ite_is_played` ran 1528 to
//! 2392 round trips until the test's 10 s deadline, and the one of
//! `deep_qe_prepass_is_entered_on_the_unknown_fallback_lane` ran 812 to 1403
//! round trips, 18 to 23 s each, to an incomplete `unknown`. Both print the
//! `RECONFIRM(4)` probe label, which is how they were first read as step (4).
//!
//! Step (4a) had only a WALL-CLOCK slice: as long as the first solve took,
//! read from `Statistics::time_seconds`. That reading includes the first
//! solve's proof assembly, which on the R30 divider shapes is most of it
//! (`fac28`: a 24.4 s slice for a question that needs 1.9 s; `f6_padb`:
//! 89.4 s), so the question's search could run for many first solves. It now
//! runs on counts, its own proof assembly included
//! (#r30-4a-nested-assembly-count); its one clock left is a cap of half of
//! what remains of the certification envelope, when there is one, so that
//! step (4) keeps the other half (`unsat_cert/trust_clause_entailment.rs`).
//!
//! # The counts
//!
//! * Step (4a)'s question: [`ENTAILMENT_FACTOR`] times the first solve's
//!   split-loop round trips (at least [`ENTAILMENT_ROUND_TRIP_FLOOR`]) and
//!   [`ENTAILMENT_FACTOR`] times its conflicts per SAT solve (at least
//!   [`ENTAILMENT_CONFLICT_FLOOR`], never more than step (4)'s allowance). A
//!   question that runs out declines, and step (4) runs after it as before.
//!   The yardstick is the first solve's check ledger (`all_lanes.round_trips`,
//!   `all_lanes.conflicts`: every lane and probe of the check, GT5), read
//!   when the certification's envelope is built ([`FirstSolveWork::of`]). It
//!   is a count, not a duration, so no proof assembly inflates it; it is not
//!   quite the same on every host, because the ledger also counts lanes that
//!   a deadline share cut (the `certification_determinism` fixture's first
//!   solve: 136 to 140 round trips between an idle and a slowed host).
//! * Step (4a)'s question's proof assembly: [`ENTAILMENT_FACTOR`] times the
//!   first solve's assembly observations (`proof_assembly.observations`,
//!   `executor/proof/assembly_observations.rs`), at least
//!   [`ENTAILMENT_ASSEMBLY_FLOOR`]. Its search can be done with no round
//!   trip and no conflict and its assembly still run for seconds
//!   (`finstore_7373_0110`), where only the slice (as long as the first solve
//!   took) bounded it, so whether the question accepted depended on the
//!   host's speed. A spent allowance is a plain decline
//!   (`unsat_cert/redecision_counts.rs`).
//! * A closed-sentence refutation: [`CLOSED_SENTENCE_REFUTATION_ROUND_TRIPS`].
//!   It runs inside a search, which has no finished first solve to measure.
//! * Step (4)'s re-solve: no round-trip count. It re-decides the whole
//!   problem in a fresh layout without the first solve's strengthenings, so
//!   its rounds are not proportional to the first solve's, and it is the
//!   funnel's last accepting step: a count that cuts it turns a correct
//!   `unsat` into `unknown`. Measured (release, generated QF_ALIA shaped like
//!   the `sem2_arithidx` family, all `unsat` for z3): accepted re-solves ran
//!   1236 round trips against the first solve's 50 (24.7 times), 537 against
//!   90 and 513 against 115, and a grant of the larger of 512 and four first
//!   solves published `unknown` for all three where `ay` publishes `unsat`
//!   (`discharged-trust`) in 8 to 21 s. The adversarial corpus's
//!   `arithidx_7373_0096` accepts at 49 against 11 (4.45 times). Its rounds
//!   stay bounded by its conflict and decision allowances per SAT solve and
//!   the backstop, as before.
//!
//! A spent count ends the nested check `Unknown` from
//! `DeterministicResourceBudget` (round trips) or its conflict allowance, a
//! plain decline (`latch_nested`), never a stop.
//!
//! # Calibration (`086779f02`, counts only)
//!
//! The first-solve conflicts below were read while ay-sat reported a solve's
//! conflicts at its restarts only. The yardstick now also counts the
//! conflicts each solve makes after its last restart, or without one
//! (`ay-sat`'s `solver/work_report.rs`), which widens step (4a)'s conflict
//! allowance: measured on R30 `r1_sdiv_sdiv32` 13,837 -> 29,611 and
//! `r3_sdiv16_or1` 3,116 -> 4,220, with the same verdicts.
//!
//! Every re-decision of the ay-dpll lib tests that reach the funnel, of
//! `group_proofs`, `group_quantifiers`, `group_regression`, `group_auflia`,
//! `group_lia`, `group_bv`, `group_arrays`, `group_theory_misc`, the
//! `deductive_checks_*` targets and `certification_determinism` (debug), and of the
//! R30 calibration corpus (154 cases) and 150 generated
//! `sem2_arithidx`-shaped files (release):
//!
//! * accepted closed-sentence refutations: at most 6 round trips;
//! * accepted step (4a) questions: at most 491 round trips (deductive-checks set-fold,
//!   first solve 2600), at most 0.53 of the first solve's
//!   (`certification_determinism`: 70 of 133), and at most 29 where that is
//!   more than the first solve's (first solve 2); at most 224 412 conflicts,
//!   at most 0.86 of the first solve's (`four_dividers`: 90 335 of 105 195),
//!   and at most 2855 where that is more (first solve 2757). Every accepted
//!   question stays at least 2.2 times below both of its counts.
//!
//! # Calibration of the assembly allowance (`fd4e00f75`, release)
//!
//! Every step (4a) question of the R30 corpus (154 cases) and of the
//! adversarial review's generated corpus with `uart-7`/`uart-8` (206 cases),
//! with the allowance lifted: 165 accepted questions. The R30 ones made at
//! most 133 observations. Of the others, the most an accepted question made
//! beyond twice its first solve's was 3918 (`finstore_7373_0038`, first
//! solve 472), and only `finstore_7373_0110` made more than its allowance
//! (7999 against 2139): its question took 4.5 s, nearly all of it in its own
//! assembly, where step (4) re-decides the problem in 0.5 s, and the wall
//! slice had declined it too. The counts were the same on an X925 and an
//! A725 core.

use crate::Executor;

/// The split-loop round trips a closed-sentence refutation may run: the
/// guard's and the lanes' grant size, about 85 times the most an accepted
/// refutation of the corpus ran (6).
pub(crate) const CLOSED_SENTENCE_REFUTATION_ROUND_TRIPS: u64 = 512;

/// Step (4a)'s question may run this many times the first solve's round trips
/// and spend this many times its conflicts per SAT solve (corpus: at most 0.53
/// and 0.86 of one).
const ENTAILMENT_FACTOR: u64 = 2;

/// The split-loop round trips step (4a)'s question may always run: more than
/// twice those of any accepted question whose first solve ran fewer (29).
const ENTAILMENT_ROUND_TRIP_FLOOR: u64 = 64;

/// The conflicts per SAT solve step (4a)'s question may always spend: more
/// than any accepted question whose first solve spent fewer (at most 2855).
const ENTAILMENT_CONFLICT_FLOOR: u64 = 10_000;

/// The proof-assembly observations step (4a)'s question may always make
/// (`executor/proof/assembly_observations.rs`): more than any accepted
/// question made beyond twice its first solve's (at most 3918, against 472).
/// The margin is thin, but it need not absorb host variance: the corpus's
/// counts were the same on an X925 and an A725 core (an assembly that runs
/// a consequence-replay probe sizes that probe in wall time,
/// `executor/proof/consequence_replay_budget.rs`, so its work after one can
/// still vary). A later assembly that polls more can only move such a
/// question to step (4), never change a verdict. A larger floor would run
/// `finstore_7373_0110`'s question (7999, against 2139) further before it
/// declines: about 1.5 s more at 6144.
const ENTAILMENT_ASSEMBLY_FLOOR: u64 = 4_096;

/// The first solve's counted work, the yardstick of step (4a)'s counts.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub(crate) struct FirstSolveWork {
    /// Split-loop round trips of the first solve's check.
    pub(crate) round_trips: u64,
    /// CDCL conflicts of the first solve's check.
    pub(crate) conflicts: u64,
    /// Proof-assembly observations of the first solve's check, on its thread.
    pub(crate) assembly_observations: u64,
}

impl FirstSolveWork {
    /// The work of `outer`'s last check-sat, from its check's ledger (zero
    /// when it recorded none: the floors apply).
    pub(crate) fn of(outer: &Executor) -> Self {
        let statistics = outer.statistics();
        Self {
            round_trips: statistics.get_int("all_lanes.round_trips").unwrap_or(0),
            conflicts: statistics.get_int("all_lanes.conflicts").unwrap_or(0),
            assembly_observations: statistics
                .get_int("proof_assembly.observations")
                .unwrap_or(0),
        }
    }

    /// Step (4a)'s round-trip count.
    pub(crate) fn entailment_round_trips(self) -> u64 {
        relative(self.round_trips, ENTAILMENT_ROUND_TRIP_FLOOR)
    }

    /// Step (4a)'s conflicts per SAT solve, before the allowance caps them.
    pub(crate) fn entailment_conflicts(self) -> u64 {
        relative(self.conflicts, ENTAILMENT_CONFLICT_FLOOR)
    }

    /// Step (4a)'s allowance of proof-assembly observations.
    pub(crate) fn entailment_assembly_observations(self) -> u64 {
        relative(self.assembly_observations, ENTAILMENT_ASSEMBLY_FLOOR)
    }
}

/// [`ENTAILMENT_FACTOR`] times `first`, at least `floor`.
fn relative(first: u64, floor: u64) -> u64 {
    first.saturating_mul(ENTAILMENT_FACTOR).max(floor)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn step_4as_counts_are_sized_from_the_first_solve_with_their_floors() {
        let none = FirstSolveWork::default();
        assert_eq!(none.entailment_round_trips(), ENTAILMENT_ROUND_TRIP_FLOOR);
        assert_eq!(none.entailment_conflicts(), ENTAILMENT_CONFLICT_FLOOR);
        assert_eq!(
            none.entailment_assembly_observations(),
            ENTAILMENT_ASSEMBLY_FLOOR
        );

        let large = FirstSolveWork {
            round_trips: 2_600,
            conflicts: 105_195,
            assembly_observations: 50_000,
        };
        assert_eq!(large.entailment_round_trips(), 2 * 2_600);
        assert_eq!(large.entailment_conflicts(), 2 * 105_195);
        assert_eq!(large.entailment_assembly_observations(), 2 * 50_000);

        let saturated = FirstSolveWork {
            round_trips: u64::MAX,
            conflicts: u64::MAX,
            assembly_observations: u64::MAX,
        };
        assert_eq!(saturated.entailment_round_trips(), u64::MAX);
        assert_eq!(saturated.entailment_conflicts(), u64::MAX);
        assert_eq!(saturated.entailment_assembly_observations(), u64::MAX);
    }

    #[test]
    fn the_first_solve_is_its_checks_ledger() {
        let mut exec = Executor::new();
        assert_eq!(FirstSolveWork::of(&exec), FirstSolveWork::default());
        let script = "(set-logic QF_LIA)
             (declare-const x Int)
             (declare-const y Int)
             (assert (< x y))
             (assert (< y x))
             (check-sat)";
        exec.execute_all(&ay_frontend::parse(script).expect("parse"))
            .expect("execute");
        let statistics = exec.statistics();
        assert_eq!(
            FirstSolveWork::of(&exec),
            FirstSolveWork {
                round_trips: statistics
                    .get_int("all_lanes.round_trips")
                    .expect("a check records its ledger"),
                conflicts: statistics
                    .get_int("all_lanes.conflicts")
                    .expect("a check records its ledger"),
                assembly_observations: statistics
                    .get_int("proof_assembly.observations")
                    .expect("a check records its assembly observations"),
            }
        );
    }

    /// The first solve's assembly observations are a count of the query: an
    /// UNSAT check that assembles a proof records some, and the same query on
    /// a fresh executor records exactly as many (#r30-4a-nested-assembly-count).
    #[test]
    fn the_first_solves_assembly_observations_are_a_count_of_the_query() {
        let observed = || {
            let mut exec = Executor::new();
            let script = "(set-logic QF_LRA)
                 (set-option :produce-proofs true)
                 (declare-const x Real)
                 (declare-const y Real)
                 (assert (< x y))
                 (assert (< y x))
                 (check-sat)";
            exec.execute_all(&ay_frontend::parse(script).expect("parse"))
                .expect("execute");
            FirstSolveWork::of(&exec).assembly_observations
        };
        let first = observed();
        assert!(
            first > 0,
            "the UNSAT check assembled a proof and polled its stop"
        );
        assert_eq!(observed(), first, "the same query records the same count");
    }
}
