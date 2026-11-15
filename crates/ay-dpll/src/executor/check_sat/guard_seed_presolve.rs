// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Seed presolve (#nra-guard-seed-instances).
//!
//! # The defect
//!
//! `guard_seed` asserts instances of an entailed real universal at the end
//! points of the interval guard on its binder. On the KeYmaera NRA family
//! those instances, with the ground part, are contradictory: the census
//! measured 103 gap files refuted in 0.03-2.5 s by that set. The primary
//! dispatch never sees it alone. It decides the instances together with
//! CEGQI's counterexample lemma `¬B[c̄]` (a hypothesis, not a consequence) and
//! every enumerative instance the triggerless universal received — on the
//! measured `magnetic_field` VC fifty full copies of the body. Before the NRA
//! check loop tried the linear relaxation first, the ground search stalled on
//! that vector for the whole budget (2M decisions, no refutation) although
//! each of its parts is refuted in 0.02 s; with it the vector is refuted
//! quickly, but the refutation rests on the counterexample hypothesis, the
//! disambiguation that follows declines, and the query still ends `unknown`
//! (measured, `--no-quantifier-guard-seeds`). The counterexample-free re-solve
//! (stage 4, `ce_free_resolve`) runs only after every other pass has answered
//! `unknown`, with no budget left.
//!
//! # The mechanism
//!
//! When the solve asserted seed instances, decide the SEED VECTOR first: the
//! quantifier-free members of the refinement snapshot, taken after
//! Skolemization and the seed pass and before E-matching or CEGQI add
//! anything — the authored ground part (in its Skolemized form), the diagonal
//! instances and the seed instances. It is decided on a disposable
//! proof-shedding probe (`ground_first_decide`, whose own `check_sat` runs the
//! whole ground pipeline, its pre-dispatch soundness passes included), under a
//! bounded share of the remaining budget. Every member is a consequence of the
//! (Skolemized, equisatisfiable) problem, so an UNSAT of the vector is an
//! UNSAT of the problem (monotonicity). SAT and an indecisive probe leave the
//! executor exactly as it was, and the primary dispatch runs as before.
//!
//! # Publication, in every posture
//!
//! The probe's refutation rests on quantifier instances, so it is a quantified
//! refutation, and those publish only with a translated authored-scope proof —
//! in `--z3-mode` too (DR-2 in the development design notes). It is adopted only once
//! such a certificate is INSTALLED, through the existing builder the artifact
//! firewall consults (the negated-existential ground-instantiation lane, which
//! proposes the seed values as witnesses first). That builder re-derives every
//! `qnt_neg_exists` / `forall_inst` step, re-solves the ground core on its own
//! proof-producing probe and installs the candidate only past the strict
//! installation boundary (authored-scope assumes, empty clause, complete
//! strict check). The adopted refutation is then classified with every CEGQI
//! flag off, as the stage-4 re-solve's is, and published through the
//! posture's ordinary admission. No certificate: the primary dispatch runs as
//! before, and the lane's per-query attempt counter is restored so the
//! firewall keeps its own attempt.

use std::time::Duration;

use ay_core::time::Instant;
use ay_core::TermId;

use super::ground_first::Decision;
use super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor::quantifier_loop::QuantifierProcessingResult;
use crate::executor_types::{Result, SolveResult};

/// The presolve may take at most this fraction (1/N) of the remaining budget.
const DECISION_SHARE: u32 = 5;
/// Cap on the presolve decision, context clone included.
const MAX_DECISION: Duration = Duration::from_secs(3);
/// Below this share of budget the presolve does not start.
const MIN_BUDGET: Duration = Duration::from_millis(50);

impl Executor {
    /// Decide the seed vector of a seeded solve before the primary dispatch
    /// (module docs). `Some` only with a refutation the caller adopts as the
    /// dispatch result; `None` leaves every output as it was.
    pub(super) fn try_guard_seed_presolve(
        &mut self,
        qr: &QuantifierProcessingResult,
    ) -> Option<Result<SolveResult>> {
        if qr.guard_seed_instances == 0
            || !crate::executor::quantifier_loop::guard_seed_instances_enabled()
            || !self.guard_seed_presolve_admissible()
            || self.should_abort_theory_loop()
        {
            return None;
        }
        let vector: Vec<TermId> = qr
            .refinement_assertions
            .as_deref()?
            .iter()
            .copied()
            .filter(|&member| !contains_quantifier(&self.ctx.terms, member))
            .collect();
        if vector.is_empty() {
            return None;
        }
        let budget = match self.current_solve_deadline() {
            Some(deadline) => (deadline.saturating_duration_since(Instant::now()) / DECISION_SHARE)
                .min(MAX_DECISION),
            None => MAX_DECISION,
        };
        if budget < MIN_BUDGET {
            return None;
        }
        let started = Instant::now();
        let decision = self.ground_first_decide(&vector, started + budget);
        let refuted = matches!(decision, Decision::Unsat);
        self.add_phase_seconds(
            "time.quantifier.guard_seed_presolve_seconds",
            started.elapsed().as_secs_f64(),
        );
        // Every posture, `--z3-mode` included (DR-2): a refutation that rests
        // on quantifier instances publishes only with its translated
        // authored-scope proof installed.
        let published = refuted && self.install_guard_seed_certificate();
        tracing::debug!(
            target: "ay::cert::guard_seed",
            "presolve: vector={} refuted={refuted} published={published} seconds={:.3}",
            vector.len(),
            started.elapsed().as_secs_f64()
        );
        self.last_statistics
            .set_int("quantifier.guard_seed.presolve_refuted", u64::from(refuted));
        self.last_statistics.set_int(
            "quantifier.guard_seed.presolve_published",
            u64::from(published),
        );
        if !published {
            return None;
        }
        self.last_unknown_reason = None;
        Some(Ok(SolveResult::unsat()))
    }

    /// The presolve applies to a plain decision, as the ground-first presolve
    /// does: no `check-sat-assuming` (its assumptions are merged into the
    /// vector, and a published refutation must name the failed ones), no
    /// unsat-core or unsat-assumption request (a refutation decided on a
    /// disposable probe has no core here), no objective or soft constraint,
    /// and not inside a nested validation probe.
    fn guard_seed_presolve_admissible(&self) -> bool {
        self.last_assumptions.is_none()
            && !self.in_alternation_validation
            && !self.in_nested_array_residue_probe
            && !self.produce_unsat_cores_enabled()
            && !matches!(
                self.ctx.get_option("produce-unsat-assumptions"),
                Some(ay_frontend::OptionValue::Bool(true))
            )
            && self.ctx.objectives().is_empty()
            && self.ctx.soft_constraints().is_empty()
    }

    /// Build and install an authored-scope certificate for a seed refutation
    /// through the firewall's own builder. An attempt the presolve spends is
    /// given back when nothing installed, so the firewall still has its own.
    fn install_guard_seed_certificate(&mut self) -> bool {
        let negated_exists_attempts = self.negated_exists_ground_inst_attempts.get();
        if self.try_translate_negated_exists_ground_instantiation_unsat() {
            return true;
        }
        self.negated_exists_ground_inst_attempts
            .set(negated_exists_attempts);
        false
    }
}
