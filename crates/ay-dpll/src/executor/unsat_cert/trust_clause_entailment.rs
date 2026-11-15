// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Step (4a) of the deferred-trust discharge: before step (4) re-decides the
//! whole authored obligation, ask a fresh `Executor` the narrower question the
//! deferred clauses pose: does the authored obligation entail every one of
//! them? (#reconfirm4-cost)
//!
//! # The cost
//!
//! Step (4) re-solves the authored obligation from scratch, so by construction
//! it costs about what the first solve cost. On deductive-checks's captured set-fold
//! obligation (`deductive_checks_set_fold_posture`, release, measured at e157e4851)
//! the first solve took 17-21 s, the re-solve 15-16.5 s more, and the query
//! published `Unknown(Timeout)` at the embedder's 30 s deadline (with this arm:
//! 18.1-20.1 s). Both solves spend most of that time in the BV-LIA bridge's
//! support relaxation, a lazy search whose length depends on term layout; the
//! re-solve's compacted arena is just another layout (24 s in one measured
//! layout).
//!
//! The proof being corroborated has 19 steps. Step (2) strictly validates all
//! of them except three `trust` units such as
//! `(= (select ordering_9 #x0) (select state_12 #x1))` and one `Generic`
//! tautology. Asked whether the authored obligation entails those four
//! clauses, a fresh executor answers `unsat` in 1.3-2.4 s over the measured
//! layouts, at its second ground bridge call, before any quantifier
//! instantiation.
//!
//! # The question, and why `unsat` certifies the verdict step (4) certifies
//!
//! Step (2) has already strictly validated every step except the collected
//! clauses `C1..Cn`, with every `assume` inside `problem`. This arm asks a
//! fresh executor `P ∧ (¬C1 ∨ … ∨ ¬Cn)`, where `P ⊆ problem` is the
//! corroboration scope step (4) re-solves. It accepts on `unsat`, under step
//! (4)'s conflict/decision allowances and structural proof screen
//! ([`Executor::reconfirm_unsat_within`]).
//!
//! `unsat` there means `P ⊨ Ci` for every `i`. Suppose the problem had a model
//! `M`. Then `M ⊨ P`, so `M` satisfies every `Ci`. Every validated leaf (an
//! `assume` from `problem`, a checked tautology, a provenance-checked fresh
//! definition, a validated skolem) holds in `M`, or in its extension to the
//! fresh symbols, which `P` never mentions. The validated inferences preserve
//! truth, so `M` would satisfy the empty clause: a contradiction. This is the
//! soundness argument of step (3)'s entailment lane
//! (`discharge_trust_clause_impl`), asked of all clauses at once and accepted
//! on step (4)'s evidence class.
//!
//! # What this is evidence of, and what it is not
//!
//! A RE-DECISION, not a derivation, exactly like step (4). The fresh executor
//! is the same engine, and its proof of the question is screened the way step
//! (4)'s is, which accepts a trust-kind rejection. On the captured obligation
//! that nested proof itself concludes the first deferred clause with a `trust`
//! step, so this arm reproduces the claim; it does not check it. The record
//! (`CorroborationMethod::Entailment`) says which question was
//! re-decided and does not call it independent.
//!
//! Nothing from the first solve is reused except the TEXT of the deferred
//! clauses, as the question: no model, lemma, learnt clause or solver state
//! crosses over; the executor is [`Executor::new_derived_query_executor`]'s
//! fresh copy, as in step (4). If the first solve's claim is false, some `Ci`
//! is false in a model of `P`, so `P ∧ ¬Ci` is satisfiable and the fresh
//! executor can answer `unsat` only if it is itself unsound on that query, the
//! residual exposure step (4) already carries. A clause naming a symbol `P`
//! does not constrain (a skolem, a fresh definition, a bridge slack) only
//! makes `¬Ci` easier to satisfy, so it can only make this arm decline.
//!
//! # The scope, and the clauses left to step (4)
//!
//! The question is asked over step (4)'s own scope, quantified roots
//! included. Dropping them would be equally sound (`G ⊆ P` and `G ⊨ Ci` give
//! `P ⊨ Ci`), but the engine routes a quantifier-free query differently: on
//! the captured obligation the question over its 38 quantifier-free roots took
//! 3.3-7.8 s against 1.3-2.4 s, and 7.8 s in a layout whose first solve was
//! 8.3 s.
//!
//! A clause that mentions a constant which some quantified root mentions and
//! no quantifier-free root does is, in practice, a quantifier INSTANCE: only
//! instantiation can entail it, so the fresh executor would re-run the
//! instantiation that produced it (the self-corroboration
//! `#qsu-downgrade-is-load-bearing` describes) at the price of a full
//! quantified attempt. Measured on `hunt_quantifier_fixup_verdicts`' `d11`,
//! whose proof defers 19 such instances: `Unknown(QuantifierUnhandled)` after
//! 1.8 s and three e-matching rounds, before step (4) ran at all. Such proofs
//! go to step (4) without a solve. A constant no root mentions (a fresh
//! symbol) does not exclude a clause: `P` says nothing about it.
//!
//! # Its bound
//!
//! The question is not step (4)'s, and a different question can be far harder
//! than the one it replaces. Measured on generated QF_ALIA (`storeeq` family),
//! which the base answers `unsat` in 1.2 s through step (4): this arm's
//! question over eleven negated store-chain equalities ran for 98 s, until the
//! process was killed, inside the array solver's cross-chain equality
//! propagation, and under a 60 s timeout it spent 57.9 s and left step (4)
//! nothing, so a correct `unsat` published `unknown`. Step (4)'s deterministic
//! allowances do not bound it: 1,642 conflicts and 205,286 decisions in 27.9 s,
//! against allowances of 400,000 and 24,000,000. On a generated datatype,
//! array and bit-vector file whose proof defers 2,964 clauses, the question
//! took 13.7 s against 0.6-0.8 s for step (4), on a path that charges no
//! split-loop round trip at all, so a counted work grant
//! (`ay_core::resource::enter_work_grant`) would not end it either. The only
//! stop such loops honour is the check's interrupt and deadline
//! (`ay_core::resource::check_stop_requested`).
//!
//! So the arm runs on COUNTS sized from the first solve's own counted work
//! (`api/proofs/certification_effort/redecision.rs`): twice its split-loop
//! round trips, twice its conflicts per SAT solve and twice its proof
//! assembly's observations, each with a floor, never more conflicts than the
//! allowance. A spent count is a plain decline, at a point fixed by the
//! query's counts, not by a clock. The counts are a liveness bound, not an
//! accepting boundary: acceptance still needs `unsat` under step (4)'s
//! screen, and a spent count can only make this arm DECLINE, after which step
//! (4) runs exactly as before. They bound the question by the first solve's
//! counted work instead of its duration, which includes its proof assembly
//! (#r30-reconfirm-slices-counted: `fac28`'s 24.4 s slice for a question that
//! needs 1.9 s). They do not tighten the R30 divider shapes: there the
//! question runs no round trip, and the first solve's ledger counts its proof
//! assembly's SAT work too (`f6_padb`: 839 138 conflicts for a 134-conflict
//! search), so the conflict count sits at the allowance.
//!
//! The question's own proof assembly is counted too
//! (#r30-4a-nested-assembly-count): every poll of the assembly owner's stop,
//! the printer's complete bit-blast callback included, and every Farkas
//! reconstruction attempt is one observation
//! (`executor/proof/assembly_observations.rs`). On `finstore_7373_0110` the
//! question re-solves `unsat` with no conflict and no round trip and then
//! spends seconds in its own proof assembly (about 8000 observations against
//! the first solve's 2139); the allowance ends it at the same observation on
//! an X925 and an A725 core, and step (4) re-decides the problem.
//!
//! The arm's one clock is a CAP: when the certification has an envelope, the
//! question stops at half of what remains of it when the question starts
//! ([`entailment_deadline`]), so step (4) always keeps the other half.
//! Measured (release, pinned): on `storeeq_7373_0236` at `--timeout 4000`
//! the question starts with 1.3 s of the envelope left and would run its
//! whole round-trip count (188 rounds, 1.2 to 1.5 s, against the first
//! solve's 94 in about 75 ms); the cap ends it after 0.64 s and step (4)
//! publishes `unsat` with the rest. Without the cap `storeeq_7373_0236` at
//! `--timeout 3000`/`4000` and `aufl_7373_00096` at `--timeout 2000`/`2500`
//! published `unknown` where the cap and the former slice both publish
//! `unsat`. With no envelope (the CLI without `--timeout`, an embedder
//! without a deadline) there is no cap, and the question is bounded by its
//! counts alone.
//!
//! The cap never masquerades as evidence: a question it ended is recorded in
//! the certification's envelope as a lane-local clock
//! (`TrustClauseDischargeControls::note_lane_clock`). Step (4) still runs, and
//! if it accepts the verdict is published; if the funnel then DECLINES, the
//! decline is reported as the clock stop it may have been (`Backstop`), never
//! as a rejection, because on a faster host this arm might have accepted.
//!
//! It halves TIME, and that is the rule until S6: DR-38 rule 7 has the
//! half-budget slicers give their lane half of the node's remaining TICKS and
//! leave the deadline whole, but it binds under a tick budget, and no check
//! has one before S6 (`api/proofs/certification_effort.rs`, `certify_node`);
//! without one the fast mode runs (KL8). At S6 the cap becomes half of the
//! certification's remaining ticks.
//!
//! The cap replaces a SLICE that was also no longer than the first solve
//! took (and at least 250 ms), with or without an envelope. That clock
//! decided what no count did: it cut the QF_LRA `uart-7`/`uart-8` and
//! `finstore_7373_0046` questions mid-search, so their corroboration flipped
//! between `entailment` and `resolve` from run to run, and it ended
//! `finstore_7373_0110`'s uncounted proof assembly wherever the host's speed
//! put it.
//!
//! # Eligibility (anything else falls through to step (4), unchanged)
//!
//! * A completed bounded pure-integer unit scope goes directly to step (4).
//!   Its exact-refinement-first search does not need the extra Boolean question.
//!   This is a routing choice, not a claim that all polynomial units are cheap;
//!   incomplete, Boolean and non-integer scopes retain the existing question.
//! * At least one deferred clause, and none empty. An empty list makes the
//!   question `P ∧ false`, which is vacuously `unsat`. An empty clause is the
//!   terminal claim itself: its negation is `true`.
//! * The question must not fold to a constant. `true` (a clause spelled
//!   `[false]`, or two complementary unit clauses) makes it the whole problem,
//!   which is step (4)'s question; `false` (every clause a syntactic
//!   tautology) would accept on the term builder's folding alone, with nothing
//!   re-decided.
//! * Every clause quantifier-free. In other layouts the same obligation's
//!   proof defers a 371-literal `Generic` lemma that negates the whole
//!   instantiated window, quantified roots included; that trust step is the
//!   whole refutation and there is no narrower question to ask.
//! * No clause constant known only to the quantified roots (above).
//! * No subproof anchor in the proof. A clause concluded inside an anchor may
//!   mention the anchor's bound variables. Read globally, a bound name that
//!   collides with an authored constant would ask a different question from
//!   the one the subproof needs.

use std::time::Duration;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::term::TermData;
use ay_core::time::Instant;
use ay_core::{ProofId, ProofStep, TermId, TermStore};

use super::{
    probe_cert_reject, Executor, FreshReconfirmationLimits, ReconfirmationReading,
    WHOLE_PROBLEM_RECONFIRMATION_LIMITS,
};
use crate::api::proofs::TrustClauseDischargeControls;
use crate::ematching::contains_quantifier;

/// Step (4a)'s question for [`Executor::reconfirm_unsat_within`]: assert
/// `¬C1 ∨ … ∨ ¬Cn` over `clauses` beside the scope, and stop at `deadline`.
pub(super) struct EntailmentQuestion<'a> {
    clauses: &'a [Vec<TermId>],
    deadline: Option<Instant>,
}

impl EntailmentQuestion<'_> {
    /// Where the question's re-decision stops: its cap
    /// ([`entailment_deadline`]), never later than the certification's
    /// `backstop`; `None` with neither.
    pub(super) fn deadline_within(&self, backstop: Option<Instant>) -> Option<Instant> {
        match (self.deadline, backstop) {
            (Some(cap), Some(backstop)) => Some(cap.min(backstop)),
            (cap, backstop) => cap.or(backstop),
        }
    }

    /// The extra root, built in `terms` (the fresh executor's own arena), or
    /// `None` for a question step (4a) must not ask.
    pub(super) fn refuted_cases(&self, terms: &mut TermStore) -> Option<TermId> {
        negated_clause_disjunction(terms, self.clauses)
    }
}

impl Executor {
    /// Step (4a): `true` when a fresh executor re-decides that
    /// `corroboration_scope` entails every clause in `deferred` (the clauses
    /// step (2)'s collecting checker could not validate). `false` when the
    /// proof is not eligible, the re-decision declines, or one of its counts
    /// or its cap runs out; step (4)'s whole-problem re-solve then runs
    /// exactly as before.
    ///
    /// On its own, `true` says nothing about whether the scope is
    /// satisfiable: it is evidence for the verdict only after step (2) has
    /// validated every other step of the proof.
    pub(super) fn reconfirms_deferred_clause_entailment(
        &self,
        corroboration_scope: &[TermId],
        deferred: &[(ProofId, Vec<TermId>)],
        controls: &TrustClauseDischargeControls,
    ) -> bool {
        // Adding the Boolean refuted-cases question can turn a unit arithmetic
        // problem into whole-formula SAT search. Re-decide that exact unit
        // problem in the unchanged step (4) instead. This is only routing: the
        // fresh UNSAT result, structural proof screen and controls still decide.
        if ay_nia::is_integer_unit_conjunction(&self.ctx.terms, corroboration_scope) {
            probe_cert_reject(|| {
                "RECONFIRM(4a) LEFT TO (4): completed integer-unit scope".to_string()
            });
            return false;
        }
        let Some(clauses) = self.entailment_eligible_clauses(corroboration_scope, deferred) else {
            probe_cert_reject(|| {
                format!(
                    "RECONFIRM(4a) NOT ELIGIBLE: {} deferred clauses (needs at least one, none \
                     empty or quantified, no constant only a quantified root mentions, and no \
                     subproof anchor)",
                    deferred.len()
                )
            });
            return false;
        };
        let now = Instant::now();
        let first_solve = Duration::try_from_secs_f64(self.last_statistics.time_seconds)
            .unwrap_or(Duration::ZERO);
        let deadline = entailment_deadline(now, controls.backstop);
        let question = EntailmentQuestion {
            clauses: &clauses,
            deadline,
        };
        let limits = entailment_limits(controls);
        let accepted = self
            .reconfirm_unsat_within(
                corroboration_scope,
                Some(&question),
                limits,
                controls,
                false,
                ReconfirmationReading::EitherClass,
            )
            .is_some();
        probe_cert_reject(|| {
            format!(
                "RECONFIRM(4a): the {}-root authored scope {} all {} deferred clauses \
                 (counts {} round trips, {} conflicts per solve, {} assembly observations; \
                 cap {}, first solve {} ms, took {} ms)",
                corroboration_scope.len(),
                if accepted {
                    "re-decided as entailing"
                } else {
                    "was not re-decided as entailing"
                },
                clauses.len(),
                limits.max_round_trips.unwrap_or_default(),
                limits.max_conflicts,
                limits.max_assembly_observations.unwrap_or_default(),
                deadline.map_or_else(
                    || "none".to_string(),
                    |deadline| format!(
                        "{} ms",
                        deadline.saturating_duration_since(now).as_millis()
                    )
                ),
                first_solve.as_millis(),
                now.elapsed().as_millis()
            )
        });
        accepted
    }

    /// The deferred clauses when step (4a) may ask about them over
    /// `corroboration_scope` (see the module documentation), in proof order.
    fn entailment_eligible_clauses(
        &self,
        corroboration_scope: &[TermId],
        deferred: &[(ProofId, Vec<TermId>)],
    ) -> Option<Vec<Vec<TermId>>> {
        if deferred.is_empty() {
            return None;
        }
        let proof = self.last_proof.as_ref()?;
        if proof
            .steps
            .iter()
            .any(|step| matches!(step, ProofStep::Anchor { .. }))
        {
            return None;
        }
        let terms = &self.ctx.terms;
        let ground = |term: &TermId| !contains_quantifier(terms, *term);
        if !deferred
            .iter()
            .all(|(_, clause)| !clause.is_empty() && clause.iter().all(ground))
        {
            return None;
        }
        let (ground_roots, quantified_roots): (Vec<&TermId>, Vec<&TermId>) =
            corroboration_scope.iter().partition(|root| ground(root));
        let grounded = free_constants(terms, ground_roots);
        let quantified = free_constants(terms, quantified_roots);
        free_constants(terms, deferred.iter().flat_map(|(_, clause)| clause))
            .iter()
            .all(|constant| grounded.contains(constant) || !quantified.contains(constant))
            .then(|| deferred.iter().map(|(_, clause)| clause.clone()).collect())
    }
}

/// The free constants (`Var` terms) occurring anywhere in `roots`.
fn free_constants<'a>(
    terms: &TermStore,
    roots: impl IntoIterator<Item = &'a TermId>,
) -> HashSet<TermId> {
    let mut pending: Vec<TermId> = roots.into_iter().copied().collect();
    let mut seen = HashSet::default();
    let mut constants = HashSet::default();
    while let Some(term) = pending.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(terms.get(term), TermData::Var(..)) {
            constants.insert(term);
        }
        pending.extend(terms.children(term));
    }
    constants
}

/// Where step (4a)'s cap ends, for a question that starts at `now`: half of
/// what remains of the certification envelope until `backstop`, so step (4)
/// keeps the other half; `None` (no cap) without an envelope.
fn entailment_deadline(now: Instant, backstop: Option<Instant>) -> Option<Instant> {
    backstop.map(|backstop| {
        now.checked_add(backstop.saturating_duration_since(now) / 2)
            .unwrap_or(backstop)
    })
}

/// Step (4a)'s counts: step (4)'s decisions, and conflicts per SAT solve,
/// split-loop round trips and proof-assembly observations sized from the
/// first solve (`FirstSolveWork::entailment_conflicts`,
/// `entailment_round_trips`, `entailment_assembly_observations`), never more
/// conflicts than step (4)'s own allowance.
fn entailment_limits(controls: &TrustClauseDischargeControls) -> FreshReconfirmationLimits {
    let first_solve = controls.effort.first_solve();
    FreshReconfirmationLimits {
        max_conflicts: first_solve
            .entailment_conflicts()
            .min(WHOLE_PROBLEM_RECONFIRMATION_LIMITS.max_conflicts),
        max_decisions: WHOLE_PROBLEM_RECONFIRMATION_LIMITS.max_decisions,
        max_round_trips: Some(first_solve.entailment_round_trips()),
        max_assembly_observations: Some(first_solve.entailment_assembly_observations()),
    }
}

/// `¬C1 ∨ … ∨ ¬Cn`, each `¬Ci` the conjunction of its negated literals, built
/// in `terms`. `None` for the questions step (4a) must never ask: an empty
/// list, an empty clause, and a disjunction that folds to a constant (`true`
/// is step (4)'s whole-problem question; `false` would accept on folding
/// alone).
pub(super) fn negated_clause_disjunction(
    terms: &mut TermStore,
    clauses: &[Vec<TermId>],
) -> Option<TermId> {
    if clauses.is_empty() || clauses.iter().any(Vec::is_empty) {
        return None;
    }
    let mut cases = Vec::with_capacity(clauses.len());
    for clause in clauses {
        let negated = clause
            .iter()
            .map(|&literal| terms.mk_not(literal))
            .collect();
        cases.push(terms.mk_and(negated));
    }
    let refuted_cases = terms.mk_or(cases);
    (refuted_cases != terms.true_term() && refuted_cases != terms.false_term())
        .then_some(refuted_cases)
}

#[cfg(test)]
#[path = "trust_clause_entailment/tests.rs"]
mod tests;
