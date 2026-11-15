// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unrewritten authored replay (#unrewritten-authored-replay).
//!
//! # The gap this closes
//!
//! A ground query's refutation is computed over the PREPROCESSED window:
//! variable substitution eliminates a symbol by its defining equality
//! everywhere, and the preprocessing record is what the proof reconstruction
//! later has to bridge back to the authored assertions. When no bridge
//! reaches the rewritten leaf, the leaf stays a premiseless `trust` step, the
//! strict checker rightly refuses it, and a correct `unsat` is withdrawn to
//! `unknown (incomplete self-check-rejected)`.
//!
//! deductive-checksgen's reachability encoding produces exactly that shape (the
//! superproject's DECISION_QUEUE D16): a join is spelled `R_J == Or(..)` over
//! fresh Boolean variables, one Tseitin definition per join, and the row
//! asserts the definitions beside the body. Substitution then inlines every
//! definition into the next one and constant-folds the result, so the unit
//! the SAT search starts from is the whole nested reach condition — a leaf
//! that is a consequence of several authored conjuncts at once, not a
//! congruence image of one of them. Measured on the captured
//! `coroutine_resume_saturated_unreachable` and `path_budget_async_sentinel`
//! `Unreachable` rows ("step t0 uses unverified trust rule").
//!
//! # What this lane does
//!
//! It re-decides the EXACT authored roots once, on the same-context
//! disposable probe the consequence-replay lane uses
//! ([`Executor::checked_same_context_unsat_proof`]). That probe performs no
//! in-place variable substitution (`proof_probe_skips_varsubst`) and runs
//! non-incrementally over a fresh window holding only those roots, so every
//! original clause of its search is a clausification of an authored root and
//! the ordinary reconstruction derives it with checked rules. Over the
//! reachability encoding the refutation is then a case split through the
//! asserted definition — `R_J`, `R_J == Or(d_i)`, and one closed branch per
//! `d_i` — spelled in `equiv_pos2`/`or_pos`/`and_pos`/`resolution` steps the
//! strict checker validates one by one.
//!
//! Inside a push/pop session the probe window is the whole LIVE assertion
//! stack and nothing else, which is the fresh-per-row question the session
//! stands for: no popped assertion, learned clause or lemma of an earlier
//! query can reach it.
//!
//! # Presentation
//!
//! The candidate replaces `last_proof` AFTER the ordinary assembly ran its
//! final presentation passes, so it owes them itself (the obligation
//! `restore_reachable_authored_assume_surface_overrides` documents): an
//! assumed elaborated conjunction is rehomed onto its authored spelling with
//! checked transports, and the reachable authored `assume`s are re-spelled
//! from the problem text. The surface spellings the ordinary rebuild
//! registered for the authored roots and their subterms stay: they are the
//! problem file's own spellings of exactly the terms this candidate projects.
//! Measured on both content-free rows: purging them first (as the cascade
//! does for candidates carrying synthesized theory clauses) left the authored
//! `assume` beside identity-spelled `and_pos` projections the printer cannot
//! bridge, and the identity spelling of the whole document is refused by
//! pinned Carcara (its `assume` matches no premise); kept, the document is
//! Carcara-valid.
//!
//! Presentation never decides the verdict. The certificate is minted from the
//! strictly checked proof; whether its Alethe document renders is decided
//! afterwards, by the exporter, exactly as for the ordinary lane: a document
//! that cannot render is refused at `(get-proof)` (or left out of the API
//! artifact) while the checked verdict stands. An earlier revision screened
//! the candidate with [`Executor::presents_wire_clean`] and withdrew the
//! verdict when the screen failed, which let the presentation passes' fixed
//! size limits turn a checked `unsat` into `unknown` (measured: the
//! coroutine row beside 8,093 irrelevant facts, proofs on).
//!
//! # Soundness
//!
//! Nothing is admitted on the probe's word. Its proof is returned only when
//! its own strict checker accepts it complete over the probe window; the
//! candidate is then installed only through
//! [`Executor::install_consequence_replay_candidate`], which re-checks that
//! every reachable `assume` is an exact authored root, that the empty clause
//! is derived, and that the full strict checker accepts it; and publication
//! mints the certificate from that proof through the unchanged strict
//! presentation gate. A probe that answers `sat`, `unknown`, or produces no
//! strict proof leaves the withdrawal exactly as it was. UNSAT-only: no arm
//! can produce or influence a SAT verdict. It is off under the parent kill
//! switch `--no-consequence-replay`.
//!
//! # Effort, not wall clock
//!
//! The probe is bounded by exactly what bounds the query it replays: the
//! caller's deadline and interrupt, and the deterministic per-solve effort
//! allowances the probe executor inherits (`qpf_probe_executor_within`). It
//! has no wall-clock sub-budget of its own and does not draw on the
//! consequence-replay probe envelope, whose fixed 5 s total, 250 ms floor and
//! half-the-remaining-deadline share made this lane's verdict a function of
//! the clock (measured: `coroutine_resume_saturated_unreachable` was
//! `unknown` at `-t 500` after 41 ms of work and `unsat` at `-t 600`). When
//! the size-scaled deterministic effort bound replaces the fixed allowances,
//! the probe inherits it with them.

use super::*;
use crate::executor::quantifier_loop::result_mapping::{
    SameContextProbeOutcome, SameContextWindow,
};

impl Executor {
    /// Re-decide the exact authored roots of a withdrawn ground UNSAT on the
    /// unrewritten probe and install its strictly checked refutation.
    ///
    /// Returns whether a candidate was installed as `last_proof`; the caller
    /// must still mint the certificate through the ordinary strict gate.
    ///
    /// The probe runs a whole nested `check-sat` on this thread, so it runs
    /// behind the executor's own stack guard, like the executor's entry points.
    pub(in crate::executor) fn install_unrewritten_authored_replay(
        &mut self,
        assumptions: &[TermId],
    ) -> bool {
        if !self.unrewritten_authored_replay_applies(assumptions) {
            return false;
        }
        let roots = self.exact_concrete_authored_scope();
        if roots.is_empty() || crate::ematching::contains_quantifier_in_any(&self.ctx.terms, &roots)
        {
            return false;
        }
        let candidate = stacker::maybe_grow(
            crate::executor::EXECUTOR_STACK_RED_ZONE,
            crate::executor::EXECUTOR_STACK_SIZE,
            || self.replay_authored_roots(&roots),
        );
        let Some(candidate) = candidate else {
            return false;
        };
        if !self.candidate_authored_surface_is_available(&candidate)
            || !self.install_consequence_replay_candidate(Some(candidate))
        {
            return false;
        }
        self.present_installed_replay();
        true
    }

    /// The window-scoped probe over `roots`, then — only when it refuted the
    /// roots but its proof fused into a lemma strict mode refuses — the same
    /// probe over the whole-store array-axiom surface (the retry
    /// `metered_consequence_replay_probe` documents). Both run under the
    /// caller's deadline alone (see the module documentation).
    fn replay_authored_roots(&mut self, roots: &[TermId]) -> Option<Proof> {
        let probe = |executor: &mut Self, scope_to_window: bool| {
            executor.checked_same_context_unsat_proof(
                roots,
                SameContextWindow::Ground,
                None,
                None,
                scope_to_window,
            )
        };
        match probe(self, true) {
            SameContextProbeOutcome::Proof(proof) => Some(proof),
            SameContextProbeOutcome::UnsatUnpromotable => match probe(self, false) {
                SameContextProbeOutcome::Proof(proof) => Some(proof),
                SameContextProbeOutcome::UnsatUnpromotable | SameContextProbeOutcome::Other => None,
            },
            SameContextProbeOutcome::Other => None,
        }
    }

    /// The assembly's final presentation passes, run on the installed
    /// candidate (see the module documentation). Presentation only: the
    /// certificate is minted afterwards from the proof these passes leave,
    /// through the unchanged strict gate.
    fn present_installed_replay(&mut self) {
        let Some(mut proof) = self.last_proof.take() else {
            return;
        };
        self.rehome_elaborated_conjunction_assumes(&mut proof);
        self.restore_reachable_authored_assume_surface_overrides(&proof);
        self.last_proof = Some(proof);
    }

    /// Whether a re-decision can differ from the solve that was just
    /// withdrawn: the original search ran over a window variable substitution
    /// rewrote, or it ran inside an incremental session whose carried state
    /// the fresh probe does not have. A replay of the very same engine on the
    /// very same window would only spend the query's time to reach the same
    /// proof.
    /// Never inside a nested certification solve: those corroborate an outer
    /// query, which runs this lane itself if its own proof is refused.
    fn unrewritten_authored_replay_applies(&self, assumptions: &[TermId]) -> bool {
        crate::quant_unit_authority::consequence_replay_enabled()
            && !crate::executor::unsat_cert::inside_nested_certification_solve()
            && assumptions.is_empty()
            && self.last_assumptions.is_none()
            && !self.proof_probe_skips_varsubst
            && (!self.skip_varsubst_for_proofs() || self.incremental_mode)
            && self.external_stop_reason().is_none()
    }
}
