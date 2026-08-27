// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl Executor {
    fn configure_public_solve_proof_posture(&mut self) {
        // Proof output is optional; proof-backed UNSAT correctness is not.
        // Enable internal proof tracking for every public decision before the
        // authored scope is finalized. `--no-proof` and `:produce-proofs false`
        // still suppress user-facing artifacts, but cannot disable the soundness
        // certificate required to publish `unsat`.
        //
        // Competition mode (#proof-capability B1) is the sole, explicit opt-out
        // of that invariant: with no proof demand in scope the tracker is left
        // DISABLED so search pays no recording cost. PRECEDENCE, not conflict —
        // `--proof`/`set_produce_proofs(true)`, in-script `(set-option
        // :produce-proofs true)`, `(set-option :check-proofs-strict true)`, and
        // self-check mode each defeat shedding and restore the certified lanes
        // for this and later solves (`competition_shedding_active`). The
        // explicit `disable()` (rather than merely skipping `enable()`) makes
        // re-shedding after `(set-option :produce-proofs false)` deterministic.
        // Publication under shedding goes through the B3 CompetitionRaw
        // admission lane (unsat_cert.rs, `certify_unsat_presentation`): the
        // exact query scope still authenticates and stops still revoke, but no
        // checked certificate backs the verdict — the documented product
        // carve-out. A raw UNSAT whose scope fails authentication still
        // fail-closes to `unknown`.
        //
        // #quantified-trace-arming: a fresh public decision always STARTS shed.
        // The trace is armed only by `quantified_trace_arming_unknown_retry`,
        // on the `Unknown` fallback, so the first pass of every solve is
        // byte-identical to the pre-campaign behaviour. Clearing the latch here
        // is what makes that true across an incremental session.
        self.quantified_query_defeats_shedding = false;
        if self.competition_shedding_active() {
            self.proof_tracker.disable();
        } else {
            self.proof_tracker.enable();
        }
        // #boolarg-orphan: drop the previous query's orphan->twin map.
        //
        // The field doc says a proxy from an earlier check-sat "can never be
        // read back" because every purification REPLACES the map. That holds
        // only while `purify_bool_args` actually runs on every solve — a later
        // query routed past the pass would inherit the previous query's entries
        // and could resolve an application through a twin THIS solve never
        // pinned. Clearing per public solve is what makes that doc claim true
        // rather than nearly true: an unrun pass now leaves an EMPTY map, which
        // fails closed to today's behaviour, instead of a stale one.
        self.bool_arg_orphan_index.clear();
        // Retention re-arm is gated exactly like the tracker: a shedding
        // competition session keeps whatever retention state the CLI/API chose
        // (the CLI turns it off at session start), while any proof demand —
        // including an in-script `:produce-proofs true` — re-arms it here for
        // proof surface-syntax alignment.
        if !self.competition_shedding_active() {
            self.ctx.set_retain_parsed_assertions(true);
        }
    }

    /// Revoke every user-visible artefact at the start of a public decision
    /// query, before preflight or elaboration can fail. Consecutive Pareto
    /// queries are the sole case that may retain algorithmic enumeration state;
    /// the previously emitted result/model/certificate are still always cleared.
    pub(crate) fn begin_public_solve(&mut self, preserve_pareto_enumeration: bool) {
        self.advance_query_authority_epoch();
        // M0(a): these counters describe one public publication attempt.
        // Internal probes deliberately share their enclosing attempt, while a
        // new user-visible decision starts a fresh attribution window.
        self.strict_check_invocations.set(0);
        self.strict_check_steps_validated.set(0);
        #[cfg(test)]
        {
            self.last_authored_query_authority_seen = false;
        }
        self.array_ext_witness_cache
            .begin_public_solve(&self.ctx.terms);
        self.configure_public_solve_proof_posture();
        let authored_assertions = self.ctx.assertions.clone();
        let pareto_state = if preserve_pareto_enumeration {
            self.pareto_state.take()
        } else {
            None
        };
        self.invalidate_last_check_result();
        if preserve_pareto_enumeration {
            self.pareto_state = pareto_state;
        }
        self.begin_unsat_query_epoch(&authored_assertions);
        // Install the pre-elaboration proof authority at the public-query
        // boundary. SMT-LIB command dispatch may replace it exactly once with
        // authenticated schematic instances; recursive retries and
        // optimization/probe solves then inherit those roots rather than
        // recapturing their generated working set as authored input.
        self.install_proof_source_provenance(&authored_assertions);
        unsat_cert::probe_cert_reject(|| {
            format!(
                "begin_public_solve: tracker={} provenance={} authored_roots={}",
                self.produce_proofs_enabled(),
                self.proof_problem_assertion_provenance.is_some(),
                authored_assertions.len()
            )
        });
        // #proof-capability B1 mis-plumbing canary: a competition-mode
        // executor with no proof demand must leave this public solve with the
        // tracker OFF — if a future edit re-enables it unconditionally above
        // (or in a helper called from here), the shedding silently dies and
        // every competition run pays the certified-mode proof cycle again.
        //
        // #quantified-trace-arming does NOT weaken this: it arms the trace on
        // the `Unknown` fallback inside `check_sat`, never at the public-solve
        // boundary, so every solve still STARTS shed and the postcondition is
        // unchanged.
        debug_assert!(
            !self.competition_shedding_active() || !self.proof_tracker.is_enabled(),
            "competition-mode executor with no proof demand must have the proof \
             tracker disabled after begin_public_solve"
        );
    }

    /// Start a caller-visible decision query and replenish resource envelopes
    /// that must remain cumulative across every nested solve/restart it owns.
    pub(crate) fn begin_external_decision_query(&mut self, preserve_pareto_enumeration: bool) {
        self.begin_external_proof_checkpoint_budget();
        // The consequence-replay lane's WALL envelope re-arms HERE and nowhere
        // else. `begin_public_solve` is the wrong boundary: nested
        // corroboration re-solves and internal probe executors call it, and a
        // per-`begin_public_solve` replenish would restore exactly the
        // unbounded multiplication this envelope exists to stop.
        self.consequence_replay_probe_budget.begin_external_query();
        // Same boundary, same reason, for the quantified model gate's arms.
        // `begin_public_solve` is the wrong one: the gate's own nested probe
        // executors call it, and re-arming there would hand every probe a fresh
        // envelope -- the per-call constant this replaced, wearing a new name.
        self.quantified_gate_probe_budget.begin_external_query();
        self.finite_array_expansion
            .prune_to_active_assertions(&self.ctx.terms, &self.ctx.assertions);
        self.finite_array_expansion.begin_external_query();
        self.begin_public_solve(preserve_pareto_enumeration);
    }

    /// Bind public UNSAT/proof authority to the frontend's final query roots.
    ///
    /// `begin_public_solve` runs before command elaboration so even a malformed
    /// query revokes stale artifacts. SMT-LIB 2.7 schematic assertions are
    /// materialized during that elaboration, however, and must be included in
    /// the exact epoch before any solver lane runs. This is the sole permitted
    /// pre-solve rebind; the epoch method refuses it once assumptions are bound.
    pub(crate) fn bind_materialized_public_query(&mut self) {
        let assertions = self.ctx.assertions.clone();
        let had = self.proof_problem_assertion_provenance.is_some();
        self.proof_problem_assertion_provenance = None;
        let rebound = self.rebind_unsat_query_epoch_assertions(&assertions);
        if rebound {
            self.install_proof_source_provenance(&assertions);
        }
        unsat_cert::probe_cert_reject(|| {
            format!(
                "bind_materialized_public_query: had_provenance={had} rebound={rebound} \
                 provenance={} epoch={}",
                self.proof_problem_assertion_provenance.is_some(),
                self.unsat_query_epoch.is_some()
            )
        });
    }
}
