// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! M1 publication: existing strict routes only (plan §4.1 "M1 shortcut").

use super::super::Executor;
use super::concat_distinct;
use super::hints::HintSource;
use crate::cegqi::lra_nested::{InstanceLog, NodeSource, QlraTree};
use crate::ematching::ForallInstantiationProvenance;
use crate::executor::proof::NegatedExistsDual;
use crate::executor::SkolemInstanceRecord;
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::LogicCategory;
use ay_core::TermId;

/// Records handed to the consequence replay. Hints only: the replay derives
/// every source from the authored scope and the strict checker re-derives
/// every substitution, duality and Skolem choice.
pub(super) fn replay_records(
    tree: &QlraTree,
    log: &InstanceLog,
) -> (
    Vec<ForallInstantiationProvenance>,
    Vec<NegatedExistsDual>,
    Vec<SkolemInstanceRecord>,
) {
    let records = log
        .entries()
        .iter()
        .map(|entry| ForallInstantiationProvenance {
            quantifier: tree.nodes[entry.node].instance_source(),
            binding: entry.tuple.clone(),
            instance: entry.instance,
        })
        .collect();
    let duals = tree
        .nodes
        .iter()
        .filter_map(|node| match node.source {
            NodeSource::NegatedExists {
                not_exists,
                exists,
                dual,
            } => Some(NegatedExistsDual {
                not_exists_root: not_exists,
                exists,
                forall: dual,
                co_units: Vec::new(),
            }),
            NodeSource::Forall { .. } => None,
        })
        .collect();
    let skolem = tree
        .skolems
        .iter()
        .map(|root| SkolemInstanceRecord {
            source: root.source,
            quantified: root.source,
            witness: root.witness,
            instance: root.instance,
            asserted: root.instance,
            positive: true,
        })
        .collect();
    (records, duals, skolem)
}

impl Executor {
    /// UNSAT: install a strict authored-scope refutation through the
    /// consequence replay, or decline. The flag reports whether a proof was
    /// INSTALLED (published or not): an installed proof holds the pass's
    /// terms, so the caller must then keep them.
    pub(in crate::executor) fn qlra_publish_unsat(
        &mut self,
        tree: &QlraTree,
        log: &InstanceLog,
    ) -> (Option<Result<SolveResult>>, bool) {
        if log.entries().is_empty() && tree.skolems.is_empty() {
            // A refutation of the ground siblings alone is the legacy path's.
            self.last_statistics.set_string("qlra.cert", "no-instances");
            return (None, false);
        }
        let (records, duals, skolem) = replay_records(tree, log);
        // The replay's per-query ATTEMPT ledger (retry count + direct
        // ground-pin fingerprint) is the legacy path's: a declined lane
        // attempt hands it back, or the lane's first pass plus its memo retry
        // exhaust `MAX_REPLAY_ATTEMPTS` and the legacy replay then refuses a
        // refutation base publishes. The query-wide WALL envelope is not
        // handed back (it is net-refunded and must stay bounded across every
        // scope); `qlra.replay_probe_ms` reports what the lane spent from it.
        let ledger = (
            self.consequence_replay_attempts.get(),
            self.consequence_replay_direct_state.get(),
        );
        let granted_before = self.consequence_replay_probe_budget.granted_ms();
        let installed = self
            .try_translate_authored_consequence_replay_unsat_with_duals(&records, &duals, &skolem);
        let spent = self
            .consequence_replay_probe_budget
            .granted_ms()
            .saturating_sub(granted_before);
        self.qlra_add_stat_ms("qlra.replay_probe_ms", spent);
        // Re-validate the exact installed proof at the consumption point
        // (scope, empty clause, strict completeness) and re-check stop state,
        // mirroring `cegqi_unsat_authority::publish_installed`.
        let publishable = installed
            && !self.should_abort_theory_loop()
            && self.authored_scope_strict_proof_installed();
        self.last_statistics.set_string(
            "qlra.cert",
            if publishable { "installed" } else { "declined" },
        );
        if !publishable {
            self.consequence_replay_attempts.set(ledger.0);
            self.consequence_replay_direct_state.set(ledger.1);
            return (None, installed);
        }
        self.last_unknown_reason = None;
        (Some(Ok(SolveResult::unsat())), true)
    }

    /// SAT: install a model of `ground ∧ Γ` and let the quantified model gate
    /// decide. A refusal restores the candidate state and declines.
    pub(super) fn qlra_publish_sat(
        &mut self,
        tree: &QlraTree,
        log: &InstanceLog,
    ) -> Option<Result<SolveResult>> {
        self.qlra_publish_sat_working(concat_distinct(&tree.ground, &log.instance_terms()), None)
    }

    /// SAT from a quantifier-free `working` set every model of which
    /// satisfies the authored roots (the search's claim; the gate re-checks
    /// it): install a model and let the quantified model gate decide. A
    /// nested search also installs its instance log as expansion hints for
    /// the gate (untrusted data; dropped again on a refusal).
    pub(super) fn qlra_publish_sat_working(
        &mut self,
        working: Vec<TermId>,
        hints: Option<(&[TermId], &HintSource<'_>)>,
    ) -> Option<Result<SolveResult>> {
        self.qlra_publish_sat_working_as(working, LogicCategory::QfLra, hints)
    }

    /// [`Self::qlra_publish_sat_working`] with the ground solve's category
    /// chosen by the caller (the QSAT route installs `Int` witnesses too).
    fn qlra_publish_sat_working_as(
        &mut self,
        working: Vec<TermId>,
        category: LogicCategory,
        hints: Option<(&[TermId], &HintSource<'_>)>,
    ) -> Option<Result<SolveResult>> {
        let saved_reason = self.last_unknown_reason;
        let window = std::mem::replace(&mut self.ctx.assertions, working);
        let solved = self.solve_for_category(category);
        self.ctx.assertions = window;
        if !matches!(solved, Ok(SolveResult::Sat)) || self.last_model.is_none() {
            self.last_statistics.set_string("qlra.gate", "no-model");
            self.last_model = None;
            self.last_model_validated = false;
            self.last_unknown_reason = saved_reason;
            return None;
        }
        self.last_model_validated = false;
        if let Some((roots, source)) = hints {
            self.qlra_install_expansion_hints(roots, source);
        }
        // Wall of the lane's gate arm: an upper bound on what it withheld
        // from the query-wide gate envelope.
        let gate_started = ay_core::time::Instant::now();
        let gated = self.apply_quantified_model_failclosed_gate(SolveResult::Sat);
        let spent = ay_core::time::Instant::now().saturating_duration_since(gate_started);
        self.qlra_add_stat_ms(
            "qlra.gate_ms",
            u64::try_from(spent.as_millis()).unwrap_or(u64::MAX),
        );
        let confirmed = gated == SolveResult::Sat && !self.should_abort_theory_loop();
        self.last_statistics
            .set_string("qlra.gate", if confirmed { "confirmed" } else { "refused" });
        if let Some(installed) = self.qlra_lane.expansion_hints.as_deref() {
            let (consulted, xp_confirmed) = (installed.consulted.get(), installed.confirmed.get());
            self.last_statistics
                .set_int("qlra.gate_xp_consulted", u64::from(consulted));
            self.last_statistics
                .set_int("qlra.gate_xp_confirmed", u64::from(xp_confirmed));
        }
        if !confirmed {
            self.qlra_lane.expansion_hints = None;
            self.last_model = None;
            self.last_model_validated = false;
            self.last_unknown_reason = saved_reason;
            return None;
        }
        self.last_unknown_reason = None;
        Some(Ok(SolveResult::Sat))
    }

    /// Accumulate a wall-envelope spend across the first pass and its memo
    /// retries (the memo restores the earlier passes' `qlra.*` values).
    pub(super) fn qlra_add_stat_ms(&mut self, key: &str, spent_ms: u64) {
        let total = self
            .last_statistics
            .get_int(key)
            .unwrap_or(0)
            .saturating_add(spent_ms);
        self.last_statistics.set_int(key, total);
    }
}
