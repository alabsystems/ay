// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The kernel: one `ay_sat::Extension` in front of every plug-in (design §3).

use std::cell::Cell;

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{TermId, TermStore, TheoryLit};
use ay_sat::{
    ExtCheckResult, ExtContinue, ExtPropagateResult, Extension, Literal, SolverContext, Variable,
};

use crate::atoms::{AtomTable, Family};
use crate::engine::{EngineStats, RecordedStep};
use crate::hub::{Hub, NodeId};
use crate::plugin::{Ctx, Effects, GiveUp, LemmaTier, ProofHint, ThId, TheoryPlugin};

mod clauses;
mod construct;
mod decide;
mod finals;
mod hub_build;
mod hub_glue;
mod intern;
mod relevancy;
mod schedule;

pub(crate) use relevancy::Relevancy;

use clauses::{sat_lit, strip_not};
use schedule::FinalSchedule;

/// `propagate` polls the stop request once per this many calls, as the
/// lanes' extension does (`propagation_guard_result`): ay-sat polls only at
/// conflicts, decisions and some theory rounds, and one long run of theory
/// rounds must not carry the search past its deadline.
const STOP_POLL_INTERVAL: u64 = 16;

/// A lazy propagation awaiting explanation; its index is ay-sat's reason tag.
struct LazyEntry {
    plugin: ThId,
    token: u64,
    lit: TheoryLit,
}

pub(crate) struct Kernel<'t> {
    terms: &'t mut TermStore,
    /// The engine's stop request (deadline, cancel flag), polled in
    /// `propagate` and before every final check.
    pub(crate) stop: Option<&'t dyn Fn() -> bool>,
    /// The check's guard, lent to plug-ins for [`Ctx::tick`].
    pub(crate) guard: Option<&'t crate::engine::Guard>,
    /// Strengthenings plug-ins registered during the check (KC26, Σ).
    pub(crate) sigma: Vec<ay_core::StrengthenId>,
    /// The search ended because `stop` answered true inside a callback.
    pub(crate) stopped: bool,
    pub(crate) plugins: Vec<Box<dyn TheoryPlugin>>,
    families: Vec<(Family, ThId)>,
    pub(crate) atoms: AtomTable,
    /// The e-graph (design H1).
    pub(crate) hub: Hub,
    /// SAT variable -> 1 + index into `hub_watch` (0: no Boolean hub node
    /// listens to it). Dense (KC3): one array read per assigned literal.
    hub_var: Vec<u32>,
    /// The Boolean hub nodes listening to one variable, each with whether it
    /// is the variable's negation (`(not p)` as an argument).
    hub_watch: Vec<Vec<(NodeId, bool)>>,
    /// Hub propagations awaiting explanation: `(node, value node)`.
    hub_props: Vec<(NodeId, NodeId)>,
    /// Hand only relevant hub propagations to the search (KC21).
    pub(crate) hub_relevancy: bool,
    /// The relevancy service (KC21), running when `hub_relevancy` is on.
    relevancy: Option<Relevancy>,
    effects: Effects,
    /// Next trail position not yet fed to the plug-ins.
    trail_pos: usize,
    /// Trail position saved when each plug-in scope was pushed (one per level).
    cursors: Vec<usize>,
    /// How far `can_propagate` has scanned the trail for theory atoms.
    scan_pos: Cell<usize>,
    /// The combined plug-in phase epoch of the last phase seeding.
    seeded_epoch: Cell<Option<u64>>,
    /// Theory-aware branching (design §3.8): an engine option, off by default.
    pub(crate) theory_branching: bool,
    decision_calls: Cell<u64>,
    lazy: Vec<LazyEntry>,
    /// Atoms minted since the last internalization pass, with their variable.
    minted: Vec<(u32, ThId, TermId)>,
    next_mint: usize,
    last_final: Option<ExtContinue>,
    /// Literals the search should decide first (H3); stale once assigned.
    preferred: Vec<Literal>,
    repeats: u32,
    /// The final check's fair turn order within each level (KC8).
    schedule: FinalSchedule,
    pub(crate) give_up: Option<GiveUp>,
    pub(crate) proof: Option<Vec<RecordedStep>>,
    pub(crate) stats: EngineStats,
    pub(crate) final_sat: bool,
}

impl Kernel<'_> {
    /// Run `f` on plug-in `id` with a context lending the term store (K3).
    fn call<R>(
        &mut self,
        id: ThId,
        sat: Option<&dyn SolverContext>,
        f: impl FnOnce(&mut Box<dyn TheoryPlugin>, &mut Ctx<'_>) -> R,
    ) -> Option<R> {
        let proofs = self.proof.is_some();
        let plugin = self.plugins.get_mut(usize::from(id))?;
        let mut ctx = Ctx::new(
            &mut *self.terms,
            sat,
            &self.atoms,
            Some(&self.hub),
            &mut self.effects,
            id,
            proofs,
        )
        .with_guard(self.guard)
        .with_relevancy(self.relevancy.as_ref());
        let result = f(plugin, &mut ctx);
        self.stats.ticks += std::mem::take(&mut self.effects.ticks);
        for id in std::mem::take(&mut self.effects.sigma) {
            if !self.sigma.contains(&id) {
                self.sigma.push(id);
            }
        }
        Some(result)
    }

    /// Whether the engine asked the search to stop; latched.
    fn stop_requested(&mut self) -> bool {
        if !self.stopped && self.stop.is_some_and(|stop| stop()) {
            self.stopped = true;
        }
        self.stopped
    }

    fn plugin_count(&self) -> ThId {
        ThId::try_from(self.plugins.len()).unwrap_or(ThId::MAX)
    }

    /// Record a clause the kernel hands ay-sat, with its hint (design P1).
    /// `sat_clause` is the same clause as SAT literals, position by position.
    fn record(
        &mut self,
        clause: Vec<TheoryLit>,
        sat_clause: &[Literal],
        hint: ProofHint,
        tier: LemmaTier,
    ) {
        if let Some(steps) = self.proof.as_mut() {
            debug_assert_eq!(clause.len(), sat_clause.len());
            steps.push(RecordedStep {
                clause,
                sat_clause: sat_clause.to_vec(),
                hint,
                tier,
            });
        }
    }

    /// Close every scope above `new_level` (a backjump): plug-ins, the
    /// relevancy service and the hub pop together, and the trail is fed
    /// again from the cursor of that level.
    fn pop_to(&mut self, new_level: u32) {
        // The trail shrank: rescan it for atoms from what the plug-ins saw.
        self.scan_pos.set(self.trail_pos);
        let target = usize::try_from(new_level).unwrap_or(usize::MAX);
        let Some(&cursor) = self.cursors.get(target) else {
            return;
        };
        let popped = u32::try_from(self.cursors.len() - target).unwrap_or(u32::MAX);
        self.trail_pos = cursor;
        self.scan_pos.set(cursor);
        self.cursors.truncate(target);
        for id in 0..self.plugin_count() {
            self.call(id, None, |p, ctx| p.pop_scope(ctx, popped));
        }
        if let Some(relevancy) = self.relevancy.as_mut() {
            relevancy.pop_scopes(popped as usize);
        }
        self.hub.pop_scopes(popped as usize);
        self.reset_effects_keeping_lemmas();
    }

    /// Catch up with a backjump the search did not report: a fail-safe that
    /// never runs (ay-sat announces every backjump, `reduce_db`'s jump to
    /// level 0 included), counted in [`EngineStats::resyncs`] and asserted
    /// against in debug builds. It pops the scopes above the current level,
    /// and those whose cursor a shrunk trail no longer reaches.
    fn resync(&mut self, sat: &dyn SolverContext) {
        let level = sat.decision_level();
        if usize::try_from(level).map_or(false, |l| l < self.cursors.len()) {
            self.stats.resyncs += 1;
            debug_assert_eq!(self.stats.resyncs, 0, "ay-sat backjumped unannounced");
            self.pop_to(level);
        }
        let len = sat.trail().len();
        if self.trail_pos > len {
            let keep = self.cursors.iter().take_while(|&&c| c <= len).count();
            if keep < self.cursors.len() {
                self.stats.resyncs += 1;
                debug_assert_eq!(self.stats.resyncs, 0, "ay-sat shrank the trail unannounced");
                self.pop_to(u32::try_from(keep).unwrap_or(u32::MAX));
            }
        }
    }

    /// Drop the buffered propagations, conflict and preferences (they belong
    /// to the assignment just left) but keep the lemmas: every lemma is
    /// T-valid or a definition (K4) at any level, and a definition an owner
    /// made while internalizing a minted atom (DL's `a ≤ b ∧ b ≤ a` for an
    /// equality) is never made again, so dropping it would leave the atom
    /// undefined.
    fn reset_effects_keeping_lemmas(&mut self) {
        let lemmas = std::mem::take(&mut self.effects.lemmas);
        self.effects = Effects::default();
        self.effects.lemmas = lemmas;
    }

    fn fail(&mut self, give_up: GiveUp) {
        self.effects = Effects::default();
        self.stats.give_ups += 1;
        self.give_up.get_or_insert(give_up);
    }

    /// Open one plug-in scope per decision level not yet mirrored, saving the
    /// pre-feed cursor, then feed every new trail literal to its owner. A
    /// backjump restores the cursor, so literals that survive it but were fed
    /// in a popped scope are fed again (safe under chronological backtracking).
    fn feed(&mut self, sat: &dyn SolverContext) -> Result<(), GiveUp> {
        let trail = sat.trail();
        self.resync(sat);
        self.trail_pos = self.trail_pos.min(trail.len());
        let level = usize::try_from(sat.decision_level()).unwrap_or(usize::MAX);
        while self.cursors.len() < level {
            self.cursors.push(self.trail_pos);
            for id in 0..self.plugin_count() {
                self.call(id, Some(sat), |p, ctx| p.push_scope(ctx));
            }
            self.hub.push_scope();
            if let Some(relevancy) = self.relevancy.as_mut() {
                relevancy.push_scope();
            }
        }
        let start = self.trail_pos;
        self.trail_pos = trail.len();
        for &lit in trail.iter().skip(start) {
            let var = lit.variable().index();
            let value = lit.is_positive();
            if let Some(relevancy) = self.relevancy.as_mut() {
                relevancy.assigned(var, self.terms, &self.atoms, &mut self.hub, sat);
            }
            let watch = self.hub_var.get(var).copied().unwrap_or(0);
            if watch != 0 {
                if let Some(nodes) = self.hub_watch.get(watch as usize - 1) {
                    for &(node, negated) in nodes {
                        self.hub.assign(node, value != negated);
                    }
                }
            }
            let Some(entry) = self.atoms.entry(var) else {
                continue;
            };
            self.stats.assigned_atoms += 1;
            let handle = entry
                .handle
                .ok_or_else(|| GiveUp::new("an atom was assigned before its owner had it"))?;
            self.call(entry.owner, Some(sat), |p, ctx| {
                p.assign(ctx, handle, value)
            })
            .unwrap_or_else(|| Err(GiveUp::new("atom owner missing")))?;
        }
        if let Some(relevancy) = self.relevancy.as_ref() {
            self.stats.relevant_marked = relevancy.marked();
        }
        self.hub_closure(sat)
    }

    fn propagate_plugins(&mut self, sat: &dyn SolverContext) -> Result<(), GiveUp> {
        for id in 0..self.plugin_count() {
            if self.effects.conflict.is_some() {
                break;
            }
            let ready = self
                .plugins
                .get(usize::from(id))
                .is_some_and(|p| p.can_propagate());
            if !ready {
                continue;
            }
            if let Some(result) = self.call(id, Some(sat), |p, ctx| p.propagate(ctx)) {
                result?;
            }
        }
        Ok(())
    }

    fn drain_search(&mut self, sat: &dyn SolverContext) -> Result<ExtPropagateResult, GiveUp> {
        let effects = std::mem::take(&mut self.effects);
        let mut result = match effects.conflict {
            Some(conflict) => ExtPropagateResult::conflict(self.conflict_clause(conflict, sat)?),
            None => ExtPropagateResult::none(),
        };
        // Lemmas are T-valid or definitional (K4), so they are kept even beside
        // a conflict; ay-sat never drops a definition (G1).
        let mapped = self.map_lemmas(effects.lemmas, sat)?;
        result.clauses = mapped.redundant;
        result.definitions = mapped.definitional;
        if result.conflict.is_none() {
            let mut seen = HashSet::default();
            for prop in effects.props {
                self.push_propagation(prop, sat, &mut seen, &mut result);
            }
        }
        self.note_preferred(effects.preferred)?;
        self.internalize_minted()?;
        result.num_vars = self.next_mint;
        Ok(result)
    }
}

impl Extension for Kernel<'_> {
    fn propagate(&mut self, sat: &dyn SolverContext) -> ExtPropagateResult {
        if self.give_up.is_some() {
            return ExtPropagateResult::none().with_stop(true);
        }
        self.stats.propagate_calls += 1;
        if self
            .stats
            .propagate_calls
            .is_multiple_of(STOP_POLL_INTERVAL)
            && self.stop_requested()
        {
            return ExtPropagateResult::none().with_stop(true);
        }
        let outcome = self
            .feed(sat)
            .and_then(|()| self.propagate_plugins(sat))
            .and_then(|()| self.drain_search(sat));
        match outcome {
            Ok(result) => result,
            Err(give_up) => {
                self.fail(give_up);
                ExtPropagateResult::none().with_stop(true)
            }
        }
    }

    fn can_propagate(&self, sat: &dyn SolverContext) -> bool {
        self.give_up.is_some()
            || !self.effects.lemmas.is_empty()
            || usize::try_from(sat.decision_level()).map_or(true, |l| l != self.cursors.len())
            || self.new_atom_on_trail(sat)
            || self.hub.has_pending()
            || self.plugins.iter().any(|p| p.can_propagate())
    }

    fn seed_phase_hints_dual(&self, phase: &mut [i8], target_phase: &mut [i8], vals: &[i8]) {
        self.seed_phases(phase, target_phase, vals);
    }

    fn check(&mut self, sat: &dyn SolverContext) -> ExtCheckResult {
        self.final_sat = false;
        if self.give_up.is_some() || self.stop_requested() {
            return ExtCheckResult::Unknown;
        }
        self.stats.final_checks += 1;
        match self.final_check(sat) {
            Ok(result) => result,
            Err(give_up) => {
                self.fail(give_up);
                ExtCheckResult::Unknown
            }
        }
    }

    fn backtrack(&mut self, new_level: u32) {
        self.pop_to(new_level);
    }

    fn suggest_decision(&self, sat: &dyn SolverContext) -> Option<Literal> {
        self.preferred
            .iter()
            .copied()
            .find(|&lit| sat.lit_value(lit).is_none())
            .or_else(|| self.theory_decision(sat))
    }

    fn explain_lazy_reason(
        &mut self,
        propagated: Literal,
        reason_data: u64,
    ) -> Option<Vec<Literal>> {
        let entry = self.lazy.get(usize::try_from(reason_data).ok()?)?;
        let (plugin, token, lit) = (entry.plugin, entry.token, entry.lit);
        let (reason, hint) = self.explain_entry(plugin, token, lit)?;
        let mut clause = Vec::with_capacity(reason.len() + 1);
        clause.push(propagated);
        for r in &reason {
            let (term, value) = strip_not(self.terms, r.term, r.value);
            clause.push(sat_lit(self.atoms.var_of(term)?, value).negated());
        }
        self.record_reason(lit, &reason, &clause, hint);
        Some(clause)
    }

    fn suggest_phase(&self, var: Variable) -> Option<bool> {
        let entry = self.atoms.entry(var.index())?;
        self.plugins
            .get(usize::from(entry.owner))?
            .phase(entry.term)
    }
}
