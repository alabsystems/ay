// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! What one [`crate::Engine::check`] answers (KC2): the verdict with
//! everything a caller may need from the check, owned, so the engine keeps no
//! borrow and no per-check proof state.

use ay_core::{ClausificationProof, CnfClause, StrengthenId, TermId, TermStore, TheoryLit};
use ay_sat::{ClauseTrace, Literal};

use crate::plugin::{LemmaTier, ProofHint};
use crate::proof::{self, KernelProof, ProofFailure};

/// One recorded proof step (design P1): the clause, as signed terms, in the
/// form it entered the SAT solver, with the hint that justifies it.
#[derive(Debug, Clone)]
pub struct RecordedStep {
    /// The clause.
    pub clause: Vec<TheoryLit>,
    /// The same clause as the SAT literals the kernel handed ay-sat, position
    /// by position; the proof assembler binds a traced clause to this step
    /// through them.
    pub sat_clause: Vec<Literal>,
    /// Its justification. Farkas coefficients, when present, are aligned with
    /// `clause`.
    pub hint: ProofHint,
    /// Its tier.
    pub tier: LemmaTier,
}

/// Structural counters of one check (design §11).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct EngineStats {
    /// ay-sat searches started by the check. The design pins this to 1 per
    /// check and per worker (K1, KC1).
    pub solve_calls: u64,
    /// Kernel `propagate` callbacks.
    pub propagate_calls: u64,
    /// Kernel final checks.
    pub final_checks: u64,
    /// Theory conflicts handed to the SAT solver.
    pub conflicts: u64,
    /// Redundant theory lemmas added during the search.
    pub lemmas: u64,
    /// Definitional (irredundant) clauses added during the search (G1).
    pub definitions: u64,
    /// Atoms that received a SAT variable during the search.
    pub minted_atoms: u64,
    /// Propagations with an eager reason clause.
    pub eager_propagations: u64,
    /// Propagations with a lazy reason.
    pub lazy_propagations: u64,
    /// Lazy reasons materialized during conflict analysis.
    pub lazy_explained: u64,
    /// Atom assignments fed to plug-ins.
    pub assigned_atoms: u64,
    /// Plug-in give-ups (0 or 1: the first one ends the check).
    pub give_ups: u64,
    /// SAT conflicts of the one search (Boolean and theory).
    pub sat_conflicts: u64,
    /// SAT decisions of the one search.
    pub sat_decisions: u64,
    /// Work units plug-ins reported through `Ctx::tick` (design R1).
    pub ticks: u64,
    /// Hub nodes after registration (design H1).
    pub hub_nodes: u64,
    /// Hub merges applied (including merges later undone).
    pub hub_merges: u64,
    /// Hub conflicts (two values in one class).
    pub hub_conflicts: u64,
    /// Hub propagations handed to the search.
    pub hub_propagations: u64,
    /// `new_eq` events delivered to plug-ins.
    pub new_eqs: u64,
    /// `new_diseq` events delivered to plug-ins.
    pub new_diseqs: u64,
    /// Model-based combination equalities proposed (design H3).
    pub combination_equalities: u64,
    /// Dynamic transitivity lemmas added (`hub/transitivity.rs`).
    pub transitivity_lemmas: u64,
    /// Backjumps the search did not report that the kernel caught up with:
    /// 0 unless ay-sat breaks its contract to announce every backjump (the
    /// kernel's fail-safe; debug builds assert it never runs).
    pub resyncs: u64,
    /// Terms the relevancy service marked relevant (KC21), undone ones
    /// included.
    pub relevant_marked: u64,
}

/// The verdict of one check.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Verdict {
    /// Satisfiable; every plug-in accepted the final assignment.
    Sat,
    /// Unsatisfiable (under the assumptions, if any).
    Unsat,
    /// Not decided; [`CheckOutcome::reason`] says why.
    Unknown,
}

/// The answer to one check (KC2).
#[derive(Debug)]
pub struct CheckOutcome {
    /// The verdict.
    pub verdict: Verdict,
    /// After `unsat` under assumptions: the assumptions in ay-sat's
    /// failed-assumption core, a subset whose conjunction with the
    /// assertions is already unsatisfiable. Empty otherwise.
    pub failed: Vec<TermId>,
    /// Literals the search fixed at decision level 0, over terms the check
    /// gave a variable (theory atoms and Boolean structure). Each follows
    /// from the assertions and T-valid lemmas alone, never from an
    /// assumption.
    pub level0_units: Vec<TheoryLit>,
    /// The strengthenings plug-ins registered in this check (KC26, Σ,
    /// through `Ctx::strengthen`). Empty today: no technique the kernel
    /// runs strengthens.
    pub sigma: Vec<StrengthenId>,
    /// Why the verdict is `Unknown` (a give-up, `timeout`, `interrupted`).
    pub reason: Option<String>,
    /// The check's counters.
    pub stats: EngineStats,
    /// With recording on (and no assumptions): what the search recorded;
    /// after `unsat`, [`Refutation::assemble`] makes the proof.
    pub proof: Option<Refutation>,
}

impl CheckOutcome {
    pub(crate) fn unknown(reason: String, stats: EngineStats) -> Self {
        Self {
            verdict: Verdict::Unknown,
            failed: Vec::new(),
            level0_units: Vec::new(),
            sigma: Vec::new(),
            reason: Some(reason),
            stats,
            proof: None,
        }
    }

    /// Whether the verdict is `sat`.
    #[must_use]
    pub fn is_sat(&self) -> bool {
        self.verdict == Verdict::Sat
    }

    /// Whether the verdict is `unsat`.
    #[must_use]
    pub fn is_unsat(&self) -> bool {
        self.verdict == Verdict::Unsat
    }
}

/// What a recording check kept for the proof assembler (design D3): the
/// assertions, the encoding's clauses with their clausification rules, the
/// kernel's recorded theory steps, and ay-sat's trace of every clause the
/// search added or learned.
#[derive(Debug)]
pub struct Refutation {
    pub(crate) assertions: Vec<TermId>,
    pub(crate) cnf: Vec<CnfClause>,
    pub(crate) annotations: Vec<Option<ClausificationProof>>,
    pub(crate) trace: Option<ClauseTrace>,
    pub(crate) var_terms: Vec<Option<TermId>>,
    pub(crate) steps: Vec<RecordedStep>,
}

impl Refutation {
    /// The theory steps the kernel recorded (design P1).
    #[must_use]
    pub fn steps(&self) -> &[RecordedStep] {
        &self.steps
    }

    /// The `unsat` answer's refutation of the asserted formulas as one
    /// DAG-shared proof (design D3), assembled from what the check recorded:
    /// the assertions as `assume` steps, the encoding's clausification steps,
    /// the kernel's theory steps with their hints, and ay-sat's resolution
    /// steps. Nothing is re-derived by search after the fact except the unit
    /// propagation that turns each learned clause's recorded antecedents into
    /// explicit resolution. `terms` is the store the check ran on; the
    /// assembly is abandoned with [`ProofFailure::OutOfTime`] once `deadline`
    /// passes.
    pub fn assemble(
        &self,
        terms: &mut TermStore,
        deadline: Option<std::time::Instant>,
    ) -> Result<KernelProof, ProofFailure> {
        let trace = self.trace.as_ref().ok_or(ProofFailure::NoTrace)?;
        proof::assemble(proof::Inputs {
            terms,
            assertions: &self.assertions,
            cnf: &self.cnf,
            annotations: &self.annotations,
            var_terms: &self.var_terms,
            records: &self.steps,
            trace,
            deadline,
        })
    }
}
