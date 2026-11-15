// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `Engine`: assertions in, one ay-sat search per check out (design K1).
//!
//! The engine owns its configuration and the plug-ins of its last check and
//! borrows nothing for its lifetime (KC2): each [`Engine::check`] is lent the
//! term store, the assumptions and the [`Guard`], and answers with an owned
//! [`CheckOutcome`]. An engine is `Send` (KC7), so a worker may own one.

mod config;
mod outcome;
mod register;

use std::collections::BTreeMap;

use ay_core::{CnfLit, TermData, TermId, TermStore, TheoryLit, Tseitin, TseitinResult};
use ay_sat::{AssumeResult, Literal, SatResult, Solver, Variable};

pub use config::{EngineConfig, EnodeMode, Exhausted, Guard, SearchProfile};
pub use outcome::{CheckOutcome, EngineStats, RecordedStep, Refutation, Verdict};

use crate::atoms::AtomTable;
use crate::content::{scan, Scan};
use crate::hub::Hub;
use crate::internalize::{normalize, Normalized};
use crate::kernel::Kernel;
use crate::plugin::{Ctx, Effects, GiveUp, ThId, TheoryPlugin};
use register::{register, Registration};

/// A check encoded for its one search ([`Engine::encode_check`]).
struct Encoded {
    normalized: Normalized,
    scanned: Scan,
    cnf: TseitinResult,
    assumption_lits: Vec<Literal>,
    solver: Solver,
}

/// How the one search ended, under assumptions or not.
enum Ended {
    Sat(Vec<bool>),
    /// With the failed-assumption core (empty without assumptions).
    Unsat(Vec<Literal>),
    Unknown,
}

/// Asserted formulas plus the plug-ins that serve them.
pub struct Engine {
    cfg: EngineConfig,
    assertions: Vec<TermId>,
    plugins: Vec<Box<dyn TheoryPlugin>>,
    atoms: AtomTable,
    pub(crate) sat_model: Vec<bool>,
    /// The assertions the last check encoded, when internalization rewrote
    /// them (empty otherwise): the model check evaluates them too.
    pub(crate) internalized: Vec<TermId>,
    stats: EngineStats,
}

/// KC2 / KC7: an engine may move to another worker between checks.
const _: () = {
    const fn assert_send<T: Send>() {}
    assert_send::<Engine>();
};

impl Engine {
    /// An engine with this configuration and no assertions.
    #[must_use]
    pub fn new(cfg: EngineConfig) -> Self {
        Self {
            cfg,
            assertions: Vec::new(),
            plugins: Vec::new(),
            atoms: AtomTable::default(),
            sat_model: Vec::new(),
            internalized: Vec::new(),
            stats: EngineStats::default(),
        }
    }

    /// The configuration.
    #[must_use]
    pub const fn config(&self) -> &EngineConfig {
        &self.cfg
    }

    /// Change the configuration (design §3.3 `reconfigure`). Between checks
    /// is the only safe point: a check holds the engine mutably.
    pub fn reconfigure(&mut self, cfg: &EngineConfig) {
        self.cfg = cfg.clone();
    }

    /// The plug-ins of the last check, by name (for example `dl-int`, `lra`).
    pub fn plugin_names(&self) -> Vec<&'static str> {
        self.plugins.iter().map(|p| p.name()).collect()
    }

    /// Assert a Boolean term.
    pub fn assert(&mut self, term: TermId) {
        self.assertions.push(term);
    }

    /// Counters of the last check (also in its [`CheckOutcome`]).
    pub fn stats(&self) -> &EngineStats {
        &self.stats
    }

    /// The SAT value, in the last `sat` answer, of a Boolean term the encoding
    /// gave a variable (a theory atom or a piece of Boolean structure).
    pub fn atom_value(&self, atom: TermId) -> Option<bool> {
        let var = self.atoms.var_of(atom)?;
        self.sat_model.get(var as usize).copied()
    }

    /// The SAT assignment of the last `sat` answer, indexed by variable
    /// (empty after any other answer).
    pub fn sat_assignment(&self) -> &[bool] {
        &self.sat_model
    }

    /// Every term the last check gave a SAT variable, with its 0-based index
    /// into [`Self::sat_assignment`]: theory atoms, minted atoms and the
    /// Boolean structure of the encoding.
    pub fn encoded_terms(&self) -> impl Iterator<Item = (TermId, u32)> + '_ {
        self.atoms.bindings()
    }

    /// The value of a term in the last `sat` answer, as a value term interned
    /// in `terms` (the store the check ran on).
    pub fn model_value(&mut self, terms: &mut TermStore, term: TermId) -> Option<TermId> {
        let mut effects = Effects::default();
        for (idx, plugin) in self.plugins.iter_mut().enumerate() {
            let id = ThId::try_from(idx).ok()?;
            let mut ctx = Ctx::new(
                &mut *terms,
                None,
                &self.atoms,
                None,
                &mut effects,
                id,
                false,
            );
            if let Some(value) = plugin.model_value(&mut ctx, term) {
                return Some(value);
            }
        }
        None
    }

    /// Decide the conjunction of the assertions and `assumptions` with
    /// exactly one ay-sat search (K1), on the lent store `terms`, stopping
    /// when `guard` says so. An `unsat` answer under assumptions names the
    /// failed ones ([`CheckOutcome::failed`]).
    pub fn check(
        &mut self,
        terms: &mut TermStore,
        assumptions: &[TermId],
        guard: &Guard,
    ) -> CheckOutcome {
        self.stats = EngineStats::default();
        self.sat_model.clear();
        self.plugins.clear();
        self.atoms = AtomTable::default();
        let record = self.cfg.record_proofs && assumptions.is_empty();
        let Encoded {
            normalized,
            scanned,
            cnf,
            assumption_lits,
            mut solver,
        } = match self.encode_check(terms, assumptions, record) {
            Ok(encoded) => encoded,
            Err(give_up) => return CheckOutcome::unknown(give_up.reason, EngineStats::default()),
        };
        let registration = match register(terms, &cnf.term_to_var, &mut solver, &self.cfg, &scanned)
        {
            Ok(registration) => registration,
            Err(give_up) => return CheckOutcome::unknown(give_up.reason, EngineStats::default()),
        };
        let Registration {
            plugins,
            families,
            atoms,
            order,
            layout,
        } = registration;
        // KC24: no quantifier plug-in exists, so every check is Sparse.
        let mode = EnodeMode::for_check(false);
        let hub = match Hub::new(terms.true_term(), terms.false_term(), mode) {
            Ok(hub) => hub,
            Err(give_up) => return CheckOutcome::unknown(give_up.reason, EngineStats::default()),
        };
        let stop = || guard.should_stop();
        let mut kernel = Kernel::new(&mut *terms, plugins, families, atoms, hub, record);
        kernel.theory_branching = self.cfg.theory_branching;
        kernel.hub_relevancy = self.cfg.hub_relevancy;
        kernel.stop = Some(&stop);
        kernel.guard = Some(guard);
        kernel.define_ite_links(&scanned.arith_ites);
        let prepared = kernel
            .build_hub(&layout)
            .and_then(|()| kernel.internalize_in(&order))
            .and_then(|()| kernel.start_relevancy(&normalized.roots()));
        // Hub variables are frozen like atoms: inprocessing must not
        // eliminate a variable whose value the hub reads.
        for var in kernel.hub_vars() {
            solver.freeze(Variable::new(var));
        }
        let ended = match prepared {
            Ok(()) => {
                kernel.stats.solve_calls += 1;
                Some(search(&mut solver, &mut kernel, &assumption_lits, &stop))
            }
            Err(give_up) => {
                kernel.give_up = Some(give_up);
                None
            }
        };
        kernel.stats.sat_conflicts = solver.num_conflicts();
        kernel.stats.sat_decisions = solver.num_decisions();
        solver.report_work_to_ledger();
        kernel.stats.hub_merges = kernel.hub.merges;
        let steps = kernel.proof.take().unwrap_or_default();
        let sigma = std::mem::take(&mut kernel.sigma);
        let give_up = kernel.give_up.take();
        let final_sat = kernel.final_sat;
        self.stats = kernel.stats.clone();
        self.plugins = std::mem::take(&mut kernel.plugins);
        self.atoms = std::mem::take(&mut kernel.atoms);
        drop(kernel);
        let proof = record.then(|| Refutation {
            assertions: self.assertions.clone(),
            cnf: cnf.clauses,
            annotations: cnf.proof_annotations.unwrap_or_default(),
            trace: solver.take_clause_trace(),
            var_terms: self.atoms.var_terms(),
            steps,
        });
        let (verdict, reason, core) = self.conclude(ended, give_up, final_sat, guard);
        let mut outcome = CheckOutcome::unknown(String::new(), self.stats.clone());
        outcome.verdict = verdict;
        outcome.reason = reason;
        outcome.failed = failed_assumptions(assumptions, &assumption_lits, &core);
        outcome.proof = proof;
        outcome.sigma = sigma;
        outcome.level0_units = self.level0_units(&solver);
        outcome
    }

    /// The check's formulas internalized and encoded, and the solver of its
    /// one search loaded. Records the internalized formulas for the model
    /// check.
    fn encode_check(
        &mut self,
        terms: &mut TermStore,
        assumptions: &[TermId],
        record: bool,
    ) -> Result<Encoded, GiveUp> {
        self.internalized.clear();
        let (normalized, scanned) = prepare(terms, &self.assertions, assumptions, record)?;
        if normalized.changed {
            // A `sat` answer makes the assumptions true as well.
            self.internalized = normalized.roots();
        }
        let (cnf, assumption_lits) = encode(
            terms,
            &normalized.assertions,
            &normalized.assumptions,
            &scanned,
            record,
        );
        let mut solver = load_solver(&cnf, &assumption_lits, record, &self.cfg);
        // The arithmetic ites' link definitions name each condition: like an
        // atom's, its variable must survive inprocessing.
        for var in condition_vars(terms, &cnf.term_to_var, &scanned.arith_ites) {
            solver.freeze(var);
        }
        Ok(Encoded {
            normalized,
            scanned,
            cnf,
            assumption_lits,
            solver,
        })
    }

    /// The verdict, the unknown reason and the failed core, from how the
    /// search ended. Keeps the model of an accepted `sat`.
    fn conclude(
        &mut self,
        ended: Option<Ended>,
        give_up: Option<GiveUp>,
        final_sat: bool,
        guard: &Guard,
    ) -> (Verdict, Option<String>, Vec<Literal>) {
        match ended {
            Some(Ended::Unsat(core)) => (Verdict::Unsat, None, core),
            Some(Ended::Sat(model)) if give_up.is_none() && final_sat => {
                self.sat_model = model;
                (Verdict::Sat, None, Vec::new())
            }
            Some(Ended::Sat(_)) => {
                let reason = give_up.map_or_else(
                    || "sat without an accepting final check".to_string(),
                    |g| g.reason,
                );
                (Verdict::Unknown, Some(reason), Vec::new())
            }
            _ => {
                let stopped = guard.exhausted().map(|why| why.reason().to_string());
                let reason = match (give_up, stopped) {
                    (Some(g), _) => g.reason,
                    (None, Some(why)) => why,
                    (None, None) => "search stopped".to_string(),
                };
                (Verdict::Unknown, Some(reason), Vec::new())
            }
        }
    }

    /// The literals at decision level 0 when the search ended, over terms
    /// with a variable.
    fn level0_units(&self, solver: &Solver) -> Vec<TheoryLit> {
        let var_terms = self.atoms.var_terms();
        solver
            .trail()
            .iter()
            .filter(|lit| solver.var_level(lit.variable()) == Some(0))
            .filter_map(|lit| {
                let term = (*var_terms.get(lit.variable().index())?)?;
                Some(TheoryLit::new(term, lit.is_positive()))
            })
            .collect()
    }
}

/// Internalization (§3.3: distinct, n-ary `=`, and, when the hub has work,
/// term-level ite) and registration by content (H2: refuse what no plug-in
/// serves before the search, and find the uninterpreted applications, H1),
/// over the assumptions exactly as over the assertions: an application, an
/// `ite` or a `distinct` that only an assumption holds is the hub's too.
fn prepare(
    terms: &mut TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
    record: bool,
) -> Result<(Normalized, Scan), GiveUp> {
    let normalized = normalize(terms, assertions, assumptions)?;
    if record && (normalized.changed || normalized.hub) {
        // Fail closed: a refutation must be about the authored assertions,
        // and the hub's congruence steps are not in the recorded proof's
        // vocabulary yet.
        return Err(GiveUp::new(
            "proof recording covers neither the hub nor internalization rewrites yet",
        ));
    }
    let scanned = scan(terms, &normalized.roots())?;
    Ok((normalized, scanned))
}

/// The one search's solver, with the encoding's clauses and the
/// assumptions frozen.
fn load_solver(
    cnf: &TseitinResult,
    assumptions: &[Literal],
    record: bool,
    cfg: &EngineConfig,
) -> Solver {
    let mut solver = Solver::new(cnf.num_vars as usize);
    if record {
        // Before any clause: the trace's ids must cover the input too.
        solver.enable_clause_trace();
    }
    cfg.search.apply(&mut solver);
    for clause in &cnf.clauses {
        let lits: Vec<Literal> = clause.literals().iter().map(|&d| dimacs(d)).collect();
        let _ = solver.add_clause(lits);
    }
    for lit in assumptions {
        solver.freeze(lit.variable());
    }
    solver
}

/// The variables of the conditions of `ites` (through `not`).
fn condition_vars(
    terms: &TermStore,
    term_to_var: &BTreeMap<TermId, u32>,
    ites: &[TermId],
) -> Vec<Variable> {
    ites.iter()
        .filter_map(|&ite| {
            let TermData::Ite(mut term, _, _) = *terms.get(ite) else {
                return None;
            };
            while let TermData::Not(inner) = terms.get(term) {
                term = *inner;
            }
            let dimacs_var = term_to_var.get(&term)?;
            Some(Variable::new(dimacs_var.checked_sub(1)?))
        })
        .collect()
}

fn dimacs(d: CnfLit) -> Literal {
    let var = Variable::new(d.unsigned_abs().saturating_sub(1));
    if d > 0 {
        Literal::positive(var)
    } else {
        Literal::negative(var)
    }
}

/// The encoding: the assertions asserted, each assumption encoded (both
/// directions, so it may be assumed either way) but not asserted, and a
/// variable for every Boolean argument of an uninterpreted application (the
/// hub merges it with `true` or `false`) and for every condition of an
/// arithmetic `ite` (the arithmetic plug-in's link lemmas name it).
fn encode(
    terms: &TermStore,
    assertions: &[TermId],
    assumptions: &[TermId],
    scanned: &Scan,
    record: bool,
) -> (TseitinResult, Vec<Literal>) {
    let tseitin = if record {
        Tseitin::new_with_proofs(terms)
    } else {
        Tseitin::new(terms)
    };
    if assumptions.is_empty() && scanned.bool_args.is_empty() && scanned.arith_ites.is_empty() {
        return (tseitin.transform_all(assertions), Vec::new());
    }
    let mut tseitin = tseitin;
    for &assertion in assertions {
        tseitin.assert_term(assertion);
    }
    let conditions = scanned
        .arith_ites
        .iter()
        .filter_map(|&ite| match terms.get(ite) {
            TermData::Ite(c, _, _) => Some(*c),
            _ => None,
        });
    for term in scanned.bool_args.iter().copied().chain(conditions) {
        let _ = tseitin.encode(term, true);
    }
    let lits: Vec<CnfLit> = assumptions
        .iter()
        .map(|&a| tseitin.encode(a, true))
        .collect();
    (
        tseitin.into_assertion_result(),
        lits.into_iter().map(dimacs).collect(),
    )
}

/// The one search (K1): ay-sat's plain entry without assumptions, its
/// assumption entry (which keeps the failed core) with them.
fn search(
    solver: &mut Solver,
    kernel: &mut Kernel<'_>,
    assumptions: &[Literal],
    stop: &dyn Fn() -> bool,
) -> Ended {
    if assumptions.is_empty() {
        return match solver
            .solve_interruptible_with_extension(kernel, stop)
            .into_inner()
        {
            SatResult::Sat(model) => Ended::Sat(model),
            SatResult::Unsat(_) => Ended::Unsat(Vec::new()),
            _ => Ended::Unknown,
        };
    }
    match solver
        .solve_with_extension_and_assumptions_core(kernel, assumptions, Some(&stop))
        .into_inner()
    {
        AssumeResult::Sat(model) => Ended::Sat(model),
        AssumeResult::Unsat(core, _) => Ended::Unsat(core),
        _ => Ended::Unknown,
    }
}

/// The assumptions whose literal is in ay-sat's failed core, each once.
fn failed_assumptions(assumptions: &[TermId], lits: &[Literal], core: &[Literal]) -> Vec<TermId> {
    let mut failed = Vec::new();
    for (&term, lit) in assumptions.iter().zip(lits) {
        if core.contains(lit) && !failed.contains(&term) {
            failed.push(term);
        }
    }
    failed
}
