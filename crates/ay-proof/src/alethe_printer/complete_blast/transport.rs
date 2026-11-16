// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tseitin planning and refutation transport.
//!
//! The gate DAG's defining clauses are DERIVED with the ordinary Boolean
//! tautology rules, never assumed, and AY's own SAT engine is then re-run on
//! exactly that clause set. Its refutation is transported as a chain of
//! BINARY resolutions — one pivot per printed step, which is exactly the
//! inference the consumer replays — and every transported clause carries the
//! extra literal `(not A)`, so the chain ends at `(cl (not A))` instead of
//! `(cl)`. That extra literal IS the assumption, which is why the root unit
//! clause is never passed as a premise: wherever the chain would resolve it
//! away, the step is skipped and the literal stays.
//!
//! ## Why binary, and not the RUP hint list
//!
//! An LRAT step names the clauses whose unit propagation makes its conclusion
//! RUP. Printing that hint list as one n-ary `resolution` step is smaller, and
//! it is what this module did first — but a hint list is not always a chain
//! the consumer can reconstruct, and on the larger refutations the pinned
//! checker answered `checking failed on step 't1' with rule 'resolution':
//! rule validation failed` for a document AY had already disclosed as
//! hole-free. The hint chain is therefore EXPANDED here, by replaying the unit
//! propagation and reverse-resolving it, into the binary steps the consumer
//! validates. The document is then replayed once more from its own printed
//! text ([`super::selfcheck`]) before a byte of it is disclosed.

use super::circuit::{GateKind, SRef};
use super::lane::{self, Lane};
use super::resolvent::{drup_pays, Resolvent};
use super::sweep;
use super::{
    selfcheck, Blaster, ClauseEmit, PlannedClause, MAX_CHAIN_STEPS, MAX_COUNTED_TEXT_BYTES,
    MAX_DERIVED_CLAUSES, MAX_PLANNED_CLAUSES,
};
use crate::resolution_dag_memo::{resolution_dag_is_memoized_by, resolution_dag_memoized_by};
use crate::sat_sweep::split::Leaves;
use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_sat::resolution_dag::RupStep;
use ay_sat::Literal;
use ay_sat::ResolutionDag;
use std::fmt::Write as _;

#[cfg(test)]
mod monolithic_owner_tests;

/// A planned lemma as its document concludes: the CNF it refutes, the
/// assumed root unit, and the step that prints the lemma.
struct Target<'t> {
    cnf: &'t [Vec<Literal>],
    root_clause_id: u64,
    root: SRef,
    unit: &'t str,
    final_clause: &'t str,
}

/// A plan's CNF extended by its priority chains' shortcuts (`ite.rs`), and
/// the indices of the shortcut clauses, each implied by the rest.
struct Extension {
    clauses: Vec<Vec<Literal>>,
    implied: Vec<usize>,
}

/// What the direct lane did (`Blaster::directly`).
enum Directly {
    Printed(String),
    /// Its solve found a model of the planned CNF: the lemma is false, and
    /// the case split, the sweep and the monolithic search after it would
    /// only spend their envelopes to say so. Measured on a fuzzed 16-bit
    /// query whose authored root alone is satisfiable (4,783 gates), they
    /// did, at every ask of the wire-gap screen: 15.9 CPU-s against 0.03.
    Satisfiable,
    Declined,
}

/// What the case-split lane did (`Blaster::cases_document`).
enum CaseSplit {
    Printed(String),
    /// It reached a case `split::Leaves::Small` leaves to the sweep.
    Deferred,
    Declined,
}

/// A clause this document has already printed, and the step that concludes it.
struct PrintedClause {
    name: String,
    lits: Vec<Literal>,
    /// Whether this clause may be a premise of an `:args` step.
    ///
    /// Two separate disagreements between the consumer's two resolution paths
    /// make a clause unusable there, and both are decided by how it PRINTS.
    ///
    /// * NEGATION DEPTH. The argument-free path compares literals by
    ///   `remove_all_negations_with_polarity` (a PARITY), so `(not (not x))`
    ///   and `x` are one literal to it. The `:args` path compares them by
    ///   `remove_all_negations` (a COUNT) and negates by `n + 1`, so they are
    ///   DIFFERENT literals to it. The circuits deliberately print doubled
    ///   negations where the `bitblast_*` rules demand them (see
    ///   [`super::circuit`]).
    /// * REPEATED LITERALS. The `:args` path folds a premise in by skipping
    ///   only the FIRST occurrence of the pivot and inserting the rest, so a
    ///   clause printing the same literal twice leaves a copy behind that this
    ///   transport's resolvent does not carry. Measured, not supposed: this is
    ///   what the pinned checker rejected at `t1.cbbr2193` with `rule
    ///   validation failed`, on a document whose every other step it accepted.
    ///
    /// Either way the chain is still transportable on the parity path, so it
    /// falls back to binary rather than being refused outright.
    count_safe: bool,
}

/// One resolution of the transported chain, before it is printed.
///
/// `pivots` empty means a BINARY step printed without `:args`, which the
/// consumer checks on its parity path. A non-empty `pivots` means an n-ary
/// step carrying one explicit `(pivot, polarity)` per link, which the consumer
/// checks by replaying exactly those links — no hint list, nothing guessed.
struct ChainStep {
    name: String,
    lits: Vec<Literal>,
    premises: Vec<String>,
    /// `(gate, is_pivot_in_current)` per link, in premise order.
    pivots: Vec<(u32, bool)>,
    /// A `weakening` of its one premise rather than a resolution.
    weakening: bool,
    /// A `drup` step over its premises rather than a resolution
    /// (`resolvent.rs`, [`drup_pays`]).
    drup: bool,
}

/// Everything the expansion needs that is not the step being expanded.
struct ChainContext<'c> {
    /// The clause set the SAT engine saw, in LRAT id order (`id - 1`).
    cnf: &'c [Vec<Literal>],
    derived: &'c [RupStep],
    position: &'c DetHashMap<u64, usize>,
    original_count: u64,
    /// LRAT id of the assumed root unit clause. It is never a premise.
    root_clause_id: u64,
    /// The literal every transported clause carries: `(not A)`.
    root_negative: Literal,
}

impl ChainContext<'_> {
    /// The clause the SAT ENGINE saw for this id — never the printed one.
    /// Unit propagation has to be replayed over the clauses that made each
    /// hint unit, not over the clauses that carry the extra assumption
    /// literal.
    fn engine_clause(&self, id: u64) -> Option<&[Literal]> {
        if id == 0 {
            return None;
        }
        if id <= self.original_count {
            return self.cnf.get((id - 1) as usize).map(Vec::as_slice);
        }
        let index = *self.position.get(&id)?;
        Some(&self.derived.get(index)?.clause)
    }
}

impl Blaster<'_, '_> {
    /// Plan the defining clauses of every gate built since the last call,
    /// with the rule that derives each.
    pub(super) fn plan_structural_clauses(&mut self) -> Option<()> {
        self.printer.complete_blast_progress()?;
        let from = self.structured_gates;
        self.structured_gates = self.circuit.len() as u32;
        for gate in from..self.circuit.len() as u32 {
            self.printer.complete_blast_progress()?;
            let positive = SRef::pos(gate);
            let negative = positive.not()?;
            match self.circuit.kind(gate).clone() {
                // Free variables define nothing; theory atoms were linked to
                // their circuits when they were built.
                GateKind::Atom(_) | GateKind::Theory(_) => {}
                GateKind::Const(true) => {
                    let step = self.true_step();
                    self.plan(vec![positive], ClauseEmit::Existing(step))?;
                }
                GateKind::Const(false) => {
                    let step = self.false_step();
                    self.plan(vec![negative], ClauseEmit::Existing(step))?;
                }
                GateKind::And(args) => {
                    for (index, arg) in args.iter().enumerate() {
                        self.plan(
                            vec![negative, *arg],
                            ClauseEmit::rule("and_pos", Some(index.to_string()), Vec::new())?,
                        )?;
                    }
                    let mut lits = vec![positive];
                    for arg in &args {
                        lits.push(arg.not()?);
                    }
                    self.plan(lits, ClauseEmit::bare("and_neg")?)?;
                }
                GateKind::Or(args) => {
                    let mut lits = vec![negative];
                    lits.extend(args.iter().copied());
                    self.plan(lits, ClauseEmit::bare("or_pos")?)?;
                    for (index, arg) in args.iter().enumerate() {
                        self.plan(
                            vec![positive, arg.not()?],
                            ClauseEmit::rule("or_neg", Some(index.to_string()), Vec::new())?,
                        )?;
                    }
                }
                GateKind::Xor(a, b) => {
                    self.plan(vec![negative, a, b], ClauseEmit::bare("xor_pos1")?)?;
                    self.plan(
                        vec![negative, a.not()?, b.not()?],
                        ClauseEmit::bare("xor_pos2")?,
                    )?;
                    self.plan(vec![positive, a, b.not()?], ClauseEmit::bare("xor_neg1")?)?;
                    self.plan(vec![positive, a.not()?, b], ClauseEmit::bare("xor_neg2")?)?;
                }
                GateKind::Implies(a, b) => {
                    // Alethe's exact implication tautologies; never replace
                    // the printed source implication by an unproved `or`.
                    self.plan(
                        vec![negative, a.not()?, b],
                        ClauseEmit::bare("implies_pos")?,
                    )?;
                    self.plan(vec![positive, a], ClauseEmit::bare("implies_neg1")?)?;
                    self.plan(vec![positive, b.not()?], ClauseEmit::bare("implies_neg2")?)?;
                }
                GateKind::Iff(a, b) => {
                    self.plan(vec![negative, a, b.not()?], ClauseEmit::bare("equiv_pos1")?)?;
                    self.plan(vec![negative, a.not()?, b], ClauseEmit::bare("equiv_pos2")?)?;
                    self.plan(
                        vec![positive, a.not()?, b.not()?],
                        ClauseEmit::bare("equiv_neg1")?,
                    )?;
                    self.plan(vec![positive, a, b], ClauseEmit::bare("equiv_neg2")?)?;
                }
                GateKind::Ite(c, a, b) => {
                    self.plan(vec![negative, c, b], ClauseEmit::bare("ite_pos1")?)?;
                    self.plan(vec![negative, c.not()?, a], ClauseEmit::bare("ite_pos2")?)?;
                    self.plan(vec![positive, c, b.not()?], ClauseEmit::bare("ite_neg1")?)?;
                    self.plan(
                        vec![positive, c.not()?, a.not()?],
                        ClauseEmit::bare("ite_neg2")?,
                    )?;
                }
            }
        }
        self.printer.complete_blast_progress()
    }

    fn sat_literal(reference: SRef) -> Option<Literal> {
        let index = i32::try_from(reference.gate).ok()?.checked_add(1)?;
        Some(Literal::from_dimacs(if reference.negative() {
            -index
        } else {
            index
        }))
    }

    fn reference_of(literal: Literal) -> SRef {
        let dimacs = literal.to_dimacs();
        SRef {
            gate: dimacs.unsigned_abs() - 1,
            nots: u8::from(dimacs < 0),
        }
    }

    /// Plan every clause of the refutation and spell it for the SAT engine:
    /// the CNF, in LRAT id order, and the id of the assumed root unit.
    pub(super) fn planned_cnf(&mut self, root: SRef) -> Option<(Vec<Vec<Literal>>, u64)> {
        self.printer.complete_blast_progress()?;
        if self.flush_gate_definitions().is_none() || self.plan_structural_clauses().is_none() {
            debug_note(|| "the gate definitions or structural clauses could not be planned".into());
            return None;
        }
        let root_clause_id = self.planned.len() as u64 + 1;
        if self.plan(vec![root], ClauseEmit::Root).is_none() {
            debug_note(|| "the root clause could not be planned".into());
            return None;
        }
        if self.planned.len() > MAX_PLANNED_CLAUSES {
            debug_note(|| {
                format!(
                    "{} planned clauses exceed {MAX_PLANNED_CLAUSES}",
                    self.planned.len()
                )
            });
            return None;
        }

        let mut cnf: Vec<Vec<Literal>> = Vec::with_capacity(self.planned.len());
        for planned in &self.planned {
            self.printer.complete_blast_progress()?;
            let mut lits = Vec::with_capacity(planned.lits.len());
            for reference in &planned.lits {
                self.printer.complete_blast_progress()?;
                lits.push(Self::sat_literal(*reference)?);
            }
            cnf.push(lits);
        }
        self.printer.complete_blast_progress()?;
        Some((cnf, root_clause_id))
    }

    /// Run the refutation of a lemma already planned (`lazy.rs`: `cnf` and
    /// its assumed root unit `root_clause_id`) and print the whole document,
    /// or refuse. Step `unit` concludes `(cl (not root))`, PRINTED as the
    /// word-level `final_clause`: a unit lemma itself, or the negated
    /// conjunction that `clause` opens.
    ///
    /// A satisfiable bit-blasting means the lemma is FALSE. Nothing is
    /// printed: this is the gate that keeps a wrong theorem from ever
    /// reaching an accepted certificate.
    ///
    /// A small circuit keeps its monolithic refutation when that is light.
    /// Otherwise the circuit is SWEPT (`sweep`): a monolithic refutation of
    /// an arithmetic miter transports to text far past the budget.
    ///
    /// A large circuit first refutes its root DIRECTLY ([`Self::directly`]),
    /// then case by case ([`Self::cases_document`]), then by its sweep, and
    /// the first lane that prints wins. A lane that declined at an earlier
    /// render of this plan would only decline again (a failure is never
    /// memoized), so a later render goes straight to the lane that printed
    /// (`lane.rs`); a sweep the refutation memo retains printed too, or only
    /// its size refused it.
    ///
    /// A sweep that refutes the plan but whose document only its size
    /// refuses ends the plan (`size_refusal.rs`): neither the split over
    /// every leaf nor the monolithic search follows it, a deliberate
    /// departure from 5b5c1f454's "every lane is still tried".
    pub(super) fn finish_planned(
        &mut self,
        cnf: &[Vec<Literal>],
        root_clause_id: u64,
        root: SRef,
        unit: &str,
        final_clause: &str,
    ) -> Option<String> {
        self.printer.complete_blast_progress()?;
        let target = Target {
            cnf,
            root_clause_id,
            root,
            unit,
            final_clause,
        };
        // Every original-CNF lane and key keeps this count. Cases may append gates.
        let variables = self.circuit.len();
        let mut best: Option<String> = None;
        let small = variables < sweep::SWEEP_FIRST_GATES;
        let (plan, printed_by) = self.lane_hint(variables, cnf)?;
        if small {
            match self.monolithic_refutation_planned(variables, cnf) {
                Ok(dag) => best = self.print_refutation(&dag, &target),
                Err(true) => return None,
                Err(false) => {}
            }
            self.printer.complete_blast_progress()?;
            if best
                .as_ref()
                .is_some_and(|document| document.len() <= sweep::LIGHT_DOCUMENT_BYTES)
            {
                return best;
            }
        } else if printed_by.is_none() {
            match self.directly(variables, &target) {
                Directly::Printed(document) => return Some(document),
                // As a small circuit's model above: no later lane refutes it.
                Directly::Satisfiable => {
                    debug_note(|| "the direct refutation found a model: the lemma is false".into());
                    return None;
                }
                Directly::Declined => {}
            }
            self.printer.complete_blast_progress()?;
        }
        // Small leaves defer the SAME extended plan to the whole-circuit sweep.
        let mut deferred = None;
        if !small && printed_by != Some(Lane::Sweep) {
            let leaves = if printed_by == Some(Lane::Cases) {
                Leaves::All
            } else {
                Leaves::Small
            };
            let extension = self.case_split_cnf(cnf);
            self.printer.complete_blast_progress()?;
            let attempt = extension.as_ref().map_or(CaseSplit::Declined, |extension| {
                self.cases_document(extension, &target, leaves)
            });
            self.printer.complete_blast_progress()?;
            match attempt {
                CaseSplit::Printed(document) => {
                    return self.remember_lane_document(plan, Lane::Cases, document);
                }
                CaseSplit::Deferred => deferred = extension,
                CaseSplit::Declined => {}
            }
        }
        self.printer.complete_blast_progress()?;
        let swept = self.retained_refutation(variables, cnf, root_clause_id);
        self.printer.complete_blast_progress()?;
        match swept.and_then(|dag| self.print_swept(&dag, &target)) {
            Some(document) if best.as_ref().is_none_or(|kept| document.len() < kept.len()) => {
                return self.remember_lane_document(plan, Lane::Sweep, document);
            }
            Some(_) => {}
            None => debug_note(|| "the swept refutation did not print".to_string()),
        }
        self.printer.complete_blast_progress()?;
        if self.swept_refused_by_size {
            return best;
        }
        if let Some(extension) = deferred {
            if let CaseSplit::Printed(document) =
                self.cases_document(&extension, &target, Leaves::All)
            {
                return self.remember_lane_document(plan, Lane::Cases, document);
            }
            self.printer.complete_blast_progress()?;
        }
        if best.is_none() && !small {
            best = self.print_refutation(
                &self.monolithic_refutation_planned(variables, cnf).ok()?,
                &target,
            );
        }
        self.printer.complete_blast_progress()?;
        best
    }

    fn lane_hint(
        &self,
        variables: usize,
        cnf: &[Vec<Literal>],
    ) -> Option<(Option<lane::Plan>, Option<Lane>)> {
        self.printer.complete_blast_progress()?;
        let plan = (variables >= sweep::SWEEP_FIRST_GATES).then(|| lane::Plan::of(variables, cnf));
        self.printer.complete_blast_progress()?;
        let mut printed_by = plan.as_ref().and_then(lane::printed_by);
        self.printer.complete_blast_progress()?;
        if printed_by.is_none() && plan.is_some() && self.has_retained_sweep(variables, cnf)? {
            printed_by = Some(Lane::Sweep);
        }
        Some((plan, printed_by))
    }

    fn remember_lane_document(
        &self,
        plan: Option<lane::Plan>,
        lane: Lane,
        document: String,
    ) -> Option<String> {
        self.printer.complete_blast_progress()?;
        lane::remember(plan, lane);
        self.printer.complete_blast_progress()?;
        Some(document)
    }

    /// `dag`, a refutation of the planned CNF, printed within the counted
    /// text bound.
    fn print_refutation(&self, dag: &ResolutionDag, target: &Target<'_>) -> Option<String> {
        self.transport_document(
            dag,
            target.cnf,
            target.root_clause_id,
            target.root,
            target.unit,
            target.final_clause,
            MAX_COUNTED_TEXT_BYTES,
        )
    }

    /// The DIRECT lane: the root refuted within one candidate lemma's
    /// conflict allowance (`sweep::refute_directly_planned`), kept only when its
    /// document prints within `sweep::DIRECT_DOCUMENT_BYTES` — it is for a
    /// root that refutes CHEAPLY.
    ///
    /// It runs before the case split and the sweep: a sweep can spend its
    /// whole wall, and a refused sweep is paid again at every render, so it
    /// runs only for a root that needs lemmas or does not print without
    /// them. Measured: external-codegen's `(a / b) ^ c` against its
    /// divide-by-zero-guarded lowering blasts one shared 32-bit divider
    /// (17,531 gates) whose root refutes in 129 conflicts and prints 1.7 MB;
    /// swept first, every render spent the 120 s wall on divider candidates,
    /// and the query answered `unknown` at external-codegen's 120 s budget.
    fn directly(&self, variables: usize, target: &Target<'_>) -> Directly {
        if self.printer.complete_blast_progress().is_none() {
            return Directly::Declined;
        }
        let satisfiable = std::cell::Cell::new(false);
        let dag = resolution_dag_memoized_by(variables, target.cnf, "direct", || {
            let outcome = sweep::refute_directly_planned(
                self.printer,
                &self.circuit,
                variables,
                &self.guarded_ites,
                target.cnf,
                target.root_clause_id,
            );
            self.printer.complete_blast_progress()?;
            match outcome {
                crate::sat_sweep::Direct::Refuted(dag) => Some(dag),
                crate::sat_sweep::Direct::Satisfiable => {
                    satisfiable.set(true);
                    None
                }
                crate::sat_sweep::Direct::Undecided => None,
            }
        });
        if self.printer.complete_blast_progress().is_none() {
            return Directly::Declined;
        }
        let Some(dag) = dag else {
            return if satisfiable.get() {
                Directly::Satisfiable
            } else {
                Directly::Declined
            };
        };
        self.transport_document(
            &dag,
            target.cnf,
            target.root_clause_id,
            target.root,
            target.unit,
            target.final_clause,
            sweep::DIRECT_DOCUMENT_BYTES,
        )
        .map_or(Directly::Declined, Directly::Printed)
    }

    /// The sweep of `cnf` over the `variables` gates it is planned over,
    /// retained on this thread under that count (`sweep::refute`).
    ///
    /// Keyed on the circuit's length when asked, the retained sweep never
    /// spared a render anything when a case split had run: its chain
    /// shortcuts mint gates after the plan, so the sweep was stored under the
    /// longer circuit and looked up, at the next render, under the planned
    /// one. Measured 2026-10-01 on external-codegen's 64-bit `IDIV` row 1373 (load
    /// average 100 to 147 on 18 cores): every render of the `b = -1` case
    /// paid its direct attempt (1.8 s) and its case split (15 s) again, then
    /// found its sweep retained (0.03 s), and the query ran past its 120 s
    /// budget in 124 s; keyed on the plan, the renders after the first take
    /// 2 s each, and the query answers in 46 s.
    fn has_retained_sweep(&self, variables: usize, cnf: &[Vec<Literal>]) -> Option<bool> {
        self.printer.complete_blast_progress()?;
        let retained = resolution_dag_is_memoized_by(variables, cnf, "sweep");
        self.printer.complete_blast_progress()?;
        Some(retained)
    }

    // All original-CNF strategies share the planned count, not the length
    // after the extended case-split plan. Retained certificates confer no
    // permission to bypass this attempt's original sticky owner.
    fn retained_refutation(
        &self,
        variables: usize,
        cnf: &[Vec<Literal>],
        root_clause_id: u64,
    ) -> Option<ResolutionDag> {
        self.printer.complete_blast_progress()?;
        let result = resolution_dag_memoized_by(variables, cnf, "sweep", || {
            let result = sweep::refute_planned(
                self.printer,
                &self.circuit,
                variables,
                &self.guarded_ites,
                cnf,
                root_clause_id,
            );
            self.printer.complete_blast_progress()?;
            result
        });
        self.printer.complete_blast_progress()?;
        result
    }

    /// The document of a case split's refutation (`sweep::refute_by_cases`)
    /// of `cnf` extended by the chain shortcuts, over every case, or `None`.
    #[cfg(test)]
    pub(super) fn by_cases(
        &mut self,
        cnf: &[Vec<Literal>],
        root_clause_id: u64,
        root: SRef,
        unit: &str,
        final_clause: &str,
    ) -> Option<String> {
        let target = Target {
            cnf,
            root_clause_id,
            root,
            unit,
            final_clause,
        };
        self.printer.complete_blast_progress()?;
        let extension = self.case_split_cnf(cnf)?;
        let result = self.cases_document(&extension, &target, Leaves::All);
        self.printer.complete_blast_progress()?;
        match result {
            CaseSplit::Printed(document) => Some(document),
            CaseSplit::Deferred | CaseSplit::Declined => None,
        }
    }

    /// `cnf` extended by the priority chains' shortcuts (`ite.rs`), which
    /// this plans: one extension per plan, however many splits read it.
    fn case_split_cnf(&mut self, cnf: &[Vec<Literal>]) -> Option<Extension> {
        self.printer.complete_blast_progress()?;
        let implied = self.plan_chain_shortcuts()?;
        self.printer.complete_blast_progress()?;
        self.flush_gate_definitions()?;
        self.printer.complete_blast_progress()?;
        self.plan_structural_clauses()?;
        self.printer.complete_blast_progress()?;
        let mut clauses = cnf.to_vec();
        self.printer.complete_blast_progress()?;
        for planned in self.planned.get(cnf.len()..)? {
            self.printer.complete_blast_progress()?;
            let mut literals = Vec::with_capacity(planned.lits.len());
            for reference in &planned.lits {
                self.printer.complete_blast_progress()?;
                literals.push(Self::sat_literal(*reference)?);
            }
            clauses.push(literals);
        }
        self.printer.complete_blast_progress()?;
        Some(Extension { clauses, implied })
    }

    /// The CASE-SPLIT lane: the document of a refutation of `extension`
    /// case by case (`crate::sat_sweep::split`) over the guarded facts its
    /// root leaves open, refuting the cases `leaves` admits. It declines at
    /// once where no guard is open. Under [`Leaves::Small`] a case that keeps
    /// a large part of the circuit DEFERS it: the sweep of the whole runs
    /// first, and the split over every case only if that sweep does not
    /// print. A refutation is retained on this thread whatever the policy
    /// that found it: it refutes the CNF.
    fn cases_document(
        &self,
        extension: &Extension,
        target: &Target<'_>,
        leaves: Leaves,
    ) -> CaseSplit {
        if self.printer.complete_blast_progress().is_none() {
            return CaseSplit::Declined;
        }
        let deferred = std::cell::Cell::new(false);
        let clauses = &extension.clauses;
        let split = resolution_dag_memoized_by(self.circuit.len(), clauses, "cases", || {
            let split = sweep::refute_by_cases(
                self.printer,
                &self.circuit,
                clauses,
                target.root_clause_id,
                &self.ite_definitions,
                &extension.implied,
                leaves,
            );
            self.printer.complete_blast_progress()?;
            deferred.set(split.deferred);
            split.refutation
        });
        if self.printer.complete_blast_progress().is_none() {
            return CaseSplit::Declined;
        }
        let Some(split) = split else {
            return if deferred.get() {
                CaseSplit::Deferred
            } else {
                CaseSplit::Declined
            };
        };
        let document = self.transport_document(
            &split,
            clauses,
            target.root_clause_id,
            target.root,
            target.unit,
            target.final_clause,
            MAX_COUNTED_TEXT_BYTES,
        );
        if self.printer.complete_blast_progress().is_none() {
            return CaseSplit::Declined;
        }
        document.map_or(CaseSplit::Declined, CaseSplit::Printed)
    }

    /// The monolithic CDCL refutation of `cnf`; `Err(true)` when the CNF is
    /// satisfiable, i.e. the lemma is false.
    #[cfg(test)]
    fn monolithic_refutation(&self, cnf: &[Vec<Literal>]) -> Result<ResolutionDag, bool> {
        self.monolithic_refutation_planned(self.circuit.len(), cnf)
    }

    /// Print `dag`, a refutation of `cnf`, as the transported chain, or
    /// refuse.
    #[expect(
        clippy::too_many_arguments,
        reason = "the transported refutation schema and its independent budget stay explicit"
    )]
    pub(super) fn transport_document(
        &self,
        dag: &ResolutionDag,
        cnf: &[Vec<Literal>],
        root_clause_id: u64,
        root: SRef,
        unit: &str,
        final_clause: &str,
        budget: usize,
    ) -> Option<String> {
        // The clauses `dag` refutes are `cnf`, the planned clauses up to its
        // length: a case split plans more after it (`by_cases`), which a
        // DAG over `cnf` never cites.
        let original_count = cnf.len() as u64;
        // Keep only what the refutation actually uses. Unit propagation is
        // confluent, so dropping unused clauses cannot break a replay.
        let UsedSteps {
            position,
            original: used_original,
            derived: used_derived,
        } = used_by_refutation(dag, original_count)?;

        let identifier = self.id.to_string();
        let mut body = String::new();
        let mut printed = self.print_used_originals(cnf, &used_original, &mut body);

        let context = ChainContext {
            cnf,
            derived: &dag.derived,
            position: &position,
            original_count,
            root_clause_id,
            root_negative: Self::sat_literal(root.not()?)?,
        };
        let mut next = 0_u64;
        let mut emitted: Vec<ChainStep> = Vec::new();
        let mut marks = Vec::new();
        let mut final_logical: Option<String> = None;
        for step in &dag.derived {
            if !used_derived.contains(&step.id) {
                continue;
            }
            emitted.clear();
            // THE FINAL STEP PRINTS THE WORD-LEVEL CLAUSE, and that clause is
            // the one the consumer compares its computed resolvent against. If
            // any of its literals prints under more than one `not`, the two
            // readings part company exactly there: the chain derives the gate
            // literal at depth 0 or 1, while the printed lemma carries it at
            // depth 2, which the parity path calls the same literal and the
            // `:args` path calls a different one. Measured: `str.post.gpr.w4`
            // printed `(not (not (= …)))` for a resolvent the consumer computed
            // as `@ay_cbb_t1_0_g4379` at depth 0, and carcara answered
            // `checking failed on step 't1' with rule 'resolution'`. Keep that
            // step on the parity path it is actually checked by.
            let force_binary =
                step.id == dag.empty_clause_id && !printed_clause_is_shallow(final_clause);
            let Some(result) = expand_rup_step(
                &identifier,
                step,
                &context,
                &printed,
                &mut next,
                &mut emitted,
                force_binary,
                &mut marks,
                // The final step prints the word-level lemma as a resolution.
                step.id != dag.empty_clause_id,
            ) else {
                debug_note(|| format!("RUP step {} did not expand to a resolution chain", step.id));
                return None;
            };
            if next > MAX_CHAIN_STEPS {
                debug_note(|| format!("{next} chain steps exceed {MAX_CHAIN_STEPS}"));
                return None;
            }
            if step.id == dag.empty_clause_id {
                final_logical = Some(self.print_final_step(
                    &mut body,
                    &emitted,
                    &result.lits,
                    context.root_negative,
                    unit,
                    final_clause,
                )?);
            } else {
                for chain in &emitted {
                    Self::print_chain_step(&mut body, &self.circuit, chain);
                }
                printed.insert(step.id, result);
            }
            body_fits(&body, budget).or_else(|| self.refuse_by_size())?;
        }
        let Some(final_logical) = final_logical else {
            debug_note(|| "the refutation never reached the empty clause".into());
            return None;
        };

        self.assembled_document(&body, unit, &final_logical)
    }

    /// The last chain step, printed as the word-level `final_clause` under
    /// the lemma's own step name `unit`; returns the gate-level clause the
    /// replay compares it with.
    fn print_final_step(
        &self,
        body: &mut String,
        emitted: &[ChainStep],
        lits: &[Literal],
        root_negative: Literal,
        unit: &str,
        final_clause: &str,
    ) -> Option<String> {
        // The chain must land on the assumption literal itself: that clause IS
        // the theory lemma, and the last step is where it is spelled at the
        // word level.
        if lits != [root_negative] {
            debug_note(|| format!("the chain ends on {} literal(s), not the root", lits.len()));
            return None;
        }
        let (last, rest) = emitted.split_last()?;
        for chain in rest {
            Self::print_chain_step(body, &self.circuit, chain);
        }
        let premises = last.premises.join(" ");
        if last.pivots.is_empty() {
            let _ = writeln!(
                body,
                "(step {unit} {final_clause} :rule resolution :premises ({premises}))"
            );
        } else {
            let args = Self::pivot_args(&self.circuit, &last.pivots);
            let _ = writeln!(
                body,
                "(step {unit} {final_clause} :rule resolution :premises ({premises}) :args ({args}))"
            );
        }
        Some(Self::chain_clause_text(&self.circuit, &last.lits))
    }

    /// Definitions, steps and the transported chain as one document, disclosed
    /// only when AY replays it itself.
    fn assembled_document(&self, body: &str, unit: &str, final_logical: &str) -> Option<String> {
        self.printer.complete_blast_progress()?;
        let mut out = String::new();
        out.push_str(&self.definitions);
        out.push_str(&self.steps);
        out.push_str(body);
        self.printer.complete_blast_progress()?;
        if !size_refusal::consumer_takes(&out) {
            debug_note(|| format!("{} document bytes exceed the consumer's budget", out.len()));
            return self.refuse_by_size();
        }
        self.printer.complete_blast_progress()?;
        // NOTHING AY cannot replay itself is disclosed. A document that fails
        // here leaves the ordinary honest `hole` in place, which discloses
        // `unproved_steps=1` — the whole point: the disclosure can never be
        // stronger than the document.
        if !selfcheck::chain_replays(&out, unit, final_logical) {
            debug_note(|| "the printed chain failed AY's own replay".to_string());
            return None;
        }
        self.printer.complete_blast_progress()?;
        // The caller appends its own newline.
        while out.ends_with('\n') {
            out.pop();
        }
        Some(out)
    }

    /// Print every input clause the refutation uses, and index each by its
    /// LRAT id for the chain.
    fn print_used_originals(
        &self,
        cnf: &[Vec<Literal>],
        used_original: &DetHashSet<u64>,
        body: &mut String,
    ) -> DetHashMap<u64, PrintedClause> {
        let identifier = self.id.to_string();
        let mut printed: DetHashMap<u64, PrintedClause> = DetHashMap::default();
        for (index, planned) in self.planned.iter().enumerate().take(cnf.len()) {
            let id = index as u64 + 1;
            if !used_original.contains(&id) {
                continue;
            }
            Self::print_planned(body, &self.circuit, &identifier, index, planned);
            // The root is carried as a literal rather than as a premise, so it
            // gets no name and can never be resolved against.
            if let Some(name) = self.original_clause_name(index) {
                // A clause the `:args` path would misread is re-spelled once
                // (`normalize`), so its chains need not fall back to binary.
                // A count-safe clause records its literals in PRINTED order:
                // a `weakening` of it must repeat them as its prefix.
                let clause = if transport_safe(&planned.lits) {
                    PrintedClause {
                        name,
                        lits: cnf[index].clone(),
                        count_safe: true,
                    }
                } else {
                    let normalized =
                        self.print_normalized_premise(body, &name, index, &planned.lits);
                    match normalized.and_then(|(normalized, spelling)| {
                        let lits = spelling
                            .iter()
                            .map(|reference| Self::sat_literal(*reference))
                            .collect::<Option<Vec<_>>>()?;
                        Some((normalized, lits))
                    }) {
                        Some((normalized, lits)) => PrintedClause {
                            name: normalized,
                            lits,
                            count_safe: true,
                        },
                        None => PrintedClause {
                            name,
                            lits: cnf[index].clone(),
                            count_safe: false,
                        },
                    }
                };
                printed.insert(id, clause);
            }
        }
        printed
    }

    /// The step name an input clause is concluded by, or `None` for the
    /// assumed root.
    fn original_clause_name(&self, index: usize) -> Option<String> {
        match &self.planned.get(index)?.emit {
            ClauseEmit::Rule { .. } => Some(format!("{}.cbbc{index}", self.id)),
            ClauseEmit::Existing(step) => Some(step.clone()),
            ClauseEmit::Root => None,
        }
    }

    fn chain_clause_text(circuit: &super::Circuit, lits: &[Literal]) -> String {
        if lits.is_empty() {
            return "(cl)".to_string();
        }
        let mut out = String::from("(cl");
        for literal in lits {
            out.push(' ');
            out.push_str(&circuit.text(Self::reference_of(*literal)));
        }
        out.push(')');
        out
    }

    /// The `:args` payload of an n-ary step: one `(pivot, polarity)` per link.
    ///
    /// The pivot is printed BARE — the gate's own reference, under no `not`.
    /// The consumer negates a pivot by ADDING a `not` (`n + 1`), never by
    /// flipping a parity, so the argument has to name the shallower half of
    /// the complementary pair; the polarity flag then says which side that
    /// half is on.
    fn pivot_args(circuit: &super::Circuit, pivots: &[(u32, bool)]) -> String {
        let mut out = String::new();
        for (gate, in_current) in pivots {
            if !out.is_empty() {
                out.push(' ');
            }
            out.push_str(&circuit.reference(*gate));
            out.push(' ');
            out.push_str(if *in_current { "true" } else { "false" });
        }
        out
    }

    fn print_chain_step(out: &mut String, circuit: &super::Circuit, step: &ChainStep) {
        let clause = Self::chain_clause_text(circuit, &step.lits);
        let premises = step.premises.join(" ");
        if step.weakening {
            let _ = writeln!(
                out,
                "(step {} {clause} :rule weakening :premises ({premises}))",
                step.name
            );
            return;
        }
        if step.drup {
            let _ = writeln!(
                out,
                "(step {} {clause} :rule drup :premises ({premises}) :args ({clause}))",
                step.name
            );
            return;
        }
        if step.pivots.is_empty() {
            let _ = writeln!(
                out,
                "(step {} {clause} :rule resolution :premises ({premises}))",
                step.name
            );
            return;
        }
        let args = Self::pivot_args(circuit, &step.pivots);
        let _ = writeln!(
            out,
            "(step {} {clause} :rule resolution :premises ({premises}) :args ({args}))",
            step.name
        );
    }

    fn print_planned(
        out: &mut String,
        circuit: &super::Circuit,
        id: &str,
        index: usize,
        planned: &PlannedClause,
    ) {
        let ClauseEmit::Rule {
            rule,
            args,
            premises,
        } = &planned.emit
        else {
            // `Existing` clauses are already in the document, and the root is
            // carried as a literal rather than as a premise.
            return;
        };
        let mut clause = String::from("(cl");
        for reference in &planned.lits {
            clause.push(' ');
            clause.push_str(&circuit.text(*reference));
        }
        clause.push(')');
        let arguments = args
            .as_ref()
            .map(|a| format!(" :args ({a})"))
            .unwrap_or_default();
        let antecedents = if premises.is_empty() {
            String::new()
        } else {
            format!(" :premises ({})", premises.join(" "))
        };
        let _ = writeln!(
            out,
            "(step {id}.cbbc{index} {clause} :rule {rule}{antecedents}{arguments})"
        );
    }
}

/// Expand one RUP step into the BINARY resolutions that derive it.
///
/// Phase 1 replays the hint chain over the clauses the SAT engine saw, which
/// is what makes each hint unit and identifies the literal it propagates.
/// Phase 2 walks the used hints backwards from the conflicting clause over the
/// clauses this document PRINTS, resolving one pivot per step. The two phases
/// read different clause sets on purpose: propagation is a fact about the
/// solved formula, while the printed clauses carry the assumption literal.
#[expect(
    clippy::too_many_arguments,
    reason = "the RUP expansion schema keeps source, output, marks, and policy explicit"
)]
fn expand_rup_step(
    id: &str,
    step: &RupStep,
    context: &ChainContext<'_>,
    printed: &DetHashMap<u64, PrintedClause>,
    next: &mut u64,
    emitted: &mut Vec<ChainStep>,
    force_binary: bool,
    marks: &mut Vec<u8>,
    drup_ok: bool,
) -> Option<PrintedClause> {
    let hints = &step.rup_hints;
    // ── 1. Replay the hint chain. ───────────────────────────────────────────
    let mut assign: DetHashMap<u32, bool> = DetHashMap::default();
    for literal in &step.clause {
        // The step's own clause is assumed FALSE, one literal at a time.
        assign.insert(variable_of(*literal), !literal.is_positive());
    }
    let mut units: Vec<Option<Literal>> = Vec::with_capacity(hints.len());
    let mut conflict_at = None;
    for (index, hint) in hints.iter().enumerate() {
        let clause = context.engine_clause(*hint)?;
        // A clause is scored by its DISTINCT unassigned literals. The
        // structural clauses of a gate whose two operands are the same
        // reference — every self-equality lemma has them — repeat a literal
        // (`(cl g (not x) (not x))`, unit on `(not x)`) or carry both
        // polarities (`(cl (not g) x (not x))`, true under every assignment).
        // Counting occurrences instead of literals scores the first as
        // non-unit and refuses a refutation that is perfectly well formed.
        let mut satisfied = false;
        let mut candidate: Option<Literal> = None;
        let mut several = false;
        for literal in clause {
            match assign.get(&variable_of(*literal)) {
                Some(value) => {
                    if *value == literal.is_positive() {
                        satisfied = true;
                        break;
                    }
                }
                None => match candidate {
                    None => candidate = Some(*literal),
                    Some(existing) if existing == *literal => {}
                    Some(existing) if existing == literal.negated() => {
                        // A tautology is true however the chain assigns: it
                        // propagates nothing and can never be the conflict.
                        satisfied = true;
                        break;
                    }
                    Some(_) => several = true,
                },
            }
        }
        if satisfied {
            // An already-true hint propagates nothing and resolves nothing.
            units.push(None);
            continue;
        }
        // A hint that is neither unit nor conflicting is not a clean unit
        // chain, and this expansion refuses to guess at one.
        if several {
            return None;
        }
        match candidate {
            None => {
                units.push(None);
                conflict_at = Some(index);
                break;
            }
            Some(unit) => {
                assign.insert(variable_of(unit), unit.is_positive());
                units.push(Some(unit));
            }
        }
    }
    let conflict = conflict_at?;
    let conflict_hint = hints[conflict];
    if conflict_hint == context.root_clause_id {
        return None;
    }
    let start = printed.get(&conflict_hint)?;
    let mut running = Resolvent::new(&start.lits, marks);

    // ── 2. Reverse-resolve, one LINK per pivot. ─────────────────────────────
    // Every link is collected BEFORE anything is printed, because the shape
    // the chain is printed in depends on all of them at once: one n-ary step
    // carrying an explicit pivot per link when every premise is count-safe,
    // and the binary chain otherwise. The resolution performed is identical
    // either way — only the number of intermediate clauses PRINTED differs.
    let mut premises: Vec<String> = vec![start.name.clone()];
    let mut pivots: Vec<(u32, bool)> = Vec::new();
    let mut resolvents: Vec<Vec<Literal>> = Vec::new();
    let mut count_safe = start.count_safe;
    for index in (0..conflict).rev() {
        let Some(unit) = units[index] else {
            continue;
        };
        if !running.contains(unit.negated()) {
            continue;
        }
        let hint = hints[index];
        if hint == context.root_clause_id {
            // Resolving the assumption's own unit clause away is exactly what
            // this document must not do. The literal stays, and it is the
            // `(not A)` every transported clause carries.
            continue;
        }
        let premise = printed.get(&hint)?;
        running.resolve(&premise.lits, unit)?;
        // `lits` holds `unit.negated()` and the premise holds `unit`, so the
        // shallower half of the complementary pair is whichever of the two is
        // POSITIVE; the flag records whether that half is the one in `lits`.
        pivots.push((variable_of(unit), !unit.is_positive()));
        premises.push(premise.name.clone());
        resolvents.push(running.lits().to_vec());
        count_safe &= premise.count_safe;
    }
    let lits = running.finish();

    let linked = !resolvents.is_empty();
    let name = if !linked {
        start.name.clone()
    } else if !force_binary && (count_safe || (drup_ok && drup_pays(pivots.len(), lits.len()))) {
        // One n-ary step. The consumer replays exactly these pivots in this
        // order, so nothing about the chain is left for it to search for — or,
        // when that is smaller or the premises are not count-safe, one `drup`
        // step, which the consumer replays by unit propagation over the
        // premises by parity, exactly as this chain was derived.
        *next = next.checked_add(1)?;
        let name = format!("{id}.cbbr{next}");
        let drup = drup_ok && drup_pays(pivots.len(), lits.len());
        emitted.push(ChainStep {
            name: name.clone(),
            lits: lits.clone(),
            premises,
            pivots: if drup { Vec::new() } else { pivots },
            weakening: false,
            drup,
        });
        name
    } else {
        // A premise prints a literal under more than one `not`, which only the
        // consumer's parity path treats as this chain does. Print the binary
        // steps that path replays instead of an `:args` step it would read
        // differently.
        let mut current = start.name.clone();
        for (link, resolved) in resolvents.into_iter().enumerate() {
            *next = next.checked_add(1)?;
            let step_name = format!("{id}.cbbr{next}");
            emitted.push(ChainStep {
                name: step_name.clone(),
                lits: resolved,
                premises: vec![current, premises.get(link + 1)?.clone()],
                pivots: Vec::new(),
                weakening: false,
                drup: false,
            });
            current = step_name;
        }
        current
    };

    // The chain must land on the derived clause, or on it plus the carried
    // assumption literal — nothing else is transported. A chain that lands on
    // a STRICT SUBSET of it (the engine derived a weakening: a hint alone is
    // already conflicting, and the step adds literals it does not need) is
    // weakened to it by the consumer's `weakening` rule, which demands the
    // premise's printed literals, in order, as the conclusion's prefix. That
    // spelling is known only for a count-safe clause, which prints exactly
    // `chain_clause_text` of its literals.
    let mut carried = step.clause.clone();
    carried.push(context.root_negative);
    if same_clause(&lits, &step.clause) || same_clause(&lits, &carried) {
        return Some(PrintedClause {
            name,
            lits,
            // A step this function printed spells its clause through
            // `reference_of`, which never emits more than one `not`. When no
            // step was printed the clause IS the conflicting premise, so it
            // inherits that premise's answer rather than claiming a stronger
            // one.
            count_safe: if linked { true } else { start.count_safe },
        });
    }
    let target = if lits.contains(&context.root_negative) {
        &carried
    } else {
        &step.clause
    };
    if force_binary
        || !(linked || start.count_safe)
        || !lits.iter().all(|literal| target.contains(literal))
    {
        return None;
    }
    weaken(id, name, lits, target, next, emitted)
}

/// Extend the printed clause `name` (spelling `lits`) to `target` with ONE
/// `weakening` step: `lits`, in order, then each literal of `target` it
/// lacks. The consumer's rule demands exactly that prefix.
fn weaken(
    id: &str,
    name: String,
    lits: Vec<Literal>,
    target: &[Literal],
    next: &mut u64,
    emitted: &mut Vec<ChainStep>,
) -> Option<PrintedClause> {
    let mut weakened = lits;
    for literal in target {
        if !weakened.contains(literal) {
            weakened.push(*literal);
        }
    }
    *next = next.checked_add(1)?;
    let weakened_name = format!("{id}.cbbr{next}");
    emitted.push(ChainStep {
        name: weakened_name.clone(),
        lits: weakened.clone(),
        premises: vec![name],
        pivots: Vec::new(),
        weakening: true,
        drup: false,
    });
    Some(PrintedClause {
        name: weakened_name,
        lits: weakened,
        count_safe: true,
    })
}

/// What a refutation's empty clause depends on.
struct UsedSteps {
    /// Index in `dag.derived` of every derived step id.
    position: DetHashMap<u64, usize>,
    /// Original clause ids used.
    original: DetHashSet<u64>,
    /// Derived clause ids used.
    derived: DetHashSet<u64>,
}

/// The steps the empty clause of `dag` depends on; `None` past the
/// derived-clause budget.
fn used_by_refutation(dag: &ResolutionDag, original_count: u64) -> Option<UsedSteps> {
    if dag.derived.len() > MAX_DERIVED_CLAUSES {
        debug_note(|| {
            format!(
                "{} derived clauses exceed {MAX_DERIVED_CLAUSES}",
                dag.derived.len()
            )
        });
        return None;
    }
    let position: DetHashMap<u64, usize> = dag
        .derived
        .iter()
        .enumerate()
        .map(|(index, step)| (step.id, index))
        .collect();
    let mut used_original: DetHashSet<u64> = DetHashSet::default();
    let mut used_derived: DetHashSet<u64> = DetHashSet::default();
    let mut queue = vec![dag.empty_clause_id];
    while let Some(id) = queue.pop() {
        if id <= original_count {
            used_original.insert(id);
            continue;
        }
        if !used_derived.insert(id) {
            continue;
        }
        let index = *position.get(&id)?;
        queue.extend(dag.derived.get(index)?.rup_hints.iter().copied());
    }
    Some(UsedSteps {
        position,
        original: used_original,
        derived: used_derived,
    })
}

/// `Some` while the proof body is within `budget`: the counted text bound
/// ([`MAX_COUNTED_TEXT_BYTES`]), or the direct lane's tighter
/// `sweep::DIRECT_DOCUMENT_BYTES`.
fn body_fits(body: &str, budget: usize) -> Option<()> {
    if body.len() > budget {
        let bytes = body.len();
        debug_note(|| format!("{bytes} proof-body bytes exceed {budget}"));
        return None;
    }
    Some(())
}

/// Whether every literal of an already-PRINTED clause sits under at most one
/// `not`.
///
/// This reads the emitted text rather than the circuit, because the clause it
/// judges — the word-level theory lemma — is built by the printer, not by the
/// gate DAG, and it is the text the consumer compares against.
fn printed_clause_is_shallow(clause_text: &str) -> bool {
    let Some(inner) = clause_text
        .strip_prefix("(cl")
        .and_then(|rest| rest.strip_suffix(')'))
    else {
        return false;
    };
    let Some(items) = selfcheck::tokens(inner) else {
        return false;
    };
    items.iter().all(|item| {
        let mut current = *item;
        let mut nots = 0_u32;
        while let Some(rest) = current.strip_prefix("(not ") {
            let Some(body) = rest.strip_suffix(')') else {
                break;
            };
            if selfcheck::tokens(body).is_none_or(|parts| parts.len() != 1) {
                break;
            }
            current = body;
            nots += 1;
        }
        nots <= 1
    })
}

/// Whether a planned clause PRINTS in a shape the consumer's `:args` path
/// reads the same way this transport does.
///
/// See [`PrintedClause::count_safe`] for the two disagreements this rules out:
/// a literal under more than one `not`, and a literal printed twice.
fn transport_safe(lits: &[SRef]) -> bool {
    let mut seen: DetHashSet<SRef> = DetHashSet::default();
    lits.iter()
        .all(|reference| reference.nots <= 1 && seen.insert(*reference))
}

/// The variable a literal stands on. `Variable`'s index is private, and the
/// raw encoding is the documented public inverse of it.
fn variable_of(literal: Literal) -> u32 {
    literal.raw() >> 1
}

fn same_clause(left: &[Literal], right: &[Literal]) -> bool {
    let left_set: DetHashSet<Literal> = left.iter().copied().collect();
    let right_set: DetHashSet<Literal> = right.iter().copied().collect();
    left_set == right_set
}

/// `--debug-cert` detail for why [`Blaster::finish`] declined.
fn debug_note(detail: impl FnOnce() -> String) {
    if ay_core::misc_cli_flags().debug_cert {
        ay_core::safe_eprintln!("c !! complete-blast finish declined: {}", detail());
    }
}

mod monolithic;
mod size_refusal;
#[cfg(test)]
#[path = "transport_tests.rs"]
mod tests;
