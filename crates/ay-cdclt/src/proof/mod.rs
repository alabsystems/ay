// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof recording at inference time (design D3, P1): one DAG-shared
//! `ay_core::Proof` for an `unsat` answer, assembled once, from what three
//! producers recorded while the one search ran.
//!
//! - **The encoding.** Tseitin annotates every input clause with the Alethe
//!   tautology rule that justifies it (`and_pos`, `or_neg`, `ite_pos1`, ...),
//!   and the unit clause of each assertion is that assertion's `assume`.
//! - **The kernel.** Every clause it hands ay-sat (a conflict, a lemma, an
//!   eager reason, a lazy reason when conflict analysis materializes it) is
//!   recorded with the plug-in's hint at that moment, together with the exact
//!   SAT literals (`RecordedStep`). A step carrying Farkas coefficients is an
//!   `la_generic` instance; the checker validates each kind independently.
//! - **ay-sat.** Its clause trace lists every clause it added or learned, and
//!   each learned clause's antecedent clause ids.
//!
//! Assembly joins them by clause identity. A traced input clause is the
//! encoding's clause of the same literals; a traced theory clause is the
//! kernel step of the same literals; a learned clause is derived from its
//! antecedents by unit propagation, which yields the resolution chain of that
//! derivation as one pivot-directed `resolution` step. Two cases need more
//! than the clause's own record, and both are still derivations, never
//! re-solving: ay-sat drops level-0-false literals from a theory clause
//! before tracing it (the traced clause then follows from the recorded one
//! and the level-0 units), and some learned clauses omit level-0 antecedents
//! from their hints (unit propagation then runs over every earlier clause).
//!
//! Every derived clause may be a subset of the traced one: a certificate may
//! use fewer literals than the clause it certifies, and a subset clause only
//! makes later unit propagation stronger.
//!
//! Only steps reachable from the empty clause are emitted.

mod clausify;
mod emit;
mod rup;
mod sources;

use std::collections::BTreeMap;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::{
    AletheRule, ClausificationProof, CnfClause, Proof, ProofId, ProofStep, TermId, TermStore,
};
use ay_sat::{ClauseTrace, ClauseTraceEntryRef, Literal};

use crate::engine::RecordedStep;
use emit::support;
use rup::{Derivation, Propagator};
use sources::{key, Sources};

/// An assembled refutation and what it is made of.
#[derive(Debug, Clone)]
pub struct KernelProof {
    /// The proof; its last step concludes the empty clause.
    pub proof: Proof,
    /// Counters over the emitted steps.
    pub stats: ProofStats,
}

/// Counters of one assembled proof (every figure counts emitted steps).
#[derive(Debug, Clone, Default, PartialEq, Eq)]
pub struct ProofStats {
    /// Steps in the proof.
    pub steps: u64,
    /// `assume` steps.
    pub assumes: u64,
    /// Clausification tautologies from the encoding.
    pub clausification: u64,
    /// Theory lemma steps, all kinds.
    pub theory_lemmas: u64,
    /// Theory lemma steps by `TheoryLemmaKind`.
    pub theory_kinds: BTreeMap<String, u64>,
    /// `resolution` steps.
    pub resolutions: u64,
    /// Steps no checker can validate: uncertified (`Generic`) lemmas and
    /// clauses nothing recorded justifies. 0 on a checkable proof.
    pub holes: u64,
    /// Of the holes, clauses nothing recorded justifies (the rest are
    /// uncertified theory lemmas).
    pub unjustified: u64,
    /// Entries in ay-sat's clause trace.
    pub trace_entries: u64,
    /// Learned clauses whose own antecedents derived them.
    pub derived_by_hints: u64,
    /// Clauses unit propagation derived only from every earlier clause (the
    /// antecedents were incomplete, or a traced theory clause lost literals).
    pub derived_by_search: u64,
}

/// Why no proof could be assembled.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofFailure {
    /// The check did not record (`EngineConfig::record_proofs` was off, or the check ran under assumptions).
    NotRecorded,
    /// ay-sat kept no clause trace.
    NoTrace,
    /// The trace dropped entries (memory budget or span accounting).
    TraceTruncated,
    /// ay-sat's search-time proof bookkeeping budget ran out.
    ProofWorkExhausted,
    /// The trace derives no empty clause (the answer was not `unsat`, or
    /// ay-sat declared it without a derivation).
    NoEmptyClause,
    /// A SAT variable in a needed clause names no term.
    UnnamedVariable(u32),
    /// The assembly's deadline passed.
    OutOfTime,
}

impl std::fmt::Display for ProofFailure {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::NotRecorded => write!(f, "recording was off"),
            Self::NoTrace => write!(f, "no clause trace"),
            Self::TraceTruncated => write!(f, "clause trace truncated"),
            Self::ProofWorkExhausted => write!(f, "proof bookkeeping budget exhausted"),
            Self::NoEmptyClause => write!(f, "trace derives no empty clause"),
            Self::UnnamedVariable(v) => write!(f, "SAT variable {v} names no term"),
            Self::OutOfTime => write!(f, "assembly deadline passed"),
        }
    }
}

/// Everything the assembler reads.
pub(crate) struct Inputs<'a> {
    pub(crate) terms: &'a mut TermStore,
    pub(crate) assertions: &'a [TermId],
    pub(crate) cnf: &'a [CnfClause],
    pub(crate) annotations: &'a [Option<ClausificationProof>],
    pub(crate) var_terms: &'a [Option<TermId>],
    pub(crate) records: &'a [RecordedStep],
    pub(crate) trace: &'a ClauseTrace,
    pub(crate) deadline: Option<std::time::Instant>,
}

/// How one node's clause is justified.
#[derive(Debug, Clone)]
enum Plan {
    /// The assertion's `assume`.
    Assume(TermId),
    /// A clausification tautology over its canonical clause.
    Tautology {
        rule: AletheRule,
        source: TermId,
        clause: Vec<TermId>,
    },
    /// The kernel step `records[i]`, reduced to its certificate's support.
    Theory(usize),
    /// Premise `j` of the derived hint of `records[i]`.
    Premise(usize, usize),
    /// Unit-propagation derivation over other nodes.
    Chain(Derivation),
    /// Nothing justifies it: a hole the checkers reject.
    Hole,
}

/// One clause of the proof DAG: a trace entry or a kernel record.
#[derive(Debug, Clone)]
struct Node {
    /// The clause this node's step concludes (sorted, deduplicated).
    lits: Vec<Literal>,
    plan: Plan,
    emitted: Option<ProofId>,
}

/// Each entry's antecedents as entry positions (a hint names a trace id, and
/// an id names the latest entry before the reader), and which entries the
/// empty clause at `empty` reaches through them.
fn antecedents(entries: &[ClauseTraceEntryRef<'_>], empty: usize) -> (Vec<Vec<usize>>, Vec<bool>) {
    let mut latest: HashMap<u64, usize> = HashMap::default();
    let mut hint_pos: Vec<Vec<usize>> = Vec::with_capacity(empty + 1);
    for (pos, entry) in entries.iter().enumerate().take(empty + 1) {
        hint_pos.push(
            entry
                .resolution_hints
                .iter()
                .filter_map(|id| latest.get(id).copied())
                .collect(),
        );
        latest.insert(entry.id, pos);
    }
    let mut needed = vec![false; empty + 1];
    needed[empty] = true;
    for pos in (0..=empty).rev() {
        if needed[pos] && !entries[pos].is_original {
            for &h in &hint_pos[pos] {
                needed[h] = true;
            }
        }
    }
    (hint_pos, needed)
}

/// Assemble the proof (see the module documentation).
///
/// The first pass derives only the learned clauses the refutation's recorded
/// antecedents reach. If a derivation then finds its antecedents incomplete
/// and nothing earlier supplies them, a second pass derives every learned
/// clause, so the widest fallback searches the whole clause history.
pub(crate) fn assemble(inputs: Inputs<'_>) -> Result<KernelProof, ProofFailure> {
    let Inputs {
        terms,
        assertions,
        cnf,
        annotations,
        var_terms,
        records,
        trace,
        deadline,
    } = inputs;
    if trace.is_truncated() {
        return Err(ProofFailure::TraceTruncated);
    }
    if trace.proof_work_exhausted() {
        return Err(ProofFailure::ProofWorkExhausted);
    }
    let entries: Vec<_> = trace.entries().iter().collect();
    let empty = entries
        .iter()
        .position(|e| e.clause.is_empty())
        .ok_or(ProofFailure::NoEmptyClause)?;
    let (hint_pos, needed) = antecedents(&entries, empty);
    let sources = Sources::new(assertions, cnf, annotations, records);
    let pass = |terms: &mut TermStore, needed: &[bool]| {
        let mut asm = Assembler {
            terms,
            var_terms,
            records,
            nodes: Vec::new(),
            units: Vec::new(),
            record_node: HashMap::default(),
            steps: Vec::new(),
            stats: ProofStats::default(),
            lit_terms: HashMap::default(),
            term_vars: HashMap::default(),
            extra_terms: Vec::new(),
            propagator: Propagator::default(),
            deadline,
            out_of_time: false,
        };
        asm.stats.trace_entries = trace.len() as u64;
        // One node per trace entry up to the empty clause (learned entries
        // only when needed), plus one per kernel record a node is made from.
        let mut node_of: Vec<Option<usize>> = vec![None; empty + 1];
        for pos in 0..=empty {
            let entry = entries[pos];
            let lits = key(entry.clause);
            let node = if entry.is_original {
                // An original no antecedent names still joins the pool the
                // widest fallback searches, when it is justified directly.
                match asm.original_node(&sources, lits, needed[pos]) {
                    Some(node) => node,
                    None => continue,
                }
            } else if !needed[pos] {
                continue;
            } else {
                let premises: Vec<usize> =
                    hint_pos[pos].iter().filter_map(|&h| node_of[h]).collect();
                asm.learned_node(lits, &premises)
            };
            node_of[pos] = Some(node);
        }
        if asm.out_of_time {
            return Err(ProofFailure::OutOfTime);
        }
        let root = node_of[empty].ok_or(ProofFailure::NoEmptyClause)?;
        asm.emit(root)?;
        asm.stats.steps = asm.steps.len() as u64;
        Ok::<_, ProofFailure>(KernelProof {
            proof: Proof::from_steps(asm.steps),
            stats: asm.stats,
        })
    };
    let first = pass(&mut *terms, &needed)?;
    if first.stats.unjustified == 0 {
        return Ok(first);
    }
    let second = pass(terms, &vec![true; empty + 1])?;
    Ok(if second.stats.unjustified < first.stats.unjustified {
        second
    } else {
        first
    })
}

struct Assembler<'a> {
    terms: &'a mut TermStore,
    var_terms: &'a [Option<TermId>],
    records: &'a [RecordedStep],
    nodes: Vec<Node>,
    /// Nodes whose clause is a unit (the level-0 facts), in creation order.
    units: Vec<usize>,
    /// Record index -> its node, once made.
    record_node: HashMap<usize, usize>,
    steps: Vec<ProofStep>,
    stats: ProofStats,
    lit_terms: HashMap<Literal, TermId>,
    /// Atom -> SAT variable, for premise atoms (built on first use).
    term_vars: HashMap<TermId, u32>,
    /// Atoms of hint premises that have no SAT variable: variable
    /// `var_terms.len() + i` names `extra_terms[i]`.
    extra_terms: Vec<TermId>,
    propagator: Propagator,
    deadline: Option<std::time::Instant>,
    /// The deadline passed: every later derivation declines at once.
    out_of_time: bool,
}

impl Assembler<'_> {
    fn push_node(&mut self, lits: Vec<Literal>, plan: Plan) -> usize {
        if lits.len() == 1 {
            self.units.push(self.nodes.len());
        }
        self.nodes.push(Node {
            lits,
            plan,
            emitted: None,
        });
        self.nodes.len() - 1
    }

    /// A node whose plan is a derivation: it concludes the derivation's result.
    fn push_chain(&mut self, d: Derivation) -> usize {
        let lits = d.result.clone();
        self.push_node(lits, Plan::Chain(d))
    }

    /// The node of kernel record `r`: its step concludes the literals its
    /// certificate uses (a Farkas certificate may leave some at 0). A record
    /// whose hint is derived from premises concludes what resolution from the
    /// premises derives.
    fn record_node(&mut self, r: usize) -> usize {
        if let Some(&n) = self.record_node.get(&r) {
            return n;
        }
        let records = self.records;
        let step = &records[r];
        let n = if step.hint.premises.is_empty() {
            let lits: Vec<Literal> = support(&step.clause, &step.hint)
                .filter_map(|p| step.sat_clause.get(p).copied())
                .collect();
            self.push_node(key(&lits), Plan::Theory(r))
        } else {
            let mut premises = Vec::with_capacity(step.hint.premises.len());
            for (j, premise) in step.hint.premises.iter().enumerate() {
                let lits: Vec<Literal> = support(&premise.clause, &premise.hint)
                    .filter_map(|p| premise.clause.get(p))
                    .map(|&lit| self.lit_of(lit))
                    .collect();
                premises.push(self.push_node(key(&lits), Plan::Premise(r, j)));
            }
            let target = key(&step.sat_clause);
            match self.derive(&target, &premises) {
                Some(d) => self.push_chain(d),
                None => self.push_node(target, Plan::Theory(r)),
            }
        };
        self.record_node.insert(r, n);
        n
    }

    /// A clause the solver added as given (not learned). A clause that is
    /// not `needed` gets a node only when something justifies it directly.
    fn original_node(
        &mut self,
        sources: &Sources<'_>,
        lits: Vec<Literal>,
        needed: bool,
    ) -> Option<usize> {
        if let Some(&idx) = sources.input.get(&lits) {
            if let Some(&assertion) = sources.roots.get(&idx) {
                if lits.len() == 1 && self.lit_term(lits[0]) == Some(assertion) {
                    return Some(self.push_node(lits, Plan::Assume(assertion)));
                }
            } else if let Some(Some(annotation)) = sources.cnf_annotations.get(idx) {
                if let Some(plan) = self.tautology_plan(annotation, &lits) {
                    return Some(self.push_node(lits, plan));
                }
            }
        }
        if let Some(&r) = sources.record.get(&lits) {
            return Some(self.record_node(r));
        }
        if !needed {
            return None;
        }
        Some(self.derived_original(sources, lits))
    }

    /// A needed original clause no record names exactly.
    fn derived_original(&mut self, sources: &Sources<'_>, lits: Vec<Literal>) -> usize {
        // A traced theory clause that lost level-0-false literals: derive it
        // from a recorded superset and the level-0 units, else every clause.
        let candidates = sources.supersets(&lits);
        if !candidates.is_empty() {
            let mut premises: Vec<usize> =
                candidates.iter().map(|&r| self.record_node(r)).collect();
            premises.extend(self.units.iter().copied());
            if let Some(d) = self.derive(&lits, &premises) {
                self.stats.derived_by_search += 1;
                return self.push_chain(d);
            }
            premises.extend(0..self.nodes.len());
            if let Some(d) = self.derive(&lits, &premises) {
                self.stats.derived_by_search += 1;
                return self.push_chain(d);
            }
        }
        self.push_node(lits, Plan::Hole)
    }

    /// A learned clause: from its antecedents, then with the level-0 units
    /// added, then from every earlier clause.
    fn learned_node(&mut self, lits: Vec<Literal>, premises: &[usize]) -> usize {
        if let Some(d) = self.derive(&lits, premises) {
            self.stats.derived_by_hints += 1;
            return self.push_chain(d);
        }
        let mut wider = premises.to_vec();
        wider.extend(self.units.iter().copied());
        if let Some(d) = self.derive(&lits, &wider) {
            self.stats.derived_by_search += 1;
            return self.push_chain(d);
        }
        let all: Vec<usize> = (0..self.nodes.len()).collect();
        if let Some(d) = self.derive(&lits, &all) {
            self.stats.derived_by_search += 1;
            return self.push_chain(d);
        }
        self.push_node(lits, Plan::Hole)
    }

    fn tautology_plan(
        &mut self,
        annotation: &ClausificationProof,
        lits: &[Literal],
    ) -> Option<Plan> {
        let traced: Vec<TermId> = lits
            .iter()
            .map(|&l| self.lit_term(l))
            .collect::<Option<_>>()?;
        let clause = clausify::canonical(
            self.terms,
            &annotation.rule,
            annotation.source_term,
            &traced,
        )?;
        Some(Plan::Tautology {
            rule: annotation.rule.clone(),
            source: annotation.source_term,
            clause,
        })
    }

    fn derive(&mut self, target: &[Literal], premises: &[usize]) -> Option<Derivation> {
        if self.out_of_time
            || self
                .deadline
                .is_some_and(|d| std::time::Instant::now() >= d)
        {
            self.out_of_time = true;
            return None;
        }
        let nodes = &self.nodes;
        self.propagator.derive(target, premises, |n| {
            nodes.get(n).map(|node| node.lits.as_slice())
        })
    }
}
