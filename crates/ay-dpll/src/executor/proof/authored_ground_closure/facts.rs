// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Boolean facts over the ground closure, and unit propagation over the
//! instance clauses `instances.rs` records.
//!
//! A fact is a literal (an atom or its negation) the candidate can prove as a
//! unit clause, recorded with the reason `emit_facts.rs` proves it. Unit
//! propagation over the instance clauses (every literal but one refuted by a
//! fact) yields new facts, and an equality fact merges its sides in the
//! closure. This is the Horn fragment of ground DPLL(T): no case
//! split is ever made, so every derived fact is forced.
//!
//! Well-foundedness mirrors the closure's: a fact records the edge count when
//! it was created and is explained only from those edges and from facts with
//! a smaller index, and a `Derived` edge names a fact created before it.

use ay_core::kani_compat::DetHashMap;

use super::instances::InstanceClause;
use super::*;

/// Facts one search may hold. A nested authored conjunction records one fact
/// per `and` level as well as one per leaf (each level is the premise of its
/// children's `and_pos` projection), so a query whose single root is a
/// right-nested conjunction of `n` leaves needs `2n` facts.
const MAX_FACTS: usize = 1_024;
/// Bit-vector predicates whose closed applications the recognizer decides.
const CLOSED_PREDICATES: &[&str] = &[
    "bvult", "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge",
];

/// Why a fact holds; see `emit_facts.rs` for the lemma each names.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(super) enum FactReason {
    /// The literal is an exact raw authored root.
    Root,
    /// The literal is conjunct `position` of the raw authored root `root`.
    Conjunct { root: TermId, position: u32 },
    /// The literal is conjunct `position` of the conjunction proved by the
    /// earlier fact `parent` (a nested authored `and`).
    SubConjunct { parent: usize, position: u32 },
    /// The body of an earlier false equality with Boolean `true` is false.
    NegatedTrueEquality { parent: usize },
    /// A disjunct of an earlier false disjunction is false.
    NegatedDisjunct { parent: usize, position: u32 },
    /// A closed bit-vector literal the recognizer proves.
    Closed,
    /// `(= s t)` with `s` and `t` merged.
    EqualityHolds,
    /// `(not (= s t))` with classes holding two different constants.
    EqualityRefuted,
    /// The same predicate over pairwise merged arguments holds (with the same
    /// polarity) by fact `source`.
    PredCongruent { source: usize },
    /// Instance clause `clause` with every other literal refuted by these facts.
    Propagated { clause: usize, refuting: Vec<usize> },
}

/// A proved literal.
#[derive(Clone, Debug)]
pub(super) struct Fact {
    pub(super) literal: TermId,
    pub(super) reason: FactReason,
    /// Closure edges recorded when the fact was created.
    pub(super) edge_limit: usize,
}

/// The facts and instance clauses of one search.
#[derive(Default)]
pub(super) struct FactBase {
    facts: Vec<Fact>,
    by_literal: DetHashMap<TermId, usize>,
    clauses: Vec<InstanceClause>,
    fired: Vec<bool>,
    /// Each fact is inspected once for forced negative Boolean projections.
    next_negative_boolean: usize,
    /// Search advice only: negative `bvult` facts may justify a modular miss.
    negative_bv_ranges: Vec<usize>,
}

impl FactBase {
    pub(super) fn facts(&self) -> &[Fact] {
        &self.facts
    }

    pub(super) fn clauses(&self) -> &[InstanceClause] {
        &self.clauses
    }

    pub(super) fn fact_for(&self, literal: TermId) -> Option<usize> {
        self.by_literal.get(&literal).copied()
    }

    pub(super) fn negative_bv_ranges(&self) -> &[usize] {
        &self.negative_bv_ranges
    }

    /// Record an instance clause, not yet fired.
    pub(super) fn push_clause(&mut self, clause: InstanceClause) {
        self.clauses.push(clause);
        self.fired.push(false);
    }

    /// Record a new fact; `None` when the literal is already a fact or the
    /// fact bound is reached.
    fn push(&mut self, literal: TermId, reason: FactReason, edge_limit: usize) -> Option<usize> {
        if self.by_literal.contains_key(&literal) || self.facts.len() >= MAX_FACTS {
            return None;
        }
        let index = self.facts.len();
        self.facts.push(Fact {
            literal,
            reason,
            edge_limit,
        });
        self.by_literal.insert(literal, index);
        Some(index)
    }
}

/// The closure together with the facts over it.
pub(super) struct GroundSearch {
    pub(super) closure: GroundClosure,
    pub(super) facts: FactBase,
    /// Recognizer calls left for proposing `Evaluated` edges and `Closed`
    /// facts; the recognizer is the only non-linear work a round can buy.
    pub(super) probes: usize,
    pub(super) read_chains: super::read_chain::ReadChainState,
    pub(super) packings: super::packing::PackingState,
}

impl Default for GroundSearch {
    fn default() -> Self {
        Self {
            closure: GroundClosure::default(),
            facts: FactBase::default(),
            probes: MAX_RECOGNIZER_PROBES,
            read_chains: super::read_chain::ReadChainState::default(),
            packings: super::packing::PackingState::default(),
        }
    }
}

/// The atom under at most one negation, and whether it is negated.
pub(super) fn literal_atom(terms: &TermStore, literal: TermId) -> (TermId, bool) {
    match terms.get(literal) {
        TermData::Not(inner) => (*inner, true),
        _ => (literal, false),
    }
}

/// The complementary literal: strips one negation or adds one.
pub(super) fn complement(terms: &mut TermStore, literal: TermId) -> TermId {
    match terms.get(literal) {
        TermData::Not(inner) => *inner,
        _ => terms.mk_not_raw(literal),
    }
}

impl Executor {
    /// Project only forced consequences of negative Boolean facts. In
    /// particular, a false conjunction is never split into guessed children.
    /// Every fact/argument visit shares the saturation allowance, and the
    /// cursor prevents repeated rounds from buying the same walk again.
    pub(super) fn expand_ground_negative_boolean_facts(
        &mut self,
        search: &mut GroundSearch,
        work: &mut SharedGroundWork,
    ) -> Option<()> {
        let stop = self.make_proof_assembly_should_stop();
        if stop() {
            return None;
        }
        while let Some(fact) = search.facts.facts.get(search.facts.next_negative_boolean) {
            work.spend(1)?;
            if stop() {
                return None;
            }
            let parent = search.facts.next_negative_boolean;
            let literal = fact.literal;
            search.facts.next_negative_boolean += 1;
            self.ctx.terms.entry_stamp(literal)?;
            if self.ctx.terms.sort(literal) != &Sort::Bool {
                return None;
            }
            let TermData::Not(inner) = self.ctx.terms.get(literal) else {
                continue;
            };
            let inner = *inner;
            self.ctx.terms.entry_stamp(inner)?;
            if self.ctx.terms.sort(inner) != &Sort::Bool {
                return None;
            }
            let TermData::App(Symbol::Named(head), arguments) = self.ctx.terms.get(inner) else {
                continue;
            };
            if head == "bvult" && arguments.len() == 2 {
                work.spend(2)?;
                search.facts.negative_bv_ranges.try_reserve(1).ok()?;
                search.facts.negative_bv_ranges.push(parent);
                continue;
            }
            if head == "=" && arguments.len() == 2 {
                work.spend(2)?;
                let left = arguments[0];
                let right = arguments[1];
                for term in [left, right] {
                    self.ctx.terms.entry_stamp(term)?;
                }
                if self.ctx.terms.sort(left) != &Sort::Bool
                    || self.ctx.terms.sort(right) != &Sort::Bool
                {
                    continue;
                }
                let truth = self.ctx.terms.true_term();
                let body = match (left == truth, right == truth) {
                    (true, false) => right,
                    (false, true) => left,
                    _ => continue,
                };
                // This search extension serves false disjunctions and
                // strict modular-range guards. Keep other existing goal and
                // geometry proof routes, rather than redirecting them through
                // a new complementary-fact conflict.
                work.spend(1)?;
                if !matches!(self.ctx.terms.get(body), TermData::App(Symbol::Named(head), args)
                    if (head == "or" && !args.is_empty()) || (head == "bvult" && args.len() == 2))
                {
                    continue;
                }
                let negative = self.ctx.terms.mk_not_raw(body);
                let _ = search.facts.push(
                    negative,
                    FactReason::NegatedTrueEquality { parent },
                    search.closure.edges().len(),
                );
                continue;
            }
            if head != "or" {
                continue;
            }
            work.spend(arguments.len())?;
            let mut children = Vec::new();
            children.try_reserve_exact(arguments.len()).ok()?;
            for &child in arguments {
                self.ctx.terms.entry_stamp(child)?;
                if self.ctx.terms.sort(child) != &Sort::Bool {
                    return None;
                }
                children.push(child);
            }
            for (position, child) in children.into_iter().enumerate() {
                if stop() {
                    return None;
                }
                let position = u32::try_from(position).ok()?;
                let negative = self.ctx.terms.mk_not_raw(child);
                let _ = search.facts.push(
                    negative,
                    FactReason::NegatedDisjunct { parent, position },
                    search.closure.edges().len(),
                );
            }
        }
        Some(())
    }

    /// Record every non-equality root, and every conjunct of an `and` root,
    /// as a fact; a conjunct equality also merges its sides.
    pub(super) fn seed_ground_root_facts(
        &mut self,
        search: &mut GroundSearch,
        roots: &[TermId],
    ) -> Option<()> {
        for &root in roots {
            if decode_eq_local(&self.ctx.terms, root).is_some() {
                continue;
            }
            let conjuncts = match self.ctx.terms.get(root) {
                TermData::App(symbol, args) if symbol.name() == "and" => args.clone(),
                _ => {
                    let limit = search.closure.edges().len();
                    let _ = search.facts.push(root, FactReason::Root, limit);
                    continue;
                }
            };
            for (position, conjunct) in conjuncts.into_iter().enumerate() {
                let position = u32::try_from(position).ok()?;
                let limit = search.closure.edges().len();
                let Some(fact) =
                    search
                        .facts
                        .push(conjunct, FactReason::Conjunct { root, position }, limit)
                else {
                    continue;
                };
                self.merge_equality_fact(search, fact)?;
            }
        }
        self.expand_nested_conjunct_facts(search)
    }

    /// Record every conjunct of a fact that is itself an `and` as a fact of
    /// its own (`SubConjunct`), transitively, so a right-nested authored
    /// conjunction `(and a (and b (and c ..)))` contributes every leaf. Each
    /// level stays a fact: it is the premise its children's `and_pos`
    /// projections resolve against. A conjunct equality also merges its sides.
    fn expand_nested_conjunct_facts(&mut self, search: &mut GroundSearch) -> Option<()> {
        let mut next = 0;
        while let Some(fact) = search.facts.facts().get(next) {
            let parent = next;
            next += 1;
            let conjuncts = match self.ctx.terms.get(fact.literal) {
                TermData::App(symbol, args) if symbol.name() == "and" => args.clone(),
                _ => continue,
            };
            for (position, conjunct) in conjuncts.into_iter().enumerate() {
                let position = u32::try_from(position).ok()?;
                let limit = search.closure.edges().len();
                let Some(child) = search.facts.push(
                    conjunct,
                    FactReason::SubConjunct { parent, position },
                    limit,
                ) else {
                    continue;
                };
                self.merge_equality_fact(search, child)?;
            }
        }
        Some(())
    }

    /// Merge the sides of an equality fact (registering them first).
    pub(super) fn merge_equality_fact(
        &mut self,
        search: &mut GroundSearch,
        fact: usize,
    ) -> Option<()> {
        let literal = search.facts.facts().get(fact)?.literal;
        if let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, literal) {
            if self.ctx.terms.sort(lhs) == self.ctx.terms.sort(rhs) {
                self.register_ground_subterms(&mut search.closure, lhs)?;
                self.register_ground_subterms(&mut search.closure, rhs)?;
                search.closure.merge(lhs, rhs, EdgeReason::Derived(fact));
            }
        }
        Some(())
    }

    /// Try to prove each watched atom in either polarity. Returns a
    /// complementary pair as soon as one appears. The outer `None` means a
    /// bound was exceeded.
    pub(super) fn derive_ground_literal_facts(
        &mut self,
        search: &mut GroundSearch,
    ) -> Option<Option<ClosureConflict>> {
        let mut watched: Vec<TermId> = Vec::new();
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        let clause_literals = search
            .facts
            .clauses
            .iter()
            .flat_map(|clause| clause.literals.iter());
        let fact_literals = search.facts.facts.iter().map(|fact| &fact.literal);
        for &literal in clause_literals.chain(fact_literals) {
            let (atom, _) = literal_atom(&self.ctx.terms, literal);
            if seen.insert(atom) {
                watched.push(atom);
            }
        }
        for atom in watched {
            let negated = self.ctx.terms.mk_not_raw(atom);
            for (literal, opposite) in [(atom, negated), (negated, atom)] {
                if search.facts.fact_for(literal).is_some() {
                    continue;
                }
                let mut probes = search.probes;
                let reason = self.derive_ground_fact_reason(search, literal, &mut probes);
                search.probes = probes;
                let Some(reason) = reason else {
                    continue;
                };
                let limit = search.closure.edges().len();
                let fact = search.facts.push(literal, reason, limit)?;
                if let Some(other) = search.facts.fact_for(opposite) {
                    return Some(Some(Self::complementary_conflict(
                        literal, fact, other, atom,
                    )));
                }
            }
        }
        Some(None)
    }

    fn complementary_conflict(
        literal: TermId,
        fact: usize,
        other: usize,
        atom: TermId,
    ) -> ClosureConflict {
        let (positive, negative) = if literal == atom {
            (fact, other)
        } else {
            (other, fact)
        };
        ClosureConflict::Complementary { positive, negative }
    }

    /// The reason `literal` holds now, if the closure, a closed evaluation or
    /// predicate congruence with an earlier fact proves it.
    fn derive_ground_fact_reason(
        &self,
        search: &GroundSearch,
        literal: TermId,
        probes: &mut usize,
    ) -> Option<FactReason> {
        let (atom, negated) = literal_atom(&self.ctx.terms, literal);
        if let Some((lhs, rhs)) = decode_eq_local(&self.ctx.terms, atom) {
            if self.ctx.terms.sort(lhs) != self.ctx.terms.sort(rhs) {
                return None;
            }
            let closure = &search.closure;
            if !negated && closure.same_class(lhs, rhs) {
                return Some(FactReason::EqualityHolds);
            }
            let separated = !closure.same_class(lhs, rhs)
                && self.class_constant(closure, lhs).is_some()
                && self.class_constant(closure, rhs).is_some();
            return (negated && separated).then_some(FactReason::EqualityRefuted);
        }
        let TermData::App(symbol, args) = self.ctx.terms.get(atom) else {
            return None;
        };
        if CLOSED_PREDICATES.contains(&symbol.name())
            && args.iter().all(|&argument| {
                Self::is_bitvec_constant(&self.ctx.terms, argument)
                    || self.is_closed_evaluable_bv_application(argument)
            })
        {
            *probes = probes.checked_sub(1)?;
            return self
                .recognize_bv_bitblast_until_stopped(&[literal])
                .then_some(FactReason::Closed);
        }
        self.pred_congruent_source(search, atom, negated)
            .map(|source| FactReason::PredCongruent { source })
    }

    /// An earlier fact of the same polarity over the same predicate whose
    /// arguments are pairwise merged with `atom`'s.
    fn pred_congruent_source(
        &self,
        search: &GroundSearch,
        atom: TermId,
        negated: bool,
    ) -> Option<usize> {
        let TermData::App(symbol, args) = self.ctx.terms.get(atom) else {
            return None;
        };
        if args.is_empty() || matches!(symbol.name(), "=" | "distinct" | "and" | "or" | "=>") {
            return None;
        }
        search.facts.facts.iter().position(|fact| {
            let (source_atom, source_negated) = literal_atom(&self.ctx.terms, fact.literal);
            source_atom != atom
                && source_negated == negated
                && matches!(
                    self.ctx.terms.get(source_atom),
                    TermData::App(source_symbol, source_args)
                        if source_symbol == symbol
                            && source_args.len() == args.len()
                            && source_args
                                .iter()
                                .zip(args.iter())
                                .all(|(&left, &right)| search.closure.same_class(left, right))
                )
        })
    }

    /// Unit-propagate every instance clause not yet fired. The outer `None`
    /// means a bound was exceeded.
    pub(super) fn propagate_ground_instances(
        &mut self,
        search: &mut GroundSearch,
    ) -> Option<Option<ClosureConflict>> {
        for index in 0..search.facts.clauses.len() {
            if search.facts.fired[index] {
                continue;
            }
            let literals = search.facts.clauses[index].literals.clone();
            let mut refuting = Vec::with_capacity(literals.len());
            let mut open = Vec::new();
            let mut satisfied = false;
            for literal in literals {
                if search.facts.fact_for(literal).is_some() {
                    satisfied = true;
                    break;
                }
                let opposite = complement(&mut self.ctx.terms, literal);
                match search.facts.fact_for(opposite) {
                    Some(fact) => refuting.push(fact),
                    None => open.push(literal),
                }
            }
            if satisfied {
                continue;
            }
            match open.as_slice() {
                [] => {
                    return Some(Some(ClosureConflict::RefutedClause {
                        clause: index,
                        refuting,
                    }));
                }
                [literal] => {
                    search.facts.fired[index] = true;
                    let limit = search.closure.edges().len();
                    let reason = FactReason::Propagated {
                        clause: index,
                        refuting,
                    };
                    let fact = search.facts.push(*literal, reason, limit)?;
                    self.merge_equality_fact(search, fact)?;
                }
                _ => {}
            }
        }
        Some(None)
    }
}
