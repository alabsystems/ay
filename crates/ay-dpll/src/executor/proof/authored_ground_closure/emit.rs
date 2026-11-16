// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Emission of the strict-checked candidate behind a closure conflict.
//!
//! Each recorded edge becomes ONE unit clause `(cl (= a b))` in the edge's own
//! orientation, built by the lemma its reason names; an explanation between
//! two class members chains the units of its edge path with `EufTransitive`.
//! Edges are memoized, and an edge is explained only from strictly earlier
//! edges (`GroundClosure::path` with `limit`), so the recursion is well
//! founded and every shared sub-derivation is emitted once.

use ay_core::kani_compat::DetHashMap;

use super::facts::FactBase;
use super::state::ClosureEdge;
use super::*;

/// Proof steps one candidate may hold before this lane declines. A nested
/// authored conjunction costs two steps per level before any equality
/// reasoning starts.
const MAX_EMITTED_STEPS: usize = 16_384;

/// The candidate under construction.
pub(super) struct ClosureEmitter<'c> {
    pub(super) closure: &'c GroundClosure,
    pub(super) facts: &'c FactBase,
    pub(super) read_chains: &'c read_chain::ReadChainState,
    pub(super) packings: &'c packing::PackingState,
    pub(super) read_index_units: DetHashMap<(TermId, TermId), read_chain_emit::ReadIndexUnit>,
    pub(super) proof: Proof,
    /// Unconditional Boolean constants shared only within this candidate.
    pub(super) offset_constants: [Option<ProofId>; 2],
    /// One shared coverage/goal-selection allowance for this candidate.
    pub(super) disjunction_work: usize,
    edge_units: DetHashMap<usize, DerivedUnit>,
    pub(super) fact_units: DetHashMap<usize, DerivedUnit>,
    assumed: DetHashMap<TermId, ProofId>,
}

impl<'c> ClosureEmitter<'c> {
    pub(super) fn new(search: &'c GroundSearch) -> Self {
        Self {
            closure: &search.closure,
            facts: &search.facts,
            read_chains: &search.read_chains,
            packings: &search.packings,
            read_index_units: DetHashMap::default(),
            proof: Proof::new(),
            offset_constants: [None; 2],
            disjunction_work: goal::MAX_GOAL_WORK,
            edge_units: DetHashMap::default(),
            fact_units: DetHashMap::default(),
            assumed: DetHashMap::default(),
        }
    }

    pub(super) fn within_budget(&self) -> Option<()> {
        (self.proof.steps.len() <= MAX_EMITTED_STEPS).then_some(())
    }

    pub(super) fn admit_steps(&self, count: usize) -> Option<()> {
        (self.proof.steps.len().checked_add(count)? <= MAX_EMITTED_STEPS).then_some(())
    }

    pub(super) fn assume(&mut self, root: TermId) -> ProofId {
        if let Some(&step) = self.assumed.get(&root) {
            return step;
        }
        let step = self.proof.add_assume(root, None);
        self.assumed.insert(root, step);
        step
    }
}

impl Executor {
    /// The empty-clause candidate for `conflict`.
    pub(super) fn emit_ground_closure_refutation(
        &mut self,
        search: &GroundSearch,
        conflict: ClosureConflict,
    ) -> Option<Proof> {
        let mut emitter = ClosureEmitter::new(search);
        let limit = search.closure.edges().len();
        match conflict {
            ClosureConflict::ConstantClash(first, second) => {
                let joined = self.emit_closure_path_unit(&mut emitter, first, second, limit)?;
                let disequality = self.ctx.terms.mk_not_raw(joined.literal);
                if !self.recognize_bv_bitblast_until_stopped(&[disequality]) {
                    return None;
                }
                let refuted = emitter.proof.add_theory_lemma_with_kind(
                    "bv",
                    vec![disequality],
                    TheoryLemmaKind::BvBitBlast,
                );
                emitter
                    .proof
                    .add_resolution(Vec::new(), joined.literal, joined.step, refuted);
            }
            ClosureConflict::Disequality {
                root,
                equality,
                lhs,
                rhs,
            } => {
                let joined = self.emit_closure_path_unit(&mut emitter, lhs, rhs, limit)?;
                if joined.literal != equality {
                    return None;
                }
                let assumed = emitter.assume(root);
                emitter
                    .proof
                    .add_resolution(Vec::new(), equality, joined.step, assumed);
            }
            ClosureConflict::Complementary { positive, negative } => {
                let holds = self.emit_ground_fact(&mut emitter, positive)?;
                let fails = self.emit_ground_fact(&mut emitter, negative)?;
                if self.ctx.terms.mk_not_raw(holds.literal) != fails.literal {
                    return None;
                }
                emitter
                    .proof
                    .add_resolution(Vec::new(), holds.literal, holds.step, fails.step);
            }
            ClosureConflict::RefutedClause { clause, refuting } => {
                self.emit_refuted_instance(&mut emitter, clause, &refuting, &[])?;
            }
            ClosureConflict::NegatedGoal { negative } => {
                self.emit_negated_goal_conflict(&mut emitter, negative)?;
            }
        }
        emitter.within_budget()?;
        Some(emitter.proof)
    }

    /// The unit `(cl (= from to))`, in exactly that orientation, from the
    /// edges recorded before `limit`.
    pub(super) fn emit_closure_path_unit(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        from: TermId,
        to: TermId,
        limit: usize,
    ) -> Option<DerivedUnit> {
        emitter.within_budget()?;
        let goal = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [from, to], Sort::Bool);
        if from == to {
            let step = emitter.proof.add_theory_lemma_with_kind(
                "euf",
                vec![goal],
                TheoryLemmaKind::EufReflexive,
            );
            return Some(DerivedUnit {
                step,
                literal: goal,
            });
        }
        let walk = emitter.closure.path(from, to, limit)?;
        let mut units = Vec::with_capacity(walk.len());
        for edge_index in walk {
            units.push(self.emit_closure_edge(emitter, edge_index)?);
        }
        if let [unit] = units.as_slice() {
            if unit.literal == goal {
                return Some(*unit);
            }
            // A single reversed edge needs only the ordinary premise-based
            // symmetry rule. The earlier unit remains the sole authority;
            // avoid a redundant premise-free transitivity clause over both
            // copies of a potentially large source term. Pinned presentation
            // retains its existing derivation.
            if self.alethe_dialect() == ay_proof::AletheDialect::Clean
                && decode_eq_local(&self.ctx.terms, unit.literal) == Some((to, from))
            {
                emitter.admit_steps(1)?;
                let step = emitter.proof.add_rule_step(
                    AletheRule::Symm,
                    vec![goal],
                    vec![unit.step],
                    Vec::new(),
                );
                return Some(DerivedUnit {
                    step,
                    literal: goal,
                });
            }
        }
        let mut clause: Vec<TermId> = units
            .iter()
            .map(|unit| self.ctx.terms.mk_not_raw(unit.literal))
            .collect();
        clause.push(goal);
        let lemma = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufTransitive,
        );
        let step = self.resolve_closure_units(emitter, lemma, clause, &units, &[goal])?;
        Some(DerivedUnit {
            step,
            literal: goal,
        })
    }

    /// Resolve every unit's literal out of `clause` (proved by `step`),
    /// requiring exactly `expected` to remain.
    pub(super) fn resolve_closure_units(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        mut step: ProofId,
        mut clause: Vec<TermId>,
        units: &[DerivedUnit],
        expected: &[TermId],
    ) -> Option<ProofId> {
        for unit in units {
            let negated = self.ctx.terms.mk_not_raw(unit.literal);
            let position = clause.iter().position(|&literal| literal == negated)?;
            let _ = clause.remove(position);
            step = emitter
                .proof
                .add_resolution(clause.clone(), unit.literal, step, unit.step);
        }
        (clause == expected).then_some(step)
    }

    /// The unit proving edge `edge_index`, emitted once.
    fn emit_closure_edge(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        edge_index: usize,
    ) -> Option<DerivedUnit> {
        if let Some(&unit) = emitter.edge_units.get(&edge_index) {
            return Some(unit);
        }
        let edge: ClosureEdge = *emitter.closure.edges().get(edge_index)?;
        let literal = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [edge.a, edge.b], Sort::Bool);
        let step = match edge.reason {
            EdgeReason::Authored(root) => {
                if root != literal {
                    return None;
                }
                emitter.assume(root)
            }
            EdgeReason::ModularOffset => {
                if let Some(unit) = self.emit_ground_offset_intrinsic(emitter, literal, true)? {
                    unit.step
                } else {
                    emitter.admit_steps(1)?;
                    // Closed additive prefixes can exceed the literal-only
                    // primitive grammar. Keep the incoming shared affine owner
                    // as the checked fallback for those offset identities.
                    emitter.proof.add_theory_lemma_with_kind(
                        "arith",
                        vec![literal],
                        TheoryLemmaKind::ArithClauseTautology,
                    )
                }
            }
            EdgeReason::Evaluated | EdgeReason::SliceIdentity => emitter
                .proof
                .add_theory_lemma_with_kind("bv", vec![literal], TheoryLemmaKind::BvBitBlast),
            EdgeReason::Congruent => {
                self.emit_closure_congruence(emitter, edge, literal, edge_index)?
            }
            EdgeReason::ReadHit => {
                self.emit_closure_read_hit(emitter, edge, literal, edge_index)?
            }
            EdgeReason::ReadMiss => {
                self.emit_closure_read_miss(emitter, edge, literal, edge_index)?
            }
            EdgeReason::ReadChain(witness) => {
                self.emit_ground_read_chain(emitter, edge, literal, edge_index, witness)?
            }
            EdgeReason::Packing(witness) => {
                self.emit_ground_packing(emitter, edge, literal, edge_index, witness)?
            }
            EdgeReason::Derived(fact) => {
                let unit = self.emit_ground_fact(emitter, fact)?;
                if unit.literal != literal {
                    return None;
                }
                unit.step
            }
        };
        let unit = DerivedUnit { step, literal };
        emitter.edge_units.insert(edge_index, unit);
        Some(unit)
    }

    /// `EufCongruent` over the two applications, one premise per position,
    /// or `cong` (`emit_closure_cong`) for the heads `eq_congruent` cannot
    /// carry.
    fn emit_closure_congruence(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        edge: ClosureEdge,
        literal: TermId,
        edge_index: usize,
    ) -> Option<ProofId> {
        let (left_symbol, left_args, right_args) = match (
            self.ctx.terms.get(edge.a).clone(),
            self.ctx.terms.get(edge.b).clone(),
        ) {
            (TermData::App(left_symbol, left_args), TermData::App(right_symbol, right_args)) => {
                if left_symbol != right_symbol || left_args.len() != right_args.len() {
                    return None;
                }
                (left_symbol, left_args, right_args)
            }
            (TermData::Ite(c1, t1, e1), TermData::Ite(c2, t2, e2)) => {
                return self.emit_closure_cong(
                    emitter,
                    &[c1, t1, e1],
                    &[c2, t2, e2],
                    literal,
                    edge_index,
                );
            }
            (TermData::Not(left), TermData::Not(right)) => {
                return self.emit_closure_cong(emitter, &[left], &[right], literal, edge_index);
            }
            _ => return None,
        };
        if matches!(left_symbol, Symbol::Indexed(..)) || left_symbol.name() == "=" {
            return self.emit_closure_cong(emitter, &left_args, &right_args, literal, edge_index);
        }
        let mut premises = Vec::with_capacity(left_args.len());
        for (&left, &right) in left_args.iter().zip(right_args.iter()) {
            premises.push(self.emit_closure_path_unit(emitter, left, right, edge_index)?);
        }
        let mut clause: Vec<TermId> = premises
            .iter()
            .map(|premise| self.ctx.terms.mk_not_raw(premise.literal))
            .collect();
        clause.push(literal);
        let lemma = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufCongruent,
        );
        self.resolve_closure_units(emitter, lemma, clause, &premises, &[literal])
    }

    /// `cong` over two applications of one head that `eq_congruent` cannot
    /// carry to the consumer, one unit premise per argument position whose
    /// two terms differ, in position order: an INDEXED head (`extract`,
    /// `zero_extend`, ..), which Carcara reads as a parameterized operator
    /// and its `eq_congruent` refuses outright ("rule validation failed"),
    /// and the dedicated `ite`, `not` and Boolean `=` nodes. Carcara's `cong`
    /// compares heads and indices and checks exactly these premises (an
    /// equality's operands in either orientation).
    pub(super) fn emit_closure_cong(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        left_args: &[TermId],
        right_args: &[TermId],
        literal: TermId,
        edge_index: usize,
    ) -> Option<ProofId> {
        let mut premises = Vec::with_capacity(left_args.len());
        for (&left, &right) in left_args.iter().zip(right_args.iter()) {
            if left != right {
                let unit = self.emit_closure_path_unit(emitter, left, right, edge_index)?;
                premises.push(unit.step);
            }
        }
        if premises.is_empty() {
            return None;
        }
        Some(
            emitter
                .proof
                .add_rule_step(AletheRule::Cong, vec![literal], premises, Vec::new()),
        )
    }

    /// ROW1: `(= (select (store A i e) j) e)`, guarded by `(not (= i j))` and
    /// resolved against the explained index equality when `i` and `j` are
    /// different terms.
    fn emit_closure_read_hit(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        edge: ClosureEdge,
        literal: TermId,
        edge_index: usize,
    ) -> Option<ProofId> {
        let (array, read_index) = select_parts_local(&self.ctx.terms, edge.a)?;
        let (_, store_index, value) = store_parts_local(&self.ctx.terms, array)?;
        if value != edge.b {
            return None;
        }
        let kind = TheoryLemmaKind::ArraySelectStore { index_eq: true };
        if store_index == read_index {
            return Some(
                emitter
                    .proof
                    .add_theory_lemma_with_kind("array", vec![literal], kind),
            );
        }
        let index = self.emit_closure_path_unit(emitter, store_index, read_index, edge_index)?;
        let guard = self.ctx.terms.mk_not_raw(index.literal);
        let clause = vec![guard, literal];
        let lemma = emitter
            .proof
            .add_theory_lemma_with_kind("array", clause.clone(), kind);
        self.resolve_closure_units(emitter, lemma, clause, &[index], &[literal])
    }

    /// ROW2: `(cl (= i j) (= (select (store A i e) j) (select A j)))`,
    /// resolved against the proved index disequality.
    fn emit_closure_read_miss(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        edge: ClosureEdge,
        literal: TermId,
        edge_index: usize,
    ) -> Option<ProofId> {
        let (array, read_index) = select_parts_local(&self.ctx.terms, edge.a)?;
        let (base, store_index, _) = store_parts_local(&self.ctx.terms, array)?;
        if select_parts_local(&self.ctx.terms, edge.b) != Some((base, read_index)) {
            return None;
        }
        let (differ, index_equality) =
            self.emit_closure_index_disequality(emitter, store_index, read_index, edge_index)?;
        let clause = vec![index_equality, literal];
        let lemma = emitter.proof.add_theory_lemma_with_kind(
            "array",
            clause.clone(),
            TheoryLemmaKind::ArraySelectStore { index_eq: false },
        );
        let remaining = vec![literal];
        let step = emitter
            .proof
            .add_resolution(remaining, index_equality, lemma, differ);
        Some(step)
    }

    /// The unit `(cl (not (= i j)))` and the equality it negates: directly by
    /// `BvBitBlast` when both indices are closed, otherwise through the two
    /// constants their classes hold (`EufTransitive` to the constant equality,
    /// which `BvBitBlast` refutes).
    pub(super) fn emit_closure_index_disequality(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        store_index: TermId,
        read_index: TermId,
        limit: usize,
    ) -> Option<(ProofId, TermId)> {
        let equality =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [store_index, read_index], Sort::Bool);
        let disequality = self.ctx.terms.mk_not_raw(equality);
        let closed = |this: &Self, term: TermId| {
            Self::is_bitvec_constant(&this.ctx.terms, term)
                || this.is_closed_evaluable_bv_application(term)
        };
        if closed(self, store_index)
            && closed(self, read_index)
            && self.recognize_bv_bitblast_until_stopped(&[disequality])
        {
            let step = emitter.proof.add_theory_lemma_with_kind(
                "bv",
                vec![disequality],
                TheoryLemmaKind::BvBitBlast,
            );
            return Some((step, equality));
        }
        let store_constant = self.reachable_constant(emitter.closure, store_index, limit)?;
        let read_constant = self.reachable_constant(emitter.closure, read_index, limit)?;
        let constants = self.ctx.terms.mk_app(
            Symbol::named("="),
            [store_constant, read_constant],
            Sort::Bool,
        );
        let constants_differ = self.ctx.terms.mk_not_raw(constants);
        if store_constant == read_constant
            || !self.recognize_bv_bitblast_until_stopped(&[constants_differ])
        {
            return None;
        }
        // Chain `store_constant — store_index — read_index — read_constant`.
        let mut anchors = Vec::with_capacity(2);
        let mut clause = Vec::with_capacity(4);
        if store_index != store_constant {
            let unit = self.emit_closure_path_unit(emitter, store_index, store_constant, limit)?;
            clause.push(self.ctx.terms.mk_not_raw(unit.literal));
            anchors.push(unit);
        }
        clause.push(disequality);
        if read_index != read_constant {
            let unit = self.emit_closure_path_unit(emitter, read_index, read_constant, limit)?;
            clause.push(self.ctx.terms.mk_not_raw(unit.literal));
            anchors.push(unit);
        }
        clause.push(constants);
        let lemma = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufTransitive,
        );
        let chained = self.resolve_closure_units(
            emitter,
            lemma,
            clause,
            &anchors,
            &[disequality, constants],
        )?;
        let refuted = emitter.proof.add_theory_lemma_with_kind(
            "bv",
            vec![constants_differ],
            TheoryLemmaKind::BvBitBlast,
        );
        let step = emitter
            .proof
            .add_resolution(vec![disequality], constants, chained, refuted);
        Some((step, equality))
    }

    /// A bit-vector constant joined to `term` by edges before `limit`.
    fn reachable_constant(
        &self,
        closure: &GroundClosure,
        term: TermId,
        limit: usize,
    ) -> Option<TermId> {
        if Self::is_bitvec_constant(&self.ctx.terms, term) {
            return Some(term);
        }
        closure.nodes().iter().copied().find(|&node| {
            Self::is_bitvec_constant(&self.ctx.terms, node)
                && self.ctx.terms.sort(node) == self.ctx.terms.sort(term)
                && closure.path(term, node, limit).is_some()
        })
    }
}
