// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explain direct read edges with ordinary checked array/BV/congruence rules.

use super::emit::ClosureEmitter;
use super::read_chain::{ReadChainEnd, ReadSkip};
use super::state::ClosureEdge;
use super::*;

#[derive(Clone, Copy)]
pub(super) struct ReadIndexUnit {
    unit: DerivedUnit,
    /// Unconditional units use zero. Alias and range units are reused only
    /// after the source edges available when their proof was constructed.
    limit: usize,
}

impl Executor {
    fn emit_read_chain_skip(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        point: TermId,
        skipped: ReadSkip,
        limit: usize,
    ) -> Option<(ProofId, TermId)> {
        if let Some(index) = skipped.disequality {
            // Reconstruct the EXACT fact at this read edge's earlier snapshot.
            // Never turn a fact-table index or a class/image into permission.
            if skipped.index_image != skipped.index
                || skipped.point_image != point
                || skipped.bases.is_some()
                || skipped.range.is_some()
            {
                return None;
            }
            let fact = emitter.facts.facts().get(index)?;
            if fact.edge_limit > limit {
                return None;
            }
            let literal = fact.literal;
            let TermData::Not(equality) = self.ctx.terms.get(literal).clone() else {
                return None;
            };
            if !equality_matches_pair_local(&self.ctx.terms, equality, point, skipped.index) {
                return None;
            }
            let unit = self.emit_ground_fact(emitter, index)?;
            if unit.literal != literal {
                return None;
            }
            // Preserve authored orientation; the ROW checker validates either
            // exact equality spelling, and the support proves its negation.
            return Some((unit.step, equality));
        }
        let pair = if point <= skipped.index {
            (point, skipped.index)
        } else {
            (skipped.index, point)
        };
        let equality = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [pair.0, pair.1], Sort::Bool);
        if let Some(cached) = emitter.read_index_units.get(&pair) {
            if cached.limit <= limit {
                return Some((cached.unit.step, equality));
            }
        }
        let dependent = skipped.bases.is_some()
            || skipped.index_image != skipped.index
            || skipped.point_image != point
            || skipped.range.is_some();
        // Refuse missing earlier authority before emitting any part of the
        // representative transport. A cache entry is never that authority.
        for (source, image) in [
            (skipped.index, skipped.index_image),
            (point, skipped.point_image),
        ] {
            if source != image {
                emitter.closure.path(source, image, limit)?;
            }
        }
        if let Some((left, right)) = skipped.bases {
            emitter.closure.path(left, right, limit)?;
        }
        let image_pair = if pair.0 == point {
            (skipped.point_image, skipped.index_image)
        } else {
            (skipped.index_image, skipped.point_image)
        };
        let image_equality =
            self.ctx
                .terms
                .mk_app(Symbol::named("="), [image_pair.0, image_pair.1], Sort::Bool);
        let image_step =
            self.emit_read_chain_image_skip(emitter, image_pair, image_equality, skipped, limit)?;
        let step = if image_equality == equality {
            image_step
        } else {
            let mut premises = Vec::new();
            premises.try_reserve_exact(2).ok()?;
            for (source, image) in [(pair.0, image_pair.0), (pair.1, image_pair.1)] {
                if source != image {
                    premises.push(
                        self.emit_closure_path_unit(emitter, source, image, limit)?
                            .step,
                    );
                }
            }
            emitter.admit_steps(3)?;
            let transport =
                self.ctx
                    .terms
                    .mk_app(Symbol::named("="), [equality, image_equality], Sort::Bool);
            let congruence =
                emitter
                    .proof
                    .add_rule_step(AletheRule::Cong, vec![transport], premises, vec![]);
            let denied_transport = self.ctx.terms.mk_not_raw(transport);
            let result = self.ctx.terms.mk_not_raw(equality);
            let bridge = emitter.proof.add_rule_step(
                AletheRule::EquivPos2,
                vec![denied_transport, result, image_equality],
                vec![],
                vec![],
            );
            emitter.proof.add_rule_step(
                AletheRule::Resolution,
                vec![result],
                vec![bridge, congruence, image_step],
                vec![],
            )
        };
        emitter.read_index_units.try_reserve(1).ok()?;
        emitter.read_index_units.insert(
            pair,
            ReadIndexUnit {
                unit: DerivedUnit {
                    literal: self.ctx.terms.mk_not_raw(equality),
                    step,
                },
                limit: if dependent { limit } else { 0 },
            },
        );
        Some((step, equality))
    }

    /// Prove only the selected image pair. The caller transports this unit
    /// back to the exact source indices using actual earlier equalities.
    fn emit_read_chain_image_skip(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        pair: (TermId, TermId),
        equality: TermId,
        skipped: ReadSkip,
        limit: usize,
    ) -> Option<ProofId> {
        if let Some(range) = skipped.range {
            return self.emit_ground_range_skip(
                emitter,
                skipped.point_image,
                skipped.index_image,
                equality,
                range,
                skipped.bases,
                limit,
            );
        }
        let disequality = self.ctx.terms.mk_not_raw(equality);
        let checked = if self.alethe_dialect() == ay_proof::AletheDialect::Clean {
            if let Some(bases) = skipped.bases {
                self.emit_ground_offset_alias_skip(
                    emitter,
                    pair,
                    skipped.index_image,
                    skipped.point_image,
                    bases,
                    limit,
                )?
            } else {
                self.emit_ground_offset_intrinsic(emitter, equality, false)?
                    .map(|unit| unit.step)
            }
        } else {
            None
        };
        if let Some(step) = checked {
            return Some(step);
        }
        let step = if let Some((a, b)) = skipped.bases {
            // This is conditional on an ACTUAL earlier base equality, not a
            // fresh symbolic-word abstraction or an assumed offset fact.
            let alias = self.emit_closure_path_unit(emitter, a, b, limit)?;
            emitter.admit_steps(2)?;
            let clause = vec![self.ctx.terms.mk_not_raw(alias.literal), disequality];
            let lemma = emitter.proof.add_theory_lemma_with_kind(
                "bv",
                clause.clone(),
                TheoryLemmaKind::BvBitBlast,
            );
            self.resolve_closure_units(emitter, lemma, clause, &[alias], &[disequality])?
        } else {
            emitter.admit_steps(1)?;
            emitter.proof.add_theory_lemma_with_kind(
                "bv",
                vec![disequality],
                TheoryLemmaKind::BvBitBlast,
            )
        };
        Some(step)
    }

    pub(super) fn emit_ground_read_chain(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        edge: ClosureEdge,
        literal: TermId,
        limit: usize,
        witness: usize,
    ) -> Option<ProofId> {
        if !emitter.read_chains.current(&self.ctx) {
            return None;
        }
        let witness = emitter.read_chains.witnesses.get(witness)?;
        let (array, source_index) = select_parts_local(&self.ctx.terms, edge.a)?;
        let stop = self.make_proof_assembly_should_stop();
        if stop() {
            return None;
        }
        emitter.admit_steps(1)?;
        let point = witness.index;
        if let ReadChainEnd::Base(base) = witness.end {
            self.ctx.terms.entry_stamp(base)?;
            self.ctx.terms.entry_stamp(edge.b)?;
            let Sort::Array(shape) = self.ctx.terms.sort(base) else {
                return None;
            };
            if &shape.element_sort != self.ctx.terms.sort(edge.b) {
                return None;
            }
            let exact_tail = select_parts_local(&self.ctx.terms, edge.b) == Some((base, point))
                || self.ctx.terms.get_const_array(base) == Some(edge.b);
            if point != source_index
                || self.ctx.terms.sort(base) != self.ctx.terms.sort(array)
                || !exact_tail
            {
                return None;
            }
        }
        let skipped = &witness.skipped;
        let adjusted = self.ctx.terms.mk_app(
            Symbol::named("select"),
            [array, point],
            self.ctx.terms.sort(edge.a).clone(),
        );
        let conclusion = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [adjusted, edge.b], Sort::Bool);
        let mut clause = Vec::new();
        let mut units = Vec::new();
        let mut seen = ay_core::kani_compat::DetHashSet::default();
        clause
            .try_reserve_exact(skipped.len().checked_add(1)?)
            .ok()?;
        units.try_reserve_exact(skipped.len()).ok()?;
        seen.try_reserve(skipped.len()).ok()?;
        for &skip in skipped {
            if stop() {
                return None;
            }
            emitter.admit_steps(1)?;
            let (step, guard) = self.emit_read_chain_skip(emitter, point, skip, limit)?;
            if seen.insert(guard) {
                clause.push(guard);
                units.push(step);
            }
        }
        clause.push(conclusion);
        emitter.admit_steps(1)?;
        let kind = if units.is_empty() {
            TheoryLemmaKind::ArraySelectStore { index_eq: true }
        } else {
            TheoryLemmaKind::ArrayRowChain
        };
        let row = emitter
            .proof
            .add_theory_lemma_with_kind("array", clause, kind);
        let row = if units.is_empty() {
            row
        } else {
            // The existing all-unit-tail resolution checker subtracts each
            // distinct guard once. No triangular shrinking clauses are built.
            emitter.admit_steps(1)?;
            let mut premises = Vec::new();
            premises
                .try_reserve_exact(units.len().checked_add(1)?)
                .ok()?;
            premises.push(row);
            premises.extend(units);
            emitter.proof.add_rule_step(
                AletheRule::Resolution,
                vec![conclusion],
                premises,
                Vec::new(),
            )
        };
        if source_index == point {
            return (conclusion == literal && !stop()).then_some(row);
        }
        // One proof-only read at the actual store key; never a read for each
        // skipped suffix. Congruence uses only source edges before this edge.
        let bridge = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [edge.a, adjusted], Sort::Bool);
        emitter.admit_steps(1)?;
        let bridge_step = self.emit_closure_cong(
            emitter,
            &[array, source_index],
            &[array, point],
            bridge,
            limit,
        )?;
        emitter.admit_steps(3)?;
        if stop() {
            return None;
        }
        let clause = vec![
            self.ctx.terms.mk_not_raw(bridge),
            self.ctx.terms.mk_not_raw(conclusion),
            literal,
        ];
        let transitive = emitter.proof.add_theory_lemma_with_kind(
            "euf",
            clause.clone(),
            TheoryLemmaKind::EufTransitive,
        );
        self.resolve_closure_units(
            emitter,
            transitive,
            clause,
            &[
                DerivedUnit {
                    literal: bridge,
                    step: bridge_step,
                },
                DerivedUnit {
                    literal: conclusion,
                    step: row,
                },
            ],
            &[literal],
        )
    }
}

#[cfg(test)]
mod authored_guard_snapshot_controls {
    use super::super::facts::GroundSearch;
    use super::*;
    use ay_frontend::parse;

    #[test]
    fn future_fact_and_replaced_index_cannot_authorize_a_read_skip() {
        let input = "(set-logic QF_BV) (declare-const p (_ BitVec 8)) (declare-const k (_ BitVec 8)) (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8)) (assert (and (= x y) (not (= p k)) (= p k)))";
        let mut exec = Executor::new();
        exec.execute_all(&parse(input).unwrap()).unwrap();
        let surface = exec.ctx.assertions_parsed()[0].clone();
        let root = exec.raw_intern_ground_bv_surface(&surface).unwrap();
        let TermData::App(_, args) = exec.ctx.terms.get(root).clone() else {
            panic!("and");
        };
        let TermData::Not(equality) = exec.ctx.terms.get(args[1]).clone() else {
            panic!("not");
        };
        let (point, index) = decode_eq_local(&exec.ctx.terms, equality).unwrap();
        let mut search = GroundSearch::default();
        exec.register_ground_subterms(&mut search.closure, root)
            .unwrap();
        exec.seed_ground_root_facts(&mut search, &[root]).unwrap();
        let fact = search.facts.fact_for(args[1]).unwrap();
        assert_eq!(search.facts.facts()[fact].edge_limit, 1);
        let mut emitter = ClosureEmitter::new(&search);
        let skip = ReadSkip {
            index,
            index_image: index,
            point_image: point,
            bases: None,
            range: None,
            disequality: Some(fact),
        };
        assert!(exec
            .emit_read_chain_skip(&mut emitter, point, skip, 0)
            .is_none());
        assert_eq!(emitter.proof.steps, [] as [ProofStep; 0]);
        let replaced = ReadSkip {
            index: point,
            index_image: point,
            ..skip
        };
        assert!(exec
            .emit_read_chain_skip(&mut emitter, point, replaced, 1)
            .is_none());
        assert_eq!(emitter.proof.steps, [] as [ProofStep; 0]);
        let (negative, pivot) = exec
            .emit_read_chain_skip(&mut emitter, point, skip, 1)
            .expect("only the exact earlier authored fact is eligible");
        // The strict entry point checks a refutation, not an open unit
        // derivation. Close it using the opposite fact from the SAME root;
        // neither support is introduced as an independent assumption.
        let positive_fact = search.facts.fact_for(args[2]).unwrap();
        let positive = exec.emit_ground_fact(&mut emitter, positive_fact).unwrap();
        assert_eq!(positive.literal, pivot);
        emitter
            .proof
            .add_resolution(vec![], pivot, negative, positive.step);
        assert!(emitter
            .proof
            .steps
            .iter()
            .all(|step| !matches!(step, ProofStep::Assume(term) if *term != root)));
        assert!(exec
            .check_proof_strict_derivation_with_datatypes(&emitter.proof)
            .unwrap()
            .is_complete());
    }
}
