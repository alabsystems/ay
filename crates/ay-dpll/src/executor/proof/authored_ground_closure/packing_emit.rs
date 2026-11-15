// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Proof-only packing contexts: ordinary Cong/Trans and one strict BV identity.

use super::emit::ClosureEmitter;
use super::packing::{extract_member, PackNode, PackPiece, PackSite, PackingWitness};
use super::state::ClosureEdge;
use super::*;

fn node_source(site: &PackSite, index: usize) -> Option<TermId> {
    Some(match *site.nodes.get(index)? {
        PackNode::Fixed(source)
        | PackNode::Unary { source, .. }
        | PackNode::Binary { source, .. } => source,
        PackNode::Piece(piece) => site.pieces.get(piece)?.source,
    })
}

fn unchanged_piece(terms: &TermStore, piece: PackPiece, word: TermId, width: u32) -> bool {
    if piece.low == 0 && piece.high + 1 == width {
        return piece.source == word;
    }
    extract_member(terms, piece.source).is_some_and(|member| {
        member.word == word
            && matches!(terms.get(member.term),
            TermData::App(Symbol::Indexed(_, indices), _)
                if indices.as_slice() == [piece.high, piece.low])
    })
}

// An allocation-free preflight. Plans have fixed operator arities and the
// existing source-node/depth bounds; the visit cap also rejects forged sharing
// or cycles. Each changed target constructor is backed by its reserved step.
fn local_cost(
    terms: &TermStore,
    site: &PackSite,
    witness: &PackingWitness,
    index: usize,
    visits: &mut usize,
    pieces: &mut usize,
    depth: usize,
) -> Option<(bool, usize, usize)> {
    *visits = visits.checked_sub(1)?;
    if depth > super::goal::MAX_GOAL_DEPTH {
        return None;
    }
    match *site.nodes.get(index)? {
        PackNode::Fixed(source) => {
            terms.entry_stamp(source)?;
            Some((false, 0, index))
        }
        PackNode::Piece(piece_index) => {
            if piece_index != *pieces {
                return None;
            }
            *pieces = pieces.checked_add(1)?;
            let piece = *site.pieces.get(piece_index)?;
            let member = *witness.members.get(piece_index)?;
            terms.entry_stamp(piece.source)?;
            if extract_member(terms, member.term) != Some(member)
                || terms.sort(member.term) != terms.sort(piece.source)
                || !matches!(terms.get(member.term),TermData::App(Symbol::Indexed(_,indices),_) if indices.as_slice()==[piece.high,piece.low])
                || terms.sort(member.word).bitvec_width() != Some(site.width)
            {
                return None;
            }
            let changed = !unchanged_piece(terms, piece, witness.word, site.width);
            let alias = changed
                && member.word != witness.word
                && !(piece.low == 0 && piece.high + 1 == site.width);
            Some((
                changed,
                usize::from(alias) + usize::from(alias && piece.source != member.term),
                index,
            ))
        }
        PackNode::Unary { source, child } => {
            if child.checked_add(1)? != index {
                return None;
            }
            terms.entry_stamp(source)?;
            let TermData::App(Symbol::Indexed(name, indices), args) = terms.get(source) else {
                return None;
            };
            let &[extra] = indices.as_slice() else {
                return None;
            };
            let child_source = node_source(site, child)?;
            terms.entry_stamp(child_source)?;
            if name != "zero_extend"
                || args.as_slice() != [child_source]
                || terms.sort(source).bitvec_width() != Some(site.width)
                || terms.sort(child_source).bitvec_width()?.checked_add(extra) != Some(site.width)
            {
                return None;
            }
            let (changed, steps, start) =
                local_cost(terms, site, witness, child, visits, pieces, depth + 1)?;
            Some((changed, steps.checked_add(usize::from(changed))?, start))
        }
        PackNode::Binary {
            source,
            left,
            right,
        } => {
            if left >= index || right.checked_add(1)? != index {
                return None;
            }
            terms.entry_stamp(source)?;
            let TermData::App(Symbol::Named(name), args) = terms.get(source) else {
                return None;
            };
            if !matches!(name.as_str(), "bvor" | "bvshl")
                || args.as_slice() != [node_source(site, left)?, node_source(site, right)?]
                || terms.sort(source).bitvec_width() != Some(site.width)
            {
                return None;
            }
            let (a, first, start) =
                local_cost(terms, site, witness, left, visits, pieces, depth + 1)?;
            let (b, second, right_start) =
                local_cost(terms, site, witness, right, visits, pieces, depth + 1)?;
            if left.checked_add(1)? != right_start {
                return None;
            }
            Some((
                a || b,
                first
                    .checked_add(second)?
                    .checked_add(usize::from(a || b))?,
                start,
            ))
        }
    }
}

#[derive(Clone, Copy)]
struct Earlier {
    source: Option<DerivedUnit>,
    alias: Option<DerivedUnit>,
}

impl Executor {
    fn packing_trans(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        from: TermId,
        to: TermId,
        first: DerivedUnit,
        second: DerivedUnit,
    ) -> Option<DerivedUnit> {
        emitter.admit_steps(1)?;
        let literal = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [from, to], Sort::Bool);
        let step = emitter.proof.add_rule_step(
            AletheRule::Trans,
            vec![literal],
            vec![first.step, second.step],
            Vec::new(),
        );
        Some(DerivedUnit { literal, step })
    }

    pub(super) fn emit_ground_packing(
        &mut self,
        emitter: &mut ClosureEmitter<'_>,
        edge: ClosureEdge,
        literal: TermId,
        limit: usize,
        witness_index: usize,
    ) -> Option<ProofId> {
        let state = emitter.packings;
        if !state.current(&self.ctx) {
            return None;
        }
        let witness = state.witnesses.get(witness_index)?;
        let site = state.sites.get(witness.site)?;
        if site.source != edge.a
            || witness.word != edge.b
            || !state.word_is_pure(witness.word)
            || self.ctx.terms.sort(witness.word).bitvec_width() != Some(site.width)
            || witness.members.len() != site.pieces.len()
        {
            return None;
        }
        let root = site.nodes.len().checked_sub(1)?;
        if node_source(site, root) != Some(site.source) {
            return None;
        }
        let mut visits = MAX_NODES;
        let mut pieces = 0;
        let (changed, steps, start) = local_cost(
            &self.ctx.terms,
            site,
            witness,
            root,
            &mut visits,
            &mut pieces,
            0,
        )?;
        if start != 0 || pieces != site.pieces.len() {
            return None;
        }
        let local_steps = steps.checked_add(1)?.checked_add(usize::from(changed))?;
        let stop = self.make_proof_assembly_should_stop();
        if stop() {
            return None;
        }
        emitter.admit_steps(local_steps)?;
        let mut earlier = Vec::new();
        earlier.try_reserve_exact(site.pieces.len()).ok()?;
        // Only this phase invokes recursive closure explanations. Re-admit
        // the entire local remainder after them, before pure-context scratch
        // or constructors. No new assembly allowance is introduced.
        for (&piece, &member) in site.pieces.iter().zip(&witness.members) {
            if stop() {
                return None;
            }
            emitter.admit_steps(local_steps)?;
            let mut units = Earlier {
                source: None,
                alias: None,
            };
            if !unchanged_piece(&self.ctx.terms, piece, witness.word, site.width) {
                if piece.low == 0 && piece.high + 1 == site.width {
                    units.source = Some(self.emit_closure_path_unit(
                        emitter,
                        piece.source,
                        witness.word,
                        limit,
                    )?);
                } else {
                    if piece.source != member.term {
                        units.source = Some(self.emit_closure_path_unit(
                            emitter,
                            piece.source,
                            member.term,
                            limit,
                        )?);
                    }
                    if member.word != witness.word {
                        units.alias = Some(self.emit_closure_path_unit(
                            emitter,
                            member.word,
                            witness.word,
                            limit,
                        )?);
                    }
                }
            }
            earlier.push(units);
        }
        emitter.admit_steps(local_steps)?;
        if stop() {
            return None;
        }
        let mut targets: Vec<(TermId, Option<DerivedUnit>)> = Vec::new();
        targets.try_reserve_exact(site.nodes.len()).ok()?;
        for (index, &node) in site.nodes.iter().enumerate() {
            if stop() {
                return None;
            }
            let source = node_source(site, index)?;
            let result = match node {
                PackNode::Fixed(term) => (term, None),
                PackNode::Piece(piece_index) => {
                    let piece = site.pieces[piece_index];
                    let member = witness.members[piece_index];
                    let units = earlier[piece_index];
                    if unchanged_piece(&self.ctx.terms, piece, witness.word, site.width) {
                        (source, None)
                    } else if piece.low == 0 && piece.high + 1 == site.width {
                        (witness.word, units.source)
                    } else {
                        let (target, alias_unit) = if let Some(alias) = units.alias {
                            emitter.admit_steps(1)?;
                            let target = self.ctx.terms.mk_app(
                                Symbol::indexed("extract", vec![piece.high, piece.low]),
                                [witness.word],
                                Sort::bitvec(piece.high - piece.low + 1),
                            );
                            let eq = self.ctx.terms.mk_app(
                                Symbol::named("="),
                                [member.term, target],
                                Sort::Bool,
                            );
                            let step = emitter.proof.add_rule_step(
                                AletheRule::Cong,
                                vec![eq],
                                vec![alias.step],
                                Vec::new(),
                            );
                            (target, Some(DerivedUnit { literal: eq, step }))
                        } else {
                            (member.term, None)
                        };
                        let unit = match (units.source, alias_unit) {
                            (Some(first), Some(second)) => {
                                Some(self.packing_trans(emitter, source, target, first, second)?)
                            }
                            (first, None) => first,
                            (None, second) => second,
                        };
                        if source != target && unit.is_none() {
                            return None;
                        }
                        (target, unit)
                    }
                }
                PackNode::Unary { source, child } => {
                    let child = targets.get(child).copied()?;
                    if child.1.is_none() {
                        (source, None)
                    } else {
                        emitter.admit_steps(1)?;
                        let TermData::App(symbol, _) = self.ctx.terms.get(source) else {
                            return None;
                        };
                        let symbol = symbol.clone();
                        let sort = self.ctx.terms.sort(source).clone();
                        let target = self.ctx.terms.mk_app(symbol, [child.0], sort);
                        let eq =
                            self.ctx
                                .terms
                                .mk_app(Symbol::named("="), [source, target], Sort::Bool);
                        let step = emitter.proof.add_rule_step(
                            AletheRule::Cong,
                            vec![eq],
                            vec![child.1?.step],
                            Vec::new(),
                        );
                        (target, Some(DerivedUnit { literal: eq, step }))
                    }
                }
                PackNode::Binary {
                    source,
                    left,
                    right,
                } => {
                    let a = targets.get(left).copied()?;
                    let b = targets.get(right).copied()?;
                    if a.1.is_none() && b.1.is_none() {
                        (source, None)
                    } else {
                        emitter.admit_steps(1)?;
                        let mut premises = Vec::new();
                        premises.try_reserve_exact(2).ok()?;
                        // Cong consumes one occurrence per changed argument;
                        // identical proof ids in two positions are not deduped.
                        for child in [a, b] {
                            if let Some(unit) = child.1 {
                                premises.push(unit.step);
                            }
                        }
                        let TermData::App(symbol, _) = self.ctx.terms.get(source) else {
                            return None;
                        };
                        let symbol = symbol.clone();
                        let sort = self.ctx.terms.sort(source).clone();
                        let target = self.ctx.terms.mk_app(symbol, [a.0, b.0], sort);
                        let eq =
                            self.ctx
                                .terms
                                .mk_app(Symbol::named("="), [source, target], Sort::Bool);
                        let step = emitter.proof.add_rule_step(
                            AletheRule::Cong,
                            vec![eq],
                            premises,
                            Vec::new(),
                        );
                        (target, Some(DerivedUnit { literal: eq, step }))
                    }
                }
            };
            targets.push(result);
        }
        let (pure, transport) = *targets.get(root)?;
        emitter.admit_steps(1 + usize::from(transport.is_some()))?;
        if stop() {
            return None;
        }
        let pure_eq = self
            .ctx
            .terms
            .mk_app(Symbol::named("="), [pure, witness.word], Sort::Bool);
        let step = if self.alethe_dialect() == ay_proof::AletheDialect::Clean
            && ay_proof::recognize_bv_reconstruct_with_progress(
                &self.ctx.terms,
                &[pure_eq],
                &mut |_, _| !stop(),
            ) {
            emitter
                .proof
                .add_rule_step(AletheRule::BvReconstructV1, vec![pure_eq], vec![], vec![])
        } else {
            if stop() {
                return None;
            }
            emitter.proof.add_theory_lemma_with_kind(
                "bv",
                vec![pure_eq],
                TheoryLemmaKind::BvBitBlast,
            )
        };
        if let Some(transport) = transport {
            let unit = self.packing_trans(
                emitter,
                edge.a,
                edge.b,
                transport,
                DerivedUnit {
                    literal: pure_eq,
                    step,
                },
            )?;
            (unit.literal == literal && !stop()).then_some(unit.step)
        } else {
            (pure_eq == literal && !stop()).then_some(step)
        }
    }
}
