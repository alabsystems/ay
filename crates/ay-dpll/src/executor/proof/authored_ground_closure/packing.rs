// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded full-width packing proposals, justified through earlier byte classes.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::term::TermStoreSnapshotStamp;
use ay_frontend::{Context, SourceContextStamp};
use num_traits::ToPrimitive;

use super::slice::MAX_MEMBERS_PER_SITE;
use super::*;

#[derive(Clone, Copy)]
pub(super) enum PackNode {
    Fixed(TermId),
    Piece(usize),
    Unary {
        source: TermId,
        child: usize,
    },
    Binary {
        source: TermId,
        left: usize,
        right: usize,
    },
}

#[derive(Clone, Copy)]
pub(super) struct PackPiece {
    pub(super) source: TermId,
    pub(super) high: u32,
    pub(super) low: u32,
}

pub(super) struct PackSite {
    pub(super) source: TermId,
    pub(super) width: u32,
    pub(super) nodes: Vec<PackNode>,
    pub(super) pieces: Vec<PackPiece>,
}

#[derive(Clone, Copy, PartialEq, Eq)]
pub(super) struct PackMember {
    pub(super) term: TermId,
    pub(super) word: TermId,
    high: u32,
    low: u32,
}

pub(super) struct PackingWitness {
    pub(super) site: usize,
    pub(super) word: TermId,
    pub(super) members: Vec<PackMember>,
}

#[derive(Default)]
pub(super) struct PackingState {
    stamp: Option<(SourceContextStamp, TermStoreSnapshotStamp)>,
    observed: usize,
    pub(super) sites: Vec<PackSite>,
    complete: DetHashSet<TermId>,
    pure_words: DetHashMap<TermId, bool>,
    pub(super) witnesses: Vec<PackingWitness>,
}

impl PackingState {
    pub(super) fn word_is_pure(&self, word: TermId) -> bool {
        self.pure_words.get(&word) == Some(&true)
    }
    pub(super) fn current(&self, ctx: &Context) -> bool {
        self.stamp.as_ref().is_some_and(|(source, terms)| {
            source == &ctx.source_context_stamp() && terms.is_append_only_prefix_of(&ctx.terms)
        })
    }

    /// An unused state may be unbound; a retired binding is never ignored.
    pub(super) fn current_or_unbound(&self, ctx: &Context) -> bool {
        self.current(ctx)
            || (self.stamp.is_none()
                && self.observed == 0
                && self.sites.is_empty()
                && self.complete.is_empty()
                && self.pure_words.is_empty()
                && self.witnesses.is_empty())
    }

    fn bind(&mut self, ctx: &Context) -> Option<()> {
        if self.stamp.is_none() {
            self.stamp = Some((ctx.source_context_stamp(), ctx.terms.snapshot_stamp()));
        }
        self.current(ctx).then_some(())
    }
}

struct Shape<'t, 's> {
    terms: &'t TermStore,
    stop: &'s dyn Fn() -> bool,
    width: u32,
    coverage: u128,
    nodes: Vec<PackNode>,
    pieces: Vec<PackPiece>,
}

impl Shape<'_, '_> {
    fn push(&mut self, node: PackNode, work: &mut SharedGroundWork) -> Option<usize> {
        work.spend(1)?;
        if self.nodes.len() >= MAX_NODES || (self.stop)() {
            return None;
        }
        self.nodes.try_reserve(1).ok()?;
        let index = self.nodes.len();
        self.nodes.push(node);
        Some(index)
    }

    fn walk(
        &mut self,
        term: TermId,
        shift: u32,
        depth: usize,
        work: &mut SharedGroundWork,
    ) -> Option<Option<usize>> {
        work.spend(1)?;
        if (self.stop)() || depth > goal::MAX_GOAL_DEPTH {
            return None;
        }
        if self.terms.entry_stamp(term).is_none()
            || self.terms.sort(term).bitvec_width() != Some(self.width)
        {
            return Some(None);
        }
        match self.terms.get(term) {
            TermData::Const(Constant::BitVec { value, width })
                if *width == self.width && value.sign() == num_bigint::Sign::NoSign =>
            {
                Some(Some(self.push(PackNode::Fixed(term), work)?))
            }
            TermData::App(Symbol::Named(name), args) if name == "bvor" => {
                // Fixed arity bounds every plan/assembly child slot, even for
                // adversarial DAGs with many repeated argument occurrences.
                let &[left, right] = args.as_slice() else {
                    return Some(None);
                };
                let Some(left) = self.walk(left, shift, depth + 1, work)? else {
                    return Some(None);
                };
                let Some(right) = self.walk(right, shift, depth + 1, work)? else {
                    return Some(None);
                };
                Some(Some(self.push(
                    PackNode::Binary {
                        source: term,
                        left,
                        right,
                    },
                    work,
                )?))
            }
            TermData::App(Symbol::Named(name), args) if name == "bvshl" => {
                let &[value, amount] = args.as_slice() else {
                    return Some(None);
                };
                if self.terms.entry_stamp(amount).is_none()
                    || self.terms.sort(amount).bitvec_width() != Some(self.width)
                {
                    return Some(None);
                }
                let TermData::Const(Constant::BitVec {
                    value: literal,
                    width,
                }) = self.terms.get(amount)
                else {
                    return Some(None);
                };
                let Some(amount_value) = literal.to_u32().filter(|n| *n < self.width) else {
                    return Some(None);
                };
                if *width != self.width {
                    return Some(None);
                }
                let Some(shift) = shift.checked_add(amount_value).filter(|n| *n < self.width)
                else {
                    return Some(None);
                };
                let Some(left) = self.walk(value, shift, depth + 1, work)? else {
                    return Some(None);
                };
                let right = self.push(PackNode::Fixed(amount), work)?;
                Some(Some(self.push(
                    PackNode::Binary {
                        source: term,
                        left,
                        right,
                    },
                    work,
                )?))
            }
            TermData::App(Symbol::Indexed(name, indices), args) if name == "zero_extend" => {
                let (&[extra], &[source]) = (indices.as_slice(), args.as_slice()) else {
                    return Some(None);
                };
                let Some(width) = self
                    .terms
                    .entry_stamp(source)
                    .and_then(|_| self.terms.sort(source).bitvec_width())
                    .filter(|n| *n > 0)
                else {
                    return Some(None);
                };
                if width.checked_add(extra) != Some(self.width)
                    || shift.checked_add(width).is_none_or(|end| end > self.width)
                {
                    return Some(None);
                }
                let mask = (u128::MAX >> (128 - width)) << shift;
                if self.coverage & mask != 0 {
                    return Some(None);
                }
                self.coverage |= mask;
                work.spend(1)?;
                self.pieces.try_reserve(1).ok()?;
                let piece = self.pieces.len();
                self.pieces.push(PackPiece {
                    source,
                    high: shift + width - 1,
                    low: shift,
                });
                let child = self.push(PackNode::Piece(piece), work)?;
                Some(Some(self.push(
                    PackNode::Unary {
                        source: term,
                        child,
                    },
                    work,
                )?))
            }
            _ => Some(None),
        }
    }
}

fn parse_site(
    terms: &TermStore,
    source: TermId,
    work: &mut SharedGroundWork,
    stop: &dyn Fn() -> bool,
) -> Option<Option<PackSite>> {
    let Some(width) = terms
        .sort(source)
        .bitvec_width()
        .filter(|n| (1..=128).contains(n))
    else {
        return Some(None);
    };
    if !matches!(terms.get(source), TermData::App(Symbol::Named(name), args) if name == "bvor" && args.len()==2)
    {
        return Some(None);
    }
    let mut shape = Shape {
        terms,
        stop,
        width,
        coverage: 0,
        nodes: Vec::new(),
        pieces: Vec::new(),
    };
    let Some(root) = shape.walk(source, 0, 0, work)? else {
        return Some(None);
    };
    if shape.coverage != u128::MAX >> (128 - width)
        || shape.pieces.is_empty()
        || root + 1 != shape.nodes.len()
    {
        return Some(None);
    }
    Some(Some(PackSite {
        source,
        width,
        nodes: shape.nodes,
        pieces: shape.pieces,
    }))
}

pub(super) fn extract_member(terms: &TermStore, term: TermId) -> Option<PackMember> {
    terms.entry_stamp(term)?;
    let TermData::App(Symbol::Indexed(name, indices), args) = terms.get(term) else {
        return None;
    };
    let (&[high, low], &[word]) = (indices.as_slice(), args.as_slice()) else {
        return None;
    };
    let width = terms
        .entry_stamp(word)
        .and_then(|_| terms.sort(word).bitvec_width())?;
    (name == "extract"
        && low <= high
        && high < width
        && terms.sort(term).bitvec_width() == Some(high - low + 1))
    .then_some(PackMember {
        term,
        word,
        high,
        low,
    })
}

fn pure_word(
    terms: &TermStore,
    word: TermId,
    cache: &mut DetHashMap<TermId, bool>,
    work: &mut SharedGroundWork,
    stop: &dyn Fn() -> bool,
) -> Option<bool> {
    if let Some(&pure) = cache.get(&word) {
        return Some(pure);
    }
    let mut pending = Vec::new();
    work.spend(1)?;
    pending.try_reserve(1).ok()?;
    pending.push(word);
    let mut seen = DetHashSet::default();
    let mut pure = true;
    while let Some(term) = pending.pop() {
        work.spend(1)?;
        if stop() {
            return None;
        }
        if seen.contains(&term) {
            continue;
        }
        if seen.len() >= MAX_NODES {
            return None;
        }
        seen.try_reserve(1).ok()?;
        seen.insert(term);
        if terms.entry_stamp(term).is_none()
            || !matches!(terms.sort(term), Sort::Bool | Sort::BitVec(_))
        {
            pure = false;
            break;
        }
        match terms.get(term) {
            TermData::Var(..) | TermData::Const(Constant::Bool(_) | Constant::BitVec { .. }) => {}
            TermData::App(_, args) => {
                work.spend(args.len())?;
                pending.try_reserve(args.len()).ok()?;
                pending.extend(args.iter().copied());
            }
            TermData::Not(inner) => {
                work.spend(1)?;
                pending.try_reserve(1).ok()?;
                pending.push(*inner);
            }
            TermData::Ite(c, t, e) => {
                work.spend(3)?;
                pending.try_reserve(3).ok()?;
                pending.extend([*c, *t, *e]);
            }
            _ => {
                pure = false;
                break;
            }
        }
    }
    if cache.len() >= MAX_NODES {
        return None;
    }
    cache.try_reserve(1).ok()?;
    cache.insert(word, pure);
    Some(pure)
}

impl Executor {
    pub(super) fn add_ground_packing_edges(
        &mut self,
        closure: &mut GroundClosure,
        state: &mut PackingState,
        proposals: &mut usize,
        work: &mut SharedGroundWork,
    ) -> Option<()> {
        if *proposals == 0 {
            return Some(());
        }
        state.bind(&self.ctx)?;
        let stop = self.make_proof_assembly_should_stop();
        while state.observed < closure.nodes().len() {
            work.spend(1)?;
            if stop() {
                return None;
            }
            let source = closure.nodes()[state.observed];
            if let Some(site) = parse_site(&self.ctx.terms, source, work, &stop)? {
                state.sites.try_reserve(1).ok()?;
                state.sites.push(site);
            }
            state.observed += 1;
        }
        if state.sites.is_empty() {
            return Some(());
        }
        work.spend(closure.nodes().len())?;
        let mut members: DetHashMap<usize, Vec<PackMember>> = DetHashMap::default();
        for &term in closure.nodes() {
            if stop() {
                return None;
            }
            if let Some(member) = extract_member(&self.ctx.terms, term) {
                let class = closure.class(term)?;
                members.try_reserve(1).ok()?;
                let entries = members.entry(class).or_default();
                if entries.len() < MAX_MEMBERS_PER_SITE {
                    entries.try_reserve(1).ok()?;
                    entries.push(member);
                }
            }
        }
        // Class-keyed scratch describes this immutable view. Collect all
        // proposals before merging; never cache a changing representative.
        let mut pending = Vec::new();
        for site_index in 0..state.sites.len() {
            work.spend(1)?;
            if stop() {
                return None;
            }
            if pending.len() >= *proposals {
                break;
            }
            let site = &state.sites[site_index];
            if state.complete.contains(&site.source) {
                continue;
            }
            let first = site.pieces.first()?;
            let Some(candidates) = members.get(&closure.class(first.source)?) else {
                continue;
            };
            let mut chosen = None;
            for candidate in candidates {
                work.spend(1)?;
                let word = candidate.word;
                if candidate.high != first.high
                    || candidate.low != first.low
                    || self.ctx.terms.sort(word).bitvec_width() != Some(site.width)
                {
                    continue;
                }
                if !pure_word(&self.ctx.terms, word, &mut state.pure_words, work, &stop)? {
                    continue;
                }
                work.spend(site.pieces.len())?;
                let mut found = Vec::new();
                found.try_reserve_exact(site.pieces.len()).ok()?;
                for piece in &site.pieces {
                    let mut matched = None;
                    if let Some(entries) = members.get(&closure.class(piece.source)?) {
                        for &member in entries {
                            work.spend(1)?;
                            if stop() {
                                return None;
                            }
                            if member.high == piece.high
                                && member.low == piece.low
                                && closure.same_class(member.word, word)
                                && self.ctx.terms.sort(member.word).bitvec_width()
                                    == Some(site.width)
                                && (piece.high + 1 != site.width
                                    || piece.low != 0
                                    || closure.same_class(piece.source, word))
                            {
                                matched = Some(member);
                                break;
                            }
                        }
                    }
                    let Some(member) = matched else { break };
                    found.push(member);
                }
                if found.len() == site.pieces.len() {
                    chosen = Some((word, found));
                    break;
                }
            }
            let Some((word, found)) = chosen else {
                continue;
            };
            if closure.same_class(site.source, word) {
                state.complete.try_reserve(1).ok()?;
                state.complete.insert(site.source);
                continue;
            }
            if closure.edges().len().checked_add(pending.len())? >= MAX_EDGES
                || state.witnesses.len().checked_add(pending.len())? >= MAX_EDGES
            {
                return None;
            }
            work.spend(1)?;
            pending.try_reserve(1).ok()?;
            pending.push(PackingWitness {
                site: site_index,
                word,
                members: found,
            });
        }
        for proposal in pending {
            work.spend(1)?;
            if stop() {
                return None;
            }
            let source = state.sites.get(proposal.site)?.source;
            if closure.same_class(source, proposal.word) {
                state.complete.try_reserve(1).ok()?;
                state.complete.insert(source);
                continue;
            }
            state.witnesses.try_reserve(1).ok()?;
            state.complete.try_reserve(1).ok()?;
            let witness = state.witnesses.len();
            let word = proposal.word;
            state.witnesses.push(proposal);
            closure
                .merge(source, word, EdgeReason::Packing(witness))
                .then_some(())?;
            state.complete.insert(source);
            *proposals -= 1;
        }
        Some(())
    }
}
