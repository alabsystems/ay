// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Conflict-owned congruence, under the same meter as coefficient checking.
//! No term store mutation, ambient equalities, or unmetered verifier is used.

use std::cmp::Ordering;
use std::mem::size_of;

use super::{FarkasValidationError, ProgressMeter};
use crate::{Symbol, TermData, TermId, TermStore, TheoryLit};

// Match the existing FULL verifier's admission; exceeding it supplies no
// congruence substitutions, rather than increasing its completeness boundary.
const MAX_APPLICATIONS: usize = 4096;

pub(super) struct Congruence {
    nodes: Vec<TermId>,
    parents: Vec<usize>,
}

struct Signature<'a> {
    symbol: &'a Symbol,
    arguments: Vec<usize>,
    application: usize,
}

fn search_work(n: usize) -> usize {
    if n == 0 {
        0
    } else {
        usize::BITS as usize - n.leading_zeros() as usize
    }
}

fn moves(entries: usize, index: usize, extra: usize) -> Result<usize, FarkasValidationError> {
    entries
        .checked_sub(index)
        .and_then(|n| n.checked_add(extra))
        .ok_or(FarkasValidationError::ResourceLimit)
}

fn equality(
    terms: &TermStore,
    literal: &TheoryLit,
    meter: &mut ProgressMeter<'_>,
) -> Result<Option<(TermId, TermId)>, FarkasValidationError> {
    let mut term = literal.term;
    let mut value = literal.value;
    loop {
        meter.charge(1, 0)?;
        if term.index() >= terms.len() {
            return Err(FarkasValidationError::NonArithmeticLiteral { term });
        }
        match terms.get(term) {
            TermData::Not(inner) => {
                term = *inner;
                value = !value;
            }
            TermData::App(Symbol::Named(name), args) => {
                return Ok(match args.as_slice() {
                    &[a, b] if (name == "=" && value) || (name == "distinct" && !value) => {
                        Some((a, b))
                    }
                    _ => None,
                });
            }
            _ => return Ok(None),
        }
    }
}

impl Congruence {
    fn empty() -> Self {
        Self {
            nodes: Vec::new(),
            parents: Vec::new(),
        }
    }

    pub(super) fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    fn index(
        &self,
        term: TermId,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<Option<usize>, FarkasValidationError> {
        meter.charge(search_work(self.nodes.len()), 0)?;
        Ok(self.nodes.binary_search(&term).ok())
    }

    fn root(
        &self,
        mut index: usize,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<usize, FarkasValidationError> {
        loop {
            meter.charge(1, 0)?;
            let parent = self.parents[index];
            if parent == index {
                return Ok(index);
            }
            index = parent;
        }
    }

    fn union(
        &mut self,
        a: usize,
        b: usize,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<bool, FarkasValidationError> {
        let a = self.root(a, meter)?;
        let b = self.root(b, meter)?;
        meter.charge(1, 0)?;
        if a == b {
            return Ok(false);
        }
        // nodes are sorted: this is precisely the old minimum-TermId rule.
        self.parents[a.max(b)] = a.min(b);
        Ok(true)
    }

    pub(super) fn representative(
        &self,
        term: TermId,
        meter: &mut ProgressMeter<'_>,
    ) -> Result<TermId, FarkasValidationError> {
        match self.index(term, meter)? {
            Some(index) => Ok(self.nodes[self.root(index, meter)?]),
            None => Ok(term),
        }
    }

    pub(super) fn build(
        terms: &TermStore,
        conflict: &[TheoryLit],
        meter: &mut ProgressMeter<'_>,
    ) -> Result<Self, FarkasValidationError> {
        // Fixed local container/candidate headers are scratch too. Heap
        // payloads and every growth are separately prepaid by reserve_vec.
        meter.charge(
            1,
            size_of::<Self>() + 4 * size_of::<Vec<TermId>>() + size_of::<Signature<'_>>(),
        )?;
        let mut equalities = Vec::new();
        // ALL positive equalities of the exact whole conflict participate,
        // including zero-weight causes. A disequality never funds a union.
        for literal in conflict {
            if let Some(pair) = equality(terms, literal, meter)? {
                meter.reserve_vec(&mut equalities, 1)?;
                meter.charge(2, 0)?; // insertion and eventual primitive cleanup
                equalities.push(pair);
            }
        }
        if equalities.is_empty() {
            return Ok(Self::empty());
        }

        let mut result = Self::empty();
        let mut pending = Vec::new();
        meter.reserve_vec(&mut pending, conflict.len())?;
        for literal in conflict {
            meter.charge(2, 0)?;
            pending.push(literal.term);
        }
        let mut applications = 0usize;
        while let Some(term) = pending.pop() {
            meter.charge(1, 0)?;
            if term.index() >= terms.len() {
                return Err(FarkasValidationError::NonArithmeticLiteral { term });
            }
            meter.charge(search_work(result.nodes.len()), 0)?;
            let Err(index) = result.nodes.binary_search(&term) else {
                continue;
            };
            meter.reserve_vec(&mut result.nodes, 1)?;
            meter.charge(moves(result.nodes.len(), index, 2)?, 0)?;
            result.nodes.insert(index, term);
            match terms.get(term) {
                TermData::App(_, args) => {
                    applications = applications
                        .checked_add(1)
                        .ok_or(FarkasValidationError::ResourceLimit)?;
                    if applications > MAX_APPLICATIONS {
                        return Ok(Self::empty());
                    }
                    meter.reserve_vec(&mut pending, args.len())?;
                    for &arg in args {
                        meter.charge(2, 0)?;
                        pending.push(arg);
                    }
                }
                TermData::Not(inner) => {
                    meter.reserve_vec(&mut pending, 1)?;
                    meter.charge(2, 0)?;
                    pending.push(*inner);
                }
                TermData::Ite(c, t, e) => {
                    meter.reserve_vec(&mut pending, 3)?;
                    meter.charge(6, 0)?;
                    pending.extend_from_slice(&[*c, *t, *e]);
                }
                _ => {}
            }
        }
        meter.reserve_vec(&mut result.parents, result.nodes.len())?;
        let mut apps = Vec::new();
        meter.reserve_vec(&mut apps, applications)?;
        for (index, &term) in result.nodes.iter().enumerate() {
            meter.charge(3, 0)?;
            result.parents.push(index);
            if matches!(terms.get(term), TermData::App(_, _)) {
                apps.push(index);
            }
        }
        for (a, b) in equalities {
            let a = result
                .index(a, meter)?
                .ok_or(FarkasValidationError::ResourceLimit)?;
            let b = result
                .index(b, meter)?
                .ok_or(FarkasValidationError::ResourceLimit)?;
            result.union(a, b, meter)?;
        }

        loop {
            let mut signatures: Vec<Signature<'_>> = Vec::new();
            meter.reserve_vec(&mut signatures, apps.len())?;
            let mut changed = false;
            for &app in &apps {
                meter.charge(1, 0)?;
                let TermData::App(symbol, arguments) = terms.get(result.nodes[app]) else {
                    unreachable!()
                };
                let mut roots = Vec::new();
                meter.reserve_vec(&mut roots, arguments.len())?;
                for &argument in arguments {
                    let index = result
                        .index(argument, meter)?
                        .ok_or(FarkasValidationError::ResourceLimit)?;
                    let root = result.root(index, meter)?;
                    meter.charge(2, 0)?;
                    roots.push(root);
                }
                let candidate = Signature {
                    symbol,
                    arguments: roots,
                    application: app,
                };
                // A fallible binary search charges every symbol byte/index
                // and argument comparison before the standard slice/string
                // comparisons. No HashMap allocation/hash escapes the meter.
                let mut low = 0;
                let mut high = signatures.len();
                let mut found = None;
                while low < high {
                    meter.charge(1, 0)?;
                    let mid = low + (high - low) / 2;
                    match compare(&signatures[mid], &candidate, meter)? {
                        Ordering::Less => low = mid + 1,
                        Ordering::Greater => high = mid,
                        Ordering::Equal => {
                            found = Some(signatures[mid].application);
                            break;
                        }
                    }
                }
                if let Some(other) = found {
                    changed |= result.union(other, app, meter)?;
                } else {
                    meter.charge(moves(signatures.len(), low, 2)?, 0)?;
                    signatures.insert(low, candidate);
                }
            }
            // Each successful union strictly reduces the finite partition.
            // Signatures are rebuilt after a merge; stale earlier-round keys
            // therefore cannot prevent the least fixed point.
            meter.charge(0, 0)?;
            if !changed {
                break;
            }
        }
        Ok(result)
    }
}

fn compare(
    a: &Signature<'_>,
    b: &Signature<'_>,
    meter: &mut ProgressMeter<'_>,
) -> Result<Ordering, FarkasValidationError> {
    let work = a
        .symbol
        .name()
        .len()
        .checked_add(b.symbol.name().len())
        .and_then(|n| n.checked_add(a.arguments.len()))
        .and_then(|n| n.checked_add(b.arguments.len()))
        .and_then(|n| n.checked_add(1))
        .ok_or(FarkasValidationError::ResourceLimit)?;
    meter.charge(work, 0)?;
    let head = match (a.symbol, b.symbol) {
        (Symbol::Named(a), Symbol::Named(b)) => a.as_str().cmp(b.as_str()),
        (Symbol::Named(_), Symbol::Indexed(_, _)) => Ordering::Less,
        (Symbol::Indexed(_, _), Symbol::Named(_)) => Ordering::Greater,
        (Symbol::Indexed(a, ai), Symbol::Indexed(b, bi)) => {
            meter.charge(
                ai.len()
                    .checked_add(bi.len())
                    .ok_or(FarkasValidationError::ResourceLimit)?,
                0,
            )?;
            a.as_str().cmp(b.as_str()).then_with(|| ai.cmp(bi))
        }
    };
    Ok(head.then_with(|| a.arguments.cmp(&b.arguments)))
}
