// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use scan::{ArrayKind, ArrayShape, Source};

mod congruence;

pub(super) struct Expanded {
    pub(super) reads: Vec<Read>,
    pub(super) steps: Vec<Step>,
    pub(super) free: Vec<Unresolved>,
}

struct Expansion<'a, 'store, 'owner> {
    builder: CountedTermBuilder<'store, 'owner>,
    owner: &'owner CountedAdmission,
    source: &'a Source,
    seen: DetHashMap<(TermId, TermId), usize>,
    out: Expanded,
}

pub(super) fn run(
    terms: &mut TermStore,
    source: &Source,
    owner: &CountedAdmission,
) -> Result<Expanded> {
    let mut expansion = Expansion {
        builder: CountedTermBuilder::new(terms, owner)?,
        owner,
        source,
        seen: DetHashMap::default(),
        out: Expanded {
            reads: Vec::new(),
            steps: Vec::new(),
            free: Vec::new(),
        },
    };
    for &(array, index) in &source.requests {
        owner.admit(1, 0)?;
        expansion.request(array, index)?;
    }
    let mut cursor = 0;
    while cursor < expansion.out.reads.len() {
        owner.admit(1, 0)?;
        expansion.expand(cursor)?;
        cursor += 1;
    }
    expansion.free_congruence()?;
    let Expansion {
        builder, seen, out, ..
    } = expansion;
    builder.finish()?;
    drop(seen);
    owner.check()?;
    Ok(out)
}

impl Expansion<'_, '_, '_> {
    fn shape(&self, array: TermId) -> Result<ArrayShape> {
        self.owner.admit(1, 0)?;
        self.source
            .shapes
            .get(array.index())
            .copied()
            .flatten()
            .ok_or(Error::Invalid)
    }

    fn request(&mut self, array: TermId, index: TermId) -> Result<usize> {
        self.owner.admit(1, 0)?;
        if let Some(&existing) = self.seen.get(&(array, index)) {
            return Ok(existing);
        }
        let shape = self.shape(array)?;
        let select = self
            .builder
            .apply(CountedBuiltin::Select, &[array, index])?;
        let next = self.out.reads.len();
        memory::map(&mut self.seen, self.owner)?;
        memory::push(
            &mut self.out.reads,
            Read {
                array,
                index,
                select,
                index_sort: shape.index,
                element_sort: shape.element,
            },
            self.owner,
        )?;
        self.seen.insert((array, index), next);
        Ok(next)
    }

    fn expand(&mut self, index: usize) -> Result<()> {
        let read = self.out.reads[index];
        match self.shape(read.array)?.kind {
            ArrayKind::Free => memory::push(
                &mut self.out.free,
                Unresolved::FreeRead { read: index },
                self.owner,
            ),
            ArrayKind::Store {
                base,
                index: at,
                value,
            } => self.store(index, read, base, at, value),
            ArrayKind::Const { fill } => {
                let equality = self
                    .builder
                    .apply(CountedBuiltin::Eq, &[read.select, fill])?;
                self.emit(
                    Derivation::ConstFill {
                        read: index,
                        array: read.array,
                        fill,
                    },
                    None,
                    equality,
                )
            }
            ArrayKind::Ite {
                condition,
                then_array,
                else_array,
            } => self.ite(index, read, condition, then_array, else_array),
        }
    }

    fn store(
        &mut self,
        index: usize,
        read: Read,
        base: TermId,
        at: TermId,
        value: TermId,
    ) -> Result<()> {
        // No identical-index shortcut: raw counted input was not simplified.
        // Both source guards and the exact parent read remain in the ledger.
        let base_read = self.request(base, read.index)?;
        let parent = self.out.reads[base_read].select;
        let guard = self.builder.apply(CountedBuiltin::Eq, &[at, read.index])?;
        let not_guard = self.builder.apply(CountedBuiltin::Not, &[guard])?;
        let hit = self
            .builder
            .apply(CountedBuiltin::Eq, &[read.select, value])?;
        let miss = self
            .builder
            .apply(CountedBuiltin::Eq, &[read.select, parent])?;
        self.emit(
            Derivation::Row1 {
                read: index,
                store: read.array,
                write_index: at,
                value,
            },
            Some(not_guard),
            hit,
        )?;
        self.emit(
            Derivation::Row2 {
                read: index,
                store: read.array,
                base_read,
            },
            Some(guard),
            miss,
        )
    }

    fn ite(
        &mut self,
        index: usize,
        read: Read,
        condition: TermId,
        then_array: TermId,
        else_array: TermId,
    ) -> Result<()> {
        let then_read = self.request(then_array, read.index)?;
        let else_read = self.request(else_array, read.index)?;
        let then_select = self.out.reads[then_read].select;
        let else_select = self.out.reads[else_read].select;
        let not_condition = self.builder.apply(CountedBuiltin::Not, &[condition])?;
        let yes = self
            .builder
            .apply(CountedBuiltin::Eq, &[read.select, then_select])?;
        let no = self
            .builder
            .apply(CountedBuiltin::Eq, &[read.select, else_select])?;
        // Retain the precise intermediate terms before CNF seals the store:
        // branch projection plus select congruence resolve to each final row.
        // The final row itself is NOT mislabeled IteBranchProjection.
        let then_eq = self
            .builder
            .apply(CountedBuiltin::Eq, &[read.array, then_array])?;
        let then_not = self.builder.apply(CountedBuiltin::Not, &[then_eq])?;
        let else_eq = self
            .builder
            .apply(CountedBuiltin::Eq, &[read.array, else_array])?;
        let else_not = self.builder.apply(CountedBuiltin::Not, &[else_eq])?;
        self.emit(
            Derivation::IteThen {
                read: index,
                array: read.array,
                condition,
                branch_read: then_read,
                array_equality: then_eq,
                not_array_equality: then_not,
            },
            Some(not_condition),
            yes,
        )?;
        self.emit(
            Derivation::IteElse {
                read: index,
                array: read.array,
                condition,
                branch_read: else_read,
                array_equality: else_eq,
                not_array_equality: else_not,
            },
            Some(condition),
            no,
        )
    }

    fn emit(
        &mut self,
        origin: Derivation,
        guard: Option<TermId>,
        conclusion: TermId,
    ) -> Result<()> {
        let (literals, len) = match guard {
            Some(guard) => ([guard, conclusion], 2),
            None => ([conclusion, conclusion], 1),
        };
        memory::push(
            &mut self.out.steps,
            Step {
                origin,
                literals,
                len,
            },
            self.owner,
        )
    }
}
