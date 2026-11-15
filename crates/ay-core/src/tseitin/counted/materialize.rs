// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! One paid final producer session; no proof-time rewriting or store cloning.
use super::*;

#[derive(Clone, Copy, Default)]
struct SourceEntry {
    known_bool: bool,
    needs_negative: bool,
    negative: Option<TermId>,
}

pub(super) struct Prepared {
    sources: Vec<SourceEntry>,
    variables: Vec<Option<TermId>>,
}

pub(super) fn prepare(
    terms: &mut TermStore,
    data: &Data,
    owner: &CountedAdmission,
) -> Result<Prepared> {
    let mut prepared = Prepared {
        sources: memory::filled(terms.len(), SourceEntry::default(), owner)?,
        variables: memory::filled(
            usize::try_from(data.num_vars)
                .map_err(|_| Error::Unsupported)?
                .checked_add(1)
                .ok_or_else(|| memory::storage(owner))?,
            None,
            owner,
        )?,
    };
    for (index, mapped) in data.term_literals.iter().enumerate() {
        owner.admit(1, 0)?;
        if let Some(literal) = mapped {
            let term = TermId(u32::try_from(index).map_err(|_| Error::Unsupported)?);
            mark(
                &mut prepared.sources,
                terms,
                SourceLit::positive(term),
                owner,
            )?;
            if *literal > 0 && !matches!(terms.get(term), TermData::Not(_)) {
                let slot = prepared
                    .variables
                    .get_mut(*literal as usize)
                    .ok_or(Error::Invalid)?;
                if slot.replace(term).is_some() {
                    return Err(Error::Invalid);
                }
            }
        }
    }
    for step in &data.steps {
        owner.admit(1, 0)?;
        for &literal in &step.clause {
            mark(&mut prepared.sources, terms, literal, owner)?;
        }
    }
    for &root in &data.roots {
        mark(
            &mut prepared.sources,
            terms,
            SourceLit::positive(root),
            owner,
        )?;
    }
    for representative in prepared.variables.iter().skip(1) {
        owner.admit(1, 0)?;
        let term = representative.ok_or(Error::Invalid)?;
        mark(
            &mut prepared.sources,
            terms,
            SourceLit::positive(term).negated(),
            owner,
        )?;
    }
    let mut builder = CountedTermBuilder::new(terms, owner)?;
    for (index, entry) in prepared.sources.iter_mut().enumerate() {
        owner.admit(1, 0)?;
        if entry.needs_negative {
            let term = TermId(u32::try_from(index).map_err(|_| Error::Unsupported)?);
            entry.negative = Some(builder.apply(CountedBuiltin::Not, &[term])?);
        }
    }
    builder.finish()?;
    owner.check()?;
    Ok(prepared)
}

fn mark(
    entries: &mut [SourceEntry],
    terms: &TermStore,
    literal: SourceLit,
    owner: &CountedAdmission,
) -> Result<()> {
    owner.admit(1, 0)?;
    let entry = entries
        .get_mut(literal.term.index())
        .ok_or(Error::Invalid)?;
    if terms.sort(literal.term) != &Sort::Bool {
        return Err(Error::Invalid);
    }
    entry.known_bool = true;
    entry.needs_negative |= !literal.positive;
    Ok(())
}

impl Prepared {
    pub(super) fn source_literal(
        &self,
        literal: SourceLit,
        owner: &CountedAdmission,
    ) -> Result<TermId> {
        owner.admit(1, 0)?;
        let entry = self
            .sources
            .get(literal.term.index())
            .filter(|entry| entry.known_bool)
            .ok_or(Error::Invalid)?;
        if literal.positive {
            Ok(literal.term)
        } else {
            entry.negative.ok_or(Error::Invalid)
        }
    }

    pub(super) fn sat_literal(&self, literal: i32, owner: &CountedAdmission) -> Result<TermId> {
        owner.admit(1, 0)?;
        let variable = literal
            .checked_abs()
            .filter(|id| *id != 0)
            .ok_or(Error::Invalid)?;
        let term = self
            .variables
            .get(variable as usize)
            .copied()
            .flatten()
            .ok_or(Error::Invalid)?;
        self.source_literal(
            SourceLit {
                term,
                positive: literal > 0,
            },
            owner,
        )
    }
}
