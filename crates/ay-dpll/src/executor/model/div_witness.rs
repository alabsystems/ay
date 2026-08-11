// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// One solver-authored value carrier for an under-specified integer
/// division application.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) struct DivWitnessCandidate {
    pub(in crate::executor) witness: TermId,
    pub(in crate::executor) dividend: TermId,
    pub(in crate::executor) divisor: Option<TermId>,
}

/// Exact reserved witness family requested by arithmetic evaluation.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(in crate::executor) enum DivWitnessFamily {
    LiteralDiv,
    LiteralMod,
    LiteralRem,
    SymbolicQuotient,
    SymbolicRemainder,
}

/// Read-only structural index of every reserved div/mod witness in one exact
/// term-store snapshot.
#[derive(Debug, Default)]
pub(in crate::executor) struct DivWitnessIndex {
    literal_div: Vec<DivWitnessCandidate>,
    literal_mod: Vec<DivWitnessCandidate>,
    literal_rem: Vec<DivWitnessCandidate>,
    symbolic_quotient: Vec<DivWitnessCandidate>,
    symbolic_remainder: Vec<DivWitnessCandidate>,
}

impl DivWitnessIndex {
    fn build(terms: &TermStore) -> Self {
        let mut index = Self::default();
        for raw in 0..terms.len() {
            let Ok(raw) = u32::try_from(raw) else {
                break;
            };
            let witness = TermId::new(raw);
            let TermData::Var(name, _) = terms.get(witness) else {
                continue;
            };
            // The producer creates Int variables. Refuse any malformed
            // reserved-name lookalike at another sort instead of treating it
            // as model evidence.
            if terms.sort(witness) != &Sort::Int {
                continue;
            }

            let parsed = if let Some(rest) = name.strip_prefix("__ay_zerodiv_div_") {
                Self::parse_candidate(terms, witness, rest, false)
                    .map(|candidate| (DivWitnessFamily::LiteralDiv, candidate))
            } else if let Some(rest) = name.strip_prefix("__ay_zerodiv_mod_") {
                Self::parse_candidate(terms, witness, rest, false)
                    .map(|candidate| (DivWitnessFamily::LiteralMod, candidate))
            } else if let Some(rest) = name.strip_prefix("__ay_zerodiv_rem_") {
                Self::parse_candidate(terms, witness, rest, false)
                    .map(|candidate| (DivWitnessFamily::LiteralRem, candidate))
            } else if let Some(rest) = name.strip_prefix("__ay_symdiv_q_") {
                Self::parse_candidate(terms, witness, rest, true)
                    .map(|candidate| (DivWitnessFamily::SymbolicQuotient, candidate))
            } else if let Some(rest) = name.strip_prefix("__ay_symdiv_r_") {
                Self::parse_candidate(terms, witness, rest, true)
                    .map(|candidate| (DivWitnessFamily::SymbolicRemainder, candidate))
            } else {
                None
            };

            if let Some((family, candidate)) = parsed {
                index.candidates_mut(family).push(candidate);
            }
        }
        index
    }

    fn parse_candidate(
        terms: &TermStore,
        witness: TermId,
        rest: &str,
        keyed_by_divisor: bool,
    ) -> Option<DivWitnessCandidate> {
        let (dividend, divisor) = if keyed_by_divisor {
            let (dividend, divisor) = rest.split_once('_')?;
            (
                TermId::new(dividend.parse::<u32>().ok()?),
                Some(TermId::new(divisor.parse::<u32>().ok()?)),
            )
        } else {
            (TermId::new(rest.parse::<u32>().ok()?), None)
        };
        if dividend.index() >= terms.len()
            || divisor.is_some_and(|divisor| divisor.index() >= terms.len())
        {
            return None;
        }
        Some(DivWitnessCandidate {
            witness,
            dividend,
            divisor,
        })
    }

    fn candidates_mut(&mut self, family: DivWitnessFamily) -> &mut Vec<DivWitnessCandidate> {
        match family {
            DivWitnessFamily::LiteralDiv => &mut self.literal_div,
            DivWitnessFamily::LiteralMod => &mut self.literal_mod,
            DivWitnessFamily::LiteralRem => &mut self.literal_rem,
            DivWitnessFamily::SymbolicQuotient => &mut self.symbolic_quotient,
            DivWitnessFamily::SymbolicRemainder => &mut self.symbolic_remainder,
        }
    }

    pub(in crate::executor) fn candidates(
        &self,
        family: DivWitnessFamily,
    ) -> &[DivWitnessCandidate] {
        match family {
            DivWitnessFamily::LiteralDiv => &self.literal_div,
            DivWitnessFamily::LiteralMod => &self.literal_mod,
            DivWitnessFamily::LiteralRem => &self.literal_rem,
            DivWitnessFamily::SymbolicQuotient => &self.symbolic_quotient,
            DivWitnessFamily::SymbolicRemainder => &self.symbolic_remainder,
        }
    }
}

/// Bounded, exact-snapshot cache for [`DivWitnessIndex`].
///
/// The index contains only structural `(witness, operand TermId)` metadata;
/// model values are still evaluated afresh and remain covered by
/// `EvalMemoSession` invalidation. Consequently model mutation does not require
/// clearing this cache. The opaque store stamp does cover every structural
/// hazard: append, rollback, compaction, clone, or replacement rebuilds before
/// reuse.
/// Holding the returned `Arc` also makes recursive zero-divisor evaluation
/// re-entrancy-safe: no `RefCell` borrow remains live while operands evaluate.
#[derive(Debug, Default)]
pub(in crate::executor) struct DivWitnessIndexCache {
    cached: std::cell::RefCell<Option<(TermStoreSnapshotStamp, Arc<DivWitnessIndex>)>>,
    #[cfg(test)]
    builds: std::cell::Cell<u64>,
}

impl DivWitnessIndexCache {
    pub(in crate::executor) fn index(&self, terms: &TermStore) -> Arc<DivWitnessIndex> {
        let stamp = terms.snapshot_stamp();
        if let Some(index) = {
            let cached = self.cached.borrow();
            cached
                .as_ref()
                .filter(|(cached_stamp, _)| cached_stamp == &stamp)
                .map(|(_, index)| Arc::clone(index))
        } {
            return index;
        }

        // Build without holding the cache borrow. The scan itself is purely
        // structural and cannot re-enter evaluation; publishing afterward
        // keeps recursive operand evaluation free to borrow the cache.
        let index = Arc::new(DivWitnessIndex::build(terms));
        *self.cached.borrow_mut() = Some((stamp, Arc::clone(&index)));
        #[cfg(test)]
        self.builds.set(self.builds.get().saturating_add(1));
        index
    }

    #[cfg(test)]
    pub(in crate::executor) fn build_count(&self) -> u64 {
        self.builds.get()
    }
}
