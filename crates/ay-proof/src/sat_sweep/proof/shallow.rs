// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A candidate lemma's first attempt, over the cone cut just below its own
//! gates ([`Sweep::cone_within`]).

use super::*;

/// Operand edges below a lemma's own gates that [`Sweep::prove_shallow`]
/// reads before the whole cone.
const SHALLOW_DEPTH: usize = 1;
/// Conflicts the cut cone's solver call may spend: its problem is a few
/// gates over free operands.
const SHALLOW_CONFLICTS: u64 = 64;

/// What the cut cone of one lemma decided ([`Sweep::prove_shallow`]).
pub(super) enum Shallow {
    Proved(u64),
    /// Nothing was cut: the whole cone is the one to try.
    Whole,
    /// The cut cone did not refute the lemma.
    Cut,
}

impl Sweep<'_, '_> {
    /// [`Self::prove`]'s first attempt: the lemma refuted over the cone cut
    /// [`SHALLOW_DEPTH`] operand edges below its gates, by unit propagation or
    /// a solver call of at most [`SHALLOW_CONFLICTS`] conflicts. A
    /// satisfiable cut cone says nothing (its cut gates are free), so it is
    /// never a counterexample.
    ///
    /// Measured on external-codegen's i128 multiply lowering (gate row 2023): a
    /// padded 128-bit product against its 64-bit limb product, or the rows of
    /// a product whose high operand bits are zero, merge gate by gate, but a
    /// gate's representative is itself unmerged, so the whole cone ran down
    /// its representative's fan-in to the inputs: every lemma paid for the
    /// multiplier below it, and the sweep ran past its wall.
    ///
    /// Under hypotheses (`care.rs`) the cut cone starts from the unit lemmas
    /// of those inside it, as the whole cone does.
    pub(super) fn prove_shallow(&mut self, lemma: &[Literal], roots: &[usize]) -> Shallow {
        let Some((cone, cut)) = self.cone_within(roots, SHALLOW_DEPTH) else {
            return Shallow::Whole;
        };
        if !cut {
            return Shallow::Whole;
        }
        let mut units = self.care_units_inside(&cone);
        units.extend(lemma.iter().map(|lit| (lit.negated(), None)));
        let local = self.local(&cone, false, &units);
        self.lemma_calls += 1;
        if let Some(id) = self
            .propagate_candidate(&local)
            .and_then(|used| self.record_rup(&local, &used, lemma))
        {
            return Shallow::Proved(id);
        }
        match self.solve(local.global.len(), &local.clauses, SHALLOW_CONFLICTS) {
            Some(ResolutionSolveOutcome::Unsat(dag)) => self
                .stitch(&local, &dag, lemma)
                .map_or(Shallow::Cut, Shallow::Proved),
            _ => Shallow::Cut,
        }
    }
}

#[cfg(test)]
#[path = "shallow_tests.rs"]
mod tests;
