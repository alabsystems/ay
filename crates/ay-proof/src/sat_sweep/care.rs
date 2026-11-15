// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Sweeping under the roots' hypotheses.
//!
//! A lemma `H -> (l = r)` often compares two circuits that agree only where
//! its hypotheses `H` hold. external-codegen's `BFM` row 2051 inserts `width` bits of
//! `x7` at `lsb` two ways: `((1 << w) - 1) << l`, and the ARM pseudocode's
//! `DecodeBitMasks` rotation, whose masks equal the first ones only for
//! `1 <= w` and `l + w <= 64`. Swept without its hypotheses, no internal
//! signal of one side equals one of the other, and the closing refutation is
//! the whole miter: measured 2026-09-30, 7.1M resolution hints for the strict
//! checker (against its 4M) and a 101 MB printed document. Swept under them
//! (with `prime.rs` and `alias.rs`), the checker's DAG replays 3.65-3.83M
//! hints, three quarters of them its closing refutation, and the printer's
//! sweep closes over 241 variables and prints 77 MB; Clean verifies the
//! row. More conflicts per checker lemma merge more gates but grow the
//! lemmas faster than the close shrinks (at 1,000, 7.0M hints).
//!
//! The roots imply, by unit propagation alone, the literals that state the
//! hypotheses. Each implied literal is derived as a unit lemma (its reason
//! clause, and the units derived before it), and those whose cone is small
//! are the sweep's HYPOTHESES: simulation reads only the patterns that
//! satisfy all of them (`signature.rs`). A candidate is proved with the
//! units of the hypotheses inside its cone and, when the counterexample that
//! refutes it violates one (`Sweep::outside_care`), again with all of them
//! and their cones. Every lemma so proved is a consequence of the CNF with
//! its roots, which is all the closing refutation needs. Nothing is trusted: the
//! strict checker replays the DAG against that CNF, and the printer's
//! transport carries the root as a literal, as it already does for every step
//! of the closing refutation.
//!
//! Care is taken only where it can matter. Patterns that satisfy the
//! hypotheses must be neither rare (random simulation would see too few of
//! them to form a class: an equality of two free words is never met) nor
//! the rule (a hypothesis nearly every pattern satisfies, like `b != 0`,
//! constrains nothing a sweep can use); otherwise the sweep runs as before.

use super::*;

/// Hypotheses kept at most.
const MAX_HYPOTHESES: usize = 256;
/// Variables in one hypothesis's cone at most: a hypothesis is a side
/// condition over a few inputs, never the miter the roots deny.
const MAX_HYPOTHESIS_CONE: usize = 4_096;
/// Literals the unit propagation from the roots may visit at most.
const MAX_PROPAGATION_WORK: usize = 64_000_000;
/// Random words simulated while care is decided, and then absorbed in
/// place of the sweep's usual four (64 patterns each).
pub(super) const CARE_WORDS: usize = 16;
/// Patterns satisfying the hypotheses, of `CARE_WORDS * 64`, that make care
/// worth taking: at least this many ...
const MIN_CARE_PATTERNS: u32 = 32;
/// ... and at most this share (in 256ths) of them.
const MAX_CARE_SHARE: u32 = 128;

/// A candidate's cone, and the unit clauses its local problem starts from:
/// the hypotheses' unit lemmas, by id (`Sweep::local`).
pub(super) type LemmaCone = (Vec<usize>, Vec<(Literal, Option<u64>)>);

/// The hypotheses a sweep proves its candidates under.
pub(super) struct Care {
    /// Each hypothesis literal, with the derived unit lemma that proves it.
    pub(super) units: Vec<(Literal, u64)>,
    /// Every variable of the hypotheses' cones, the units' own included.
    pub(super) vars: Vec<usize>,
    /// Whether a variable is an input some hypothesis reads.
    pub(super) support: Vec<bool>,
}

impl Care {
    /// The simulation patterns of one word that satisfy every hypothesis.
    pub(super) fn mask(&self, values: &[u64]) -> u64 {
        self.units
            .iter()
            .fold(u64::MAX, |care, &(unit, _)| care & value_of(values, unit))
    }
}

/// The salt of the `word`th random word care is decided on.
pub(super) fn care_salt(word: usize) -> u64 {
    splitmix(0xca7e ^ word as u64)
}

impl Sweep<'_, '_> {
    /// Decide whether to sweep under the roots' hypotheses and, if so,
    /// derive them (see the module documentation). A sweep that does not
    /// take care keeps no step of the attempt.
    pub(super) fn take_care(&mut self) {
        let (mark, next_id) = (self.derived.len(), self.next_id);
        if self.care_under_hypotheses().is_none() {
            for step in self.derived.drain(mark..) {
                self.derived_at.remove(&step.id);
            }
            self.next_id = next_id;
        }
    }

    /// The hypotheses, chosen greedily in the order the roots imply them:
    /// an implied literal with a small cone joins while the patterns can
    /// still satisfy all the chosen ones together. The roots' denial of the
    /// lemma itself (`l != r` under hypotheses the lemma makes true) leaves
    /// no pattern and is never chosen.
    fn care_under_hypotheses(&mut self) -> Option<()> {
        let implied = self.root_implications();
        let implied = implied?;
        // The patterns care is decided on. A candidate every one of them
        // satisfies constrains nothing (a constant's consequence) and is
        // passed over; so is an input's or a constant's own literal.
        let words: Vec<Vec<u64>> = (0..CARE_WORDS)
            .map(|word| {
                let salt = care_salt(word);
                self.simulate(&mut |var| splitmix(salt ^ var as u64))
            })
            .collect();
        let mut candidates: Vec<(Literal, u64, Vec<usize>)> = Vec::new();
        let mut masks: Vec<[u64; CARE_WORDS]> = Vec::new();
        for &(unit, id) in &implied {
            if candidates.len() >= MAX_HYPOTHESES {
                break;
            }
            let var = unit.variable().index();
            if matches!(self.nodes[var], Gate::Input | Gate::Const(_)) {
                continue;
            }
            let mask: [u64; CARE_WORDS] = std::array::from_fn(|word| value_of(&words[word], unit));
            if mask.iter().all(|word| *word == u64::MAX) {
                continue;
            }
            if let Some(cone) = self
                .cone(&[var])
                .filter(|cone| cone.len() <= MAX_HYPOTHESIS_CONE)
            {
                candidates.push((unit, id, cone));
                masks.push(mask);
            }
        }
        if candidates.is_empty() {
            return None;
        }
        let count =
            |words: &[u64; CARE_WORDS]| words.iter().map(|word| word.count_ones()).sum::<u32>();
        let mut joint = [u64::MAX; CARE_WORDS];
        let mut units: Vec<(Literal, u64)> = Vec::new();
        let mut vars: Vec<usize> = Vec::new();
        let mut support = vec![false; self.nodes.len()];
        for ((unit, id, cone), mask) in candidates.into_iter().zip(&masks) {
            let narrowed: [u64; CARE_WORDS] = std::array::from_fn(|word| joint[word] & mask[word]);
            if count(&narrowed) < MIN_CARE_PATTERNS {
                continue;
            }
            joint = narrowed;
            for &member in &cone {
                if matches!(self.nodes[member], Gate::Input) {
                    support[member] = true;
                }
            }
            vars.extend(cone);
            units.push((unit, id));
        }
        let patterns = u32::try_from(CARE_WORDS * 64).ok()?;
        if units.is_empty() || count(&joint).saturating_mul(256) / patterns > MAX_CARE_SHARE {
            return None;
        }
        vars.sort_unstable();
        vars.dedup();
        self.care = Some(Care {
            units,
            vars,
            support,
        });
        Some(())
    }

    /// Unit propagation from the unit roots (and the CNF's other units) over
    /// the whole CNF and the gates' prime clauses (`prime.rs`): each implied
    /// literal with the id of the unit lemma derived for it, in order; `None`
    /// when a root is not a unit, nothing is implied, or propagation
    /// conflicts (a refutation the closing step finds by itself).
    fn root_implications(&mut self) -> Option<Vec<(Literal, u64)>> {
        let count = self.nodes.len();
        if self.roots.iter().any(|&root| self.cnf[root].len() != 1) {
            return None;
        }
        // Every clause propagation reads, by id: the CNF's, then the primes.
        let cnf: &[Vec<Literal>] = self.cnf;
        let primes: Vec<(u64, Vec<Literal>)> = self
            .prime
            .iter()
            .flatten()
            .map(|&id| (id, self.derived[self.derived_at[&id]].clause.clone()))
            .collect();
        let sources: Vec<(u64, &[Literal])> = cnf
            .iter()
            .enumerate()
            .map(|(index, clause)| (index as u64 + 1, clause.as_slice()))
            .chain(primes.iter().map(|(id, clause)| (*id, clause.as_slice())))
            .collect();
        let mut value: Vec<Option<bool>> = vec![None; count];
        // The unit lemma (or unit clause) that proves each assigned variable.
        let mut proof: Vec<u64> = vec![0; count];
        let mut trail: Vec<Literal> = Vec::new();
        // The roots, and every other unit of the CNF (a constant's own
        // clause), start the propagation.
        for &(id, clause) in &sources {
            let [unit] = clause else {
                continue;
            };
            let var = unit.variable().index();
            match value[var] {
                Some(assigned) if assigned == unit.is_positive() => continue,
                Some(_) => return None,
                None => {}
            }
            value[var] = Some(unit.is_positive());
            proof[var] = id;
            trail.push(*unit);
        }
        let mut occurs: Vec<Vec<u32>> = vec![Vec::new(); count];
        for (index, &(_, clause)) in sources.iter().enumerate() {
            for lit in clause {
                occurs[lit.variable().index()].push(u32::try_from(index).ok()?);
            }
        }
        let mut implied = Vec::new();
        let mut work = 0_usize;
        let mut head = 0;
        while head < trail.len() {
            let var = trail[head].variable().index();
            head += 1;
            for &index in &occurs[var] {
                let (id, clause) = sources[index as usize];
                work += clause.len();
                if work > MAX_PROPAGATION_WORK {
                    return (!implied.is_empty()).then_some(implied);
                }
                let mut open: Option<Literal> = None;
                let mut several = false;
                let mut satisfied = false;
                for lit in clause {
                    match value[lit.variable().index()] {
                        Some(assigned) if assigned == lit.is_positive() => {
                            satisfied = true;
                            break;
                        }
                        Some(_) => {}
                        None => match open {
                            None => open = Some(*lit),
                            Some(existing) if existing == *lit => {}
                            Some(_) => several = true,
                        },
                    }
                }
                if satisfied || several {
                    continue;
                }
                let unit = open?;
                let unit_var = unit.variable().index();
                // The unit lemma: the units of the clause's other literals,
                // then the clause itself, which they leave conflicting.
                let mut hints: Vec<u64> = clause
                    .iter()
                    .filter(|lit| lit.variable().index() != unit_var)
                    .map(|lit| proof[lit.variable().index()])
                    .collect();
                hints.sort_unstable();
                hints.dedup();
                hints.push(id);
                let id = self.record_unit(unit, &hints)?;
                value[unit_var] = Some(unit.is_positive());
                proof[unit_var] = id;
                trail.push(unit);
                implied.push((unit, id));
            }
        }
        (!implied.is_empty()).then_some(implied)
    }

    /// `(unit)` as one derived step with these hints, replayed as every
    /// derived step is.
    fn record_unit(&mut self, unit: Literal, hints: &[u64]) -> Option<u64> {
        let (hints, clause) = self.normalized_hints(&[unit], hints)?;
        let id = self.next_id;
        self.next_id += 1;
        self.derived_at.insert(id, self.derived.len());
        self.derived.push(RupStep {
            id,
            clause,
            rup_hints: hints,
        });
        Some(id)
    }

    /// The cone of a candidate over `roots` and the hypotheses it is proved
    /// under: all of them, their cones joining its own, when it reads an
    /// input of theirs; none otherwise. `None` when the cone is not local.
    pub(super) fn lemma_cone(&self, roots: &[usize], full: bool) -> Option<LemmaCone> {
        let mut cone = self.cone(roots)?;
        let Some(care) = self.care.as_ref() else {
            return Some((cone, Vec::new()));
        };
        if !full {
            let units = self.care_units_inside(&cone);
            return Some((cone, units));
        }
        cone.extend_from_slice(&care.vars);
        cone.sort_unstable();
        cone.dedup();
        let units = care.units.iter().map(|&(unit, id)| (unit, Some(id)));
        (cone.len() <= MAX_CONE_VARS).then(|| (cone, units.collect()))
    }

    /// Every hypothesis, as the unit lemma it is; none outside a sweep under
    /// hypotheses.
    pub(super) fn care_units_all(&self) -> Vec<(Literal, Option<u64>)> {
        self.care.as_ref().map_or_else(Vec::new, |care| {
            care.units
                .iter()
                .map(|&(unit, id)| (unit, Some(id)))
                .collect()
        })
    }

    /// The hypotheses already inside the sorted `cone`, as the unit lemmas
    /// they are; none outside a sweep under hypotheses.
    pub(super) fn care_units_inside(&self, cone: &[usize]) -> Vec<(Literal, Option<u64>)> {
        self.care.as_ref().map_or_else(Vec::new, |care| {
            care.units
                .iter()
                .filter(|(unit, _)| cone.binary_search(&unit.variable().index()).is_ok())
                .map(|&(unit, id)| (unit, Some(id)))
                .collect()
        })
    }

    /// Whether a counterexample reads the hypotheses' inputs and violates
    /// them: a pattern the sweep does not care about, refuting nothing.
    pub(super) fn outside_care(&self, pattern: &[(usize, bool)]) -> bool {
        let Some(care) = self.care.as_ref() else {
            return false;
        };
        if !pattern
            .iter()
            .any(|&(var, _)| care.support.get(var).copied().unwrap_or(false))
        {
            return false;
        }
        let assigned: DetHashMap<usize, bool> = pattern.iter().copied().collect();
        let values = self.simulate(&mut |var| match assigned.get(&var) {
            Some(true) => u64::MAX,
            Some(false) => 0,
            None => splitmix(0x0c7e ^ var as u64),
        });
        care.mask(&values) & 1 == 0
    }
}

#[cfg(test)]
#[path = "care_tests.rs"]
mod tests;
