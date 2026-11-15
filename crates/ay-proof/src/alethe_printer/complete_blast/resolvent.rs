// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The clause a transported resolution chain carries from link to link.
//!
//! Every link of a chain resolves the running clause with one premise. Done
//! from scratch, a link hashes every literal of the running clause again, so
//! a chain costs the product of its length and its clause width. A direct
//! (unswept) refutation has both long: measured 2026-09-30 on external-codegen's
//! `BSR` row (a 64-deep `ite` chain against its complement, whose root
//! refutes directly in 0.3 s), printing the 35.5 MB document took 84 s, and
//! 70% of that was rehashing a set per link.
//!
//! [`Resolvent`] keeps the clause in order with one mark per variable, so a
//! link costs the premise it reads and the one literal it removes. The first
//! link still goes through [`resolve`], because the chain's first premise is
//! an original clause, which may repeat a literal or carry both polarities of
//! one; every later resolvent has neither, which is what the marks rely on.
//! The literals, their order and every refusal are exactly [`resolve`]'s.

use ay_core::kani_compat::DetHashSet;
use ay_sat::Literal;

/// Links from which a chain is printed as ONE `drup` step (see [`drup_pays`]).
const DRUP_LINKS: usize = 8;

/// Whether a chain of `links` resolutions landing on `literals` literals is
/// printed as one `drup` step — `(step n C :rule drup :premises (..) :args
/// (C))`, which the consumer checks by unit propagation over the premises —
/// rather than as one `resolution` carrying a pivot and a polarity per link.
///
/// The consumer's zero-extension normalizer (clean `carcara_verify/
/// zero_extend.rs`, a 4,000,000-unit budget per certificate) charges every
/// term of every clause and argument, so the pivots cost two units per link
/// and `drup` about two per literal of the clause it repeats. Measured
/// 2026-09-30 on external-codegen's 64-bit `SDIV` definitional rows, whose swept
/// dividers prove about 4,000 lemmas by chains of about 200 links: those
/// chains' pivots were 2.0M of the document's 4.6M units, and the consumer
/// refused it as over budget. A short chain keeps its `resolution`.
pub(super) fn drup_pays(links: usize, literals: usize) -> bool {
    links >= DRUP_LINKS && links > literals.saturating_add(1)
}

/// Resolve `left` (holding the negation of `pivot`) with `right` (holding
/// `pivot`): `left`'s other literals in order, then `right`'s not yet seen.
///
/// Refuses when a SECOND complementary pair would leave the pivot ambiguous:
/// a consumer is free to eliminate the other one, and a document that depends
/// on the choice is not one AY can stand behind.
pub(super) fn resolve(left: &[Literal], right: &[Literal], pivot: Literal) -> Option<Vec<Literal>> {
    if !left.contains(&pivot.negated()) || !right.contains(&pivot) {
        return None;
    }
    let mut seen: DetHashSet<Literal> = DetHashSet::default();
    seen.reserve(left.len() + right.len());
    let mut out = Vec::with_capacity(left.len() + right.len());
    for literal in left {
        if *literal == pivot.negated() {
            continue;
        }
        if seen.insert(*literal) {
            out.push(*literal);
        }
    }
    for literal in right {
        if *literal == pivot {
            continue;
        }
        if seen.insert(*literal) {
            out.push(*literal);
        }
    }
    if out.iter().any(|literal| seen.contains(&literal.negated())) {
        return None;
    }
    Some(out)
}

/// A chain's running clause (see the module documentation). Dropping it
/// clears every mark it set, so one scratch serves every chain.
pub(super) struct Resolvent<'m> {
    lits: Vec<Literal>,
    /// Whether `lits` has been through [`resolve`] (no repeats, no
    /// complementary pair) and `marks` mirrors it.
    marked: bool,
    /// Per variable: 0 absent, 1 positive, 2 negative.
    marks: &'m mut Vec<u8>,
}

fn mark(literal: Literal) -> u8 {
    if literal.is_positive() {
        1
    } else {
        2
    }
}

fn variable(literal: Literal) -> usize {
    (literal.raw() >> 1) as usize
}

impl<'m> Resolvent<'m> {
    /// The chain's first premise, as printed. `marks` must be all zero.
    pub(super) fn new(start: &[Literal], marks: &'m mut Vec<u8>) -> Self {
        Self {
            lits: start.to_vec(),
            marked: false,
            marks,
        }
    }

    pub(super) fn lits(&self) -> &[Literal] {
        &self.lits
    }

    pub(super) fn contains(&self, literal: Literal) -> bool {
        if self.marked {
            self.marks.get(variable(literal)) == Some(&mark(literal))
        } else {
            self.lits.contains(&literal)
        }
    }

    /// Resolve with `right` on `pivot`, as [`resolve`] would.
    pub(super) fn resolve(&mut self, right: &[Literal], pivot: Literal) -> Option<()> {
        if !self.marked {
            self.lits = resolve(&self.lits, right, pivot)?;
            for index in 0..self.lits.len() {
                self.set(self.lits[index]);
            }
            self.marked = true;
            return Some(());
        }
        let negated = pivot.negated();
        if !self.contains(negated) || !right.contains(&pivot) {
            return None;
        }
        let at = self.lits.iter().position(|literal| *literal == negated)?;
        self.lits.remove(at);
        self.marks[variable(negated)] = 0;
        for &literal in right {
            if literal == pivot {
                continue;
            }
            match self.marks.get(variable(literal)).copied().unwrap_or(0) {
                0 => {
                    self.set(literal);
                    self.lits.push(literal);
                }
                present if present == mark(literal) => {}
                // A second complementary pair.
                _ => return None,
            }
        }
        Some(())
    }

    fn set(&mut self, literal: Literal) {
        let index = variable(literal);
        if index >= self.marks.len() {
            self.marks.resize(index + 1, 0);
        }
        self.marks[index] = mark(literal);
    }

    /// The clause, the marks cleared.
    pub(super) fn finish(mut self) -> Vec<Literal> {
        self.clear();
        std::mem::take(&mut self.lits)
    }

    fn clear(&mut self) {
        if self.marked {
            for literal in &self.lits {
                if let Some(slot) = self.marks.get_mut(variable(*literal)) {
                    *slot = 0;
                }
            }
        }
    }
}

impl Drop for Resolvent<'_> {
    fn drop(&mut self) {
        self.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(variable: u32, positive: bool) -> Literal {
        if positive {
            Literal::positive(ay_sat::Variable::new(variable))
        } else {
            Literal::negative(ay_sat::Variable::new(variable))
        }
    }

    /// A chain of links gives [`resolve`]'s clauses, in its order, and
    /// refuses exactly where it does; the marks are left clear.
    #[test]
    fn a_running_resolvent_matches_resolve_link_for_link() {
        let mut marks = Vec::new();
        // The start repeats a literal; its first link normalizes it.
        let start = [lit(1, true), lit(2, false), lit(2, false), lit(3, true)];
        let premises = [
            (
                vec![lit(1, false), lit(4, true), lit(3, true)],
                lit(1, false),
            ),
            (vec![lit(2, true), lit(5, false)], lit(2, true)),
            (
                vec![lit(4, false), lit(6, true), lit(5, false)],
                lit(4, false),
            ),
        ];
        let mut expected = start.to_vec();
        let mut running = Resolvent::new(&start, &mut marks);
        for (premise, pivot) in &premises {
            expected = resolve(&expected, premise, *pivot).unwrap();
            running.resolve(premise, *pivot).unwrap();
            assert_eq!(running.lits(), expected.as_slice());
            assert!(expected.iter().all(|l| running.contains(*l)));
        }
        assert_eq!(running.finish(), expected);
        assert!(marks.iter().all(|m| *m == 0));

        // A second complementary pair is refused by both.
        let mut running = Resolvent::new(&start, &mut marks);
        let (premise, pivot) = &premises[0];
        running.resolve(premise, *pivot).unwrap();
        let clash = vec![lit(2, true), lit(3, false)];
        assert!(resolve(running.lits(), &clash, lit(2, true)).is_none());
        assert!(running.resolve(&clash, lit(2, true)).is_none());
        drop(running);
        assert!(marks.iter().all(|m| *m == 0));
    }
}
