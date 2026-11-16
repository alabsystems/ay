// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A clause's derivation by unit propagation, as one resolution chain.
//!
//! Assume every literal of the target clause false and unit-propagate over
//! the premises until one of them is falsified. Resolving that conflict clause
//! backwards along the propagation trail, each step on the literal a premise
//! propagated, cancels every literal that is not one of the target's: what
//! remains is a subset of the target. This is conflict analysis stopped at the
//! assumptions, and it is how a learned clause's recorded antecedents become
//! the explicit resolution steps a checker replays.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_sat::Literal;

/// One resolution in a chain: resolve the accumulator with `premise`, which
/// contains `pivot`; the accumulator contains its negation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Link {
    pub(super) premise: usize,
    pub(super) pivot: Literal,
}

/// A derivation of `result` from `conflict` and the linked premises.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(super) struct Derivation {
    /// The premise falsified first; the chain starts from its clause.
    pub(super) conflict: usize,
    /// The resolutions, in the order the chain applies them.
    pub(super) links: Vec<Link>,
    /// The conclusion: a subset of the target (sorted).
    pub(super) result: Vec<Literal>,
}

impl Derivation {
    /// Every premise node, conflict first.
    pub(super) fn premises(&self) -> impl Iterator<Item = usize> + '_ {
        std::iter::once(self.conflict).chain(self.links.iter().map(|l| l.premise))
    }
}

const NO_REASON: usize = usize::MAX;

/// Reusable propagation state (values are reset after each derivation).
#[derive(Debug, Default)]
pub(super) struct Propagator {
    /// Per variable index: 0 unassigned, 1 true, -1 false.
    value: Vec<i8>,
    /// Per variable index: the premise (index into the current premise list)
    /// that propagated it, or `NO_REASON` for an assumption.
    reason: Vec<usize>,
    /// Literals made true, in order.
    trail: Vec<Literal>,
}

impl Propagator {
    fn val(&self, lit: Literal) -> i8 {
        let v = self.value.get(lit.variable().index()).copied().unwrap_or(0);
        if lit.is_positive() {
            v
        } else {
            -v
        }
    }

    fn assign(&mut self, lit: Literal, reason: usize) {
        let idx = lit.variable().index();
        if self.value.len() <= idx {
            self.value.resize(idx + 1, 0);
            self.reason.resize(idx + 1, NO_REASON);
        }
        self.value[idx] = if lit.is_positive() { 1 } else { -1 };
        self.reason[idx] = reason;
        self.trail.push(lit);
    }

    fn reset(&mut self) {
        for lit in self.trail.drain(..) {
            let idx = lit.variable().index();
            self.value[idx] = 0;
            self.reason[idx] = NO_REASON;
        }
    }

    /// Derive `target` (sorted, deduplicated) from the premise nodes, whose
    /// clauses `lits_of` gives. `None` when unit propagation does not refute
    /// the target's negation over these premises.
    pub(super) fn derive<'n>(
        &mut self,
        target: &[Literal],
        premises: &[usize],
        lits_of: impl Fn(usize) -> Option<&'n [Literal]>,
    ) -> Option<Derivation> {
        let result = self.run(target, premises, &lits_of);
        self.reset();
        result
    }

    fn run<'n>(
        &mut self,
        target: &[Literal],
        premises: &[usize],
        lits_of: &impl Fn(usize) -> Option<&'n [Literal]>,
    ) -> Option<Derivation> {
        let mut nodes: Vec<usize> = premises.to_vec();
        nodes.sort_unstable();
        nodes.dedup();
        let clauses: Vec<&[Literal]> = nodes.iter().map(|&n| lits_of(n)).collect::<Option<_>>()?;
        for &lit in target {
            match self.val(lit) {
                1 => return None, // complementary target literals: a tautology
                -1 => {}
                _ => self.assign(lit.negated(), NO_REASON),
            }
        }
        // Occurrence lists: literal -> premises containing it.
        let mut occ: HashMap<Literal, Vec<usize>> = HashMap::default();
        for (i, c) in clauses.iter().enumerate() {
            for &l in *c {
                occ.entry(l).or_default().push(i);
            }
        }
        let mut false_count = vec![0u32; clauses.len()];
        let mut conflict = None;
        // Initial scan: count literals the assumptions falsified; queue units.
        let mut pending: Vec<usize> = Vec::new();
        for (i, c) in clauses.iter().enumerate() {
            let falsified = c.iter().filter(|&&l| self.val(l) == -1).count();
            false_count[i] = u32::try_from(falsified).unwrap_or(u32::MAX);
            if falsified + 1 >= c.len() {
                pending.push(i);
            }
        }
        let mut head = self.trail.len();
        loop {
            while let Some(i) = pending.pop() {
                match self.examine(clauses[i]) {
                    Examined::Satisfied | Examined::Open => {}
                    Examined::Unit(l) => {
                        self.assign(l, i);
                    }
                    Examined::Falsified => {
                        conflict = Some(i);
                        break;
                    }
                }
            }
            if conflict.is_some() || head >= self.trail.len() {
                break;
            }
            // Each literal made true falsifies its negation's occurrences.
            while head < self.trail.len() {
                let falsified = self.trail[head].negated();
                head += 1;
                if let Some(list) = occ.get(&falsified) {
                    for &i in list {
                        false_count[i] += 1;
                        if false_count[i] as usize + 1 >= clauses[i].len() {
                            pending.push(i);
                        }
                    }
                }
            }
        }
        let conflict = conflict?;
        Some(self.analyze(conflict, &nodes, &clauses, target))
    }

    fn examine(&self, clause: &[Literal]) -> Examined {
        let mut open = None;
        let mut open_count = 0;
        for &l in clause {
            match self.val(l) {
                1 => return Examined::Satisfied,
                -1 => {}
                _ => {
                    open_count += 1;
                    open = Some(l);
                }
            }
        }
        match (open_count, open) {
            (0, _) => Examined::Falsified,
            (1, Some(l)) => Examined::Unit(l),
            _ => Examined::Open,
        }
    }

    /// Resolve the conflict clause backwards along the trail.
    fn analyze(
        &self,
        conflict: usize,
        nodes: &[usize],
        clauses: &[&[Literal]],
        target: &[Literal],
    ) -> Derivation {
        let mut acc: Vec<Literal> = clauses[conflict].to_vec();
        let mut links = Vec::new();
        for &t in self.trail.iter().rev() {
            let reason = self.reason[t.variable().index()];
            if reason == NO_REASON {
                continue;
            }
            let Some(pos) = acc.iter().position(|&l| l == t.negated()) else {
                continue;
            };
            acc.swap_remove(pos);
            for &l in clauses[reason] {
                if l != t && !acc.contains(&l) {
                    acc.push(l);
                }
            }
            links.push(Link {
                premise: nodes[reason],
                pivot: t,
            });
        }
        acc.sort_unstable();
        debug_assert!(
            acc.iter().all(|l| target.binary_search(l).is_ok()),
            "a unit-propagation derivation concludes a subset of its target"
        );
        Derivation {
            conflict: nodes[conflict],
            links,
            result: acc,
        }
    }
}

enum Examined {
    Satisfied,
    Open,
    Unit(Literal),
    Falsified,
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lit(d: i32) -> Literal {
        Literal::from_dimacs(d)
    }

    fn sorted(v: &[i32]) -> Vec<Literal> {
        let mut out: Vec<Literal> = v.iter().map(|&d| lit(d)).collect();
        out.sort_unstable();
        out
    }

    #[test]
    fn a_learned_clause_becomes_a_resolution_chain() {
        // (a ∨ b), (¬b ∨ c), (¬c ∨ a ∨ d) ⊢ (a ∨ d)
        let clauses = [sorted(&[1, 2]), sorted(&[-2, 3]), sorted(&[-3, 1, 4])];
        let mut p = Propagator::default();
        let target = sorted(&[1, 4]);
        let d = p
            .derive(&target, &[0, 1, 2], |n| clauses.get(n).map(Vec::as_slice))
            .expect("RUP derivation");
        assert!(d.result.iter().all(|l| target.contains(l)));
        assert_eq!(d.links.len(), 2, "{d:?}");
        // The state is reset: a second derivation starts clean.
        let again = p.derive(&target, &[0, 1, 2], |n| clauses.get(n).map(Vec::as_slice));
        assert_eq!(again, Some(d));
    }

    #[test]
    fn missing_antecedents_are_reported() {
        let clauses = [sorted(&[1, 2]), sorted(&[-2, 3])];
        let mut p = Propagator::default();
        assert!(p
            .derive(&sorted(&[1]), &[0, 1], |n| clauses
                .get(n)
                .map(Vec::as_slice))
            .is_none());
    }

    #[test]
    fn the_empty_clause_from_complementary_units() {
        let clauses = [sorted(&[1]), sorted(&[-1])];
        let mut p = Propagator::default();
        let d = p
            .derive(&[], &[0, 1], |n| clauses.get(n).map(Vec::as_slice))
            .expect("refutation");
        assert_eq!(d.result.as_slice(), &[] as &[Literal]);
        assert_eq!(d.links.len(), 1);
    }
}
