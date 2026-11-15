// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Derived facts: offering a bound, relaxing a row onto one kept part, and
//! reconstructing the chain the final contradiction reaches.

use super::{
    classes, BTreeMap, BTreeSet, BigInt, BigRational, Chain, ChainCut, Coeffs, Fact, Integer,
    Offer, One, Search, Signed, TermId, Zero, MAX_CHAIN_CUTS,
};

/// A relaxed piece's contribution: `(U, parts)` bounds the piece above by `U`
/// using the listed facts with positive multipliers.
type Piece = (BigInt, Vec<(usize, BigInt)>);

impl Search<'_> {
    /// Offer `kept ≥ rhs` (derived from base row `row` plus `parts`) as a
    /// bound on the primitive form of `kept`.
    pub(super) fn offer(
        &mut self,
        kept: Coeffs,
        rhs: BigInt,
        row: usize,
        parts: Vec<(usize, BigInt)>,
    ) -> Offer {
        let content = kept
            .values()
            .fold(BigInt::zero(), |gcd, coeff| gcd.gcd(&coeff.abs()));
        if content.is_zero() {
            return Offer::Stale;
        }
        let upper = kept.values().next().is_some_and(Signed::is_negative);
        let divisor = if upper { -&content } else { content.clone() };
        let form: Coeffs = kept
            .iter()
            .map(|(atom, coeff)| (*atom, coeff / &divisor))
            .collect();
        let bound = rhs.div_ceil(&content);
        let cut = !rhs.is_multiple_of(&content);
        let slot = usize::from(upper);
        let entry = self.store.entry(form.clone()).or_default();
        if entry[slot].is_some_and(|existing| self.facts[existing].bound >= bound) {
            return Offer::Stale;
        }
        let index = self.facts.len();
        entry[slot] = Some(index);
        let other = entry[1 - slot];
        self.facts.push(Fact {
            form,
            upper,
            bound: bound.clone(),
            row,
            parts,
            divisor: content,
            cut,
        });
        match other {
            // `P ≥ lower` and `−P ≥ upper` cross when `lower + upper > 0`.
            Some(other) if (&self.facts[other].bound + &bound).is_positive() => {
                if upper {
                    Offer::Contradiction(other, index)
                } else {
                    Offer::Contradiction(index, other)
                }
            }
            _ => Offer::Improved,
        }
    }

    /// Relax base row `row` onto the kept atoms `kept`: bound every other
    /// atom's contribution above by derived facts and offer the rest.
    pub(super) fn relax(&mut self, row: usize, kept: &[TermId]) -> Offer {
        let base = &self.base[row];
        self.work = self.work.saturating_add(base.form.len());
        let full_classes = classes(&base.form);
        let mut relaxed: BTreeMap<BigInt, Vec<(TermId, BigInt)>> = BTreeMap::new();
        for (atom, coeff) in &base.form {
            if !kept.contains(atom) {
                relaxed
                    .entry(coeff.abs())
                    .or_default()
                    .push((*atom, coeff.clone()));
            }
        }
        let mut total = BigInt::zero();
        let mut parts = Vec::new();
        for (magnitude, atoms) in &relaxed {
            let whole_class = full_classes
                .get(magnitude)
                .is_some_and(|class| class.len() == atoms.len() && atoms.len() > 1);
            let singles = self.singleton_pieces(atoms);
            let class = if whole_class {
                self.class_piece(magnitude, atoms)
            } else {
                None
            };
            // The tighter bound; on a tie, the one citing fewer cuts (a
            // shorter chain), then the single class fact.
            let best = match (singles, class) {
                (Some(singles), Some(class))
                    if (&singles.0, self.cut_parts(&singles.1))
                        < (&class.0, self.cut_parts(&class.1)) =>
                {
                    singles
                }
                (_, Some(class)) => class,
                (Some(singles), None) => singles,
                (None, None) => return Offer::Stale,
            };
            total += best.0;
            parts.extend(best.1);
        }
        let kept_form: Coeffs = base
            .form
            .iter()
            .filter(|(atom, _)| kept.contains(atom))
            .map(|(atom, coeff)| (*atom, coeff.clone()))
            .collect();
        let rhs = &base.bound - total;
        self.offer(kept_form, rhs, row, parts)
    }

    fn cut_parts(&self, parts: &[(usize, BigInt)]) -> usize {
        parts
            .iter()
            .filter(|(fact, _)| self.facts[*fact].cut)
            .count()
    }

    /// Bound `Σ a_x·x` above atom by atom.
    fn singleton_pieces(&self, atoms: &[(TermId, BigInt)]) -> Option<Piece> {
        let mut total = BigInt::zero();
        let mut parts = Vec::with_capacity(atoms.len());
        for (atom, coeff) in atoms {
            let form = Coeffs::from([(*atom, BigInt::one())]);
            let (bound, part) = self.piece_upper(coeff, &form)?;
            total += bound;
            parts.push(part);
        }
        Some((total, parts))
    }

    /// Bound a whole class `|a|·Σ ±x` above through a fact on its own
    /// primitive form.
    fn class_piece(&self, magnitude: &BigInt, atoms: &[(TermId, BigInt)]) -> Option<Piece> {
        let flip = atoms.first().is_some_and(|(_, coeff)| coeff.is_negative());
        let form: Coeffs = atoms
            .iter()
            .map(|(atom, coeff)| {
                let unit = coeff / magnitude;
                (*atom, if flip { -unit } else { unit })
            })
            .collect();
        let scale = if flip { -magnitude } else { magnitude.clone() };
        let (bound, part) = self.piece_upper(&scale, &form)?;
        Some((bound, vec![part]))
    }

    /// An upper bound on `scale·form` for a primitive `form`, and the fact
    /// (with its positive multiplier) that proves it.
    fn piece_upper(&self, scale: &BigInt, form: &Coeffs) -> Option<(BigInt, (usize, BigInt))> {
        let slots = self.store.get(form)?;
        if scale.is_positive() {
            // `−form ≥ b` gives `scale·form ≤ −scale·b`.
            let fact = slots[1]?;
            Some((-(scale * &self.facts[fact].bound), (fact, scale.clone())))
        } else {
            // `form ≥ b` gives `scale·form ≤ scale·b`.
            let fact = slots[0]?;
            Some((scale * &self.facts[fact].bound, (fact, -scale)))
        }
    }

    /// The cut chain the crossing facts `lower` and `upper` reach.
    pub(super) fn chain(&self, row_count: usize, lower: usize, upper: usize) -> Option<Chain> {
        let mut reached = BTreeSet::new();
        let mut stack = vec![lower, upper];
        while let Some(fact) = stack.pop() {
            if reached.insert(fact) {
                stack.extend(self.facts[fact].parts.iter().map(|(part, _)| *part));
            }
        }
        let cut_facts: Vec<usize> = reached
            .iter()
            .copied()
            .filter(|&fact| self.facts[fact].cut)
            .collect();
        if cut_facts.len() > MAX_CHAIN_CUTS {
            return None;
        }
        let position: BTreeMap<usize, usize> = cut_facts
            .iter()
            .enumerate()
            .map(|(position, &fact)| (fact, position))
            .collect();
        let mut derived: BTreeMap<usize, Derivation> = BTreeMap::new();
        for &fact in &reached {
            let raw = self.raw_derivation(fact, &position, &derived);
            let _ = derived.insert(fact, raw);
        }
        let cuts = cut_facts
            .iter()
            .enumerate()
            .map(|(position, &fact)| {
                let facts = &self.facts[fact];
                let (row_multipliers, cut_multipliers) =
                    derived.get(&fact)?.dense(row_count, position);
                let orientation = if facts.upper {
                    -BigInt::one()
                } else {
                    BigInt::one()
                };
                Some(ChainCut {
                    form: facts
                        .form
                        .iter()
                        .map(|(atom, coeff)| (*atom, coeff * &orientation))
                        .collect(),
                    bound: facts.bound.clone(),
                    row_multipliers,
                    cut_multipliers,
                })
            })
            .collect::<Option<Vec<_>>>()?;
        let mut last = self.reference(lower, &position, &derived)?;
        last.add_scaled(
            &self.reference(upper, &position, &derived)?,
            &BigRational::one(),
        );
        let (final_rows, final_cuts) = last.dense(row_count, cut_facts.len());
        Some(Chain {
            cuts,
            final_rows,
            final_cuts,
        })
    }

    /// `(base row + Σ multiplier·reference(part)) / divisor`. Facts are
    /// visited in index order, so every part is already in `derived`.
    fn raw_derivation(
        &self,
        fact: usize,
        position: &BTreeMap<usize, usize>,
        derived: &BTreeMap<usize, Derivation>,
    ) -> Derivation {
        let facts = &self.facts[fact];
        let mut raw = Derivation::default();
        for (row, multiplier) in &self.base[facts.row].multipliers {
            let _ = raw
                .rows
                .insert(*row, BigRational::from_integer(multiplier.clone()));
        }
        for (part, multiplier) in &facts.parts {
            if let Some(reference) = self.reference(*part, position, derived) {
                raw.add_scaled(&reference, &BigRational::from_integer(multiplier.clone()));
            }
        }
        let inverse = BigRational::new(BigInt::one(), facts.divisor.clone());
        raw.scale(&inverse);
        raw
    }

    /// How a later derivation cites `fact`: the cut itself, or its exact
    /// combination inlined.
    fn reference(
        &self,
        fact: usize,
        position: &BTreeMap<usize, usize>,
        derived: &BTreeMap<usize, Derivation>,
    ) -> Option<Derivation> {
        if self.facts[fact].cut {
            let mut cited = Derivation::default();
            let _ = cited.cuts.insert(*position.get(&fact)?, BigRational::one());
            return Some(cited);
        }
        derived.get(&fact).cloned()
    }
}

/// Sparse multipliers over clause rows and chain cuts.
#[derive(Clone, Default)]
struct Derivation {
    rows: BTreeMap<usize, BigRational>,
    cuts: BTreeMap<usize, BigRational>,
}

impl Derivation {
    fn add_scaled(&mut self, other: &Derivation, scale: &BigRational) {
        super::add_scaled(&mut self.rows, &other.rows, scale);
        super::add_scaled(&mut self.cuts, &other.cuts, scale);
    }

    fn scale(&mut self, factor: &BigRational) {
        for value in self.rows.values_mut().chain(self.cuts.values_mut()) {
            *value *= factor;
        }
    }

    fn dense(&self, row_count: usize, cut_count: usize) -> (Vec<BigRational>, Vec<BigRational>) {
        (
            super::dense(row_count, &self.rows),
            super::dense(cut_count, &self.cuts),
        )
    }
}
