// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Replay a modular linear combination of the original equality sides.
//! Sparse coefficients are independent of the producer's matrix and pivots.

use super::ProofCheckError;
use ay_core::{
    Constant, FiniteFieldSort, ProofId, Sort, Symbol, TermData, TermId, TermStore, TheoryLemmaKind,
};

#[derive(Default)]
struct Affine {
    terms: Vec<(TermId, u32)>,
    constant: u32,
}

struct Check<'a, 'p> {
    terms: &'a TermStore,
    field: FiniteFieldSort,
    work: usize,
    progress: &'p mut dyn FnMut(usize, usize) -> bool,
}

impl Check<'_, '_> {
    fn pay(&mut self, work: usize, bytes: usize) -> Option<()> {
        self.work = self.work.checked_sub(work)?;
        (self.progress)(work, bytes).then_some(())
    }

    fn insert(&mut self, row: &mut Affine, term: TermId, coefficient: u32) -> Option<()> {
        if coefficient == 0 {
            return Some(());
        }
        let p = self.field.modulus();
        // The search needs at most log2(1024)+1 comparisons.
        self.pay(11, 0)?;
        match row.terms.binary_search_by_key(&term, |&(id, _)| id) {
            Ok(i) => {
                let sum =
                    ((u64::from(row.terms[i].1) + u64::from(coefficient)) % u64::from(p)) as u32;
                if sum == 0 {
                    self.pay(row.terms.len() - i, 0)?;
                    let _ = row.terms.remove(i);
                } else {
                    row.terms[i].1 = sum;
                }
            }
            Err(i) => {
                if row.terms.len() == 1024 {
                    return None;
                }
                if row.terms.len() == row.terms.capacity() {
                    let capacity = row.terms.capacity().max(2).checked_mul(2)?;
                    self.pay(
                        row.terms.len(),
                        capacity.checked_mul(size_of::<(TermId, u32)>())?,
                    )?;
                    row.terms
                        .try_reserve_exact(capacity - row.terms.len())
                        .ok()?;
                }
                self.pay(row.terms.len() - i, 0)?;
                row.terms.insert(i, (term, coefficient));
            }
        }
        Some(())
    }

    fn add(&mut self, target: &mut Affine, source: Affine, scale: u32) -> Option<()> {
        let p = self.field.modulus();
        self.pay(source.terms.len(), 0)?;
        target.constant = ((u64::from(target.constant)
            + u64::from(scale) * u64::from(source.constant))
            % u64::from(p)) as u32;
        for (id, coefficient) in source.terms {
            let coefficient = (u64::from(scale) * u64::from(coefficient) % u64::from(p)) as u32;
            self.insert(target, id, coefficient)?;
        }
        Some(())
    }

    fn scale(&mut self, row: &mut Affine, scale: u32) -> Option<()> {
        self.pay(row.terms.len(), 0)?;
        let p = self.field.modulus();
        row.constant = (u64::from(row.constant) * u64::from(scale) % u64::from(p)) as u32;
        if scale == 0 {
            row.terms.clear();
        } else {
            for (_, coefficient) in &mut row.terms {
                *coefficient = (u64::from(*coefficient) * u64::from(scale) % u64::from(p)) as u32;
            }
        }
        Some(())
    }

    fn parse(&mut self, id: TermId, depth: usize) -> Option<Affine> {
        self.pay(1, 0)?;
        if depth > 128 || self.terms.sort(id) != &Sort::FiniteField(self.field) {
            return None;
        }
        let p = self.field.modulus();
        let mut row = Affine::default();
        if let TermData::App(Symbol::Named(name), _) = self.terms.get(id) {
            self.pay(name.len(), 0)?;
            if self.terms.is_declared_function(name) {
                return None;
            }
        }
        match self.terms.get(id) {
            TermData::Var(..) => self.insert(&mut row, id, 1)?,
            TermData::Const(Constant::FiniteField { value, field })
                if *field == self.field && *value < p =>
            {
                row.constant = *value;
            }
            TermData::App(Symbol::Named(name), args) if args.len() <= 1024 => match name.as_str() {
                "ff.neg" if args.len() == 1 => {
                    row = self.parse(args[0], depth + 1)?;
                    self.scale(&mut row, p - 1)?;
                }
                "ff.add" | "ff.bitsum" if args.len() >= 2 => {
                    let mut weight = 1;
                    for &arg in args {
                        let child = self.parse(arg, depth + 1)?;
                        self.add(&mut row, child, weight)?;
                        if name == "ff.bitsum" {
                            weight = (u64::from(weight) * 2 % u64::from(p)) as u32;
                        }
                    }
                }
                "ff.mul" if args.len() >= 2 => {
                    row.constant = 1;
                    for &arg in args {
                        let mut child = self.parse(arg, depth + 1)?;
                        if child.terms.is_empty() {
                            self.scale(&mut row, child.constant)?;
                        } else if row.terms.is_empty() {
                            self.scale(&mut child, row.constant)?;
                            row = child;
                        } else {
                            return None;
                        }
                    }
                }
                _ => return None,
            },
            _ => return None,
        }
        Some(row)
    }
}

fn equality(terms: &TermStore, literal: TermId) -> Option<(TermId, TermId, FiniteFieldSort)> {
    let TermData::Not(root) = terms.get(literal) else {
        return None;
    };
    let TermData::App(Symbol::Named(name), args) = terms.get(*root) else {
        return None;
    };
    let &[left, right] = args.as_slice() else {
        return None;
    };
    let Sort::FiniteField(field) = terms.sort(left) else {
        return None;
    };
    (name == "="
        && !terms.is_declared_function(name)
        && terms.sort(literal) == &Sort::Bool
        && terms.sort(*root) == &Sort::Bool
        && terms.sort(right) == &Sort::FiniteField(*field))
        .then_some((left, right, *field))
}

pub(in crate::checker) fn validate(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    multipliers: &[u32; TheoryLemmaKind::MAX_FINITE_FIELD_LINEAR_ROWS],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    if clause.len() > TheoryLemmaKind::MAX_FINITE_FIELD_LINEAR_ROWS
        || multipliers[clause.len()..].iter().any(|&c| c != 0)
    {
        return Err(ProofCheckError::InvalidTheoryLemma {
            step,
            reason: "invalid fixed finite-field multiplier padding".into(),
        });
    }
    validate_variable(terms, step, clause, &multipliers[..clause.len()], progress)
}

pub(in crate::checker) fn validate_variable(
    terms: &TermStore,
    step: ProofId,
    clause: &[TermId],
    multipliers: &[u32],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let valid = (|| -> Option<bool> {
        if clause.is_empty()
            || clause.len() != multipliers.len()
            || u32::try_from(clause.len()).is_err()
            || !progress(1, 0)
        {
            return None;
        }
        let (_, _, field) = equality(terms, clause[0])?;
        let p = field.modulus();
        let mut checker = Check {
            terms,
            field,
            work: 4_000_000,
            progress,
        };
        let mut sum = Affine::default();
        for (&literal, &multiplier) in clause.iter().zip(multipliers) {
            checker.pay(1, 0)?;
            let (left, right, row_field) = equality(terms, literal)?;
            if row_field != field || multiplier >= p {
                return None;
            }
            let left = checker.parse(left, 0)?;
            let right = checker.parse(right, 0)?;
            checker.add(&mut sum, left, multiplier)?;
            checker.add(&mut sum, right, (p - multiplier) % p)?;
        }
        checker.pay(1, 0)?;
        Some(sum.terms.is_empty() && sum.constant != 0)
    })() == Some(true);
    if valid {
        Ok(())
    } else {
        Err(ProofCheckError::InvalidTheoryLemma {
            step,
            reason: "finite-field linear combination is invalid, unsupported, or over budget"
                .into(),
        })
    }
}
