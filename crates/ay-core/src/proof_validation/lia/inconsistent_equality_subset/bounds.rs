// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

use std::collections::BTreeSet;

use num_rational::BigRational;

use crate::{Constant, Sort, Symbol, TermData, TermId, TermStore};

pub(super) const MAX_ROWS: usize = 8;
pub(super) const MAX_CLAUSE: usize = 64;
const MAX_OCCURRENCES: usize = 512;
const MAX_DEPTH: usize = 32;
const MAX_INT_NODES: usize = 32;
const MAX_LITERAL_BITS: u64 = 128;
const MAX_LITERAL_BIT_MASS: u64 = 512;
const MAX_INTERMEDIATE_BITS: u64 = 4_096;
const MAX_WORK: usize = 1_000_000;

enum Operation {
    Add,
    Multiply,
    Divide,
}

pub(super) struct Control<'a> {
    remaining: usize,
    remaining_bytes: usize,
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
}

impl<'a> Control<'a> {
    pub(super) fn new(progress: &'a mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            remaining: MAX_WORK,
            remaining_bytes: 16 * 1024 * 1024,
            progress,
        }
    }

    pub(super) fn charge(&mut self, work: usize, bytes: usize) -> Option<()> {
        self.remaining = self.remaining.checked_sub(work)?;
        self.remaining_bytes = self.remaining_bytes.checked_sub(bytes)?;
        (self.progress)(work, bytes).then_some(())
    }

    pub(super) fn rational(&mut self, value: &BigRational) -> Option<()> {
        let bits = value.numer().bits().checked_add(value.denom().bits())?;
        (bits <= MAX_INTERMEDIATE_BITS).then_some(())?;
        self.charge(1, usize::try_from(bits.div_ceil(8)).ok()?.checked_add(64)?)
    }

    fn operation(&mut self, a: &BigRational, b: &BigRational, operation: Operation) -> Option<()> {
        self.rational(a)?;
        self.rational(b)?;
        let (an, ad) = (a.numer().bits().max(1), a.denom().bits().max(1));
        let (bn, bd) = if matches!(operation, Operation::Divide) {
            (b.denom().bits().max(1), b.numer().bits().max(1))
        } else {
            (b.numer().bits().max(1), b.denom().bits().max(1))
        };
        let numerator = if matches!(operation, Operation::Add) {
            (an.checked_add(bd)?)
                .max(bn.checked_add(ad)?)
                .checked_add(1)?
        } else {
            an.checked_add(bn)?
        };
        let denominator = ad.checked_add(bd)?;
        // Bound BEFORE multiplication/GCD, even when cancellation would make
        // the eventual answer tiny. The operation has no hidden large scratch.
        let bits = numerator.checked_add(denominator)?;
        (bits <= MAX_INTERMEDIATE_BITS).then_some(())?;
        let limbs = usize::try_from(bits.div_ceil(32)).ok()?.max(1);
        self.charge(
            limbs.checked_mul(limbs)?,
            usize::try_from(bits.div_ceil(8)).ok()?.checked_mul(32)?,
        )
    }

    pub(super) fn add(&mut self, a: &BigRational, b: &BigRational) -> Option<BigRational> {
        self.operation(a, b, Operation::Add)?;
        Some(a + b)
    }

    pub(super) fn multiply(&mut self, a: &BigRational, b: &BigRational) -> Option<BigRational> {
        self.operation(a, b, Operation::Multiply)?;
        Some(a * b)
    }

    pub(super) fn divide(&mut self, a: &BigRational, b: &BigRational) -> Option<BigRational> {
        use num_traits::Zero;
        (!b.is_zero()).then_some(())?;
        self.operation(a, b, Operation::Divide)?;
        Some(a / b)
    }
}

/// Traverse occurrences before invoking the shared, recursive normalizer.
/// Integer-node and literal-bit mass caps bound its possible maps/products,
/// including terms which would cancel out before a post-normalization check.
pub(super) fn preflight(
    terms: &TermStore,
    roots: &[TermId],
    control: &mut Control<'_>,
) -> Option<usize> {
    (!roots.is_empty() && roots.len() <= MAX_CLAUSE).then_some(())?;
    control.charge(roots.len(), roots.len().checked_mul(16)?)?;
    for &root in roots {
        terms.entry_stamp(root)?;
        (terms.sort(root) == &Sort::Bool).then_some(())?;
    }
    let mut pending: Vec<_> = roots.iter().map(|&root| (root, 0usize)).collect();
    let mut integer_nodes = BTreeSet::new();
    let mut occurrences = 0usize;
    let mut bit_mass = 0u64;
    while let Some((root, depth)) = pending.pop() {
        control.charge(1, 0)?;
        occurrences = occurrences.checked_add(1)?;
        (occurrences <= MAX_OCCURRENCES && depth <= MAX_DEPTH).then_some(())?;
        terms.entry_stamp(root)?;
        matches!(terms.sort(root), Sort::Int | Sort::Bool).then_some(())?;
        let children: &[TermId] = match terms.get(root) {
            TermData::Const(Constant::Int(value)) => {
                (value.bits() <= MAX_LITERAL_BITS).then_some(())?;
                bit_mass = bit_mass.checked_add(value.bits())?;
                (bit_mass <= MAX_LITERAL_BIT_MASS).then_some(())?;
                &[]
            }
            TermData::Const(Constant::Bool(_)) => &[],
            TermData::Var(name, _) if name.len() <= 256 => &[],
            TermData::Not(inner) => {
                terms.entry_stamp(*inner)?;
                (terms.sort(root) == &Sort::Bool && terms.sort(*inner) == &Sort::Bool)
                    .then_some(())?;
                std::slice::from_ref(inner)
            }
            TermData::App(Symbol::Named(name), args) if name.len() <= 256 => {
                // Check count and handles before either allocation or indexing.
                (args.len() <= MAX_OCCURRENCES.saturating_sub(occurrences + pending.len()))
                    .then_some(())?;
                for &arg in args {
                    terms.entry_stamp(arg)?;
                }
                if matches!(name.as_str(), "+" | "-" | "*") {
                    (terms.sort(root) == &Sort::Int
                        && args.iter().all(|&arg| terms.sort(arg) == &Sort::Int))
                    .then_some(())?;
                }
                if name == "=" {
                    (terms.sort(root) == &Sort::Bool
                        && args.len() >= 2
                        && args
                            .iter()
                            .all(|&arg| terms.sort(arg) == terms.sort(args[0])))
                    .then_some(())?;
                }
                args
            }
            // Quantifiers, lets, non-integer literals and unsupported nodes
            // remain outside this bounded arithmetic capability.
            _ => return None,
        };
        if terms.sort(root) == &Sort::Int && !matches!(terms.get(root), TermData::Const(_)) {
            if !integer_nodes.contains(&root) {
                (integer_nodes.len() < MAX_INT_NODES).then_some(())?;
                control.charge(1, 64)?;
                integer_nodes.insert(root);
            }
        }
        (children.len() <= MAX_OCCURRENCES.saturating_sub(occurrences + pending.len()))
            .then_some(())?;
        control.charge(children.len(), children.len().checked_mul(16)?)?;
        pending.extend(children.iter().map(|&child| (child, depth + 1)));
    }
    // Parsing is occurrence-bounded and bit-mass bounded before it starts;
    // charge its conservative tree/map work and allow cancellation here too.
    control.charge(
        occurrences.checked_mul(MAX_INT_NODES)?,
        occurrences.checked_mul(4_096)?,
    )?;
    Some(occurrences)
}
