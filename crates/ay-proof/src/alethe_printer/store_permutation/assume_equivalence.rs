// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Typed literal-index store permutations at an authored assumption boundary.

use super::*;
use crate::checker::MAX_STORE_PERMUTATION_CHAIN;
use std::fmt;

struct MeteredText<'a, 'terms> {
    printer: &'a AlethePrinter<'terms>,
    text: String,
}

impl fmt::Write for MeteredText<'_, '_> {
    fn write_str(&mut self, text: &str) -> fmt::Result {
        let wanted = self.text.len().checked_add(text.len()).ok_or(fmt::Error)?;
        let growth = if wanted > self.text.capacity() {
            self.text
                .len()
                .checked_add(wanted.checked_mul(2).ok_or(fmt::Error)?)
                .ok_or(fmt::Error)?
        } else {
            0
        };
        self.admit_copy(text.len().checked_add(growth).ok_or(fmt::Error)?)
            .ok_or(fmt::Error)?;
        self.text.try_reserve(text.len()).map_err(|_| fmt::Error)?;
        self.text.push_str(text);
        Ok(())
    }
}

impl PermutationText for MeteredText<'_, '_> {
    fn admit_copy(&mut self, bytes: usize) -> Option<()> {
        self.printer
            .admit_emission_work(u64::try_from(bytes).ok()?)
            .then_some(())
    }
}

#[derive(PartialEq, Eq)]
enum LiteralIndex {
    Int(num_bigint::BigInt),
    Real(num_rational::BigRational),
    BitVec(num_bigint::BigUint, u32),
}

fn arithmetic_literal(text: &str, sort: &Sort) -> Option<num_rational::BigRational> {
    let text = text.trim();
    let body = text
        .strip_prefix("(-")
        .and_then(|body| body.strip_suffix(')'))
        .map(str::trim)
        .unwrap_or(text);
    let digits = match sort {
        Sort::Int => body.bytes().all(|b| b.is_ascii_digit()),
        // Decimal real literals carry their own Real sort in an independent
        // evaluate premise. A bare integer token must not guess that sort.
        Sort::Real => body.contains('.') && body.bytes().all(|b| b.is_ascii_digit() || b == b'.'),
        _ => false,
    };
    if body.is_empty() || !digits {
        return None;
    }
    crate::la_generic_signs::parse_numeric_constant(text)
}

fn printed_index(text: &str, sort: &Sort) -> Option<LiteralIndex> {
    match sort {
        Sort::Int => {
            let value = arithmetic_literal(text, sort)?;
            value
                .is_integer()
                .then(|| LiteralIndex::Int(value.to_integer()))
        }
        Sort::Real => Some(LiteralIndex::Real(arithmetic_literal(text, sort)?)),
        Sort::BitVec(width) => {
            let (value, actual_width) = parse_printed_bitvec_literal(text)?;
            (actual_width == width.width).then_some(LiteralIndex::BitVec(value, actual_width))
        }
        _ => None,
    }
}

fn native_index(terms: &TermStore, term: TermId, sort: &Sort) -> Option<LiteralIndex> {
    if terms.entry_stamp(term).is_none() || terms.sort(term) != sort {
        return None;
    }
    match (sort, terms.get(term)) {
        (Sort::Int, TermData::Const(Constant::Int(value))) => {
            Some(LiteralIndex::Int(value.clone()))
        }
        (Sort::Real, TermData::Const(Constant::Rational(value))) => {
            Some(LiteralIndex::Real(value.0.clone()))
        }
        (
            Sort::BitVec(width),
            TermData::Const(Constant::BitVec {
                value,
                width: actual,
            }),
        ) if width.width == *actual => Some(LiteralIndex::BitVec(value.to_biguint()?, *actual)),
        _ => None,
    }
}

fn spend_node(nodes: &mut usize) -> Option<()> {
    *nodes = nodes.checked_sub(1)?;
    Some(())
}

/// A borrowed syntax walk. All scan and Vec-slot work is admitted before it
/// starts; at most the existing checked permutation's eight stores are read.
fn printed_chain<'a>(
    text: &'a str,
    nodes: &mut usize,
    depth: usize,
) -> Option<(&'a str, Vec<(&'a str, &'a str)>)> {
    let mut current = text;
    let mut entries = Vec::with_capacity(MAX_STORE_PERMUTATION_CHAIN);
    loop {
        spend_node(nodes)?;
        let Ok(args) = split_alethe_application_bounded(
            current,
            "store",
            3,
            super::super::authored_assume::MAX_EQUIVALENCE_BYTES,
        ) else {
            return Some((current, entries));
        };
        let [base, index, value] = args.as_slice() else {
            return None;
        };
        if entries.len() == MAX_STORE_PERMUTATION_CHAIN || entries.len() == depth {
            return None;
        }
        entries.push((*index, *value));
        current = base;
    }
}

impl AlethePrinter<'_> {
    /// `canonical` is the identity rendering just obtained by the existing
    /// authored-equivalence entry. Recheck the actual native spine, index sort
    /// and literal values; the source may only permute its exact writes.
    pub(in crate::alethe_printer) fn literal_store_permutation_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical_term: TermId,
        canonical: &str,
        remaining_nodes: &mut usize,
        remaining_depth: usize,
    ) -> Option<String> {
        let Sort::Array(array_sort) = self.terms.sort(canonical_term) else {
            return None;
        };
        if !matches!(
            array_sort.index_sort,
            Sort::Int | Sort::Real | Sort::BitVec(_)
        ) || !surface.starts_with("(store ")
        {
            return None;
        }
        // Refuse an unsupported native spine before scanning the authored
        // text. This borrows the same node/depth allowance as the syntax walk;
        // a failed attempt never gives that allowance back to another leaf.
        let mut cursor = canonical_term;
        let mut stores = 0;
        loop {
            if !self.admit_emission_work((5 * std::mem::size_of::<TermId>()) as u64) {
                return None;
            }
            spend_node(remaining_nodes)?;
            let TermData::App(Symbol::Named(head), args) = self.terms.get(cursor) else {
                break;
            };
            if head != "store" {
                break;
            }
            let [inner, at, value] = args.as_slice() else {
                return None;
            };
            if stores == MAX_STORE_PERMUTATION_CHAIN
                || stores == remaining_depth
                || [cursor, *inner, *at, *value]
                    .iter()
                    .any(|&term| self.terms.entry_stamp(term).is_none())
                || self.terms.sort(cursor) != self.terms.sort(canonical_term)
                || self.terms.sort(*inner) != self.terms.sort(canonical_term)
                || self.terms.sort(*value) != &array_sort.element_sort
                || self.terms.sort(*at) != &array_sort.index_sort
                || !matches!(
                    (&array_sort.index_sort, self.terms.get(*at)),
                    (Sort::Int, TermData::Const(Constant::Int(_)))
                        | (Sort::Real, TermData::Const(Constant::Rational(_)))
                        | (Sort::BitVec(_), TermData::Const(Constant::BitVec { .. }))
                )
            {
                return None;
            }
            stores += 1;
            cursor = *inner;
        }
        if stores < 2 {
            return None;
        }
        let input = surface.len().checked_add(canonical.len())?;
        let scan = input
            .checked_mul(MAX_STORE_PERMUTATION_CHAIN + 1 + 2 * (std::mem::size_of::<String>() + 2))?
            .checked_add(2 * MAX_STORE_PERMUTATION_CHAIN * 5 * std::mem::size_of::<&str>())?;
        if !self.admit_emission_work(u64::try_from(scan).ok()?) {
            return None;
        }
        // Capture census visits at most the fully expanded canonical text's
        // node count; reserve its work/slots before the existing bounded walk.
        let capture = canonical
            .len()
            .checked_mul(std::mem::size_of::<TermId>() + 2)?;
        if !self.admit_emission_work(u64::try_from(capture).ok()?)
            || term_mentions_symbol(self.terms, canonical_term, EXT_CHOICE_BINDER)
        {
            return None;
        }
        let (source_base, source) = printed_chain(surface, remaining_nodes, remaining_depth)?;
        let (base, target) = printed_chain(canonical, remaining_nodes, remaining_depth)?;
        if target.len() != stores
            || source.len() != target.len()
            || !surface_literal::same_printed_term(source_base, base)
        {
            return None;
        }
        let mut cursor = canonical_term;
        let mut output = MeteredText {
            printer: self,
            text: String::new(),
        };
        output.admit_copy(
            target
                .len()
                .checked_mul(std::mem::size_of::<LiteralIndex>())?,
        )?;
        let mut values = Vec::with_capacity(target.len());
        for (index, _) in &target {
            let TermData::App(Symbol::Named(head), args) = self.terms.get(cursor) else {
                return None;
            };
            let [inner, at, value] = args.as_slice() else {
                return None;
            };
            if head != "store"
                || [*inner, *at, *value]
                    .iter()
                    .any(|&term| self.terms.entry_stamp(term).is_none())
                || self.terms.sort(cursor) != self.terms.sort(canonical_term)
                || self.terms.sort(*inner) != self.terms.sort(canonical_term)
                || self.terms.sort(*value) != &array_sort.element_sort
            {
                return None;
            }
            // Reserving the literal's expanded input bytes covers its owned
            // integer/rational payload before parsing or cloning it.
            output.admit_copy(index.len().checked_mul(8)?)?;
            let literal = native_index(self.terms, *at, &array_sort.index_sort)?;
            if printed_index(index, &array_sort.index_sort)? != literal || values.contains(&literal)
            {
                return None;
            }
            values.push(literal);
            cursor = *inner;
        }
        if matches!(self.terms.get(cursor), TermData::App(Symbol::Named(head), _) if head == "store")
        {
            return None;
        }
        // Byte comparisons may scan the complete fields for each pairing.
        output.admit_copy(input.checked_mul(target.len().checked_mul(target.len())?)?)?;
        output.admit_copy(
            (source.len() + target.len()).checked_mul(std::mem::size_of::<PrintedEntry>())?,
        )?;
        let mut left = Vec::with_capacity(source.len());
        output.admit_copy(target.len())?;
        let mut used = vec![false; target.len()];
        for (source_index, source_value) in source {
            output.admit_copy(source_index.len().checked_mul(8)?)?;
            let literal = printed_index(source_index, &array_sort.index_sort)?;
            let at = values.iter().position(|value| *value == literal)?;
            if used[at] || !surface_literal::same_printed_term(source_value, target[at].1) {
                return None;
            }
            used[at] = true;
            output.admit_copy(target[at].0.len().checked_add(target[at].1.len())?)?;
            left.push((target[at].0.to_string(), target[at].1.to_string()));
        }
        let mut right = Vec::with_capacity(target.len());
        for (index, value) in target {
            output.admit_copy(index.len().checked_add(value.len())?)?;
            right.push((index.to_string(), value.to_string()));
        }
        output.admit_copy(base.len())?;
        let base = base.to_string();
        let left_text = admitted_store_chain_text(&mut output, &base, &left)?;
        let right_text = admitted_store_chain_text(&mut output, &base, &right)?;
        if !surface_literal::same_printed_term(surface, &left_text) || canonical != right_text {
            return None;
        }
        output.admit_copy(input.checked_mul(left.len().checked_mul(left.len())?)?)?;
        let swaps = adjacent_transposition_schedule(&left, &right)?;
        if swaps.is_empty() {
            return None;
        }
        let false_fact = output.term(format_args!("{id}.nf"))?;
        writeln!(output, "(step {false_fact} (cl (not false)) :rule false)").ok()?;
        let mut disequalities = HashMap::default();
        let pairs = left.len().checked_mul(left.len() - 1)? / 2;
        output.admit_copy(
            pairs
                .checked_mul(
                    std::mem::size_of::<((String, String), (String, String, String))>()
                        .checked_add(8)?,
                )?
                .checked_mul(4)?
                .checked_add(64)?,
        )?;
        disequalities.try_reserve(pairs).ok()?;
        for i in 0..left.len() {
            for j in i + 1..left.len() {
                let (a, b) = (&left[i].0, &left[j].0);
                let step = output.term(format_args!("{id}.d{i}_{j}"))?;
                writeln!(
                    output,
                    "(step {step}.ev (cl (= (= {a} {b}) false)) :rule evaluate)\n\
                     (step {step}.lift (cl (not (= {a} {b})) false) :rule equiv1 :premises ({step}.ev))\n\
                     (step {step} (cl (not (= {a} {b}))) :rule resolution :premises ({step}.lift {false_fact}))"
                )
                .ok()?;
                output.admit_copy(a.len().checked_add(b.len())?.checked_mul(2)?)?;
                let key = unordered_printed_pair(a, b);
                disequalities.insert(key, (step, a.clone(), b.clone()));
            }
        }
        let index_sort = output.term(format_args!("{}", array_sort.index_sort))?;
        let printed = PrintedPermutation {
            literals: Vec::new(),
            base,
            left,
            right,
            left_text,
            right_text,
            disequalities,
            index_sort,
            row_position: 0,
        };
        let segments = write_swap_segments(&mut output, id, &false_fact, &printed, &swaps)?;
        let chain = compose_segments(&mut output, id, &printed, &segments)?;
        writeln!(
            output,
            "(step {id} (cl (= {surface} {canonical})) :rule reordering :premises ({chain}))"
        )
        .ok()?;
        Some(output.text)
    }
}

#[cfg(test)]
#[path = "assume_equivalence_tests.rs"]
mod tests;
