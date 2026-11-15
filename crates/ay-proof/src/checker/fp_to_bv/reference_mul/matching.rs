// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Match the COMPLETE typed word expression against the independent recipe.
//! Neither a caller circuit tag nor selected product fields are accepted.
//! Reserved SMT operator/signature semantics and full proof/input assumptions
//! still belong to the enclosing strict reader's authenticated source scope.

use super::{
    graph::{Operation, RefId},
    Arithmetic, Progress, Reference, ReferenceError, Result,
};
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

mod constants;
mod operators;

pub(super) fn unit(
    terms: &TermStore,
    clause: &[TermId],
    operation: Arithmetic,
    progress: Progress<'_>,
) -> Result<bool> {
    if !progress(1, 0) {
        return Err(ReferenceError::Resource);
    }
    if clause.len() != 1 {
        return Ok(false);
    }
    if !progress(2, 0) {
        return Err(ReferenceError::Resource);
    }
    if clause[0].index() >= terms.len() {
        return Ok(false);
    }
    if !matches!(terms.sort(clause[0]), Sort::Bool) {
        return Ok(false);
    }
    let TermData::App(Symbol::Named(name), args) = terms.get(clause[0]) else {
        return Ok(false);
    };
    if !progress(4, 0) {
        return Err(ReferenceError::Resource);
    }
    if name.as_str() != "=" || args.len() != 2 || terms.is_declared_function(name) {
        return Ok(false);
    }
    if orientation(terms, args[0], args[1], operation, progress)? {
        return Ok(true);
    }
    orientation(terms, args[1], args[0], operation, progress)
}

fn orientation(
    terms: &TermStore,
    source: TermId,
    target: TermId,
    operation: Arithmetic,
    progress: Progress<'_>,
) -> Result<bool> {
    let result = (|| {
        let mut reference = Reference::build_operation(terms, source, operation, progress)?;
        reference.matches(target)
    })();
    match result {
        Err(ReferenceError::Source | ReferenceError::Width) => Ok(false),
        other => other,
    }
}

type Pair = (RefId, TermId);

impl Reference<'_, '_> {
    fn pair(&mut self, pairs: &mut Vec<Pair>, pair: Pair) -> Result<()> {
        self.charge(1, 0)?;
        if pairs.len() == pairs.capacity() {
            return self.stop(ReferenceError::Resource);
        }
        pairs.push(pair);
        Ok(())
    }

    fn matches(&mut self, target: TermId) -> Result<bool> {
        let (_, sort) = self.term(target)?;
        if !matches!(sort, Sort::FloatingPoint(eb, p) if *eb == self.format.eb && *p == self.format.p)
        {
            return Ok(false);
        }
        let [sign, exponent, fraction] = self.app(target, "fp")?;
        let output = self.output.ok_or(ReferenceError::Source)?;
        let mut todo = Vec::new();
        let mut seen = Vec::<Option<TermId>>::new();
        let count = self.nodes.len();
        let tasks = count
            .checked_mul(3)
            .and_then(|n| n.checked_add(3))
            .ok_or(ReferenceError::Resource)?;
        let todo_bytes = tasks
            .checked_mul(std::mem::size_of::<Pair>())
            .ok_or(ReferenceError::Resource)?;
        self.storage(tasks, todo_bytes)?;
        if todo.try_reserve_exact(tasks).is_err() {
            return self.stop(ReferenceError::Allocation);
        }
        let seen_bytes = count
            .checked_mul(std::mem::size_of::<Option<TermId>>())
            .ok_or(ReferenceError::Resource)?;
        self.storage(count, seen_bytes)?;
        if seen.try_reserve_exact(count).is_err() {
            return self.stop(ReferenceError::Allocation);
        }
        seen.resize(count, None);
        self.pair(&mut todo, (output.sign, sign))?;
        self.pair(&mut todo, (output.exponent, exponent))?;
        self.pair(&mut todo, (output.fraction, fraction))?;
        while let Some(pair) = todo.pop() {
            self.charge(1, 0)?;
            let Some(prior) = seen.get_mut(pair.0 .0) else {
                return Err(ReferenceError::Source);
            };
            if let Some(actual) = *prior {
                // A canonical recipe reuses each exact source computation.
                // Imported duplicate subtrees may be valid but are not this
                // narrow schema; decline them instead of unbounded expansion.
                if actual != pair.1 {
                    return Err(ReferenceError::Source);
                }
                continue;
            }
            *prior = Some(pair.1);
            self.match_node(pair.0, pair.1, &mut todo)?;
        }
        self.charge(0, 0)?;
        Ok(true)
    }

    fn match_node(&mut self, expected: RefId, target: TermId, todo: &mut Vec<Pair>) -> Result<()> {
        self.charge(1, 0)?;
        let Some(node) = self.nodes.get(expected.0).copied() else {
            return Err(ReferenceError::Source);
        };
        let (_, sort) = self.term(target)?;
        if !matches!(sort, Sort::BitVec(actual) if actual.width == node.width) {
            return Err(ReferenceError::Source);
        }
        match node.operation {
            Operation::Input(source) => self.match_input(source, target, node.width),
            Operation::Small(value) => self.constant(target, node.width, Some(value)),
            Operation::Ones => self.constant(target, node.width, None),
            Operation::Not(inner) => {
                let [argument] = self.app(target, "bvnot")?;
                self.pair(todo, (inner, argument))
            }
            Operation::Resize(inner) => {
                let old_width = self.width(inner)?;
                let argument = if old_width < node.width {
                    self.indexed_unary(target, "zero_extend", &[node.width - old_width])?
                } else {
                    self.indexed_unary(target, "extract", &[node.width - 1, 0])?
                };
                self.pair(todo, (inner, argument))
            }
            Operation::Extract(inner, high, low) => {
                let argument = self.indexed_unary(target, "extract", &[high, low])?;
                self.pair(todo, (inner, argument))
            }
            Operation::Binary(op, a, b) => self.match_binary(target, op, a, b, todo),
            Operation::Select(condition, yes, no) => {
                let (data, _) = self.term(target)?;
                let TermData::Ite(test, yes_term, no_term) = data else {
                    return Err(ReferenceError::Source);
                };
                let actual = self.bit_condition(*test)?;
                self.pair(todo, (condition, actual))?;
                self.pair(todo, (yes, *yes_term))?;
                self.pair(todo, (no, *no_term))
            }
        }
    }
}
