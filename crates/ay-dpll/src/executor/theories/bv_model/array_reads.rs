// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Original scalar reads through array substitutions, without rewriting ASTs.
//! Results are model data only; complete original-root validation is unchanged.

use super::*;
use ay_core::Symbol;

mod plan;
#[cfg(test)]
mod tests;

// One allowance across dependency planning AND all read recovery attempts.
// This bounds new graph visits/edges and retained read/dependency slots, not
// all work performed by the existing BV arithmetic evaluator.
const MAX_WORK: usize = 20_000;
const MAX_DEPTH: usize = 500;

pub(super) struct Recovery<'a> {
    terms: &'a TermStore,
    definitions: &'a HashMap<TermId, TermId>,
    remaining: usize,
    enabled: bool,
}

pub(super) struct Plan {
    reads: Vec<TermId>,
}

enum Value {
    Bv(BigInt),
    Bool(bool),
}

impl<'a> Recovery<'a> {
    pub(super) fn new(terms: &'a TermStore, definitions: &'a HashMap<TermId, TermId>) -> Self {
        let enabled = definitions.keys().any(|&term| {
            (term.0 as usize) < terms.len() && matches!(terms.sort(term), Sort::Array(_))
        });
        Self {
            terms,
            definitions,
            remaining: MAX_WORK,
            enabled,
        }
    }

    pub(super) fn enabled(&self) -> bool {
        self.enabled
    }

    fn spend(&mut self, amount: usize) -> Option<()> {
        match self.remaining.checked_sub(amount) {
            Some(left) => {
                self.remaining = left;
                Some(())
            }
            None => {
                self.remaining = 0;
                None
            }
        }
    }

    fn live(&self, term: TermId) -> Option<()> {
        ((term.0 as usize) < self.terms.len()).then_some(())
    }

    pub(super) fn seed(
        &mut self,
        plan: &Plan,
        model: &mut BvModel,
        memo: &mut BvEvalMemo,
        substituted: &HashSet<TermId>,
    ) -> Option<()> {
        let terms = self.terms;
        if !plan.reads.is_empty() {
            // Correcting old compound read entries is not a monotone map
            // extension. Drop earlier success caches before those corrections;
            // this postorder batch seeds the reads its dependents need again.
            *memo = BvEvalMemo::default();
        }
        for &read in &plan.reads {
            // The plan is postorder: nested scalar reads needed by a key or
            // payload have already received their exact values.
            let TermData::App(Symbol::Named(name), args) = terms.get(read) else {
                return None;
            };
            let [array, index] = args.as_slice() else {
                return None;
            };
            let Sort::Array(sort) = terms.sort(*array) else {
                return None;
            };
            if name != "select"
                || terms.sort(*index) != &sort.index_sort
                || terms.sort(read) != &sort.element_sort
            {
                return None;
            }
            let key = self.key(*index, model, memo)?;
            let value = self.read(*array, &key, model, memo, substituted)?;
            // Publish the same derived read data used by recovery: leaving old
            // select bits here would make restored assertions disagree with
            // their recovered scalar variables. No fresh SAT choices are made.
            match value {
                Value::Bv(value) => {
                    memo.bv.insert(read, value.clone());
                    model.values.insert(read, value);
                }
                Value::Bool(value) => {
                    memo.boolean.insert(read, value);
                    model.bool_overrides.insert(read, value);
                }
            }
        }
        Some(())
    }

    fn key(&mut self, term: TermId, model: &BvModel, memo: &mut BvEvalMemo) -> Option<BigInt> {
        let Sort::BitVec(sort) = self.terms.sort(term) else {
            return None;
        };
        if sort.width == 0 {
            return None;
        }
        self.spend(1 + sort.width as usize / 64)?;
        Executor::store_chain_operand_value(self.terms, model, term, memo)
    }

    fn value(&mut self, term: TermId, model: &BvModel, memo: &mut BvEvalMemo) -> Option<Value> {
        match self.terms.sort(term) {
            Sort::BitVec(_) => self.key(term, model, memo).map(Value::Bv),
            Sort::Bool => {
                self.spend(1)?;
                Executor::evaluate_bool_substitution(
                    self.terms,
                    term,
                    &model.values,
                    &model.bool_overrides,
                    memo,
                )
                .map(Value::Bool)
            }
            _ => None,
        }
    }

    fn read(
        &mut self,
        mut array: TermId,
        key: &BigInt,
        model: &BvModel,
        memo: &mut BvEvalMemo,
        substituted: &HashSet<TermId>,
    ) -> Option<Value> {
        let terms = self.terms;
        self.live(array)?;
        let expected = terms.sort(array);
        for _ in 0..MAX_DEPTH {
            self.spend(1)?;
            self.live(array)?;
            if terms.sort(array) != expected {
                return None;
            }
            let Sort::Array(sort) = expected else {
                return None;
            };
            match terms.get(array) {
                TermData::Var(_, _) => {
                    if let Some(&definition) = self.definitions.get(&array) {
                        array = definition;
                    } else {
                        return self
                            .free_read(array, key, model, substituted)
                            .map(Value::Bv);
                    }
                }
                TermData::App(Symbol::Named(name), args) if name == "store" => {
                    let [base, index, value] = args.as_slice() else {
                        return None;
                    };
                    for &child in args {
                        self.live(child)?;
                    }
                    if terms.sort(*base) != expected
                        || terms.sort(*index) != &sort.index_sort
                        || terms.sort(*value) != &sort.element_sort
                    {
                        return None;
                    }
                    // Unknown equality must not be treated as a miss.
                    if self.key(*index, model, memo)? == *key {
                        return self.value(*value, model, memo);
                    }
                    array = *base;
                }
                TermData::App(Symbol::Named(name), args) if name == "const-array" => {
                    let [value] = args.as_slice() else {
                        return None;
                    };
                    self.live(*value)?;
                    if terms.sort(*value) != &sort.element_sort {
                        return None;
                    }
                    return self.value(*value, model, memo);
                }
                _ => return None,
            }
        }
        None
    }

    fn free_read(
        &mut self,
        array: TermId,
        key: &BigInt,
        model: &BvModel,
        substituted: &HashSet<TermId>,
    ) -> Option<BigInt> {
        // Only existing, non-decoupled reads may constrain a free base. This
        // is congruence, not an invented default for an unknown array cell.
        let mut result = None;
        let mut memo = BvEvalMemo::default();
        let terms = self.terms;
        for (&read, value) in &model.values {
            self.spend(1)?;
            self.live(read)?;
            let TermData::App(Symbol::Named(name), args) = terms.get(read) else {
                continue;
            };
            let [base, index] = args.as_slice() else {
                continue;
            };
            if name != "select" || *base != array {
                continue;
            }
            self.live(*index)?;
            let Sort::Array(sort) = terms.sort(array) else {
                return None;
            };
            if terms.sort(read) != &sort.element_sort
                || terms.sort(*index) != &sort.index_sort
                || !matches!(sort.element_sort, Sort::BitVec(_))
            {
                return None;
            }
            if self.mentions_substituted(*index, substituted)? {
                continue;
            }
            if self.key(*index, model, &mut memo)? != *key {
                continue;
            }
            let Sort::BitVec(width) = &sort.element_sort else {
                return None;
            };
            if width.width == 0
                || value.sign() == num_bigint::Sign::Minus
                || value.bits() > u64::from(width.width)
            {
                return None;
            }
            if result.as_ref().is_some_and(|old| old != value) {
                return None;
            }
            self.spend(1 + width.width as usize / 64)?;
            result = Some(value.clone());
        }
        result
    }
}
