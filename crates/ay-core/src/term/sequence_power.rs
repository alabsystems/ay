// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Z3 sequence power: s^n is empty for n <= 0, otherwise n copies of s.
//! Ground words fold within a bounded materialization budget. Small constant
//! exponents over symbolic bases lower by repeated squaring to a shared
//! concatenation DAG with O(log n) nodes, never an n-element argument vector.
//! Reference: Z3 src/ast/rewriter/seq_rewriter.cpp (OP_SEQ_POWER).

use super::{Constant, Symbol, TermData, TermId, TermStore};
use crate::Sort;
use num_traits::{One, Signed, ToPrimitive, Zero};

impl TermStore {
    pub(super) fn fold_sequence_power_application(
        &mut self,
        function: &Symbol,
        args: &[TermId],
        sort: &Sort,
    ) -> Option<TermId> {
        let Symbol::Named(name) = function else {
            return None;
        };
        match name.as_str() {
            "seq.power" if !self.is_declared_function(name) => self.fold_sequence_power(args, sort),
            "seq.len" | "str.len" => self.fold_sequence_power_length(name, args, sort),
            _ => None,
        }
    }

    /// For a fixed nonempty word w, w^n = t iff t belongs to w* and
    /// |t| = max(n, 0) * |w|. Membership and length determine the repetition
    /// count uniquely; this is equivalence under every polarity and binder.
    /// It enables symbolic-count solving with the existing regex/arithmetic
    /// combination and introduces no fresh variables or witness assumptions.
    pub(super) fn fold_sequence_power_equality(
        &mut self,
        lhs: TermId,
        rhs: TermId,
    ) -> Option<TermId> {
        if self.sort(rhs) != &Sort::String {
            return None;
        }
        for (power, word) in [(lhs, rhs), (rhs, lhs)] {
            let TermData::App(Symbol::Named(operation), operands) = self.get(power) else {
                continue;
            };
            if operation != "seq.power" || self.is_declared_function(operation) {
                continue;
            }
            let [base, count] = operands.as_slice() else {
                continue;
            };
            let (base, count) = (*base, *count);
            if self.sort(count) != &Sort::Int {
                continue;
            }
            let base_length = match self.get(base) {
                TermData::Const(Constant::String(value)) if !value.is_empty() => {
                    value.chars().count()
                }
                _ => continue,
            };
            let zero = self.mk_int(0.into());
            let nonpositive = self.mk_le(count, zero);
            if matches!(self.get(word), TermData::Const(Constant::String(value)) if value.is_empty())
            {
                return Some(nonpositive);
            }
            let literal = self.mk_app(Symbol::named("str.to_re"), [base], Sort::RegLan);
            let repeats = self.mk_app(Symbol::named("re.*"), [literal], Sort::RegLan);
            let member = self.mk_app(Symbol::named("str.in_re"), [word, repeats], Sort::Bool);
            let word_length = match self.get(word) {
                TermData::Const(Constant::String(value)) => {
                    self.mk_int(value.chars().count().into())
                }
                _ => self.mk_app(Symbol::named("str.len"), [word], Sort::Int),
            };
            let base_length = self.mk_int(base_length.into());
            let power_length = self.mk_mul(vec![count, base_length]);
            let same_length = self.mk_eq(word_length, power_length);
            let positive = self.mk_lt(zero, count);
            let positive_case = self.mk_and(vec![positive, member, same_length]);
            let empty = self.mk_string(String::new());
            let empty_word = self.mk_eq(word, empty);
            let nonpositive_case = self.mk_and(vec![nonpositive, empty_word]);
            return Some(self.mk_or(vec![nonpositive_case, positive_case]));
        }
        None
    }

    /// |s^n| = if n <= 0 then 0 else n * |s|, including symbolic n.
    pub(super) fn fold_sequence_power_length(
        &mut self,
        name: &str,
        args: &[TermId],
        sort: &Sort,
    ) -> Option<TermId> {
        let [power] = args else { return None };
        let expected_sequence = match name {
            "str.len" => matches!(self.sort(*power), Sort::String),
            "seq.len" => matches!(self.sort(*power), Sort::Seq(_)),
            _ => return None,
        };
        if !expected_sequence || sort != &Sort::Int {
            return None;
        }
        let TermData::App(Symbol::Named(operation), operands) = self.get(*power) else {
            return None;
        };
        if operation != "seq.power"
            || self.is_declared_function(operation)
            || self.is_declared_function(name)
        {
            return None;
        }
        let [base, count] = operands.as_slice() else {
            return None;
        };
        let (base, count) = (*base, *count);
        if self.sort(base) != self.sort(*power) || self.sort(count) != &Sort::Int {
            return None;
        }
        let zero = self.mk_int(0.into());
        let nonpositive = self.mk_le(count, zero);
        let base_length = match self.get(base) {
            TermData::Const(Constant::String(value)) => self.mk_int(value.chars().count().into()),
            _ => self.mk_app(Symbol::named(name), [base], Sort::Int),
        };
        let positive_length = self.mk_mul(vec![count, base_length]);
        Some(self.mk_ite(nonpositive, zero, positive_length))
    }

    pub(super) fn fold_sequence_power(&mut self, args: &[TermId], sort: &Sort) -> Option<TermId> {
        let [base, count] = args else { return None };
        if self.sort(*base) != sort || self.sort(*count) != &Sort::Int {
            return None;
        }
        let concat = match sort {
            Sort::String => "str.++",
            Sort::Seq(_) => "seq.++",
            _ => return None,
        };
        let empty_base = match self.get(*base) {
            TermData::Const(Constant::String(value)) => value.is_empty(),
            TermData::App(Symbol::Named(name), children) => {
                name == "seq.empty" && children.is_empty()
            }
            _ => false,
        };
        if empty_base {
            return Some(*base);
        }
        let TermData::Const(Constant::Int(count)) = self.get(*count) else {
            return None;
        };
        if count.is_negative() || count.is_zero() {
            return Some(if sort == &Sort::String {
                self.mk_string(String::new())
            } else {
                self.mk_app(Symbol::named("seq.empty"), [], sort.clone())
            });
        }
        if count.is_one() {
            return Some(*base);
        }
        if let TermData::Const(Constant::String(value)) = self.get(*base) {
            let copies = count.to_usize()?;
            let size = value.len().checked_mul(copies)?;
            if size > (1 << 20) {
                return None;
            }
            let repeated = value.repeat(copies);
            return Some(self.mk_string(repeated));
        }
        // Larger and symbolic exponents retain their interpreted operator;
        // they must not be coerced, truncated, or treated as an arbitrary UF.
        let mut remaining = count.to_u64()?;
        if remaining > 64 {
            return None;
        }
        let mut block = *base;
        let mut result = None;
        while remaining != 0 {
            if remaining & 1 != 0 {
                result = Some(match result {
                    None => block,
                    Some(prefix) => {
                        self.mk_app(Symbol::named(concat), [prefix, block], sort.clone())
                    }
                });
            }
            remaining >>= 1;
            if remaining != 0 {
                block = self.mk_app(Symbol::named(concat), [block, block], sort.clone());
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_bigint::BigInt;

    fn length(terms: &TermStore, term: TermId) -> usize {
        match terms.get(term) {
            TermData::Const(Constant::String(value)) => value.chars().count(),
            TermData::App(Symbol::Named(name), args) if name == "str.++" => {
                args.iter().map(|&arg| length(terms, arg)).sum()
            }
            _ => panic!("unexpected sequence expression"),
        }
    }

    #[test]
    fn sequence_power_preserves_multiplicity_and_negative_semantics() {
        let mut terms = TermStore::new();
        let base = terms.mk_string("λ🦀".to_string());
        for copies in [-2i64, 0, 1, 3, 7, 64] {
            let exponent = terms.mk_int(BigInt::from(copies));
            let power = terms.mk_app(Symbol::named("seq.power"), [base, exponent], Sort::String);
            assert_eq!(length(&terms, power), 2 * copies.max(0) as usize);
        }
        let huge = terms.mk_int(BigInt::from(1u32) << 100usize);
        let power = terms.mk_app(Symbol::named("seq.power"), [base, huge], Sort::String);
        assert!(matches!(terms.get(power), TermData::App(name, _) if name.name() == "seq.power"));
    }

    #[test]
    fn sequence_power_does_not_fold_a_declared_uf() {
        let mut terms = TermStore::new();
        terms.register_declared_function("seq.power");
        let base = terms.mk_string("x".to_string());
        let zero = terms.mk_int(BigInt::from(0));
        let power = terms.mk_app(Symbol::named("seq.power"), [base, zero], Sort::String);
        assert!(matches!(terms.get(power), TermData::App(name, _) if name.name() == "seq.power"));
    }

    #[test]
    fn structural_sequence_power_retains_its_operator_until_simplified() {
        let mut terms = TermStore::new();
        let base = terms.mk_string("ab".to_string());
        let count = terms.mk_int(2.into());
        let power =
            terms.mk_app_structural(Symbol::named("seq.power"), [base, count], Sort::String);
        assert!(matches!(terms.get(power), TermData::App(name, args)
            if name.name() == "seq.power" && args == &[base, count]));
        let length = terms.mk_app_structural(Symbol::named("str.len"), [power], Sort::Int);
        assert!(matches!(terms.get(length), TermData::App(name, args)
            if name.name() == "str.len" && args == &[power]));
        let simplified_power = terms.simplify(power);
        assert_ne!(simplified_power, power);
        assert!(
            matches!(terms.get(simplified_power), TermData::Const(Constant::String(value)) if value == "abab")
        );
    }

    fn numeric_value(terms: &TermStore, term: TermId, exponent: i64) -> i64 {
        match terms.get(term) {
            TermData::Const(Constant::Int(value)) => value.to_i64().unwrap(),
            TermData::Var(name, _) if name == "n" => exponent,
            TermData::Ite(condition, left, right) => {
                let chosen = if numeric_value(terms, *condition, exponent) != 0 {
                    left
                } else {
                    right
                };
                numeric_value(terms, *chosen, exponent)
            }
            TermData::App(name, args) if name.name() == "str.len" => length(terms, args[0]) as i64,
            TermData::App(name, args) if name.name() == "*" => args
                .iter()
                .map(|&arg| numeric_value(terms, arg, exponent))
                .product(),
            TermData::App(name, args) if name.name() == "<=" => i64::from(
                numeric_value(terms, args[0], exponent) <= numeric_value(terms, args[1], exponent),
            ),
            _ => panic!("unexpected numeric expression"),
        }
    }

    #[test]
    fn sequence_power_symbolic_length_handles_both_signs_without_expansion() {
        let mut terms = TermStore::new();
        let base = terms.mk_string("λ🦀".to_string());
        let count = terms.mk_var("n".to_string(), Sort::Int);
        let power = terms.mk_app(Symbol::named("seq.power"), [base, count], Sort::String);
        let size = terms.mk_app(Symbol::named("str.len"), [power], Sort::Int);
        for exponent in [-1000i64, -1, 0, 1, 3, 1000] {
            assert_eq!(numeric_value(&terms, size, exponent), exponent.max(0) * 2);
        }
    }
}
