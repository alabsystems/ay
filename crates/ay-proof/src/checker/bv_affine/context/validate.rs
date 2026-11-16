// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Validate every original branch and guard before any contextual reduction.

use super::*;

impl Reducer<'_> {
    pub(super) fn validate(&mut self, term: TermId, depth: usize) -> Option<()> {
        self.visit(term, depth)?;
        let sort = self.terms.sort(term);
        if sort != &Sort::Bool && sort != &Sort::bitvec(self.width) {
            return None;
        }
        if let Some((condition, yes, no)) = context_conditional(self.terms, term) {
            for child in [condition, yes, no] {
                self.validate(child, depth + 1)?;
            }
            return (self.terms.sort(condition) == &Sort::Bool
                && self.terms.sort(yes) == sort
                && self.terms.sort(no) == sort)
                .then_some(());
        }
        match self.terms.get(term) {
            TermData::Var(_, _) => Some(()),
            TermData::Const(Constant::Bool(_)) if sort == &Sort::Bool => Some(()),
            TermData::Const(Constant::BitVec { value, width })
                if *width == self.width
                    && sort == &Sort::bitvec(*width)
                    && value.to_u128()? <= self.mask =>
            {
                Some(())
            }
            TermData::Not(inner) if sort == &Sort::Bool => {
                self.validate(*inner, depth + 1)?;
                (self.terms.sort(*inner) == &Sort::Bool).then_some(())
            }
            TermData::App(Symbol::Named(op), args) => self.application(op, args, sort, depth),
            _ => None,
        }
    }

    fn application(&mut self, op: &str, args: &[TermId], sort: &Sort, depth: usize) -> Option<()> {
        let (arity, input, output) = match op {
            "and" | "or" => (2, Sort::Bool, Sort::Bool),
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                (2, Sort::bitvec(self.width), Sort::Bool)
            }
            "=" => {
                if self.terms.is_declared_function(op) {
                    return None;
                }
                let [left, right] = args else {
                    return None;
                };
                self.validate(*left, depth + 1)?;
                self.validate(*right, depth + 1)?;
                return (sort == &Sort::Bool && self.terms.sort(*left) == self.terms.sort(*right))
                    .then_some(());
            }
            "bvadd" | "bvsub" | "bvmul" | "bvand" | "bvor" | "bvxor" | "bvshl" | "bvlshr"
            | "bvashr" => (2, Sort::bitvec(self.width), Sort::bitvec(self.width)),
            "bvneg" | "bvnot" => (1, Sort::bitvec(self.width), Sort::bitvec(self.width)),
            _ => return None,
        };
        if self.terms.is_declared_function(op) {
            return (sort == &Sort::bitvec(self.width)).then_some(());
        }
        if args.len() != arity || sort != &output {
            return None;
        }
        for &arg in args {
            self.validate(arg, depth + 1)?;
            if self.terms.sort(arg) != &input {
                return None;
            }
        }
        Some(())
    }
}
