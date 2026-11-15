// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Postorder dispatch to the existing Boolean gates, without recursive scratch.

use super::*;

impl BvSolver<'_> {
    pub(crate) fn counted_bool(&mut self, term: TermId) -> CnfLit {
        if !self.encoding_step() {
            return 0;
        }
        if let Some(&literal) = self.bool_to_var.get(&term) {
            return literal;
        }
        let Some(data) = self.counted_term_data(term) else {
            return 0;
        };
        let literal = match data {
            TermData::Const(Constant::Bool(value)) => {
                let literal = self.fresh_var();
                self.emit_clause(&[if value { literal } else { -literal }]);
                literal
            }
            TermData::Var(..) => self.fresh_var(),
            TermData::Not(child) => -self.counted_bool(child),
            TermData::Ite(c, t, e) => {
                if !memory::set(&mut self.bv_ite_conditions, &self.encoding) {
                    return 0;
                }
                self.bv_ite_conditions.insert(c);
                let c = self.counted_bool(c);
                let t = self.counted_bool(t);
                let e = self.counted_bool(e);
                self.mk_mux(t, e, c)
            }
            TermData::App(symbol, args) => self.counted_bool_app(term, symbol.name(), &args),
            _ => {
                self.counted_unsupported("untyped Boolean dispatch");
                return 0;
            }
        };
        if !self.encoding_complete() || !memory::map(&mut self.bool_to_var, &self.encoding) {
            return 0;
        }
        self.bool_to_var.insert(term, literal);
        literal
    }

    fn counted_bool_app(&mut self, term: TermId, name: &str, args: &[TermId]) -> CnfLit {
        if let Some(literal) = self.bitblast_predicate(term) {
            return literal;
        }
        if !self.encoding_complete() {
            return 0;
        }
        if matches!(name, "=" | "distinct") && args.len() == 2 {
            let eq = if self.terms.sort(args[0]) == &Sort::Bool {
                let a = self.counted_bool(args[0]);
                let b = self.counted_bool(args[1]);
                self.mk_xnor(a, b)
            } else {
                self.bitblast_term_eq(args[0], args[1])
            };
            return if name == "distinct" { -eq } else { eq };
        }
        if name == "=>" && args.len() == 2 {
            let a = self.counted_bool(args[0]);
            let b = self.counted_bool(args[1]);
            return self.mk_or(-a, b);
        }
        let Some(mut literals) = self.counted_bits(args.len()) else {
            return 0;
        };
        for &arg in args {
            if !self.encoding_step() {
                return 0;
            }
            literals.push(self.counted_bool(arg));
        }
        match name {
            "and" => self.mk_and_many(&literals),
            "or" => self.mk_or_many(&literals),
            "xor" => {
                let Some((&first, rest)) = literals.split_first() else {
                    return self.fresh_false();
                };
                let mut result = first;
                for &next in rest {
                    if !self.encoding_step() {
                        return 0;
                    }
                    result = self.mk_xor(result, next);
                }
                result
            }
            _ => {
                self.counted_unsupported("unaccounted Boolean application");
                0
            }
        }
    }
}
