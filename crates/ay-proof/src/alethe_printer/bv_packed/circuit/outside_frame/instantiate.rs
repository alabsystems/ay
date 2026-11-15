// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Outside {
    pub(in crate::alethe_printer::bv_packed::circuit) fn different(
        &self,
        proof: &mut PackedProof<'_, '_>,
        key: TermId,
        outside_unit: &str,
    ) -> Option<String> {
        let offset = self.shape.offset(proof.printer.terms, key)?;
        let literal = |n| format!("(_ bv{n} {})", self.shape.width);
        let start = proof.printer.format_term(self.shape.start);
        let observe = proof.printer.format_term(self.shape.observe);
        let guard = proof.printer.format_term(self.shape.guard);
        let outside = proof.printer.format_term(self.shape.outside);
        let at = format!("(bvadd {start} {})", literal(offset));
        let within = format!("(bvult {} {})", literal(offset), literal(self.shape.length));
        let equal = format!("(= {observe} {at})");
        let query = format!("(and {guard} {outside} {within} {equal})");
        let inst = proof.fresh();
        proof.named_step(
            &inst,
            &format!("(or (not {}) (not {query}))", self.universal),
            "forall_inst",
            &[],
            &format!(" :args ({})", literal(offset)),
        )?;
        let expanded = proof.step(
            &format!("(not {}) (not {query})", self.universal),
            "or",
            &[&inst],
        )?;
        let negative = proof.step(
            &format!("(not {query})"),
            "resolution",
            &[&self.unit, &expanded],
        )?;
        let evaluated = proof.equality(&within, "true", "evaluate", &[])?;
        let reverse = proof.equality("true", &within, "symm", &[&evaluated.step])?;
        let yes = proof.step("true", "true", &[])?;
        let bound = proof.transport_unit(&reverse, &yes)?;
        let implication = proof.step(
            &format!("{query} (not {guard}) (not {outside}) (not {within}) (not {equal})"),
            "and_neg",
            &[],
        )?;
        let unit = proof.step(
            &format!("(not {equal})"),
            "resolution",
            &[
                &implication,
                &negative,
                &self.guard_unit,
                outside_unit,
                &bound,
            ],
        )?;
        let key = proof.printer.format_term(key);
        let normalized = proof.equality(&key, &at, "poly_simp", &[])?;
        let unchanged = proof.equality(&observe, &observe, "refl", &[])?;
        let moved = proof.congruence("=", &[unchanged, normalized])?;
        let moved = proof.congruence("not", &[moved])?;
        let reverse = proof.equality(&moved.right, &moved.left, "symm", &[&moved.step])?;
        let unit = proof.transport_unit(&reverse, &unit)?;
        proof.step(&format!("(not (= {key} {observe}))"), "not_symm", &[&unit])
    }
}
