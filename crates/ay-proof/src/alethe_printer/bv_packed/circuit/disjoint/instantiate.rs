// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Disjoint {
    pub(in crate::alethe_printer::bv_packed::circuit) fn different(
        &self,
        proof: &mut PackedProof<'_, '_>,
        a: TermId,
        b: TermId,
    ) -> Option<String> {
        let terms = proof.printer.terms;
        let swapped = self.shape.offset(terms, a, 0).is_none();
        let (first, second) = if swapped { (b, a) } else { (a, b) };
        let i = self.shape.offset(terms, first, 0)?;
        let j = self.shape.offset(terms, second, 1)?;
        let literal = |n| format!("(_ bv{n} {})", self.shape.width);
        let starts = self
            .shape
            .spans
            .map(|span| proof.printer.format_term(span.start));
        let normalized = [
            format!("(bvadd {} {})", literal(i), starts[0]),
            format!("(bvadd {} {})", literal(j), starts[1]),
        ];
        let guard = self.guard_text(proof);
        let ina = format!(
            "(bvult {} {})",
            literal(i),
            literal(self.shape.spans[0].length)
        );
        let inb = format!(
            "(bvult {} {})",
            literal(j),
            literal(self.shape.spans[1].length)
        );
        let equal = format!("(= {} {})", normalized[0], normalized[1]);
        let query = format!("(and {guard} {ina} {inb} {equal})");
        let disjunction = format!("(or (not {}) (not {query}))", self.universal);
        let inst = proof.fresh();
        proof.named_step(
            &inst,
            &disjunction,
            "forall_inst",
            &[],
            &format!(" :args ({} {})", literal(i), literal(j)),
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
        let bounds = [ground_true(proof, &ina)?, ground_true(proof, &inb)?];
        let implication = proof.step(
            &format!("{query} (not {guard}) (not {ina}) (not {inb}) (not {equal})"),
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
                &bounds[0],
                &bounds[1],
            ],
        )?;
        let left = proof.equality(
            &proof.printer.format_term(first),
            &normalized[0],
            "poly_simp",
            &[],
        )?;
        let right = proof.equality(
            &proof.printer.format_term(second),
            &normalized[1],
            "poly_simp",
            &[],
        )?;
        let eq = proof.congruence("=", &[left, right])?;
        let eq = proof.congruence("not", &[eq])?;
        let reverse = proof.equality(&eq.right, &eq.left, "symm", &[&eq.step])?;
        let unit = proof.transport_unit(&reverse, &unit)?;
        if swapped {
            proof.step(
                &format!(
                    "(not (= {} {}))",
                    proof.printer.format_term(a),
                    proof.printer.format_term(b)
                ),
                "not_symm",
                &[&unit],
            )
        } else {
            Some(unit)
        }
    }
}

fn ground_true(proof: &mut PackedProof<'_, '_>, term: &str) -> Option<String> {
    let eq = proof.equality(term, "true", "evaluate", &[])?;
    let reverse = proof.equality("true", term, "symm", &[&eq.step])?;
    let yes = proof.step("true", "true", &[])?;
    proof.transport_unit(&reverse, &yes)
}
