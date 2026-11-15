// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Project an authored quantifier and explicitly derive its canonical spelling.

use super::*;

impl AlethePrinter<'_> {
    pub(super) fn quantified_alpha_and_pos_bridge(
        &self,
        id: ProofId,
        selected: TermId,
        index: usize,
        gate: &str,
        target: &str,
        operands: &[&str],
    ) -> Result<Option<String>, AlethePrintError> {
        if !matches!(
            self.terms.get(selected),
            TermData::Forall(..) | TermData::Exists(..)
        ) {
            return Ok(None);
        }
        // Only the corresponding authored position is tried. Reordering or
        // flattening does not trigger an unbounded search over candidate pairs.
        let Some(&source) = operands.get(index) else {
            return Ok(None);
        };
        self.charge((source.len() as u64).saturating_add(target.len() as u64));
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        // The bounded comparator mirrors the independent checker's `refl`:
        // binder alpha-equivalence, literal identity and binary equality
        // reordering. No source spelling is installed on any native term.
        if !super::super::quantifier_surface::printed_terms_alpha_equivalent(source, target) {
            // Elaboration rewrote the body (`=>` into `or`): derive it under `bind`.
            return self.quantified_body_and_pos_bridge(id, selected, index, gate, source, target);
        }
        let output_bound = (source.len() as u64)
            .saturating_add(target.len() as u64)
            .saturating_mul(8)
            .saturating_add((gate.len() as u64).saturating_mul(2))
            .saturating_add(1024);
        self.charge(output_bound);
        if self.work_budget_exhausted() {
            return Err(self.work_budget_error(id.0));
        }
        Ok(Some(format!(
            "(step {id}.qa (cl {gate} {source}) :rule and_pos :args ({index}))\n\
             (step {id}.qr (cl (= {source} {target})) :rule refl)\n\
             (step {id}.qe (cl (not (= {source} {target})) (not {source}) {target}) :rule equiv_pos2)\n\
             (step {id}.qb (cl (not {source}) {target}) :rule resolution :premises ({id}.qr {id}.qe))\n\
             (step {id} (cl {gate} {target}) :rule resolution :premises ({id}.qa {id}.qb))"
        )))
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::TermStore;

    #[test]
    fn quantified_projection_bridge_rejects_capture_sort_and_body_changes() {
        let mut terms = TermStore::new();
        let body = terms.mk_var("p", Sort::Bool);
        let selected = terms.mk_forall(vec![("x".to_string(), Sort::Int)], body);
        let printer = AlethePrinter::new(&terms);
        for (source, target) in [
            ("(forall ((x Int)) (= x y))", "(forall ((y Int)) (= y y))"),
            ("(forall ((x Int)) (P x))", "(forall ((x Real)) (P x))"),
            ("(forall ((x Int)) (P x))", "(forall ((x Int)) (Q x))"),
            (
                "(forall ((x (_ BitVec 8))) (= x #x01))",
                "(forall ((y (_ BitVec 8))) (= y #b00000010))",
            ),
        ] {
            assert!(printer
                .quantified_alpha_and_pos_bridge(
                    ProofId(0),
                    selected,
                    0,
                    "(not source)",
                    target,
                    &[source],
                )
                .unwrap()
                .is_none());
        }
        let bounded = AlethePrinter::new_with_overrides_and_budget(&terms, None, Some(1));
        assert!(bounded
            .quantified_alpha_and_pos_bridge(
                ProofId(0),
                selected,
                0,
                "(not source)",
                "(forall ((y Int)) (P y))",
                &["(forall ((x Int)) (P x))"],
            )
            .is_err());
    }
}
