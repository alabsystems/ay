// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl ContextProof<'_, '_, '_> {
    pub(super) fn reflexive_ult(&mut self, term: TermId) -> Option<Equality> {
        let word = self.proof.vector(term, 0)?;
        let changed = self
            .proof
            .congruence("bvult", &[word.equality.clone(), word.equality])?;
        let mut previous = None;
        for bit in word.bits {
            let generated = self.proof.equality(
                &format!("(and (not {bit}) {bit})"),
                "false",
                "and_simplify",
                &[],
            )?;
            let Some(carry) = previous else {
                previous = Some(generated);
                continue;
            };
            let same =
                self.proof
                    .equality(&format!("(= {bit} {bit})"), "true", "equiv_simplify", &[])?;
            let propagated = self.proof.congruence("and", &[same, carry])?;
            let reduced = self
                .proof
                .equality(&propagated.right, "false", "and_simplify", &[])?;
            let propagated = self.proof.chain(propagated, reduced)?;
            let combined = self.proof.congruence("or", &[propagated, generated])?;
            let reduced = self
                .proof
                .equality(&combined.right, "false", "or_simplify", &[])?;
            let mut combined = self.proof.chain(combined, reduced)?;
            combined.left = self.proof.define_term(&combined.left, "Bool")?;
            previous = Some(combined);
        }
        let previous = previous?;
        let blasted = self
            .proof
            .equality(&changed.right, &previous.left, "bitblast_ult", &[])?;
        let changed = self.proof.chain(changed, blasted)?;
        self.proof.chain(changed, previous)
    }
}
