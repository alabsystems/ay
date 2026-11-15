// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bitblast an unsigned power-of-two bound and project its checked zero bits.

use super::*;

impl PackedProof<'_, '_> {
    pub(super) fn range_zero_facts(
        &mut self,
        guard: TermId,
        bound: TermId,
        source: &Value,
        unit: &str,
    ) -> Option<Vec<Equality>> {
        let bound = self.vector(bound, 0)?;
        let set: Vec<_> = bound
            .bits
            .iter()
            .enumerate()
            .filter(|(_, b)| *b == "true")
            .map(|(i, _)| i)
            .collect();
        let [first] = set.as_slice() else {
            return None;
        };
        let changed = self.congruence("bvult", &[source.equality.clone(), bound.equality])?;
        if changed.left != self.printer.format_term(guard) {
            return None;
        }
        let mut prefix = Vec::new();
        let mut result = self.equality("false", "false", "refl", &[])?;
        for (i, (bit, constant)) in source.bits.iter().zip(&bound.bits).enumerate() {
            result = self.range_stage(bit, constant, i, *first, result)?;
            result.left = self.define_term(&result.left, "Bool")?;
            if i > *first {
                result.right = self.define_term(&result.right, "Bool")?;
            }
            prefix.push(result.right.clone());
        }
        let blasted = self.equality(&changed.right, &result.left, "bitblast_ult", &[])?;
        let changed = self.chain(changed, blasted)?;
        let changed = self.chain(changed, result)?;
        let mut unit = self.transport_unit(&changed, unit)?;
        let mut facts = Vec::new();
        for i in (*first..source.bits.len()).rev() {
            let bit = &source.bits[i];
            let negated = if i == *first {
                unit.clone()
            } else {
                self.project_conjunct(&prefix[i], &unit, &format!("(not {bit})"), 0)?
            };
            facts.push(self.zero_bit(bit, &negated)?);
            if i > *first {
                unit = self.project_conjunct(&prefix[i], &unit, &prefix[i - 1], 1)?;
            }
        }
        Some(facts)
    }

    fn range_stage(
        &mut self,
        bit: &str,
        constant: &str,
        index: usize,
        first: usize,
        previous: Equality,
    ) -> Option<Equality> {
        let generated = format!("(and (not {bit}) {constant})");
        let simple = if constant == "true" {
            format!("(not {bit})")
        } else {
            "false".into()
        };
        let generated = self.equality(&generated, &simple, "and_simplify", &[])?;
        if index == 0 {
            return Some(generated);
        }
        let equal = self.simplify_equal(bit, constant)?;
        let propagated = self.congruence("and", &[equal, previous])?;
        let target = if index <= first {
            "false".into()
        } else {
            propagated.right.clone()
        };
        let reduced = self.equality(
            &propagated.right,
            &target,
            if index <= first {
                "and_simplify"
            } else {
                "refl"
            },
            &[],
        )?;
        let propagated = self.chain(propagated, reduced)?;
        let combined = self.congruence("or", &[propagated, generated])?;
        let target = if index < first {
            "false".into()
        } else if index == first {
            format!("(not {bit})")
        } else {
            target
        };
        // Past `first`, `generated` is `false` and the ONE survivor is the
        // propagated disjunct, which can itself be an `or`.
        let reduced = if index > first {
            self.simplify_to_survivor(&combined.right, &target, "or", "or_simplify")?
        } else {
            self.equality(&combined.right, &target, "or_simplify", &[])?
        };
        self.chain(combined, reduced)
    }
}
