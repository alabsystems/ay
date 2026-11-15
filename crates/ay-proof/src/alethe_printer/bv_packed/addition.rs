// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Checked additions with a constant per bit, or exact opaque word decomposition.

use super::boolean_cases::Boolean;
use super::*;

impl PackedProof<'_, '_> {
    pub(super) fn addition(
        &mut self,
        args: &[TermId],
        width: usize,
        depth: usize,
    ) -> Option<Value> {
        let [left, right] = args else { return None };
        let left = self.vector(*left, depth + 1)?;
        let right = self.vector(*right, depth + 1)?;
        self.addition_values(left, right, width)
    }

    pub(super) fn addition_values(
        &mut self,
        left: Value,
        right: Value,
        width: usize,
    ) -> Option<Value> {
        if left.bits.len() != width || right.bits.len() != width {
            return None;
        }
        let changed = self.congruence("bvadd", &[left.equality, right.equality])?;
        if !left.bits.iter().zip(&right.bits).all(|(a, b)| {
            matches!(a.as_str(), "true" | "false") || matches!(b.as_str(), "true" | "false")
        }) {
            // Keep the complete normalized sum as an atom. bitblast_var checks
            // this word's exact bit decomposition, including compound terms.
            let name = self.define_term(&changed.right, &format!("(_ BitVec {width})"))?;
            let bits = (0..width)
                .map(|i| format!("((_ @bit_of {i}) {name})"))
                .collect();
            let blasted = self.blast(&changed.right, bits, "bitblast_var")?;
            return Some(Value {
                equality: self.chain(changed, blasted.equality)?,
                bits: blasted.bits,
            });
        }
        let mut carry = self.equality("false", "false", "refl", &[])?;
        let mut sums = Vec::new();
        for (i, (a, b)) in left.bits.iter().zip(&right.bits).enumerate() {
            let parity = self.equality(
                &format!("(xor {a} {b})"),
                &format!("(xor {a} {b})"),
                "refl",
                &[],
            )?;
            let source = self.congruence("xor", &[parity, carry.clone()])?;
            let (constant, variable) = if matches!(a.as_str(), "true" | "false") {
                (a, b)
            } else {
                (b, a)
            };
            let parity = self.normal_gate("xor", variable, &carry.right)?;
            let target = if constant == "true" {
                negate(&parity)
            } else {
                parity
            };
            let normal = self.boolean_identity(
                Boolean::app(
                    "xor",
                    [
                        Boolean::app("xor", [Boolean::term(a), Boolean::term(b)]),
                        Boolean::term(&carry.right),
                    ],
                ),
                Boolean::term(&target),
            )?;
            sums.push(self.chain(source, normal)?);
            if i + 1 < width {
                carry = self.addition_carry(a, b, constant, variable, carry)?;
            }
        }
        let raw: Vec<_> = sums.iter().map(|sum| sum.left.clone()).collect();
        let bits: Vec<_> = sums.iter().map(|sum| sum.right.clone()).collect();
        self.define_word(&raw)?;
        self.define_word(&bits)?;
        let blasted = self.equality(&changed.right, &bbterm(&raw), "bitblast_add", &[])?;
        let references: Vec<_> = sums.iter().map(|sum| sum.step.as_str()).collect();
        let simplified = self.equality(&bbterm(&raw), &bbterm(&bits), "cong", &references)?;
        let equality = self.chain(changed, blasted)?;
        Some(Value {
            equality: self.chain(equality, simplified)?,
            bits,
        })
    }

    fn addition_carry(
        &mut self,
        a: &str,
        b: &str,
        constant: &str,
        variable: &str,
        carry: Equality,
    ) -> Option<Equality> {
        let parity = format!("(xor {a} {b})");
        let parity = self.equality(&parity, &parity, "refl", &[])?;
        let propagated = self.congruence("and", &[parity, carry.clone()])?;
        let generated = format!("(and {a} {b})");
        let generated = self.equality(&generated, &generated, "refl", &[])?;
        let changed = self.congruence("or", &[generated, propagated])?;
        let target = self.normal_gate(
            if constant == "true" { "or" } else { "and" },
            variable,
            &carry.right,
        )?;
        let source = Boolean::app(
            "or",
            [
                Boolean::app("and", [Boolean::term(a), Boolean::term(b)]),
                Boolean::app(
                    "and",
                    [
                        Boolean::app("xor", [Boolean::term(a), Boolean::term(b)]),
                        Boolean::term(&carry.right),
                    ],
                ),
            ],
        );
        let normalized = self.boolean_identity(source, Boolean::term(&target))?;
        let mut equality = self.chain(changed, normalized)?;
        // Definitions are pure abbreviations, expanded by the consumer. Sharing
        // carries keeps the exact checker topology linear in serialized size.
        equality.left = self.define_term(&equality.left, "Bool")?;
        equality.right = self.share_boolean(&equality.right)?;
        Some(equality)
    }

    fn normal_gate(&mut self, op: &'static str, a: &str, b: &str) -> Option<String> {
        let result = match op {
            "and" if a == "false" || b == "false" => "false".into(),
            "and" if a == "true" || a == b => b.into(),
            "and" if b == "true" => a.into(),
            "or" if a == "true" || b == "true" => "true".into(),
            "or" if a == "false" || a == b => b.into(),
            "or" if b == "false" => a.into(),
            "xor" if a == "false" => b.into(),
            "xor" if b == "false" => a.into(),
            "xor" if a == "true" => negate(b),
            "xor" if b == "true" => negate(a),
            "xor" if a == b => "false".into(),
            _ => format!("({op} {a} {b})"),
        };
        // Do not hide a parity expression until its local case proof has seen
        // its constituent atoms. Carries are shared after that proof closes.
        Some(result)
    }

    fn share_boolean(&mut self, term: &str) -> Option<String> {
        if term.starts_with("(and ") || term.starts_with("(or ") || term.starts_with("(xor ") {
            self.define_term(term, "Bool")
        } else {
            Some(term.into())
        }
    }
}

fn negate(term: &str) -> String {
    match term {
        "true" => "false".into(),
        "false" => "true".into(),
        _ => term
            .strip_prefix("(not ")
            .and_then(|s| s.strip_suffix(')'))
            .map_or_else(|| format!("(not {term})"), str::to_owned),
    }
}
