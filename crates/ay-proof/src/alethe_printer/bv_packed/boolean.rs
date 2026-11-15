// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl PackedProof<'_, '_> {
    pub(super) fn vector_equality(&mut self, left: Value, right: Value) -> Option<Equality> {
        if left.bits.len() != right.bits.len() {
            return None;
        }
        let changed = self.congruence("=", &[left.equality, right.equality])?;
        let mut simplified = Vec::with_capacity(left.bits.len());
        for (left, right) in left.bits.iter().zip(&right.bits) {
            simplified.push(self.simplify_equal(left, right)?);
        }
        let (expanded, reduced) = if simplified.len() == 1 {
            (simplified[0].left.clone(), simplified.remove(0))
        } else {
            let changed = self.congruence("and", &simplified)?;
            let simple = self.simplify_and(&simplified)?;
            (changed.left.clone(), self.chain(changed, simple)?)
        };
        let blasted = self.equality(&changed.right, &expanded, "bitblast_equal", &[])?;
        let equality = self.chain(changed, blasted)?;
        self.chain(equality, reduced)
    }

    pub(super) fn simplify_ite(
        &mut self,
        condition: &str,
        yes: &str,
        no: &str,
    ) -> Option<Equality> {
        let source = format!("(ite {condition} {yes} {no})");
        let target = if condition == "true" || yes == no {
            yes.into()
        } else if condition == "false" {
            no.into()
        } else if yes == "true" && no == "false" {
            condition.into()
        } else if yes == "false" && no == "true" {
            format!("(not {condition})")
        } else {
            return self.equality(&source, &source, "refl", &[]);
        };
        self.equality(&source, &target, "ite_simplify", &[])
    }

    pub(super) fn simplify_equal(&mut self, left: &str, right: &str) -> Option<Equality> {
        let source = format!("(= {left} {right})");
        let target = if left == right {
            "true".into()
        } else if left == format!("(not {right})") || right == format!("(not {left})") {
            "false".into()
        } else if left == "true" {
            right.into()
        } else if right == "true" {
            left.into()
        } else if left == "false" {
            format!("(not {right})")
        } else if right == "false" {
            format!("(not {left})")
        } else {
            return self.equality(&source, &source, "refl", &[]);
        };
        self.equality(&source, &target, "equiv_simplify", &[])
    }

    pub(super) fn simplify_and(&mut self, args: &[Equality]) -> Option<Equality> {
        let mut unique = Vec::new();
        for arg in args {
            if arg.right != "true" && !unique.contains(&arg.right.as_str()) {
                unique.push(arg.right.as_str());
            }
        }
        let source = application("and", args.iter().map(|a| a.right.as_str()));
        let target = if unique.contains(&"false") {
            "false".into()
        } else {
            match unique.as_slice() {
                [] => "true".into(),
                [only] => {
                    let only = (*only).to_string();
                    return self.simplify_to_survivor(&source, &only, "and", "and_simplify");
                }
                _ => application("and", unique),
            }
        };
        self.equality(&source, &target, "and_simplify", &[])
    }
}
