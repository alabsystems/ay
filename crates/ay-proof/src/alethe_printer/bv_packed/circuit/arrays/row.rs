// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl Circuit<'_, '_, '_> {
    pub(super) fn read_over_write(&mut self, write: &Write, key: &str) -> Option<Equality> {
        let index = &write.index.text;
        let read = format!("(select {} {key})", write.outer);
        let previous = format!("(select {} {key})", write.inner);
        let condition = format!("(= {index} {key})");
        let target = format!("(ite {condition} {} {previous})", write.value.equality.left);
        let sort = format!("(_ BitVec {})", write.value.bits.len());
        for text in [&read, &previous, &target] {
            self.proof.define_term(text, &sort)?;
        }
        let yes = self.row_case(write, key, &read, &previous, &condition, &target, true)?;
        let no = self.row_case(write, key, &read, &previous, &condition, &target, false)?;
        self.proof
            .equality(&read, &target, "resolution", &[&yes, &no])
    }

    fn row_case(
        &mut self,
        write: &Write,
        key: &str,
        read: &str,
        previous: &str,
        condition: &str,
        target: &str,
        positive: bool,
    ) -> Option<String> {
        let end = self.proof.fresh();
        let assumption = self.proof.fresh();
        let literal = if positive {
            condition.into()
        } else {
            format!("(not {condition})")
        };
        self.proof.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {literal})\n"
        ))?;
        let left = if positive {
            let at_index = format!("(select {} {})", write.outer, write.index.text);
            let reverse = self
                .proof
                .equality(key, &write.index.text, "symm", &[&assumption])?;
            let moved = self
                .proof
                .equality(read, &at_index, "cong", &[&reverse.step])?;
            let value =
                self.proof
                    .equality(&at_index, &write.value.equality.left, "arrays_idx", &[])?;
            self.proof.chain(moved, value)?
        } else {
            self.proof
                .equality(read, previous, "arrays_row", &[&assumption])?
        };
        let truth = positive.to_string();
        let equation = format!("(= {condition} {truth})");
        let simple = self
            .proof
            .equality(&equation, &literal, "equiv_simplify", &[])?;
        let implication = self.proof.step(
            &format!("{equation} (not {literal})"),
            "equiv2",
            &[&simple.step],
        )?;
        let unit = self
            .proof
            .step(&equation, "resolution", &[&implication, &assumption])?;
        let guard = Equality {
            left: condition.into(),
            right: truth.clone(),
            step: unit,
        };
        let yes = self.proof.equality(
            &write.value.equality.left,
            &write.value.equality.left,
            "refl",
            &[],
        )?;
        let no = self.proof.equality(previous, previous, "refl", &[])?;
        let changed = self.proof.congruence("ite", &[guard, yes, no])?;
        let reduced = self
            .proof
            .simplify_ite(&truth, &write.value.equality.left, previous)?;
        let right = self.proof.chain(changed, reduced)?;
        let reverse = self
            .proof
            .equality(&right.right, &right.left, "symm", &[&right.step])?;
        let result = self.proof.chain(left, reverse)?;
        if result.left != read || result.right != target {
            return None;
        }
        self.proof.named_step(
            &end,
            &format!(
                "(not {literal}) (= {} {})",
                self.proof.spelling(read),
                self.proof.spelling(target)
            ),
            "subproof",
            &[],
            &format!(" :discharge ({assumption})"),
        )?;
        Some(end)
    }
}
