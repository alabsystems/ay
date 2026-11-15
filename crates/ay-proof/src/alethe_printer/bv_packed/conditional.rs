// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

impl PackedProof<'_, '_> {
    pub(super) fn vector_conditional(
        &mut self,
        condition: TermId,
        then_term: TermId,
        else_term: TermId,
        width: usize,
        depth: usize,
    ) -> Option<Value> {
        let condition = self.boolean(condition, depth + 1)?;
        let then_value = self.vector(then_term, depth + 1)?;
        let else_value = self.vector(else_term, depth + 1)?;
        if then_value.bits.len() != width || else_value.bits.len() != width {
            return None;
        }
        let changed = self.congruence(
            "ite",
            &[condition.clone(), then_value.equality, else_value.equality],
        )?;
        let distributed = self.distribute(&condition.right, &then_value.bits, &else_value.bits)?;
        let mut simplified = Vec::with_capacity(width);
        for (yes, no) in then_value.bits.iter().zip(&else_value.bits) {
            simplified.push(self.simplify_ite(&condition.right, yes, no)?);
        }
        let bits = simplified.iter().map(|bit| bit.right.clone()).collect();
        let reduced = self.congruence("@bbterm", &simplified)?;
        let equality = self.chain(changed, distributed)?;
        Some(Value {
            equality: self.chain(equality, reduced)?,
            bits,
        })
    }

    pub(super) fn distribute(
        &mut self,
        condition: &str,
        yes: &[String],
        no: &[String],
    ) -> Option<Equality> {
        if yes.len() != no.len() || yes.is_empty() || yes.len() > MAX_WIDTH {
            return None;
        }
        let source = format!("(ite {condition} {} {})", bbterm(yes), bbterm(no));
        let bits: Vec<_> = yes
            .iter()
            .zip(no)
            .map(|(y, n)| format!("(ite {condition} {y} {n})"))
            .collect();
        let target = bbterm(&bits);
        if matches!(condition, "true" | "false") {
            return self.distribute_constant(condition, yes, no);
        }
        let cases = [true, false]
            .map(|positive| self.distribution_case(condition, yes, no, &source, &target, positive));
        let [Some(positive), Some(negative)] = cases else {
            return None;
        };
        self.equality(&source, &target, "resolution", &[&positive, &negative])
    }

    fn distribute_constant(
        &mut self,
        condition: &str,
        yes: &[String],
        no: &[String],
    ) -> Option<Equality> {
        let left = self.simplify_ite(condition, &bbterm(yes), &bbterm(no))?;
        let mut bits = Vec::with_capacity(yes.len());
        for (yes, no) in yes.iter().zip(no) {
            bits.push(self.simplify_ite(condition, yes, no)?);
        }
        let right = self.congruence("@bbterm", &bits)?;
        let reversed = self.equality(&right.right, &right.left, "symm", &[&right.step])?;
        self.chain(left, reversed)
    }

    fn distribution_case(
        &mut self,
        condition: &str,
        yes: &[String],
        no: &[String],
        source: &str,
        target: &str,
        positive: bool,
    ) -> Option<String> {
        let end = self.fresh();
        let assumption = self.fresh();
        let literal = if positive {
            condition.into()
        } else {
            format!("(not {condition})")
        };
        let value = positive.to_string();
        self.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {literal})\n"
        ))?;
        let equation = format!("(= {condition} {value})");
        let simplified = self.equality(&equation, &literal, "equiv_simplify", &[])?;
        let implication = self.step(
            &format!("{equation} (not {literal})"),
            "equiv2",
            &[&simplified.step],
        )?;
        let condition_step = self.step(&equation, "resolution", &[&implication, &assumption])?;
        let condition_eq = Equality {
            left: condition.into(),
            right: value,
            step: condition_step,
        };
        let yes_text = bbterm(yes);
        let no_text = bbterm(no);
        let yes_eq = self.equality(&yes_text, &yes_text, "refl", &[])?;
        let no_eq = self.equality(&no_text, &no_text, "refl", &[])?;
        let changed = self.congruence("ite", &[condition_eq.clone(), yes_eq, no_eq])?;
        let simple = self.simplify_ite(&condition_eq.right, &yes_text, &no_text)?;
        let left = self.chain(changed, simple)?;
        let mut bits = Vec::with_capacity(yes.len());
        for (yes, no) in yes.iter().zip(no) {
            let yes_eq = self.equality(yes, yes, "refl", &[])?;
            let no_eq = self.equality(no, no, "refl", &[])?;
            let changed = self.congruence("ite", &[condition_eq.clone(), yes_eq, no_eq])?;
            let simple = self.simplify_ite(&condition_eq.right, yes, no)?;
            bits.push(self.chain(changed, simple)?);
        }
        let right = self.congruence("@bbterm", &bits)?;
        let reversed = self.equality(&right.right, &right.left, "symm", &[&right.step])?;
        let final_eq = self.chain(left, reversed)?;
        if final_eq.left != source || final_eq.right != target {
            return None;
        }
        self.named_step(
            &end,
            &format!("(not {literal}) (= {source} {target})"),
            "subproof",
            &[],
            &format!(" :discharge ({assumption})"),
        )?;
        Some(end)
    }
}
