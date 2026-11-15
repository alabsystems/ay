// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Derive an exact complement sum, then transport it through checked BV algebra.

use super::super::dialect::attempt;
use super::boolean_cases::Boolean;
use super::*;

impl AlethePrinter<'_> {
    pub(crate) fn format_bv_structural_arithmetic(
        &self,
        id: ProofId,
        clause: &[TermId],
        kind: &ay_core::TheoryLemmaKind,
        budget: &mut crate::ArithPolySimpPromotionBudget,
    ) -> Option<String> {
        if !matches!(kind, ay_core::TheoryLemmaKind::ArithClauseTautology)
            || !budget.spend_attempt()
            || self.support_declined(kind, clause)
        {
            return None;
        }
        self.format_bv_structural_arithmetic_attempt(id, clause)
    }

    /// [`Self::format_bv_structural_arithmetic`] once its attempt is spent:
    /// what it prints reads the lemma and this printer, never the budget.
    pub(in crate::alethe_printer) fn format_bv_structural_arithmetic_attempt(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        // Each lane keeps its Clean-only notes only when it produces text.
        attempt(|| self.format_bv_complement_affine_identity(id, clause))
            .or_else(|| attempt(|| self.format_bv_guarded_mask_identity(id, clause)))
            .or_else(|| attempt(|| self.format_bv_context_identity(id, clause)))
            .or_else(|| attempt(|| self.format_bv_partition_identity(id, clause)))
            // The checked bit-blast lowering proves the clause itself, whatever
            // lane validated it — external-codegen's 64-bit `x * (2^a - 1) == (x << a)
            // - x`, which the native affine checker admits. Inside this attempt
            // it is charged to the same proof-wide cap as the lanes above, so
            // a proof of many arithmetic lemmas cannot multiply its work.
            .or_else(|| self.format_checked_bv_bitblast_lowering(id, clause))
    }

    pub(in crate::alethe_printer) fn format_bv_complement_affine_identity(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let relation =
            crate::checker::bv_affine::complement_relation(self.terms, clause, &mut |work, _| {
                self.charge(work as u64);
                !self.work_budget_exhausted()
            })
            .ok()??;
        // Render from the authenticated DAG, within the remaining outer work
        // envelope. Every copied byte is charged even if the candidate fails.
        let budget = self.work_budget.map_or(MAX_TEXT as u64, |limit| {
            limit.saturating_sub(self.work_used()).min(MAX_TEXT as u64)
        });
        let raw = AlethePrinter::new_with_overrides_and_budget(self.terms, None, Some(budget));
        let goal = raw.format_term(clause[0]);
        let operand = raw.format_term(relation.operand);
        let constant = raw.format_term(relation.constant);
        let left = raw.format_term(relation.left);
        let right = raw.format_term(relation.right);
        self.charge(raw.work_used());
        if raw.work_budget_exhausted()
            || self.work_budget_exhausted()
            || self.format_term(clause[0]) != goal
        {
            return None;
        }
        let mut proof = PackedProof::new(self, id)?;
        let known = proof.complement_sum(
            &operand,
            &constant,
            relation.constant_first,
            relation.width as usize,
        )?;
        let known_clause = format!("(= {} {})", known.left, known.right);
        let one = format!("(_ bv1 {})", relation.width);
        let factor = format!(
            "#b{:0width$b}",
            relation.coefficient,
            width = relation.width as usize
        );
        let polynomial = proof.equality(
            &format!("(bvmul {factor} (bvsub {} {}))", known.left, known.right),
            &format!("(bvmul {one} (bvsub {left} {right}))"),
            "poly_simp",
            &[],
        )?;
        let relation =
            proof.equality(&known_clause, &goal, "poly_simp_rel", &[&polynomial.step])?;
        let implication = proof.step(
            &format!("(not {known_clause}) {goal}"),
            "equiv1",
            &[&relation.step],
        )?;
        proof.named_step(
            &id.to_string(),
            &goal,
            "resolution",
            &[&known.step, &implication],
            "",
        )?;
        proof.definitions.push_str(&proof.out);
        Some(proof.definitions)
    }
}

impl PackedProof<'_, '_> {
    fn complement_sum(
        &mut self,
        operand: &str,
        constant: &str,
        constant_first: bool,
        width: usize,
    ) -> Option<Equality> {
        let bits: Vec<_> = (0..width)
            .map(|i| format!("((_ @bit_of {i}) {operand})"))
            .collect();
        let ones = vec!["true".into(); width];
        let word = self.equality(operand, &bbterm(&bits), "bitblast_var", &[])?;
        let maximum = self.equality(constant, &bbterm(&ones), "bitblast_const", &[])?;
        let args = if constant_first {
            [maximum.clone(), word.clone()]
        } else {
            [word.clone(), maximum.clone()]
        };
        let changed = self.congruence("bvxor", &args)?;
        let inverted: Vec<_> = bits
            .iter()
            .map(|bit| {
                if constant_first {
                    format!("(xor true {bit})")
                } else {
                    format!("(xor {bit} true)")
                }
            })
            .collect();
        let blasted = self.equality(&changed.right, &bbterm(&inverted), "bitblast_xor", &[])?;
        let inverted_word = self.chain(changed, blasted)?;
        let changed = self.congruence("bvadd", &[word, inverted_word])?;
        let mut carry = self.equality("false", "false", "refl", &[])?;
        let mut sums = Vec::new();
        for (i, (a, b)) in bits.iter().zip(&inverted).enumerate() {
            let parity = format!("(xor {a} {b})");
            let unchanged = self.equality(&parity, &parity, "refl", &[])?;
            let changed = self.congruence("xor", &[unchanged, carry.clone()])?;
            let reduced =
                self.boolean_identity(Boolean::term(&changed.right), Boolean::Constant(true))?;
            sums.push(self.chain(changed, reduced)?);
            if i + 1 < width {
                carry = self.complement_carry(a, b, carry)?;
            }
        }
        let raw: Vec<_> = sums.iter().map(|sum| sum.left.clone()).collect();
        self.define_word(&raw)?;
        self.define_word(&ones)?;
        let blasted = self.equality(&changed.right, &bbterm(&raw), "bitblast_add", &[])?;
        let references: Vec<_> = sums.iter().map(|sum| sum.step.as_str()).collect();
        let reduced = self.equality(&bbterm(&raw), &bbterm(&ones), "cong", &references)?;
        let reverse = self.equality(&maximum.right, &maximum.left, "symm", &[&maximum.step])?;
        let result = self.chain(changed, blasted)?;
        let result = self.chain(result, reduced)?;
        self.chain(result, reverse)
    }

    fn complement_carry(&mut self, a: &str, b: &str, carry: Equality) -> Option<Equality> {
        let parity = format!("(xor {a} {b})");
        let parity = self.equality(&parity, &parity, "refl", &[])?;
        let propagated = self.congruence("and", &[parity, carry])?;
        let generated = format!("(and {a} {b})");
        let generated = self.equality(&generated, &generated, "refl", &[])?;
        let changed = self.congruence("or", &[generated, propagated])?;
        let reduced =
            self.boolean_identity(Boolean::term(&changed.right), Boolean::Constant(false))?;
        let mut result = self.chain(changed, reduced)?;
        result.left = self.define_term(&result.left, "Bool")?;
        Some(result)
    }
}
