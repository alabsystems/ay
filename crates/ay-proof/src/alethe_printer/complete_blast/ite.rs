// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The bit-vector `ite`. The pinned checker has no rule that bit-blasts one,
//! so its bits stay free `@bit_of` atoms and its meaning arrives as two
//! guarded clauses, `(cl (not c) E_then)` and `(cl c E_else)`, over the bit
//! equalities of the value with each branch. Each is recorded as a
//! [`sweep::GuardedIte`] so the sweep simulates the bits as the `ite` they
//! are and gives every lemma about them the clauses that define them, and as
//! the word's DEFINITION for the case split (`crate::sat_sweep::split`).
//!
//! ## Chain shortcuts
//!
//! A priority chain `W0 = ite(c0, v0, W1)`, `W1 = ite(c1, v1, W2)`, … relates
//! `W0` to the level `Wk` a case selects only through every level between:
//! bit by bit, `k` guarded equalities. A case split that visits each level
//! pays that walk once per case, for every bit, and on proof_gate_strict row
//! 1257 (a 54-level chain, 52 live bits) the walks were most of the printed
//! document. The chain's SHORTCUTS are the word equalities `Tk = (= W0 Wk)`,
//! each a theory atom tied to its own bit-blast, and one `eq_transitive`
//! clause per level, `(cl (not T(k-1)) (not (= W(k-1) Wk)) Tk)`: under a case
//! that passes the first `k` levels, propagation reaches `Tk`, and every bit
//! of `W0` is one equality away from `Wk`.

use super::*;

/// Chains shorter than this keep no shortcuts: their walks are short.
const MIN_CHAIN_LEVELS: usize = 4;

#[cfg(test)]
#[path = "ite_tests.rs"]
mod tests;

impl Blaster<'_, '_> {
    /// A bit-vector `ite` has no bit-blasting rule in the pinned checker. Its
    /// bits stay free and its semantics arrive as clauses: `ite_intro` proves
    /// the guarded-equality conjunction outright, and `ite1`/`ite2` split it.
    pub(super) fn build_bitvector_ite(
        &mut self,
        cond: TermId,
        then_branch: TermId,
        else_branch: TermId,
        width: u32,
    ) -> Option<usize> {
        let condition = self.bool_of.get(&cond).copied()?;
        let then_word = self.word_of_term(then_branch)?;
        let else_word = self.word_of_term(else_branch)?;
        if self.words[then_word].width != width || self.words[else_word].width != width {
            return None;
        }
        let body = format!(
            "(ite {} {} {})",
            self.circuit.text(condition),
            self.word_ref(then_word),
            self.word_ref(else_word)
        );
        let word = self.new_word(body, width, WordOp::Leaf)?;
        self.ite_else.insert(word, else_word);

        let value = self.word_ref(word);
        let then_reference = self.word_ref(then_word);
        let else_reference = self.word_ref(else_word);
        let condition_text = self.circuit.text(condition);
        let guarded = format!(
            "(ite {condition_text} (= {value} {then_reference}) (= {value} {else_reference}))"
        );
        let conjunction = format!("(and true {guarded})");
        let intro = self.step_name(".ti");
        let lifted = self.step_name(".tl");
        let conjoined = self.step_name(".tc");
        let projected = self.step_name(".tp");
        let then_case = self.step_name(".tt");
        let else_case = self.step_name(".te");
        let true_step = self.true_step();
        self.push_step(&format!(
            "(step {intro} (cl (= true {conjunction})) :rule ite_intro)"
        ))?;
        self.push_step(&format!(
            "(step {lifted} (cl (not true) {conjunction}) :rule equiv1 :premises ({intro}))"
        ))?;
        self.push_step(&format!(
            "(step {conjoined} (cl {conjunction}) :rule resolution :premises ({true_step} {lifted}))"
        ))?;
        self.push_step(&format!(
            "(step {projected} (cl {guarded}) :rule and :premises ({conjoined}) :args (1))"
        ))?;
        self.push_step(&format!(
            "(step {then_case} (cl (not {condition_text}) (= {value} {then_reference})) :rule ite2 :premises ({projected}))"
        ))?;
        self.push_step(&format!(
            "(step {else_case} (cl {condition_text} (= {value} {else_reference})) :rule ite1 :premises ({projected}))"
        ))?;

        let negated_condition = condition.not()?;
        let first_clause = self.planned.len();
        let then_equal = self.ite_branch(word, then_word, &then_case, negated_condition)?;
        let else_equal = self.ite_branch(word, else_word, &else_case, condition)?;
        // The word's bits are free; these two clauses are all they mean.
        self.ite_definitions
            .push(crate::sat_sweep::split::Definition {
                vars: self.words[word]
                    .bits
                    .iter()
                    .map(|bit| bit.gate as usize)
                    .collect(),
                clauses: (first_clause..self.planned.len()).collect(),
            });
        let value = self.words[word].bits.clone();
        let then_bits = self.words[then_word].bits.clone();
        let else_bits = self.words[else_word].bits.clone();
        // The conjuncts `bit_equality` built, interned: the same gates.
        let links = (0..value.len())
            .map(|i| {
                [
                    self.circuit.iff(value[i], then_bits[i]),
                    self.circuit.iff(value[i], else_bits[i]),
                ]
            })
            .collect();
        self.guarded_ites.push(sweep::GuardedIte {
            condition,
            value,
            then_bits,
            else_bits,
            equalities: [then_equal, else_equal],
            links,
        });
        Some(word)
    }

    /// Plan every priority chain's shortcuts (see "Chain shortcuts"): the
    /// indices of the planned `eq_transitive` clauses, each implied by the
    /// rest of the CNF. Their atoms' gates are left for the caller to define
    /// and structure.
    pub(super) fn plan_chain_shortcuts(&mut self) -> Option<Vec<usize>> {
        if !ay_core::is_checkable_alethe_rule("eq_transitive") {
            return Some(Vec::new());
        }
        let inner: DetHashSet<usize> = self
            .ite_else
            .values()
            .copied()
            .filter(|word| self.ite_else.contains_key(word))
            .collect();
        let mut heads: Vec<usize> = self
            .ite_else
            .keys()
            .copied()
            .filter(|word| !inner.contains(word))
            .collect();
        heads.sort_unstable();
        let mut implied = Vec::new();
        for head in heads {
            let mut chain = vec![head];
            while let Some(&next) = self.ite_else.get(chain.last()?) {
                if !self.ite_else.contains_key(&next) || chain.contains(&next) {
                    break;
                }
                chain.push(next);
            }
            if chain.len() < MIN_CHAIN_LEVELS {
                continue;
            }
            let top = chain[0];
            let mut reached = self.theory_atom(top, chain[1], AtomKind::Equality)?;
            for pair in chain[1..].windows(2) {
                let (from, to) = (pair[0], pair[1]);
                let link = self.theory_atom(from, to, AtomKind::Equality)?;
                let next = self.theory_atom(top, to, AtomKind::Equality)?;
                let step = self.step_name(".tq");
                self.push_step(&format!(
                    "(step {step} (cl (not {}) (not {}) {}) :rule eq_transitive)",
                    self.circuit.text(reached),
                    self.circuit.text(link),
                    self.circuit.text(next)
                ))?;
                implied.push(self.planned.len());
                self.plan(
                    vec![reached.not()?, link.not()?, next],
                    ClauseEmit::Existing(step),
                )?;
                reached = next;
            }
        }
        Some(implied)
    }

    /// Reduce one guarded branch equality of a bit-vector `ite` to a clause
    /// over the branch's already-derived bits; the bit equality it guards.
    fn ite_branch(
        &mut self,
        value_word: usize,
        branch_word: usize,
        guard_step: &str,
        guard: SRef,
    ) -> Option<SRef> {
        let value = self.word_ref(value_word);
        let branch = self.word_ref(branch_word);
        let value_bits = self.words[value_word].bits.clone();
        let branch_bits = self.words[branch_word].bits.clone();
        let equality = format!("(= {value} {branch})");
        let application = format!(
            "(= {} {})",
            self.bbterm(&value_bits),
            self.bbterm(&branch_bits)
        );
        let blasted = self.bit_equality(&value_bits, &branch_bits)?;
        let blasted_text = self.circuit.text(blasted);
        let congruence = self.step_name(".bc");
        let rule_step = self.step_name(".bb");
        let chained = self.step_name(".bt");
        let split = self.step_name(".bs");
        let clause_step = self.step_name(".br");
        let value_step = self.words[value_word].step.clone();
        let branch_step = self.words[branch_word].step.clone();
        self.push_step(&format!(
            "(step {congruence} (cl (= {equality} {application})) :rule cong :premises ({value_step} {branch_step}))"
        ))?;
        self.push_step(&format!(
            "(step {rule_step} (cl (= {application} {blasted_text})) :rule bitblast_equal)"
        ))?;
        self.push_step(&format!(
            "(step {chained} (cl (= {equality} {blasted_text})) :rule trans :premises ({congruence} {rule_step}))"
        ))?;
        self.push_step(&format!(
            "(step {split} (cl (not {equality}) {blasted_text}) :rule equiv1 :premises ({chained}))"
        ))?;
        let guard_text = self.circuit.text(guard);
        self.push_step(&format!(
            "(step {clause_step} (cl {guard_text} {blasted_text}) :rule resolution :premises ({guard_step} {split}))"
        ))?;
        self.plan(vec![guard, blasted], ClauseEmit::Existing(clause_step))?;
        Some(blasted)
    }
}
