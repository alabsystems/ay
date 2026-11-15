// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An `or_pos` clausification tautology stated with its literals reordered.
//!
//! AY records a Boolean tautology as a clause SET, so the lemma
//! `(cl (not (bvult k 65)) (= t u) (not (or (= t u) (not (bvult k 65)))))`
//! is the `or_pos` axiom over `(or (= t u) (not (bvult k 65)))` with its
//! literals in another order. Pinned carcara 1.1.0's `or_pos` compares the
//! literals POSITIONALLY (`checker/rules/tautology.rs`), so the reordered
//! clause is not an instance of it and the lemma used to print as a `hole`.
//! `reordering` is carcara's multiset check between one premise clause and
//! the conclusion (`checker/rules/extras.rs`), so the exact axiom followed by
//! one `reordering` derives the printed clause. Both commands are judged over
//! the printed text: the gate literal must be `(not (or d_1 .. d_n))` and the
//! remaining literals must be exactly `d_1 .. d_n` as a byte multiset.

use super::*;

const MAX_PERMUTED_OR_POS_BYTES: usize = 64 * 1024;
const MAX_PERMUTED_OR_POS_LITERALS: usize = 256;

/// The `or_pos` gate literal of `literals` and its disjuncts, when the other
/// literals are exactly those disjuncts as a multiset.
fn permuted_or_pos_gate(literals: &[String]) -> Option<(&str, Vec<String>)> {
    for (index, literal) in literals.iter().enumerate() {
        let Some(negated) = split_application(literal, "not") else {
            continue;
        };
        let [disjunction] = negated.as_slice() else {
            continue;
        };
        let Some(disjuncts) = split_application(disjunction, "or") else {
            continue;
        };
        if disjuncts.len() + 1 != literals.len() {
            continue;
        }
        let mut rest: Vec<&str> = literals
            .iter()
            .enumerate()
            .filter(|(position, _)| *position != index)
            .map(|(_, literal)| literal.as_str())
            .collect();
        let mut expected: Vec<&str> = disjuncts.iter().map(String::as_str).collect();
        rest.sort_unstable();
        expected.sort_unstable();
        if rest == expected {
            return Some((literal.as_str(), disjuncts));
        }
    }
    None
}

impl AlethePrinter<'_> {
    /// `or_pos` (+ `reordering`) for a printed clause that is a permutation
    /// of an `or_pos` instance, or `None`.
    pub(super) fn lower_permuted_or_pos(&self, id: ProofId, clause: &str) -> Option<String> {
        if clause.len() > MAX_PERMUTED_OR_POS_BYTES || self.work_budget_exhausted() {
            return None;
        }
        self.charge(clause.len() as u64);
        let literals = split_application(clause, "cl")?;
        if literals.len() < 2 || literals.len() > MAX_PERMUTED_OR_POS_LITERALS {
            return None;
        }
        let (gate, disjuncts) = permuted_or_pos_gate(&literals)?;
        let axiom = format!("(cl {gate} {})", disjuncts.join(" "));
        let output = if axiom == clause {
            format!("(step {id} {clause} :rule or_pos)")
        } else {
            format!(
                "(step {id}.op {axiom} :rule or_pos)\n\
                 (step {id} {clause} :rule reordering :premises ({id}.op))"
            )
        };
        self.charge(output.len() as u64);
        (!self.work_budget_exhausted()).then_some(output)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn lower(clause: &str) -> Option<String> {
        let terms = TermStore::new();
        AlethePrinter::new(&terms).lower_permuted_or_pos(ProofId(13), clause)
    }

    #[test]
    fn reordered_or_pos_is_the_axiom_plus_reordering() {
        let clause = "(cl (not p) (= a b) (not (or (= a b) (not p))))";
        assert_eq!(
            lower(clause).as_deref(),
            Some(
                "(step t13.op (cl (not (or (= a b) (not p))) (= a b) (not p)) :rule or_pos)\n\
                 (step t13 (cl (not p) (= a b) (not (or (= a b) (not p)))) :rule reordering :premises (t13.op))"
            )
        );
    }

    #[test]
    fn positional_or_pos_needs_no_reordering() {
        let clause = "(cl (not (or a b)) a b)";
        assert_eq!(
            lower(clause).as_deref(),
            Some("(step t13 (cl (not (or a b)) a b) :rule or_pos)")
        );
    }

    #[test]
    fn a_missing_or_foreign_disjunct_is_not_or_pos() {
        // The clause drops `b` and carries `c`: not a tautology instance.
        assert_eq!(lower("(cl (not (or a b)) a c)"), None);
        // One disjunct short.
        assert_eq!(lower("(cl (not (or a b)) a)"), None);
        // A duplicated literal does not stand in for a missing one.
        assert_eq!(lower("(cl (not (or a b)) a a)"), None);
        // No gate literal at all.
        assert_eq!(lower("(cl a b)"), None);
    }
}
