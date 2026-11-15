// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A MULTI-literal bit-vector lemma `(cl (not A_1) .. (not A_n))`.
//!
//! Reached ONLY where the wire rule is already the honest `hole`, after the
//! named lowerings of the clause (the checked bit-blast dispatch, the ground
//! disequality and closed-Boolean repairs) have declined, so it can displace
//! nothing the checker already accepts. The permuted `or_pos` repair after it
//! can overlap only on an `or_pos` instance whose disjuncts are all negative
//! literals: a bit-blast lemma of that shape is printed here instead, and
//! either document is a stock, checker-re-derived proof of the same clause.
//!
//! Like those other hole-fallback repairs it is a PRINTER lowering only: the
//! shared capability predicate `checked_bv_bitblast_lowering_supported` does
//! not include it, so the executor's wire-gap screen keeps reporting such a
//! lemma as a gap. That is the conservative direction on purpose. The screen
//! decides whether the executor's authored-repair lanes run, and a screen that
//! called these lemmas clean would stop them: MEASURED on `QF_BV/puzzle_03`,
//! whose native proof is one six-literal bit-blast lemma, admitting it there
//! replaced the repaired `eq_transitive` + `evaluate` document the ground
//! disequality test pins with this blast. Under strict proofs the screen
//! therefore still withholds such a verdict, exactly as it did for the hole.
//!
//! The complete blaster refutes ONE assumed root and lands on `(cl (not A))`.
//! A conflict clause over several atoms is the same refutation of their
//! conjunction: the root is the circuit's own `and` gate over the atoms, whose
//! `and_pos` projections are ordinary planned Tseitin clauses, and the chain
//! lands on `(cl (not (and A_1 .. A_n)))`. Two stock steps then open the
//! conjunction back into the lemma's literals:
//!
//! ```text
//! (step tK.cbu (cl (not (and A_1 .. A_n))) :rule resolution ...) ; the chain
//! (step tK.cban (cl (and A_1 .. A_n) (not A_1) .. (not A_n)) :rule and_neg)
//! (step tK (cl (not A_1) .. (not A_n)) :rule resolution :premises (tK.cban tK.cbu))
//! ```
//!
//! Only NEGATIVE literals are admitted: a positive literal's complement is a
//! printed `(not B)`, whose `and_neg` literal `(not (not B))` is a different
//! term to carcara's rule layer than the `B` the lemma prints. Such a clause,
//! a repeated atom (by term, by parsed spelling, or by circuit gate), or a
//! literal that does not print as `(not <atom>)` declines and keeps the
//! honest `hole`, like every other refusal here: the `and_neg` opening and its
//! resolution sit outside the transported chain's self-replay, so they are
//! printed only where each conjunct is one distinct term to the checker. The
//! SAT gate in `finish` still refuses a satisfiable conjunction, so a clause
//! that is not a theorem is never printed.

use super::super::surface_literal::same_printed_term;
use super::*;
use ay_core::TheoryLemmaKind;

/// Most literals one clause lowering conjoins.
const MAX_CLAUSE_LITERALS: usize = 64;

impl AlethePrinter<'_> {
    pub(in crate::alethe_printer) fn format_bv_complete_blast_clause(
        &self,
        id: ProofId,
        clause: &[TermId],
        kind: &TheoryLemmaKind,
    ) -> Option<String> {
        if !matches!(
            kind,
            TheoryLemmaKind::BvBitBlast | TheoryLemmaKind::BvBitBlastGate { .. }
        ) || clause.len() < 2
            || clause.len() > MAX_CLAUSE_LITERALS
        {
            return None;
        }
        // As at the unit lane's entry: never blasted where no document is
        // observable, nor past the stop of a render asked from inside a solve
        // (`ask.rs`).
        if self.complete_blast_unasked().is_some() {
            return None;
        }
        let mut atoms = Vec::with_capacity(clause.len());
        let mut atom_texts = Vec::with_capacity(clause.len());
        let mut literal_texts = Vec::with_capacity(clause.len());
        let mut seen = DetHashSet::default();
        for &literal in clause {
            let TermData::Not(atom) = self.terms.get(literal) else {
                return None;
            };
            let atom = *atom;
            if !seen.insert(atom)
                || self.terms.sort(atom) != &Sort::Bool
                || matches!(self.terms.get(atom), TermData::Not(_))
            {
                return None;
            }
            // The literal exactly as the lemma prints it, and the atom inside.
            let printed = self.format_clause(std::slice::from_ref(&literal));
            let literal_text = printed.strip_prefix("(cl ")?.strip_suffix(')')?;
            let atom_text = self.format_term(atom);
            if literal_text != format!("(not {atom_text})")
                || atom_texts
                    .iter()
                    .any(|seen_text: &String| same_printed_term(seen_text, &atom_text))
            {
                return None;
            }
            atoms.push(atom);
            atom_texts.push(atom_text);
            literal_texts.push(literal_text.to_string());
        }
        let prefix = self.fresh_complete_blast_prefix(id)?;
        for &literal in clause {
            self.complete_blast_surface_agrees(literal)?;
        }
        let orient = |blaster: &mut Blaster<'_, '_>, conjuncts: &[SRef]| {
            let distinct_gates: DetHashSet<SRef> = conjuncts.iter().copied().collect();
            (distinct_gates.len() == conjuncts.len())
                .then(|| blaster.circuit.and(conjuncts.to_vec()))
        };
        let conjunction = format!("(and {})", atom_texts.join(" "));
        let unit = format!("{id}.cbu");
        let final_clause = format!("(cl (not {conjunction}))");
        let document = Blaster::lemma_document(
            self,
            id,
            &prefix,
            &atoms,
            &orient,
            &final_clause,
            Some(&unit),
            None,
        )?;
        let literals = literal_texts.join(" ");
        let opened = format!(
            "{document}\n(step {id}.cban (cl {conjunction} {literals}) :rule and_neg)\n\
             (step {id} (cl {literals}) :rule resolution :premises ({id}.cban {unit}))"
        );
        self.charge(opened.len().saturating_sub(document.len()) as u64);
        (!self.work_budget_exhausted()).then_some(opened)
    }
}

#[cfg(test)]
mod tests;
