// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! A multi-literal bit-vector lemma, refuted as the conjunction of its
//! complements and opened with the checker's own Boolean rules.
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
//! For a positive literal `B`, its complement is `(not B)`. Opening the
//! conjunction therefore produces `(not (not B))`, which is re-derived as
//! `B` using `not_not` and binary resolution, exactly as in `normalize.rs`.
//! The final step retains the lemma's original name and literal order. A
//! repeated base term or parsed spelling declines; the mixed lane also
//! requires distinct circuit gates so each normalization has one pivot.
//! Surface disagreement, limits and a satisfiable complement conjunction
//! retain the honest `hole`. The existing all-negative opening and the
//! executor's wire-gap policy are unchanged.

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
        let mut positive = Vec::with_capacity(clause.len());
        let mut seen = DetHashSet::default();
        for &literal in clause {
            let (atom, is_positive) = match self.terms.get(literal) {
                TermData::Not(atom) => (*atom, false),
                _ => (literal, true),
            };
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
            let expected = if is_positive {
                atom_text.clone()
            } else {
                format!("(not {atom_text})")
            };
            if literal_text != expected
                || atom_texts
                    .iter()
                    .any(|seen_text: &String| same_printed_term(seen_text, &atom_text))
            {
                return None;
            }
            atoms.push(atom);
            atom_texts.push(atom_text);
            literal_texts.push(literal_text.to_string());
            positive.push(is_positive);
        }
        let prefix = self.fresh_complete_blast_prefix(id)?;
        for &literal in clause {
            self.complete_blast_surface_agrees(literal)?;
        }
        let orient = |blaster: &mut Blaster<'_, '_>, conjuncts: &[SRef]| {
            let distinct_gates: DetHashSet<SRef> = conjuncts.iter().copied().collect();
            if distinct_gates.len() != conjuncts.len() {
                return None;
            }
            if !positive.iter().any(|value| *value) {
                return Some(blaster.circuit.and(conjuncts.to_vec()));
            }
            let bases: DetHashSet<u32> = conjuncts.iter().map(|value| value.gate).collect();
            if bases.len() != conjuncts.len() {
                return None;
            }
            let complements = conjuncts
                .iter()
                .zip(&positive)
                .map(|(&value, &is_positive)| {
                    if is_positive {
                        value.not()
                    } else {
                        Some(value)
                    }
                })
                .collect::<Option<Vec<_>>>()?;
            Some(blaster.circuit.and(complements))
        };
        let conjuncts: Vec<String> = atom_texts
            .iter()
            .zip(&positive)
            .map(|(atom, is_positive)| {
                if *is_positive {
                    format!("(not {atom})")
                } else {
                    atom.clone()
                }
            })
            .collect();
        let conjunction = format!("(and {})", conjuncts.join(" "));
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
        if positive.iter().any(|value| *value) {
            return self.open_mixed_blast_clause(
                id,
                document,
                &conjunction,
                &literal_texts,
                &positive,
            );
        }
        let literals = literal_texts.join(" ");
        let opened = format!(
            "{document}\n(step {id}.cban (cl {conjunction} {literals}) :rule and_neg)\n\
             (step {id} (cl {literals}) :rule resolution :premises ({id}.cban {unit}))"
        );
        self.charge(opened.len().saturating_sub(document.len()) as u64);
        (!self.work_budget_exhausted()).then_some(opened)
    }

    fn append_blast_clause_parts(&self, output: &mut String, parts: &[&str]) -> Option<()> {
        let bytes = parts
            .iter()
            .try_fold(0_usize, |sum, part| sum.checked_add(part.len()))?;
        if output.len().checked_add(bytes)? > MAX_COUNTED_TEXT_BYTES {
            return None;
        }
        self.charge(bytes as u64);
        self.check_emission_progress(0).ok()?;
        output.try_reserve(bytes).ok()?;
        for part in parts {
            output.push_str(part);
        }
        Some(())
    }

    fn open_mixed_blast_clause(
        &self,
        id: ProofId,
        mut document: String,
        conjunction: &str,
        literals: &[String],
        positive: &[bool],
    ) -> Option<String> {
        let positions: Vec<usize> = positive
            .iter()
            .enumerate()
            .filter_map(|(at, value)| value.then_some(at))
            .collect();
        let mut current: Vec<String> = literals
            .iter()
            .zip(positive)
            .map(|(literal, value)| {
                if *value {
                    format!("(not (not {literal}))")
                } else {
                    literal.clone()
                }
            })
            .collect();
        let text = joined_literals(&current)?;
        let mut premise = format!("{id}.cbopen");
        self.append_blast_clause_parts(
            &mut document,
            &[
                &format!("\n(step {id}.cban (cl "),
                conjunction,
                " ",
                &text,
                ") :rule and_neg)",
                &format!("\n(step {premise} (cl "),
                &text,
                &format!(") :rule resolution :premises ({id}.cban {id}.cbu))"),
            ],
        )?;
        for (step, &position) in positions.iter().enumerate() {
            let literal = &literals[position];
            let tautology = format!("{id}.cbnn{position}");
            let next = if step + 1 == positions.len() {
                id.to_string()
            } else {
                format!("{id}.cbnorm{position}")
            };
            current[position] = literal.clone();
            let text = joined_literals(&current)?;
            self.append_blast_clause_parts(
                &mut document,
                &[
                    &format!("\n(step {tautology} (cl (not (not (not "),
                    literal,
                    "))) ",
                    literal,
                    ") :rule not_not)",
                    &format!("\n(step {next} (cl "),
                    &text,
                    &format!(") :rule resolution :premises ({premise} {tautology}))"),
                ],
            )?;
            premise = next;
        }
        consumer_accepts(&document).then_some(document)
    }
}

fn joined_literals(literals: &[String]) -> Option<String> {
    let bytes = literals
        .iter()
        .try_fold(literals.len().saturating_sub(1), |sum, literal| {
            sum.checked_add(literal.len())
        })?;
    if bytes > MAX_COUNTED_TEXT_BYTES {
        return None;
    }
    let mut text = String::new();
    text.try_reserve(bytes).ok()?;
    for (index, literal) in literals.iter().enumerate() {
        if index != 0 {
            text.push(' ');
        }
        text.push_str(literal);
    }
    Some(text)
}

#[cfg(test)]
mod tests;
