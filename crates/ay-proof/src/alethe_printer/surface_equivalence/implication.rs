// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! An authored implication against its canonical flat disjunction.
//!
//! Elaboration turns `(=> A B)` into `(or B' (not A'))`, and
//! `(=> (and A1 .. Ak) B)` into `(or B' (not A1') .. (not Ak'))`, with the
//! disjuncts in AY's order and each literal possibly re-spelled
//! (`(bvuge i old)` as `(bvule old i)`, `(= x y)` as `(= y x)`). No single
//! pinned-carcara rule relates the two; the equality is the propositional
//! two-way implication, which this derives with clausification axioms and
//! `resolution`:
//!
//! ```text
//! (cl (not I) O):  implies_pos, and_neg, or_neg per disjunct,
//!                  equiv_pos2 per re-spelled literal
//! (cl I (not O)):  or_pos, implies_neg1, implies_neg2, and_pos per
//!                  antecedent, equiv_pos1 per re-spelled literal
//! (cl (= I O)):    equiv_neg1, equiv_neg2 and three resolutions
//! ```
//!
//! Each literal is paired with a DISTINCT disjunct, exact text first, and a
//! re-spelled pair must itself carry a derived equality; every disjunct must
//! be claimed. Any other shape declines.

use super::super::*;
use super::{CanonicalNode, Derivation};

/// One authored literal of the implication and the disjunct it became.
struct PairedLiteral {
    literal: String,
    disjunct: usize,
    /// The step concluding `(= literal disjunct)`, when the texts differ.
    equality: Option<String>,
}

impl AlethePrinter<'_> {
    pub(super) fn implication_disjunction_equivalence(
        &self,
        id: &str,
        surface: &str,
        canonical: CanonicalNode<'_>,
        depth: usize,
        derivation: &mut Derivation,
    ) -> bool {
        let Some(parts) = split_application(surface, "=>") else {
            return false;
        };
        let [antecedent, consequent] = parts.as_slice() else {
            return false;
        };
        let Some(disjuncts) = self.canonical_printed_children(canonical, "or") else {
            return false;
        };
        let conjuncts = split_application(antecedent, "and").filter(|parts| !parts.is_empty());
        let antecedents = conjuncts
            .clone()
            .unwrap_or_else(|| vec![antecedent.clone()]);
        let mut literals: Vec<String> = antecedents.iter().map(|a| format!("(not {a})")).collect();
        literals.push(consequent.clone());
        if literals.len() != disjuncts.len() {
            return false;
        }
        let Some(paired) =
            self.pair_implication_literals(id, &literals, &disjuncts, depth, derivation)
        else {
            return false;
        };
        let texts: Vec<&str> = disjuncts.iter().map(|(_, text)| text.as_str()).collect();
        let shape = ImplicationShape {
            implication: surface,
            disjunction: canonical.text,
            antecedent,
            consequent,
            conjuncts: conjuncts.as_deref(),
            disjuncts: &texts,
            paired: &paired,
        };
        emit_implication_equivalence(id, shape, derivation);
        true
    }

    fn pair_implication_literals(
        &self,
        id: &str,
        literals: &[String],
        disjuncts: &[(TermId, String)],
        depth: usize,
        derivation: &mut Derivation,
    ) -> Option<Vec<PairedLiteral>> {
        let mut owner: Vec<bool> = vec![false; disjuncts.len()];
        let mut paired: Vec<Option<PairedLiteral>> = literals.iter().map(|_| None).collect();
        for (index, literal) in literals.iter().enumerate() {
            if let Some(disjunct) =
                (0..disjuncts.len()).find(|&j| !owner[j] && disjuncts[j].1 == *literal)
            {
                owner[disjunct] = true;
                paired[index] = Some(PairedLiteral {
                    literal: literal.clone(),
                    disjunct,
                    equality: None,
                });
            }
        }
        for (index, literal) in literals.iter().enumerate() {
            if paired[index].is_some() {
                continue;
            }
            let leg = format!("{id}.q{index}");
            let found = (0..disjuncts.len()).find(|&j| {
                if owner[j] {
                    return false;
                }
                let checkpoint = derivation.steps.len();
                let node = CanonicalNode {
                    term: disjuncts[j].0,
                    text: &disjuncts[j].1,
                };
                if self.derive_printed_equivalence(&leg, literal, node, depth + 1, derivation) {
                    true
                } else {
                    derivation.steps.truncate(checkpoint);
                    false
                }
            })?;
            owner[found] = true;
            paired[index] = Some(PairedLiteral {
                literal: literal.clone(),
                disjunct: found,
                equality: Some(leg),
            });
        }
        paired.into_iter().collect()
    }
}

/// The printed pieces one implication-to-disjunction equivalence relates.
#[derive(Clone, Copy)]
struct ImplicationShape<'a> {
    implication: &'a str,
    disjunction: &'a str,
    antecedent: &'a str,
    consequent: &'a str,
    conjuncts: Option<&'a [String]>,
    disjuncts: &'a [&'a str],
    paired: &'a [PairedLiteral],
}

fn emit_implication_equivalence(
    id: &str,
    ImplicationShape {
        implication,
        disjunction,
        antecedent,
        consequent,
        conjuncts,
        disjuncts,
        paired,
    }: ImplicationShape<'_>,
    derivation: &mut Derivation,
) {
    let steps = &mut derivation.steps;
    // (cl (not I) O)
    steps.push(format!(
        "(step {id}.ip (cl (not {implication}) (not {antecedent}) {consequent}) :rule implies_pos)"
    ));
    let mut forward = vec![format!("{id}.ip")];
    if let Some(conjuncts) = conjuncts {
        let negated: Vec<String> = conjuncts.iter().map(|c| format!("(not {c})")).collect();
        steps.push(format!(
            "(step {id}.an (cl {antecedent} {}) :rule and_neg)",
            negated.join(" ")
        ));
        forward.push(format!("{id}.an"));
    }
    for (index, pair) in paired.iter().enumerate() {
        let disjunct = disjuncts[pair.disjunct];
        steps.push(format!(
            "(step {id}.on{index} (cl {disjunction} (not {disjunct})) :rule or_neg :args ({}))",
            pair.disjunct
        ));
        forward.push(format!("{id}.on{index}"));
        if let Some(equality) = &pair.equality {
            let literal = &pair.literal;
            steps.push(format!(
                "(step {id}.qp{index} (cl (not (= {literal} {disjunct})) (not {literal}) {disjunct}) :rule equiv_pos2)"
            ));
            forward.push(format!("{id}.qp{index}"));
            forward.push(equality.clone());
        }
    }
    steps.push(format!(
        "(step {id}.d1 (cl (not {implication}) {disjunction}) :rule resolution :premises ({}))",
        forward.join(" ")
    ));
    // (cl I (not O))
    steps.push(format!(
        "(step {id}.op (cl (not {disjunction}) {}) :rule or_pos)",
        disjuncts.join(" ")
    ));
    steps.push(format!(
        "(step {id}.in1 (cl {implication} {antecedent}) :rule implies_neg1)"
    ));
    steps.push(format!(
        "(step {id}.in2 (cl {implication} (not {consequent})) :rule implies_neg2)"
    ));
    let mut backward = vec![format!("{id}.op"), format!("{id}.in1"), format!("{id}.in2")];
    if let Some(conjuncts) = conjuncts {
        for (index, conjunct) in conjuncts.iter().enumerate() {
            steps.push(format!(
                "(step {id}.ap{index} (cl (not {antecedent}) {conjunct}) :rule and_pos :args ({index}))"
            ));
            backward.push(format!("{id}.ap{index}"));
        }
    }
    for (index, pair) in paired.iter().enumerate() {
        if let Some(equality) = &pair.equality {
            let literal = &pair.literal;
            let disjunct = disjuncts[pair.disjunct];
            steps.push(format!(
                "(step {id}.qn{index} (cl (not (= {literal} {disjunct})) {literal} (not {disjunct})) :rule equiv_pos1)"
            ));
            backward.push(format!("{id}.qn{index}"));
            backward.push(equality.clone());
        }
    }
    steps.push(format!(
        "(step {id}.d2 (cl {implication} (not {disjunction})) :rule resolution :premises ({}))",
        backward.join(" ")
    ));
    // (cl (= I O))
    let equality = format!("(= {implication} {disjunction})");
    steps.push(format!(
        "(step {id}.n1 (cl {equality} (not {implication}) (not {disjunction})) :rule equiv_neg1)"
    ));
    steps.push(format!(
        "(step {id}.n2 (cl {equality} {implication} {disjunction}) :rule equiv_neg2)"
    ));
    steps.push(format!(
        "(step {id}.r1 (cl {equality} (not {disjunction})) :rule resolution :premises ({id}.n1 {id}.d2))"
    ));
    steps.push(format!(
        "(step {id}.r2 (cl {equality} {disjunction}) :rule resolution :premises ({id}.n2 {id}.d1))"
    ));
    steps.push(format!(
        "(step {id} (cl {equality}) :rule resolution :premises ({id}.r1 {id}.r2))"
    ));
}
