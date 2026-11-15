// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked integer clauses and their exact propositional assertion units.

use super::{
    AletheRule, LemmaKey, ProofId, ProofTracker, Symbol, TermData, TermId, TermStore,
    TheoryLemmaKind,
};

impl ProofTracker {
    /// Validate the flat integer theorem, then derive its packed OR unit.
    /// No authored premise or arithmetic annotation is invented here.
    pub(crate) fn add_packed_guarded_integer_lemma(
        &mut self,
        terms: &mut TermStore,
        packed: TermId,
        clause: Vec<TermId>,
    ) -> Option<ProofId> {
        if !self.enabled || clause.len() < 2 {
            return None;
        }
        let TermData::App(Symbol::Named(name), args) = terms.get(packed) else {
            return None;
        };
        if name != "or"
            || args != &clause
            || !ay_core::proof_validation::recognize_int_guarded_split_gap(terms, &clause)
        {
            return None;
        }
        if let Some(existing) = self
            .lemma_map
            .get(TheoryLemmaKind::Generic, &[packed], None)
        {
            return Some(existing);
        }
        let kind = TheoryLemmaKind::IntGuardedSplitGap;
        let mut current = self.add_theory_lemma_with_kind(clause.clone(), kind)?;
        let mut remaining = clause;
        for literal in remaining.clone() {
            let complement = match terms.get(literal) {
                TermData::Not(inner) => *inner,
                _ => terms.mk_not_raw(literal),
            };
            let bridge = self.proof.add_rule_step(
                AletheRule::OrNeg,
                vec![packed, complement],
                Vec::new(),
                vec![packed],
            );
            let position = remaining.iter().position(|&term| term == literal)?;
            let _ = remaining.remove(position);
            remaining.push(packed);
            current = self
                .proof
                .add_resolution(remaining.clone(), literal, current, bridge);
        }
        let unit = self.proof.add_rule_step(
            AletheRule::Contraction,
            vec![packed],
            vec![current],
            Vec::new(),
        );
        self.lemma_map.or_insert(
            LemmaKey::new(TheoryLemmaKind::Generic, &[packed], None),
            unit,
        );
        Some(unit)
    }
}
