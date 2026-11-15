// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Discharge the original guard before publishing a one-word masked identity.

use super::*;
use crate::checker::bv_affine::{guarded_mask_identity, GuardKind, GuardedMask};

impl AlethePrinter<'_> {
    pub(super) fn format_bv_guarded_mask_identity(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let identity = guarded_mask_identity(self.terms, clause, &mut |work, _| {
            self.charge(work as u64);
            !self.work_budget_exhausted()
        })
        .ok()??;
        let budget = self.work_budget.map_or(MAX_TEXT as u64, |limit| {
            limit.saturating_sub(self.work_used()).min(MAX_TEXT as u64)
        });
        let raw = AlethePrinter::new_with_overrides_and_budget(self.terms, None, Some(budget))
            .with_parent_emission_progress(self);
        let root = raw.format_term(identity.root);
        let guard = raw.format_term(identity.guard);
        let equality = raw.format_term(identity.equality);
        let goal = format!("(not {root})");
        self.charge(raw.work_used());
        if raw.work_budget_exhausted()
            || self.work_budget_exhausted()
            || self.format_term(clause[0]) != goal
        {
            return None;
        }
        let mut proof = PackedProof::new(self, id)?;
        let end = proof.fresh();
        let assumption = proof.fresh();
        proof.append(&format!(
            "(anchor :step {end})\n(assume {assumption} {root})\n"
        ))?;
        let guard_unit =
            proof.project_conjunct(&root, &assumption, &guard, identity.guard_position)?;
        let negated = format!("(not {equality})");
        let negated_unit =
            proof.project_conjunct(&root, &assumption, &negated, 1 - identity.guard_position)?;
        let derived = proof.guarded_equality(&identity, &guard_unit)?;
        if format!("(= {} {})", derived.left, derived.right) != equality {
            return None;
        }
        proof.step("", "resolution", &[&derived.step, &negated_unit])?;
        proof.named_step(
            &end,
            &format!("{goal} false"),
            "subproof",
            &[],
            &format!(" :discharge ({assumption})"),
        )?;
        let not_false = proof.step("(not false)", "false", &[])?;
        proof.named_step(
            &id.to_string(),
            &goal,
            "resolution",
            &[&end, &not_false],
            "",
        )?;
        proof.definitions.push_str(&proof.out);
        Some(proof.definitions)
    }
}

impl PackedProof<'_, '_> {
    pub(super) fn project_conjunct(
        &mut self,
        root: &str,
        unit: &str,
        child: &str,
        index: usize,
    ) -> Option<String> {
        let projection = self.fresh();
        self.named_step(
            &projection,
            &format!("(not {root}) {child}"),
            "and_pos",
            &[],
            &format!(" :args ({index})"),
        )?;
        self.step(child, "resolution", &[unit, &projection])
    }

    pub(super) fn transport_unit(&mut self, equality: &Equality, unit: &str) -> Option<String> {
        let implication = self.step(
            &format!("(not {}) {}", equality.left, equality.right),
            "equiv1",
            &[&equality.step],
        )?;
        self.step(&equality.right, "resolution", &[unit, &implication])
    }

    pub(super) fn zero_bit(&mut self, bit: &str, negated_unit: &str) -> Option<Equality> {
        let equation = format!("(= {bit} false)");
        let literal = format!("(not {bit})");
        let simple = self.equality(&equation, &literal, "equiv_simplify", &[])?;
        let implication = self.step(
            &format!("{equation} (not {literal})"),
            "equiv2",
            &[&simple.step],
        )?;
        let step = self.step(&equation, "resolution", &[&implication, negated_unit])?;
        Some(Equality {
            left: bit.into(),
            right: "false".into(),
            step,
        })
    }

    fn guarded_equality(&mut self, identity: &GuardedMask, guard_unit: &str) -> Option<Equality> {
        let source = self.vector(identity.source, 0)?;
        // Distinct projections keep the guard's conjunction and its extracted
        // facts one-to-one. Other vector normal forms decline this wire lane.
        let mut seen = std::collections::BTreeSet::new();
        if source.bits.len() != identity.width as usize
            || source
                .bits
                .iter()
                .any(|bit| !bit.starts_with("((_ @bit_of ") || !seen.insert(bit.clone()))
        {
            return None;
        }
        let facts = match identity.kind {
            GuardKind::Range { bound } => {
                self.range_zero_facts(identity.guard, bound, &source, guard_unit)?
            }
            GuardKind::Mask => self.mask_zero_facts(identity, &source, guard_unit)?,
        };
        let left = self.vector(identity.left, 0)?;
        let right = self.vector(identity.right, 0)?;
        let mut bits = Vec::new();
        for (a, b) in left.bits.iter().zip(&right.bits) {
            let equality = if a == b {
                self.equality(a, b, "refl", &[])?
            } else if b == "false" {
                facts.iter().find(|fact| fact.left == *a)?.clone()
            } else if a == "false" {
                let fact = facts.iter().find(|fact| fact.left == *b)?;
                self.equality(a, b, "symm", &[&fact.step])?
            } else {
                return None;
            };
            bits.push(equality);
        }
        if left.bits.len() != right.bits.len() {
            return None;
        }
        let middle = self.congruence("@bbterm", &bits)?;
        let reverse = self.equality(
            &right.equality.right,
            &right.equality.left,
            "symm",
            &[&right.equality.step],
        )?;
        let result = self.chain(left.equality, middle)?;
        let mut result = self.chain(result, reverse)?;
        for frame in identity.frames.iter().rev() {
            let shared = self.printer.format_term(frame.shared);
            let shared = self.equality(&shared, &shared, "refl", &[])?;
            let args = if frame.changing == 0 {
                [result, shared]
            } else {
                [shared, result]
            };
            result = self.congruence("bvadd", &args)?;
        }
        Some(result)
    }

    fn mask_zero_facts(
        &mut self,
        identity: &GuardedMask,
        source: &Value,
        unit: &str,
    ) -> Option<Vec<Equality>> {
        let bits: Vec<_> = source
            .bits
            .iter()
            .enumerate()
            .filter(|(i, _)| identity.zeros & (1u128 << i) != 0)
            .map(|(_, bit)| bit.clone())
            .collect();
        let negations: Vec<_> = bits.iter().map(|bit| format!("(not {bit})")).collect();
        let expected = match negations.as_slice() {
            [] => "true".into(),
            [one] => one.clone(),
            _ => application("and", negations.iter().map(String::as_str)),
        };
        let guard = self.boolean(identity.guard, 0)?;
        if guard.right != expected {
            return None;
        }
        let unit = self.transport_unit(&guard, unit)?;
        let mut facts = Vec::new();
        for (i, bit) in bits.iter().enumerate() {
            let negated = if bits.len() == 1 {
                unit.clone()
            } else {
                self.project_conjunct(&guard.right, &unit, &negations[i], i)?
            };
            facts.push(self.zero_bit(bit, &negated)?);
        }
        Some(facts)
    }
}
