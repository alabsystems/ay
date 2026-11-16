// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Explicitly connect authored literal spellings to the canonical derivation.

use super::*;

pub(super) struct Clause {
    pub canonical: Vec<Node>,
    pub texts: Vec<String>,
    changed: Vec<Option<Node>>,
}

impl Clause {
    pub(super) fn render(
        printer: &AlethePrinter<'_>,
        clause: &[TermId],
        meter: &mut Meter<'_, '_>,
    ) -> Option<Self> {
        let raw = AlethePrinter::new_with_overrides_and_budget(
            printer.terms,
            None,
            Some(MAX_INPUT as u64),
        );
        let mut result = Self {
            canonical: Vec::new(),
            texts: Vec::new(),
            changed: Vec::new(),
        };
        let mut bytes = 0usize;
        for &literal in clause {
            let before = raw.work_used();
            let canonical = raw.format_term(literal);
            meter.spend(raw.work_used().saturating_sub(before))?;
            let printed = printer.format_term(literal);
            bytes = bytes
                .checked_add(canonical.len())?
                .checked_add(printed.len())?;
            if bytes > MAX_INPUT || raw.work_budget_exhausted() || printer.work_budget_exhausted() {
                return None;
            }
            meter.spend(canonical.len().min(printed.len()) as u64 + 1)?;
            let changed = if canonical == printed {
                None
            } else {
                Some(Node::parse(&printed, 0, meter)?)
            };
            result.canonical.push(Node::parse(&canonical, 0, meter)?);
            result.texts.push(printed);
            result.changed.push(changed);
        }
        Some(result)
    }

    pub(super) fn node(&self, index: usize) -> &Node {
        self.changed[index]
            .as_ref()
            .unwrap_or(&self.canonical[index])
    }
}

impl Derivation<'_, '_> {
    /// A spelling change is a checked equality followed by Boolean resolution.
    /// No override is installed inside the native substitution derivation.
    pub(super) fn fact_as(&mut self, source: &str, target: &str, premise: &str) -> Option<String> {
        self.meter.spend(premise.len() as u64)?;
        if self.same(source, target)? {
            return Some(premise.to_owned());
        }
        self.meter
            .spend(source.len().checked_add(target.len())? as u64)?;
        // Precharge the comparator's full node allowance, including alternate
        // equality orientations, against this derivation's aggregate budget.
        self.meter
            .spend(quantifier_surface::MAX_SURFACE_NODES as u64)?;
        if !quantifier_surface::printed_terms_alpha_equivalent(source, target) {
            return None;
        }
        let equality = self.eq(source, target, "refl", &[])?;
        let implication = self.step(
            &format!("(not (= {source} {target})) (not {source}) {target}"),
            "equiv_pos2",
            &[],
        )?;
        let conditional = self.step(
            &format!("(not {source}) {target}"),
            "resolution",
            &[equality, implication],
        )?;
        self.step(target, "resolution", &[conditional, premise.to_owned()])
    }
}
