// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Ground substitution exported as congruence and discharged Boolean proofs.

use super::*;

mod syntax;
use syntax::{Meter, Node};
mod derivation;
use derivation::Derivation;

const MAX_WORK: u64 = 8 * 1024 * 1024;
const MAX_INPUT: usize = 64 * 1024;
const MAX_NODES: usize = 512;
const MAX_DEPTH: usize = 32;
const MAX_PINS: usize = 16;
const MAX_OUTPUT: usize = 2 * 1024 * 1024;

mod bounds;
mod surface;

impl AlethePrinter<'_> {
    pub(super) fn format_ground_substitution(
        &self,
        id: ProofId,
        clause: &[TermId],
    ) -> Option<String> {
        let mut meter = Meter::new(self);
        meter.spend(MAX_NODES as u64)?;
        let render_bound = bounds::bounded_clause(self, clause)?;
        meter.spend(render_bound)?;
        // The native validator has an explicit 200,000-node total allowance.
        // Charge that allowance before invoking its independent acceptance leg.
        meter.spend(200_000)?;
        if !crate::recognize_ground_equality_substitution(self.terms, clause) {
            return None;
        }
        let surface = surface::Clause::render(self, clause, &mut meter)?;
        let nodes = &surface.canonical;
        let mut d = Derivation::new(id, meter);
        d.append(&format!("(anchor :step {id})\n"))?;
        // Alethe subproofs require every assumption before their first step.
        let discharge = (0..nodes.len() - 1)
            .map(|index| d.assume(&surface.node(index).unary("not")?.text))
            .collect::<Option<Vec<_>>>()?;
        let mut pins = Vec::new();
        for (index, negative) in nodes[..nodes.len() - 2].iter().enumerate() {
            let equality = negative.unary("not")?;
            if equality.head.as_deref() != Some("=") || equality.args.len() != 2 {
                return None;
            }
            let authored = surface.node(index).unary("not")?;
            let label = d.fact_as(&authored.text, &equality.text, &discharge[index])?;
            pins.push((&equality.args[0], &equality.args[1], label.clone()));
        }
        let source = nodes[nodes.len() - 2].unary("not")?;
        let target = nodes.last()?;
        let authored = surface.node(nodes.len() - 2).unary("not")?;
        let input = d.fact_as(&authored.text, &source.text, &discharge[nodes.len() - 2])?;
        let (image, substituted) = d.substitute_pinned(source, &pins)?;
        let (left, left_normal) = d.normalize(&image)?;
        let (right, right_normal) = d.normalize(target)?;
        if !d.same(&left.text, &right.text)? {
            return None;
        }
        let mut equalities: Vec<String> = substituted.into_iter().collect();
        equalities.extend(left_normal);
        if let Some(normal) = right_normal {
            equalities.push(d.eq(&right.text, &target.text, "symm", &[normal])?);
        }
        if equalities.is_empty() {
            return None;
        }
        let equality = if equalities.len() == 1 {
            equalities.pop()?
        } else {
            d.eq(&source.text, &target.text, "trans", &equalities)?
        };
        let implication = d.step(
            &format!(
                "(not (= {} {})) (not {}) {}",
                source.text, target.text, source.text, target.text
            ),
            "equiv_pos2",
            &[],
        )?;
        let conditional = d.step(
            &format!("(not {}) {}", source.text, target.text),
            "resolution",
            &[implication, equality],
        )?;
        let result = d.step(&target.text, "resolution", &[conditional, input])?;
        d.fact_as(&target.text, &surface.node(nodes.len() - 1).text, &result)?;
        d.append(&format!(
            "(step {id} (cl {}) :rule subproof :discharge ({}))",
            surface.texts.join(" "),
            discharge.join(" "),
        ))?;
        Some(d.output)
    }
}

/// Run the same bounded renderer used by export under an aggregate allowance.
#[must_use]
pub fn checked_ground_substitution_lowering_supported(
    terms: &TermStore,
    clause: &[TermId],
    overrides: Option<&HashMap<TermId, String>>,
    remaining_work: &mut u64,
) -> bool {
    if *remaining_work == 0 {
        return false;
    }
    let printer = AlethePrinter::new_with_overrides_and_budget(
        terms,
        overrides,
        Some((*remaining_work).min(MAX_WORK)),
    );
    let supported = printer
        .format_ground_substitution(ProofId(0), clause)
        .is_some();
    *remaining_work = remaining_work.saturating_sub(printer.work_used());
    supported && !printer.work_budget_exhausted()
}

#[cfg(test)]
mod tests;
