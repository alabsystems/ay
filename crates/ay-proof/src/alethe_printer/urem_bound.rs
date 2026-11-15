// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Export of the exact native remainder theorem; native acceptance is separate.

use super::emission_progress::EmissionProgress;
use super::{dialect, AlethePrinter};
use ay_core::kani_compat::DetHashSet;
use ay_core::{ProofId, TermData, TermId};

mod names;
mod support;
pub use support::checked_urem_bound_lowering_supported;

impl AlethePrinter<'_> {
    pub(super) fn format_urem_bound(&self, id: ProofId, clause: &[TermId]) -> Option<String> {
        self.check_emission_progress(0).ok()?;
        let shape =
            crate::checker::bv_urem_bound::validate(self.terms, id, clause, &mut |work, bytes| {
                work.checked_add(bytes)
                    .and_then(|n| u64::try_from(n).ok())
                    .is_some_and(|n| self.admit_emission_work(n))
            })
            .ok()?;
        self.urem_source_agrees(shape.theorem)?;
        let prefix = self.urem_definition_prefix(id)?;
        let dividend = self.format_term(shape.dividend);
        let divisor = self.format_term(shape.divisor);
        let spelled = self.format_clause(clause);
        let bytes = dividend
            .len()
            .checked_add(divisor.len())?
            .checked_add(spelled.len())?;
        self.admit_emission_work(u64::try_from(bytes).ok()?)
            .then_some(())?;
        // All nested stage observations debit THIS cumulative printer owner.
        // The existing local SAT/Chain caps remain defensive limits, never a
        // renewal of caller permission. This is checkpoint accounting, not a
        // claim that every internal evaluator instruction is instrumented.
        let mut continuing = || self.admit_emission_work(1);
        let progress = EmissionProgress::with_caller(&mut continuing);
        let text = super::mul_overflow_cert::remainder::certificate(
            shape.width,
            &dividend,
            &divisor,
            &prefix,
            &id.to_string(),
            &spelled,
            progress,
        )?;
        self.admit_emission_work(u64::try_from(text.len()).ok()?)
            .then_some(())?;
        drop(dividend);
        drop(divisor);
        drop(spelled);
        self.check_emission_progress(0).ok()?;
        dialect::note_clean_only(dialect::CleanOnlySpelling::FixedDivider);
        Some(text)
    }

    // An override must preserve every reached node, not just the theorem's
    // head. A renamed descendant cannot inherit the native source theorem.
    fn urem_source_agrees(&self, root: TermId) -> Option<()> {
        let mut stack = Vec::new();
        let mut seen = DetHashSet::default();
        self.admit_emission_work(64).then_some(())?;
        stack.try_reserve(1).ok()?;
        stack.push(root);
        while let Some(id) = stack.pop() {
            self.admit_emission_work(64).then_some(())?;
            seen.try_reserve(1).ok()?;
            if !seen.insert(id) {
                continue;
            }
            let overridden = self.term_overrides.is_some_and(|map| map.contains_key(&id))
                || self.skolem_overrides.borrow().contains_key(&id)
                || self.let_bridge_renderings.borrow().contains_key(&id);
            if overridden {
                let actual = self.format_term(id);
                let expected = self.format_term_data(self.terms.get(id));
                self.admit_emission_work(
                    u64::try_from(actual.len().checked_add(expected.len())?).ok()?,
                )
                .then_some(())?;
                if actual != expected {
                    return None;
                }
            }
            let inline;
            let children: &[TermId] = match self.terms.get(id) {
                TermData::App(_, args) => args,
                TermData::Not(arg) => std::slice::from_ref(arg),
                TermData::Ite(c, a, b) => {
                    inline = [*c, *a, *b];
                    &inline
                }
                TermData::Const(_) | TermData::Var(..) => &[],
                _ => return None,
            };
            let work = children.len().checked_mul(8)?;
            self.admit_emission_work(u64::try_from(work).ok()?)
                .then_some(())?;
            stack.try_reserve(children.len()).ok()?;
            stack.extend_from_slice(children);
        }
        drop(stack);
        drop(seen);
        self.check_emission_progress(0).ok()?;
        Some(())
    }
}
