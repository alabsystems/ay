// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Keep a raw authored premise distinct from canonical descendant aliases.
//!
//! `(>= r 0)` elaborates to the same term as `(<= 0 r)`. A first-wins
//! printer override for the former must not rename occurrences of the latter
//! inside a raw root that contains BOTH spellings. This candidate replaces
//! the whole proof, so its raw descendants can use their own native spelling
//! if and only if the unchanged whole-root roundtrip accepts that spelling.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{TermData, TermId};
use ay_frontend::command::Term as FrontendTerm;

use super::super::Executor;
use crate::executor::proof_surface_syntax::{
    strip_frontend_annotations, surface_override_map_is_bounded,
};
use crate::executor::proof_trust_surgery_provenance::canonical_term_work_probe_metered;
use crate::executor::proof_trust_surgery_surface_audit::{
    render_roots_have_bounded_payload, term_child_count, ProofSourcePass,
};

const ASSERT_WRAPPER_BYTES: usize = "(assert )".len();
const PARSE_PASSES: usize = 4;

#[derive(Clone, Copy)]
enum RoundtripSpelling {
    Exact,
    BitVectorLiterals,
}

impl Executor {
    pub(super) fn try_raw_descendant_spellings(
        &mut self,
        root: TermId,
        assertion: &FrontendTerm,
    ) -> bool {
        // The ordinary fast path still supports datatype fields. This extra
        // retry declines before an unpriced derived overlay can be allocated.
        if self.ctx.has_dt_field_surface_entries() {
            return false;
        }
        // A sparse map can have huge capacity and almost no live entries.
        // Inspect only its header before any values()/iter() walk or clone.
        let Some(table_work) = self
            .last_proof_term_overrides
            .as_ref()
            .and_then(override_table_copy_work)
        else {
            return false;
        };
        if table_work > self.proof_source_work.remaining() {
            return false;
        }
        // Retain the existing source-stage debit. Canonical walks, global
        // map copies and the rendered roundtrip are charged separately below.
        if !self.proof_source_work.spend(
            ProofSourcePass::AuthoredFoldIdentityRebuild,
            std::iter::once(assertion),
        ) {
            return false;
        }
        let Some((canonical_work, visits)) = self.raw_retry_canonical_work(root) else {
            return false;
        };
        let Some(seen) = self.raw_retry_descendants(root) else {
            return false;
        };
        // Pay for walking the table before either scan of its live strings.
        if !self.proof_source_work.spend_canonical_scan_work(table_work) {
            return false;
        }
        let Some(overrides) = self.last_proof_term_overrides.as_ref() else {
            return false;
        };
        if !surface_override_map_is_bounded(overrides) {
            return false;
        }
        let Some(string_work) = override_string_copy_work(overrides) else {
            return false;
        };
        if !self
            .proof_source_work
            .spend_canonical_scan_work(string_work)
        {
            return false;
        }
        let Some(render_budget) = self.raw_retry_render_budget(root, canonical_work, visits) else {
            return false;
        };
        let Some(overrides) = self.last_proof_term_overrides.as_ref() else {
            return false;
        };
        let saved = overrides.clone();
        let mut filtered = saved.clone();
        // Preserve root/let bridges, unrelated entries and leaf spellings.
        // Only composite aliases can hide the raw connective structure.
        filtered.retain(|term, _| {
            *term == root
                || !seen.contains(term)
                || !matches!(
                    self.ctx.terms.get(*term),
                    TermData::App(..) | TermData::Not(..) | TermData::Ite(..)
                )
        });
        if filtered == saved {
            return false;
        }
        if filtered.iter().any(|(term, text)| {
            (*term == root || seen.contains(term)) && text.len() > render_budget
        }) {
            return false;
        }
        self.last_proof_term_overrides = Some(filtered);
        if self.raw_retry_roundtrip(root, assertion, render_budget) {
            super::super::authored_consequence_replay::replay_note(|| {
                "[fold-identity] raw descendant spellings restored the exact authored root".into()
            });
            true
        } else {
            self.last_proof_term_overrides = Some(saved);
            false
        }
    }

    fn raw_retry_canonical_work(&self, root: TermId) -> Option<(usize, usize)> {
        if self.proof_source_work.remaining() < size_of::<TermData>() {
            return None;
        }
        let (work, visits) = canonical_term_work_probe_metered(&self.ctx.terms, root, |work| {
            self.proof_source_work.spend_canonical_scan_work(work)
        });
        work?.ok().map(|work| (work, visits))
    }

    fn raw_retry_descendants(&self, root: TermId) -> Option<HashSet<TermId>> {
        let mut seen = HashSet::default();
        let mut pending = vec![root];
        while let Some(term) = pending.pop() {
            if !self
                .proof_source_work
                .spend_canonical_scan_work(size_of::<TermData>())
            {
                return None;
            }
            if !seen.insert(term) {
                continue;
            }
            let children = term_child_count(&self.ctx.terms, term)?;
            if seen
                .len()
                .saturating_add(pending.len())
                .saturating_add(children)
                > super::MAX_SCANNED_CONJUNCT_NODES
            {
                return None;
            }
            pending.extend(self.ctx.terms.children(term));
        }
        Some(seen)
    }

    fn raw_retry_render_budget(
        &self,
        root: TermId,
        canonical_work: usize,
        visits: usize,
    ) -> Option<usize> {
        // The payload preflight visits at most `visits` terms and that many
        // sort nodes; pay before asking it, including on a refused payload.
        let work = visits.checked_mul(2)?.checked_mul(size_of::<TermData>())?;
        if !self.proof_source_work.spend_canonical_scan_work(work) {
            return None;
        }
        let parse_overhead = ASSERT_WRAPPER_BYTES.checked_mul(PARSE_PASSES)?;
        let budget = self
            .proof_source_work
            .remaining()
            .checked_sub(parse_overhead)?
            / (PARSE_PASSES + 1);
        if canonical_work > budget || budget == 0 {
            return None;
        }
        render_roots_have_bounded_payload(&self.ctx.terms, &[root], visits, budget)
            .then_some(budget)
    }

    /// Literal-only roundtrip for DAG-native propositional steps. Congruence
    /// candidates retain the exact-source gate; no authored operand is renamed.
    pub(super) fn raw_propositional_literal_roundtrip(
        &self,
        root: TermId,
        assertion: &FrontendTerm,
    ) -> bool {
        if !self.proof_source_work.spend(
            ProofSourcePass::AuthoredFoldIdentityRebuild,
            std::iter::once(assertion),
        ) {
            return false;
        }
        let Some((work, visits)) = self.raw_retry_canonical_work(root) else {
            return false;
        };
        let Some(budget) = self.raw_retry_render_budget(root, work, visits) else {
            return false;
        };
        self.raw_retry_roundtrip_in_spelling(
            root,
            assertion,
            budget,
            RoundtripSpelling::BitVectorLiterals,
        )
    }

    fn raw_retry_roundtrip(&self, root: TermId, assertion: &FrontendTerm, budget: usize) -> bool {
        self.raw_retry_roundtrip_in_spelling(root, assertion, budget, RoundtripSpelling::Exact)
    }

    fn raw_retry_roundtrip_in_spelling(
        &self,
        root: TermId,
        assertion: &FrontendTerm,
        budget: usize,
        spelling: RoundtripSpelling,
    ) -> bool {
        let Some(overrides) = self.last_proof_term_overrides.as_ref() else {
            return false;
        };
        let Ok(budget_u64) = u64::try_from(budget) else {
            return false;
        };
        let result = ay_proof::format_terms_alethe_with_overrides_and_canonical_bounded_with_work(
            &self.ctx.terms,
            &[root],
            overrides,
            &[],
            budget_u64,
        );
        let Ok((mut rendered, _, work)) = result else {
            // A failed renderer does not return its exact work. Conservatively
            // exhaust its reserved query allowance instead of replaying it.
            self.proof_source_work
                .spend_canonical_scan_work(self.proof_source_work.remaining());
            return false;
        };
        let Ok(work) = usize::try_from(work) else {
            return false;
        };
        if !self.proof_source_work.spend_canonical_scan_work(work) {
            return false;
        }
        let Some(rendered) = rendered.remove(&root) else {
            return false;
        };
        // Account for the assert wrapper, parsing and the AST clone returned
        // by the existing exact-source parser before any of them runs.
        let Some(parse_work) = rendered
            .len()
            .checked_add(ASSERT_WRAPPER_BYTES)
            .and_then(|bytes| bytes.checked_mul(PARSE_PASSES))
        else {
            return false;
        };
        if !self.proof_source_work.spend_canonical_scan_work(parse_work) {
            return false;
        }
        super::super::parse_rendered_assertion(&rendered).is_some_and(|parsed| {
            let parsed = strip_frontend_annotations(&parsed);
            let assertion = strip_frontend_annotations(assertion);
            if matches!(spelling, RoundtripSpelling::Exact) {
                return parsed == assertion;
            }
            use super::super::authored_bv_bitblast_refutation::bv_literal_spelling::{
                literal_normalization_work, same_modulo_bv_literal_spelling,
            };
            let Some(work) = literal_normalization_work(parsed).and_then(|left| {
                literal_normalization_work(assertion).and_then(|right| left.checked_add(right))
            }) else {
                return false;
            };
            self.proof_source_work.spend_canonical_scan_work(work)
                && same_modulo_bv_literal_spelling(parsed, assertion)
        })
    }
}

fn override_table_copy_work(overrides: &HashMap<TermId, String>) -> Option<usize> {
    // Capacity includes vacant buckets. Double the entry layout to cover
    // bucket/control overhead. Keep the earlier conservative four-copy
    // allowance for table scans and snapshots; rendering is charged separately.
    overrides
        .capacity()
        .checked_mul(size_of::<(TermId, String)>())?
        .checked_mul(2)?
        .checked_mul(4)
}

fn override_string_copy_work(overrides: &HashMap<TermId, String>) -> Option<usize> {
    overrides
        .values()
        .try_fold(0usize, |work, text| work.checked_add(text.len()))?
        .checked_mul(4)
}

#[cfg(test)]
#[path = "authored_fold_raw_spelling_tests.rs"]
mod tests;
