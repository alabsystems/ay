// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Optional, bounded Alethe surface for a checked finite-enum proof.

use ay_core::kani_compat::DetHashMap;
use ay_core::{Symbol, TermData, TermId, TermStore};
use ay_frontend::command::Term as FrontendTerm;

use crate::executor::Executor;

use super::finite_enum::MAX_RENDER_WORK;

const SURFACE_REPEATS: usize = 4;
const PROOF_TEXT_OVERHEAD_PER_EDGE: usize = 256;

#[derive(Debug)]
pub(super) struct FiniteEnumProofSurface {
    pub(super) overrides: DetHashMap<TermId, String>,
}

fn symbol_render_upper_bound(name: &str) -> Option<usize> {
    // Quoting adds two delimiters and can add one escape byte per input byte.
    name.len().checked_mul(2)?.checked_add(2)
}

pub(super) fn surface_text_bounds(left: &str, right: &str) -> Option<(usize, usize)> {
    let left = symbol_render_upper_bound(left)?;
    let right = symbol_render_upper_bound(right)?;
    let equality = left.checked_add(right)?.checked_add(5)?;
    Some((equality.checked_add(6)?, equality))
}

pub(super) fn add_repeated_render_work(total: &mut usize, source: usize, equality: usize) -> bool {
    let Some(rendered) = source
        .checked_add(equality)
        .and_then(|bytes| bytes.checked_mul(SURFACE_REPEATS))
        .and_then(|bytes| bytes.checked_add(PROOF_TEXT_OVERHEAD_PER_EDGE))
        .and_then(|bytes| total.checked_add(bytes))
    else {
        return false;
    };
    let Ok(work) = u64::try_from(rendered) else {
        return false;
    };
    if work > MAX_RENDER_WORK {
        return false;
    }
    *total = rendered;
    true
}

fn canonical_surface_work(
    terms: &TermStore,
    sources: &[(usize, TermId)],
    equalities: &[TermId],
    members: &[TermId],
) -> Option<usize> {
    // `canonical_term_work` is iterative, rejects depth > 256 and accounts
    // string/BigInt/vector payload. Charge every proof occurrence rather than
    // deduplicating the DAG so repeated formatting remains inside 64 MiB.
    sources
        .iter()
        .map(|(_, term)| *term)
        .chain(equalities.iter().copied())
        .chain(members.iter().copied())
        .try_fold(0usize, |used, term| {
            used.checked_add(
                crate::executor::proof_trust_surgery_provenance::canonical_term_work(terms, term)?,
            )
            .filter(|&next| u64::try_from(next).is_ok_and(|work| work <= MAX_RENDER_WORK))
        })
}

#[cfg(test)]
pub(super) fn canonical_surface_work_is_bounded(
    terms: &TermStore,
    sources: &[(usize, TermId)],
    equalities: &[TermId],
    members: &[TermId],
) -> bool {
    canonical_surface_work(terms, sources, equalities, members).is_some()
}

fn exact_surface_binary_equality(
    parsed: &FrontendTerm,
) -> Option<(&FrontendTerm, &FrontendTerm, &str, &str)> {
    let FrontendTerm::App(not, not_args) = parsed else {
        return None;
    };
    let [equality] = not_args.as_slice() else {
        return None;
    };
    let FrontendTerm::App(eq, eq_args) = equality else {
        return None;
    };
    let [FrontendTerm::Symbol(left), FrontendTerm::Symbol(right)] = eq_args.as_slice() else {
        return None;
    };
    (not == "not" && eq == "=").then_some((parsed, equality, left, right))
}

fn canonical_var_name(terms: &TermStore, term: TermId) -> Option<&str> {
    match terms.get(term) {
        TermData::Var(name, _) => Some(name),
        _ => None,
    }
}

fn parsed_pair_matches_canonical(
    terms: &TermStore,
    equality: TermId,
    left: &str,
    right: &str,
) -> bool {
    let TermData::App(Symbol::Named(name), args) = terms.get(equality) else {
        return false;
    };
    let [first, second] = args.as_slice() else {
        return false;
    };
    if name != "=" {
        return false;
    }
    let (Some(first), Some(second)) = (
        canonical_var_name(terms, *first),
        canonical_var_name(terms, *second),
    ) else {
        return false;
    };
    first == left && second == right || first == right && second == left
}

fn insert_conflict_free(
    overrides: &mut DetHashMap<TermId, String>,
    term: TermId,
    rendering: String,
) -> bool {
    match overrides.get(&term) {
        Some(existing) => existing == &rendering,
        None => {
            overrides.insert(term, rendering);
            true
        }
    }
}

impl Executor {
    /// Keep stale sealed proofs out of generic scopes/global overrides.
    pub(crate) fn last_proof_has_finite_enum_sidecar(&self) -> bool {
        self.last_checked_finite_enum_pigeonhole.is_some()
    }

    pub(super) fn build_finite_enum_proof_surface(
        &self,
        roots: &[TermId],
        sources: &[(usize, TermId)],
        equalities: &[TermId],
        members: &[TermId],
    ) -> Option<FiniteEnumProofSurface> {
        if sources.len() != equalities.len() || self.ctx.assertions_parsed().len() != roots.len() {
            return None;
        }

        // First inspect only borrowed shallow AST nodes and charge worst-case
        // quoting/repeated rendering. No source String is formatted yet.
        let canonical_work = canonical_surface_work(&self.ctx.terms, sources, equalities, members)?;
        let mut preflight_work = canonical_work;
        for ((root_index, source), equality) in sources.iter().zip(equalities) {
            if roots.get(*root_index) != Some(source) {
                return None;
            }
            let parsed = self.ctx.assertions_parsed().get(*root_index)?;
            let (_, _, left, right) = exact_surface_binary_equality(parsed)?;
            if !parsed_pair_matches_canonical(&self.ctx.terms, *equality, left, right) {
                return None;
            }
            let (source_bound, equality_bound) = surface_text_bounds(left, right)?;
            if !add_repeated_render_work(&mut preflight_work, source_bound, equality_bound) {
                return None;
            }
        }

        let mut overrides = DetHashMap::default();
        let mut actual_work = canonical_work;
        for ((root_index, source), equality) in sources.iter().zip(equalities) {
            let parsed = self.ctx.assertions_parsed().get(*root_index)?;
            let (source_surface, equality_surface, _, _) = exact_surface_binary_equality(parsed)?;
            let source_rendering =
                crate::executor::proof_surface_syntax::format_frontend_term(source_surface);
            let equality_rendering =
                crate::executor::proof_surface_syntax::format_frontend_term(equality_surface);
            if !add_repeated_render_work(
                &mut actual_work,
                source_rendering.len(),
                equality_rendering.len(),
            ) || !insert_conflict_free(&mut overrides, *source, source_rendering)
                || !insert_conflict_free(&mut overrides, *equality, equality_rendering)
            {
                return None;
            }
        }
        (actual_work <= preflight_work).then_some(FiniteEnumProofSurface { overrides })
    }

    pub(super) fn finite_enum_surface_overrides_for_proof(
        &self,
        proof: &ay_core::Proof,
    ) -> Option<&DetHashMap<TermId, String>> {
        self.checked_finite_enum_capability_for_proof(proof)
            .and_then(|capability| capability.surface.as_ref())
            .map(|surface| &surface.overrides)
    }
}
