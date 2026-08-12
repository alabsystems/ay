// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded validation of the final merged retained-surface map.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::TermData;
use ay_core::TermId;
use ay_proof::split_alethe_application_bounded;

use super::{
    render_roots_have_bounded_depth, render_roots_have_bounded_payload, ProvenanceSurfaceAudit,
    MAX_ALIAS_SCAN_TERMS, MAX_AUDITED_FARKAS_SIGN_CHECKS, MAX_AUDITED_RENDER_WORK,
    MAX_AUDITED_TERMS,
};

fn exact_surface_complements(left: &str, right: &str) -> bool {
    left.strip_prefix("(not ")
        .and_then(|inner| inner.strip_suffix(')'))
        .is_some_and(|inner| inner == right)
        || right
            .strip_prefix("(not ")
            .and_then(|inner| inner.strip_suffix(')'))
            .is_some_and(|inner| inner == left)
}

fn rendered_application_matches(whole: &str, head: &str, operands: &[&str]) -> bool {
    let Some(mut rest) = whole
        .strip_prefix('(')
        .and_then(|text| text.strip_prefix(head))
    else {
        return false;
    };
    for operand in operands {
        let Some(next) = rest
            .strip_prefix(' ')
            .and_then(|text| text.strip_prefix(operand))
        else {
            return false;
        };
        rest = next;
    }
    rest == ")"
}

fn validate_and_roles(
    terms: &ay_core::TermStore,
    rendered: &HashMap<TermId, String>,
    generated: &ay_core::kani_compat::DetHashSet<(TermId, u32, TermId)>,
    copied: &ay_core::kani_compat::DetHashSet<(TermId, u32, TermId)>,
    introductions: &ay_core::kani_compat::DetHashSet<(TermId, Vec<TermId>)>,
) -> bool {
    // The final flag preserves the stronger generated-plan contract: its
    // selected operand must occur exactly once. Copied SAT projections allow
    // duplicates because either identical printed position proves the same
    // literal. Group both classes by root so each bounded source is scanned
    // exactly once across the complete audit.
    let mut roles: Vec<(TermId, u32, TermId, bool)> = generated
        .iter()
        .map(|&(root, index, selected)| (root, index, selected, true))
        .chain(
            copied
                .iter()
                .map(|&(root, index, selected)| (root, index, selected, false)),
        )
        .collect();
    roles.sort_unstable();
    let mut roots: Vec<TermId> = roles
        .iter()
        .map(|role| role.0)
        .chain(introductions.iter().map(|role| role.0))
        .collect();
    roots.sort_unstable();
    roots.dedup();
    let mut role_start = 0usize;
    for root_id in roots {
        while role_start < roles.len() && roles[role_start].0 < root_id {
            role_start += 1;
        }
        let mut role_end = role_start;
        while role_end < roles.len() && roles[role_end].0 == root_id {
            role_end += 1;
        }
        let TermData::App(ay_core::Symbol::Named(head), conjuncts) = terms.get(root_id) else {
            return false;
        };
        let Some(root) = rendered.get(&root_id) else {
            return false;
        };
        let Ok(mut actual) = split_alethe_application_bounded(
            root,
            "and",
            crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS,
            MAX_AUDITED_RENDER_WORK as usize,
        ) else {
            return false;
        };
        let mut expected: Vec<&str> = conjuncts
            .iter()
            .filter_map(|term| rendered.get(term).map(String::as_str))
            .collect();
        if head != "and" || expected.len() != conjuncts.len() || actual.len() != expected.len() {
            return false;
        }
        if introductions
            .iter()
            .any(|(root, expected)| *root == root_id && expected.as_slice() != conjuncts.as_slice())
        {
            return false;
        }
        for &(_, index, selected_id, unique) in &roles[role_start..role_end] {
            let Some(selected) = rendered.get(&selected_id) else {
                return false;
            };
            let occurrences = actual
                .iter()
                .filter(|operand| **operand == selected.as_str())
                .count();
            if conjuncts.get(index as usize) != Some(&selected_id)
                || occurrences == 0
                || unique && occurrences != 1
            {
                return false;
            }
        }
        actual.sort_unstable();
        expected.sort_unstable();
        if actual != expected {
            return false;
        }
        role_start = role_end;
    }
    true
}

impl ProvenanceSurfaceAudit {
    /// Materialize the authenticated subset for a standalone repair whose
    /// effective map starts empty. Collection is already byte/count bounded;
    /// this is the only clone of each selected spelling.
    pub(in crate::executor) fn materialize_protected_requirements(
        &self,
    ) -> Option<HashMap<TermId, String>> {
        if self.overflowed {
            return None;
        }
        Some(
            self.requirements
                .iter()
                .filter(|(term, _)| {
                    self.protected.contains(*term)
                        && !self.compatibility_requirements.contains(*term)
                })
                .map(|(&term, spelling)| (term, spelling.clone()))
                .collect(),
        )
    }

    pub(in crate::executor) fn validate_effective(
        &self,
        terms: &ay_core::TermStore,
        effective: &HashMap<TermId, String>,
    ) -> bool {
        if self.overflowed {
            return false;
        }
        let override_bytes = effective.values().try_fold(0u64, |total, surface| {
            total.checked_add(surface.len() as u64)
        });
        if override_bytes.is_none_or(|bytes| bytes > MAX_AUDITED_RENDER_WORK) {
            return false;
        }
        for (&term, expected) in &self.requirements {
            if self.protected.contains(&term) {
                match effective.get(&term) {
                    Some(actual) if actual != expected => return false,
                    None if !self.compatibility_requirements.contains(&term) => {
                        // A required spelling that IS the canonical rendering
                        // is satisfied by the absence of any override: the
                        // renderer prints exactly the required bytes on its
                        // own. (The caller prunes such inert identity
                        // overrides before the static-rendering scans.)
                        if ay_proof::format_term_alethe(terms, term) != *expected {
                            return false;
                        }
                    }
                    _ => {}
                }
            }
        }
        let roles_valid = self.protected.iter().all(|term| {
            let requirement = self.requirements.get(term);
            let overridden = effective.get(term);
            if self.rigid.contains(term)
                && overridden.is_some()
                && !self.recursive_rigid_identity.contains(term)
            {
                return false;
            }
            if self.farkas.contains(term)
                && overridden.is_some()
                && !self.arithmetic_requirements.contains(term)
            {
                return false;
            }
            overridden.is_none_or(|actual| requirement.is_some_and(|expected| expected == actual))
        });
        if !roles_valid {
            return false;
        }
        // Every registered rule operand is formatted through this one cache,
        // including non-Boolean forall-instantiation arguments that do not
        // participate in a polarity pair or Farkas row.
        let mut render_terms = self.protected.clone();
        for &(left, right) in &self.polarity_pairs {
            if self.protected.contains(&left) || self.protected.contains(&right) {
                render_terms.insert(left);
                render_terms.insert(right);
            }
        }
        for (clause, _) in &self.farkas_lemmas {
            for &literal in clause {
                render_terms.insert(match terms.get(literal) {
                    TermData::Not(inner) => *inner,
                    _ => literal,
                });
            }
        }
        for &(left, right) in &self.render_equalities {
            render_terms.insert(left);
            render_terms.insert(right);
        }
        if render_terms.len() > MAX_AUDITED_TERMS {
            return false;
        }
        let mut render_terms: Vec<TermId> = render_terms.into_iter().collect();
        render_terms.sort_unstable();
        let mut recursive_rigid_overrides: Vec<TermId> = self
            .recursive_rigid_identity
            .iter()
            .filter(|term| effective.contains_key(*term))
            .copied()
            .collect();
        recursive_rigid_overrides.sort_unstable();
        if !render_roots_have_bounded_depth(
            terms,
            &render_terms,
            MAX_AUDITED_TERMS,
            MAX_ALIAS_SCAN_TERMS,
        ) {
            return false;
        }
        if !render_roots_have_bounded_payload(
            terms,
            &render_terms,
            MAX_AUDITED_TERMS,
            MAX_AUDITED_RENDER_WORK as usize,
        ) {
            return false;
        }
        if !render_roots_have_bounded_depth(
            terms,
            &recursive_rigid_overrides,
            MAX_AUDITED_TERMS,
            MAX_ALIAS_SCAN_TERMS,
        ) || !render_roots_have_bounded_payload(
            terms,
            &recursive_rigid_overrides,
            MAX_AUDITED_TERMS,
            MAX_AUDITED_RENDER_WORK as usize,
        ) {
            return false;
        }
        let Ok((rendered, canonical_rigid, render_work)) =
            ay_proof::format_terms_alethe_with_overrides_and_canonical_bounded_with_work(
                terms,
                &render_terms,
                effective,
                &recursive_rigid_overrides,
                MAX_AUDITED_RENDER_WORK,
            )
        else {
            return false;
        };
        if !recursive_rigid_overrides.iter().all(|term| {
            rendered
                .get(term)
                .zip(canonical_rigid.get(term))
                .is_some_and(|(effective, canonical)| effective == canonical)
        }) {
            return false;
        }
        let generated_render_work = self.generated_connective_render_uses.iter().try_fold(
            0usize,
            |work, (root, factor)| {
                rendered
                    .get(root)
                    .and_then(|surface| surface.len().checked_mul(*factor))
                    .and_then(|next| work.checked_add(next))
            },
        );
        let remaining_render_work = MAX_AUDITED_RENDER_WORK
            .checked_sub(render_work)
            .and_then(|remaining| usize::try_from(remaining).ok());
        if generated_render_work
            .zip(remaining_render_work)
            .is_none_or(|(work, remaining)| work > remaining)
        {
            return false;
        }
        if !self.polarity_pairs.iter().all(|&(left, right)| {
            (!self.protected.contains(&left) && !self.protected.contains(&right))
                || rendered
                    .get(&left)
                    .zip(rendered.get(&right))
                    .is_some_and(|(left, right)| exact_surface_complements(left, right))
        }) {
            return false;
        }
        if !self.render_equalities.iter().all(|&(left, right)| {
            rendered
                .get(&left)
                .zip(rendered.get(&right))
                .is_some_and(|(left, right)| left == right)
        }) {
            return false;
        }
        if !self
            .ite_intro_roles
            .iter()
            .all(|&(ite_term, eq_then, eq_else)| {
                let TermData::Ite(cond, then_term, else_term) = *terms.get(ite_term) else {
                    return false;
                };
                let Some((ite, cond, then_term, else_term, eq_then, eq_else)) = rendered
                    .get(&ite_term)
                    .zip(rendered.get(&cond))
                    .zip(rendered.get(&then_term))
                    .zip(rendered.get(&else_term))
                    .zip(rendered.get(&eq_then))
                    .zip(rendered.get(&eq_else))
                    .map(
                        |(((((ite, cond), then_term), else_term), eq_then), eq_else)| {
                            (ite, cond, then_term, else_term, eq_then, eq_else)
                        },
                    )
                else {
                    return false;
                };
                rendered_application_matches(ite, "ite", &[cond, then_term, else_term])
                    && rendered_application_matches(eq_then, "=", &[ite, then_term])
                    && rendered_application_matches(eq_else, "=", &[ite, else_term])
            })
        {
            return false;
        }
        if !validate_and_roles(
            terms,
            &rendered,
            &self.and_projection_roles,
            &self.copied_and_projection_roles,
            &self.and_introduction_roles,
        ) {
            return false;
        }
        if !self.or_decomposition_roles.iter().all(|(root, disjuncts)| {
            let Some(root) = rendered.get(root) else {
                return false;
            };
            let Ok(mut actual) = split_alethe_application_bounded(
                root,
                "or",
                crate::executor::proof_trust_surgery_provenance::MAX_PROVENANCE_REPAIR_TERMS,
                MAX_AUDITED_RENDER_WORK as usize,
            ) else {
                return false;
            };
            let mut expected: Vec<&str> = disjuncts
                .iter()
                .filter_map(|term| rendered.get(term).map(String::as_str))
                .collect();
            if expected.len() != disjuncts.len() || actual.len() != expected.len() {
                return false;
            }
            actual.sort_unstable();
            expected.sort_unstable();
            actual == expected
        }) {
            return false;
        }
        let mut sign_checks = MAX_AUDITED_FARKAS_SIGN_CHECKS;
        let mut parse_bytes = MAX_AUDITED_RENDER_WORK as usize;
        self.validate_farkas_lemmas_with_budget(
            terms,
            &rendered,
            &mut sign_checks,
            &mut parse_bytes,
        )
    }
}
