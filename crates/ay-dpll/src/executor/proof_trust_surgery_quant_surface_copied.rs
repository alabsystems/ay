// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Conservative census for copied rules under a quantifier surface map.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{AletheRule, Proof, ProofStep, TermId};

use super::QuantSurfacePlans;
use crate::executor::proof_trust_surgery_surface_audit::term_child_count;

/// Resolution consumes only syntactic complements, which the shared audit
/// validates. Any other copied rule touched by a selected override has a rule
/// role this quantifier-specific audit did not plan and therefore fails closed.
pub(super) fn copied_quant_rendering_roles_are_static(
    proof: &Proof,
    live: &[bool],
    plans: &QuantSurfacePlans<'_>,
    terms: &ay_core::TermStore,
    overrides: &HashMap<TermId, String>,
    authenticated_assume_roots: &HashSet<TermId>,
) -> bool {
    const MAX_SCAN_WORK: usize = 100_000;

    if live.len() != proof.steps.len() {
        return false;
    }
    let mut work = 0usize;
    for (index, step) in proof.steps.iter().enumerate() {
        if !live[index]
            || plans.assumes.contains_key(&index)
            || plans.consequences.contains_key(&index)
            || plans.negations.contains_key(&index)
        {
            continue;
        }
        let mut roots = Vec::new();
        match step {
            ProofStep::Assume(term)
                if overrides.contains_key(term) && authenticated_assume_roots.contains(term) =>
            {
                continue;
            }
            ProofStep::Assume(term) => roots.push(*term),
            ProofStep::Resolution { .. } => continue,
            ProofStep::Step {
                rule: AletheRule::Resolution | AletheRule::ThResolution,
                args,
                ..
            } => {
                if args.is_empty() {
                    continue;
                }
                return false;
            }
            ProofStep::Step { clause, args, .. } => {
                if clause.len().saturating_add(args.len()) > MAX_SCAN_WORK.saturating_sub(work) {
                    return false;
                }
                roots.extend(clause.iter().copied());
                roots.extend(args.iter().copied());
            }
            ProofStep::TheoryLemma { clause, .. } => {
                if clause.len() > MAX_SCAN_WORK.saturating_sub(work) {
                    return false;
                }
                roots.extend(clause.iter().copied());
            }
            ProofStep::Anchor { .. } => return false,
            _ => return false,
        }
        let mut pending = roots;
        let mut seen = HashSet::default();
        while let Some(term) = pending.pop() {
            work += 1;
            if work > MAX_SCAN_WORK || overrides.contains_key(&term) {
                return false;
            }
            if seen.insert(term) {
                let Some(child_count) = term_child_count(terms, term) else {
                    return false;
                };
                if pending
                    .len()
                    .saturating_add(work)
                    .saturating_add(child_count)
                    > MAX_SCAN_WORK
                {
                    return false;
                }
                pending.extend(terms.children(term));
            }
        }
    }
    true
}
