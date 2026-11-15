// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Checked integer separation for current ground equality arrangements.

use ay_core::kani_compat::DetHashSet;
use ay_core::{Sort, Symbol, TermData, TermId, TermStore};

use super::super::Executor;

#[cfg(test)]
mod tests;

fn integer_variable(terms: &TermStore, term: TermId) -> bool {
    matches!(terms.get(term), TermData::Var(_, _)) && terms.sort(term) == &Sort::Int
}

/// Finish inventory before mutating solver state. Stops, binders or excessive
/// work decline the optimization, including repeated/shared incoming edges.
fn equality_pairs(
    terms: &TermStore,
    roots: &[TermId],
    work_limit: usize,
    stop: &impl Fn() -> bool,
) -> Option<Vec<(TermId, TermId)>> {
    if roots.len() > work_limit {
        return None;
    }
    let mut pending = roots.to_vec();
    let mut seen = DetHashSet::default();
    let mut pairs = DetHashSet::default();
    let mut work = 0;
    while let Some(term) = pending.pop() {
        work += 1;
        if work > work_limit || stop() {
            return None;
        }
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return None,
            TermData::App(symbol, args) => {
                if symbol.name() == "=" && args.len() == 2 {
                    let (a, b) = (args[0], args[1]);
                    if a != b && integer_variable(terms, a) && integer_variable(terms, b) {
                        pairs.insert(if a < b { (a, b) } else { (b, a) });
                    }
                }
                if pending.len().saturating_add(args.len()) > work_limit {
                    return None;
                }
                pending.extend(args.iter().copied());
            }
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(condition, then_term, else_term) => {
                if pending.len().saturating_add(3) > work_limit {
                    return None;
                }
                pending.extend([*condition, *then_term, *else_term]);
            }
            TermData::Var(..) | TermData::Const(..) => {}
            _ => return None,
        }
    }
    let mut pairs: Vec<_> = pairs.into_iter().collect();
    pairs.sort_unstable();
    Some(pairs)
}

fn separation_clause(terms: &mut TermStore, a: TermId, b: TermId) -> Vec<TermId> {
    let equality = terms.mk_eq(a, b);
    let one = terms.mk_int(1.into());
    let next_a = terms.mk_add(vec![a, one]);
    let next_b = terms.mk_add(vec![b, one]);
    let forward = terms.mk_le(next_a, b);
    let reverse = terms.mk_le(next_b, a);
    vec![equality, forward, reverse]
}

impl Executor {
    /// Expose the integer-domain separation needed when a UF arrangement
    /// decides x != y. Each clause is checked and, when tracking is enabled,
    /// recorded as a derived packed unit; it never gains authored authority.
    pub(in crate::executor) fn add_ground_integer_separation(&mut self, cap: usize) -> usize {
        // A working assertion window may already contain derived constraints.
        // Only the caller's existing original-root authority can license the
        // later proof; never recapture this window as authored premises.
        if cap == 0 {
            return 0;
        }
        let Some(original) = self
            .proof_problem_assertion_provenance
            .as_ref()
            .map(|provenance| provenance.original_problem_assertions.as_slice())
        else {
            return 0;
        };
        let stop = self.make_should_stop();
        // Leave the established shared scalar-ITE arrangement lane intact.
        // Naming may already have hidden those ITEs from the working DAG, so
        // this boundary must inspect the caller's exact original roots.
        if super::solve_harness::ite_definitions::scan_uf_argument_ites(
            &self.ctx.terms,
            original,
            &stop,
        ) != Some(false)
        {
            return 0;
        }
        let Some(pairs) = equality_pairs(
            &self.ctx.terms,
            &self.ctx.assertions,
            cap.saturating_mul(128),
            &stop,
        ) else {
            return 0;
        };
        let mut active: DetHashSet<_> = self.ctx.assertions.iter().copied().collect();
        let mut added = 0;
        for (a, b) in pairs.into_iter().take(cap) {
            if stop() {
                break;
            }
            let clause = separation_clause(&mut self.ctx.terms, a, b);
            if !ay_core::proof_validation::recognize_int_guarded_split_gap(&self.ctx.terms, &clause)
            {
                continue;
            }
            // Raw packing retains the exact independently validated order.
            let packed = self
                .ctx
                .terms
                .mk_app(Symbol::named("or"), clause.clone(), Sort::Bool);
            if active.contains(&packed) {
                continue;
            }
            if self.proof_tracker.is_enabled()
                && self
                    .proof_tracker
                    .add_packed_guarded_integer_lemma(&mut self.ctx.terms, packed, clause)
                    .is_none()
            {
                continue;
            }
            active.insert(packed);
            self.ctx.assertions.push(packed);
            added += 1;
        }
        added
    }
}
