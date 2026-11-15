// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Bounded, ground application inventory for functional-congruence lemmas.

use ay_core::kani_compat::{DetHashMap, DetHashSet};
use ay_core::{Symbol, TermData, TermId, TermStore};

pub(super) type ApplicationGroups = DetHashMap<(String, usize), Vec<(TermId, Vec<TermId>)>>;

/// Inventory only the current query DAG. A binder, stop or traversal limit
/// declines the optimization before any lemma is emitted. Both pending memory
/// and examined edges are bounded, including repeated/shared children.
pub(super) fn collect(
    terms: &TermStore,
    roots: &[TermId],
    max_work: usize,
    should_stop: &impl Fn() -> bool,
) -> Option<ApplicationGroups> {
    if roots.len() > max_work {
        return None;
    }
    let mut pending = roots.to_vec();
    let mut seen = DetHashSet::default();
    let mut groups = ApplicationGroups::default();
    let mut work = 0_usize;
    while let Some(term) = pending.pop() {
        work = work.saturating_add(1);
        if work > max_work || should_stop() {
            return None;
        }
        if !seen.insert(term) {
            continue;
        }
        match terms.get(term) {
            TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return None,
            TermData::App(symbol, args) => {
                if pending.len().saturating_add(args.len()) > max_work {
                    return None;
                }
                if let Symbol::Named(name) = symbol {
                    if !args.is_empty() && !crate::features::is_builtin_symbol_name(name) {
                        groups
                            .entry((name.to_string(), args.len()))
                            .or_default()
                            .push((term, args.clone()));
                    }
                }
                pending.extend(args.iter().copied());
            }
            TermData::Not(inner) => pending.push(*inner),
            TermData::Ite(c, a, b) => {
                if pending.len().saturating_add(3) > max_work {
                    return None;
                }
                pending.extend([*c, *a, *b]);
            }
            _ => {}
        }
    }
    for apps in groups.values_mut() {
        apps.sort_unstable_by_key(|(term, _)| term.0);
    }
    Some(groups)
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::Sort;

    #[test]
    fn ignores_unreachable_store_applications() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let b = terms.mk_var("b", Sort::Int);
        let c = terms.mk_var("unreachable", Sort::Int);
        let fa = terms.mk_app(Symbol::named("f"), [a], Sort::Int);
        let fb = terms.mk_app(Symbol::named("f"), [b], Sort::Int);
        let _unused = terms.mk_app(Symbol::named("f"), [c], Sort::Int);
        let root = terms.mk_eq(fa, fb);
        let groups = collect(&terms, &[root], 100, &|| false).expect("ground inventory");
        assert_eq!(groups[&("f".to_string(), 1)].len(), 2);
    }

    #[test]
    fn stops_and_traversal_limits_decline_without_partial_inventory() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let fa = terms.mk_app(Symbol::named("f"), [a], Sort::Int);
        assert!(collect(&terms, &[fa], 100, &|| true).is_none());
        assert!(collect(&terms, &[fa], 1, &|| false).is_none());
    }

    #[test]
    fn binders_and_lets_decline() {
        let mut terms = TermStore::new();
        let a = terms.mk_var("a", Sort::Int);
        let zero = terms.mk_int(0.into());
        let body = terms.mk_eq(a, zero);
        let quantified = terms.mk_forall(vec![("a".to_string(), Sort::Int)], body);
        let bound = terms.mk_let(vec![("a".to_string(), zero)], body);
        assert!(collect(&terms, &[quantified], 100, &|| false).is_none());
        assert!(collect(&terms, &[bound], 100, &|| false).is_none());
    }

    #[test]
    fn helper_caps_new_lemmas_deduplicates_and_records_checked_congruence() {
        let mut executor = crate::executor::Executor::new();
        executor.proof_tracker.enable();
        for (index, name) in ["a", "b", "c"].iter().enumerate() {
            let argument = executor.ctx.terms.mk_var(*name, Sort::Int);
            let app = executor
                .ctx
                .terms
                .mk_app(Symbol::named("f"), [argument], Sort::Int);
            let value = executor.ctx.terms.mk_int(index.into());
            let root = executor.ctx.terms.mk_eq(app, value);
            executor.ctx.assertions.push(root);
        }
        // 3 candidate pairs fit the examined budget (4 * cap) even at
        // cap 1, so emission proceeds incrementally across calls.
        assert_eq!(executor.add_uf_ackermann_congruence_clauses(1), 1);
        assert_eq!(executor.add_uf_ackermann_congruence_clauses(1), 1);
        assert_eq!(executor.add_uf_ackermann_congruence_clauses(10), 1);
        assert_eq!(executor.add_uf_ackermann_congruence_clauses(10), 0);
        assert_eq!(executor.ctx.assertions.len(), 6);
        let proof = executor.proof_tracker.take_proof();
        assert_eq!(proof.steps.len(), 3);
        assert!(proof.steps.iter().all(|step| matches!(
            step,
            ay_core::ProofStep::TheoryLemma {
                kind: ay_core::TheoryLemmaKind::EufCongruent,
                ..
            }
        )));
    }

    #[test]
    fn helper_declines_when_pair_space_exceeds_examined_budget() {
        let mut executor = crate::executor::Executor::new();
        // 8 applications of f: 28 pairs. At cap 1 the examined budget
        // is 4, far below the pair space, so nothing is emitted; at
        // cap 10 the budget (40) covers the space and the first 10
        // clauses of the partial subset are emitted as before.
        for index in 0..8_usize {
            let argument = executor.ctx.terms.mk_var(&format!("x{index}"), Sort::Int);
            let app = executor
                .ctx
                .terms
                .mk_app(Symbol::named("f"), [argument], Sort::Int);
            let value = executor.ctx.terms.mk_int(index.into());
            let root = executor.ctx.terms.mk_eq(app, value);
            executor.ctx.assertions.push(root);
        }
        assert_eq!(executor.add_uf_ackermann_congruence_clauses(1), 0);
        assert_eq!(executor.ctx.assertions.len(), 8);
        assert_eq!(executor.add_uf_ackermann_congruence_clauses(10), 10);
        assert_eq!(executor.ctx.assertions.len(), 18);
    }
}
