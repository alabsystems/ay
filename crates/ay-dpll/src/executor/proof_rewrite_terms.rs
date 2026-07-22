// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof term rewriting engine.
//!
//! Rewrites proof terms to substitute auxiliary variables (e.g. division
//! quotient/remainder) with their semantic equivalents, deduplicates clauses,
//! and fixes up resolution conclusions after rewriting.
//!
//! Extracted from `proof_rewrite.rs` for code health (#5970).

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep};
use ay_core::{TermId, TermStore};

/// Red zone size for `stacker::maybe_grow` in proof term rewrite recursion (#8414).
const PROOF_REWRITE_STACK_RED_ZONE: usize = 32 * 1024;

/// Stack segment size allocated by stacker for proof term rewrite recursion.
const PROOF_REWRITE_STACK_SIZE: usize = 1024 * 1024;

use super::Executor;

impl Executor {
    pub(in crate::executor) fn rewrite_proof_terms(
        terms: &mut TermStore,
        proof: &mut Proof,
        rewrites: &HashMap<TermId, TermId>,
    ) {
        let mut cache: HashMap<TermId, TermId> = HashMap::default();
        for step in &mut proof.steps {
            match step {
                ProofStep::Assume(term) => {
                    *term = Self::rewrite_term(terms, *term, rewrites, &mut cache);
                }
                ProofStep::TheoryLemma { clause, .. } => {
                    for lit in clause.iter_mut() {
                        *lit = Self::rewrite_term(terms, *lit, rewrites, &mut cache);
                    }
                    Self::dedup_clause(clause);
                }
                ProofStep::Step { clause, args, .. } => {
                    for lit in clause.iter_mut() {
                        *lit = Self::rewrite_term(terms, *lit, rewrites, &mut cache);
                    }
                    Self::dedup_clause(clause);
                    for arg in args {
                        *arg = Self::rewrite_term(terms, *arg, rewrites, &mut cache);
                    }
                }
                ProofStep::Resolution { clause, pivot, .. } => {
                    *pivot = Self::rewrite_term(terms, *pivot, rewrites, &mut cache);
                    for lit in clause.iter_mut() {
                        *lit = Self::rewrite_term(terms, *lit, rewrites, &mut cache);
                    }
                    Self::dedup_clause(clause);
                }
                ProofStep::Anchor { .. } => {}
                other => unreachable!("unhandled ProofStep in rewrite_proof_terms(): {other:?}"),
            }
        }
    }

    fn dedup_clause(clause: &mut Vec<TermId>) {
        #[cfg(not(kani))]
        let mut seen = ay_core::kani_compat::det_hash_set_with_capacity(clause.len());
        #[cfg(kani)]
        let mut seen = HashSet::default();
        clause.retain(|lit| seen.insert(*lit));
    }

    pub(in crate::executor) fn fixup_resolution_conclusions(terms: &TermStore, proof: &mut Proof) {
        let mut derived: Vec<Vec<TermId>> = Vec::with_capacity(proof.steps.len());
        for step in &proof.steps {
            derived.push(match step {
                ProofStep::Assume(term) => vec![*term],
                ProofStep::TheoryLemma { clause, .. }
                | ProofStep::Step { clause, .. }
                | ProofStep::Resolution { clause, .. } => clause.clone(),
                _ => Vec::new(),
            });
        }
        for (idx, step) in proof.steps.iter_mut().enumerate() {
            let (clause, premises) = match step {
                ProofStep::Step {
                    rule: AletheRule::ThResolution | AletheRule::Resolution,
                    clause,
                    premises,
                    ..
                } => (clause, premises),
                _ => continue,
            };
            if premises.len() != 2 {
                continue;
            }
            let (p0, p1) = (premises[0].0 as usize, premises[1].0 as usize);
            if p0 >= idx || p1 >= idx {
                continue;
            }
            if let Some(new_clause) = Self::compute_resolvent(terms, &derived[p0], &derived[p1]) {
                *clause = new_clause.clone();
                derived[idx] = new_clause;
            }
        }
    }

    fn compute_resolvent(terms: &TermStore, c1: &[TermId], c2: &[TermId]) -> Option<Vec<TermId>> {
        for &lit1 in c1 {
            for &lit2 in c2 {
                if !Self::are_complementary(terms, lit1, lit2) {
                    continue;
                }
                let mut result = Vec::new();
                let mut seen = HashSet::default();
                for &l in c1 {
                    if l != lit1 && seen.insert(l) {
                        result.push(l);
                    }
                }
                for &l in c2 {
                    if l != lit2 && seen.insert(l) {
                        result.push(l);
                    }
                }
                return Some(result);
            }
        }
        None
    }

    fn are_complementary(terms: &TermStore, a: TermId, b: TermId) -> bool {
        match terms.get(a) {
            TermData::Not(inner) if *inner == b => true,
            _ => matches!(terms.get(b), TermData::Not(inner) if *inner == a),
        }
    }

    /// Uses `stacker::maybe_grow` for stack safety on deeply nested terms (#8414).
    pub(in crate::executor) fn rewrite_term(
        terms: &mut TermStore,
        term: TermId,
        rewrites: &HashMap<TermId, TermId>,
        cache: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        stacker::maybe_grow(
            PROOF_REWRITE_STACK_RED_ZONE,
            PROOF_REWRITE_STACK_SIZE,
            || {
                if let Some(&r) = rewrites.get(&term) {
                    return r;
                }
                if let Some(&r) = cache.get(&term) {
                    return r;
                }
                let term_data = terms.get(term).clone();
                let rewritten = match term_data {
                    TermData::Const(_) | TermData::Var(_, _) | TermData::Let(_, _) => term,
                    TermData::Not(inner) => {
                        let new_inner = Self::rewrite_term(terms, inner, rewrites, cache);
                        if new_inner == inner {
                            term
                        } else {
                            terms.mk_not(new_inner)
                        }
                    }
                    TermData::Ite(cond, then_t, else_t) => {
                        let (nc, nt, ne) = (
                            Self::rewrite_term(terms, cond, rewrites, cache),
                            Self::rewrite_term(terms, then_t, rewrites, cache),
                            Self::rewrite_term(terms, else_t, rewrites, cache),
                        );
                        if (nc, nt, ne) == (cond, then_t, else_t) {
                            term
                        } else {
                            terms.mk_ite(nc, nt, ne)
                        }
                    }
                    TermData::Forall(vars, body, triggers) => Self::rewrite_quantifier(
                        terms, term, vars, body, triggers, true, rewrites, cache,
                    ),
                    TermData::Exists(vars, body, triggers) => Self::rewrite_quantifier(
                        terms, term, vars, body, triggers, false, rewrites, cache,
                    ),
                    TermData::App(sym, args) => {
                        let mut changed = false;
                        let new_args: Vec<TermId> = args
                            .into_iter()
                            .map(|a| {
                                let na = Self::rewrite_term(terms, a, rewrites, cache);
                                changed |= na != a;
                                na
                            })
                            .collect();
                        if !changed {
                            term
                        } else {
                            terms.mk_app(sym, new_args, terms.sort(term).clone())
                        }
                    }
                    other => {
                        unreachable!("unhandled TermData variant in rewrite_term(): {other:?}")
                    }
                };
                debug_assert!(
                    terms.sort(term) == terms.sort(rewritten),
                    "BUG: proof rewrite changed sort of term {term:?}",
                );
                cache.insert(term, rewritten);
                rewritten
            },
        ) // stacker::maybe_grow
    }

    #[allow(clippy::too_many_arguments)]
    fn rewrite_quantifier(
        terms: &mut TermStore,
        original: TermId,
        vars: Vec<(String, ay_core::Sort)>,
        body: TermId,
        triggers: Vec<Vec<TermId>>,
        is_forall: bool,
        rewrites: &HashMap<TermId, TermId>,
        cache: &mut HashMap<TermId, TermId>,
    ) -> TermId {
        let mut changed = false;
        let new_body = Self::rewrite_term(terms, body, rewrites, cache);
        changed |= new_body != body;
        let new_triggers: Vec<Vec<TermId>> = triggers
            .into_iter()
            .map(|multi| {
                multi
                    .into_iter()
                    .map(|t| {
                        let nt = Self::rewrite_term(terms, t, rewrites, cache);
                        changed |= nt != t;
                        nt
                    })
                    .collect()
            })
            .collect();
        if !changed {
            return original;
        }
        if is_forall {
            terms.mk_forall_with_triggers(vars, new_body, new_triggers)
        } else {
            terms.mk_exists_with_triggers(vars, new_body, new_triggers)
        }
    }
}
