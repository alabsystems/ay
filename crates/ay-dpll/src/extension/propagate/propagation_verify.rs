// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Semantic verification policy for eager propagations.
//!
//! Structural checks always run for materialized propagations in the delivery
//! lane. Direct lazy deliveries carry an opaque theory-owned reason token and
//! do not enter this policy until they are materialized. Semantic checks retain
//! the established size budget, warmups, sampling cadence, and trust-true-only
//! memo discipline. Rejections are never memoized.

use ay_core::{TermStore, TheoryPropagation, TheoryResult, TheorySolver};

use super::*;
use crate::verification::{
    classify_propagation_domain, verify_memo_armed, verify_propagation_semantic,
    verify_theory_propagation, TheoryDomain,
};

enum VerificationVerdict {
    Accepted,
    Rejected,
    NeedsFreshCheck,
}

struct VerificationPlan {
    domain: TheoryDomain,
    memo_key: Option<Vec<(u32, bool)>>,
    memo_hit: bool,
}

impl<'a, T: TheorySolver> TheoryExtension<'a, T> {
    pub(super) fn propagation_is_semantically_valid(
        &mut self,
        propagation: &TheoryPropagation,
    ) -> bool {
        const TERM_LIMIT: usize = 50_000;
        let Some(terms) = self.terms else {
            return true;
        };
        if terms.len() > TERM_LIMIT {
            tracing::debug!(
                term_count = terms.len(),
                limit = TERM_LIMIT,
                "semantic propagation verification skipped: term count exceeds budget (#8558)"
            );
            return true;
        }
        if self.semantic_verify_interval == 0 {
            self.semantic_verify_interval = if self.theory_atoms.len() > 1000 {
                64
            } else {
                1
            };
        }
        self.semantic_verify_sample_counter += 1;
        let selected = self.semantic_verify_interval <= 1
            || self
                .semantic_verify_sample_counter
                .is_multiple_of(u64::from(self.semantic_verify_interval));
        if !selected {
            return true;
        }
        ay_lia::instrument::bump_verify_prop_selected();
        self.verify_selected_propagation(propagation, terms)
    }

    fn verify_selected_propagation(
        &mut self,
        propagation: &TheoryPropagation,
        terms: &'a TermStore,
    ) -> bool {
        let plan = self.verification_plan(propagation, terms);
        let verdict = if plan.memo_hit {
            VerificationVerdict::Accepted
        } else {
            match plan.domain {
                TheoryDomain::Unknown => self.verify_mixed_propagation(propagation, terms),
                TheoryDomain::Array => self.verify_array_propagation(propagation, terms),
                TheoryDomain::Euf => self.verify_euf_propagation(propagation, terms),
                _ => VerificationVerdict::NeedsFreshCheck,
            }
        };
        let accepted = match verdict {
            VerificationVerdict::Accepted => true,
            VerificationVerdict::Rejected => {
                self.log_cached_verification_rejection(propagation);
                false
            }
            VerificationVerdict::NeedsFreshCheck => {
                ay_lia::instrument::bump_verify_prop_fresh_full();
                self.verify_fresh_propagation(propagation, terms)
            }
        };
        if accepted && !plan.memo_hit {
            self.memoize_verified_propagation(plan.memo_key);
        }
        accepted
    }

    fn verification_plan(
        &self,
        propagation: &TheoryPropagation,
        terms: &TermStore,
    ) -> VerificationPlan {
        let domain = classify_propagation_domain(terms, propagation);
        let memo_key = (verify_memo_armed()
            && self.verify_prop_memo.is_some()
            && matches!(
                domain,
                TheoryDomain::Unknown
                    | TheoryDomain::Arithmetic
                    | TheoryDomain::BitVec
                    | TheoryDomain::String
            ))
        .then(|| propagation_key(propagation));
        let memo_hit = match (&memo_key, self.verify_prop_memo.as_deref()) {
            (Some(key), Some(memo)) => memo.get(key) == Some(&true),
            _ => false,
        };
        if memo_key.is_some() {
            ay_lia::instrument::bump_verify_prop_memo(memo_hit);
        }
        VerificationPlan {
            domain,
            memo_key,
            memo_hit,
        }
    }

    fn verify_mixed_propagation(
        &mut self,
        propagation: &TheoryPropagation,
        terms: &'a TermStore,
    ) -> VerificationVerdict {
        ay_lia::instrument::bump_verify_prop_mixed_full();
        let cache = self.verify_mixed_cache.get_or_insert_with(|| {
            let all_terms = propagation
                .reason
                .iter()
                .map(|literal| literal.term)
                .chain(std::iter::once(propagation.literal.term));
            crate::verification::make_verification_combiner(terms, all_terms)
        });
        cache.push();
        for literal in &propagation.reason {
            cache.register_atom(literal.term);
        }
        cache.register_atom(propagation.literal.term);
        for literal in &propagation.reason {
            cache.assert_literal(literal.term, literal.value);
        }
        cache.assert_literal(propagation.literal.term, !propagation.literal.value);
        let verdict = cache.check();
        cache.pop();
        match verdict {
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                VerificationVerdict::Accepted
            }
            TheoryResult::Sat => VerificationVerdict::Rejected,
            _ => VerificationVerdict::Accepted,
        }
    }

    fn verify_array_propagation(
        &mut self,
        propagation: &TheoryPropagation,
        terms: &TermStore,
    ) -> VerificationVerdict {
        const WARMUP: u64 = 512;
        const MEMO_CAP: usize = 1 << 20;
        let key = propagation_key(propagation);
        if let Some(&allowed) = self.verify_array_memo.get(&key) {
            return verdict_from_bool(allowed);
        }
        self.verify_array_sem_counter += 1;
        let count = self.verify_array_sem_counter;
        if count > WARMUP && !count.is_multiple_of(64) {
            return VerificationVerdict::Accepted;
        }
        let allowed = verify_propagation_semantic(propagation, terms).is_ok();
        if allowed && self.verify_array_memo.len() < MEMO_CAP {
            self.verify_array_memo.insert(key, true);
        }
        verdict_from_bool(allowed)
    }

    fn verify_euf_propagation(
        &mut self,
        propagation: &TheoryPropagation,
        terms: &'a TermStore,
    ) -> VerificationVerdict {
        if verify_theory_propagation(propagation).is_err() {
            return VerificationVerdict::Rejected;
        }
        use std::cell::Cell;
        thread_local!(static EUF_SEM_CTR: Cell<u64> = const { Cell::new(0) });
        const WARMUP: u64 = 512;
        let count = EUF_SEM_CTR.with(|counter| {
            let next = counter.get().wrapping_add(1);
            counter.set(next);
            next
        });
        if count > WARMUP && !count.is_multiple_of(64) {
            return VerificationVerdict::Accepted;
        }
        let cache = self
            .verify_euf_cache
            .get_or_insert_with(|| ay_euf::EufSolver::new(terms).verify_only());
        cache.push();
        for literal in &propagation.reason {
            cache.assert_literal(literal.term, literal.value);
        }
        cache.assert_literal(propagation.literal.term, !propagation.literal.value);
        let verdict = cache.check();
        cache.pop();
        match verdict {
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_) => {
                VerificationVerdict::Accepted
            }
            TheoryResult::Sat => VerificationVerdict::Rejected,
            _ => VerificationVerdict::Accepted,
        }
    }

    fn verify_fresh_propagation(&self, propagation: &TheoryPropagation, terms: &TermStore) -> bool {
        if let Err(error) = verify_propagation_semantic(propagation, terms) {
            tracing::error!(
                error = %error,
                propagated_term = ?propagation.literal.term,
                propagated_value = propagation.literal.value,
                reason_count = propagation.reason.len(),
                "BUG(#6242): propagation semantic verification failed; skipping unsound propagation"
            );
            return false;
        }
        true
    }

    fn log_cached_verification_rejection(&self, propagation: &TheoryPropagation) {
        tracing::error!(
            propagated_term = ?propagation.literal.term,
            propagated_value = propagation.literal.value,
            reason_count = propagation.reason.len(),
            "BUG(#6242): propagation semantic verification failed (cached); skipping unsound propagation"
        );
    }

    fn memoize_verified_propagation(&mut self, key: Option<Vec<(u32, bool)>>) {
        const MEMO_CAP: usize = 1 << 20;
        if let (Some(key), Some(memo)) = (key, self.verify_prop_memo.as_deref_mut()) {
            if memo.len() < MEMO_CAP {
                memo.insert(key, true);
            }
        }
    }
}

fn propagation_key(propagation: &TheoryPropagation) -> Vec<(u32, bool)> {
    let mut key: Vec<_> = propagation
        .reason
        .iter()
        .map(|literal| (literal.term.0, literal.value))
        .collect();
    key.sort_unstable();
    key.push((propagation.literal.term.0, propagation.literal.value));
    key
}

const fn verdict_from_bool(allowed: bool) -> VerificationVerdict {
    if allowed {
        VerificationVerdict::Accepted
    } else {
        VerificationVerdict::Rejected
    }
}
