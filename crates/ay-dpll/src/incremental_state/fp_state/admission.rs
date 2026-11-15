// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Cooperative full-root reuse admission; cancellation grants no admission.

use ay_core::{Sort, TermId, TermStore};

use super::{FpIncrementalAdmission, HashSet, IncrementalFpState, UnknownOrigin};

type Check<'a> = &'a mut dyn FnMut() -> Result<(), UnknownOrigin>;

impl IncrementalFpState {
    /// Admit only exact full-set reuse, preserving the old defer/re-admit rule.
    /// Call on a moved trial: completed relevance-cache entries are harmless,
    /// but refusal or unwind must not commit partial admission bookkeeping.
    pub(crate) fn observe_live_assertion_reuse_with_control(
        &mut self,
        terms: &TermStore,
        assertions: &[TermId],
        check: Check<'_>,
    ) -> Result<FpIncrementalAdmission, UnknownOrigin> {
        check()?;
        let mut relevant = HashSet::default();
        for &term in assertions {
            check()?;
            if self.term_mentions_fp(terms, term, check)? {
                check()?;
                relevant.insert(term);
            }
        }
        let mut fully_observed = !relevant.is_empty();
        for term in &relevant {
            check()?;
            let known = if self.solves > 0 {
                self.encoded_assertions.contains_key(term)
            } else {
                self.reuse_probe
                    .as_ref()
                    .is_some_and(|prior| prior.contains(term))
            };
            if !known {
                fully_observed = false;
                break;
            }
        }
        check()?;
        let result = if self.solves > 0 {
            if fully_observed {
                FpIncrementalAdmission::Admit
            } else {
                self.reset_sat_encoding_for_rebuild();
                self.reuse_probe = Some(relevant);
                FpIncrementalAdmission::Defer
            }
        } else if fully_observed {
            self.reuse_probe = None;
            FpIncrementalAdmission::Admit
        } else {
            self.reuse_probe = Some(relevant);
            FpIncrementalAdmission::Defer
        };
        check()?;
        Ok(result)
    }

    fn term_mentions_fp(
        &mut self,
        terms: &TermStore,
        root: TermId,
        check: Check<'_>,
    ) -> Result<bool, UnknownOrigin> {
        check()?;
        if let Some(relevant) = self.cached_fp_relevance(root) {
            return Ok(relevant);
        }
        let mut stack = vec![(root, false)];
        while let Some((term, expanded)) = stack.pop() {
            check()?;
            if self.cached_fp_relevance(term).is_some() {
                continue;
            }
            if matches!(terms.sort(term), Sort::FloatingPoint(..)) {
                self.cache_fp_relevance(term, true, check)?;
                continue;
            }
            // children() copies one node's child list; bracket that opaque
            // allocation, then poll each child scan/push below.
            let children = terms.children(term);
            check()?;
            if expanded {
                let mut relevant = false;
                for child in children {
                    check()?;
                    if self.cached_fp_relevance(child) == Some(true) {
                        relevant = true;
                        break;
                    }
                }
                self.cache_fp_relevance(term, relevant, check)?;
            } else {
                stack.push((term, true));
                for child in children {
                    check()?;
                    stack.push((child, false));
                }
            }
        }
        Ok(self.cached_fp_relevance(root) == Some(true))
    }

    fn cached_fp_relevance(&self, term: TermId) -> Option<bool> {
        self.fp_relevance_cache
            .get(term.0 as usize)
            .copied()
            .flatten()
    }

    fn cache_fp_relevance(
        &mut self,
        term: TermId,
        relevant: bool,
        check: Check<'_>,
    ) -> Result<(), UnknownOrigin> {
        check()?;
        let index = term.0 as usize;
        if self.fp_relevance_cache.len() <= index {
            let len = index
                .checked_add(1)
                .ok_or(UnknownOrigin::DeterministicResourceBudget)?;
            self.fp_relevance_cache.resize(len, None);
            check()?;
        }
        self.fp_relevance_cache[index] = Some(relevant);
        Ok(())
    }
}
