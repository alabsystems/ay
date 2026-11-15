// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-engine lemma transfer pool for the adaptive portfolio (#7919).
//!
//! When PDR runs on the non-inlined problem and returns Unknown, it may have
//! discovered useful lemmas that subsequent engines can reuse. `LemmaPool`
//! captures these learned lemmas and injects them as hints into portfolio
//! engines and failure-guided retries.

use crate::{ChcExpr, PredicateId};

/// A lemma learned by one engine that can be shared with others.
#[derive(Debug, Clone)]
pub(crate) struct SharedLemma {
    /// The invariant formula (over canonical predicate variables).
    pub(crate) formula: ChcExpr,
    /// The predicate this lemma constrains.
    pub(crate) predicate: PredicateId,
    /// Frame level where this lemma was learned (higher = more mature).
    pub(crate) source_frame: usize,
}

/// Collection of learned lemmas shared between solver instances.
///
/// Populated by `PdrSolver::export_lemmas()` after a non-inlined PDR
/// stage returns Unknown. Consumed by subsequent portfolio engines and
/// failure-guided retry via conversion to `LemmaHint` entries added
/// to `PdrConfig::user_hints`.
#[derive(Debug, Default, Clone)]
pub(crate) struct LemmaPool {
    pub(crate) lemmas: Vec<SharedLemma>,
}

impl LemmaPool {
    pub(crate) fn new() -> Self {
        Self { lemmas: Vec::new() }
    }

    pub(crate) fn is_empty(&self) -> bool {
        self.lemmas.is_empty()
    }

    pub(crate) fn len(&self) -> usize {
        self.lemmas.len()
    }

    /// `seeds` ahead of `rest` (CH4b): the seeds take the highest priority in
    /// [`Self::to_hint_vec`] (a frame above everything in `rest`), and a
    /// lemma already in `rest` is not duplicated. `None` when both are absent.
    pub(crate) fn seeds_then(seeds: Option<LemmaPool>, rest: Option<&LemmaPool>) -> Option<Self> {
        let top = rest
            .and_then(|pool| pool.lemmas.iter().map(|l| l.source_frame).max())
            .unwrap_or(0)
            .saturating_add(1);
        match (seeds, rest) {
            (None, None) => None,
            (None, Some(rest)) => Some(rest.clone()),
            (Some(seeds), rest) => {
                let mut merged = LemmaPool::new();
                for mut lemma in seeds.lemmas {
                    lemma.source_frame = top;
                    merged.lemmas.push(lemma);
                }
                if let Some(rest) = rest {
                    for lemma in &rest.lemmas {
                        if !merged
                            .lemmas
                            .iter()
                            .any(|l| l.predicate == lemma.predicate && l.formula == lemma.formula)
                        {
                            merged.lemmas.push(lemma.clone());
                        }
                    }
                }
                Some(merged)
            }
        }
    }

    /// Convert to `LemmaHint` entries for injection into `PdrConfig::user_hints`.
    ///
    /// Higher-frame lemmas get lower priority values (higher priority) since
    /// they survived more propagation rounds and are more likely to be useful.
    pub(crate) fn to_hint_vec(&self) -> Vec<crate::lemma_hints::LemmaHint> {
        self.lemmas
            .iter()
            .map(|sl| crate::lemma_hints::LemmaHint {
                predicate: sl.predicate,
                formula: sl.formula.clone(),
                // Lower priority number = higher priority. Frame 10 lemma gets
                // priority 0, frame 0 lemma gets priority 10. Cap at u16::MAX.
                priority: u16::try_from(
                    self.lemmas
                        .iter()
                        .map(|l| l.source_frame)
                        .max()
                        .unwrap_or(0)
                        .saturating_sub(sl.source_frame),
                )
                .unwrap_or(u16::MAX),
                source: "lemma_pool_transfer",
            })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ChcExpr;

    fn pred(id: u32) -> PredicateId {
        PredicateId(id)
    }

    #[test]
    fn seeds_then_puts_seeds_first_with_top_priority_and_dedups() {
        let lemma = |value: i64, frame: usize| SharedLemma {
            formula: ChcExpr::int(value),
            predicate: pred(0),
            source_frame: frame,
        };
        let mut rest = LemmaPool::new();
        rest.lemmas.extend([lemma(1, 4), lemma(2, 1)]);
        let mut seeds = LemmaPool::new();
        seeds.lemmas.extend([lemma(9, 0), lemma(2, 0)]);
        let merged = LemmaPool::seeds_then(Some(seeds), Some(&rest)).expect("merged pool");
        let values: Vec<_> = merged.lemmas.iter().map(|l| l.formula.clone()).collect();
        // seeds first; lemma 2 already seeded, so rest contributes only 1.
        assert_eq!(
            values,
            vec![ChcExpr::int(9), ChcExpr::int(2), ChcExpr::int(1)]
        );
        let hints = merged.to_hint_vec();
        assert_eq!(
            hints[0].priority, 0,
            "a seed outranks every transferred lemma"
        );
        assert_eq!(hints[1].priority, 0);
        assert!(hints[2].priority > 0);
        assert!(LemmaPool::seeds_then(None, None).is_none());
        assert_eq!(
            LemmaPool::seeds_then(None, Some(&rest)).map(|p| p.len()),
            Some(2)
        );
    }

    #[test]
    fn test_empty_pool() {
        let pool = LemmaPool::new();
        assert!(pool.is_empty());
        assert_eq!(pool.len(), 0);
        assert!(pool.to_hint_vec().is_empty());
    }

    #[test]
    fn test_single_lemma_pool() {
        let mut pool = LemmaPool::new();
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::int(42),
            predicate: pred(0),
            source_frame: 3,
        });
        assert!(!pool.is_empty());
        assert_eq!(pool.len(), 1);
        let hints = pool.to_hint_vec();
        assert_eq!(hints.len(), 1);
        assert_eq!(hints[0].predicate, pred(0));
        assert_eq!(hints[0].source, "lemma_pool_transfer");
        assert_eq!(hints[0].priority, 0);
    }

    #[test]
    fn test_priority_ordering() {
        let mut pool = LemmaPool::new();
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::int(1),
            predicate: pred(0),
            source_frame: 5,
        });
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::int(2),
            predicate: pred(0),
            source_frame: 2,
        });
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::int(3),
            predicate: pred(1),
            source_frame: 0,
        });
        let hints = pool.to_hint_vec();
        assert_eq!(hints.len(), 3);
        assert_eq!(hints[0].priority, 0);
        assert_eq!(hints[1].priority, 3);
        assert_eq!(hints[2].priority, 5);
    }

    #[test]
    fn test_multi_predicate_pool() {
        let mut pool = LemmaPool::new();
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::Bool(false),
            predicate: pred(0),
            source_frame: 1,
        });
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::Bool(true),
            predicate: pred(1),
            source_frame: 2,
        });
        pool.lemmas.push(SharedLemma {
            formula: ChcExpr::int(99),
            predicate: pred(2),
            source_frame: 3,
        });
        assert_eq!(pool.len(), 3);
        let hints = pool.to_hint_vec();
        assert_eq!(hints.len(), 3);
        assert_eq!(hints[0].predicate, pred(0));
        assert_eq!(hints[1].predicate, pred(1));
        assert_eq!(hints[2].predicate, pred(2));
    }
}
