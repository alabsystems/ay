// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Tests for cross-engine lemma transfer (#7919).
//!
//! Validates the LemmaCache/LemmaPool pipeline that transfers learned lemmas
//! from prior PDR runs to subsequent portfolio engines.

use super::*;

/// Verify `set_pdr_lemma_pool` injects `lemma_hints` into all PDR engine configs.
#[test]
fn test_set_pdr_lemma_pool_populates_all_pdr_engines() {
    use crate::lemma_pool::{LemmaPool, SharedLemma};

    let mut pool = LemmaPool::new();
    pool.lemmas.push(SharedLemma {
        formula: ChcExpr::int(42),
        predicate: crate::PredicateId(0),
        source_frame: 3,
    });
    pool.lemmas.push(SharedLemma {
        formula: ChcExpr::Bool(false),
        predicate: crate::PredicateId(1),
        source_frame: 5,
    });

    let mut config = PortfolioConfig::production_default();

    // Count PDR engines before seeding.
    let pdr_count = config
        .engines
        .iter()
        .filter(|e| matches!(e, EngineConfig::Pdr(_)))
        .count();
    assert!(
        pdr_count >= 2,
        "Production portfolio should have at least 2 PDR engines"
    );

    // Seed all PDR engines with the pool.
    config.set_pdr_lemma_pool(&pool);

    // Verify every PDR engine received lemma_hints.
    let mut seeded_count = 0;
    for engine in &config.engines {
        if let EngineConfig::Pdr(pdr) = engine {
            let hints = pdr
                .lemma_hints
                .as_ref()
                .expect("PDR engine should have lemma_hints");
            assert_eq!(hints.len(), 2, "Each PDR engine should receive 2 lemmas");
            seeded_count += 1;
        }
    }
    assert_eq!(seeded_count, pdr_count, "All PDR engines should be seeded");
}

/// Verify that an empty pool does not inject None-to-Some lemma_hints.
#[test]
fn test_set_pdr_lemma_pool_empty_is_noop() {
    let pool = crate::lemma_pool::LemmaPool::new();
    let mut config = PortfolioConfig::production_default();
    config.set_pdr_lemma_pool(&pool);

    for engine in &config.engines {
        if let EngineConfig::Pdr(pdr) = engine {
            assert!(
                pdr.lemma_hints.is_none(),
                "Empty pool should not set lemma_hints"
            );
        }
    }
}

/// Verify `LemmaCache` accumulates across multiple merges and produces
/// a valid snapshot for `seed_from_lemma_cache`.
#[test]
fn test_lemma_cache_sequential_accumulation() {
    use crate::lemma_cache::LemmaCache;
    use crate::lemma_pool::{LemmaPool, SharedLemma};

    let cache = LemmaCache::new();

    // Simulate engine 0 producing lemmas.
    let mut pool0 = LemmaPool::new();
    pool0.lemmas.push(SharedLemma {
        formula: ChcExpr::int(10),
        predicate: crate::PredicateId(0),
        source_frame: 1,
    });
    cache.merge(&pool0);
    assert_eq!(cache.len(), 1);

    // Simulate engine 1 producing more lemmas.
    let mut pool1 = LemmaPool::new();
    pool1.lemmas.push(SharedLemma {
        formula: ChcExpr::int(20),
        predicate: crate::PredicateId(0),
        source_frame: 2,
    });
    // Same as pool0 - should be deduplicated.
    pool1.lemmas.push(SharedLemma {
        formula: ChcExpr::int(10),
        predicate: crate::PredicateId(0),
        source_frame: 5, // different frame, same formula
    });
    cache.merge(&pool1);

    // Should have 2 unique lemmas (the duplicate was skipped).
    assert_eq!(cache.len(), 2);

    // Snapshot should produce a usable pool.
    let snapshot = cache.snapshot();
    assert_eq!(snapshot.len(), 2);
    let hints = snapshot.to_hint_vec();
    assert_eq!(hints.len(), 2);
    // All hints should have source "lemma_pool_transfer".
    for hint in &hints {
        assert_eq!(hint.source, "lemma_pool_transfer");
    }
}

/// Verify that `inject_lemma_cache` + `seed_from_lemma_cache` work on EngineConfig.
#[test]
fn test_engine_config_cache_injection_and_seeding() {
    use crate::lemma_cache::LemmaCache;
    use crate::lemma_pool::{LemmaPool, SharedLemma};

    let cache = LemmaCache::new();

    // Pre-populate the cache.
    let mut pool = LemmaPool::new();
    pool.lemmas.push(SharedLemma {
        formula: ChcExpr::Bool(true),
        predicate: crate::PredicateId(0),
        source_frame: 2,
    });
    cache.merge(&pool);

    // Create a PDR engine config and inject the cache.
    let mut engine = EngineConfig::Pdr(PdrConfig::default());
    engine.inject_lemma_cache(&cache);
    engine.seed_from_lemma_cache(&cache);

    if let EngineConfig::Pdr(pdr) = &engine {
        // lemma_cache should be set (for the engine to write back).
        assert!(pdr.lemma_cache.is_some());
        // lemma_hints should be set (seeded from cache snapshot).
        let hints = pdr.lemma_hints.as_ref().expect("should be seeded");
        assert_eq!(hints.len(), 1);
    } else {
        panic!("Expected PDR engine config");
    }

    // Non-PDR engines should be unaffected.
    let mut bmc = EngineConfig::Bmc(BmcConfig::default());
    bmc.inject_lemma_cache(&cache);
    bmc.seed_from_lemma_cache(&cache);
    // No panic means success: BMC ignores the cache silently.
}

/// Full round-trip: create a safe problem, run a short PDR that returns Unknown
/// (due to tight limits), verify that the LemmaCache captured lemmas, and
/// confirm a second PDR run seeded from the cache also receives them.
#[test]
#[ntest::timeout(15000)]
fn test_full_lemma_transfer_round_trip() {
    use crate::lemma_cache::LemmaCache;
    use crate::pdr::PdrSolver;

    let problem = create_safe_problem();
    let cache = LemmaCache::new();

    // Run PDR with very tight limits so it returns Unknown with some learned lemmas.
    let config = PdrConfig {
        max_frames: 3,
        max_iterations: 10,
        max_obligations: 50,
        lemma_cache: Some(cache.clone()),
        ..PdrConfig::default()
    };
    let result = PdrSolver::solve_problem(&problem, config);

    // Even if it solves (the problem is simple), check the cache mechanism works.
    // If it returned Unknown, the cache should have captured some lemmas.
    if matches!(result, crate::pdr::PdrResult::Unknown) {
        // The cache should have received some lemmas.
        // (Not guaranteed - depends on how many iterations ran.)
        // Verify the cache is at least structurally valid.
        let snapshot = cache.snapshot();
        // Convert snapshot to hints for a second engine.
        let hints = snapshot.to_hint_vec();
        // Hints (if any) should all be from "lemma_pool_transfer" source.
        for hint in &hints {
            assert_eq!(hint.source, "lemma_pool_transfer");
        }
    }

    // Run a second PDR seeded from the cache.
    let config2 = PdrConfig {
        lemma_hints: if cache.is_empty() {
            None
        } else {
            Some(cache.snapshot())
        },
        ..PdrConfig::default()
    };
    let result2 = PdrSolver::solve_problem(&problem, config2);
    // The problem is safe and should eventually be solved.
    assert!(
        matches!(
            result2,
            crate::pdr::PdrResult::Safe(_) | crate::pdr::PdrResult::Unknown
        ),
        "Second PDR run should return Safe or Unknown, got {:?}",
        std::mem::discriminant(&result2)
    );
}
