// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// #cold-core-descent D3: the minimum-sample brake must not be satisfiable
/// by BATCHED core payments.
///
/// `pay_mined_cores` and the AM1 probe's failed-selector loop call
/// `process_core` back-to-back over an already-computed list, so 8
/// "intervals" can be recorded in microseconds without a single SAT call —
/// handing the gate a "this instance was streaming cores" baseline built
/// entirely out of bookkeeping, and satisfying `COLD_CORE_MIN_SAMPLE` on an
/// instance that has searched for nothing.
#[test]
fn cold_core_rate_sample_ignores_batched_core_payments() -> Result<(), &'static str> {
    let mk = || {
        let mut soft_store = ClauseStore::new();
        for i in 1..=24i32 {
            soft_store.push_from_iter([i].iter().map(|&l| Literal::from(l)));
        }
        let mut engine = OllEngine::new(32, ClauseStore::new(), soft_store, vec![1; 24]);
        for i in 1..=24i32 {
            engine.active.insert(Literal::from(i), 1);
        }
        engine.level = 1;
        engine
    };

    // 12 batch payments, back-to-back, exactly as the batch sites do.
    let mut batched = mk();
    for i in 1..=12i32 {
        batched.process_core(&[Literal::from(i)], CoreOrigin::Batch);
    }
    assert_eq!(batched.stats.cores_found, 12, "batch cores still count");
    assert_eq!(batched.core_search_cores, 0);
    assert!(
        batched.core_gaps_ms.is_empty(),
        "batched payments must contribute no rate intervals",
    );
    assert!(
        !batched.core_discovery_cold(checked_test_instant_sub(
            Instant::now(),
            Duration::from_mins(10),
        )?),
        "the minimum-sample brake must not be satisfiable by bookkeeping",
    );

    // The same 12 cores arriving from search DO set the baseline.
    let mut searched = mk();
    for i in 1..=12i32 {
        searched.process_core(&[Literal::from(i)], CoreOrigin::Search);
    }
    assert_eq!(searched.core_search_cores, 12);
    assert_eq!(
        searched.core_gaps_ms.len(),
        11,
        "n search cores give n-1 intervals",
    );
    Ok(())
}
