// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn bounded_base_walk_refuses_a_cache_cycle_under_the_same_original_owner() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    solver.store_cache.insert(
        fixture.stores[0],
        (fixture.stores[0], fixture.indices[0], fixture.writes[0]),
    );
    let original = owner(end, 1_000_000, 128 << 20);
    assert!(original
        .with_work(|work| scan::chain(&solver, fixture.stores[0], work))
        .is_err());
    assert!(original.clone().check().is_err());
    assert_eq!(solver.store_cache[&fixture.stores[0]].0, fixture.stores[0]);
}
