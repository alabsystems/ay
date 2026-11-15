// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;

#[test]
fn real_external_euf_edges_preserve_flat_class_and_default_data() {
    let end = Instant::now() + Duration::from_secs(20);
    let fixture = Fixture::new();
    let mut solver = fixture.solver();
    let _ = solver.assert_external_equality(fixture.bases[0], fixture.bases[1]);
    solver.rebuild_assign_indices();
    let mut values = fixture.values();
    values.insert(fixture.defaults[0], "agreed".into());
    let original = owner(end, 1_000_000, 128 << 20);
    let output = run(&solver, &values, &original);
    same(&output, &solver.extract_model(&values));
    assert_eq!(
        output.array_values[&fixture.bases[0]].default,
        output.array_values[&fixture.bases[1]].default
    );
    assert!(solver.external_eqs.contains(&ArraySolver::ordered_pair(
        fixture.bases[0],
        fixture.bases[1]
    )));
    drop(output);
    original.check().unwrap();
}
