// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

/// The GPU path must honor the CPU path's ELIM_OCC_LIMIT policy cap.
#[cfg(feature = "gpu")]
#[test]
fn test_gpu_bve_dispatch_enforces_occ_limit() {
    let mut solver = Solver::new(4000);
    let x0 = Variable(0);

    let mut pos = Vec::new();
    let mut neg = Vec::new();
    for i in 0..1100u32 {
        pos.push(solver.arena.add(
            &[Literal::positive(x0), Literal::positive(Variable(1 + i))],
            false,
        ));
        neg.push(solver.arena.add(
            &[Literal::negative(x0), Literal::negative(Variable(1 + i))],
            false,
        ));
    }

    // 2200 live occurrences > ELIM_OCC_LIMIT (2000): rejected before any
    // GPU work, regardless of adapter availability.
    let result = solver.gpu_bve_resolve_and_check(x0, &pos, &neg, u64::MAX);
    let (can_eliminate, resolvents, _, _, attempts) =
        result.expect("occ-limit rejection must not require a GPU");
    assert!(!can_eliminate, "occ-limit must reject like the CPU path");
    assert!(resolvents.is_empty());
    assert_eq!(attempts, 0);
}
