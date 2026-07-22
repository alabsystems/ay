// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

// Reproduction of #8744: IntSat probe returns UNSAT on SAT QF_LIA input.
// Benchmark: benchmarks/smt/QF_LIA/false_unsat_20var_bb.smt2

use ay_intsat::{Constraint, IntSatConfig, IntSatResult, IntSatSolver, VarId};
use num_bigint::BigInt;

fn c(coeffs: &[(u32, i64)], rhs: i64) -> Constraint {
    Constraint {
        coeffs: coeffs
            .iter()
            .map(|(v, k)| (VarId(*v), BigInt::from(*k)))
            .collect(),
        rhs: BigInt::from(rhs),
    }
}

#[test]
fn reproduces_issue_8744_false_unsat_20var_bb() {
    // 20 variables v0..v19.
    // v0,v2,...,v18 map to x1,x3,...,x19 (odd group in SMT2, weights 13,7,11,3,17,5,19,2,23,29)
    // v1,v3,...,v19 map to x2,x4,...,x20 (even group, weights 31,37,41,43,47,53,59,61,67,71)
    let mut constraints = vec![
        // Sum = 10 (as two <= constraints).
        c(
            &[
                (0, 1),
                (1, 1),
                (2, 1),
                (3, 1),
                (4, 1),
                (5, 1),
                (6, 1),
                (7, 1),
                (8, 1),
                (9, 1),
                (10, 1),
                (11, 1),
                (12, 1),
                (13, 1),
                (14, 1),
                (15, 1),
                (16, 1),
                (17, 1),
                (18, 1),
                (19, 1),
            ],
            10,
        ),
        c(
            &[
                (0, -1),
                (1, -1),
                (2, -1),
                (3, -1),
                (4, -1),
                (5, -1),
                (6, -1),
                (7, -1),
                (8, -1),
                (9, -1),
                (10, -1),
                (11, -1),
                (12, -1),
                (13, -1),
                (14, -1),
                (15, -1),
                (16, -1),
                (17, -1),
                (18, -1),
                (19, -1),
            ],
            -10,
        ),
        // 85 <= 13*v0 + 7*v2 + 11*v4 + 3*v6 + 17*v8 + 5*v10 + 19*v12 + 2*v14 + 23*v16 + 29*v18 <= 87
        c(
            &[
                (0, 13),
                (2, 7),
                (4, 11),
                (6, 3),
                (8, 17),
                (10, 5),
                (12, 19),
                (14, 2),
                (16, 23),
                (18, 29),
            ],
            87,
        ),
        c(
            &[
                (0, -13),
                (2, -7),
                (4, -11),
                (6, -3),
                (8, -17),
                (10, -5),
                (12, -19),
                (14, -2),
                (16, -23),
                (18, -29),
            ],
            -85,
        ),
        // 250 <= 31*v1 + 37*v3 + 41*v5 + 43*v7 + 47*v9 + 53*v11 + 59*v13 + 61*v15 + 67*v17 + 71*v19 <= 254
        c(
            &[
                (1, 31),
                (3, 37),
                (5, 41),
                (7, 43),
                (9, 47),
                (11, 53),
                (13, 59),
                (15, 61),
                (17, 67),
                (19, 71),
            ],
            254,
        ),
        c(
            &[
                (1, -31),
                (3, -37),
                (5, -41),
                (7, -43),
                (9, -47),
                (11, -53),
                (13, -59),
                (15, -61),
                (17, -67),
                (19, -71),
            ],
            -250,
        ),
    ];
    // Also add the 0/1 bounds as explicit constraints (matches what the bridge submits).
    for i in 0..20u32 {
        constraints.push(c(&[(i, 1)], 1));
        constraints.push(c(&[(i, -1)], 0));
    }

    let mut solver = IntSatSolver::new(
        constraints,
        20,
        IntSatConfig {
            max_conflicts: 5000,
            max_learned: 2000,
            deadline: None,
        },
    );
    for i in 0..20u32 {
        solver.add_initial_bound(VarId(i), BigInt::from(0), BigInt::from(1));
    }

    let r = solver.solve();
    // Must NEVER return Unsat on a SAT instance. Sat or Unknown is acceptable.
    assert!(
        !matches!(r, IntSatResult::Unsat),
        "IntSat claimed UNSAT on a SAT instance (#8744). Result: {r:?}"
    );
}
