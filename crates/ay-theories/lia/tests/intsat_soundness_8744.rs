// IntSat probe soundness regression (#8744) — LIA/IntSat-level test.
//
// Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//
// Feeds the exact integer constraint system derived from
// benchmarks/smt/QF_LIA/false_unsat_20var_bb.smt2 into the underlying IntSat
// solver (the same solver the LIA bridge invokes) and asserts that IntSat
// does NOT claim UNSAT on this SAT instance. This guards the bridge's
// faithful under-approximation invariant: if the constraint translation is
// sound, IntSat must never claim UNSAT on a genuinely satisfiable system.
//
// See crates/ay-theories/intsat/tests/smoke_8744.rs for the
// minimal IntSat-only reproduction. This file is the LIA-side regression
// test the issue #8744 acceptance criteria required.

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

/// #8744: IntSat must NEVER return Unsat on the full false_unsat_20var_bb
/// constraint system (Z3 confirms SAT in ~0.12s). Unknown is acceptable.
#[test]
fn intsat_never_unsat_on_false_unsat_20var_bb_8744() {
    // Variable mapping (sorted by TermId, as the LIA bridge does):
    //   v0..v18 even-indexed = odd-indexed SMT2 vars (x1, x3, ..., x19)
    //   v1..v19 odd-indexed  = even-indexed SMT2 vars (x2, x4, ..., x20)
    //
    // Odd-group weights:  13*x1 + 7*x3 + 11*x5 + 3*x7 + 17*x9 + 5*x11 +
    //                     19*x13 + 2*x15 + 23*x17 + 29*x19  in [85, 87].
    // Even-group weights: 31*x2 + 37*x4 + 41*x6 + 43*x8 + 47*x10 + 53*x12 +
    //                     59*x14 + 61*x16 + 67*x18 + 71*x20 in [250, 254].
    // Sum of all 20 vars = 10.  All vars in [0, 1].
    let mut constraints = vec![
        // Sum of all 20 vars = 10 (two <= constraints).
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
        // Odd-group in [85, 87]
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
        // Even-group in [250, 254]
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
    // 0/1 bounds as explicit <= constraints (matches what the bridge submits).
    for i in 0..20u32 {
        constraints.push(c(&[(i, 1)], 1));
        constraints.push(c(&[(i, -1)], 0));
    }

    let mut solver = IntSatSolver::new(
        constraints,
        20,
        IntSatConfig {
            max_conflicts: 5_000,
            max_learned: 2_000,
            deadline: None,
        },
    );
    for i in 0..20u32 {
        solver.add_initial_bound(VarId(i), BigInt::from(0), BigInt::from(1));
    }

    let r = solver.solve();
    assert!(
        !matches!(r, IntSatResult::Unsat),
        "IntSat claimed UNSAT on a SAT instance (#8744). Result: {r:?}"
    );
}
