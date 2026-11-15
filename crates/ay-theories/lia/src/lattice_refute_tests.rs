// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Unit tests for the lattice-closure refutation engine.

use super::*;

fn row(coeffs: &[(usize, i64)], constant: i64, source: usize) -> IntRow {
    IntRow::new(
        coeffs.iter().map(|&(v, c)| (v, BigInt::from(c))).collect(),
        BigInt::from(constant),
        SourceSet::single(source),
    )
}

fn sources(r: &Refutation) -> Vec<usize> {
    match r {
        Refutation::Refuted(s) => s.iter().collect(),
        Refutation::Open => panic!("expected a refutation, got Open"),
    }
}

/// The CHC-COMP s_split_12 parity leaf after mod elimination
/// (A=0, B=1, C=2, q=3, r=4): `B - A - C = 0`, `B = 2q + r`, `A <= C + 1`,
/// `A <= B`, `C <= A`, `0 <= r < 2`, `r >= 1` (the split of `r != 0`), `A < C + 1`.
#[test]
fn parity_leaf_is_refuted_with_exact_core() {
    let eqs = vec![
        row(&[(1, 1), (0, -1), (2, -1)], 0, 0),
        row(&[(1, 1), (3, -2), (4, -1)], 0, 1),
    ];
    let ineqs = vec![
        row(&[(0, 1), (2, -1)], 1, 2), // A - C <= 1
        row(&[(0, 1), (1, -1)], 0, 3), // A - B <= 0
        row(&[(2, 1), (0, -1)], 0, 4), // C - A <= 0
        row(&[(4, -1)], 0, 5),         // -r <= 0
        row(&[(4, 1)], 1, 6),          // r <= 1   (r < 2)
        row(&[(4, -1)], -1, 7),        // -r <= -1 (r >= 1)
        row(&[(0, 1), (2, -1)], 0, 8), // A - C <= 0 (A < C + 1)
    ];
    let r = refute(eqs, ineqs, &Limits::default());
    assert_eq!(sources(&r), vec![0, 1, 4, 6, 7, 8]);
}

#[test]
fn disequality_moves_bounds_inwards() {
    // The same leaf with the residue literal `r != 0` instead of its split
    // `r >= 1`: `0 <= r <= 1 ∧ r != 0` tightens to `r = 1`.
    let eqs = vec![
        row(&[(1, 1), (0, -1), (2, -1)], 0, 0),
        row(&[(1, 1), (3, -2), (4, -1)], 0, 1),
    ];
    let ineqs = vec![
        row(&[(2, 1), (0, -1)], 0, 2), // C - A <= 0
        row(&[(4, -1)], 0, 3),         // -r <= 0
        row(&[(4, 1)], 1, 4),          // r <= 1
        row(&[(0, 1), (2, -1)], 0, 5), // A - C <= 0
    ];
    let diseqs = vec![row(&[(4, 1)], 0, 6)]; // r != 0
    let system = System { eqs, ineqs, diseqs };
    let (r, _) = refute_system(system, &Limits::default());
    assert_eq!(sources(&r), vec![0, 1, 2, 3, 4, 5, 6]);
    // A disequality refutes an implied equality directly: x = y ∧ x != y.
    let system = System {
        eqs: vec![row(&[(0, 1), (1, -1)], 0, 0)],
        ineqs: vec![],
        diseqs: vec![row(&[(0, 2), (1, -2)], 0, 1)],
    };
    assert_eq!(
        sources(&refute_system(system, &Limits::default()).0),
        vec![0, 1]
    );
}

#[test]
fn parity_leaf_even_case_stays_open() {
    // Same body with r = 0 (B even): A = C = q is a solution.
    let eqs = vec![
        row(&[(1, 1), (0, -1), (2, -1)], 0, 0),
        row(&[(1, 1), (3, -2), (4, -1)], 0, 1),
    ];
    let ineqs = vec![
        row(&[(2, 1), (0, -1)], 0, 2),
        row(&[(0, 1), (2, -1)], 0, 3),
        row(&[(4, 1)], 0, 4),
        row(&[(4, -1)], 0, 5),
    ];
    assert_eq!(refute(eqs, ineqs, &Limits::default()), Refutation::Open);
}

#[test]
fn chain_implied_equalities_need_fourier_motzkin() {
    // A <= B <= C <= A and A + B + C = 3q + 1 (A=0, B=1, C=2, q=3).
    let eqs = vec![row(&[(0, 1), (1, 1), (2, 1), (3, -3)], 1, 0)];
    let ineqs = vec![
        row(&[(0, 1), (1, -1)], 0, 1),
        row(&[(1, 1), (2, -1)], 0, 2),
        row(&[(2, 1), (0, -1)], 0, 3),
    ];
    assert_eq!(
        sources(&refute(eqs, ineqs, &Limits::default())),
        vec![0, 1, 2, 3]
    );
}

#[test]
fn equality_gcd_and_euclid_steps() {
    // 6x + 10y = 1: gcd 2 does not divide 1.
    let r = refute(
        vec![row(&[(0, 6), (1, 10)], 1, 0)],
        vec![],
        &Limits::default(),
    );
    assert_eq!(sources(&r), vec![0]);
    // 6x + 10y + 15z = 1 is solvable (gcd 1): no refutation.
    let r = refute(
        vec![row(&[(0, 6), (1, 10), (2, 15)], 1, 0)],
        vec![],
        &Limits::default(),
    );
    assert_eq!(r, Refutation::Open);
    // 3x + 5y = 1 inside the box [0,1]^2 has no solution (Euclid step needed).
    let ineqs = vec![
        row(&[(0, -1)], 0, 1),
        row(&[(0, 1)], 1, 2),
        row(&[(1, -1)], 0, 3),
        row(&[(1, 1)], 1, 4),
    ];
    let r = refute(
        vec![row(&[(0, 3), (1, 5)], 1, 0)],
        ineqs,
        &Limits::default(),
    );
    assert!(matches!(r, Refutation::Refuted(_)));
}

#[test]
fn chvatal_gomory_rounding_refutes_thin_slab() {
    // 1 <= 2x <= 1 has no integer solution.
    let ineqs = vec![row(&[(0, 2)], 1, 0), row(&[(0, -2)], -1, 1)];
    assert_eq!(
        sources(&refute(vec![], ineqs, &Limits::default())),
        vec![0, 1]
    );
}

#[test]
fn resource_caps_answer_open() {
    let limits = Limits {
        max_ineqs: 400,
        max_bits: 256,
        max_work: 0,
    };
    let ineqs = vec![row(&[(0, 2)], 1, 0), row(&[(0, -2)], -1, 1)];
    assert_eq!(refute(vec![], ineqs, &limits), Refutation::Open);
}

/// Deterministic xorshift for the soundness sweep below.
struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        self.0 ^= self.0 << 13;
        self.0 ^= self.0 >> 7;
        self.0 ^= self.0 << 17;
        self.0
    }
    fn range(&mut self, lo: i64, hi: i64) -> i64 {
        lo + (self.next() % ((hi - lo + 1) as u64)) as i64
    }
}

fn value(r: &IntRow, point: &[i64]) -> BigInt {
    r.coeffs
        .iter()
        .map(|(v, c)| c * BigInt::from(point[*v]))
        .sum()
}

fn has_point(system: &System, nvars: usize, radius: i64) -> bool {
    let width = (2 * radius + 1) as usize;
    let total = width.pow(nvars as u32);
    (0..total).any(|mut code| {
        let point: Vec<i64> = (0..nvars)
            .map(|_| {
                let digit = (code % width) as i64 - radius;
                code /= width;
                digit
            })
            .collect();
        system.eqs.iter().all(|r| value(r, &point) == r.constant)
            && system.ineqs.iter().all(|r| value(r, &point) <= r.constant)
            && system.diseqs.iter().all(|r| value(r, &point) != r.constant)
    })
}

/// SOUNDNESS sweep: random boxed systems (the box rows are part of the input,
/// so enumerating the box is the whole solution space). A refutation must
/// never have an integer solution, and its source set must itself be
/// infeasible (it is used verbatim as the conflict clause).
#[test]
fn refutations_are_sound_and_cores_are_infeasible() {
    let mut rng = Rng(0x9e37_79b9_7f4a_7c15);
    let radius = 3;
    let (mut refuted, mut infeasible) = (0, 0);
    for _case in 0..4000 {
        let nvars = rng.range(1, 3) as usize;
        let mut system = System::default();
        let mut next_source = 0;
        let mut fresh = |r: &mut Vec<IntRow>, coeffs: Vec<(usize, i64)>, c: i64| {
            r.push(row(&coeffs, c, next_source));
            next_source += 1;
        };
        for v in 0..nvars {
            fresh(&mut system.ineqs, vec![(v, 1)], radius);
            fresh(&mut system.ineqs, vec![(v, -1)], radius);
        }
        for _ in 0..rng.range(1, 5) {
            let coeffs: Vec<(usize, i64)> = (0..nvars).map(|v| (v, rng.range(-4, 4))).collect();
            let c = rng.range(-6, 6);
            match rng.range(0, 5) {
                0 => fresh(&mut system.eqs, coeffs, c),
                1 => fresh(&mut system.diseqs, coeffs, c),
                _ => fresh(&mut system.ineqs, coeffs, c),
            }
        }
        let feasible = has_point(&system, nvars, radius);
        infeasible += usize::from(!feasible);
        if let (Refutation::Refuted(core), _) = refute_system(system.clone(), &Limits::default()) {
            refuted += 1;
            assert!(!feasible, "unsound refutation: {system:?}");
            let members: Vec<usize> = core.iter().collect();
            let keep = |rows: &[IntRow]| -> Vec<IntRow> {
                rows.iter()
                    .filter(|r| r.sources.iter().all(|s| members.contains(&s)))
                    .cloned()
                    .collect()
            };
            let core_system = System {
                eqs: keep(&system.eqs),
                ineqs: keep(&system.ineqs),
                diseqs: keep(&system.diseqs),
            };
            assert!(
                !has_point(&core_system, nvars, radius + 3),
                "core is satisfiable: core={members:?} system={system:?}"
            );
        }
    }
    // Boxed systems with <= 3 variables are within the procedure's reach almost
    // always; a large gap would mean a broken step, not a lost corner case.
    assert!(
        refuted * 10 >= infeasible * 9,
        "refuted {refuted} of {infeasible} infeasible systems"
    );
}
