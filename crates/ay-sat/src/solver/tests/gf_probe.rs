// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the GF(p) one-hot linear-system probe (`gf_probe.rs`): the
//! SAT-COMP "bare-numeric" family shape in miniature. Detection must fire
//! only on exact instances of the structure (one-hot groups + complete AMO +
//! exactly `d^r - d^(r-1)` forbidden tuples per scope + a linear fit), and
//! every bail-out must be silent — never a verdict.

use super::*;
use std::time::Duration;

/// Builder for synthetic one-hot GF(d) linear-system CNFs.
///
/// Variable layout is deliberately INTERLEAVED across groups
/// (`var(g, v) = v * num_groups + g + 1` in DIMACS), so group variables are
/// never contiguous — this exercises the detector's permutation robustness
/// (value labels must come from rank in sorted order, not var arithmetic).
struct GfBuilder {
    d: usize,
    num_groups: usize,
    clauses: Vec<Vec<i32>>,
}

impl GfBuilder {
    fn new(d: usize, num_groups: usize) -> Self {
        let mut b = Self {
            d,
            num_groups,
            clauses: Vec::new(),
        };
        b.push_one_hot();
        b
    }

    fn var(&self, g: usize, v: usize) -> i32 {
        (v * self.num_groups + g + 1) as i32
    }

    /// ALO (rotated literal order per group) + complete pairwise AMO.
    fn push_one_hot(&mut self) {
        for g in 0..self.num_groups {
            let alo: Vec<i32> = (0..self.d).map(|v| self.var(g, (v + g) % self.d)).collect();
            self.clauses.push(alo);
            for a in 0..self.d {
                for b in a + 1..self.d {
                    self.clauses.push(vec![-self.var(g, a), -self.var(g, b)]);
                }
            }
        }
    }

    /// Encode `Σ coefs[i] * x_{groups[i]} ≡ c (mod d)` by forbidding every
    /// violating tuple as an all-negative clause (literal order rotated per
    /// tuple for permutation robustness).
    fn push_equation(&mut self, groups: &[usize], coefs: &[u8], c: u8) {
        assert_eq!(groups.len(), coefs.len());
        let r = groups.len();
        let total = self.d.pow(r as u32);
        for code in 0..total {
            let mut sum = 0usize;
            let mut rest = code;
            let mut vals = Vec::with_capacity(r);
            for &a in coefs {
                let v = rest % self.d;
                rest /= self.d;
                sum += usize::from(a) * v;
                vals.push(v);
            }
            if sum % self.d == c as usize {
                continue; // allowed tuple
            }
            let mut clause: Vec<i32> = (0..r).map(|i| -self.var(groups[i], vals[i])).collect();
            clause.rotate_left(code % r);
            self.clauses.push(clause);
        }
    }

    fn solver(&self) -> Solver {
        let num_vars = self.num_groups * self.d;
        let mut solver = Solver::new(num_vars);
        for clause in &self.clauses {
            let lits: Vec<Literal> = clause.iter().map(|&l| Literal::from_dimacs(l)).collect();
            assert!(solver.add_clause(lits), "clause {clause:?} rejected");
        }
        solver
    }
}

fn probe(solver: &Solver) -> Option<Vec<bool>> {
    solver.gf_linear_probe(Duration::from_secs(5))
}

/// The 6-unknown / 4-equation GF(3) system with r=4 scopes (the family
/// shape in miniature).
fn small_gf3_system() -> GfBuilder {
    let mut b = GfBuilder::new(3, 6);
    b.push_equation(&[0, 1, 2, 3], &[1, 2, 1, 1], 1);
    b.push_equation(&[1, 2, 4, 5], &[1, 1, 2, 1], 0);
    b.push_equation(&[2, 3, 4, 5], &[1, 2, 2, 1], 2);
    b.push_equation(&[0, 2, 3, 5], &[1, 1, 1, 2], 1);
    b
}

#[test]
fn gf_probe_solves_synthetic_gf3_system() {
    let b = small_gf3_system();
    let solver = b.solver();
    let model = probe(&solver).expect("probe must construct a model");
    // One-hot per group.
    for g in 0..b.num_groups {
        let true_count = (0..b.d)
            .filter(|&v| model[(b.var(g, v) - 1) as usize])
            .count();
        assert_eq!(true_count, 1, "group {g} must be one-hot");
    }
    // Every clause satisfied (independent re-check of the probe's verifier).
    for clause in &b.clauses {
        assert!(
            clause
                .iter()
                .any(|&l| model[(l.unsigned_abs() - 1) as usize] == (l > 0)),
            "clause {clause:?} unsatisfied"
        );
    }
}

#[test]
fn gf_probe_end_to_end_solves_without_search() {
    let mut solver = small_gf3_system().solver();
    let result = solver.solve().into_inner();
    assert!(matches!(result, SatResult::Sat(_)));
    assert_eq!(
        solver.num_conflicts, 0,
        "gf probe SAT must need zero search"
    );
    assert!(
        solver.stats.gf_probe_time_ns > 0,
        "gf probe must have run (gf_probe_time_ns recorded)"
    );
}

#[test]
fn gf_probe_bails_on_missing_tuple() {
    // 53 of 54 forbidden tuples in one scope: the exact-count predicate
    // must bail (the removed clause makes the scope non-equational).
    let mut b = GfBuilder::new(3, 4);
    b.push_equation(&[0, 1, 2, 3], &[1, 2, 1, 1], 1);
    let removed = b.clauses.pop().expect("builder emitted tuple clauses");
    assert_eq!(removed.len(), 4, "popped clause must be a tuple clause");
    assert_eq!(probe(&b.solver()), None, "53-tuple scope must bail");
}

#[test]
fn gf_probe_bails_on_nonlinear_tuple_set() {
    // Keep the 54-tuple count exact but swap one forbidden tuple for an
    // allowed one: no linear equation fits the resulting set — the fit
    // verification against all allowed tuples must fail.
    let mut b = GfBuilder::new(3, 4);
    b.push_equation(&[0, 1, 2, 3], &[1, 2, 1, 1], 1);
    let removed = b.clauses.pop().expect("builder emitted tuple clauses");
    assert_eq!(removed.len(), 4);
    // (0,0,0,1) satisfies 1*0+2*0+1*0+1*1 = 1 ≡ c=1: an allowed tuple.
    let allowed = vec![-b.var(0, 0), -b.var(1, 0), -b.var(2, 0), -b.var(3, 1)];
    assert!(!b.clauses.contains(&allowed));
    b.clauses.push(allowed);
    assert_eq!(probe(&b.solver()), None, "non-linear tuple set must bail");
}

#[test]
fn gf_probe_bails_on_nonprime_domain() {
    // d = 4 is not prime: GF(4) is not Z/4Z, so modular elimination is
    // unsound — the primality predicate must bail even on a perfectly
    // linear-looking mod-4 instance.
    let mut b = GfBuilder::new(4, 2);
    b.push_equation(&[0, 1], &[1, 1], 0);
    assert_eq!(probe(&b.solver()), None, "non-prime domain must bail");
}

#[test]
fn gf_probe_bails_on_inconsistent_system_without_verdict() {
    // x0+x1 ≡ 0, x1+x2 ≡ 0, x0+2*x2 ≡ 1 (mod 3): substitution gives
    // -3*x1 ≡ 0 ≢ 1 — inconsistent. The probe must bail with NO verdict
    // (detection could have mis-fit); CDCL still proves the CNF UNSAT.
    let mut b = GfBuilder::new(3, 3);
    b.push_equation(&[0, 1], &[1, 1], 0);
    b.push_equation(&[1, 2], &[1, 1], 0);
    b.push_equation(&[0, 2], &[1, 2], 1);
    let mut solver = b.solver();
    assert_eq!(probe(&solver), None, "inconsistent system must bail");
    assert!(
        matches!(solver.solve().into_inner(), SatResult::Unsat(_)),
        "the encoded inconsistent system is UNSAT via normal search"
    );
}

#[test]
fn gf_probe_bails_on_mixed_polarity_clause() {
    let mut b = small_gf3_system();
    b.clauses.push(vec![b.var(0, 0), -b.var(1, 0)]);
    assert_eq!(probe(&b.solver()), None, "mixed polarity must bail");
}

#[test]
fn gf_probe_bails_on_incomplete_amo() {
    let mut b = small_gf3_system();
    let amo_pos = b
        .clauses
        .iter()
        .position(|c| c.len() == 2 && c.iter().all(|&l| l < 0))
        .expect("builder emitted AMO binaries");
    b.clauses.remove(amo_pos);
    assert_eq!(probe(&b.solver()), None, "incomplete AMO must bail");
}

#[test]
fn gf_probe_cli_opt_out_is_honored() {
    let _guard = ay_core::sat_ab_test_override::set(ay_core::SatAbSwitches {
        gf_probe: Some(false),
        ..Default::default()
    });
    let mut solver = small_gf3_system().solver();
    let result = solver.solve().into_inner();
    assert!(
        matches!(result, SatResult::Sat(_)),
        "instance still solves via normal search"
    );
    assert_eq!(
        solver.stats.gf_probe_time_ns, 0,
        "--sat-gf-probe false must keep the probe off"
    );
}

#[test]
fn gf_probe_never_mutates_solver() {
    let solver = small_gf3_system().solver();
    let vals_before = solver.vals.clone();
    let trail_before = solver.trail.clone();
    let decisions_before = solver.num_decisions;
    let props_before = solver.num_propagations;
    let _ = probe(&solver);
    assert_eq!(solver.vals, vals_before);
    assert_eq!(solver.trail, trail_before);
    assert_eq!(solver.num_decisions, decisions_before);
    assert_eq!(solver.num_propagations, props_before);
    assert_eq!(solver.decision_level, 0);
}
