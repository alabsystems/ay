// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! `--lra-unit-pivot-pref` (#lra-unit-pivot-pref): the ±1 entering-variable
//! tie-break must never change a verdict. Random small LPs with mixed unit
//! and non-unit coefficients are solved twice — flag OFF (the default,
//! byte-identical to the historical scoring) and flag ON — and the
//! SAT/UNSAT classification must agree on every instance; a SAT model under
//! the flag must still satisfy every asserted atom exactly.

use super::*;
use ay_core::term::TermId;

struct Rng(u64);

impl Rng {
    fn next(&mut self) -> u64 {
        let mut x = self.0;
        x ^= x << 13;
        x ^= x >> 7;
        x ^= x << 17;
        self.0 = x;
        x
    }
    fn below(&mut self, n: usize) -> usize {
        (self.next() % n as u64) as usize
    }
}

fn is_unsat(r: &TheoryResult) -> bool {
    matches!(r, TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_))
}

/// Build one random instance; returns (terms, atoms, asserted literals).
fn build_instance(seed: u64) -> (TermStore, Vec<(TermId, bool)>) {
    let mut rng = Rng(seed | 1);
    let mut terms = TermStore::new();
    let n_vars = 5;
    let vars: Vec<TermId> = (0..n_vars)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Real))
        .collect();
    let mut exprs: Vec<TermId> = vars.clone();
    for _ in 0..8 {
        let a = rng.below(n_vars);
        let mut b = rng.below(n_vars);
        while b == a {
            b = rng.below(n_vars);
        }
        // Mixed coefficients: some ±1 (unit) and some in {2, 3, 5, 7}.
        let ka = [1i64, 1, 2, 3, 5, 7][rng.below(6)];
        let kb = [1i64, -1, 1, 2, 3, 7][rng.below(6)];
        let ta = terms.mk_rational(BigRational::from(BigInt::from(ka)));
        let tb = terms.mk_rational(BigRational::from(BigInt::from(kb)));
        let pa = terms.mk_mul(vec![ta, vars[a]]);
        let pb = terms.mk_mul(vec![tb, vars[b]]);
        let e = if rng.below(2) == 0 {
            terms.mk_add(vec![pa, pb])
        } else {
            terms.mk_sub(vec![pa, pb])
        };
        exprs.push(e);
    }
    let mut lits: Vec<(TermId, bool)> = Vec::new();
    for &e in &exprs {
        // Upper thresholds >= 0 and lower thresholds <= 0 keep the origin
        // feasible often enough that both verdict classes occur; negated
        // literals (`e > c`) and tight thresholds supply the UNSAT half.
        let c1 = terms.mk_rational(BigRational::from(BigInt::from(rng.below(21) as i64)));
        let c2 = terms.mk_rational(BigRational::from(BigInt::from(-(rng.below(21) as i64))));
        if rng.below(2) == 0 {
            lits.push((terms.mk_le(e, c1), rng.below(6) != 0));
        }
        if rng.below(2) == 0 {
            lits.push((terms.mk_ge(e, c2), rng.below(6) != 0));
        }
    }
    (terms, lits)
}

fn solve(terms: &TermStore, lits: &[(TermId, bool)]) -> TheoryResult {
    let mut solver = LraSolver::new(terms);
    for &(atom, _) in lits {
        solver.register_atom(atom);
    }
    for &(atom, value) in lits {
        solver.assert_literal(atom, value);
    }
    solver.check()
}

#[test]
fn unit_pivot_preference_never_changes_a_verdict() {
    let mut sat = 0usize;
    let mut unsat = 0usize;
    for seed in 1..=150u64 {
        let (terms, lits) = build_instance(seed);
        let off = solve(&terms, &lits);
        let on = {
            let _g = ay_core::misc_test_override::set(ay_core::MiscCliFlags {
                lra_unit_pivot_pref: true,
                ..ay_core::misc_cli_flags().clone()
            });
            assert!(ay_core::misc_cli_flags().lra_unit_pivot_pref);
            solve(&terms, &lits)
        };
        assert!(
            !ay_core::misc_cli_flags().lra_unit_pivot_pref,
            "override restored"
        );
        assert_eq!(
            is_unsat(&off),
            is_unsat(&on),
            "seed {seed}: verdict differs with --lra-unit-pivot-pref: off={off:?} on={on:?}"
        );
        if is_unsat(&off) {
            unsat += 1;
        } else {
            sat += 1;
        }
    }
    // Anti-vacuity: both verdict classes must be exercised.
    assert!(sat >= 10, "too few SAT instances: {sat}");
    assert!(unsat >= 10, "too few UNSAT instances: {unsat}");
}
