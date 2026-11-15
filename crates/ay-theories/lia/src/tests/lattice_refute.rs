// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lattice-closure refutation through the full `LiaSolver::check()` path
//! (LIA_mod_completeness_2026-09-25). Before the fix these systems made
//! branch-and-bound diverge along an unbounded direction.

use super::*;

fn int(terms: &mut TermStore, v: i64) -> TermId {
    terms.mk_int(BigInt::from(v))
}

/// s_split_12's parity leaf with `(mod B 2)` eliminated to `B = 2q + r`,
/// `0 <= r < 2`: `B - A - C = 0`, `A <= C + 1`, `A <= B`, `C <= A`,
/// `C + 1 > A`, plus `r = residue`.
fn parity_leaf(terms: &mut TermStore, residue: i64) -> Vec<(TermId, bool)> {
    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let c = terms.mk_var("C", Sort::Int);
    let q = terms.mk_var("q", Sort::Int);
    let r = terms.mk_var("r", Sort::Int);
    let (zero, one, two) = (int(terms, 0), int(terms, 1), int(terms, 2));
    let neg_a = terms.mk_neg(a);
    let neg_c = terms.mk_neg(c);
    let body_sum = terms.mk_add(vec![b, neg_a, neg_c]);
    let c_plus_1 = terms.mk_add(vec![c, one]);
    let two_q = terms.mk_mul(vec![two, q]);
    let two_q_r = terms.mk_add(vec![two_q, r]);
    let residue_term = int(terms, residue);
    vec![
        (terms.mk_eq(body_sum, zero), true),
        (terms.mk_le(a, c_plus_1), true),
        (terms.mk_le(a, b), true),
        (terms.mk_le(c, a), true),
        (terms.mk_gt(c_plus_1, a), true),
        (terms.mk_eq(b, two_q_r), true),
        (terms.mk_le(zero, r), true),
        (terms.mk_lt(r, two), true),
        (terms.mk_eq(r, residue_term), true),
    ]
}

#[test]
fn odd_parity_leaf_is_unsat_and_core_is_sound() {
    let mut terms = TermStore::new();
    let lits = parity_leaf(&mut terms, 1);
    let mut solver = LiaSolver::new(&terms);
    for &(t, v) in &lits {
        solver.assert_literal(t, v);
    }
    let result = solver.check();
    let conflict = assert_conflict_soundness(result, LiaSolver::new(&terms));
    for lit in &conflict {
        assert!(
            lits.contains(&(lit.term, lit.value)),
            "conflict literal {lit:?} not asserted"
        );
    }
    // `A <= C + 1` and `A <= B` are redundant for the refutation.
    assert!(!conflict
        .iter()
        .any(|l| l.term == lits[1].0 || l.term == lits[2].0));
}

#[test]
fn odd_parity_leaf_with_residue_disequality_is_refuted() {
    // The form `(not (= (mod B 2) 0))` takes after mod elimination: `r != 0`.
    // `check()` first asks for the disequality split when the LRA model is
    // integral; the closure itself refutes the unsplit form.
    let mut terms = TermStore::new();
    let mut lits = parity_leaf(&mut terms, 0);
    let last = lits.len() - 1;
    lits[last].1 = false;
    let q = terms.mk_var("q", Sort::Int);
    let mut solver = LiaSolver::new(&terms);
    for &(t, v) in &lits {
        solver.assert_literal(t, v);
    }
    let conflict = solver
        .lattice_refutation_before_split(q)
        .expect("lattice closure refutes the r != 0 leaf");
    let mut got: Vec<(TermId, bool)> = conflict.iter().map(|l| (l.term, l.value)).collect();
    got.sort_unstable();
    // B - A - C = 0, C <= A, C + 1 > A, B = 2q + r, 0 <= r, r < 2, r != 0.
    let mut want: Vec<(TermId, bool)> = [0, 3, 4, 5, 6, 7, 8].iter().map(|&i| lits[i]).collect();
    want.sort_unstable();
    assert_eq!(got, want);
}

#[test]
fn even_parity_leaf_is_not_refuted() {
    // Same body with B even: A = C = q, B = 2q is a solution.
    let mut terms = TermStore::new();
    let lits = parity_leaf(&mut terms, 0);
    let mut solver = LiaSolver::new(&terms);
    for &(t, v) in &lits {
        solver.assert_literal(t, v);
    }
    let result = solver.check();
    assert!(
        !matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ),
        "satisfiable parity leaf refuted: {result:?}"
    );
}

#[test]
fn chain_equalities_with_mod_three_is_unsat() {
    // A <= B, B <= C, C <= A, A + B + C = 3q + 1: all equal, so 3A = 3q + 1.
    let mut terms = TermStore::new();
    let a = terms.mk_var("A", Sort::Int);
    let b = terms.mk_var("B", Sort::Int);
    let c = terms.mk_var("C", Sort::Int);
    let q = terms.mk_var("q", Sort::Int);
    let (one, three) = (int(&mut terms, 1), int(&mut terms, 3));
    let sum = terms.mk_add(vec![a, b, c]);
    let three_q = terms.mk_mul(vec![three, q]);
    let rhs = terms.mk_add(vec![three_q, one]);
    let lits = [
        terms.mk_le(a, b),
        terms.mk_le(b, c),
        terms.mk_le(c, a),
        terms.mk_eq(sum, rhs),
    ];
    let mut solver = LiaSolver::new(&terms);
    for &t in &lits {
        solver.assert_literal(t, true);
    }
    let conflict = assert_conflict_soundness(solver.check(), LiaSolver::new(&terms));
    assert_eq!(conflict.len(), 4);
}

/// One generated atom `Σ coeffs·x  op  constant` and its asserted polarity.
struct GenAtom {
    term: TermId,
    op: &'static str,
    coeffs: Vec<i64>,
    constant: i64,
    value: bool,
}

fn holds(atom: &GenAtom, point: &[i64]) -> bool {
    let lhs: i64 = atom.coeffs.iter().zip(point).map(|(c, x)| c * x).sum();
    let truth = match atom.op {
        "<=" => lhs <= atom.constant,
        "<" => lhs < atom.constant,
        ">=" => lhs >= atom.constant,
        ">" => lhs > atom.constant,
        _ => lhs == atom.constant,
    };
    truth == atom.value
}

/// SOUNDNESS sweep through the bridge: random Int atoms of every operator and
/// polarity (the translation of strict/negated atoms and disequalities is
/// what this exercises). A returned conflict must have no integer solution;
/// checked by enumeration on a box larger than every atom's constants.
#[test]
fn bridge_conflicts_are_semantically_unsat() {
    const OPS: [&str; 5] = ["<=", "<", ">=", ">", "="];
    let mut state: u64 = 0x2545_f491_4f6c_dd1d;
    let mut next = |lo: i64, hi: i64| {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        lo + (state % ((hi - lo + 1) as u64)) as i64
    };
    let mut refuted = 0;
    for _case in 0..1500 {
        let mut terms = TermStore::new();
        let nvars = next(1, 3) as usize;
        let vars: Vec<TermId> = (0..nvars)
            .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
            .collect();
        let mut atoms = Vec::new();
        for _ in 0..next(2, 6) {
            let coeffs: Vec<i64> = (0..nvars).map(|_| next(-3, 3)).collect();
            let constant = next(-4, 4);
            let mut parts = Vec::new();
            for (v, c) in vars.iter().zip(&coeffs) {
                if *c != 0 {
                    let k = terms.mk_int(BigInt::from(*c));
                    parts.push(terms.mk_mul(vec![k, *v]));
                }
            }
            if parts.is_empty() {
                continue;
            }
            let lhs = if parts.len() == 1 {
                parts[0]
            } else {
                terms.mk_add(parts)
            };
            let rhs = terms.mk_int(BigInt::from(constant));
            let op = OPS[next(0, 4) as usize];
            let term = match op {
                "<=" => terms.mk_le(lhs, rhs),
                "<" => terms.mk_lt(lhs, rhs),
                ">=" => terms.mk_ge(lhs, rhs),
                ">" => terms.mk_gt(lhs, rhs),
                _ => terms.mk_eq(lhs, rhs),
            };
            let value = next(0, 2) != 0;
            atoms.push(GenAtom {
                term,
                op,
                coeffs,
                constant,
                value,
            });
        }
        let mut solver = LiaSolver::new(&terms);
        for atom in &atoms {
            solver.assert_literal(atom.term, atom.value);
        }
        let Some(conflict) = solver.lattice_refutation_before_split(vars[0]) else {
            continue;
        };
        refuted += 1;
        let in_conflict: Vec<&GenAtom> = conflict
            .iter()
            .map(|lit| {
                atoms
                    .iter()
                    .find(|a| a.term == lit.term && a.value == lit.value)
                    .expect("conflict literal was asserted")
            })
            .collect();
        let radius = 12i64;
        let width = (2 * radius + 1) as usize;
        for mut code in 0..width.pow(nvars as u32) {
            let point: Vec<i64> = (0..nvars)
                .map(|_| {
                    let d = (code % width) as i64 - radius;
                    code /= width;
                    d
                })
                .collect();
            assert!(
                !in_conflict.iter().all(|a| holds(a, &point)),
                "conflict satisfied at {point:?}"
            );
        }
    }
    assert!(refuted > 100, "only {refuted} refutations in the sweep");
}
