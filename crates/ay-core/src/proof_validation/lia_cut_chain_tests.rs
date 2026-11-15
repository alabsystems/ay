// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the Chvátal–Gomory cut-chain certificate.
//!
//! * `certifies_*` pin the corpus lemma it exists for
//!   (`QF_LIA_ring_2exp16_5vars_cascade_unsat` t161, 43 literals) and the
//!   smallest rounding-only refutation;
//! * `refuses_*` corrupt one field of a real witness and expect the exact
//!   validator to reject it (the negative twins of the new acceptance path);
//! * `declines_*` name the integer model, or the fail-closed guard, of every
//!   clause it must not certify;
//! * the sweep checks, over every small bounded two-atom clause it
//!   enumerates, that a certificate never exists when brute force finds an
//!   integer model of the clause's negation.

use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Zero};

use super::lia_cut_chain::validate_cut_chain;
use super::{lia_cut_chain_witness, recognize_int_cg_cut_chain, LiaCutChainWitness};
use crate::term::Symbol;
use crate::{Sort, TermId, TermStore};

fn int(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(BigInt::from(value))
}

/// `(* var coefficient)`, the spelling the cascade lemma carries.
fn times(terms: &mut TermStore, var: TermId, coefficient: i64) -> TermId {
    let coefficient = int(terms, coefficient);
    terms.mk_mul(vec![var, coefficient])
}

fn not(terms: &mut TermStore, atom: TermId) -> TermId {
    terms.mk_not_raw(atom)
}

fn raw(terms: &mut TermStore, op: &str, lhs: TermId, rhs: TermId) -> TermId {
    terms.mk_app(Symbol::named(op), vec![lhs, rhs], Sort::Bool)
}

/// The cascade lemma: five multiples of three in `[40000, 60000]` summed
/// through a 16-bit carry chain whose final sum is `65536·c4 + tail`, with
/// every literal in the solver's own spelling. `tail = 1` is t161 of
/// `QF_LIA_ring_2exp16_5vars_cascade_unsat` (43 literals): `Σ 3m_i =
/// 65536·Σ c_i + 1`, the bounds force `Σ c_i = 4`, and `262145` is not a
/// multiple of three. Rationally satisfiable (`Σ m_i = 262145/3`).
fn cascade_clause(terms: &mut TermStore, tail: i64) -> Vec<TermId> {
    let var = |terms: &mut TermStore, name: &str| terms.mk_var(name, Sort::Int);
    let s: Vec<TermId> = ["s1", "s2", "s3"].iter().map(|n| var(terms, n)).collect();
    let c: Vec<TermId> = ["c1", "c2", "c3", "c4"]
        .iter()
        .map(|n| var(terms, n))
        .collect();
    let m: Vec<TermId> = ["m1", "m2", "m3", "m4", "m5"]
        .iter()
        .map(|n| var(terms, n))
        .collect();
    let m3: Vec<TermId> = m.iter().map(|&mi| times(terms, mi, 3)).collect();
    let c16: Vec<TermId> = c.iter().map(|&ci| times(terms, ci, 65536)).collect();
    let mut clause = Vec::new();
    let tail = int(terms, tail);
    let equalities = [
        (vec![s[2], m3[4]], vec![c16[3], tail]),
        (vec![c16[2], s[2]], vec![s[1], m3[3]]),
        (vec![c16[0], s[0]], vec![m3[0], m3[1]]),
        (vec![c16[1], s[1]], vec![s[0], m3[2]]),
    ];
    for (lhs, rhs) in equalities {
        let lhs = terms.mk_add(lhs);
        let rhs = terms.mk_add(rhs);
        let equality = terms.mk_eq(lhs, rhs);
        clause.push(not(terms, equality));
    }
    let (zero, one, lo, hi, word) = (
        int(terms, 0),
        int(terms, 1),
        int(terms, 40000),
        int(terms, 60000),
        int(terms, 65535),
    );
    let mut bound = |terms: &mut TermStore, lhs: TermId, rhs: TermId| {
        let atom = terms.mk_le(lhs, rhs);
        clause.push(not(terms, atom));
    };
    for &si in &s {
        bound(terms, si, word);
        bound(terms, zero, si);
    }
    for &ci in &c {
        bound(terms, ci, one);
        bound(terms, zero, ci);
    }
    for (&mi, &mi3) in m.iter().zip(&m3) {
        bound(terms, zero, mi);
        bound(terms, mi3, hi);
        bound(terms, mi3, word);
        bound(terms, lo, mi3);
        bound(terms, zero, mi3);
    }
    clause
}

#[test]
fn certifies_the_cascade_lemma_through_a_cut_chain() {
    let mut terms = TermStore::new();
    let clause = cascade_clause(&mut terms, 1);
    assert_eq!(clause.len(), 43);
    let witness = lia_cut_chain_witness(&terms, &clause).expect("cut chain");
    assert!(recognize_int_cg_cut_chain(&terms, &clause));
    // Integer rounding is load-bearing: the negation is rationally
    // satisfiable, so no zero-cut (Farkas) combination can exist.
    assert!(!witness.cuts.is_empty());
    assert!(validate_cut_chain(&witness));
    // The chain rounds the carry total `c1 + c2 + c3 + c4` somewhere.
    let carries: std::collections::BTreeSet<TermId> = ["c1", "c2", "c3", "c4"]
        .iter()
        .map(|n| terms.mk_var(*n, Sort::Int))
        .collect();
    assert!(witness.cuts.iter().any(|cut| {
        let atoms: std::collections::BTreeSet<TermId> = cut.form.keys().copied().collect();
        atoms == carries
    }));
}

/// `2x ≥ 1 ∧ 2x ≤ 1`: satisfiable at `x = 1/2`, so one rounding is needed.
#[test]
fn certifies_a_parity_squeeze_with_one_rounding() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let two_x = times(&mut terms, x, 2);
    let one = int(&mut terms, 1);
    let low = terms.mk_le(one, two_x);
    let high = terms.mk_le(two_x, one);
    let clause = vec![not(&mut terms, low), not(&mut terms, high)];
    let witness = lia_cut_chain_witness(&terms, &clause).expect("cut chain");
    assert!(!witness.cuts.is_empty());
}

/// A rationally infeasible clause needs no rounding: the certificate is a
/// plain Farkas combination. The funnel's payload-free rational arm tries
/// only UNIT multipliers, so it owns this clause first but not one whose
/// Farkas multipliers are not all one
/// (`a_non_unit_farkas_certificate_is_a_cut_free_chain`).
#[test]
fn a_rationally_infeasible_clause_needs_no_cut() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let (zero, one) = (int(&mut terms, 0), int(&mut terms, 1));
    let low = terms.mk_le(one, x);
    let high = terms.mk_le(x, zero);
    let clause = vec![not(&mut terms, low), not(&mut terms, high)];
    let witness = lia_cut_chain_witness(&terms, &clause).expect("Farkas chain");
    assert!(witness.cuts.is_empty());
    assert!(witness.final_row_multipliers.iter().all(|m| !m.is_zero()));
}

/// `x + 2y ≥ 4, x ≤ 1, y ≤ 1` (and `x + y + 3z ≥ 7` with `x, y, z ≤ 1`):
/// rationally infeasible, but only with the multipliers `(1, 1, 2)` and
/// `(1, 1, 1, 3)`, never with the unit ones the funnel's payload-free
/// rational arm tries. So this rule, asked last, is what certifies them — the
/// pair with no cut (its final combination IS the Farkas certificate), the
/// triple after one rounding the search takes on its way (`3z ≥ 5` rounds to
/// `z ≥ 2`) — and each lowers to checked `la_generic` steps. Pinned so the
/// label stays deliberate; the executor's
/// `reconstruct_missing_farkas_coefficients` relabels such a lemma
/// `LraFarkas` afterwards (`proof_farkas_tests.rs`).
#[test]
fn a_non_unit_farkas_certificate_is_a_cut_free_chain() {
    let mut terms = TermStore::new();
    let (x, y, z) = (
        terms.mk_var("x", Sort::Int),
        terms.mk_var("y", Sort::Int),
        terms.mk_var("z", Sort::Int),
    );
    let (one, four, seven) = (int(&mut terms, 1), int(&mut terms, 4), int(&mut terms, 7));
    let two_y = times(&mut terms, y, 2);
    let three_z = times(&mut terms, z, 3);
    let upper = |terms: &mut TermStore, var: TermId| {
        let atom = terms.mk_le(var, one);
        not(terms, atom)
    };
    let (x_le, y_le, z_le) = (
        upper(&mut terms, x),
        upper(&mut terms, y),
        upper(&mut terms, z),
    );
    let sum = terms.mk_add(vec![x, two_y]);
    let low = terms.mk_le(four, sum);
    let pair = vec![not(&mut terms, low), x_le, y_le];
    let sum = terms.mk_add(vec![x, y, three_z]);
    let low = terms.mk_le(seven, sum);
    let triple = vec![not(&mut terms, low), x_le, y_le, z_le];
    for (clause, multipliers) in [(pair, vec![1, 1, 2]), (triple, vec![1, 1, 1, 3])] {
        // Certified here — the search may round on its way (a cut is still a
        // checked `la_generic` step) …
        let witness = lia_cut_chain_witness(&terms, &clause).expect("certified");
        assert!(recognize_int_cg_cut_chain(&terms, &clause));
        // … although the plain Farkas certificate alone is a cut-free chain,
        let farkas = |multipliers: Vec<i64>| LiaCutChainWitness {
            rows: witness.rows.clone(),
            cuts: Vec::new(),
            final_row_multipliers: multipliers
                .into_iter()
                .map(|m| BigRational::from_integer(BigInt::from(m)))
                .collect(),
            final_cut_multipliers: Vec::new(),
        };
        assert!(validate_cut_chain(&farkas(multipliers)));
        // … and the unit multipliers the funnel's rational arm tries are not.
        assert!(!validate_cut_chain(&farkas(vec![1; clause.len()])));
    }
}

/// The chained-equality rows of `search::budget_tests` spelled as clause
/// literals: `(not (= (+ x_i y_0 … y_{f−1}) x_{i+1}))` for `i < 48` and
/// `(not (= (+ x_0 (* y_0 48) …) (+ x_48 1)))`. Refuted by exact elimination
/// alone, which costs `48·fillers + 2404` atom visits.
fn chained_equality_clause(terms: &mut TermStore, fillers: usize) -> Vec<TermId> {
    let x: Vec<TermId> = (0..=48)
        .map(|i| terms.mk_var(format!("x{i}"), Sort::Int))
        .collect();
    let y: Vec<TermId> = (0..fillers)
        .map(|j| terms.mk_var(format!("y{j}"), Sort::Int))
        .collect();
    let mut clause = Vec::with_capacity(49);
    for i in 0..48 {
        let mut summands = vec![x[i]];
        summands.extend(&y);
        let lhs = terms.mk_add(summands);
        let equality = raw(terms, "=", lhs, x[i + 1]);
        clause.push(not(terms, equality));
    }
    let mut summands = vec![x[0]];
    for &yj in &y {
        summands.push(times(terms, yj, 48));
    }
    let lhs = terms.mk_add(summands);
    let one = int(terms, 1);
    let rhs = terms.mk_add(vec![x[48], one]);
    let equality = raw(terms, "=", lhs, rhs);
    clause.push(not(terms, equality));
    clause
}

/// A clause whose equality elimination alone costs just more than the
/// search's work budget declines, fail-closed, while its twin one filler
/// narrower — exactly as refutable — is certified. Timing-free: the budget
/// counts atom visits (`search::budget_tests` pins the exact counts).
#[test]
fn declines_a_clause_whose_elimination_exceeds_the_work_budget() {
    let mut terms = TermStore::new();
    let within = chained_equality_clause(&mut terms, 632);
    let witness = lia_cut_chain_witness(&terms, &within).expect("refuted by elimination");
    assert!(witness.cuts.is_empty());
    let mut terms = TermStore::new();
    let over = chained_equality_clause(&mut terms, 633);
    assert!(lia_cut_chain_witness(&terms, &over).is_none());
}

fn cascade_witness(terms: &mut TermStore) -> LiaCutChainWitness {
    let clause = cascade_clause(terms, 1);
    lia_cut_chain_witness(terms, &clause).expect("cut chain")
}

#[test]
fn refuses_a_cut_rounded_past_its_combination() {
    let mut terms = TermStore::new();
    let mut witness = cascade_witness(&mut terms);
    for index in 0..witness.cuts.len() {
        let mut tampered = witness.clone();
        tampered.cuts[index].bound += 1;
        assert!(!validate_cut_chain(&tampered), "cut {index} +1 accepted");
    }
    witness.cuts.clear();
    witness.final_cut_multipliers.clear();
    assert!(!validate_cut_chain(&witness), "cut-free chain accepted");
}

#[test]
fn refuses_a_perturbed_or_sign_flipped_multiplier() {
    let mut terms = TermStore::new();
    let witness = cascade_witness(&mut terms);
    let half = BigRational::new(BigInt::one(), BigInt::from(2));
    for index in 0..witness.cuts.len() {
        let used = witness.cuts[index]
            .row_multipliers
            .iter()
            .position(|m| !m.is_zero())
            .expect("a cut uses a row");
        let mut perturbed = witness.clone();
        perturbed.cuts[index].row_multipliers[used] += &half;
        assert!(!validate_cut_chain(&perturbed), "cut {index} perturbed");
    }
    // An inequality row (index >= 4) used with a negative multiplier.
    let (cut, row) = witness
        .cuts
        .iter()
        .enumerate()
        .find_map(|(cut, c)| {
            (4..c.row_multipliers.len())
                .find(|&row| !c.row_multipliers[row].is_zero())
                .map(|row| (cut, row))
        })
        .expect("a cut uses an inequality row");
    let mut flipped = witness.clone();
    let value = flipped.cuts[cut].row_multipliers[row].clone();
    flipped.cuts[cut].row_multipliers[row] = -value;
    assert!(!validate_cut_chain(&flipped));
    let mut short = witness;
    let _ = short.final_row_multipliers.pop();
    assert!(!validate_cut_chain(&short), "short multiplier vector");
}

/// `0 ≤ x ∧ x ≤ 5` holds at `x = 3`, yet `−1·(x ≥ 0) + −1·(−x ≥ −5)` reads
/// `0 ≥ 5`: a negative multiplier on an inequality row flips it, and the
/// validator must refuse it. The same signs on two EQUALITY rows
/// (`x = 0 ∧ x = 1`, which has no model) are sound and accepted.
#[test]
fn refuses_a_negative_multiplier_on_an_inequality_row() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let (zero, one, five) = (int(&mut terms, 0), int(&mut terms, 1), int(&mut terms, 5));
    let witness_over =
        |terms: &TermStore, clause: &[TermId], multipliers: [i64; 2]| LiaCutChainWitness {
            rows: clause
                .iter()
                .map(|&literal| super::lia_cut_chain::chain_row(terms, literal).expect("row"))
                .collect(),
            cuts: Vec::new(),
            final_row_multipliers: multipliers
                .iter()
                .map(|&m| BigRational::from_integer(BigInt::from(m)))
                .collect(),
            final_cut_multipliers: Vec::new(),
        };
    let low = terms.mk_le(zero, x);
    let high = terms.mk_le(x, five);
    let clause = [not(&mut terms, low), not(&mut terms, high)];
    assert!(!validate_cut_chain(&witness_over(
        &terms,
        &clause,
        [-1, -1]
    )));
    assert!(lia_cut_chain_witness(&terms, &clause).is_none(), "x = 3");
    let at_zero = terms.mk_eq(x, zero);
    let at_one = terms.mk_eq(x, one);
    let clause = [not(&mut terms, at_zero), not(&mut terms, at_one)];
    assert!(validate_cut_chain(&witness_over(&terms, &clause, [-1, 1])));
}

/// `tail = 2`: `Σ 3m_i = 262146` has the integer model
/// `m = (17476, 17476, 17476, 17477, 17477)`, `c_i = 1`,
/// `s = (39320, 52392, 65464)`.
#[test]
fn declines_the_satisfiable_cascade() {
    let mut terms = TermStore::new();
    let clause = cascade_clause(&mut terms, 2);
    assert!(lia_cut_chain_witness(&terms, &clause).is_none());
}

#[test]
fn declines_real_atoms_and_positive_equalities() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Real);
    let two = terms.mk_rational(BigRational::from_integer(BigInt::from(2)));
    let one = terms.mk_rational(BigRational::one());
    let two_x = terms.mk_mul(vec![x, two]);
    let low = terms.mk_le(one, two_x);
    let high = terms.mk_le(two_x, one);
    let clause = vec![not(&mut terms, low), not(&mut terms, high)];
    assert!(lia_cut_chain_witness(&terms, &clause).is_none(), "x = 1/2");
    let y = terms.mk_var("y", Sort::Int);
    let zero = int(&mut terms, 0);
    let equality = terms.mk_eq(y, zero);
    let low = terms.mk_le(zero, y);
    let clause = vec![equality, not(&mut terms, low)];
    assert!(
        lia_cut_chain_witness(&terms, &clause).is_none(),
        "disequality"
    );
}

/// Each comparison, both polarities, reads as the pinned checker orients it.
#[test]
fn literal_rows_follow_the_checker_orientation() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let five = int(&mut terms, 5);
    let cases: [(&str, bool, i64, i64); 8] = [
        ("<=", true, -1, -5),
        ("<", true, -1, -4),
        (">=", true, 1, 5),
        (">", true, 1, 6),
        ("<=", false, 1, 6),
        ("<", false, 1, 5),
        (">=", false, -1, -4),
        (">", false, -1, -5),
    ];
    for (op, negated, coeff, bound) in cases {
        let atom = raw(&mut terms, op, x, five);
        let literal = if negated { not(&mut terms, atom) } else { atom };
        let row = super::lia_cut_chain::chain_row(&terms, literal).expect("row");
        assert!(!row.equality, "{op} {negated}");
        assert_eq!(
            row.form.get(&x),
            Some(&BigInt::from(coeff)),
            "{op} {negated}"
        );
        assert_eq!(row.bound, BigInt::from(bound), "{op} {negated}");
    }
}

/// Every clause over `x, y ∈ [-3, 3]` with two extra rows
/// `a·x + b·y ≥ k` (`a, b ∈ {-2..2}`, `k ∈ {-1, 1, 2}`): a certificate
/// exists only if brute force finds no integer model, and the rounding-only
/// ones are found.
#[test]
fn sweep_never_certifies_a_clause_with_an_integer_model() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let y = terms.mk_var("y", Sort::Int);
    let (minus_three, three) = (int(&mut terms, -3), int(&mut terms, 3));
    let mut box_literals = Vec::new();
    for var in [x, y] {
        let low = terms.mk_le(minus_three, var);
        let high = terms.mk_le(var, three);
        box_literals.push(not(&mut terms, low));
        box_literals.push(not(&mut terms, high));
    }
    let rows: Vec<(i64, i64, i64)> = (-2..=2)
        .flat_map(|a| (-2..=2).flat_map(move |b| [-1, 1, 2].map(move |k| (a, b, k))))
        .filter(|&(a, b, _)| a != 0 || b != 0)
        .collect();
    let (mut certified, mut rounding_only) = (0, 0);
    for (i, first) in rows.iter().enumerate() {
        for second in &rows[i + 1..] {
            let mut clause = box_literals.clone();
            for &(a, b, k) in [first, second] {
                let ax = times(&mut terms, x, a);
                let by = times(&mut terms, y, b);
                let sum = terms.mk_add(vec![ax, by]);
                let k = int(&mut terms, k);
                let atom = raw(&mut terms, ">=", sum, k);
                clause.push(not(&mut terms, atom));
            }
            let holds = |(a, b, k): (i64, i64, i64), vx: i64, vy: i64| a * vx + b * vy >= k;
            let integer_model = (-3..=3)
                .any(|vx| (-3..=3).any(|vy| holds(*first, vx, vy) && holds(*second, vx, vy)));
            if let Some(witness) = lia_cut_chain_witness(&terms, &clause) {
                assert!(!integer_model, "certified {first:?} {second:?}");
                certified += 1;
                rounding_only += usize::from(!witness.cuts.is_empty());
            }
        }
    }
    assert!(
        certified > 0 && rounding_only > 0,
        "{certified} {rounding_only}"
    );
}
