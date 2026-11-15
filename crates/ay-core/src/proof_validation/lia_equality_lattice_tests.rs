// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Tests for the all-equality lattice witness.
//!
//! * `recovers_*` pin the two corpus lemma shapes it exists for
//!   (`QF_LIA_ring_2exp12_3vars_deep_unsat` t20, which needs the multiplier
//!   3, and `QF_LIA_ring_2exp8_5vars_modular_unsat` t37, a parity chain);
//! * `declines_*` name the assignment that satisfies the clause's negation, or
//!   the exact fail-closed guard, for every shape it must refuse;
//! * the sweep binds the witness to the strict validator it mirrors: on small
//!   all-equality clauses it exists exactly when
//!   [`recognize_int_guarded_split_gap`] accepts, and it never exists for a
//!   clause whose negation has an integer model in the searched box.

use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};

use super::{lia_equality_lattice_witness, recognize_int_guarded_split_gap};
use crate::{Sort, TermId, TermStore};

fn int(terms: &mut TermStore, value: i64) -> TermId {
    terms.mk_int(BigInt::from(value))
}

fn scaled(terms: &mut TermStore, coefficient: i64, var: TermId) -> TermId {
    let coefficient = int(terms, coefficient);
    terms.mk_mul(vec![var, coefficient])
}

fn negated_equality(terms: &mut TermStore, lhs: TermId, rhs: TermId) -> TermId {
    let equality = terms.mk_eq(lhs, rhs);
    terms.mk_not_raw(equality)
}

/// `D = Σ λ_i·(lhs_i − rhs_i)` recomputed from scratch: `(gcd, constant)`.
fn combined(terms: &TermStore, witness: &super::LiaEqualityLatticeWitness) -> (BigInt, BigInt) {
    use num_integer::Integer;
    let mut form = std::collections::BTreeMap::<TermId, BigInt>::new();
    let mut constant = BigInt::zero();
    for (&(lhs, rhs), multiplier) in witness.equalities.iter().zip(&witness.multipliers) {
        let (row, row_constant) = super::lia::int_linear_diff(terms, lhs, rhs).expect("int row");
        for (term, coeff) in row {
            *form.entry(term).or_insert_with(BigInt::zero) += coeff * multiplier;
        }
        constant += row_constant * multiplier;
    }
    let gcd = form
        .values()
        .fold(BigInt::zero(), |gcd, coeff| gcd.gcd(&coeff.abs()));
    (gcd, constant)
}

/// t20 of the deep ring row: `3·s1 = 4096·c2 + s2`, `4096 = 4096·c1 + s1`,
/// `s2 + 500 = 4096·c3 + 1000`. Eliminating `s1` and `s2` needs the SECOND
/// row three times: `E1 + 3·E2 + E3` is `−4096·(3c1 + c2 + c3) + 11788 = 0`,
/// and `4096 ∤ 11788`. Rationally satisfiable (`c1 = 1, s1 = 0, c2 = 0,
/// s2 = 0, c3 = −500/4096`), so no Farkas certificate exists.
fn deep_ring_clause(terms: &mut TermStore) -> Vec<TermId> {
    let s1 = terms.mk_var("s1", Sort::Int);
    let s2 = terms.mk_var("s2", Sort::Int);
    let c1 = terms.mk_var("c1", Sort::Int);
    let c2 = terms.mk_var("c2", Sort::Int);
    let c3 = terms.mk_var("c3", Sort::Int);
    let three_s1 = scaled(terms, 3, s1);
    let c2_scaled = scaled(terms, 4096, c2);
    let e1_rhs = terms.mk_add(vec![c2_scaled, s2]);
    let e1 = negated_equality(terms, three_s1, e1_rhs);
    let modulus = int(terms, 4096);
    let c1_scaled = scaled(terms, 4096, c1);
    let e2_rhs = terms.mk_add(vec![c1_scaled, s1]);
    let e2 = negated_equality(terms, modulus, e2_rhs);
    let five_hundred = int(terms, 500);
    let e3_lhs = terms.mk_add(vec![s2, five_hundred]);
    let c3_scaled = scaled(terms, 4096, c3);
    let thousand = int(terms, 1000);
    let e3_rhs = terms.mk_add(vec![c3_scaled, thousand]);
    let e3 = negated_equality(terms, e3_lhs, e3_rhs);
    vec![e1, e2, e3]
}

#[test]
fn recovers_the_non_unit_multiplier_of_the_deep_ring_lemma() {
    let mut terms = TermStore::new();
    let clause = deep_ring_clause(&mut terms);
    assert!(recognize_int_guarded_split_gap(&terms, &clause));
    let witness = lia_equality_lattice_witness(&terms, &clause).expect("lattice witness");
    let sign = witness.multipliers[0].signum();
    let expected: Vec<BigInt> = [1, 3, 1].iter().map(|m| BigInt::from(*m) * &sign).collect();
    assert_eq!(witness.multipliers, expected);
    let (gcd, constant) = combined(&terms, &witness);
    assert_eq!(gcd, BigInt::from(4096));
    assert_eq!(constant, BigInt::from(11788) * &sign);
    let (lower, upper) = witness
        .gap
        .clone()
        .expect("a lattice gap, not a ground constant");
    assert_eq!(&upper - &lower, gcd);
    assert!(lower.is_negative() && upper.is_positive());
    // Both neighbours lie in `constant + 4096ℤ`.
    assert!(((&lower - &constant) % &gcd).is_zero());
    assert!(((&upper - &constant) % &gcd).is_zero());
}

/// t37 of the modular ring row: `256k3 + s3 = s2 + 2d2`,
/// `256k2 + s2 = s1 + 2c2`, `s3 + 2e2 = 256k4 + 127`,
/// `256k1 + s1 = 2a2 + 2b2` — an even form forced to equal 127.
#[test]
fn recovers_the_parity_chain_of_the_modular_ring_lemma() {
    let mut terms = TermStore::new();
    let names = [
        "a2", "b2", "c2", "d2", "e2", "s1", "s2", "s3", "k1", "k2", "k3", "k4",
    ];
    let v: Vec<TermId> = names.iter().map(|n| terms.mk_var(*n, Sort::Int)).collect();
    let (a2, b2, c2, d2, e2, s1, s2, s3, k1, k2, k3, k4) = (
        v[0], v[1], v[2], v[3], v[4], v[5], v[6], v[7], v[8], v[9], v[10], v[11],
    );
    let k3_scaled = scaled(&mut terms, 256, k3);
    let l1 = terms.mk_add(vec![k3_scaled, s3]);
    let d2_scaled = scaled(&mut terms, 2, d2);
    let r1 = terms.mk_add(vec![s2, d2_scaled]);
    let k2_scaled = scaled(&mut terms, 256, k2);
    let l2 = terms.mk_add(vec![k2_scaled, s2]);
    let c2_scaled = scaled(&mut terms, 2, c2);
    let r2 = terms.mk_add(vec![s1, c2_scaled]);
    let e2_scaled = scaled(&mut terms, 2, e2);
    let l3 = terms.mk_add(vec![s3, e2_scaled]);
    let k4_scaled = scaled(&mut terms, 256, k4);
    let odd = int(&mut terms, 127);
    let r3 = terms.mk_add(vec![k4_scaled, odd]);
    let k1_scaled = scaled(&mut terms, 256, k1);
    let l4 = terms.mk_add(vec![k1_scaled, s1]);
    let a2_scaled = scaled(&mut terms, 2, a2);
    let b2_scaled = scaled(&mut terms, 2, b2);
    let r4 = terms.mk_add(vec![a2_scaled, b2_scaled]);
    let clause = vec![
        negated_equality(&mut terms, l1, r1),
        negated_equality(&mut terms, l2, r2),
        negated_equality(&mut terms, l3, r3),
        negated_equality(&mut terms, l4, r4),
    ];
    assert!(recognize_int_guarded_split_gap(&terms, &clause));
    let witness = lia_equality_lattice_witness(&terms, &clause).expect("lattice witness");
    assert!(witness.multipliers.iter().all(|m| m.abs().is_one()));
    let (gcd, constant) = combined(&terms, &witness);
    assert_eq!(gcd, BigInt::from(2));
    assert!(!(&constant % BigInt::from(2)).is_zero());
    assert_eq!(witness.gap.map(|(lower, upper)| upper - lower), Some(gcd));
}

/// `x = 1` and `x = 2`: a GROUND contradiction after one substitution, with no
/// lattice step. The witness says so (`gap: None`), and its multipliers
/// really do combine the two rows to a nonzero constant.
#[test]
fn recovers_a_ground_contradiction_without_a_gap() {
    let mut terms = TermStore::new();
    let x = terms.mk_var("x", Sort::Int);
    let one = int(&mut terms, 1);
    let two = int(&mut terms, 2);
    let clause = vec![
        negated_equality(&mut terms, x, one),
        negated_equality(&mut terms, x, two),
    ];
    let witness = lia_equality_lattice_witness(&terms, &clause).expect("ground witness");
    assert_eq!(witness.gap, None);
    let (gcd, constant) = combined(&terms, &witness);
    assert!(gcd.is_zero() && !constant.is_zero());
}

/// `2x + 4y − 2z − 4w = 4`, `−2x + 2z − 4w = 0`, `2x − 2y + 4z + 6w = −10`,
/// `4x + 6y + 2z − 6w = −10`: no `±1` pivot and every single row and every
/// elimination pair has an even gcd dividing its constant, so no derived row
/// refutes on its own. Two elimination pairs instead pin ONE form to two
/// different values, which the validator's gap pool refutes through that
/// form's lower and upper bound; the witness must take the difference of the
/// two rows, a nonzero constant (found by a 4-variable sweep; without that
/// branch of the witness's pool the validator accepts and the witness
/// declines).
#[test]
fn recovers_one_form_pinned_to_two_values() {
    let mut terms = TermStore::new();
    let vars: Vec<TermId> = ["x", "y", "z", "w"]
        .iter()
        .map(|n| terms.mk_var(*n, Sort::Int))
        .collect();
    let table: [([i64; 4], i64); 4] = [
        ([2, 4, -2, -4], 4),
        ([-2, 0, 2, -4], 0),
        ([2, -2, 4, 6], -10),
        ([4, 6, 2, -6], -10),
    ];
    let mut clause = Vec::new();
    for (coeffs, constant) in table {
        let summands: Vec<TermId> = vars
            .iter()
            .zip(coeffs)
            .filter(|(_, coeff)| *coeff != 0)
            .map(|(&var, coeff)| scaled(&mut terms, coeff, var))
            .collect();
        let lhs = terms.mk_add(summands);
        let rhs = int(&mut terms, constant);
        clause.push(negated_equality(&mut terms, lhs, rhs));
    }
    assert!(recognize_int_guarded_split_gap(&terms, &clause));
    let witness = lia_equality_lattice_witness(&terms, &clause).expect("lattice witness");
    let (gcd, constant) = combined(&terms, &witness);
    assert!(gcd.is_zero() && !constant.is_zero(), "{witness:?}");
    assert_eq!(witness.gap, None);
}

/// Negative twin of the deep lemma: with the third row's target 1000 replaced
/// by 500 the system has the integer model `s1 = 0, s2 = 0, c1 = 1, c2 = 0,
/// c3 = 0`; the validator declines, and so must the witness.
#[test]
fn declines_a_satisfiable_equality_system() {
    let mut terms = TermStore::new();
    let mut clause = deep_ring_clause(&mut terms);
    let s2 = terms.mk_var("s2", Sort::Int);
    let c3 = terms.mk_var("c3", Sort::Int);
    let five_hundred = int(&mut terms, 500);
    let lhs = terms.mk_add(vec![s2, five_hundred]);
    let c3_scaled = scaled(&mut terms, 4096, c3);
    let target = int(&mut terms, 500);
    let rhs = terms.mk_add(vec![c3_scaled, target]);
    clause[2] = negated_equality(&mut terms, lhs, rhs);
    assert!(!recognize_int_guarded_split_gap(&terms, &clause));
    assert_eq!(lia_equality_lattice_witness(&terms, &clause), None);
}

/// `2r = 1` over a REAL `r` holds at `r = 1/2`. Alone, the recognizer
/// declines it as well. Appended to the valid deep ring clause, the
/// recognizer SKIPS it (an unparsed literal only weakens the refuted
/// hypothesis) and still accepts, so there the witness's own all-`Int` row
/// read is what declines: every literal must be an integer row.
#[test]
fn declines_a_real_sorted_variable() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::Real);
    let two = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::from(2)));
    let two_r = terms.mk_mul(vec![two, r]);
    let one = terms.mk_rational(num_rational::BigRational::from_integer(BigInt::one()));
    let real_literal = negated_equality(&mut terms, two_r, one);
    assert_eq!(lia_equality_lattice_witness(&terms, &[real_literal]), None);
    let mut clause = deep_ring_clause(&mut terms);
    clause.push(real_literal);
    assert!(recognize_int_guarded_split_gap(&terms, &clause));
    assert_eq!(lia_equality_lattice_witness(&terms, &clause), None);
}

/// Only negated equalities are rows. A positive equality (whose negation is a
/// DISEQUALITY) or an order literal makes the clause a different theorem, so
/// the witness declines the whole clause rather than dropping the literal.
#[test]
fn declines_a_clause_with_a_non_row_literal() {
    let mut terms = TermStore::new();
    let mut clause = deep_ring_clause(&mut terms);
    let x = terms.mk_var("x", Sort::Int);
    let zero = int(&mut terms, 0);
    let positive = terms.mk_eq(x, zero);
    clause.push(positive);
    assert_eq!(lia_equality_lattice_witness(&terms, &clause), None);
    clause.pop();
    let bound = terms.mk_le(x, zero);
    clause.push(bound);
    assert_eq!(lia_equality_lattice_witness(&terms, &clause), None);
}

/// Deterministic sweep over small all-equality clauses: two or three rows over
/// three variables, coefficients in `[-4, 4]`, constants in `[-6, 6]`.
#[test]
fn sweep_agrees_with_the_validator_and_never_refutes_a_model() {
    let mut state: u64 = 0x9E37_79B9_7F4A_7C15;
    let mut next = |bound: u64| {
        state = state
            .wrapping_mul(6_364_136_223_846_793_005)
            .wrapping_add(1_442_695_040_888_963_407);
        (state >> 33) % bound
    };
    let mut accepted = 0usize;
    for _ in 0..1500 {
        let mut terms = TermStore::new();
        let vars: Vec<TermId> = ["x", "y", "z"]
            .iter()
            .map(|n| terms.mk_var(*n, Sort::Int))
            .collect();
        let rows = 2 + next(2) as usize;
        let mut table = Vec::new();
        let mut clause = Vec::new();
        for _ in 0..rows {
            let mut coeffs: Vec<i64> = (0..3).map(|_| next(9) as i64 - 4).collect();
            // A variable-free row is a ground literal the store folds to a
            // Boolean constant, not a negated equality; keep every row a row.
            if coeffs.iter().all(|&c| c == 0) {
                coeffs[0] = 1;
            }
            let constant = next(13) as i64 - 6;
            let mut summands = Vec::new();
            for (&var, &coeff) in vars.iter().zip(&coeffs) {
                if coeff != 0 {
                    summands.push(scaled(&mut terms, coeff, var));
                }
            }
            let lhs = if summands.len() == 1 {
                summands[0]
            } else {
                terms.mk_add(summands)
            };
            let rhs = int(&mut terms, constant);
            clause.push(negated_equality(&mut terms, lhs, rhs));
            table.push((coeffs, constant));
        }
        let validator = recognize_int_guarded_split_gap(&terms, &clause);
        let witness = lia_equality_lattice_witness(&terms, &clause);
        assert_eq!(
            validator,
            witness.is_some(),
            "witness and validator disagree on {table:?}"
        );
        let Some(witness) = witness else {
            continue;
        };
        accepted += 1;
        let (gcd, constant) = combined(&terms, &witness);
        assert!(
            if gcd.is_zero() {
                !constant.is_zero()
            } else {
                !(&constant % &gcd).is_zero()
            },
            "{table:?}"
        );
        for x in -8..=8_i64 {
            for y in -8..=8_i64 {
                for z in -8..=8_i64 {
                    let model = table
                        .iter()
                        .all(|(c, k)| c[0] * x + c[1] * y + c[2] * z == *k);
                    assert!(!model, "refuted {table:?} has model {x} {y} {z}");
                }
            }
        }
    }
    assert!(accepted > 50, "sweep exercised only {accepted} refutations");
}
