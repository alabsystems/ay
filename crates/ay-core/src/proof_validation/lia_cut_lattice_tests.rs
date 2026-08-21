// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the rank-1 two-row integer cut recognizer.
//!
//! Organized as the soundness argument is:
//!
//! * `accepts_*` pin the shapes the rule is FOR, starting with the verbatim
//!   #4751 empty-clause-closer head, and each records why the shipped
//!   `IntBoundLatticeGap` rule cannot reach it;
//! * `rejects_*` are adversarial negatives, and EVERY ONE names the concrete
//!   integer assignment that falsifies the clause, so a future loosening
//!   cannot be argued to be harmless;
//! * the `sweeps` child module enumerates bounded coefficient/bound boxes
//!   exhaustively and re-evaluates every ACCEPT at every point of an integer
//!   box with a plain-`i64` evaluator sharing no code with the recognizer;
//! * `GUARD_MUTATION_LEDGER` names, per guard, the test that fails when the
//!   guard is removed (the removal is performed by hand).

use num_bigint::BigInt;

use super::lia_cut_lattice::{int_cut_lattice_gap_core, recognize_int_cut_lattice_gap, CutRow};
use super::recognize_int_bound_lattice_gap;
use crate::{Sort, TermId, TermStore};

#[path = "lia_cut_lattice_accept_tests.rs"]
mod accepts;
#[path = "lia_cut_lattice_sweep_tests.rs"]
mod sweeps;

/// Which guard each test defends, and whether the guard is SOUNDNESS-critical.
///
/// A soundness guard is one whose removal admits a FALSE clause; every such
/// entry below was checked by DELETING the guard, running the named test,
/// observing the failure, and restoring the guard — nine of nine failed as
/// required.
///
/// A scope guard cannot make an accept unsound, and its deletion was MEASURED
/// to leave every verdict unchanged. Its entry names the test that pins the
/// rule's intended reach instead, and states why the guard is safe to keep.
const GUARD_MUTATION_LEDGER: &[(&str, &str, Soundness)] = &[
    (
        "int_linear_diff: `Sort::Int` check on every variable (inherited)",
        "rejects_real_sorted_cut_satisfied_at_one_half",
        Soundness::Critical,
    ),
    (
        "BoundPool::insert: the group key is the EXACT canonical coefficient \
         map, not the set of variables",
        "rejects_bounds_on_the_same_variable_with_different_coefficients",
        Soundness::Critical,
    ),
    (
        "BoundPool::find_gap: both a lower AND an upper bound required",
        "rejects_cut_with_only_a_lower_bound",
        Soundness::Critical,
    ),
    (
        "BoundPool::find_gap: `gcd.is_positive()` (SCOPE — DEFENSIVE and \
         unreachable by construction: an empty form has no leading \
         coefficient, so `insert` always files it as a LOWER bound and the \
         both-directions check skips the group before the gcd is read; every \
         non-empty form has all-nonzero coefficients, so its gcd is positive. \
         Deleting it therefore changes no verdict — MEASURED — and the named \
         test pins that a variable-free combination still cannot panic)",
        "rejects_variable_free_combination_without_panicking",
        Soundness::Scope,
    ),
    (
        "BoundPool::find_gap: strict `>` in the attainability test",
        "rejects_derived_range_whose_endpoint_is_attainable",
        Soundness::Critical,
    ),
    (
        "BoundPool::find_gap: `div_ceil` rounding, not a bare `lower > upper`",
        "accepts_the_benchmark_empty_clause_closer_head",
        Soundness::Critical,
    ),
    (
        "BoundPool::insert: tightest-bound selection per group",
        "accepts_only_when_the_tightest_derived_pair_conflicts",
        Soundness::Critical,
    ),
    (
        "eliminating_combinations: the BOUND is scaled by the same multipliers \
         as the form",
        "rejects_scaled_pair_whose_unscaled_bound_would_forge_a_gap",
        Soundness::Critical,
    ),
    (
        "eliminating_combinations: multipliers are `|c|/gcd`, so BOTH are \
         positive — a signed multiplier SUBTRACTS a `>=` row",
        "rejects_pair_whose_signed_multiplier_would_forge_a_gap",
        Soundness::Critical,
    ),
    (
        "parse_ge_rows: `MAX_CUT_ROWS` declines outright rather than truncating",
        "rejects_a_clause_wider_than_the_row_cap",
        Soundness::Critical,
    ),
    (
        "eliminating_combinations: opposite-sign filter (SCOPE — a same-sign \
         pair still combines with positive multipliers, which is sound; it \
         just cancels nothing, so removing it costs work, not soundness)",
        "rejects_clause_whose_only_route_is_a_negative_multiplier",
        Soundness::Scope,
    ),
];

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Soundness {
    Critical,
    Scope,
}

#[test]
fn guard_mutation_ledger_names_a_test_per_guard() {
    assert_eq!(
        GUARD_MUTATION_LEDGER.len(),
        11,
        "every guard in the recognizer must name the test that defends it",
    );
    let critical = GUARD_MUTATION_LEDGER
        .iter()
        .filter(|(_, _, s)| *s == Soundness::Critical)
        .count();
    assert_eq!(
        critical, 9,
        "the soundness-critical guards are the ones whose deletion admits a \
         FALSE clause; that count must not drift silently",
    );
    for (guard, test, _) in GUARD_MUTATION_LEDGER {
        assert!(!guard.is_empty() && !test.is_empty());
    }
}

// ---------------------------------------------------------------------------
// A tiny independent literal model over three integer variables.
//
// `LitSpec` is evaluated with plain `i64` arithmetic and shares NO code with
// the recognizer (no `TermStore`, no `parse_linear_expr`, no `BigInt`), so
// agreement between the two is real evidence rather than a tautology.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum Cmp {
    Le,
    Lt,
}

/// `negated ? not(c0*x + c1*y + c2*z + k CMP rhs) : (...)`.
#[derive(Clone, Copy, Debug)]
struct LitSpec {
    coeffs: [i64; 3],
    constant: i64,
    cmp: Cmp,
    rhs: i64,
    negated: bool,
}

impl LitSpec {
    fn holds(self, point: [i64; 3]) -> bool {
        let lhs = self.coeffs[0] * point[0]
            + self.coeffs[1] * point[1]
            + self.coeffs[2] * point[2]
            + self.constant;
        let atom = match self.cmp {
            Cmp::Le => lhs <= self.rhs,
            Cmp::Lt => lhs < self.rhs,
        };
        atom != self.negated
    }

    fn build(self, terms: &mut TermStore, vars: [TermId; 3]) -> TermId {
        let mut summands = Vec::new();
        for (coeff, var) in self.coeffs.into_iter().zip(vars) {
            if coeff != 0 {
                let c = terms.mk_int(BigInt::from(coeff));
                summands.push(terms.mk_mul(vec![c, var]));
            }
        }
        if self.constant != 0 || summands.is_empty() {
            summands.push(terms.mk_int(BigInt::from(self.constant)));
        }
        let lhs = if summands.len() == 1 {
            summands[0]
        } else {
            terms.mk_add(summands)
        };
        let rhs = terms.mk_int(BigInt::from(self.rhs));
        let atom = match self.cmp {
            Cmp::Le => terms.mk_le(lhs, rhs),
            Cmp::Lt => terms.mk_lt(lhs, rhs),
        };
        if self.negated {
            terms.mk_not(atom)
        } else {
            atom
        }
    }
}

/// `c·vars >= value`, spelled as the POSITIVE literal `c·vars < value` whose
/// FALSITY is the bound (the positive-literal arm of `parse_int_bound`).
fn ge(coeffs: [i64; 3], value: i64) -> LitSpec {
    LitSpec {
        coeffs,
        constant: 0,
        cmp: Cmp::Lt,
        rhs: value,
        negated: false,
    }
}

/// `c·vars <= value`, spelled as the NEGATED literal `(not (c·vars <= value))`.
fn le(coeffs: [i64; 3], value: i64) -> LitSpec {
    LitSpec {
        coeffs,
        constant: 0,
        cmp: Cmp::Le,
        rhs: value,
        negated: true,
    }
}

fn build_clause(terms: &mut TermStore, spec: &[LitSpec]) -> Vec<TermId> {
    let vars = [
        terms.mk_var("x", Sort::Int),
        terms.mk_var("y", Sort::Int),
        terms.mk_var("z", Sort::Int),
    ];
    spec.iter().map(|lit| lit.build(terms, vars)).collect()
}

/// True when `spec`'s clause is FALSE at `point` — every literal false there,
/// so the NAMED point refutes the clause's validity. Used by the adversarial
/// negatives, which each name their own witness rather than reporting whichever
/// point a search happens to reach first.
fn falsified_at(spec: &[LitSpec], point: [i64; 3]) -> bool {
    spec.iter().all(|lit| !lit.holds(point))
}

/// Search a box for an integer point falsifying EVERY literal of `spec`.
fn falsifying_point(spec: &[LitSpec], radius: i64) -> Option<[i64; 3]> {
    for x in -radius..=radius {
        for y in -radius..=radius {
            for z in -radius..=radius {
                if spec.iter().all(|lit| !lit.holds([x, y, z])) {
                    return Some([x, y, z]);
                }
            }
        }
    }
    None
}

/// Accept the clause and re-check, with the independent evaluator, that no
/// point of a generous integer box falsifies it.
fn accept_and_re_evaluate(spec: &[LitSpec], radius: i64) -> super::IntCutLatticeGap {
    let mut terms = TermStore::new();
    let clause = build_clause(&mut terms, spec);
    let core = int_cut_lattice_gap_core(&terms, &clause)
        .unwrap_or_else(|| panic!("expected an accept for {spec:?}"));
    assert_eq!(
        falsifying_point(spec, radius),
        None,
        "ACCEPTED a clause the independent evaluator falsifies: {spec:?}"
    );
    core
}

fn assert_declined(spec: &[LitSpec]) {
    let mut terms = TermStore::new();
    let clause = build_clause(&mut terms, spec);
    assert!(
        !recognize_int_cut_lattice_gap(&terms, &clause),
        "expected a decline for {spec:?}"
    );
}

// ---------------------------------------------------------------------------
// Adversarial negatives. Each names the assignment that falsifies the clause.
// ---------------------------------------------------------------------------

/// FALSIFYING ASSIGNMENT: `r = 1/2, s = 0` gives `2r + s = 1`, satisfying both
/// `2r + s >= 1` and `2r + s <= 1` together with `s ∈ [0, 0]`. Over the reals
/// the lattice argument is simply false, and `int_linear_diff` fails closed on
/// a non-`Int` variable, which is what keeps it out.
#[test]
fn rejects_real_sorted_cut_satisfied_at_one_half() {
    let mut terms = TermStore::new();
    let r = terms.mk_var("r", Sort::Real);
    let s = terms.mk_var("s", Sort::Real);
    let two = terms.mk_rational(num_rational::BigRational::from(BigInt::from(2)));
    let two_r = terms.mk_mul(vec![two, r]);
    let form = terms.mk_add(vec![two_r, s]);
    let one = terms.mk_rational(num_rational::BigRational::from(BigInt::from(1)));
    let zero = terms.mk_rational(num_rational::BigRational::from(BigInt::from(0)));
    let lower = terms.mk_lt(form, one);
    let upper = terms.mk_le(form, one);
    let upper = terms.mk_not(upper);
    let s_lower = terms.mk_lt(s, zero);
    let s_upper = terms.mk_le(s, zero);
    let s_upper = terms.mk_not(s_upper);
    let clause = vec![lower, upper, s_lower, s_upper];
    assert!(!recognize_int_cut_lattice_gap(&terms, &clause));
}

/// FALSIFYING ASSIGNMENT: `x = 0, y = 3` satisfies `3x - 2y >= -6`,
/// `3y >= 7` and `9x <= 8`. The correct combination scales the BOUNDS by the
/// same `(3, 2)` the form is scaled by, giving `9x >= -4`; scaling only the
/// form and adding the raw bounds would forge `9x >= 1` and a gap against
/// `9x <= 8`.
#[test]
fn rejects_scaled_pair_whose_unscaled_bound_would_forge_a_gap() {
    let spec = [ge([3, -2, 0], -6), ge([0, 3, 0], 7), le([9, 0, 0], 8)];
    assert!(
        falsified_at(&spec, [0, 3, 0]),
        "precondition: the named point really falsifies the clause"
    );
    assert_declined(&spec);
}

/// FALSIFYING ASSIGNMENT: `x = 0, y = 1` satisfies `2x + y >= 1`,
/// `2x + y <= 1` and `y >= 0`. Reaching `2x >= 1` here would need to SUBTRACT
/// `y >= 0` from `2x + y >= 1`, i.e. a negative multiplier, which is not a
/// valid inference.
#[test]
fn rejects_clause_whose_only_route_is_a_negative_multiplier() {
    let spec = [ge([2, 1, 0], 1), le([2, 1, 0], 1), ge([0, 1, 0], 0)];
    assert!(
        falsified_at(&spec, [0, 1, 0]),
        "precondition: the named point really falsifies the clause"
    );
    assert_declined(&spec);
}

/// FALSIFYING ASSIGNMENT: `x = 1, y = 0, z = 0`. The derived forms `2x` (from
/// eliminating `y`) and `2z` (from eliminating `y` on the other pair) are
/// DIFFERENT linear forms; pooling their bounds into one group would forge a
/// gap that does not exist.
#[test]
fn rejects_bounds_on_two_different_derived_forms() {
    let spec = [
        ge([2, 1, 0], 1),
        ge([0, -1, 0], 0),
        le([0, 0, 2], 1),
        le([0, -1, 0], 0),
    ];
    assert!(
        falsified_at(&spec, [1, 0, 0]),
        "precondition: the named point really falsifies the clause"
    );
    assert_declined(&spec);
}

/// FALSIFYING ASSIGNMENT: `x = 6, y = 0`. Every derived form here carries only
/// a LOWER bound, and a half-open range always contains an attainable value.
#[test]
fn rejects_cut_with_only_a_lower_bound() {
    let spec = [ge([2, 1, 0], 1), ge([0, -1, 0], 0), ge([0, 3, 0], -9)];
    assert!(
        falsified_at(&spec, [6, 0, 0]),
        "precondition: the named point really falsifies the clause"
    );
    assert_declined(&spec);
}

/// FALSIFYING ASSIGNMENT: `x = 0, y = 0`. Eliminating `x` between `x >= 0` and
/// `-x >= -5` cancels EVERY variable, leaving the ground row `0 >= -5`. That
/// is not a lattice at all (`gcd = 0`), and treating it as one would divide by
/// zero or accept a vacuous range.
#[test]
fn rejects_variable_free_combination_without_panicking() {
    let spec = [ge([1, 0, 0], 0), le([1, 0, 0], 5)];
    assert!(
        falsified_at(&spec, [0, 0, 0]),
        "precondition: the named point really falsifies the clause"
    );
    assert_declined(&spec);
}

/// FALSIFYING ASSIGNMENT: `x = 1, y = -1` gives `2x + y = 1` and `y = -1`, so
/// the derived form `2x` equals 2 — an ATTAINABLE point of the range `[2, 2]`.
/// A non-strict comparison in the attainability test would accept it.
#[test]
fn rejects_derived_range_whose_endpoint_is_attainable() {
    let spec = [
        ge([2, 1, 0], 1),
        le([2, 1, 0], 1),
        ge([0, -1, 0], 1),
        le([0, -1, 0], 1),
    ];
    assert!(
        falsified_at(&spec, [1, -1, 0]),
        "precondition: the named point really falsifies the clause"
    );
    assert_declined(&spec);
}

/// The row cap declines OUTRIGHT rather than truncating. The clause below is
/// the accepted `2q ∈ [1, 1]` core padded with enough irrelevant bounds to
/// cross `MAX_CUT_ROWS`; truncation would make acceptance depend on literal
/// order, so a producer could hide a rejection by permuting a clause.
#[test]
fn rejects_a_clause_wider_than_the_row_cap() {
    let mut spec = vec![ge([2, 0, 0], 1), le([2, 0, 0], 1)];
    for k in 0..60i64 {
        spec.push(ge([0, 1, 0], -1000 - k));
    }
    let mut terms = TermStore::new();
    let clause = build_clause(&mut terms, &spec);
    assert!(
        !recognize_int_cut_lattice_gap(&terms, &clause),
        "a clause past the row cap must be declined, not truncated"
    );
    // The same core WITHOUT the padding is accepted, so the decline is the cap
    // and nothing else.
    let core_only = [spec[0], spec[1]];
    let mut terms = TermStore::new();
    let clause = build_clause(&mut terms, &core_only);
    assert!(recognize_int_cut_lattice_gap(&terms, &clause));
}

/// FALSIFYING ASSIGNMENT: `x = 1` satisfies `4x >= 2` and `3x <= 3`. The two
/// bounds are on the SAME variable but on DIFFERENT linear forms (`4x` and
/// `3x`), and pooling them by variable set instead of by exact coefficient map
/// would read them as `4x ∈ [2, 3]` and forge a gap at `gcd = 4`.
#[test]
fn rejects_bounds_on_the_same_variable_with_different_coefficients() {
    let spec = [ge([4, 0, 0], 2), le([3, 0, 0], 3)];
    assert!(
        falsified_at(&spec, [1, 0, 0]),
        "precondition: the named point really falsifies the clause"
    );
    assert_declined(&spec);
}

/// FALSIFYING ASSIGNMENT: `x = 3, y = 5` satisfies `y >= 0`, `2x - y >= 1` and
/// `2x - 2y <= 1`. Cancelling `y` between the first two rows with a SIGNED
/// multiplier — `-1` on `y >= 0` — would subtract a `>=` row and forge
/// `2x - 2y >= 1`, which is false at that very point (`6 - 10 = -4`); against
/// the clause's own `2x - 2y <= 1` that forges a `gcd = 2` gap.
#[test]
fn rejects_pair_whose_signed_multiplier_would_forge_a_gap() {
    let spec = [ge([0, 1, 0], 0), ge([2, -1, 0], 1), le([2, -2, 0], 1)];
    assert!(
        falsified_at(&spec, [3, 5, 0]),
        "precondition: the named point really falsifies the clause"
    );
    assert_declined(&spec);
}

/// A clause with a single bound has no pair to combine and must decline.
/// FALSIFYING ASSIGNMENT: `x = 5`.
#[test]
fn rejects_a_single_bound_clause() {
    let spec = [ge([2, 0, 0], 1)];
    assert!(falsified_at(&spec, [5, 0, 0]));
    assert_declined(&spec);
}

/// An empty clause has nothing to certify.
#[test]
fn rejects_the_empty_clause() {
    let terms = TermStore::new();
    assert!(!recognize_int_cut_lattice_gap(&terms, &[]));
}
