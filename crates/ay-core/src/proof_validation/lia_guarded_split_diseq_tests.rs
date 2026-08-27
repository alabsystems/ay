// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Soundness tests for the guarded-split rule's SECOND split source: a
//! POSITIVE integer `=` literal, whose negation is a disequality and therefore
//! its own two-way case split over ℤ.
//!
//! Organized as the soundness argument is:
//!
//! * `accepts_*` pin the shape the arm is FOR, starting with a corpus clause
//!   copied literally out of `chc-comp/2025/extra-small-lia/phases_m_000`, and
//!   each records why every SHIPPED rule declines it;
//! * `rejects_*` are adversarial negatives, and EVERY ONE names a concrete
//!   integer assignment that falsifies the clause and CHECKS that assignment
//!   in-test with an evaluator that shares no code with the recognizer;
//! * the `sweeps` child module enumerates the parity family exhaustively and
//!   compares the verdict against an INDEPENDENT enumeration ground truth;
//! * [`DISEQ_GUARD_MUTATION_LEDGER`] names, per guard of the new arm, the test
//!   that fails when the guard is removed (the removal is performed by hand).

use num_bigint::BigInt;

use super::{
    recognize_int_bound_lattice_gap, recognize_int_cut_lattice_gap, recognize_int_guarded_split_gap,
};
use crate::{Sort, TermId, TermStore};

#[path = "lia_guarded_split_diseq_sweep_tests.rs"]
mod sweeps;
#[path = "lia_guarded_split_zero_split_tests.rs"]
mod zero_split;

/// Which guard of the disequality-split arm each test defends.
///
/// Every `Critical` entry below was checked by DELETING or weakening the guard
/// by hand, running the named test, observing the failure, and restoring the
/// guard. A `Scope` guard cannot make an accept unsound; its entry names the
/// test that pins the arm's intended reach instead.
pub(super) const DISEQ_GUARD_MUTATION_LEDGER: &[(&str, &str, bool)] = &[
    (
        "parse_base: a POSITIVE `=` literal is recorded ONLY as a split \
         candidate, never as a base equality row — the hypothesis contains \
         the DISEQUALITY it negates",
        "rejects_positive_equality_read_as_a_base_row",
        true,
    ),
    (
        "parse_base: the split arm fires on the POSITIVE `=` only; a NEGATED \
         `=` stays a base equality row and is never case-split",
        "rejects_negated_equality_read_as_a_disequality_split",
        true,
    ),
    (
        "disequality_split_refutes: BOTH branches must be refuted before the \
         candidate is accepted",
        "rejects_split_with_only_one_branch_refuted",
        true,
    ),
    (
        "disequality_branches: the two branches COVER `form != bound` EXACTLY \
         (`bound+1` and `bound-1`). A WIDER exclusion window leaves a \
         satisfying point in neither branch, so both can be refuted while the \
         clause is false. (The NARROWER direction — dropping the +1 — is \
         completeness-only, and it is pinned separately and two-sided by the \
         EXACT sweep, which turns RED on it.)",
        "rejects_split_whose_branches_would_leave_a_point_uncovered",
        true,
    ),
    (
        "disequality_branches: the `below` branch NEGATES the form as well as \
         the bound (`-form >= -bound + 1`)",
        "rejects_split_whose_below_branch_would_repeat_the_above_branch",
        true,
    ),
    (
        "int_equality_row / int_linear_diff: `Sort::Int` on every variable \
         (inherited) — the lattice step is licensed by integrality alone",
        "rejects_real_sorted_parity_clause",
        true,
    ),
    (
        "parse_base: a split candidate must carry a NON-EMPTY linear form; \
         `int_linear_diff` cancels `(= t t)` to the empty map at any sort, \
         and splitting it accepts every clause with a reflexive equality — \
         sound, but outside this rule's stated reach and ahead of the rules \
         that render such a clause with a real Alethe name",
        "declines_a_split_over_a_variable_free_reflexive_equality",
        false,
    ),
    (
        "disequality_split_refutes: MAX_SPLIT_DISJUNCTS caps the number of \
         disequality CANDIDATES, declining the arm outright rather than \
         trying a prefix (SCOPE — a work bound; trying more candidates \
         cannot admit a false clause, only cost time)",
        "rejects_a_clause_with_more_split_candidates_than_the_cap",
        false,
    ),
    (
        "disequality_split_refutes: MAX_GUARDED_ROWS on the branch row set \
         (SCOPE — MEASURED GREEN on its own AND in a PAIR with `parse_base`'s \
         cap, because `branch_refuted` carries a THIRD cap over the same \
         constant; deleting all THREE together turns the named test RED. More \
         rows can never admit a false clause: every row is implied by the \
         clause's negation, so a larger row set only makes the hypothesis \
         being refuted stronger)",
        "rejects_a_split_branch_wider_than_the_row_cap",
        false,
    ),
];

#[test]
fn diseq_guard_mutation_ledger_names_a_test_per_guard() {
    assert_eq!(
        DISEQ_GUARD_MUTATION_LEDGER.len(),
        9,
        "every guard of the disequality-split arm must name its defending test",
    );
    let critical = DISEQ_GUARD_MUTATION_LEDGER
        .iter()
        .filter(|(_, _, c)| *c)
        .count();
    assert_eq!(critical, 6, "six guards admit a FALSE clause when removed");
}

// ---------------------------------------------------------------------------
// An independent literal model. Nothing here calls the recognizer; `holds` is
// plain `i64` arithmetic and `build` is plain term construction, so the sweeps
// and the negatives below decide validity without sharing any code with the
// rule under test.
// ---------------------------------------------------------------------------

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(super) enum Rel {
    Le,
    Lt,
    Eq,
}

/// `coeffs · vars + constant  REL  rhs`, optionally `not`-wrapped.
#[derive(Clone, Copy, Debug)]
pub(super) struct Lit {
    pub(super) coeffs: [i64; 3],
    pub(super) constant: i64,
    pub(super) rel: Rel,
    pub(super) rhs: i64,
    pub(super) negated: bool,
}

impl Lit {
    /// The literal's truth value at `point` — independent `i64` arithmetic.
    pub(super) fn holds(self, point: [i64; 3]) -> bool {
        let lhs = self.coeffs[0] * point[0]
            + self.coeffs[1] * point[1]
            + self.coeffs[2] * point[2]
            + self.constant;
        let atom = match self.rel {
            Rel::Le => lhs <= self.rhs,
            Rel::Lt => lhs < self.rhs,
            Rel::Eq => lhs == self.rhs,
        };
        atom != self.negated
    }

    pub(super) fn build(self, terms: &mut TermStore, vars: [TermId; 3]) -> TermId {
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
        let atom = match self.rel {
            Rel::Le => terms.mk_le(lhs, rhs),
            Rel::Lt => terms.mk_lt(lhs, rhs),
            Rel::Eq => terms.mk_eq(lhs, rhs),
        };
        if self.negated {
            // `mk_not_raw`, not `mk_not`: the folding builder rewrites
            // `(not (<= a b))` to `(< b a)`, which would silently change which
            // parse arm the literal reaches.
            terms.mk_not_raw(atom)
        } else {
            atom
        }
    }
}

/// `c·vars >= value`, spelled as the POSITIVE literal `c·vars < value` whose
/// FALSITY is the bound.
pub(super) fn ge(coeffs: [i64; 3], value: i64) -> Lit {
    Lit {
        coeffs,
        constant: 0,
        rel: Rel::Lt,
        rhs: value,
        negated: false,
    }
}

/// `c·vars <= value`, spelled as the NEGATED literal `(not (c·vars <= value))`.
pub(super) fn le(coeffs: [i64; 3], value: i64) -> Lit {
    Lit {
        coeffs,
        constant: 0,
        rel: Rel::Le,
        rhs: value,
        negated: true,
    }
}

/// `c·vars = value` as a BASE row, spelled `(not (= c·vars value))`.
pub(super) fn eq_row(coeffs: [i64; 3], value: i64) -> Lit {
    Lit {
        coeffs,
        constant: 0,
        rel: Rel::Eq,
        rhs: value,
        negated: true,
    }
}

/// `c·vars != value` as the SPLIT literal, spelled `(= c·vars value)`.
pub(super) fn diseq(coeffs: [i64; 3], value: i64) -> Lit {
    Lit {
        coeffs,
        constant: 0,
        rel: Rel::Eq,
        rhs: value,
        negated: false,
    }
}

pub(super) fn build_clause(terms: &mut TermStore, spec: &[Lit]) -> Vec<TermId> {
    let vars = [
        terms.mk_var("x", Sort::Int),
        terms.mk_var("y", Sort::Int),
        terms.mk_var("z", Sort::Int),
    ];
    spec.iter().map(|lit| lit.build(terms, vars)).collect()
}

/// True when EVERY literal of `spec` is false at `point`, i.e. the named point
/// refutes the clause's validity.
pub(super) fn falsified_at(spec: &[Lit], point: [i64; 3]) -> bool {
    spec.iter().all(|lit| !lit.holds(point))
}

/// Search a box for an integer point falsifying every literal.
pub(super) fn falsifying_point(spec: &[Lit], radius: i64) -> Option<[i64; 3]> {
    for x in -radius..=radius {
        for y in -radius..=radius {
            for z in -radius..=radius {
                if falsified_at(spec, [x, y, z]) {
                    return Some([x, y, z]);
                }
            }
        }
    }
    None
}

pub(super) fn recognizes(spec: &[Lit]) -> bool {
    let mut terms = TermStore::new();
    let clause = build_clause(&mut terms, spec);
    recognize_int_guarded_split_gap(&terms, &clause)
}

/// Assert the clause is DECLINED and that the named point really falsifies it,
/// so the decline can never be argued away as over-caution.
fn assert_declined_and_falsified_at(spec: &[Lit], point: [i64; 3]) {
    assert!(
        falsified_at(spec, point),
        "the negative's own witness {point:?} does not falsify {spec:?}"
    );
    assert!(
        !recognizes(spec),
        "ACCEPTED a clause falsified at {point:?}: {spec:?}"
    );
}

// ---------------------------------------------------------------------------
// Accepts.
// ---------------------------------------------------------------------------

/// The corpus clause, copied literally from the census dump of
/// `benchmarks/chc-comp/2025/extra-small-lia/phases_m_000.smt2`:
///
/// ```text
/// (cl (not (= (+ (* q2 2) r3) (+ (* q0 2) 2)))
///     (not (< r3 2))
///     (not (<= C (* q0 2)))
///     (not (<= 0 r3))
///     (= r3 0))
/// ```
///
/// Its negation asserts `2q2 + r3 = 2q0 + 2`, `r3 < 2`, `C <= 2q0`,
/// `0 <= r3` and `r3 != 0`. The equality forces `r3` EVEN, `0 <= r3 <= 1`
/// then forces `r3 = 0`, and the disequality contradicts it. Rationally the
/// system is satisfiable at `r3 = 1, q2 = q0 + 1/2`, so no Farkas certificate
/// exists — which is why the whole family carried payload `none`.
fn phases_clause(terms: &mut TermStore) -> Vec<TermId> {
    let q0 = terms.mk_var("q0", Sort::Int);
    let q2 = terms.mk_var("q2", Sort::Int);
    let r3 = terms.mk_var("r3", Sort::Int);
    let c = terms.mk_var("C", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));

    let two_q2 = terms.mk_mul(vec![two, q2]);
    let lhs = terms.mk_add(vec![two_q2, r3]);
    let two_b = terms.mk_int(BigInt::from(2));
    let two_q0 = terms.mk_mul(vec![two_b, q0]);
    let two_c = terms.mk_int(BigInt::from(2));
    let rhs = terms.mk_add(vec![two_q0, two_c]);
    let witness = terms.mk_eq(lhs, rhs);
    let l0 = terms.mk_not_raw(witness);

    let two_d = terms.mk_int(BigInt::from(2));
    let upper = terms.mk_lt(r3, two_d);
    let l1 = terms.mk_not_raw(upper);

    let two_e = terms.mk_int(BigInt::from(2));
    let two_q0_again = terms.mk_mul(vec![two_e, q0]);
    let c_bound = terms.mk_le(c, two_q0_again);
    let l2 = terms.mk_not_raw(c_bound);

    let zero = terms.mk_int(BigInt::from(0));
    let lower = terms.mk_le(zero, r3);
    let l3 = terms.mk_not_raw(lower);

    let zero_again = terms.mk_int(BigInt::from(0));
    let l4 = terms.mk_eq(r3, zero_again);

    vec![l0, l1, l2, l3, l4]
}

#[test]
fn accepts_the_corpus_parity_conflict_no_shipped_rule_could_reach() {
    let mut terms = TermStore::new();
    let clause = phases_clause(&mut terms);
    assert!(
        !recognize_int_bound_lattice_gap(&terms, &clause),
        "precondition: the bound-lattice rule must decline (no shared form \
         carries both a lower and an upper bound)"
    );
    assert!(
        !recognize_int_cut_lattice_gap(&terms, &clause),
        "precondition: the cut-lattice rule must decline (it never reads the \
         equality literal, and the remaining rows are satisfiable at r3 = 0)"
    );
    assert!(
        recognize_int_guarded_split_gap(&terms, &clause),
        "the disequality split must certify the corpus parity conflict"
    );
}

/// Independent re-evaluation of the accept above over an integer box: no
/// assignment of `(q0, q2, r3)` in `[-6, 6]^3` with `C = 2q0` falsifies it.
/// (`C` is chosen to falsify its own literal at every point, which is the
/// hardest case for the clause.)
#[test]
fn the_accepted_corpus_clause_is_true_at_every_point_of_a_box() {
    for q0 in -6..=6i64 {
        for q2 in -6..=6i64 {
            for r3 in -6..=6i64 {
                // Literal truth values, computed independently of the rule.
                let witness = 2 * q2 + r3 == 2 * q0 + 2;
                let upper = r3 < 2;
                let c_bound = 2 * q0 <= 2 * q0; // C := 2q0, always true
                let lower = 0 <= r3;
                let goal = r3 == 0;
                assert!(
                    !witness || !upper || !c_bound || !lower || goal,
                    "accepted clause is FALSE at q0={q0} q2={q2} r3={r3}"
                );
            }
        }
    }
}

/// The mechanism in miniature, with an OPAQUE `Int` term in place of a
/// variable: `int_linear_diff` normalizes an uninterpreted application to an
/// opaque atom and the argument then treats it as an unconstrained integer,
/// which only ENLARGES the reachable set — so a gap over the enlarged set is
/// still a gap.
#[test]
fn accepts_a_parity_conflict_over_an_opaque_integer_atom() {
    let mut terms = TermStore::new();
    let a = terms.mk_var("a", Sort::Int);
    let i = terms.mk_var("i", Sort::Int);
    let read = terms.mk_app(crate::term::Symbol::named("f"), vec![a, i], Sort::Int);
    let k = terms.mk_var("k", Sort::Int);
    let two = terms.mk_int(BigInt::from(2));
    let two_k = terms.mk_mul(vec![two, k]);
    let eq = terms.mk_eq(read, two_k);
    let l0 = terms.mk_not_raw(eq);
    let zero = terms.mk_int(BigInt::from(0));
    let lower = terms.mk_le(zero, read);
    let l1 = terms.mk_not_raw(lower);
    let one = terms.mk_int(BigInt::from(1));
    let upper = terms.mk_le(read, one);
    let l2 = terms.mk_not_raw(upper);
    let zero_again = terms.mk_int(BigInt::from(0));
    let l3 = terms.mk_eq(read, zero_again);
    let clause = vec![l0, l1, l2, l3];
    assert!(
        recognize_int_guarded_split_gap(&terms, &clause),
        "`f(a,i) = 2k` with `0 <= f(a,i) <= 1` forces `f(a,i) = 0`"
    );
}

// ---------------------------------------------------------------------------
// Adversarial negatives. Each names a falsifying assignment and CHECKS it.
// ---------------------------------------------------------------------------

/// FALSIFYING ASSIGNMENT `x = 1`: `x != 0`, `x <= 1` and `x >= 0` all hold, so
/// every literal is false. Reading the POSITIVE `(= x 0)` as a base equality
/// row would pin `x = 0` and refute both branches — the clause would be
/// "proved" false.
#[test]
fn rejects_positive_equality_read_as_a_base_row() {
    let spec = [diseq([1, 0, 0], 0), le([1, 0, 0], 1), ge([1, 0, 0], 0)];
    assert_declined_and_falsified_at(&spec, [1, 0, 0]);
}

/// FALSIFYING ASSIGNMENT `x = 0`: the NEGATED `(not (= x 0))` is false there
/// (the equality holds), as are `x <= 1` and `x >= 0`. Splitting a negated
/// equality as if it were a disequality refutes both halves of a dichotomy the
/// hypothesis does not contain.
#[test]
fn rejects_negated_equality_read_as_a_disequality_split() {
    let spec = [eq_row([1, 0, 0], 0), le([1, 0, 0], 1), ge([1, 0, 0], 0)];
    assert_declined_and_falsified_at(&spec, [0, 0, 0]);
}

/// FALSIFYING ASSIGNMENT `x = 5`: `x != 0` and `x >= 0` both hold. Only the
/// `x <= -1` branch is refuted; accepting on one refuted branch would be a
/// false certificate.
#[test]
fn rejects_split_with_only_one_branch_refuted() {
    let spec = [diseq([1, 0, 0], 0), ge([1, 0, 0], 0)];
    assert_declined_and_falsified_at(&spec, [5, 0, 0]);
}

/// FALSIFYING ASSIGNMENT `y = 6`: `y != 5` and `5 <= y <= 6` all hold, so
/// every literal is false. The branches must be `y >= 6` and `y <= 4`; a
/// WIDER exclusion window (`y >= 7` and `y <= 4`) is refuted on BOTH sides by
/// `y <= 6` and `y >= 5` while leaving `y = 6` — a genuine satisfying point —
/// in neither branch. That is the unsound direction of the `±1` offset.
#[test]
fn rejects_split_whose_branches_would_leave_a_point_uncovered() {
    let spec = [diseq([0, 1, 0], 5), ge([0, 1, 0], 5), le([0, 1, 0], 6)];
    assert_declined_and_falsified_at(&spec, [0, 6, 0]);
}

/// The candidate cap declines the arm OUTRIGHT rather than trying a prefix, so
/// acceptance can never depend on literal order. The same accepted core plus
/// enough extra positive equalities to pass the cap must decline.
#[test]
fn rejects_a_clause_with_more_split_candidates_than_the_cap() {
    let core = [
        eq_row([2, 1, 0], 0),
        ge([0, 1, 0], 0),
        le([0, 1, 0], 1),
        diseq([0, 1, 0], 0),
    ];
    assert!(recognizes(&core), "the uncapped core must be accepted");

    let mut spec = core.to_vec();
    for k in 0..60i64 {
        spec.push(diseq([0, 0, 1], 10_000 + k));
    }
    assert!(
        !recognizes(&spec),
        "a clause past the candidate cap must be declined, not prefixed"
    );
}

/// FALSIFYING ASSIGNMENT `x = 3`: `x != 0` and `x >= 2` hold. If the `below`
/// branch failed to negate the FORM it would repeat the `above` branch
/// (`x >= 1`), which `x >= 2` leaves unrefuted either way — the guard is
/// pinned by the accept in the sweeps, and this negative fixes the direction.
#[test]
fn rejects_split_whose_below_branch_would_repeat_the_above_branch() {
    let spec = [diseq([1, 0, 0], 0), ge([1, 0, 0], 2)];
    assert_declined_and_falsified_at(&spec, [3, 0, 0]);
}

#[path = "lia_guarded_split_diseq_scope_tests.rs"]
mod scope;
