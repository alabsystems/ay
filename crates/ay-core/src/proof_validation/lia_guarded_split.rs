// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Guarded-split lattice validation for WIDE integer clauses carrying one
//! negated-disjunction literal (#4751).
//!
//! The empty-clause closer's head on the `dillig12_m` clause-1 verification
//! shape is the claim "these leaves are jointly inconsistent": a clause whose
//! literals are the negations of ~35 integer facts (bounds and equalities)
//! plus the negations of one or two `or` terms. [`super::lia_cut_lattice`]
//! correctly declines it — the clause's linear literals alone are SATISFIABLE
//! (the facts only become inconsistent against the case analysis the `or`
//! literal carries), so no bound pool over them exhibits a gap.
//!
//! # The argument
//!
//! A clause `C = (cl L1 … Ln)` is valid iff `¬L1 ∧ … ∧ ¬Ln` is unsatisfiable.
//! Suppose some literal `Lk` is `(not O)` for a disjunction
//! `O = (or d1 … dm)`. Then `¬Lk = O`, and
//!
//! ```text
//! ¬C  ⊨  O  ⟹  ¬C satisfiable ⟹ some branch  ¬C ∧ dj  satisfiable.
//! ```
//!
//! Contrapositive: if EVERY branch `{¬Li} ∪ {dj}` is unsatisfiable over ℤ,
//! then `¬C` is unsatisfiable and `C` is valid. Each branch is tested against
//! a SUBSET of `¬C`'s conjuncts — the literals that parse as integer linear
//! constraints — which is sound because a subset of an unsatisfiable
//! constraint set only under-approximates the hypothesis being refuted:
//! `S ⊆ T` and `S` infeasible imply `T` infeasible.
//!
//! ## The zero-split case: the base rows alone
//!
//! The contrapositive degenerates gracefully. `¬C` entails every base row, so
//! if the base rows are ALREADY infeasible over ℤ the clause is valid with no
//! case analysis at all. That is not reachable by
//! [`super::lia_cut_lattice`] whenever the infeasibility lives in an EQUALITY
//! literal: `parse_int_bound` returns `None` for `=`, so both lattice rules
//! skip those literals, while the equality SUBSTITUTION step below consumes
//! them exactly. The corpus shape is a chain of Euclidean witness equalities
//! whose parities cannot be simultaneously satisfied — e.g.
//! `256k1 + s1 = 2a + 2b`, `256k2 + s2 = s1 + 2c`, `256k3 + s3 = s2 + 2d`,
//! `s3 + 2e = 256k4 + 127`, which forces an even form to equal an odd one.
//!
//! ## The second split source: a POSITIVE integer `=` literal
//!
//! The same contrapositive needs no `or` in the clause at all. If some literal
//! `Lk` is a POSITIVE integer equality `(= A B)`, then `¬Lk` is the
//! DISEQUALITY `A ≠ B`, and with `A − B = form + c` (so `A = B ⟺ form = b` for
//! `b = −c`) over ℤ
//!
//! ```text
//! ¬C  ⊨  form ≥ b+1  ∨  form ≤ b−1
//! ```
//!
//! — an exact two-way case split, because a linear form over `Int` variables
//! with integral coefficients takes only integral values, so `form ≠ b` leaves
//! no room between `b−1` and `b+1`. Refuting BOTH branches refutes `¬C`. This
//! is the CDCL(T) learned-conflict shape: a wide clause of negated bounds and
//! negated equalities plus ONE positive equality, whose negation is
//! rationally satisfiable and integrally infeasible only once the disequality
//! is split. `parse_int_bound` returns `None` for `=`, so such a literal
//! contributes no base row and the split cannot double-count it — the
//! hypothesis holds the disequality, never the equality.
//!
//! Per branch, infeasibility is established by exactly three certified means,
//! each self-contained and re-derived from the clause (no payload exists):
//!
//! 1. **Equality substitution.** An equality row `Σ aᵢxᵢ = b` whose pivot
//!    variable `x_v` has coefficient `±1` determines
//!    `x_v = ±(b − Σ_{i≠v} aᵢxᵢ)`, an integer for every integer assignment of
//!    the remaining variables, and conversely every solution of the reduced
//!    system extends uniquely to one of the original. Substituting it away is
//!    therefore an EXACT transformation over ℤ in both directions. A ground
//!    residue `0 = b` with `b ≠ 0` refutes the branch outright.
//! 2. **Non-negative two-row combination.** For `≥`-oriented rows,
//!    `λ·(F_i ≥ b_i) + μ·(F_j ≥ b_j)` with `λ, μ > 0` yields
//!    `λF_i + μF_j ≥ λb_i + μb_j`, again an all-`Int` linear form with an
//!    integer bound. As in [`super::lia_cut_lattice`], only the canonical
//!    Fourier–Motzkin elimination pair per (row, row, shared variable) triple
//!    is enumerated. A ground residue `0 ≥ b` with `b > 0` refutes the branch
//!    (a rational Farkas contradiction, valid a fortiori over ℤ).
//! 3. **Attainable-value gap.** If one canonical form `F` (a literal row or a
//!    derived combination) carries a lower bound `lo` and an upper bound `hi`
//!    and `g = gcd` of `F`'s coefficients admits no multiple in `[lo, hi]`,
//!    the branch has no integer solution: by Bézout the values of `F` over ℤ
//!    assignments are exactly `g·ℤ`. All variables are `Int`-sorted by
//!    construction (`parse_int_bound` / `int_linear_diff` fail-close on
//!    `Real`), which is what licenses the lattice step.
//!
//! Disjuncts and disequalities:
//!
//! * a disjunct `dj` that is itself a negated integer equality asserts a
//!   DISEQUALITY; over ℤ it splits exactly into `F ≥ b+1` or `F ≤ b−1`, and
//!   BOTH sub-branches must be refuted;
//! * a disjunct that is the literal constant `false` has no satisfying
//!   assignment, so its branch is vacuously refuted;
//! * any disjunct that does not parse EXACTLY as an integer constraint
//!   (including the literal `true`) fails the whole candidate `or` literal,
//!   fail-closed — for the branch hypothesis, unlike the base conjunction,
//!   dropping a conjunct would WEAKEN the refutation obligation, so nothing
//!   may be dropped there. The clause may still be admitted through another
//!   `(not (or …))` literal.
//!
//! Worked instance — the `dillig12_m`/q0000 closer head, 38 literals. The
//! chosen `or` is the substituted goal disjunction; its `(not (= r3 0))`
//! branch needs the strictly-integer step: the base equalities force
//! `2q2 + r3 − 2q0 − 2A = 2` after substituting `r1 = 0` and `B = A`, the
//! branch bounds force `1 ≤ r3 ≤ 1`, and eliminating `r3` squeezes the
//! all-even form `2q2 − 2q0 − 2A` into `[1, 1]`, which holds no multiple of
//! `gcd = 2`. Rationally that branch is satisfiable (`q2 = q0 + A + 1/2`), so
//! no Farkas certificate exists — the same reason the whole head family never
//! rescued through the discharge lanes.
//!
//! # Why the search is BOUNDED
//!
//! One candidate `or` per clause literal, at most [`MAX_SPLIT_DISJUNCTS`]
//! disjuncts each, at most two sub-branches per disjunct; per branch at most
//! [`MAX_GUARDED_ROWS`] rows, one substitution round per equality row, and
//! the same one-canonical-pair-per-triple elimination enumeration the cut
//! rule uses. Everything outside that class declines, fail-closed: a decline
//! is never evidence that a clause is false.
//!
//! # Why there is no payload
//!
//! The recognizer IS the validator: the producer-side classifier
//! (`empty_clause::trust_closer`) and the strict checker call this same
//! function, so no annotation exists to forge and no classifier/validator
//! drift is representable — the discipline established by
//! [`super::lia_bound_lattice`] and [`super::lia_cut_lattice`].

use std::collections::BTreeMap;

use num_bigint::BigInt;
use num_integer::Integer;
use num_traits::{Signed, Zero};

use crate::term::{Symbol, TermData};
use crate::{TermId, TermStore};

/// Canonical integer linear form: variable/opaque-atom term → coefficient.
/// Zero coefficients are never present.
type Coeffs = BTreeMap<TermId, BigInt>;

/// The most rows one branch will consider. A branch that would exceed this is
/// declined OUTRIGHT rather than truncated, so acceptance can never depend on
/// literal order.
const MAX_GUARDED_ROWS: usize = 96;

/// The widest `or` literal this rule will case-split.
const MAX_SPLIT_DISJUNCTS: usize = 48;

/// One `≥`-oriented row `form >= bound`.
#[derive(Debug, Clone)]
struct GeRow {
    form: Coeffs,
    bound: BigInt,
}

/// One equality row `form == bound`.
#[derive(Debug, Clone)]
struct EqRow {
    form: Coeffs,
    bound: BigInt,
}

/// The rows a branch starts from.
#[derive(Debug, Clone, Default)]
struct Rows {
    eqs: Vec<EqRow>,
    ges: Vec<GeRow>,
}

impl Rows {
    fn len(&self) -> usize {
        self.eqs.len() + self.ges.len()
    }
}

/// Recognize a WIDE integer clause made valid by case-splitting one of its
/// negated-disjunction literals and refuting every branch with equality
/// substitution, canonical two-row elimination, and the attainable-value gap
/// test. See the module docs for the full soundness argument.
#[must_use]
pub fn recognize_int_guarded_split_gap(terms: &TermStore, clause: &[TermId]) -> bool {
    let Some(base) = parse_base(terms, clause) else {
        return false;
    };
    if equality_substitution_refutes(&base) {
        return true;
    }
    if base.or_splits.is_empty() && base.diseq_splits.is_empty() {
        return false;
    }
    if disequality_split_refutes(&base) {
        return true;
    }
    let (base, split_candidates) = (base.rows, base.or_splits);
    'candidate: for &or_term in &split_candidates {
        let TermData::App(Symbol::Named(name), disjuncts) = terms.get(or_term) else {
            continue;
        };
        if name != "or" || disjuncts.len() < 2 || disjuncts.len() > MAX_SPLIT_DISJUNCTS {
            continue;
        }
        let disjuncts = disjuncts.clone();
        for &disjunct in &disjuncts {
            let Some(branches) = disjunct_branches(terms, disjunct) else {
                continue 'candidate;
            };
            for branch in branches {
                let mut rows = base.clone();
                rows.eqs.extend(branch.eqs);
                rows.ges.extend(branch.ges);
                if rows.len() > MAX_GUARDED_ROWS {
                    continue 'candidate;
                }
                if !branch_refuted(rows) {
                    continue 'candidate;
                }
            }
        }
        return true;
    }
    false
}

/// The clause's base conjunction plus every literal this rule can case-split.
#[derive(Debug, Clone, Default)]
struct Base {
    /// The rows the clause's other literals force unconditionally.
    rows: Rows,
    /// `(not (or …))` literals: the negation asserts the disjunction.
    or_splits: Vec<TermId>,
    /// POSITIVE integer `=` literals: the negation asserts a DISEQUALITY,
    /// which over ℤ is itself a two-way case split. `parse_int_bound` returns
    /// `None` for `=`, so such a literal contributes NO base row and the two
    /// readings cannot double-count.
    diseq_splits: Vec<EqRow>,
}

/// Read the clause's base conjunction (the negations of its literals) into
/// rows, and collect every literal this rule can case-split: a `(not (or …))`
/// whose negation asserts the disjunction, and a POSITIVE integer `=` whose
/// negation asserts a disequality.
///
/// Literals that do not parse are SKIPPED, which is sound for the BASE side:
/// dropping conjuncts of the hypothesis being refuted only weakens it.
fn parse_base(terms: &TermStore, clause: &[TermId]) -> Option<Base> {
    let mut base = Base::default();
    for &literal in clause {
        if let TermData::Not(inner) = terms.get(literal) {
            let inner = *inner;
            if let TermData::App(Symbol::Named(name), args) = terms.get(inner) {
                if name == "or" && args.len() >= 2 {
                    base.or_splits.push(inner);
                    continue;
                }
                if name == "=" && args.len() == 2 {
                    // Literal false ⟺ the equality HOLDS.
                    if let Some(eq) = int_equality_row(terms, args[0], args[1]) {
                        base.rows.eqs.push(eq);
                    }
                    continue;
                }
            }
        } else if let TermData::App(Symbol::Named(name), args) = terms.get(literal) {
            if name == "=" && args.len() == 2 {
                // Literal false ⟺ the equality FAILS. Recorded as the
                // equality it negates; `disequality_branches` turns that into
                // the two ℤ branches. Never pushed to `base.rows` — the
                // hypothesis contains the DISEQUALITY, not the equality.
                //
                // A VARIABLE-FREE form is declined: `int_linear_diff` returns
                // an empty map for `(= a a)` at ANY sort (the two sides cancel
                // before the `Sort::Int` check can run on anything), and the
                // resulting `0 != 0` split is a reflexivity tautology, not an
                // integer lattice fact. Leaving it to the reflexivity and
                // ground-evaluation rules that own it keeps this rule's reach
                // exactly what its soundness argument describes.
                if let Some(eq) = int_equality_row(terms, args[0], args[1]) {
                    if !eq.form.is_empty() {
                        base.diseq_splits.push(eq);
                    }
                }
                continue;
            }
        }
        if let Some(row) = literal_false_ge_row(terms, literal) {
            base.rows.ges.push(row);
        }
        if base.rows.len() > MAX_GUARDED_ROWS {
            return None;
        }
    }
    Some(base)
}

/// The `≥`-oriented constraint that holds when `literal` is FALSE, or `None`.
fn literal_false_ge_row(terms: &TermStore, literal: TermId) -> Option<GeRow> {
    let (coeffs, is_upper, value) = super::lia::parse_int_bound(terms, literal)?;
    Some(ge_row(coeffs, is_upper, value))
}

fn ge_row(coeffs: Coeffs, is_upper: bool, value: BigInt) -> GeRow {
    if is_upper {
        GeRow {
            form: coeffs.into_iter().map(|(v, c)| (v, -c)).collect(),
            bound: -value,
        }
    } else {
        GeRow {
            form: coeffs,
            bound: value,
        }
    }
}

/// Whether the branch's rows are unsatisfiable over ℤ by the certified means
/// described in the module docs. `false` is a DECLINE, never a satisfiability
/// claim.
fn branch_refuted(mut rows: Rows) -> bool {
    // (1) Equality substitution to fixpoint; each round removes one equality.
    let max_rounds = rows.eqs.len();
    for _ in 0..max_rounds {
        let Some((index, pivot)) = rows.eqs.iter().enumerate().find_map(|(i, eq)| {
            eq.form
                .iter()
                .find(|(_, c)| c.abs() == BigInt::from(1))
                .map(|(v, _)| (i, *v))
        }) else {
            break;
        };
        let eq = rows.eqs.swap_remove(index);
        let k = eq.form[&pivot].clone(); // ±1
        let mut rest = eq.form.clone();
        rest.remove(&pivot);
        // k·pivot = bound − rest  ⟹  pivot = (bound − rest)/k, exact since
        // k = ±1. A row with m·pivot gains (m/k)·(bound − rest).
        let substitute = |form: &Coeffs, bound: &BigInt| -> (Coeffs, BigInt) {
            let Some(m) = form.get(&pivot) else {
                return (form.clone(), bound.clone());
            };
            let scale = m / &k; // exact: k = ±1
            let mut out: Coeffs = form.clone();
            out.remove(&pivot);
            for (v, c) in &rest {
                let delta = -(&scale) * c;
                let entry = out.entry(*v).or_insert_with(BigInt::zero);
                *entry += delta;
                if entry.is_zero() {
                    out.remove(v);
                }
            }
            (out, bound - &scale * &eq.bound)
        };
        let mut next = Rows::default();
        for other in &rows.eqs {
            let (form, bound) = substitute(&other.form, &other.bound);
            next.eqs.push(EqRow { form, bound });
        }
        for other in &rows.ges {
            let (form, bound) = substitute(&other.form, &other.bound);
            next.ges.push(GeRow { form, bound });
        }
        rows = next;
    }
    // (2) Ground equality residue `0 = b`, `b ≠ 0` refutes; residual
    // equalities become row pairs.
    let mut ges = rows.ges;
    for eq in rows.eqs {
        if eq.form.is_empty() {
            if !eq.bound.is_zero() {
                return true;
            }
            continue;
        }
        ges.push(GeRow {
            form: eq.form.iter().map(|(v, c)| (*v, -c)).collect(),
            bound: -&eq.bound,
        });
        ges.push(GeRow {
            form: eq.form,
            bound: eq.bound,
        });
    }
    if ges.len() > MAX_GUARDED_ROWS {
        return false;
    }
    // (3) Pool of literal rows.
    let mut pool = BoundPool::default();
    for row in &ges {
        if row.form.is_empty() {
            if row.bound.is_positive() {
                return true; // 0 ≥ b > 0
            }
            continue;
        }
        pool.insert(row);
    }
    if pool.find_gap() {
        return true;
    }
    // (4) Canonical two-row eliminations.
    for (i, left) in ges.iter().enumerate() {
        for right in ges.iter().skip(i + 1) {
            for var in left.form.keys() {
                let Some(right_coeff) = right.form.get(var) else {
                    continue;
                };
                let left_coeff = &left.form[var];
                if left_coeff.is_negative() == right_coeff.is_negative() {
                    continue;
                }
                let g = left_coeff.abs().gcd(&right_coeff.abs());
                let left_multiplier = right_coeff.abs() / &g;
                let right_multiplier = left_coeff.abs() / &g;
                let mut form: Coeffs = BTreeMap::new();
                for (v, c) in &left.form {
                    form.insert(*v, c * &left_multiplier);
                }
                for (v, c) in &right.form {
                    let scaled = c * &right_multiplier;
                    let entry = form.entry(*v).or_insert_with(BigInt::zero);
                    *entry += scaled;
                    if entry.is_zero() {
                        form.remove(v);
                    }
                }
                let bound = &left.bound * &left_multiplier + &right.bound * &right_multiplier;
                if form.is_empty() {
                    if bound.is_positive() {
                        return true; // ground 0 ≥ b > 0
                    }
                    continue;
                }
                pool.insert(&GeRow { form, bound });
            }
        }
    }
    pool.find_gap()
}

/// The tightest lower/upper bound seen per canonical form.
#[derive(Default)]
struct BoundPool {
    groups: BTreeMap<Coeffs, (Option<BigInt>, Option<BigInt>)>,
}

impl BoundPool {
    fn insert(&mut self, row: &GeRow) {
        let leading_negative = row.form.values().next().is_some_and(BigInt::is_negative);
        let (form, is_upper, value): (Coeffs, bool, BigInt) = if leading_negative {
            (
                row.form.iter().map(|(v, c)| (*v, -c)).collect(),
                true,
                -row.bound.clone(),
            )
        } else {
            (row.form.clone(), false, row.bound.clone())
        };
        let (lower, upper) = self.groups.entry(form).or_default();
        let slot = if is_upper { upper } else { lower };
        let tighter = slot.as_ref().is_none_or(|current| {
            if is_upper {
                &value < current
            } else {
                &value > current
            }
        });
        if tighter {
            *slot = Some(value);
        }
    }

    fn find_gap(&self) -> bool {
        for (form, (lower, upper)) in &self.groups {
            let (Some(lower), Some(upper)) = (lower, upper) else {
                continue;
            };
            let mut gcd = BigInt::zero();
            for coeff in form.values() {
                gcd = gcd.gcd(&coeff.abs());
            }
            if !gcd.is_positive() {
                continue;
            }
            if &gcd * lower.div_ceil(&gcd) > *upper {
                return true;
            }
        }
        false
    }
}

include!("lia_guarded_split/case_split.rs");
