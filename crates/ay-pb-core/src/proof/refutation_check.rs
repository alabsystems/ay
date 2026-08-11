// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! In-production cutting-planes refutation SELF-CHECK.
//!
//! This module checks the pseudo-Boolean certificate algebra for addition,
//! scaling, division, and contradictory bounds. It replays a
//! cutting-planes (Chvatal-Gomory) derivation over the ORIGINAL instance's
//! constraints and accepts it **only** if the derivation ends in the
//! contradiction `0 >= c` with `c >= 1`.
//!
//! # Why this exists
//!
//! AY's structural-UNSAT paths (notably the GF(2) parity refutation in
//! [`crate::optimize::gf2_parity`]) used to *assert* `s UNSATISFIABLE` from an
//! engine decision that was only validated empirically (RoundingSat + VeriPB),
//! never self-checked at runtime. This checker closes that gap BY CONSTRUCTION:
//! the emitter must hand us a concrete derivation, we recompute every step from
//! the inputs, and a refutation that does not actually reduce to `0 >= 1` is
//! REJECTED. A rejected refutation must downgrade the answer to `s UNKNOWN`
//! (AY's prefer-no-unchecked-answer / fail-closed design) — never an unchecked
//! `UNSAT`.
//!
//! # Soundness model
//!
//! Every constraint is held in normalized `>=` form over **plain** boolean
//! variables (`x_v in {0,1}`):
//!
//! ```text
//!   sum_v coeff[v] * x_v  >=  rhs
//! ```
//!
//! A negated literal `a * ~x = a - a*x` is normalized away: it contributes
//! `-a` to `coeff[x]` and `-a` to `rhs` (move the constant `a` to the right).
//! The three derivation rules are exactly the kernel arrows:
//!
//! * **add** (`impliedGe_add`): if `A >= a` and `B >= b` hold then
//!   `A + B >= a + b` holds. Implemented by [`LinConstraint::add`].
//! * **scale** (`impliedGe_scale`): for `k >= 1`, `A >= a` implies
//!   `k*A >= k*a`. Implemented by [`LinConstraint::scale`].
//! * **divide** (`impliedGe_division`): for `d >= 1`, `A >= a` implies
//!   `sum ceil(coeff/d) x >= ceil(a/d)`. Sound for any integer coefficients
//!   because `ceil(c/d) >= c/d` and `x >= 0`, and the LHS is integral so it
//!   rounds the RHS up. Implemented by [`LinConstraint::divide_ceil`].
//!
//! The terminal rule (`pb_unsat_of_contradictory_bounds`): a constraint whose
//! LHS is empty (all coefficients zero) with `rhs >= 1` is `0 >= 1`, which no
//! assignment satisfies — so the input set from which it was derived is UNSAT.
//!
//! The checker recomputes each step from scratch, so a buggy emitter cannot
//! smuggle a false refutation past it: only the *checker's* correctness is
//! trusted, and that correctness is the kernel algebra mirrored here.

use std::collections::BTreeMap;

use crate::types::{PbConstraint, PbRel};

/// A pseudo-Boolean constraint in normalized greater-or-equal form over plain
/// boolean variables: `sum_v coeff[v] * x_v >= rhs`. Zero coefficients are never
/// stored (they are pruned on every operation), so an empty `coeff` map denotes
/// the constant LHS `0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LinConstraint {
    /// Per-(plain)-variable integer coefficient. Variables are 1-indexed, as in
    /// [`crate::types::PbLit`]. Entries with value `0` are never present.
    coeff: BTreeMap<u32, i128>,
    /// Right-hand side lower bound.
    rhs: i128,
}

impl LinConstraint {
    /// The constant `0 >= rhs` constraint (empty LHS).
    fn constant(rhs: i128) -> Self {
        Self {
            coeff: BTreeMap::new(),
            rhs,
        }
    }

    /// Inserts `delta` into variable `var`'s coefficient, pruning to keep the
    /// no-zero invariant. Returns `None` on `i128` overflow (fail-closed).
    fn add_coeff(&mut self, var: u32, delta: i128) -> Option<()> {
        if delta == 0 {
            return Some(());
        }
        let entry = self.coeff.entry(var).or_insert(0);
        *entry = entry.checked_add(delta)?;
        if *entry == 0 {
            self.coeff.remove(&var);
        }
        Some(())
    }

    /// Normalizes a single linear PB constraint (`>=`) into a [`LinConstraint`].
    ///
    /// Returns `None` for any constraint the checker does not model exactly: a
    /// non-`Ge` relation, a non-linear term (`lits.len() != 1`), a zero variable
    /// id, or an arithmetic overflow. Callers must expand `=` rows into the two
    /// `>=` halves themselves (see [`pb_eq_halves`]).
    fn from_ge(c: &PbConstraint) -> Option<Self> {
        if c.rel != PbRel::Ge {
            return None;
        }
        let mut out = Self::constant(c.rhs);
        for term in &c.terms {
            if term.lits.len() != 1 {
                return None; // non-linear term: not modeled
            }
            let lit = term.lits[0];
            if lit.var == 0 {
                return None;
            }
            if lit.negated {
                // a * ~x = a - a*x  ⇒  coeff[x] -= a, rhs -= a.
                out.add_coeff(lit.var, term.coeff.checked_neg()?)?;
                out.rhs = out.rhs.checked_sub(term.coeff)?;
            } else {
                out.add_coeff(lit.var, term.coeff)?;
            }
        }
        Some(out)
    }

    /// `impliedGe_add`: pointwise sum of two `>=` facts.
    fn add(&self, other: &Self) -> Option<Self> {
        let mut out = self.clone();
        for (&var, &delta) in &other.coeff {
            out.add_coeff(var, delta)?;
        }
        out.rhs = out.rhs.checked_add(other.rhs)?;
        Some(out)
    }

    /// `impliedGe_scale`: multiply a `>=` fact by a positive scalar `k >= 1`.
    fn scale(&self, k: i128) -> Option<Self> {
        if k < 1 {
            return None;
        }
        let mut out = Self::constant(self.rhs.checked_mul(k)?);
        for (&var, &c) in &self.coeff {
            out.add_coeff(var, c.checked_mul(k)?)?;
        }
        Some(out)
    }

    /// `impliedGe_division`: divide by `d >= 1`, rounding every coefficient and
    /// the RHS UP (ceiling). Sound for arbitrary integer coefficients.
    fn divide_ceil(&self, d: i128) -> Option<Self> {
        if d < 1 {
            return None;
        }
        let mut out = Self::constant(ceil_div(self.rhs, d)?);
        for (&var, &c) in &self.coeff {
            out.add_coeff(var, ceil_div(c, d)?)?;
        }
        Some(out)
    }

    /// `impliedGe_saturate` (degree capping): for a constraint with every
    /// coefficient `>= 0` and degree `rhs = b >= 0`, replacing each coefficient
    /// `a_i` by `min(a_i, b)` preserves entailment over `0/1` variables (the
    /// kernel's `cut_saturate_sound`). Returns `None` (fail-closed) on any other
    /// shape — a negative coefficient or a negative degree — because the cap is
    /// only sound under the kernel's `0 <= a_i`, `0 <= b` side conditions.
    fn saturate(&self) -> Option<Self> {
        if self.rhs < 0 {
            return None;
        }
        let mut out = Self::constant(self.rhs);
        for (&var, &c) in &self.coeff {
            if c < 0 {
                return None;
            }
            out.add_coeff(var, c.min(self.rhs))?;
        }
        Some(out)
    }

    /// `pb_unsat_of_contradictory_bounds`: `true` iff this is `0 >= c` with
    /// `c >= 1` — an unsatisfiable constraint, hence a refutation.
    fn is_contradiction(&self) -> bool {
        self.coeff.is_empty() && self.rhs >= 1
    }

    /// The right-hand side (lower bound) of this normalized `>=` constraint.
    pub(crate) fn rhs(&self) -> i128 {
        self.rhs
    }

    /// Number of stored (non-zero) coefficients — the constraint's density. Used
    /// only to size the replay memory-budget guard; not part of the checker.
    pub(crate) fn width(&self) -> usize {
        self.coeff.len()
    }

    /// The sound boolean lower-bound axiom `x_v >= 0` (every `0/1` variable is
    /// non-negative). Used by the OPTIMUM certificate builder to lift a derived
    /// dual bound onto the exact objective linear form: adding `k * (x_v >= 0)`
    /// raises `coeff[v]` by `k >= 0` without changing the RHS, and is sound
    /// because `x_v >= 0` holds for every boolean assignment.
    pub(crate) fn var_geq_zero(var: u32) -> Self {
        let mut out = Self::constant(0);
        out.coeff.insert(var, 1);
        out
    }
}

/// `ceil(a / d)` for `d >= 1`, exact over `i128`; `None` only on the impossible
/// `i128::MIN.div_euclid` overflow shape (fail-closed).
fn ceil_div(a: i128, d: i128) -> Option<i128> {
    if d < 1 {
        return None;
    }
    let q = a.checked_div_euclid(d)?;
    let r = a.checked_rem_euclid(d)?;
    if r == 0 {
        Some(q)
    } else {
        q.checked_add(1)
    }
}

/// Expands an equality PB constraint `L = b` into its two `>=` halves
/// (`L >= b` and `-L >= -b`), each normalized. Returns `None` if either half is
/// not modeled (non-linear, etc.).
pub fn pb_eq_halves(c: &PbConstraint) -> Option<(LinConstraint, LinConstraint)> {
    if c.rel != PbRel::Eq {
        return None;
    }
    let ge = LinConstraint::from_ge(&PbConstraint {
        terms: c.terms.clone(),
        rel: PbRel::Ge,
        rhs: c.rhs,
    })?;
    // `-L >= -b`: negate every coefficient and the rhs.
    let mut le = LinConstraint::constant(ge.rhs.checked_neg()?);
    for (&var, &coeff) in &ge.coeff {
        le.add_coeff(var, coeff.checked_neg()?)?;
    }
    Some((ge, le))
}

/// Normalizes a `>=` PB constraint, exposed for refutation builders.
pub fn pb_ge(c: &PbConstraint) -> Option<LinConstraint> {
    LinConstraint::from_ge(c)
}

/// A single replayable cutting-planes derivation step. Each step appends one new
/// constraint to the working database; operands reference earlier database
/// entries (inputs first, then prior derived constraints) by 0-based index.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefStep {
    /// `impliedGe_add`: database[i] + database[j].
    Add(usize, usize),
    /// `impliedGe_scale`: database[i] * k (k >= 1).
    Scale(usize, i128),
    /// `impliedGe_division`: ceil-divide database[i] by d (d >= 1).
    Divide(usize, i128),
    /// `impliedGe_saturate`: cap every coefficient of database[i] at its degree
    /// (only sound when all coefficients and the degree are non-negative).
    Saturate(usize),
}

/// A complete refutation: a list of input constraints (`>=` normalized) plus a
/// sequence of derivation steps that must terminate in `0 >= c` (`c >= 1`).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Refutation {
    /// Input constraints, already normalized to `>=` form. These are the AXIOMS
    /// the checker trusts as given (they must come from the instance's original
    /// constraints — see the builders in [`crate::optimize::gf2_parity`]).
    pub inputs: Vec<LinConstraint>,
    /// Derivation steps, applied in order; each appends one constraint.
    pub steps: Vec<RefStep>,
}

/// Why a refutation failed to self-check.
#[derive(Debug, Clone, PartialEq, Eq)]
pub enum RefError {
    /// A step referenced a database index that does not exist yet.
    BadRef {
        /// Index of the offending step.
        step: usize,
    },
    /// A rule's side condition or arithmetic failed (e.g. non-positive
    /// scalar/divisor, or `i128` overflow).
    BadStep {
        /// Index of the offending step.
        step: usize,
    },
    /// The derivation completed but the final constraint is not `0 >= c`
    /// (`c >= 1`), so it does not refute the inputs.
    NotContradiction,
    /// There were no steps at all to produce a derived contradiction.
    Empty,
}

impl Refutation {
    /// Replays the derivation from the inputs and returns `Ok(())` iff the LAST
    /// produced constraint is the contradiction `0 >= c` (`c >= 1`).
    ///
    /// The checker recomputes every step independently of how it was found, so a
    /// buggy or adversarial builder cannot get a non-refutation accepted.
    pub fn check(&self) -> Result<(), RefError> {
        let last = replay_derivation(&self.inputs, &self.steps)?;
        if last.is_contradiction() {
            Ok(())
        } else {
            Err(RefError::NotContradiction)
        }
    }
}

/// Replays a cutting-planes derivation from `inputs` and returns the LAST
/// produced constraint, recomputing every step from scratch via the kernel
/// arrows (`add`/`scale`/`divide_ceil`/`saturate`). Shared by the UNSAT
/// refutation checker ([`Refutation::check`]) and the OPTIMUM lower-bound
/// checker (`crate::proof::optimum_check`). Returns [`RefError::Empty`] when
/// there are no steps (no derived constraint to inspect).
pub(crate) fn replay_derivation(
    inputs: &[LinConstraint],
    steps: &[RefStep],
) -> Result<LinConstraint, RefError> {
    if steps.is_empty() {
        return Err(RefError::Empty);
    }
    let mut db: Vec<LinConstraint> = inputs.to_vec();
    for (idx, step) in steps.iter().enumerate() {
        let derived = match *step {
            RefStep::Add(i, j) => {
                let a = db.get(i).ok_or(RefError::BadRef { step: idx })?;
                let b = db.get(j).ok_or(RefError::BadRef { step: idx })?;
                a.add(b).ok_or(RefError::BadStep { step: idx })?
            }
            RefStep::Scale(i, k) => {
                let a = db.get(i).ok_or(RefError::BadRef { step: idx })?;
                a.scale(k).ok_or(RefError::BadStep { step: idx })?
            }
            RefStep::Divide(i, d) => {
                let a = db.get(i).ok_or(RefError::BadRef { step: idx })?;
                a.divide_ceil(d).ok_or(RefError::BadStep { step: idx })?
            }
            RefStep::Saturate(i) => {
                let a = db.get(i).ok_or(RefError::BadRef { step: idx })?;
                a.saturate().ok_or(RefError::BadStep { step: idx })?
            }
        };
        db.push(derived);
    }
    // `db` is non-empty here (inputs may be empty but steps >= 1 appended).
    Ok(db.last().expect("at least one derived step").clone())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::types::{PbLit, PbTerm};

    fn term(coeff: i128, var: u32, negated: bool) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![PbLit { var, negated }],
        }
    }

    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn eq(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Eq,
            rhs,
        }
    }

    #[test]
    fn negated_literal_is_normalized_into_plain_form() {
        // 3*~x1 + 2*x2 >= 4  ==  -3 x1 + 2 x2 >= 1.
        let c = ge(vec![term(3, 1, true), term(2, 2, false)], 4);
        let lin = LinConstraint::from_ge(&c).expect("linear, modeled");
        assert_eq!(lin.coeff.get(&1), Some(&-3));
        assert_eq!(lin.coeff.get(&2), Some(&2));
        assert_eq!(lin.rhs, 1);
    }

    #[test]
    fn nonlinear_term_is_rejected() {
        let c = PbConstraint {
            terms: vec![PbTerm {
                coeff: 1,
                lits: vec![
                    PbLit {
                        var: 1,
                        negated: false,
                    },
                    PbLit {
                        var: 2,
                        negated: false,
                    },
                ],
            }],
            rel: PbRel::Ge,
            rhs: 1,
        };
        assert!(LinConstraint::from_ge(&c).is_none());
    }

    #[test]
    fn divide_ceil_rounds_rhs_up_and_handles_negative_coeffs() {
        // (2 x1 - 4 x2 >= 3) / 2  ==  x1 - 2 x2 >= 2  (ceil(3/2)=2, ceil(-4/2)=-2).
        let c = ge(vec![term(2, 1, false), term(-4, 2, false)], 3);
        let lin = LinConstraint::from_ge(&c).unwrap();
        let d = lin.divide_ceil(2).unwrap();
        assert_eq!(d.coeff.get(&1), Some(&1));
        assert_eq!(d.coeff.get(&2), Some(&-2));
        assert_eq!(d.rhs, 2);
    }

    /// The canonical handshake / parity refutation over a 3-cycle of equalities:
    ///   A: x1 + x2 = 1, B: x2 + x3 = 1, C: x1 + x3 = 1.
    /// Sum the three `>=` halves: 2x1+2x2+2x3 >= 3; sum the three `<=` halves:
    /// -2x1-2x2-2x3 >= -3; ceil-divide each by 2: x1+x2+x3 >= 2 and
    /// -x1-x2-x3 >= -1; add: 0 >= 1. (This system is genuinely UNSAT.)
    fn three_cycle_inputs() -> Vec<LinConstraint> {
        let a = eq(vec![term(1, 1, false), term(1, 2, false)], 1);
        let b = eq(vec![term(1, 2, false), term(1, 3, false)], 1);
        let c = eq(vec![term(1, 1, false), term(1, 3, false)], 1);
        let (a_ge, a_le) = pb_eq_halves(&a).unwrap();
        let (b_ge, b_le) = pb_eq_halves(&b).unwrap();
        let (c_ge, c_le) = pb_eq_halves(&c).unwrap();
        vec![a_ge, a_le, b_ge, b_le, c_ge, c_le]
    }

    #[test]
    fn parity_contradiction_checks_positive() {
        // inputs: 0:a_ge 1:a_le 2:b_ge 3:b_le 4:c_ge 5:c_le
        let inputs = three_cycle_inputs();
        let steps = vec![
            RefStep::Add(0, 2),    // 6: a_ge + b_ge
            RefStep::Add(6, 4),    // 7: + c_ge  => 2x1+2x2+2x3 >= 3
            RefStep::Add(1, 3),    // 8: a_le + b_le
            RefStep::Add(8, 5),    // 9: + c_le  => -2x1-2x2-2x3 >= -3
            RefStep::Divide(7, 2), // 10: x1+x2+x3 >= 2
            RefStep::Divide(9, 2), // 11: -x1-x2-x3 >= -1
            RefStep::Add(10, 11),  // 12: 0 >= 1
        ];
        let refutation = Refutation { inputs, steps };
        assert_eq!(refutation.check(), Ok(()));
    }

    // ------- NEGATIVE CONTROLS: a refutation that does NOT reduce to 0>=1
    // MUST be rejected. -------

    #[test]
    fn negative_control_tampered_divisor_is_rejected() {
        // Same derivation but divide by 3 instead of 2: the halves no longer
        // cancel to 0 >= 1, so the checker MUST reject.
        let inputs = three_cycle_inputs();
        let steps = vec![
            RefStep::Add(0, 2),
            RefStep::Add(6, 4),
            RefStep::Add(1, 3),
            RefStep::Add(8, 5),
            RefStep::Divide(7, 3), // WRONG divisor
            RefStep::Divide(9, 3),
            RefStep::Add(10, 11),
        ];
        let refutation = Refutation { inputs, steps };
        assert_eq!(refutation.check(), Err(RefError::NotContradiction));
    }

    #[test]
    fn negative_control_incomplete_derivation_is_rejected() {
        // Stop before producing the contradiction: last constraint is x1+x2+x3>=2,
        // which is NOT 0 >= 1.
        let inputs = three_cycle_inputs();
        let steps = vec![
            RefStep::Add(0, 2),
            RefStep::Add(6, 4),
            RefStep::Divide(7, 2), // ends at x1+x2+x3 >= 2
        ];
        let refutation = Refutation { inputs, steps };
        assert_eq!(refutation.check(), Err(RefError::NotContradiction));
    }

    #[test]
    fn negative_control_non_positive_scalar_is_rejected() {
        let inputs = three_cycle_inputs();
        let steps = vec![RefStep::Scale(0, 0)];
        let refutation = Refutation { inputs, steps };
        assert_eq!(refutation.check(), Err(RefError::BadStep { step: 0 }));
    }

    #[test]
    fn negative_control_out_of_range_reference_is_rejected() {
        let inputs = three_cycle_inputs();
        let steps = vec![RefStep::Add(0, 99)];
        let refutation = Refutation { inputs, steps };
        assert_eq!(refutation.check(), Err(RefError::BadRef { step: 0 }));
    }

    #[test]
    fn negative_control_empty_derivation_is_rejected() {
        let refutation = Refutation {
            inputs: three_cycle_inputs(),
            steps: vec![],
        };
        assert_eq!(refutation.check(), Err(RefError::Empty));
    }

    #[test]
    fn negative_control_satisfiable_inputs_cannot_be_refuted() {
        // x1 + x2 >= 1 and -x1 - x2 >= -2 (i.e. x1+x2 <= 2): satisfiable.
        // No sound sequence of add/scale/divide can derive 0 >= 1; a builder that
        // tries (e.g. just adds them) gets a true but non-contradictory fact.
        let a = ge(vec![term(1, 1, false), term(1, 2, false)], 1);
        let b = ge(vec![term(-1, 1, false), term(-1, 2, false)], -2);
        let inputs = vec![
            LinConstraint::from_ge(&a).unwrap(),
            LinConstraint::from_ge(&b).unwrap(),
        ];
        // 0:a 1:b ; add -> 0 >= -1, which is NOT 0 >= 1.
        let steps = vec![RefStep::Add(0, 1)];
        let refutation = Refutation { inputs, steps };
        assert_eq!(refutation.check(), Err(RefError::NotContradiction));
    }
}
