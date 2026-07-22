// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! NIA rational SOS / Positivstellensatz UNSAT pre-phase (W3).
//!
//! A certificate-gated, **sound-for-UNSAT-only** decision pre-phase that
//! discharges coupled-multivariate NIA infeasibilities — cross-term / quadratic
//! form refutations like `(x−y)² < 0`, `x²+y² < 2xy`, checked_mul / overflow
//! bounds, box×box product monotonicity, and quadratic loop-invariant
//! infeasibilities — that the incremental-linearization check loop otherwise
//! leaves as `Unknown`.
//!
//! ## Soundness contract
//!
//! * The pre-phase returns ONLY [`TheoryResult::Unsat`] (backed by an
//!   independently re-checkable degree-2 Positivstellensatz certificate, or a
//!   syntactically-false atom) or `None`. It NEVER emits `Sat` and NEVER turns a
//!   satisfiable system into `Unsat`.
//! * A SOS/Positivstellensatz refutation certifies infeasibility over the
//!   **reals**; since ℤ ⊂ ℝ, real-infeasible ⇒ integer-infeasible, so the
//!   certificate is a valid witness of NIA UNSAT (see [`crate::sos`]).
//! * Out-of-fragment atoms (division, modulo, unparseable comparisons) are
//!   SKIPPED. Dropping constraints only WEAKENS the system, and a refutation of a
//!   *subset* refutes the whole conjunction — so skipping is sound *for UNSAT*.
//!   It is never used to claim SAT (the pre-phase has no SAT path).
//! * Any emitted certificate has already passed the module's independent
//!   `verify` re-check ([`crate::sos::SosCertificate::verify`]) inside
//!   [`crate::sos::search`]; a tampered certificate is rejected there.

use ay_core::term::{Constant, Symbol, TermData, TermId};
use ay_core::{TheoryLit, TheoryResult};
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::sos::{MultiConstraint, MultiPoly, Rel};
use crate::NiaSolver;

/// Cap on the number of distinct variables the pre-phase considers. Mirrors
/// [`crate::sos`]'s internal `MAX_VARS`; the degree-2 LP grows superlinearly in
/// the variable count, so above this the search declines rather than stall.
const MAX_SOS_VARS: usize = 8;

/// Classification of a single asserted atom for the SOS fragment.
enum NiaMultiAtom {
    /// A genuine `poly REL 0` constraint.
    Constraint(MultiConstraint),
    /// The atom is a constant `true` (vacuous — dropped from the system).
    ConstTrue,
    /// The atom is a constant `false` — the asserted conjunction is UNSAT.
    ConstFalse,
}

/// Outcome of translating the whole asserted literal set into the polynomial
/// fragment used by the SOS search.
enum SosFragment {
    /// Some asserted atom is syntactically false, so the conjunction is UNSAT
    /// outright (no polynomial certificate needed).
    ConstFalse,
    /// The (possibly weakened) constraint system and its sorted variable set.
    /// Atoms outside the polynomial fragment were SKIPPED — sound for UNSAT.
    System {
        constraints: Vec<MultiConstraint>,
        vars: Vec<TermId>,
    },
}

impl NiaSolver<'_> {
    /// Decision pre-phase: attempt to refute the current asserted set with a
    /// degree-2 rational Positivstellensatz certificate. Returns
    /// `Some(TheoryResult::Unsat(..))` when a certificate is found (and stored in
    /// `self.last_unsat_certificate`) or when an asserted atom is syntactically
    /// false; `None` otherwise. It NEVER returns `Sat`.
    pub(crate) fn try_sos_positivstellensatz_unsat(&mut self) -> Option<TheoryResult> {
        match self.build_sos_fragment() {
            SosFragment::ConstFalse => {
                // A syntactically-false asserted atom makes the whole conjunction
                // unsatisfiable. This is a genuine UNSAT (no SOS certificate is
                // attached for this degenerate, non-polynomial case).
                Some(TheoryResult::Unsat(self.all_asserted_lits()))
            }
            SosFragment::System { constraints, vars } => {
                if vars.is_empty() || vars.len() > MAX_SOS_VARS {
                    return None;
                }
                // Nonlinearity gate: the degree-2 SOS/Positivstellensatz search
                // only adds decision power when the system has a genuine
                // nonlinear term. Purely linear/univariate systems are already
                // decided completely by LIA and the univariate-integer decider,
                // so building the LP and calling `search` on them is pure
                // latency. Skip (return `None`) when no constraint is nonlinear.
                if !constraints.iter().any(is_nonlinear) {
                    return None;
                }
                // `search` runs the independent checker on its own output before
                // returning, so a `Some(cert)` here is already verified.
                let cert = crate::sos::search(&constraints, &vars)?;
                if self.debug {
                    safe_eprintln!("[NIA] {}", cert.summary());
                }
                self.last_unsat_certificate = Some(cert);
                Some(TheoryResult::Unsat(self.all_asserted_lits()))
            }
        }
    }

    /// Build a Positivstellensatz certificate for the current (already-refuted)
    /// asserted set, or `None` if the degree-2 rational search does not find one.
    /// Used to *attach* a replayable certificate to an UNSAT that some other NIA
    /// path proved. Returns the certificate without emitting a verdict. The
    /// returned certificate is guaranteed to have passed the independent checker
    /// ([`crate::sos::SosCertificate::verify`]).
    pub(crate) fn try_build_unsat_sos_certificate(&self) -> Option<crate::sos::SosCertificate> {
        match self.build_sos_fragment() {
            // A degenerate constant-false UNSAT has no polynomial refutation to
            // certify; leave the existing (non-SOS) UNSAT reason as-is.
            SosFragment::ConstFalse => None,
            SosFragment::System { constraints, vars } => {
                if vars.is_empty() || vars.len() > MAX_SOS_VARS {
                    return None;
                }
                // Same nonlinearity gate as the decision pre-phase: a linear /
                // univariate system was decided elsewhere and carries no
                // degree-2 Positivstellensatz certificate worth searching for.
                if !constraints.iter().any(is_nonlinear) {
                    return None;
                }
                crate::sos::search(&constraints, &vars)
            }
        }
    }

    /// Translate every asserted literal into the SOS polynomial fragment.
    ///
    /// Out-of-fragment atoms (unrecognized comparisons, `/`, `mod`, …) are
    /// SKIPPED: dropping a constraint only weakens the system, so any refutation
    /// of the retained subset still refutes the full conjunction. This is sound
    /// *for UNSAT only* and is never used to justify SAT.
    fn build_sos_fragment(&self) -> SosFragment {
        let mut constraints: Vec<MultiConstraint> = Vec::new();
        for &(atom, value) in &self.asserted {
            match self.atom_to_multi(atom, value) {
                Some(NiaMultiAtom::ConstFalse) => return SosFragment::ConstFalse,
                Some(NiaMultiAtom::ConstTrue) => {}
                Some(NiaMultiAtom::Constraint(c)) => constraints.push(c),
                // Out-of-fragment atom: SKIP (sound-for-UNSAT weakening).
                None => {}
            }
        }
        let mut vars: Vec<TermId> = Vec::new();
        for c in &constraints {
            for v in c.poly.variables() {
                if !vars.contains(&v) {
                    vars.push(v);
                }
            }
        }
        vars.sort_unstable_by_key(|t| t.0);
        SosFragment::System { constraints, vars }
    }

    /// All asserted literals as a `TheoryResult::Unsat` conflict clause. The full
    /// asserted set is a sound (if not necessarily minimal) UNSAT core for a
    /// refutation that may weaken the system by skipping atoms.
    fn all_asserted_lits(&self) -> Vec<TheoryLit> {
        self.asserted
            .iter()
            .map(|&(term, value)| TheoryLit { term, value })
            .collect()
    }

    /// Classify an asserted atom into a multivariate `poly REL 0` form, a
    /// constant truth value, or `None` if it is not a recognized arithmetic
    /// comparison / uses an unsupported operator.
    fn atom_to_multi(&self, atom: TermId, value: bool) -> Option<NiaMultiAtom> {
        let (rel0, lhs, rhs) = self.comparison_parts(atom)?;
        let rel = if value { rel0 } else { negate_rel(rel0) };
        let lhs_poly = self.term_to_multipoly(lhs)?;
        let rhs_poly = self.term_to_multipoly(rhs)?;
        let poly = lhs_poly.sub(&rhs_poly);
        if poly.variables().is_empty() {
            // Pure constant constraint.
            let sign = if poly.is_zero() {
                0
            } else {
                // Single constant term.
                rational_sign(&poly.terms[0].1)
            };
            if rel.holds_for_sign(sign) {
                Some(NiaMultiAtom::ConstTrue)
            } else {
                Some(NiaMultiAtom::ConstFalse)
            }
        } else {
            Some(NiaMultiAtom::Constraint(MultiConstraint { poly, rel }))
        }
    }

    /// Extract `(rel, lhs, rhs)` from a binary comparison atom, or `None` if the
    /// atom is not a recognized arithmetic comparison.
    fn comparison_parts(&self, atom: TermId) -> Option<(Rel, TermId, TermId)> {
        match self.terms.get(atom) {
            TermData::App(Symbol::Named(name), args) if args.len() == 2 => {
                let rel = match name.as_str() {
                    "<" => Rel::Lt,
                    "<=" => Rel::Le,
                    "=" => Rel::Eq,
                    ">=" => Rel::Ge,
                    ">" => Rel::Gt,
                    "distinct" | "!=" => Rel::Ne,
                    _ => return None,
                };
                Some((rel, args[0], args[1]))
            }
            _ => None,
        }
    }

    /// Convert an arithmetic term to a multivariate polynomial, or `None` for
    /// unsupported operators (`/`, `div`, `mod`, `abs`, transcendental, …).
    ///
    /// Mirrors `NraSolver::term_to_multipoly`. Variables are treated as real
    /// unknowns; since ℤ ⊂ ℝ, a real refutation over these polynomials is a valid
    /// integer refutation. `None` here causes the enclosing atom to be skipped
    /// (sound-for-UNSAT weakening).
    fn term_to_multipoly(&self, term: TermId) -> Option<MultiPoly> {
        match self.terms.get(term) {
            TermData::Const(Constant::Int(n)) => {
                Some(MultiPoly::constant(BigRational::from_integer(n.clone())))
            }
            TermData::Const(Constant::Rational(r)) => Some(MultiPoly::constant(r.0.clone())),
            TermData::Var(_, _) => Some(MultiPoly::var(term)),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" if !args.is_empty() => {
                    let mut acc = MultiPoly::zero();
                    for &a in args {
                        acc = acc.add(&self.term_to_multipoly(a)?);
                    }
                    Some(acc)
                }
                "-" if args.len() == 1 => Some(self.term_to_multipoly(args[0])?.neg()),
                "-" if args.len() >= 2 => {
                    let mut acc = self.term_to_multipoly(args[0])?;
                    for &a in &args[1..] {
                        acc = acc.sub(&self.term_to_multipoly(a)?);
                    }
                    Some(acc)
                }
                "*" if !args.is_empty() => {
                    let mut acc = MultiPoly::constant(BigRational::one());
                    for &a in args {
                        acc = acc.mul(&self.term_to_multipoly(a)?);
                    }
                    Some(acc)
                }
                _ => None,
            },
            _ => None,
        }
    }
}

/// True iff the constraint's polynomial contains a NONLINEAR monomial — a term
/// whose sorted variable multiset has total degree ≥ 2. `MultiPoly` encodes a
/// monomial as the sorted `Vec<TermId>` of its variable factors *with
/// multiplicity*, so `mono.len()` IS the total degree: `[]` is the constant term
/// (degree 0), `[x]` is linear (degree 1), and `[x, x]` (a squared variable) or
/// `[x, y]` (a cross-term) are nonlinear (degree ≥ 2). The SOS/Positivstellensatz
/// search only adds decision power when at least one constraint is nonlinear;
/// linear/univariate systems are already decided completely by LIA and the
/// univariate-integer decider, so running the search on them is pure latency.
fn is_nonlinear(c: &MultiConstraint) -> bool {
    c.poly.terms.iter().any(|(mono, _)| mono.len() >= 2)
}

/// Negate a comparison relation (used when an atom is asserted false).
fn negate_rel(rel: Rel) -> Rel {
    match rel {
        Rel::Lt => Rel::Ge,
        Rel::Le => Rel::Gt,
        Rel::Eq => Rel::Ne,
        Rel::Ge => Rel::Lt,
        Rel::Gt => Rel::Le,
        Rel::Ne => Rel::Eq,
    }
}

/// Sign of a rational: -1, 0, or +1.
fn rational_sign(r: &BigRational) -> i32 {
    if r.is_zero() {
        0
    } else if r.is_positive() {
        1
    } else {
        -1
    }
}

#[cfg(test)]
mod tests {
    use crate::NiaSolver;
    use ay_core::term::TermStore;
    use ay_core::{Sort, TheoryResult, TheorySolver};
    use num_bigint::BigInt;

    /// Mandatory test 1: `(x − y)² < 0` over integers is UNSAT via a certificate.
    #[test]
    fn sos_x_minus_y_squared_lt_zero_is_unsat_with_certificate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let diff = terms.mk_sub(vec![x, y]); // x - y
        let sq = terms.mk_mul(vec![diff, diff]); // (x - y) * (x - y)
        let zero = terms.mk_int(BigInt::from(0));
        let atom = terms.mk_lt(sq, zero); // (x - y)^2 < 0

        let mut solver = NiaSolver::new(&terms);
        solver.assert_literal(atom, true);

        let res = solver
            .try_sos_positivstellensatz_unsat()
            .expect("pre-phase must refute (x-y)^2 < 0");
        assert!(matches!(res, TheoryResult::Unsat(_)), "expected Unsat");
        assert!(
            solver.took_sos_unsat_certificate(),
            "UNSAT must carry an SOS certificate"
        );
        let rendered = solver
            .render_sos_unsat_certificate("t1")
            .expect("certificate renders");
        assert!(rendered.contains(":rule nia_positivstellensatz"));
    }

    /// Mandatory test 2: `x² + y² < 2xy` is UNSAT via a certificate
    /// (equivalent to `(x − y)² < 0`).
    #[test]
    fn sos_xx_plus_yy_lt_2xy_is_unsat_with_certificate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xx = terms.mk_mul(vec![x, x]);
        let yy = terms.mk_mul(vec![y, y]);
        let lhs = terms.mk_add(vec![xx, yy]); // x^2 + y^2
        let two = terms.mk_int(BigInt::from(2));
        let two_x_y = terms.mk_mul(vec![two, x, y]); // 2*x*y
        let atom = terms.mk_lt(lhs, two_x_y); // x^2 + y^2 < 2xy

        let mut solver = NiaSolver::new(&terms);
        solver.assert_literal(atom, true);

        let res = solver
            .try_sos_positivstellensatz_unsat()
            .expect("pre-phase must refute x^2+y^2 < 2xy");
        assert!(matches!(res, TheoryResult::Unsat(_)), "expected Unsat");
        assert!(
            solver.took_sos_unsat_certificate(),
            "UNSAT must carry an SOS certificate"
        );
    }

    /// Mandatory test 3 (SOUNDNESS GUARD): a SATISFIABLE nonlinear system
    /// (`x² ≥ 0 ∧ x ≥ 1`) must yield `None` from the pre-phase — never a false
    /// UNSAT.
    #[test]
    fn sos_declines_on_satisfiable_nonlinear_system() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let xx = terms.mk_mul(vec![x, x]);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let a0 = terms.mk_ge(xx, zero); // x^2 >= 0
        let a1 = terms.mk_ge(x, one); // x >= 1

        let mut solver = NiaSolver::new(&terms);
        solver.assert_literal(a0, true);
        solver.assert_literal(a1, true);

        assert!(
            solver.try_sos_positivstellensatz_unsat().is_none(),
            "satisfiable system must NOT be refuted by the SOS pre-phase"
        );
        assert!(
            !solver.took_sos_unsat_certificate(),
            "no certificate may be stored for a satisfiable system"
        );
    }

    /// Mandatory test 4 (TAMPER): an altered certificate fails the module's
    /// independent verification. Build a valid certificate via the pre-phase,
    /// then corrupt a multiplier and confirm `verify` rejects it.
    #[test]
    fn sos_tampered_certificate_fails_verification() {
        use crate::sos::{search, MultiConstraint, MultiPoly, Rel};
        use ay_core::term::TermId;
        use num_rational::BigRational;

        // Reconstruct the { x²+y² < 0 } system directly in the checker's rep and
        // obtain a valid certificate.
        let x = TermId(1);
        let y = TermId(2);
        let r = |n: i64| BigRational::from_integer(BigInt::from(n));
        let mut poly = MultiPoly::zero();
        poly.add_term(vec![x, x], r(1));
        poly.add_term(vec![y, y], r(1));
        let c0 = MultiConstraint { poly, rel: Rel::Lt };
        let constraints = vec![c0];
        let cert = search(&constraints, &[x, y]).expect("valid certificate for x^2+y^2<0");
        assert!(
            cert.verify(&constraints).is_ok(),
            "untampered cert verifies"
        );

        // Tamper: scale a constraint multiplier so the identity no longer holds.
        let mut tampered = cert.clone();
        assert!(!tampered.terms.is_empty(), "cert has a constraint term");
        tampered.terms[0].multiplier = &tampered.terms[0].multiplier + r(1);
        assert!(
            tampered.verify(&constraints).is_err(),
            "a tampered certificate MUST be rejected by independent verification"
        );
    }

    /// End-to-end: driving the full `check()` entry on `(x − y)² < 0` also
    /// yields UNSAT with the certificate surfaced through the public accessor.
    #[test]
    fn end_to_end_check_carries_certificate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let diff = terms.mk_sub(vec![x, y]);
        let sq = terms.mk_mul(vec![diff, diff]);
        let zero = terms.mk_int(BigInt::from(0));
        let atom = terms.mk_lt(sq, zero);

        let mut solver = NiaSolver::new(&terms);
        solver.assert_literal(atom, true);
        let res = solver.check();
        assert!(
            matches!(res, TheoryResult::Unsat(_)),
            "(x-y)^2 < 0 is UNSAT end-to-end"
        );
        assert!(
            solver.took_sos_unsat_certificate(),
            "the end-to-end UNSAT must carry an SOS certificate"
        );
    }
}
