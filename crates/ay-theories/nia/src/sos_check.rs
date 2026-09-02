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

mod translation;

use ay_core::term::TermId;
use ay_core::{TheoryLit, TheoryResult};

use self::translation::is_nonlinear;
use crate::sos::MultiConstraint;
use crate::NiaSolver;

/// Cap on the number of distinct variables the pre-phase considers. Mirrors
/// [`crate::sos`]'s internal `MAX_VARS`; the degree-2 LP grows superlinearly in
/// the variable count, so above this the search declines rather than stall.
const MAX_SOS_VARS: usize = 8;

/// Outcome of translating the whole asserted literal set into the polynomial
/// fragment used by the SOS search.
enum SosFragment {
    /// A deterministic translation resource bound was exhausted. The entire
    /// SOS attempt declines; a prefix is never mistaken for a complete pass.
    Exhausted,
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
            SosFragment::Exhausted => None,
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
            SosFragment::Exhausted => None,
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

    /// All asserted literals as a `TheoryResult::Unsat` conflict clause. The full
    /// asserted set is a sound (if not necessarily minimal) UNSAT core for a
    /// refutation that may weaken the system by skipping atoms.
    fn all_asserted_lits(&self) -> Vec<TheoryLit> {
        self.asserted
            .iter()
            .map(|&(term, value)| TheoryLit { term, value })
            .collect()
    }
}

#[cfg(test)]
mod tests {
    use crate::sos::budget::{
        MAX_SOS_ASSERTED_LITERALS, MAX_SOS_COEFFICIENT_BITS, MAX_SOS_TERM_DEPTH,
    };
    use crate::NiaSolver;
    use ay_core::term::{Symbol, TermStore};
    use ay_core::{Sort, TheoryResult, TheorySolver};
    use num_bigint::BigInt;
    use num_rational::BigRational;

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
        // The emitted step must be a rule the Alethe checker implements; the
        // Positivstellensatz payload survives as line comments.
        assert!(rendered.contains(":rule hole"));
        assert!(!rendered.contains(":rule nia_positivstellensatz"));
        assert!(rendered.contains("; ay-nia Positivstellensatz certificate"));
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

    #[test]
    fn asserted_literal_limit_declines_without_storing_a_prefix_certificate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let difference = terms.mk_sub(vec![x, y]);
        let square = terms.mk_mul(vec![difference, difference]);
        let zero = terms.mk_int(BigInt::from(0));
        let contradiction = terms.mk_lt(square, zero);

        let mut solver = NiaSolver::new(&terms);
        solver.asserted = vec![(contradiction, true); MAX_SOS_ASSERTED_LITERALS + 1];
        assert!(solver.try_sos_positivstellensatz_unsat().is_none());
        assert!(!solver.took_sos_unsat_certificate());
    }

    #[test]
    fn deep_term_exhaustion_declines_the_whole_attempt() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let difference = terms.mk_sub(vec![x, y]);
        let square = terms.mk_mul(vec![difference, difference]);
        let zero = terms.mk_int(BigInt::from(0));
        let contradiction = terms.mk_lt(square, zero);

        let mut deep = x;
        for _ in 0..=MAX_SOS_TERM_DEPTH {
            deep = terms.mk_app(Symbol::named("+"), [deep], Sort::Int);
        }
        let over_limit = terms.mk_ge(deep, zero);

        let mut solver = NiaSolver::new(&terms);
        solver.asserted = vec![(contradiction, true), (over_limit, true)];
        assert!(solver.try_sos_positivstellensatz_unsat().is_none());
        assert!(!solver.took_sos_unsat_certificate());
    }

    #[test]
    fn coefficient_exhaustion_declines_the_whole_attempt() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let difference = terms.mk_sub(vec![x, y]);
        let square = terms.mk_mul(vec![difference, difference]);
        let zero = terms.mk_int(BigInt::from(0));
        let contradiction = terms.mk_lt(square, zero);
        let huge = terms.mk_int(BigInt::from(1u8) << MAX_SOS_COEFFICIENT_BITS as usize);
        let over_limit = terms.mk_ge(x, huge);

        let mut solver = NiaSolver::new(&terms);
        solver.asserted = vec![(contradiction, true), (over_limit, true)];
        assert!(solver.try_sos_positivstellensatz_unsat().is_none());
        assert!(!solver.took_sos_unsat_certificate());
    }

    #[test]
    fn rational_coefficient_exhaustion_declines_before_translation_clone() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Real);
        let y = terms.mk_var("y", Sort::Real);
        let difference = terms.mk_sub(vec![x, y]);
        let square = terms.mk_mul(vec![difference, difference]);
        let zero = terms.mk_rational(BigRational::from_integer(BigInt::from(0)));
        let contradiction = terms.mk_lt(square, zero);
        let huge = terms.mk_rational(BigRational::new(
            BigInt::from(1u8) << MAX_SOS_COEFFICIENT_BITS as usize,
            BigInt::from(3u8),
        ));
        let over_limit = terms.mk_ge(x, huge);

        let mut solver = NiaSolver::new(&terms);
        solver.asserted = vec![(contradiction, true), (over_limit, true)];
        assert!(solver.try_sos_positivstellensatz_unsat().is_none());
        assert!(!solver.took_sos_unsat_certificate());
    }

    #[test]
    fn variable_limit_declines_without_a_prefix_certificate() {
        let mut terms = TermStore::new();
        let variables: Vec<_> = (0..=super::MAX_SOS_VARS)
            .map(|index| terms.mk_var(format!("x{index}"), Sort::Int))
            .collect();
        let difference = terms.mk_sub(vec![variables[0], variables[1]]);
        let square = terms.mk_mul(vec![difference, difference]);
        let zero = terms.mk_int(BigInt::from(0));
        let contradiction = terms.mk_lt(square, zero);
        let mut assertions = vec![(contradiction, true)];
        assertions.extend(
            variables
                .iter()
                .map(|&variable| (terms.mk_ge(variable, zero), true)),
        );

        let mut solver = NiaSolver::new(&terms);
        solver.asserted = assertions;
        assert!(solver.try_sos_positivstellensatz_unsat().is_none());
        assert!(!solver.took_sos_unsat_certificate());
    }

    #[test]
    fn unsupported_conjunct_keeps_retained_verified_contradiction() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let difference = terms.mk_sub(vec![x, y]);
        let square = terms.mk_mul(vec![difference, difference]);
        let zero = terms.mk_int(BigInt::from(0));
        let contradiction = terms.mk_lt(square, zero);
        let opaque = terms.mk_app(Symbol::named("opaque"), [x], Sort::Int);
        let unsupported = terms.mk_ge(opaque, zero);

        let mut solver = NiaSolver::new(&terms);
        solver.asserted = vec![(unsupported, true), (contradiction, true)];
        assert!(matches!(
            solver.try_sos_positivstellensatz_unsat(),
            Some(TheoryResult::Unsat(_))
        ));
        let certificate = solver
            .last_unsat_certificate
            .as_ref()
            .expect("retained nonlinear contradiction must carry a certificate");
        let super::SosFragment::System { constraints, .. } = solver.build_sos_fragment() else {
            panic!("unsupported conjunct must be a sound weakening");
        };
        assert_eq!(constraints.len(), 1);
        assert!(certificate.verify(&constraints).is_ok());
    }

    #[test]
    fn unsupported_only_fragment_cannot_mint_a_certificate() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let opaque = terms.mk_app(Symbol::named("opaque"), [x], Sort::Int);
        let atom = terms.mk_ge(opaque, zero);

        let mut solver = NiaSolver::new(&terms);
        solver.asserted = vec![(atom, true)];
        assert!(solver.try_sos_positivstellensatz_unsat().is_none());
        assert!(!solver.took_sos_unsat_certificate());
    }
}
