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
//! * The pre-phase returns [`TheoryResult::Unsat`] (backed by an
//!   independently re-checkable degree-2 Positivstellensatz certificate, or a
//!   syntactically-false atom), terminal `Unknown` on cancellation, or `None`.
//!   It NEVER emits `Sat` and NEVER turns a
//!   satisfiable system into `Unsat`.
//! * A SOS/Positivstellensatz refutation certifies infeasibility over the
//!   **reals**; since ℤ ⊂ ℝ, real-infeasible ⇒ integer-infeasible, so the
//!   certificate is a valid witness of NIA UNSAT (see [`crate::sos`]).
//! * Out-of-fragment atoms (division, modulo, unparseable comparisons) are
//!   SKIPPED. Dropping constraints only WEAKENS the system, and a refutation of a
//!   *subset* refutes the whole conjunction — so skipping is sound *for UNSAT*.
//!   It is never used to claim SAT (the pre-phase has no SAT path).
//! * Any emitted certificate has already passed the module's independent
//!   `verify` re-check ([`crate::sos::SosCertificate::verify_with_progress`]) inside
//!   [`crate::sos::search_with_progress`]; a tampered certificate is rejected there.

#[cfg(test)]
mod stop_tests;
mod translation;

use ay_core::term::TermId;
use ay_core::TheoryLit;
#[cfg(test)]
use ay_core::TheoryResult;

use self::translation::is_nonlinear;
use crate::sos::budget::SosProgress;
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

/// Keep a refused attempt distinct from ordinary incompleteness until its
/// caller decides whether to enter another cascade phase.
#[derive(Debug)]
pub(crate) enum SosAttempt {
    Declined,
    Interrupted,
    Refuted(Vec<TheoryLit>),
}

/// One asserted atom's cached translation outcome.
#[derive(Clone)]
pub(super) enum CachedSosAtom {
    Constraint(MultiConstraint),
    ConstTrue,
    ConstFalse,
    Unsupported,
}

/// Incremental SOS fragment cache: per-atom translations for a prefix
/// of `asserted`, aligned 1:1 by index, each with the cumulative
/// polynomial-budget counts and retained-term total AFTER that atom.
/// Translation is a pure function of the atom, its asserted value and
/// the cumulative budget, so a later build replays the prefix and
/// translates only newly appended atoms, resuming the budget from
/// the tip snapshot. `exhausted` records a deterministic budget
/// exhaustion at the atom just past the tip. Maintained in lockstep
/// with `asserted`: pop truncates both, reset clears both, and
/// `tip_asserted` lets a build detect (and discard) any desync.
#[derive(Default)]
pub(crate) struct SosFragmentCache {
    pub(super) entries: Vec<(CachedSosAtom, (usize, usize, usize), usize)>,
    pub(super) exhausted: bool,
    pub(super) tip_asserted: Option<(TermId, bool)>,
}

impl SosFragmentCache {
    /// Truncate to the (already truncated) asserted set after a scope
    /// pop, re-deriving the tip from the asserted entry the last cached
    /// translation corresponds to.
    pub(crate) fn truncate_to_asserted(&mut self, asserted: &[(TermId, bool)]) {
        self.entries.truncate(asserted.len());
        self.exhausted = false;
        self.tip_asserted = self
            .entries
            .len()
            .checked_sub(1)
            .and_then(|idx| asserted.get(idx))
            .copied();
    }
}

enum SosWitness {
    ConstFalse,
    Certificate(crate::sos::SosCertificate),
}

impl NiaSolver<'_> {
    /// Test convenience preserves the pre-phase interruption as an explicit Unknown.
    #[cfg(test)]
    pub(crate) fn try_sos_positivstellensatz_unsat(&mut self) -> Option<TheoryResult> {
        match self.try_sos_attempt() {
            SosAttempt::Refuted(conflict) => Some(TheoryResult::Unsat(conflict)),
            SosAttempt::Interrupted => Some(TheoryResult::Unknown),
            SosAttempt::Declined => None,
        }
    }

    /// A refused callback ends this check even if a live stop later clears.
    /// A refutation still requires a syntactically-false atom or a complete,
    /// independently checked SOS certificate; this lane never emits SAT.
    pub(crate) fn try_sos_attempt(&mut self) -> SosAttempt {
        let allow = || !self.should_timeout();
        let progress = SosProgress::new(&allow);
        let witness = self.find_sos_witness(&progress);
        if self.debug {
            if let Some(SosWitness::Certificate(cert)) = &witness {
                safe_eprintln!("[NIA] {}", cert.summary());
            }
        }
        let decision = witness.map(|witness| (witness, self.full_conflict_lits()));
        if !progress.poll() {
            return SosAttempt::Interrupted;
        }
        let Some((witness, conflict)) = decision else {
            return SosAttempt::Declined;
        };
        if let SosWitness::Certificate(cert) = witness {
            self.last_unsat_certificate = Some(cert);
        }
        SosAttempt::Refuted(conflict)
    }

    /// Build a certificate for an UNSAT already decided by another path.
    /// Refusal declines attachment without replacing that existing result.
    pub(crate) fn try_build_unsat_sos_certificate(&self) -> Option<crate::sos::SosCertificate> {
        let allow = || !self.should_timeout();
        let progress = SosProgress::new(&allow);
        let Some(SosWitness::Certificate(cert)) = self.find_sos_witness(&progress) else {
            return None;
        };
        progress.poll().then_some(cert)
    }

    fn find_sos_witness(&self, progress: &SosProgress<'_>) -> Option<SosWitness> {
        match self.build_sos_fragment_with_progress(progress) {
            SosFragment::Exhausted => None,
            SosFragment::ConstFalse => Some(SosWitness::ConstFalse),
            SosFragment::System { constraints, vars } => {
                if vars.is_empty() || vars.len() > MAX_SOS_VARS {
                    return None;
                }
                // Purely linear fragments add no decision power in this lane.
                if !constraints.iter().any(is_nonlinear) {
                    return None;
                }
                // No candidate reaches the caller without independent replay.
                crate::sos::search_with_progress(&constraints, &vars, progress)
                    .map(SosWitness::Certificate)
            }
        }
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

    /// The incremental fragment cache translates each asserted prefix
    /// once: repeat builds reuse it, appending translates only the new
    /// atom, and pop truncates it in lockstep with `asserted`.
    #[test]
    fn sos_fragment_cache_extends_and_truncates_with_asserted() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let zero = terms.mk_int(BigInt::from(0));
        let one = terms.mk_int(BigInt::from(1));
        let xx = terms.mk_mul(vec![x, x]);
        let a0 = terms.mk_ge(xx, zero); // x^2 >= 0
        let a1 = terms.mk_ge(x, one); // x >= 1
        let a2 = terms.mk_ge(y, one); // y >= 1

        let mut solver = NiaSolver::new(&terms);
        solver.assert_literal(a0, true);
        solver.assert_literal(a1, true);
        let super::SosFragment::System { constraints, .. } = solver.build_sos_fragment() else {
            panic!("satisfiable fragment must build");
        };
        assert_eq!(constraints.len(), 2);
        assert_eq!(solver.sos_fragment_cache.borrow().entries.len(), 2);

        // Identical rebuild: no new translations.
        let super::SosFragment::System { constraints, .. } = solver.build_sos_fragment() else {
            panic!("cached rebuild must succeed");
        };
        assert_eq!(constraints.len(), 2);
        assert_eq!(solver.sos_fragment_cache.borrow().entries.len(), 2);

        // Append under a scope: exactly one more entry.
        solver.push();
        solver.assert_literal(a2, true);
        let super::SosFragment::System { constraints, .. } = solver.build_sos_fragment() else {
            panic!("extended fragment must build");
        };
        assert_eq!(constraints.len(), 3);
        assert_eq!(solver.sos_fragment_cache.borrow().entries.len(), 3);

        // Pop truncates cache and asserted set together.
        solver.pop();
        assert_eq!(solver.sos_fragment_cache.borrow().entries.len(), 2);
        let super::SosFragment::System { constraints, .. } = solver.build_sos_fragment() else {
            panic!("post-pop fragment must build");
        };
        assert_eq!(constraints.len(), 2);
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
