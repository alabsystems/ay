//! Kani verification harnesses for NRA solver
//!
//! Copyright (c) 2026 Andrew Yates. Licensed under Apache-2.0.
//!
//! Verifies core properties of the NRA sign reasoning subsystem:
//! - sign_contradicts is a total, correct predicate over all SignConstraint variants
//! - check_sign_consistency detects conflicts when factor signs contradict monomial constraints
//! - propagate_monomial_signs correctly derives product signs from factor signs

#[cfg(kani)]
mod proofs {
    use crate::monomial::Monomial;
    use crate::sign::{self, SignConstraint};
    use ay_core::kani_compat::DetHashMap;
    use ay_core::term::TermId;

    // ========================================================================
    // sign_contradicts: exhaustive correctness
    // ========================================================================

    /// Verify sign_contradicts is correct for all SignConstraint variants
    /// and all valid sign values (-1, 0, 1).
    ///
    /// Property: sign_contradicts(C, s) = true iff the sign value s
    /// violates the constraint C. This is non-tautological because
    /// a wrong implementation (e.g., flipping >= to >) would pass
    /// compilation but fail this proof.
    #[kani::proof]
    fn sign_contradicts_exhaustive() {
        let variant: u8 = kani::any();
        kani::assume(variant < 5);
        let sign: i32 = kani::any();
        kani::assume(sign >= -1 && sign <= 1);

        let constraint = match variant {
            0 => SignConstraint::Positive,
            1 => SignConstraint::Negative,
            2 => SignConstraint::Zero,
            3 => SignConstraint::NonNegative,
            _ => SignConstraint::NonPositive,
        };

        let result = sign::sign_contradicts(constraint, sign);

        // Verify the semantic definition for each constraint variant.
        // These assertions encode the mathematical meaning of each constraint.
        match constraint {
            SignConstraint::Positive => {
                // Positive means sign > 0. Contradicts iff sign <= 0.
                assert_eq!(result, sign <= 0);
            }
            SignConstraint::Negative => {
                // Negative means sign < 0. Contradicts iff sign >= 0.
                assert_eq!(result, sign >= 0);
            }
            SignConstraint::Zero => {
                // Zero means sign == 0. Contradicts iff sign != 0.
                assert_eq!(result, sign != 0);
            }
            SignConstraint::NonNegative => {
                // NonNegative means sign >= 0. Contradicts iff sign < 0.
                assert_eq!(result, sign < 0);
            }
            SignConstraint::NonPositive => {
                // NonPositive means sign <= 0. Contradicts iff sign > 0.
                assert_eq!(result, sign > 0);
            }
        }
    }

    /// Verify that sign_contradicts is self-consistent: a constraint
    /// never simultaneously contradicts all possible sign values.
    /// (Every constraint is satisfiable by at least one sign.)
    #[kani::proof]
    fn sign_contradicts_not_all_contradicted() {
        let variant: u8 = kani::any();
        kani::assume(variant < 5);

        let constraint = match variant {
            0 => SignConstraint::Positive,
            1 => SignConstraint::Negative,
            2 => SignConstraint::Zero,
            3 => SignConstraint::NonNegative,
            _ => SignConstraint::NonPositive,
        };

        // At least one of {-1, 0, 1} must not be contradicted.
        let all_contradicted = sign::sign_contradicts(constraint, -1)
            && sign::sign_contradicts(constraint, 0)
            && sign::sign_contradicts(constraint, 1);

        assert!(
            !all_contradicted,
            "Every SignConstraint must be satisfiable by at least one sign value"
        );
    }

    // ========================================================================
    // check_sign_consistency: conflict detection soundness
    // ========================================================================

    /// Verify that check_sign_consistency detects a conflict when
    /// two positive factors have a monomial constrained as Negative.
    ///
    /// Property: positive * positive = positive, which contradicts
    /// Negative. check_sign_consistency must return Some(conflict).
    #[kani::proof]
    fn check_sign_consistency_detects_pos_pos_neg_conflict() {
        let x = TermId::new(1);
        let y = TermId::new(2);
        let aux = TermId::new(3);
        let assert_x = TermId::new(10);
        let assert_y = TermId::new(11);
        let assert_m = TermId::new(12);

        let vars = vec![x, y];
        let mon = Monomial::new(vars.clone(), aux);

        let mut monomials: DetHashMap<Vec<TermId>, Monomial> = DetHashMap::default();
        monomials.insert(vars.clone(), mon);

        let mut var_signs: DetHashMap<TermId, Vec<(SignConstraint, TermId)>> =
            DetHashMap::default();
        var_signs
            .entry(x)
            .or_default()
            .push((SignConstraint::Positive, assert_x));
        var_signs
            .entry(y)
            .or_default()
            .push((SignConstraint::Positive, assert_y));

        let mut sign_constraints: DetHashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> =
            DetHashMap::default();
        sign_constraints
            .entry(vars)
            .or_default()
            .push((SignConstraint::Negative, assert_m));

        let asserted = vec![(assert_x, true), (assert_y, true), (assert_m, true)];

        let conflict = sign::check_sign_consistency(
            &monomials,
            &sign_constraints,
            &var_signs,
            &asserted,
            false,
        );

        assert!(
            conflict.is_some(),
            "pos * pos with Negative constraint must produce a conflict"
        );

        let conflict = conflict.unwrap();
        // Conflict must be non-empty
        assert!(!conflict.is_empty(), "conflict clause must be non-empty");
        // Conflict must only contain relevant assertions (at most 3)
        assert!(
            conflict.len() <= 3,
            "conflict clause should be minimal (at most 3 literals)"
        );
    }

    /// Verify that check_sign_consistency does NOT report a conflict
    /// when factor signs are consistent with the monomial constraint.
    ///
    /// Property: positive * negative = negative, which satisfies
    /// a Negative constraint. No conflict should be reported.
    #[kani::proof]
    fn check_sign_consistency_no_false_conflict() {
        let x = TermId::new(1);
        let y = TermId::new(2);
        let aux = TermId::new(3);
        let assert_x = TermId::new(10);
        let assert_y = TermId::new(11);
        let assert_m = TermId::new(12);

        let vars = vec![x, y];
        let mon = Monomial::new(vars.clone(), aux);

        let mut monomials: DetHashMap<Vec<TermId>, Monomial> = DetHashMap::default();
        monomials.insert(vars.clone(), mon);

        let mut var_signs: DetHashMap<TermId, Vec<(SignConstraint, TermId)>> =
            DetHashMap::default();
        var_signs
            .entry(x)
            .or_default()
            .push((SignConstraint::Positive, assert_x));
        var_signs
            .entry(y)
            .or_default()
            .push((SignConstraint::Negative, assert_y));

        let mut sign_constraints: DetHashMap<Vec<TermId>, Vec<(SignConstraint, TermId)>> =
            DetHashMap::default();
        // pos * neg = neg, so Negative constraint is consistent
        sign_constraints
            .entry(vars)
            .or_default()
            .push((SignConstraint::Negative, assert_m));

        let asserted = vec![(assert_x, true), (assert_y, true), (assert_m, true)];

        let conflict = sign::check_sign_consistency(
            &monomials,
            &sign_constraints,
            &var_signs,
            &asserted,
            false,
        );

        assert!(
            conflict.is_none(),
            "pos * neg with Negative constraint should NOT produce a conflict"
        );
    }

    // ========================================================================
    // propagate_monomial_signs: sign propagation correctness
    // ========================================================================

    /// Verify that propagate_monomial_signs derives the correct sign
    /// for a binary monomial when both factors have known signs.
    ///
    /// Property: for m = x * y, if x is Positive and y is Negative,
    /// then m's aux_var should get a Negative sign constraint.
    #[kani::proof]
    fn propagate_monomial_signs_derives_product_sign() {
        let x = TermId::new(1);
        let y = TermId::new(2);
        let aux = TermId::new(3);
        let assert_x = TermId::new(10);
        let assert_y = TermId::new(11);

        let vars = vec![x, y];
        let mon = Monomial::new(vars.clone(), aux);

        let mut monomials: DetHashMap<Vec<TermId>, Monomial> = DetHashMap::default();
        monomials.insert(vars, mon);

        let mut var_signs: DetHashMap<TermId, Vec<(SignConstraint, TermId)>> =
            DetHashMap::default();
        var_signs
            .entry(x)
            .or_default()
            .push((SignConstraint::Positive, assert_x));
        var_signs
            .entry(y)
            .or_default()
            .push((SignConstraint::Negative, assert_y));

        // aux_var should not have a sign yet
        assert!(
            var_signs.get(&aux).is_none(),
            "aux_var should have no sign before propagation"
        );

        sign::propagate_monomial_signs(&monomials, &mut var_signs);

        // After propagation, aux_var should have a Negative sign
        let aux_signs = var_signs.get(&aux);
        assert!(
            aux_signs.is_some(),
            "propagation must derive a sign for the aux_var"
        );
        let aux_signs = aux_signs.unwrap();
        assert!(
            !aux_signs.is_empty(),
            "propagated sign list must be non-empty"
        );

        // The derived sign should be Negative (pos * neg = neg)
        let has_negative = aux_signs
            .iter()
            .any(|(c, _)| matches!(c, SignConstraint::Negative));
        assert!(
            has_negative,
            "pos * neg must propagate as Negative to aux_var"
        );
    }

    /// Verify that propagate_monomial_signs does NOT propagate a sign
    /// when one factor has no definite sign (only NonNegative, not Positive).
    ///
    /// Property: sign_from_constraints only returns definite signs
    /// (Positive, Negative, Zero). NonNegative is not definite.
    #[kani::proof]
    fn propagate_monomial_signs_skips_indefinite() {
        let x = TermId::new(1);
        let y = TermId::new(2);
        let aux = TermId::new(3);
        let assert_x = TermId::new(10);
        let assert_y = TermId::new(11);

        let vars = vec![x, y];
        let mon = Monomial::new(vars.clone(), aux);

        let mut monomials: DetHashMap<Vec<TermId>, Monomial> = DetHashMap::default();
        monomials.insert(vars, mon);

        let mut var_signs: DetHashMap<TermId, Vec<(SignConstraint, TermId)>> =
            DetHashMap::default();
        var_signs
            .entry(x)
            .or_default()
            .push((SignConstraint::Positive, assert_x));
        // y only has NonNegative — not a definite sign
        var_signs
            .entry(y)
            .or_default()
            .push((SignConstraint::NonNegative, assert_y));

        sign::propagate_monomial_signs(&monomials, &mut var_signs);

        // aux_var should NOT have a sign — y's sign is indefinite
        assert!(
            var_signs.get(&aux).is_none(),
            "propagation must NOT derive a sign when a factor has only indefinite sign"
        );
    }
}
