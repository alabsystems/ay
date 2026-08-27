// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Exact, order-independent recovery of clause MILPs as CNF.
//!
//! This route recognizes semantics, not a compiler's row layout.  Every model
//! column must have an integral domain contained in `{0, 1}`, every true
//! objective coefficient must be zero, and every finite side of every row must
//! be either a Boolean tautology, a contradiction, or one scaled clause.
//! Coefficients and row bounds are read through [`Model`]'s authoritative exact
//! side store.  Anything outside that class receives a typed decline and stays
//! on the ordinary MILP path.

use std::time::Instant;

use ay_sat::{Literal, Variable};
use num_bigint::BigInt;
use num_integer::Integer;
use num_rational::BigRational;
use num_traits::{One, Signed, Zero};

use crate::model::{exact, ColKind, Model};
use crate::sat_route::{deadline_reached, solve_and_lift, SatDecision};

/// Which exact side of a range row failed clause admission.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum RowSide {
    Lower,
    Upper,
}

/// A fail-closed reason this exact reduction did not own the model.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum DirectCnfDecline {
    Deadline,
    NonConstantObjective { column: usize },
    NonBooleanColumn { column: usize },
    NonBooleanDomain { column: usize },
    NonClauseSide { row: usize, side: RowSide },
}

/// Typed admission: unsupported is distinct from solver `Unknown` and from a
/// conclusive SAT/UNSAT decision.
pub(crate) enum DirectCnfAdmission {
    Admitted(DirectCnfPlan),
    Declined(DirectCnfDecline),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum BooleanDomain {
    Both,
    Zero,
    One,
    Empty,
}

pub(crate) struct DirectCnfPlan {
    clauses: Vec<Vec<Literal>>,
    domains: Vec<BooleanDomain>,
}

/// Try the exact Direct-CNF route, returning `None` on typed decline, timeout,
/// solver `Unknown`, or a rejected SAT lift.
pub(crate) fn try_solve(model: &Model, deadline: Option<Instant>) -> Option<SatDecision> {
    let started = Instant::now();
    let plan = match admit(model, deadline) {
        DirectCnfAdmission::Admitted(plan) => plan,
        DirectCnfAdmission::Declined(reason) => {
            if trace_enabled() {
                eprintln!("--trace direct-cnf: declined={reason:?}");
            }
            return None;
        }
    };
    let decision = solve_and_lift(
        model,
        plan.domains.len(),
        &plan.clauses,
        deadline,
        |assignment| lift(&plan, assignment),
    );
    if let Some(ref decision) = decision {
        if trace_enabled() {
            let verdict = match decision {
                SatDecision::Sat(_) => "SAT",
                SatDecision::Unsat => "UNSAT",
            };
            eprintln!(
                "--trace direct-cnf: vars={} clauses={} verdict={verdict} wall={:.6}s",
                plan.domains.len(),
                plan.clauses.len(),
                started.elapsed().as_secs_f64(),
            );
        }
    }
    decision
}

pub(crate) fn admit(model: &Model, deadline: Option<Instant>) -> DirectCnfAdmission {
    if deadline_reached(deadline) {
        return DirectCnfAdmission::Declined(DirectCnfDecline::Deadline);
    }

    for (column, spec) in model.cols.iter().enumerate() {
        if column & 0x3ff == 0 && deadline_reached(deadline) {
            return DirectCnfAdmission::Declined(DirectCnfDecline::Deadline);
        }
        if !model.obj_coeff_exact_at(column as u32, spec.obj).is_zero() {
            return DirectCnfAdmission::Declined(DirectCnfDecline::NonConstantObjective { column });
        }
    }

    let mut domains = Vec::with_capacity(model.cols.len());
    for (column, spec) in model.cols.iter().enumerate() {
        if column & 0x3ff == 0 && deadline_reached(deadline) {
            return DirectCnfAdmission::Declined(DirectCnfDecline::Deadline);
        }
        if !matches!(spec.kind, ColKind::Binary | ColKind::Integer) {
            return DirectCnfAdmission::Declined(DirectCnfDecline::NonBooleanColumn { column });
        }
        let Some(lb) = exact(spec.lb) else {
            return DirectCnfAdmission::Declined(DirectCnfDecline::NonBooleanDomain { column });
        };
        let Some(ub) = exact(spec.ub) else {
            return DirectCnfAdmission::Declined(DirectCnfDecline::NonBooleanDomain { column });
        };
        let lo = lb.numer().div_ceil(lb.denom());
        let hi = ub.numer().div_floor(ub.denom());
        let zero = BigInt::zero();
        let one = BigInt::one();
        let domain = if lo > hi {
            BooleanDomain::Empty
        } else if lo < zero || hi > one {
            return DirectCnfAdmission::Declined(DirectCnfDecline::NonBooleanDomain { column });
        } else if lo == zero && hi == one {
            BooleanDomain::Both
        } else if lo == zero {
            BooleanDomain::Zero
        } else {
            debug_assert_eq!(lo, one);
            debug_assert_eq!(hi, one);
            BooleanDomain::One
        };
        domains.push(domain);
    }

    let mut clauses = Vec::new();
    for (column, domain) in domains.iter().copied().enumerate() {
        let variable = Variable::new(column as u32);
        match domain {
            BooleanDomain::Both => {}
            BooleanDomain::Zero => clauses.push(vec![Literal::negative(variable)]),
            BooleanDomain::One => clauses.push(vec![Literal::positive(variable)]),
            BooleanDomain::Empty => clauses.push(Vec::new()),
        }
    }

    for (row_index, row) in model.rows.iter().enumerate() {
        if row_index & 0x3ff == 0 && deadline_reached(deadline) {
            return DirectCnfAdmission::Declined(DirectCnfDecline::Deadline);
        }
        if let Some(bound) = model.row_lb_exact(row_index, row.lb) {
            match clause_for_side(
                model,
                row_index,
                &row.coeffs,
                bound,
                RowSide::Lower,
                &domains,
                deadline,
            ) {
                Ok(Some(clause)) => clauses.push(clause),
                Ok(None) => {}
                Err(reason) => return DirectCnfAdmission::Declined(reason),
            }
        }
        if let Some(bound) = model.row_ub_exact(row_index, row.ub) {
            match clause_for_side(
                model,
                row_index,
                &row.coeffs,
                bound,
                RowSide::Upper,
                &domains,
                deadline,
            ) {
                Ok(Some(clause)) => clauses.push(clause),
                Ok(None) => {}
                Err(reason) => return DirectCnfAdmission::Declined(reason),
            }
        }
    }

    DirectCnfAdmission::Admitted(DirectCnfPlan { clauses, domains })
}

/// Return one exact clause, `None` for a tautology, or a typed decline.
/// An empty returned clause is an exact contradiction.
fn clause_for_side(
    model: &Model,
    row: usize,
    coeffs: &[(u32, f64)],
    mut rhs: BigRational,
    side: RowSide,
    domains: &[BooleanDomain],
    deadline: Option<Instant>,
) -> Result<Option<Vec<Literal>>, DirectCnfDecline> {
    if side == RowSide::Upper {
        rhs = -rhs;
    }

    let mut terms: Vec<(u32, BigRational)> = Vec::with_capacity(coeffs.len());
    for (index, &(column, advice)) in coeffs.iter().enumerate() {
        if index & 0x3ff == 0 && deadline_reached(deadline) {
            return Err(DirectCnfDecline::Deadline);
        }
        let mut coefficient = model.row_coeff_exact(row, column, advice);
        if side == RowSide::Upper {
            coefficient = -coefficient;
        }
        if coefficient.is_zero() {
            continue;
        }
        match domains[column as usize] {
            BooleanDomain::Zero => {}
            BooleanDomain::One => rhs -= coefficient,
            // An empty domain already emitted the empty clause. Treating the
            // variable as free here still checks that every row belongs to the
            // admitted clause class instead of using infeasibility to hide an
            // unsupported row.
            BooleanDomain::Both | BooleanDomain::Empty => {
                terms.push((column, coefficient));
            }
        }
    }

    if terms.is_empty() {
        return Ok((rhs > BigRational::zero()).then(Vec::new));
    }

    // Classify Boolean tautologies/contradictions before requiring clause
    // coefficients. This accepts harmless sides such as `x <= 1` on a range
    // or equality row without weakening the nontrivial-side gate.
    let mut minimum = BigRational::zero();
    let mut maximum = BigRational::zero();
    for (_, coefficient) in &terms {
        if coefficient.is_negative() {
            minimum += coefficient;
        } else {
            maximum += coefficient;
        }
    }
    if rhs <= minimum {
        return Ok(None);
    }
    if rhs > maximum {
        return Ok(Some(Vec::new()));
    }

    let scale = terms[0].1.abs();
    if scale.is_zero()
        || terms
            .iter()
            .any(|(_, coefficient)| coefficient.abs() != scale)
    {
        return Err(DirectCnfDecline::NonClauseSide { row, side });
    }
    let negative = terms
        .iter()
        .filter(|(_, coefficient)| coefficient.is_negative())
        .count();
    let expected_multiplier = BigInt::one() - BigInt::from(negative);
    let expected_rhs = &scale * BigRational::from_integer(expected_multiplier);
    if rhs != expected_rhs {
        return Err(DirectCnfDecline::NonClauseSide { row, side });
    }

    let clause = terms
        .into_iter()
        .map(|(column, coefficient)| {
            let variable = Variable::new(column);
            if coefficient.is_positive() {
                Literal::positive(variable)
            } else {
                Literal::negative(variable)
            }
        })
        .collect();
    Ok(Some(clause))
}

fn lift(plan: &DirectCnfPlan, assignment: &[bool]) -> Option<Vec<BigRational>> {
    if assignment.len() < plan.domains.len() {
        return None;
    }
    let mut point = Vec::with_capacity(plan.domains.len());
    for (column, domain) in plan.domains.iter().copied().enumerate() {
        let value = assignment[column];
        let allowed = match domain {
            BooleanDomain::Both => true,
            BooleanDomain::Zero => !value,
            BooleanDomain::One => value,
            BooleanDomain::Empty => false,
        };
        if !allowed {
            return None;
        }
        point.push(if value {
            BigRational::one()
        } else {
            BigRational::zero()
        });
    }
    Some(point)
}

fn trace_enabled() -> bool {
    // Cached: the ratchet in `tests/env_ledger.rs` counts a bare `env::var_os`
    // on the solve path as a LIVE read — a fresh `getenv` a concurrent
    // `set_var` can race, which priming cannot help. `OnceLock` is the shape
    // that ratchet asks for and `simplex.rs` already uses.
    static ENABLED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ENABLED.get_or_init(|| crate::debug_flags::milp_debug_flags().trace)
}

/// Prime this cached accessor from `bab::prime_env_all` before window solves rewrite the environment.
pub(crate) fn prime_env() {
    let _ = trace_enabled();
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BabSession, Col, Outcome, Sense, SolveOpts};
    use std::time::Duration;

    fn rat(numerator: i64, denominator: i64) -> BigRational {
        BigRational::new(numerator.into(), denominator.into())
    }

    fn two_binary_cols() -> (Model, Col, Col) {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let y = model.add_binary_col();
        (model, x, y)
    }

    fn sat_point(model: &Model) -> Vec<BigRational> {
        match try_solve(model, None) {
            Some(SatDecision::Sat(point)) => point.into_values(),
            Some(SatDecision::Unsat) => panic!("expected SAT, got UNSAT"),
            None => panic!("clause model was declined"),
        }
    }

    #[test]
    fn admits_scaled_signed_clauses_independent_of_row_order() {
        let build = |reverse: bool| {
            let (mut model, x, y) = two_binary_cols();
            let rows = [
                // 2x - 2y >= 0  <=>  x OR NOT y.
                (0.0, f64::INFINITY, vec![(x, 2.0), (y, -2.0)]),
                // x + y >= 1  <=>  x OR y.
                (1.0, f64::INFINITY, vec![(x, 1.0), (y, 1.0)]),
            ];
            let order = if reverse { [1, 0] } else { [0, 1] };
            for index in order {
                let (lb, ub, coeffs) = &rows[index];
                model.add_row(*lb, *ub, coeffs);
            }
            model
        };

        for model in [build(false), build(true)] {
            let point = sat_point(&model);
            assert_eq!(point[0], BigRational::one());
            assert!(model.check_point(&point).is_ok());
        }
    }

    #[test]
    fn consumes_both_sides_of_a_range_row() {
        let (mut model, x, y) = two_binary_cols();
        // Together these sides say exactly one of x,y is true:
        //   x+y >= 1 => x OR y
        //   x+y <= 1 => NOT x OR NOT y.
        model.add_row(1.0, 1.0, &[(x, 1.0), (y, 1.0)]);
        let point = sat_point(&model);
        assert_ne!(point[0], point[1]);
        assert!(model.check_point(&point).is_ok());
    }

    #[test]
    fn fixed_binary_bounds_become_units_and_are_substituted_from_rows() {
        let (mut model, x, y) = two_binary_cols();
        model.fix_col(x, 1.0);
        // After exact substitution of x=1 this is the unit clause y.
        model.add_row(2.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        let point = sat_point(&model);
        assert_eq!(point, vec![BigRational::one(), BigRational::one()]);
    }

    #[test]
    fn authoritative_exact_side_store_controls_admission_and_sat_lift() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        // The advice row 7x >= 5 is deliberately NOT a clause. The true row
        // is (1/3)x >= 1/3, i.e. the unit clause x.
        let row = model.add_row(5.0, f64::INFINITY, &[(x, 7.0)]);
        model.record_inexact_row_coeff(row, x.0, rat(1, 3));
        model.record_inexact_row_bound(row, true, rat(1, 3));

        let point = sat_point(&model);
        assert_eq!(point, vec![BigRational::one()]);
        assert!(model.check_point(&point).is_ok());
    }

    #[test]
    fn exact_side_store_unsat_survives_the_float_search_backstop() {
        let mut model = Model::new();
        let x = model.add_binary_col();
        let lower = model.add_row(5.0, f64::INFINITY, &[(x, 7.0)]);
        model.record_inexact_row_coeff(lower, x.0, rat(1, 3));
        model.record_inexact_row_bound(lower, true, rat(1, 3));
        let upper = model.add_row(f64::NEG_INFINITY, 5.0, &[(x, 7.0)]);
        model.record_inexact_row_coeff(upper, x.0, rat(1, 3));
        model.record_inexact_row_bound(upper, false, BigRational::zero());

        // LANE LEVEL: Direct-CNF itself must read the exact side store and
        // refute, not the `7x >= 5` / `7x <= 5` f64 proxy.
        assert!(matches!(try_solve(&model, None), Some(SatDecision::Unsat)));

        // SESSION LEVEL: the property in the name is that this UNSAT is NOT
        // degraded by `fail_closed_for_inexact`. Which exact lane gets there
        // first is not the subject and must not be pinned: a proof-exporting PB
        // route now runs ahead of the REPLAY-only routes precisely so the
        // default posture stops emitting unbacked claims for models a succinct
        // proof can refute.
        let opts = SolveOpts::new();
        let mut session = BabSession::new(model, &opts).expect("session");
        let outcome = session.check().expect("solve");
        assert!(
            outcome.is_infeasible(),
            "an exact-side-store UNSAT must survive the float-search backstop, \
             not degrade to Unknown: {outcome:?}"
        );
        assert!(
            session.single_row_dp_infeasibility_certificate().is_some()
                || session.multi_row_bdd_infeasibility_certificate().is_some()
                || session
                    .replay_claims()
                    .iter()
                    .any(|claim| claim.claim == "direct-cnf-unsat"),
            "the verdict must arrive with either a typed artifact or an honest \
             replay claim, never bare: {:?}",
            session.replay_claims()
        );
    }

    #[test]
    fn declines_a_non_clause_side_with_a_typed_reason() {
        let (mut model, x, y) = two_binary_cols();
        // Requires both variables, so this one row is a conjunction rather
        // than one disjunction.
        model.add_row(2.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
        assert!(matches!(
            admit(&model, None),
            DirectCnfAdmission::Declined(DirectCnfDecline::NonClauseSide {
                row: 0,
                side: RowSide::Lower
            })
        ));
    }

    #[test]
    fn declines_continuous_or_wide_integer_columns() {
        let mut continuous = Model::new();
        let x = continuous.add_col(0.0, 1.0);
        continuous.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        assert!(matches!(
            admit(&continuous, None),
            DirectCnfAdmission::Declined(DirectCnfDecline::NonBooleanColumn { column: 0 })
        ));

        let mut wide_integer = Model::new();
        let x = wide_integer.add_int_col(0.0, 2.0);
        wide_integer.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        assert!(matches!(
            admit(&wide_integer, None),
            DirectCnfAdmission::Declined(DirectCnfDecline::NonBooleanDomain { column: 0 })
        ));
    }

    #[test]
    fn constant_objective_is_optimal_but_any_true_linear_term_declines() {
        let mut constant = Model::new();
        let x = constant.add_binary_col();
        constant.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        constant.set_objective_offset(7.0);
        let opts = SolveOpts::new();
        let mut session = BabSession::new(constant, &opts).expect("session");
        assert!(matches!(
            session.check().expect("solve"),
            Outcome::Optimal { ref value, .. }
                if value == &BigRational::from_integer(7.into())
        ));

        let mut linear = Model::new();
        let x = linear.add_binary_col();
        linear.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
        linear.set_objective(&[(x, 1.0)], Sense::Minimize);
        assert!(matches!(
            admit(&linear, None),
            DirectCnfAdmission::Declined(DirectCnfDecline::NonConstantObjective { column: 0 })
        ));

        // The side store is authoritative even if the advice coefficient is 0.
        let mut exact_linear = Model::new();
        let x = exact_linear.add_binary_col();
        exact_linear.record_inexact_obj_coeff(x.0, BigRational::one());
        assert!(matches!(
            admit(&exact_linear, None),
            DirectCnfAdmission::Declined(DirectCnfDecline::NonConstantObjective { column: 0 })
        ));
    }

    #[test]
    fn expired_deadline_is_a_typed_decline() {
        let model = Model::new();
        let deadline = Instant::now()
            .checked_sub(Duration::from_millis(1))
            .unwrap_or_else(Instant::now);
        assert!(matches!(
            admit(&model, Some(deadline)),
            DirectCnfAdmission::Declined(DirectCnfDecline::Deadline)
        ));
        assert!(try_solve(&model, Some(deadline)).is_none());
    }

    /// A CDCL refutation is not one of the exported MILP certificate formats, so
    /// it may be RECORDED as a replay claim and must never be the thing that
    /// ends a solve the native tree could have proved.
    ///
    /// This test used to assert something weaker and, it turns out, wrong: that
    /// the CERTIFICATE POSTURE skipped the route. That is how the defect was
    /// spelled — `session.rs` gated the whole block on
    /// `!self.opts.require_certificates`, so `--require full` ran different
    /// LANES from the shipped default, and the default came back with
    /// `verify` exit 10 where the strict posture got exit 0 on the same model.
    /// Posture must select which evidence is ACCEPTABLE, never which code runs.
    ///
    /// The contract now is stronger and posture-independent: the lane runs in
    /// every posture, its claim is filed either way, and `claim::may_close`
    /// decides whether it may CLOSE. On a model whose native refutation the
    /// anchor can certify, it may not.
    #[test]
    fn a_cdcl_refutation_is_recorded_but_never_preempts_a_reachable_proof() {
        // 8 pigeons into 7 holes: a genuine clause model that the bounded PB
        // proof routes decline (the compact-plan admission gate turns it away),
        // so Direct-CNF really does own the session route here. The one-column
        // `x >= 1, x <= 0` fixture this test used to carry no longer reaches
        // Direct-CNF at all — a single-row DP refutes it succinctly first —
        // which made both halves assert about a lane that never ran.
        let make = || {
            let (pigeons, holes) = (8usize, 7usize);
            let mut model = Model::new();
            let cells: Vec<Vec<_>> = (0..pigeons)
                .map(|_| (0..holes).map(|_| model.add_binary_col()).collect())
                .collect();
            for row in &cells {
                let terms: Vec<_> = row.iter().map(|&col| (col, 1.0)).collect();
                model.add_row(1.0, f64::INFINITY, &terms);
            }
            for hole in 0..holes {
                for first in 0..pigeons {
                    for second in (first + 1)..pigeons {
                        model.add_row(
                            f64::NEG_INFINITY,
                            1.0,
                            &[(cells[first][hole], 1.0), (cells[second][hole], 1.0)],
                        );
                    }
                }
            }
            model
        };

        let opts = SolveOpts::new();
        let mut session = BabSession::new(make(), &opts).expect("session");
        assert!(session.check().expect("solve").is_infeasible());
        assert!(
            session
                .replay_claims()
                .iter()
                .any(|claim| claim.claim == "direct-cnf-unsat"),
            "Direct-CNF must still own the session route on a clause model the \
             bounded PB proof routes decline; if this stops holding the lane is \
             unreachable from `check` and the tests below prove nothing: {:?}",
            session.replay_claims()
        );

        // THE FLOOR HELD IT BACK, in the DEFAULT posture. The lane produced a
        // verdict and was not allowed to publish it, because the anchor could
        // still reach a succinct refutation of the same model.
        let mut session = BabSession::new(make(), &SolveOpts::new()).expect("session");
        let _ = session.check().expect("solve");
        assert_eq!(
            session.deferred_lane(),
            Some(("direct-cnf", "infeasible")),
            "a REPLAY-only CDCL refutation must be DEFERRED behind the anchor's \
             first refusal, not published as the verdict"
        );

        // A CDCL refutation is not an exported certificate type, so certificate
        // posture must not let it stand as evidence. Note what is NOT asserted
        // any more: that the lane was skipped. It runs, and its claim is filed;
        // what it may not do is close the solve.
        let opts = SolveOpts::new().with_require_certificates(true);
        let mut session = BabSession::new(make(), &opts).expect("session");
        let outcome = session.check().expect("solve");
        if let Outcome::Infeasible { cert, tree_cert } = &outcome {
            assert!(
                cert.is_some() || tree_cert.is_some(),
                "certificate posture must not report a bare Infeasible: {outcome:?}"
            );
        }
    }

    #[test]
    fn direct_cnf_matches_the_native_solver_on_small_sat_and_unsat_models() {
        let sat = {
            let (mut model, x, y) = two_binary_cols();
            model.add_row(1.0, f64::INFINITY, &[(x, 1.0), (y, 1.0)]);
            model
        };
        let unsat = {
            let mut model = Model::new();
            let x = model.add_binary_col();
            model.add_row(1.0, f64::INFINITY, &[(x, 1.0)]);
            model.add_row(f64::NEG_INFINITY, 0.0, &[(x, 1.0)]);
            model
        };
        let opts = SolveOpts::new().with_time_limit(Duration::from_secs(2));

        for (model, expect_sat) in [(sat, true), (unsat, false)] {
            let routed = try_solve(&model, None).expect("direct route verdict");
            let native = crate::bab::solve_milp(&model, &opts);
            assert_eq!(matches!(routed, SatDecision::Sat(_)), expect_sat);
            assert_eq!(native.is_sat(), expect_sat);
            assert_eq!(native.is_infeasible(), !expect_sat);
        }
    }
}
