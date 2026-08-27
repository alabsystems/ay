// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::super::*;

/// The two grid traversals have different authority and cost models.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum GridPass {
    /// Enumerate candidates only; never enter the univariate solver.
    Enumerate,
    /// Revisit prefixes solely to solve their last free coordinate exactly.
    SolveLastCoordinate,
}

/// Budget and empty-prefix streak for one grid traversal.
pub(in super::super) struct ExactState {
    pass: GridPass,
    remaining: std::cell::Cell<usize>,
    empty_streak: std::cell::Cell<usize>,
}

impl ExactState {
    pub(in super::super) fn disabled() -> Self {
        Self {
            pass: GridPass::Enumerate,
            remaining: std::cell::Cell::new(0),
            empty_streak: std::cell::Cell::new(0),
        }
    }

    pub(in super::super) fn with(limit: usize) -> Self {
        Self {
            pass: GridPass::SolveLastCoordinate,
            remaining: std::cell::Cell::new(limit),
            empty_streak: std::cell::Cell::new(0),
        }
    }

    pub(in super::super) fn solves_last_coordinate(&self) -> bool {
        self.pass == GridPass::SolveLastCoordinate
    }

    pub(in super::super) fn available(&self) -> bool {
        self.remaining.get() > 0
    }

    /// An exhausted exact traversal must unwind instead of repeating the
    /// candidate-only traversal after it has no exact work left.
    pub(in super::super) fn spent(&self) -> bool {
        self.solves_last_coordinate() && !self.available()
    }

    pub(in super::super) fn charge(&self, outcome: &ExactOutcome) {
        self.remaining.set(self.remaining.get().saturating_sub(1));
        match outcome {
            ExactOutcome::Empty => {
                let streak = self.empty_streak.get() + 1;
                self.empty_streak.set(streak);
                if streak >= GRID_EXACT_EMPTY_STREAK {
                    diag!("NRA-LAST streak-cut after={streak}");
                    self.remaining.set(0);
                }
            }
            ExactOutcome::Declined => {}
            ExactOutcome::Model(_) => self.empty_streak.set(0),
        }
    }
}

/// Result of deciding one residual last-coordinate system.
pub(in super::super) enum ExactOutcome {
    /// A complete model, already verified against the parsed problem.
    Model(UniResult),
    /// This prefix alone is infeasible; the overall search is not refuted.
    Empty,
    /// The exact decision could not establish anything.
    Declined,
}

struct ResidualSystem {
    decision: Vec<UniConstraint>,
    verification: Vec<(UniPoly, Rel)>,
}

enum ResidualBuild {
    Ready(ResidualSystem),
    Empty,
    Declined,
}

fn pinned_coordinates(
    vars: &[TermId],
    free: TermId,
    bx: &VarBox,
) -> Option<Vec<(TermId, BigRational)>> {
    let mut pins = Vec::with_capacity(vars.len());
    for &var in vars {
        if var == free {
            continue;
        }
        let Some(value) = bx.get(&var).and_then(interval_point) else {
            diag!("NRA-LAST bail=pin-not-point");
            return None;
        };
        pins.push((var, value.clone()));
    }
    Some(pins)
}

fn residual_system(
    constraints: &[MultiConstraint],
    pins: &[(TermId, BigRational)],
) -> ResidualBuild {
    let mut decision = Vec::with_capacity(constraints.len() + 2);
    let mut verification = Vec::with_capacity(constraints.len());
    for constraint in constraints {
        let mut residual = constraint.poly.clone();
        for (var, value) in pins {
            residual = substitute_point(&residual, *var, value);
        }
        let Some(poly) = residual.to_unipoly() else {
            diag!(
                "NRA-LAST bail=not-univariate vars={:?}",
                residual.variables().len()
            );
            return ResidualBuild::Declined;
        };
        if poly.degree() == Some(0) || poly.is_zero() {
            let value = poly
                .coeffs()
                .first()
                .cloned()
                .unwrap_or_else(BigRational::zero);
            if !constraint.rel.holds_for_sign(rational_sign(&value)) {
                return ResidualBuild::Empty;
            }
            continue;
        }
        verification.push((poly.clone(), constraint.rel));
        decision.push(UniConstraint {
            poly,
            rel: constraint.rel,
        });
    }
    ResidualBuild::Ready(ResidualSystem {
        decision,
        verification,
    })
}

fn add_interval_bounds(decision: &mut Vec<UniConstraint>, iv: &Interval) {
    if let Endpoint::Finite(lo, _) = &iv.lo {
        let poly = UniPoly::x().sub(&UniPoly::constant(lo.clone()));
        decision.push(UniConstraint { poly, rel: Rel::Ge });
    }
    if let Endpoint::Finite(hi, _) = &iv.hi {
        let poly = UniPoly::constant(hi.clone()).sub(&UniPoly::x());
        decision.push(UniConstraint { poly, rel: Rel::Ge });
    }
}

fn rational_model(
    vars: &[TermId],
    solved: TermId,
    value: &BigRational,
    bx: &VarBox,
) -> Option<Vec<(TermId, BigRational)>> {
    vars.iter()
        .copied()
        .map(|var| {
            let value = if var == solved {
                value.clone()
            } else {
                bx.get(&var).and_then(interval_point)?.clone()
            };
            Some((var, value))
        })
        .collect()
}

fn algebraic_model(
    vars: &[TermId],
    solved: TermId,
    value: &crate::algebraic::RealAlgebraic,
    bx: &VarBox,
) -> Option<Vec<(TermId, UniWitness)>> {
    vars.iter()
        .copied()
        .map(|var| {
            let witness = if var == solved {
                UniWitness::Algebraic(value.as_value())
            } else {
                UniWitness::Rational(bx.get(&var).and_then(interval_point)?.clone())
            };
            Some((var, witness))
        })
        .collect()
}

impl NraSolver<'_> {
    /// Decide the last free coordinate of a grid prefix exactly. Every other
    /// coordinate must be a point, making each residual polynomial univariate.
    /// `Empty` only rejects this prefix; the grid phase never returns UNSAT.
    pub(in super::super) fn solve_last_coordinate(
        &self,
        constraints: &[MultiConstraint],
        vars: &[TermId],
        solved: TermId,
        interval: &Interval,
        bx: &VarBox,
    ) -> ExactOutcome {
        let Some(pins) = pinned_coordinates(vars, solved, bx) else {
            return ExactOutcome::Declined;
        };
        let mut residual = match residual_system(constraints, &pins) {
            ResidualBuild::Ready(residual) => residual,
            ResidualBuild::Empty => return ExactOutcome::Empty,
            ResidualBuild::Declined => return ExactOutcome::Declined,
        };
        add_interval_bounds(&mut residual.decision, interval);
        if residual.decision.is_empty() {
            return ExactOutcome::Declined;
        }

        match decide_single_variable(&residual.decision) {
            SingleVarResult::Witness(value) => {
                diag!("NRA-LAST witness={value}");
                rational_model(vars, solved, &value, bx)
                    .filter(|model| self.verify_model(model))
                    .map(|model| ExactOutcome::Model(UniResult::Sat(model)))
                    .unwrap_or(ExactOutcome::Declined)
            }
            SingleVarResult::IrrationalSat(value) => {
                if residual.verification.iter().any(|(poly, rel)| {
                    value
                        .sign_of_poly(poly)
                        .map(|sign| !rel.holds_for_sign(sign))
                        .unwrap_or(true)
                }) {
                    return ExactOutcome::Declined;
                }
                if !self.asserted_fully_parsed() {
                    return ExactOutcome::Declined;
                }
                diag!("NRA-LAST algebraic-witness");
                algebraic_model(vars, solved, &value, bx)
                    .map(|model| ExactOutcome::Model(UniResult::SatAlgebraic(model)))
                    .unwrap_or(ExactOutcome::Declined)
            }
            outcome => {
                let empty = matches!(outcome, SingleVarResult::Empty);
                diag!(
                    "NRA-LAST bail=decide pins={:?} n_uni={} kind={}",
                    pins.iter()
                        .map(|(_, value)| value.to_string())
                        .collect::<Vec<_>>(),
                    residual.decision.len(),
                    if empty { "Empty" } else { "Unknown" }
                );
                if empty {
                    ExactOutcome::Empty
                } else {
                    ExactOutcome::Declined
                }
            }
        }
    }
}
