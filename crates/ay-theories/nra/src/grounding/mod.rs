// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Model-guided grounding for bilinear template systems.
//!
//! The regular NRA loop repeatedly linearizes a nonlinear relaxation.  On
//! Motzkin/Farkas template problems, products join two disjoint groups of
//! unbounded reals and that refinement can oscillate indefinitely.  This phase
//! instead pins a cover of the nonlinear factors at the current model point,
//! making the residual exactly linear, and solves that residual privately.
//!
//! This is deliberately a SAT-only lane.  A failed or infeasible residual says
//! nothing about the original formula.  A feasible residual is only a
//! candidate: [`NraSolver::verify_model`] must re-evaluate every original atom
//! with exact rationals before this module can report success.  Unsupported
//! syntax, division, an `Int`-sorted factor, resource exhaustion, and
//! unreadable model values all decline without changing the caller's solver.
//!
//! # Where it fires
//!
//! Unlike every other exact phase, this one can fire MID refinement — on the
//! relaxation point of iteration `k`, on top of the tangent lemmas, tentative
//! sign cuts and patch bounds that iterations `0..k` left in the still-open
//! tentative scope.  [`NraSolver::install_grounded_model`] retires that scope
//! before injecting.  Both the pre-loop and the mid-loop entry are covered end
//! to end (`model_guided_grounding_turns_bilinear_template_system_sat` and
//! `grounding_installs_its_verified_point_over_live_refinement_bounds`); the
//! latter is the only test that reaches the mid-loop entry, which restricting
//! [`scheduled`] to iteration 0 demonstrates.
//!
//! # How much it converts
//!
//! Measured for the pre-landing revision of this phase against a base without
//! it (2026-08-14, interleaved same-day A/B, one release build per side, 289
//! QF_NRA instances, 20 s cap):
//!
//!   * 43 target-family instances the base declines FAST, sampled at RANDOM
//!     rather than picked: 3 unknown -> sat, 0 losses.  The same 43 at a 60 s
//!     cap convert the same 3, so the iteration cap is not the binding
//!     constraint.  ~7% on a random fast-decline sample, NOT the ~45% (18/40)
//!     an earlier HAND-CHOSEN sample reported.
//!   * CONTROL, 130 instances the base already decides: 0 answer changes,
//!     397.0 s -> 392.4 s.  116 fast declines outside the target families: 0
//!     losses, no unknown -> timeout trade, 481.4 s -> 464.8 s.
//!   * Whole run 1090.0 s -> 1088.6 s; 0 sat on any of the 98 declared-unsat
//!     instances.  All 3 new sats were accepted by external Dolmen.
//!
//! So: a small, cheap, one-directional win, not a large one.  The numbers are
//! the pre-landing revision's; this module is that phase adapted onto the
//! fixed-factor loop, so treat them as the expected order of magnitude rather
//! than a measurement of this exact code.

mod cover;
mod residual;
#[cfg(test)]
mod test_probe;

use ay_core::term::{Constant, Symbol, TermData, TermId};
use num_rational::BigRational;
use num_traits::{One, Zero};

use crate::univariate::{MultiAtom, MultiConstraint};
use crate::NraSolver;

use self::cover::grounding_covers;
#[cfg(test)]
use self::test_probe::{
    reset_test_successes, test_probe, test_successes, GroundingProbe, TEST_PROBE,
};

/// Residual solves allowed during one NRA `check()`.
const MAX_ATTEMPTS: usize = 64;
/// Assertions accepted by one plan.
const MAX_ASSERTIONS: usize = 2_048;
/// Arithmetic source nodes inspected across one plan.
const MAX_SOURCE_NODES: usize = 32_768;
/// Maximum nesting handed to the recursive polynomial reader.
const MAX_TERM_DEPTH: usize = 128;
/// Conservative expansion ceiling for one source arithmetic term.
const MAX_EXPANDED_TERMS_PER_TERM: usize = 4_096;
/// Expanded polynomial terms retained across the assertion set.
const MAX_POLY_TERMS: usize = 8_192;
/// Factor cells retained across all expanded monomials.
const MAX_POLY_FACTORS: usize = 32_768;
/// Distinct variables whose candidate values may be assembled.
const MAX_MODEL_VARS: usize = 4_096;
/// Distinct nonlinear monomials planned by the cover algorithm.
const MAX_MONOMIALS: usize = 4_096;

/// Dense early schedule followed by sparse probes. Repeated points are also
/// suppressed by the exact pin-vector stall detector.
pub(crate) fn scheduled(iteration: usize) -> bool {
    iteration < 8 || iteration.is_multiple_of(8)
}

/// Immutable assertion-set data plus bounded per-check attempt state.
pub(crate) struct GroundingPlan {
    pub(super) constraints: Vec<MultiConstraint>,
    pub(super) covers: Vec<Vec<TermId>>,
    pub(super) model_vars: Vec<TermId>,
    tried: Vec<Vec<(TermId, BigRational)>>,
    attempts: usize,
}

impl GroundingPlan {
    pub(crate) fn exhausted(&self) -> bool {
        self.attempts >= MAX_ATTEMPTS
    }
}

/// Ordered transformations of a relaxation-model pin.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum PinSnap {
    Model,
    Integer,
    Zero,
}

impl PinSnap {
    const ORDERED: [Self; 3] = [Self::Model, Self::Integer, Self::Zero];

    fn apply(self, value: BigRational) -> BigRational {
        match self {
            Self::Model => value,
            Self::Integer => value.round(),
            Self::Zero => BigRational::zero(),
        }
    }
}

#[derive(Clone, Copy)]
struct PolyShape {
    terms: usize,
    degree: usize,
}

impl NraSolver<'_> {
    /// Build immutable plan data once, before the refinement loop starts.
    pub(crate) fn build_grounding_plan(&self) -> Option<GroundingPlan> {
        // Division is intentionally unsupported.  In particular, a residual
        // model cannot certify the functional consistency required at a zero
        // divisor, so accepting even purified division terms would be unsound.
        if !self.div_terms.is_empty() || self.asserted.len() > MAX_ASSERTIONS {
            return None;
        }

        let (constraints, mut model_vars) = self.collect_grounding_constraints()?;
        model_vars.sort_unstable();
        model_vars.dedup();
        if model_vars.is_empty() || model_vars.len() > MAX_MODEL_VARS {
            return None;
        }
        // Every support variable must be Real-sorted -- the same guard, for the
        // same reason, as `icp.rs`'s: a rational witness for an Int variable
        // would be unsound, and integrality is NIA's province.  Nothing further
        // down would catch it.  The residual is decided by a REAL simplex plus
        // `Interval::sample`'s midpoint, both free to answer `3/2`; the pin
        // snaps only *offer* an integer alternative; and `verify_model`
        // (univariate.rs) re-checks the atoms, not the sorts.  Declining the
        // whole plan is also honest about what this phase is: a SAT-only lane
        // for the real-valued bilinear template families.
        if model_vars
            .iter()
            .any(|&variable| !matches!(self.terms.sort(variable), ay_core::Sort::Real))
        {
            return None;
        }

        let monomials = nonlinear_monomials(&constraints)?;
        let mut covers = grounding_covers(&monomials);
        // Pinning the complete support merely retries the already-inconsistent
        // relaxation point and is pure cost (notably on sums of squares).
        covers.retain(|cover| model_vars.iter().any(|var| !cover.contains(var)));
        if covers.is_empty() {
            return None;
        }

        if self.debug {
            tracing::debug!(
                "[NRA] grounding plan: {} constraints, {} monomials, {} support vars, covers={:?}",
                constraints.len(),
                monomials.len(),
                model_vars.len(),
                covers.iter().map(Vec::len).collect::<Vec<_>>()
            );
        }
        Some(GroundingPlan {
            constraints,
            covers,
            model_vars,
            tried: Vec::new(),
            attempts: 0,
        })
    }

    /// Parse supported atoms after an iterative size/depth preflight.
    fn collect_grounding_constraints(&self) -> Option<(Vec<MultiConstraint>, Vec<TermId>)> {
        let mut constraints = Vec::new();
        let mut model_vars = Vec::new();
        let mut source_nodes = 0usize;
        let mut poly_terms = 0usize;
        let mut poly_factors = 0usize;

        for &(atom, value) in &self.asserted {
            let (lhs, rhs) = comparison_children(self.terms.get(atom))?;
            for root in [lhs, rhs] {
                let (shape, visited) = self.inspect_arithmetic_term(root, &mut model_vars)?;
                source_nodes = source_nodes.checked_add(visited)?;
                if source_nodes > MAX_SOURCE_NODES
                    || shape.terms > MAX_EXPANDED_TERMS_PER_TERM
                    || shape.terms.checked_mul(shape.degree)? > MAX_POLY_FACTORS
                {
                    return None;
                }
            }

            match self.atom_to_multi(atom, value)? {
                MultiAtom::ConstTrue => {}
                MultiAtom::ConstFalse => return None,
                MultiAtom::Constraint(constraint) => {
                    poly_terms = poly_terms.checked_add(constraint.poly.terms.len())?;
                    for (monomial, _) in &constraint.poly.terms {
                        poly_factors = poly_factors.checked_add(monomial.len())?;
                    }
                    if poly_terms > MAX_POLY_TERMS || poly_factors > MAX_POLY_FACTORS {
                        return None;
                    }
                    constraints.push(constraint);
                }
            }
        }
        Some((constraints, model_vars))
    }

    /// Iteratively validate one arithmetic term before the existing recursive
    /// polynomial converter sees it.  Besides avoiding an unbounded call stack,
    /// the conservative term-count estimate rejects products-of-sums before
    /// exact expansion can allocate exponentially many monomials.
    fn inspect_arithmetic_term(
        &self,
        root: TermId,
        variables: &mut Vec<TermId>,
    ) -> Option<(PolyShape, usize)> {
        let mut shapes: crate::HashMap<TermId, PolyShape> = crate::HashMap::default();
        let mut stack = vec![(root, 0usize, false)];
        let mut visited = 0usize;

        while let Some((term, depth, expanded)) = stack.pop() {
            if depth > MAX_TERM_DEPTH {
                return None;
            }
            if shapes.contains_key(&term) {
                continue;
            }
            visited = visited.checked_add(1)?;
            if visited > MAX_SOURCE_NODES {
                return None;
            }

            match self.terms.get(term) {
                TermData::Const(Constant::Int(_) | Constant::Rational(_)) => {
                    shapes.insert(
                        term,
                        PolyShape {
                            terms: 1,
                            degree: 0,
                        },
                    );
                }
                TermData::Var(_, _) => {
                    variables.push(term);
                    shapes.insert(
                        term,
                        PolyShape {
                            terms: 1,
                            degree: 1,
                        },
                    );
                }
                TermData::App(Symbol::Named(name), args) => {
                    if !arithmetic_arity_is_supported(name.as_str(), args.len()) {
                        return None;
                    }
                    if !expanded {
                        stack.push((term, depth, true));
                        for &child in args.iter().rev() {
                            stack.push((child, depth + 1, false));
                        }
                        continue;
                    }
                    let shape = combine_shapes(name.as_str(), args, &shapes)?;
                    shapes.insert(term, shape);
                }
                _ => return None,
            }
        }
        Some((*shapes.get(&root)?, visited))
    }

    /// Try the current relaxation point and its bounded snapped variants.
    pub(crate) fn try_model_guided_grounding(&mut self, plan: &mut GroundingPlan) -> bool {
        if plan.exhausted() {
            return false;
        }
        let covers = std::mem::take(&mut plan.covers);
        let mut solved = None;
        'search: for snap in PinSnap::ORDERED {
            for cover in &covers {
                if plan.exhausted() {
                    break 'search;
                }
                let Some(pins) = self.read_grounding_pins(cover, snap) else {
                    continue;
                };
                if plan.tried.contains(&pins) {
                    continue;
                }
                plan.tried.push(pins.clone());
                plan.attempts += 1;
                if let Some(model) = residual::solve_grounded_residual(self, &pins, plan) {
                    solved = Some(model);
                    break 'search;
                }
            }
        }
        plan.covers = covers;

        let Some(model) = solved else {
            return false;
        };
        #[cfg(test)]
        let probe = GroundingProbe {
            successes: TEST_PROBE.with(std::cell::Cell::get).successes + 1,
            tentative_scopes: self.tentative_depth,
            scoped_bounds: self.lra.bounds_in_top_scopes(self.tentative_depth as usize),
            tangent_lemmas: self.tangent_lemma_count,
        };
        if !self.install_grounded_model(model) {
            return false;
        }
        #[cfg(test)]
        TEST_PROBE.with(|slot| slot.set(probe));
        if self.debug {
            tracing::debug!(
                "[NRA] model-guided grounding solved after {} residual solves",
                plan.attempts
            );
        }
        true
    }

    fn read_grounding_pins(
        &self,
        cover: &[TermId],
        snap: PinSnap,
    ) -> Option<Vec<(TermId, BigRational)>> {
        let mut pins = Vec::with_capacity(cover.len());
        for &variable in cover {
            pins.push((variable, snap.apply(self.var_value(variable)?)));
        }
        Some(pins)
    }

    /// Replace every reported support/auxiliary value with the verified point.
    fn install_grounded_model(&mut self, mut model: Vec<(TermId, BigRational)>) -> bool {
        // The caller may be MID refinement, with tangent lemmas, tentative
        // sign cuts and patch bounds live in an open scope (measured, see
        // `grounding_installs_its_verified_point_over_live_refinement_bounds`:
        // 16 lemmas and 20 scoped bounds at the instant it fires).  Retire the
        // model-derived ones before injecting rather than reasoning about
        // which of them the verified point happens to satisfy.  NOTE this is
        // hygiene, not a load-bearing guard: deleting this line changes no
        // test outcome, because LRA bounds only ever tighten and the next
        // `assert_literal` pops the scope anyway (`theory_impl.rs:15`).
        self.undo_tentative_patch();
        let mut products: Vec<_> = self
            .products()
            .map(|monomial| {
                (
                    monomial.vars.clone(),
                    monomial.aux_var,
                    monomial.coeff.clone(),
                )
            })
            .collect();
        products.sort_unstable_by_key(|(_, auxiliary, _)| auxiliary.0);
        for (factors, auxiliary, coefficient) in products {
            let bare_product = factors.iter().try_fold(BigRational::one(), |acc, factor| {
                self.eval_term_under_model(*factor, &model)
                    .map(|value| acc * value)
            });
            let Some(bare_product) = bare_product else {
                return false;
            };
            let exact_value = coefficient * bare_product;
            if let Some((_, stale_value)) = model
                .iter_mut()
                .find(|(variable, _)| *variable == auxiliary)
            {
                *stale_value = exact_value;
            } else {
                model.push((auxiliary, exact_value));
            }
        }
        self.inject_univariate_model(&model);
        debug_assert!(self.div_terms.is_empty());
        debug_assert!(!self.zero_divisor_model_is_unsound());
        true
    }
}

fn comparison_children(term: &TermData) -> Option<(TermId, TermId)> {
    match term {
        TermData::App(Symbol::Named(name), args)
            if args.len() == 2
                && matches!(
                    name.as_str(),
                    "<" | "<=" | "=" | ">=" | ">" | "distinct" | "!="
                ) =>
        {
            Some((args[0], args[1]))
        }
        _ => None,
    }
}

fn arithmetic_arity_is_supported(operator: &str, arity: usize) -> bool {
    match operator {
        "+" | "*" => arity > 0,
        "-" => arity > 0,
        _ => false,
    }
}

fn combine_shapes(
    operator: &str,
    args: &[TermId],
    shapes: &crate::HashMap<TermId, PolyShape>,
) -> Option<PolyShape> {
    let mut terms = if operator == "*" { 1usize } else { 0usize };
    let mut degree = 0usize;
    for arg in args {
        let child = shapes.get(arg)?;
        if operator == "*" {
            terms = terms.checked_mul(child.terms)?;
            degree = degree.checked_add(child.degree)?;
        } else {
            terms = terms.checked_add(child.terms)?;
            degree = degree.max(child.degree);
        }
        if terms > MAX_EXPANDED_TERMS_PER_TERM || degree > MAX_POLY_FACTORS {
            return None;
        }
    }
    Some(PolyShape { terms, degree })
}

fn nonlinear_monomials(constraints: &[MultiConstraint]) -> Option<Vec<Vec<TermId>>> {
    let mut monomials = Vec::new();
    let mut factors = 0usize;
    for constraint in constraints {
        for (monomial, _) in &constraint.poly.terms {
            if monomial.len() < 2 {
                continue;
            }
            factors = factors.checked_add(monomial.len())?;
            if factors > MAX_POLY_FACTORS {
                return None;
            }
            monomials.push(monomial.clone());
        }
    }
    monomials.sort_unstable();
    monomials.dedup();
    if monomials.is_empty() || monomials.len() > MAX_MONOMIALS {
        None
    } else {
        Some(monomials)
    }
}

#[cfg(test)]
mod tests;
