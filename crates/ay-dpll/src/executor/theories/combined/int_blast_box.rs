// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Small-box model search for QF_NIA by bit-blasting (#nia-box-blast,
//! AY-SMT-5).
//!
//! Many SAT QF_NIA instances (AProVE termination proofs above all) have a
//! model with tiny values: three of the four SAT instances of AY-SMT-5 have
//! one with every variable in `[-2, 2]` or `[-16, 16]`, while the
//! incremental linearisation walks splits and the integer local search
//! spends its 60 % share without finding one. Their rivals find these models
//! in under a second.
//!
//! The lane BOXES every Int variable — `[-r, r]` intersected with the bounds
//! the top-level facts prove (`collect_int_facts`), or a width-`2r` box at
//! the proven bound when that bound lies outside `[-r, r]` — for
//! `r = 1, 2, 4, 8, 16, ...`, and decides each box EXACTLY with the eager
//! bit-blaster through the translator of `int_blast.rs`, nonlinear products
//! included (`IntBlaster::nonlinear_products`). The common signed width `W`
//! is chosen so that every Int-sorted subterm's interval under the box fits,
//! so `+`, `-` and `*` never wrap and the signed order is the integer order.
//!
//! SOUNDNESS. A box is an ADDED constraint, so a box that is UNSAT says
//! nothing about the instance: the lane never returns `unsat`, it moves to
//! the next box or gives up (`None`). A box that is SAT yields a candidate
//! Int model (the signed value of each vector) that must re-evaluate EVERY
//! original root to `true` independently (`bridge_sat_model_validates`)
//! before it is offered, and the caller then runs the ordinary SAT
//! finalisation and publication gates on it. A translation slip can only
//! lose a model, never manufacture a `sat`.

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::time::Instant;
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use ay_lia::LiaModel;
use num_bigint::BigInt;

use super::super::super::super::Executor;
use super::super::collect_int_facts;
use super::{children, signed_value, IntBlastPlan, IntBlaster, IntVarEncoding, Interval};
use crate::executor::model::{EvalValue, Model};
use crate::executor::theories::bv::BvSolveConfig;
use crate::executor_types::{ExecutorError, Result, SolveResult};

/// Box radii tried, in order (geometric growth).
const BOX_RADII: [u32; 6] = [1, 2, 4, 8, 16, 32];

/// Widest common signed width a box is blasted at. A product of `d` factors
/// boxed to `[-r, r]` needs about `d * log2(r)` bits; beyond this the
/// multipliers cost more than the box is likely to repay.
const BOX_BLAST_MAX_WIDTH: u32 = 24;

/// Share of the remaining wall time the lane may use, in percent, and its
/// absolute ceiling. It runs BEFORE the incremental-linearisation search,
/// so it must stay cheap when it finds nothing.
const BOX_BLAST_WALL_SHARE_PCT: u32 = 10;
const BOX_BLAST_WALL_CAP: std::time::Duration = std::time::Duration::from_secs(20);

/// Interval of an Int-sorted term under the box, nonlinear products
/// included; `None` outside the fragment (`div`, `mod`, a UF, a Real, ...).
fn box_interval(
    terms: &TermStore,
    term: TermId,
    boxes: &HashMap<TermId, Interval>,
    memo: &mut HashMap<TermId, Option<Interval>>,
) -> Option<Interval> {
    if let Some(cached) = memo.get(&term) {
        return cached.clone();
    }
    memo.insert(term, None);
    let result = box_interval_inner(terms, term, boxes, memo);
    memo.insert(term, result.clone());
    result
}

fn mul_interval(a: &Interval, b: &Interval) -> Interval {
    let products = [&a.lo * &b.lo, &a.lo * &b.hi, &a.hi * &b.lo, &a.hi * &b.hi];
    let mut lo = products[0].clone();
    let mut hi = products[0].clone();
    for p in &products[1..] {
        if *p < lo {
            lo = p.clone();
        }
        if *p > hi {
            hi = p.clone();
        }
    }
    Interval { lo, hi }
}

fn box_interval_inner(
    terms: &TermStore,
    term: TermId,
    boxes: &HashMap<TermId, Interval>,
    memo: &mut HashMap<TermId, Option<Interval>>,
) -> Option<Interval> {
    if *terms.sort(term) != Sort::Int {
        return None;
    }
    match terms.get(term).clone() {
        TermData::Const(Constant::Int(v)) => Some(Interval::point(v)),
        TermData::Var(_, _) => boxes.get(&term).cloned(),
        TermData::Ite(_, t, e) => {
            let t = box_interval(terms, t, boxes, memo)?;
            let e = box_interval(terms, e, boxes, memo)?;
            Some(t.hull(&e))
        }
        TermData::App(Symbol::Named(name), args) if !args.is_empty() => {
            let mut parts = Vec::with_capacity(args.len());
            for &arg in &args {
                parts.push(box_interval(terms, arg, boxes, memo)?);
            }
            let mut iter = parts.into_iter();
            let first = iter.next()?;
            match name.as_str() {
                "+" => Some(iter.fold(first, |acc, p| acc.add(&p))),
                "-" if args.len() == 1 => Some(first.neg()),
                "-" => Some(iter.fold(first, |acc, p| acc.sub(&p))),
                "*" => Some(iter.fold(first, |acc, p| mul_interval(&acc, &p))),
                _ => None,
            }
        }
        _ => None,
    }
}

/// Whether some product in the roots has two or more non-constant factors.
fn has_nonlinear_product(terms: &TermStore, roots: &[TermId]) -> bool {
    let mut seen = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
            if name == "*"
                && args
                    .iter()
                    .filter(|&&a| !matches!(terms.get(a), TermData::Const(_)))
                    .count()
                    >= 2
            {
                return true;
            }
        }
        stack.extend(children(terms, term));
    }
    false
}

/// The Int variables reachable from the roots, in id order.
fn int_vars(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    let mut seen = HashSet::default();
    let mut vars = Vec::new();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if matches!(terms.get(term), TermData::Var(_, _)) && *terms.sort(term) == Sort::Int {
            vars.push(term);
        }
        stack.extend(children(terms, term));
    }
    vars.sort_unstable_by_key(|v| v.0);
    vars
}

/// The box of one variable at radius `r`: `[-r, r]` met with its proven
/// bounds, or a width-`2r` box at a proven bound that lies outside
/// `[-r, r]`. `None` when the proven bounds are themselves contradictory
/// (the lane then declines and leaves that to the exact search).
fn variable_box(lower: Option<&BigInt>, upper: Option<&BigInt>, r: u32) -> Option<Interval> {
    let r = BigInt::from(r);
    let mut lo = match lower {
        Some(l) if *l > -&r => l.clone(),
        _ => -&r,
    };
    let mut hi = match upper {
        Some(u) if *u < r => u.clone(),
        _ => r.clone(),
    };
    if lo > hi {
        match (lower, upper) {
            (Some(l), _) if *l > r => {
                lo = l.clone();
                hi = l + BigInt::from(2u32) * &r;
                if let Some(u) = upper {
                    if *u < hi {
                        hi = u.clone();
                    }
                }
            }
            (_, Some(u)) if *u < -&r => {
                hi = u.clone();
                lo = u - BigInt::from(2u32) * &r;
                if let Some(l) = lower {
                    if *l > lo {
                        lo = l.clone();
                    }
                }
            }
            _ => {}
        }
    }
    (lo <= hi).then_some(Interval { lo, hi })
}

/// The blast plan for one box, or `None` when some Int subterm is outside
/// the fragment or the width would exceed `BOX_BLAST_MAX_WIDTH`.
fn box_plan(terms: &TermStore, roots: &[TermId], vars: &[TermId], r: u32) -> Option<IntBlastPlan> {
    let facts = collect_int_facts(terms, roots);
    let mut boxes: HashMap<TermId, Interval> = HashMap::default();
    let mut encodings: HashMap<TermId, IntVarEncoding> = HashMap::default();
    let mut synthetic = Vec::with_capacity(vars.len());
    for &var in vars {
        let interval = variable_box(facts.lower_bound(var), facts.upper_bound(var), r)?;
        boxes.insert(var, interval.clone());
        encodings.insert(var, IntVarEncoding::Bounded);
        synthetic.push((var, interval));
    }
    let mut width = 2u32;
    let mut memo = HashMap::default();
    let mut seen = HashSet::default();
    let mut stack: Vec<TermId> = roots.to_vec();
    while let Some(term) = stack.pop() {
        if !seen.insert(term) {
            continue;
        }
        if *terms.sort(term) == Sort::Int {
            let interval = box_interval(terms, term, &boxes, &mut memo)?;
            width = width.max(interval.signed_width());
            if width > BOX_BLAST_MAX_WIDTH {
                return None;
            }
        }
        stack.extend(children(terms, term));
    }
    Some(IntBlastPlan {
        encodings,
        width,
        synthetic,
    })
}

impl Executor {
    /// Validate a proposed assignment against the original query before it
    /// can short-circuit ordinary nonlinear solving.
    pub(in crate::executor) fn accept_nia_box_witness(&mut self, model: Model) -> Result<bool> {
        let prior_model = self.last_model.replace(model);
        let prior_result = self.last_result.replace(SolveResult::Sat);
        let prior_reason = self.last_unknown_reason.take();
        let prior_validated = std::mem::replace(&mut self.last_model_validated, false);
        let prior_skip = std::mem::replace(&mut self.skip_model_eval, false);
        let prior_defer = std::mem::replace(&mut self.defer_model_validation, false);
        let prior_clause = self.qfax_refinement_clause.clone();
        let prior_core = self.last_assumption_core.clone();

        let finalized = self.finalize_sat_model_validation();
        let confirmed = matches!(finalized, Ok(SolveResult::Sat))
            && self.last_model_validated
            && matches!(
                self.confirm_sat_with_independent_gate(),
                ay_model_check::GateVerdict::ConfirmedSat
            );
        self.skip_model_eval = prior_skip;
        self.defer_model_validation = prior_defer;
        if confirmed {
            return Ok(true);
        }

        self.last_model = prior_model;
        self.last_result = prior_result;
        self.last_unknown_reason = prior_reason;
        self.last_model_validated = prior_validated;
        self.qfax_refinement_clause = prior_clause;
        self.last_assumption_core = prior_core;
        finalized?;
        Ok(false)
    }

    /// Search growing boxes for a model of the QF_NIA `roots` (module doc).
    /// `Ok(Some(model))` returns a model that re-evaluated every root to
    /// `true`; `Ok(None)` means no box produced one within the lane's share
    /// of the deadline. Never returns `unsat`. Runs only under a deadline.
    pub(in crate::executor) fn try_nia_box_blast(
        &mut self,
        roots: &[TermId],
    ) -> Result<Option<Box<Model>>> {
        let Some(deadline) = self.current_solve_deadline() else {
            return Ok(None);
        };
        if self.should_abort_theory_loop() {
            return Ok(None);
        }
        if !has_nonlinear_product(&self.ctx.terms, roots) {
            self.last_statistics
                .set_string("nia.box_blast", "skipped-linear");
            return Ok(None);
        }
        let started = Instant::now();
        if deadline <= started {
            return Ok(None);
        }
        let share = ((deadline - started) * BOX_BLAST_WALL_SHARE_PCT / 100).min(BOX_BLAST_WALL_CAP);
        let lane_deadline = started + share;
        let vars = int_vars(&self.ctx.terms, roots);
        let mut outcome = String::from("none");
        for r in BOX_RADII {
            if Instant::now() >= lane_deadline || self.should_abort_theory_loop() {
                outcome = format!("budget r={r}");
                break;
            }
            let Some(plan) = box_plan(&self.ctx.terms, roots, &vars, r) else {
                outcome = format!("declined r={r}");
                break;
            };
            match self.solve_nia_box(roots, plan, lane_deadline)? {
                BoxOutcome::Sat(model) => {
                    self.last_statistics
                        .set_string("nia.box_blast", format!("sat r={r}"));
                    return Ok(Some(model));
                }
                BoxOutcome::Empty => {
                    outcome = format!("box-unsat r={r}");
                }
                BoxOutcome::Undecided => {
                    outcome = format!("undecided r={r}");
                    break;
                }
            }
        }
        self.last_statistics.set_string("nia.box_blast", outcome);
        Ok(None)
    }

    /// Decide one box in a disposable probe (as `solve_bv_lia_by_int_blast`
    /// does) under the lane's own deadline.
    fn solve_nia_box(
        &mut self,
        roots: &[TermId],
        plan: IntBlastPlan,
        lane_deadline: Instant,
    ) -> Result<BoxOutcome> {
        let Some(mut probe) = self.int_blast_probe() else {
            return Ok(BoxOutcome::Undecided);
        };
        let lane_deadline = match self.current_solve_deadline() {
            Some(outer) if outer < lane_deadline => outer,
            _ => lane_deadline,
        };
        probe.set_solve_controls(self.solve_interrupt.clone(), Some(lane_deadline));
        let shared_terms = self.ctx.terms.len();
        let (translated, (width, bindings)) = {
            let mut blaster = IntBlaster::new(&mut probe.ctx.terms, plan);
            blaster.nonlinear_products = true;
            let translated: Option<Vec<TermId>> = roots
                .iter()
                .map(|&root| blaster.translate(root))
                .collect::<Option<Vec<TermId>>>()
                .and_then(|mut translated| {
                    translated.extend(blaster.synthetic_bounds()?);
                    Some(translated)
                });
            (translated, blaster.into_bindings())
        };
        let Some(translated) = translated else {
            return Ok(BoxOutcome::Undecided);
        };
        probe.ctx.assertions = translated;
        let result = probe.solve_bv_core(BvSolveConfig::qf_bv(), &[]);
        if self.should_abort_theory_loop() {
            return Ok(BoxOutcome::Undecided);
        }
        let bv_model = match result {
            // The box only: no verdict about the instance.
            Ok(SolveResult::Unsat(_)) => return Ok(BoxOutcome::Empty),
            Ok(SolveResult::Sat) => match probe.last_model.take() {
                Some(model) => model,
                None => return Ok(BoxOutcome::Undecided),
            },
            Ok(SolveResult::Unknown) | Err(ExecutorError::ModelValidation(_)) => {
                return Ok(BoxOutcome::Undecided)
            }
            Err(error) => return Err(error),
        };
        let mut values: HashMap<TermId, BigInt> = HashMap::default();
        for (var, bv, _) in bindings {
            let EvalValue::BitVec { value, width: got } = probe.evaluate_term(&bv_model, bv) else {
                return Ok(BoxOutcome::Undecided);
            };
            values.insert(var, signed_value(value, width.min(got)));
        }
        drop(probe);
        let Some(mut model) = bv_model.restricted_to_shared_terms(shared_terms) else {
            return Ok(BoxOutcome::Undecided);
        };
        model.lia_model = Some(LiaModel { values });
        let prior = self.last_model.replace(model);
        let valid = self.bridge_sat_model_validates(roots);
        let candidate = std::mem::replace(&mut self.last_model, prior);
        match (valid, candidate) {
            (true, Some(model)) => Ok(BoxOutcome::Sat(Box::new(model))),
            _ => Ok(BoxOutcome::Undecided),
        }
    }
}

/// What one box decided.
enum BoxOutcome {
    /// A model of the box that re-evaluates every root to `true`.
    Sat(Box<Model>),
    /// The box has no model (a statement about the box only).
    Empty,
    /// Not decided (budget, decline, or a candidate that failed validation).
    Undecided,
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nia_box_witness_rejects_a_forged_assignment_and_restores_state() {
        let mut executor = Executor::new();
        let x = executor.ctx.terms.mk_var("x", Sort::Int);
        let square = executor.ctx.terms.mk_mul(vec![x, x]);
        let four = executor.ctx.terms.mk_int(BigInt::from(4));
        let original = executor.ctx.terms.mk_eq(square, four);
        executor.ctx.assertions.push(original);
        executor.last_result = Some(SolveResult::Unknown);
        executor.skip_model_eval = true;
        executor.defer_model_validation = true;
        executor.qfax_refinement_clause = Some(vec![(original, false)]);
        executor.last_assumption_core = Some(vec![original]);

        let mut forged = Model::empty();
        forged.lia_model = Some(LiaModel {
            values: [(x, BigInt::from(3))].into_iter().collect(),
        });
        assert!(!executor.accept_nia_box_witness(forged).unwrap());
        assert!(executor.last_model.is_none());
        assert!(matches!(executor.last_result, Some(SolveResult::Unknown)));
        assert!(executor.skip_model_eval && executor.defer_model_validation);
        assert_eq!(
            executor.qfax_refinement_clause,
            Some(vec![(original, false)])
        );
        assert_eq!(executor.last_assumption_core, Some(vec![original]));
    }

    fn iv(lo: i64, hi: i64) -> Interval {
        Interval {
            lo: BigInt::from(lo),
            hi: BigInt::from(hi),
        }
    }

    #[test]
    fn variable_box_meets_the_radius_with_proven_bounds() {
        assert_eq!(variable_box(None, None, 2), Some(iv(-2, 2)));
        assert_eq!(
            variable_box(Some(&BigInt::from(0)), None, 2),
            Some(iv(0, 2))
        );
        assert_eq!(
            variable_box(None, Some(&BigInt::from(1)), 4),
            Some(iv(-4, 1))
        );
        // A proven bound outside the radius: a width-2r box at that bound.
        assert_eq!(
            variable_box(Some(&BigInt::from(10)), None, 2),
            Some(iv(10, 14))
        );
        assert_eq!(
            variable_box(Some(&BigInt::from(10)), Some(&BigInt::from(11)), 2),
            Some(iv(10, 11))
        );
        assert_eq!(
            variable_box(None, Some(&BigInt::from(-9)), 1),
            Some(iv(-11, -9))
        );
        // Contradictory proven bounds: decline.
        assert_eq!(
            variable_box(Some(&BigInt::from(5)), Some(&BigInt::from(3)), 1),
            None
        );
    }

    #[test]
    fn product_interval_covers_every_sign_combination() {
        assert_eq!(mul_interval(&iv(-2, 3), &iv(-5, 4)), iv(-15, 12));
        assert_eq!(mul_interval(&iv(1, 2), &iv(3, 4)), iv(3, 8));
        assert_eq!(mul_interval(&iv(-2, -1), &iv(3, 4)), iv(-8, -3));
    }

    #[test]
    fn box_width_covers_a_cubic_term() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let xxy = terms.mk_mul(vec![x, x, y]);
        let c = terms.mk_int(BigInt::from(7));
        let eq = terms.mk_eq(xxy, c);
        let vars = int_vars(&terms, &[eq]);
        assert_eq!(vars.len(), 2);
        assert!(has_nonlinear_product(&terms, &[eq]));
        // r = 4: |x*x*y| <= 64 needs 8 signed bits.
        let plan = box_plan(&terms, &[eq], &vars, 4).expect("in fragment");
        assert_eq!(plan.width, 8);
    }
}
