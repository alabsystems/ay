// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Staged finite-model pins and exact emitted-witness validation.
//!
//! Search may propose values, but this module never commits them. It builds a
//! semantic clone, requires that clone to satisfy the checked residual and all
//! pins, and returns it affinely to the query-authority installer. That installer
//! performs output-only completion, exact-root/model sealing, and the single
//! public model replacement only after every fallible check has succeeded.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{TermData, TermId, TermStore};

use super::{finite_value_term, is_pinnable_finite_sort, trace, AuthoredUniversal, LaneBudget};
use crate::executor::model::{EvalValue, Model};
use crate::executor::Executor;

/// Cap on pins so a huge ground slice cannot blow up the sub-queries.
const MAX_PINS: usize = 256;

/// What one certificate pass established about the authored root window.
///
/// There is deliberately no `Refuted` variant. A refuted residual under
/// arbitrary pins does not refute the authored query, and the available dual
/// has no single authored-scope translated proof for public UNSAT authority.
#[derive(Debug)]
pub(super) enum PassOutcome {
    /// The query is satisfiable and this staged model was checked against the
    /// residual and pins. It carries no publication authority until the atomic
    /// model-bound installer consumes it.
    Certified(Model),
    /// Counterexample instances were produced for the next round.
    Refined,
    /// Nothing established; the caller must fail closed.
    Declined,
}

impl PassOutcome {
    /// Trace label. `Debug` on this enum prints the whole staged `Model`, which
    /// is megabytes per certified pass and unreadable in a `--debug-cert` log.
    pub(super) fn label(&self) -> &'static str {
        match self {
            Self::Certified(_) => "certified",
            Self::Refined => "refined",
            Self::Declined => "declined",
        }
    }
}

/// Collect every `Var` leaf of a quantifier-free term.
///
/// Over-collecting costs probe work and under-collecting costs a decision. A
/// returned probe value never carries authority: the final exact evaluator
/// check is the sole acceptance boundary for the staged model.
fn collect_var_leaves(
    terms: &TermStore,
    term: TermId,
    out: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    match terms.get(term) {
        TermData::Var(..) => out.push(term),
        TermData::App(_, args) => {
            for &arg in args {
                collect_var_leaves(terms, arg, out, seen);
            }
        }
        TermData::Not(inner) => collect_var_leaves(terms, *inner, out, seen),
        TermData::Ite(condition, then_term, else_term) => {
            for sub in [*condition, *then_term, *else_term] {
                collect_var_leaves(terms, sub, out, seen);
            }
        }
        _ => {}
    }
}

/// Collect the free finite-sorted `Var` leaves of one quantifier body.
fn collect_finite_var_leaves(
    terms: &TermStore,
    term: TermId,
    bound: &HashSet<String>,
    out: &mut Vec<TermId>,
    seen: &mut HashSet<TermId>,
) {
    if !seen.insert(term) {
        return;
    }
    match terms.get(term) {
        TermData::Var(name, _) => {
            if !bound.contains(name) && is_pinnable_finite_sort(terms.sort(term)) {
                out.push(term);
            }
        }
        TermData::App(_, args) => {
            for &arg in args {
                collect_finite_var_leaves(terms, arg, bound, out, seen);
            }
        }
        TermData::Not(inner) => {
            collect_finite_var_leaves(terms, *inner, bound, out, seen);
        }
        TermData::Ite(condition, then_term, else_term) => {
            for sub in [*condition, *then_term, *else_term] {
                collect_finite_var_leaves(terms, sub, bound, out, seen);
            }
        }
        TermData::Let(bindings, body) => {
            let (bindings, body) = (bindings.clone(), *body);
            for (_, value) in &bindings {
                collect_finite_var_leaves(terms, *value, bound, out, seen);
            }
            collect_finite_var_leaves(terms, body, bound, out, seen);
        }
        // Candidates have quantifier-free bodies. Missing a future term form
        // only weakens the pin premise and therefore loses completeness.
        _ => {}
    }
}

impl Executor {
    /// Build ground equalities pinning every free finite-sorted body symbol.
    ///
    /// A symbol absent from the candidate model may be assigned an arbitrary
    /// canonical value: pins are premises of checked UNSAT obligations plus one
    /// checked SAT confirm. The choice is recorded so the staged output model
    /// receives the same value before the residual-and-pins check.
    pub(super) fn finite_model_pins(
        &mut self,
        leaves_of: &[AuthoredUniversal],
        completions: &mut Vec<(TermId, EvalValue)>,
    ) -> (Vec<TermId>, bool) {
        let Some(model) = self.last_model.clone() else {
            return (Vec::new(), false);
        };
        let bound: HashSet<String> = leaves_of
            .iter()
            .flat_map(|leaf| leaf.vars.iter().map(|(name, _)| name.clone()))
            .collect();
        let mut leaves = Vec::new();
        let mut seen = HashSet::default();
        for leaf in leaves_of {
            collect_finite_var_leaves(&self.ctx.terms, leaf.body, &bound, &mut leaves, &mut seen);
        }
        leaves.sort_unstable();
        leaves.dedup();
        if leaves.len() > MAX_PINS {
            return (Vec::new(), false);
        }

        let mut pins = Vec::new();
        let mut total = true;
        for leaf in leaves {
            let sort = self.ctx.terms.sort(leaf).clone();
            let mut value = self.evaluate_term(&model, leaf);
            let mut completed = false;
            if matches!(value, EvalValue::Unknown) {
                if let Some(default) = self.unconstrained_default_value(&sort) {
                    trace(|| format!("pin completed: sort={sort:?} default={default:?}"));
                    value = default;
                    completed = true;
                }
            }
            if let Some(value_term) = finite_value_term(&mut self.ctx.terms, &sort, &value) {
                pins.push(self.ctx.terms.mk_eq(leaf, value_term));
                if completed {
                    completions.push((leaf, value));
                }
            } else {
                trace(|| format!("pin declined: sort={sort:?} value={value:?}"));
                total = false;
            }
        }
        (pins, total)
    }

    /// Prepare, but do not install, a verified model of `confirm`.
    ///
    /// `confirm` is the residual root window followed by every pin. All writes
    /// target a clone; a decline leaves the installed model and every evidence
    /// token untouched. Probe values are proposals only and are accepted solely
    /// when every element of `confirm` re-evaluates to `Bool(true)` afterward.
    pub(super) fn finite_model_prepare_witness(
        &mut self,
        confirm: &[TermId],
        completions: &[(TermId, EvalValue)],
        budget: LaneBudget,
    ) -> Option<Model> {
        let mut model = self.last_model.clone()?;
        for (leaf, value) in completions {
            if !Self::insert_completed_value(&self.ctx.terms, &mut model, *leaf, value) {
                trace(|| "witness: completion refused by insert_completed_value".to_string());
                return None;
            }
        }
        if !self.finite_model_model_satisfies(&model, confirm) {
            let mut targets = Vec::new();
            let mut seen = HashSet::default();
            for &term in confirm {
                collect_var_leaves(&self.ctx.terms, term, &mut targets, &mut seen);
            }
            targets
                .retain(|&target| matches!(self.evaluate_term(&model, target), EvalValue::Unknown));
            targets.sort_unstable();
            if targets.is_empty() {
                trace(|| {
                    "witness: model falsifies the residual and nothing is fillable".to_string()
                });
                return None;
            }
            // The gap-filling probe is bounded like every other sub-solve of
            // the pass. It PROPOSES values only: a probe that returns nothing,
            // or values that do not work, falls through to the re-check below
            // and declines. Bounding it therefore cannot weaken the check.
            let values = self.probe_finite_witness_values(
                confirm.to_vec(),
                &targets,
                budget.sub_solve_ms(),
            )?;
            for (&target, value) in targets.iter().zip(&values) {
                if matches!(value, EvalValue::Unknown) {
                    continue;
                }
                if !Self::insert_completed_value(&self.ctx.terms, &mut model, target, value) {
                    trace(|| "witness: probe value refused".to_string());
                    return None;
                }
            }
            if !self.finite_model_model_satisfies(&model, confirm) {
                trace(|| "witness: still not a model of the residual".to_string());
                return None;
            }
        }
        trace(|| "witness: staged model verified against residual and pins".to_string());
        Some(model)
    }

    fn finite_model_model_satisfies(&mut self, model: &Model, terms: &[TermId]) -> bool {
        terms
            .iter()
            .all(|&term| matches!(self.evaluate_term(model, term), EvalValue::Bool(true)))
    }
}

#[cfg(test)]
mod tests {
    use crate::executor::Executor;

    /// Hand-minimised `rlim_invariant` index 88. SAT: choose `S` different from
    /// `+zero`. Bitwuzla 0.9.1 and z3 4.16.0 independently agree.
    const UNPINNED_LEAF_SAT: &str = r#"
        (set-logic BVFPLRA)
        (declare-fun Y () (_ FloatingPoint 8 24))
        (declare-fun S () (_ FloatingPoint 8 24))
        (assert (not (and (exists ((d (_ FloatingPoint 8 24)))
                            (and (fp.geq d (_ +zero 8 24))
                                 (fp.leq d ((_ to_fp 8 24) RNE 16.0))
                                 (= (fp.sub RNE ((_ to_fp 8 24) RNE (_ bv0 32)) d) Y)))
                          (= ((_ to_fp 8 24) RNE (_ bv0 32)) S))))
        (check-sat)
    "#;

    fn run(script: &str) -> Vec<String> {
        run_with_lane_budget(script, None)
    }

    fn run_with_lane_budget(script: &str, budget_ms: Option<u64>) -> Vec<String> {
        let commands = ay_frontend::parse(script).expect("fixture must parse");
        let mut executor = Executor::new();
        executor.finite_model_lane.budget_ms_override = budget_ms;
        executor.execute_all(&commands).expect("fixture must solve")
    }

    /// Mutation control: removing unknown-leaf completion makes this `unknown`.
    #[test]
    fn completed_pin_decides_an_unpinned_leaf() {
        assert_eq!(run(UNPINNED_LEAF_SAT), vec!["sat".to_string()]);
    }

    /// BARRIER for the lane wall budget (#witness-check-cost).
    ///
    /// The first assertion is the POSITIVE CONTROL and it is the whole point:
    /// this exact fixture, this exact executor, reaches
    /// `finite_model_certificate_pass` and certifies. So the second assertion
    /// is not testing an unreachable branch — it drives the same lane with an
    /// account that is already spent and requires the fail-closed `unknown`.
    ///
    /// MUTATION-TESTED, and the result is reported exactly, because it is not
    /// the obvious one:
    ///
    /// * `LaneBudget::sub_solve_ms -> FINITE_MODEL_PROBE_MS` (the account stops
    ///   reaching the sub-solves) — this test PASSES. Review measured it and
    ///   the original claim here was BACKWARDS. That single mutation is caught
    ///   by `a_zero_override_opens_an_already_spent_account` instead, and it
    ///   does not make the budget inert either: `budget.spent()` still declines
    ///   at the early-return checks. What THIS test catches is the JOINT no-op
    ///   (both `sub_solve_ms` and `spent` mutated), measured at 13 passed / 2
    ///   failed. So the barrier is non-vacuous — for a different reason than
    ///   was claimed.
    /// * `LaneBudget::spent -> false` alone — this test still PASSES. The
    ///   early-return checks are belt, not braces, for this fixture: a spent
    ///   account also hands every sub-solve 0 ms, which fails closed on its
    ///   own. `spent` is pinned instead by
    ///   `lane_account_tests::a_zero_override_opens_an_already_spent_account`,
    ///   which that mutation DOES fail. Two tests, one for each mechanism —
    ///   claiming one test covers both would be the vacuous-barrier mistake
    ///   this lane has already made once.
    #[test]
    fn a_spent_lane_budget_fails_closed() {
        assert_eq!(
            run_with_lane_budget(UNPINNED_LEAF_SAT, None),
            vec!["sat".to_string()],
            "positive control: the fixture must reach the lane and certify"
        );
        assert_eq!(
            run_with_lane_budget(UNPINNED_LEAF_SAT, Some(0)),
            vec!["unknown".to_string()],
            "a spent lane budget must decline, not publish an unchecked witness"
        );
    }

    /// A budget large enough for this pass must not change the answer, so the
    /// barrier above is measuring the SPENT account and not merely the
    /// presence of an override.
    #[test]
    fn a_funded_lane_budget_still_certifies() {
        assert_eq!(
            run_with_lane_budget(UNPINNED_LEAF_SAT, Some(60_000)),
            vec!["sat".to_string()]
        );
    }

    /// Mutation control: accepting the predecessor model without checking the
    /// residual prints `S = +zero`, which falsifies the sole assertion.
    #[test]
    fn emitted_witness_satisfies_the_query() {
        let script = UNPINNED_LEAF_SAT.replace("(check-sat)", "(check-sat)\n(get-model)");
        let outputs = run(&script);
        assert_eq!(outputs.first().map(String::as_str), Some("sat"));
        let model = outputs.get(1).expect("(get-model) must print a witness");
        let binding = model
            .lines()
            .find(|line| line.contains("define-fun S "))
            .expect("the witness must interpret S");
        assert!(
            !binding.contains("+zero"),
            "witness falsifies its own query: {binding}"
        );
    }
}
