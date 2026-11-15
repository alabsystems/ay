// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The QSAT route's ground kernel: disposable probe executors.
//!
//! The verdict and the model come from a plain solve of `formulas ∧
//! assumptions` on the full lane for the query's category, and the model is
//! re-evaluated exactly against every formula and assumption before it is
//! trusted. Only an UNSAT whose core will be projected pays a second,
//! assumption-based solve; a strict sub-core must re-refute on the plain lane
//! before it replaces "every assumption". A decisive UNSAT (one that ends the
//! game) is confirmed by an independent solve over canonicalized atoms, with
//! the full `check-sat` pipeline as a bounded refuter. No authority crosses
//! back: values and core indices only.
//!
//! Every probe is bounded by the query's deadline (the route's per-query
//! cap), never by a budget captured earlier in the query.

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::time::Instant;
use ay_core::{Sort, TermId};

use super::super::model::EvalValue;
use super::super::Executor;
use crate::executor_types::{Result, SolveResult};
use crate::logic_detection::{LogicCategory, TheoryKind};
use crate::qsat::{self, KernelAnswer, Val};

fn eval_value(v: EvalValue) -> Option<Val> {
    match v {
        EvalValue::Rational(r) => Some(Val::Num(r)),
        EvalValue::Bool(b) => Some(Val::Bool(b)),
        _ => None,
    }
}

/// The ground category of a query over `targets`.
fn category_of(executor: &Executor, targets: &[TermId]) -> LogicCategory {
    let (mut ints, mut reals) = (false, false);
    for &t in targets {
        match executor.ctx.terms.sort(t) {
            Sort::Int => ints = true,
            Sort::Real => reals = true,
            _ => {}
        }
    }
    match (ints, reals) {
        (true, true) => LogicCategory::QfLira,
        (true, false) => LogicCategory::QfLia,
        (false, true) => LogicCategory::QfLra,
        (false, false) => LogicCategory::Propositional,
    }
}

/// The most the confirmation's pipeline refuter may take.
const CONFIRM_PIPELINE_MS: u64 = 500;

fn millis_since(started: Instant) -> u64 {
    u64::try_from(
        Instant::now()
            .saturating_duration_since(started)
            .as_millis(),
    )
    .unwrap_or(u64::MAX)
}

/// Milliseconds left until `deadline` (0 once it passed).
fn millis_until(deadline: Instant) -> u64 {
    u64::try_from(
        deadline
            .saturating_duration_since(Instant::now())
            .as_millis(),
    )
    .unwrap_or(u64::MAX)
}

impl Executor {
    /// A disposable probe over `roots` with the kernel's settings.
    pub(super) fn qsat_probe(&self, roots: &[TermId], budget_ms: u64) -> Option<Executor> {
        let ctx = self.isolated_probe_context(roots)?;
        let mut probe = self.qpf_probe_executor(ctx, budget_ms);
        probe.qsat_route.inert = true;
        probe.original_problem_had_quantifiers = false;
        probe.incremental_mode = false;
        probe.begin_public_solve(false);
        probe.bind_unsat_query_assumptions(&[]);
        // The kernel's answers are hints: no proof is recorded or checked.
        probe.proof_tracker.disable();
        // Game queries are wide Boolean combinations over few variables:
        // implied-bound derivation on every check costs more than it prunes
        // (the nested-CEGQI oracle's measured setting).
        probe.qlra_lane.probe_lra_no_implied_bounds = true;
        Some(probe)
    }

    /// `roots` with every negatively occurring arithmetic equality split
    /// into its two inequalities (`split`), or as given.
    fn qsat_formulation(&mut self, roots: &[TermId], split: bool) -> Vec<TermId> {
        if !split {
            return roots.to_vec();
        }
        let mut memo = HashMap::default();
        roots
            .iter()
            .map(|&r| {
                qsat::formula::split_negative_equalities(&mut self.ctx.terms, r, true, &mut memo)
            })
            .collect()
    }

    /// Solve `roots` under two equivalent formulations, tried in the order
    /// that last succeeded: as given, and with every negatively occurring
    /// arithmetic equality split into its two inequalities (Boolean splits
    /// instead of theory disequalities). The ground lanes stall on different
    /// shapes of each; the first attempt gets a third of the query's time (at
    /// most 2 s) when the second can still follow. Measured on scholl
    /// RNDPRE_3_44's first query: under `--z3-mode` only the plain
    /// formulation decides it (~0.8 s), so a quarter of a 2.7 s query lost
    /// the game's `sat`; in the default posture only the split one does
    /// (~1.3 s), so half of a 3 s query (the plain slice overshoots to
    /// ~1.6 s) left it a 30 ms margin.
    fn qsat_kernel_decide(
        &mut self,
        roots: &[TermId],
        category: LogicCategory,
        deadline: Instant,
    ) -> Option<(Executor, Result<SolveResult>)> {
        let started = Instant::now();
        let order = if self.qsat_route.prefer_split {
            [true, false]
        } else {
            [false, true]
        };
        for (attempt, &split) in order.iter().enumerate() {
            let remaining = millis_until(deadline);
            if remaining == 0 {
                return None;
            }
            let slice = if attempt == 0 {
                (remaining / 3).clamp(1, 2_000)
            } else {
                remaining
            };
            let formulation = self.qsat_formulation(roots, split);
            let mut probe = self.qsat_probe(&formulation, slice)?;
            let solved = probe.solve_for_category(category);
            tracing::debug!(
                target: "ay::qsat",
                roots = roots.len(),
                split,
                decided = matches!(solved, Ok(SolveResult::Sat | SolveResult::Unsat(_))),
                ms = millis_since(started),
                "kernel query"
            );
            if matches!(solved, Ok(SolveResult::Sat | SolveResult::Unsat(_))) {
                if attempt > 0 {
                    self.qsat_route.prefer_split = split;
                }
                self.qsat_route.last_decided_split = Some(split);
                return Some((probe, solved));
            }
        }
        None
    }

    /// Confirm a decisive kernel UNSAT of `roots` (it ends the game) by an
    /// independent solve:
    ///
    /// 1. every arithmetic atom canonicalized (`mbp::canonical_atoms`:
    ///    constants folded, like terms and `to_real` merged) and solved on
    ///    the plain lane. A plain-lane refutation of a satisfiable level-0
    ///    query was measured under BOTH kernel formulations (`(distinct
    ///    (to_real c) (+ (to_real c) 0.5))`, whose canonical form is `true`);
    ///    the canonical solve answers `sat` there, which refutes the kernel.
    ///    An `unsat` confirms, unless the full `check-sat` pipeline, run as a
    ///    bounded refuter, finds a model;
    /// 2. only when that is undecided (the ground lane is shape-sensitive on
    ///    residue queries: measured `unknown` on an int-mod level-1 query the
    ///    plain lane refutes in 37 ms), the full pipeline on the query as
    ///    given, then the formulation that did NOT decide it; the first
    ///    decided answer stands.
    pub(super) fn qsat_kernel_confirm_unsat(
        &mut self,
        roots: &[TermId],
        targets: &[TermId],
        deadline: Instant,
    ) -> bool {
        let category = category_of(self, targets);
        let mut memo = HashMap::default();
        let canonical: Vec<TermId> = roots
            .iter()
            .map(|&r| qsat::mbp::canonical_atoms(&mut self.ctx.terms, r, &mut memo))
            .collect();
        let canonical_verdict = self.qsat_confirm_solve(&canonical, category, deadline, 2);
        let confirmed = match canonical_verdict {
            Some(false) => false,
            Some(true) => {
                self.qsat_confirm_pipeline(roots, deadline, CONFIRM_PIPELINE_MS) != Some(false)
            }
            None => match self.qsat_confirm_pipeline(roots, deadline, millis_until(deadline) / 2) {
                Some(unsat) => unsat,
                None => {
                    let split = !self.qsat_route.last_decided_split.unwrap_or(false);
                    let other = self.qsat_formulation(roots, split);
                    self.qsat_confirm_solve(&other, category, deadline, 1) == Some(true)
                }
            },
        };
        tracing::debug!(target: "ay::qsat", ?canonical_verdict, confirmed, "kernel confirmation");
        confirmed
    }

    /// The full `check-sat` pipeline on `roots` for at most `cap_ms`:
    /// `Some(true)` unsat, `Some(false)` sat, `None` undecided.
    fn qsat_confirm_pipeline(
        &mut self,
        roots: &[TermId],
        deadline: Instant,
        cap_ms: u64,
    ) -> Option<bool> {
        let budget = millis_until(deadline).min(cap_ms);
        if budget == 0 || self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            return None;
        }
        let mut probe = self.qsat_probe(roots, budget)?;
        match probe.check_sat() {
            Ok(SolveResult::Unsat(_)) => Some(true),
            Ok(SolveResult::Sat) => Some(false),
            _ => None,
        }
    }

    /// One plain-lane solve of `roots` with `1/share_den` of the time left:
    /// `Some(true)` unsat, `Some(false)` sat, `None` undecided.
    fn qsat_confirm_solve(
        &mut self,
        roots: &[TermId],
        category: LogicCategory,
        deadline: Instant,
        share_den: u64,
    ) -> Option<bool> {
        if self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            return None;
        }
        let budget = millis_until(deadline) / share_den.max(1);
        if budget == 0 {
            return None;
        }
        let mut probe = self.qsat_probe(roots, budget)?;
        match probe.solve_for_category(category) {
            Ok(SolveResult::Unsat(_)) => Some(true),
            Ok(SolveResult::Sat) => Some(false),
            _ => None,
        }
    }

    /// Decide `formulas ∧ assumptions` (see the module docs).
    pub(super) fn qsat_kernel_check(
        &mut self,
        formulas: &[TermId],
        assumptions: &[TermId],
        targets: &[TermId],
        deadline: Instant,
        want_core: bool,
    ) -> KernelAnswer {
        if self.should_abort_theory_loop() || !self.qpf_probe_preflight() {
            return KernelAnswer::Unknown;
        }
        self.qsat_route.last_decided_split = None;
        let category = category_of(self, targets);
        let mut roots = formulas.to_vec();
        roots.extend_from_slice(assumptions);
        if tracing::enabled!(target: "ay::qsat", tracing::Level::TRACE) {
            self.qsat_trace_query(&roots, targets);
        }
        let Some((probe, solved)) = self.qsat_kernel_decide(&roots, category, deadline) else {
            return KernelAnswer::Unknown;
        };
        match solved {
            Ok(SolveResult::Sat) => {
                let Some(model) = probe.last_model.as_ref() else {
                    return KernelAnswer::Unknown;
                };
                let values: Vec<Option<Val>> = targets
                    .iter()
                    .map(|&t| eval_value(probe.evaluate_term(model, t)))
                    .collect();
                drop(probe);
                if self.qsat_model_holds(&roots, targets, &values) {
                    KernelAnswer::Sat(values)
                } else {
                    KernelAnswer::Unknown
                }
            }
            Ok(SolveResult::Unsat(_)) => {
                drop(probe);
                let everything: Vec<usize> = (0..assumptions.len()).collect();
                if !want_core || assumptions.len() <= 1 {
                    return KernelAnswer::Unsat(everything);
                }
                KernelAnswer::Unsat(
                    self.qsat_kernel_core(formulas, assumptions, category, deadline)
                        .unwrap_or(everything),
                )
            }
            _ => KernelAnswer::Unknown,
        }
    }

    /// The query as a standalone SMT-LIB script, at trace level.
    fn qsat_trace_query(&self, roots: &[TermId], targets: &[TermId]) {
        let mut text = String::new();
        for &v in targets {
            let sort = match self.ctx.terms.sort(v) {
                Sort::Int => "Int",
                Sort::Real => "Real",
                _ => "Bool",
            };
            text.push_str(&format!(
                "(declare-fun {} () {sort})\n",
                self.format_term(v)
            ));
        }
        for &r in roots {
            text.push_str(&format!("(assert {})\n", self.format_term(r)));
        }
        tracing::trace!(target: "ay::qsat", "kernel query script BEGIN\n{text}(check-sat)\nkernel query script END");
    }

    /// Exact re-evaluation: every root must hold under the reported values
    /// (defaults for unreported ones).
    fn qsat_model_holds(
        &self,
        roots: &[TermId],
        targets: &[TermId],
        values: &[Option<Val>],
    ) -> bool {
        let mut m = qsat::lin::Model::default();
        for (&t, v) in targets.iter().zip(values) {
            let v = v.clone().unwrap_or_else(|| match self.ctx.terms.sort(t) {
                Sort::Bool => Val::Bool(false),
                _ => Val::Num(num_rational::BigRational::from_integer(0.into())),
            });
            m.vals.insert(t, v);
        }
        let mut ev = qsat::lin::Eval::new(&self.ctx.terms, &m);
        let holds = roots.iter().all(|&r| ev.boolean(r) == Some(true));
        if !holds {
            tracing::debug!(target: "ay::qsat", "kernel model refused by exact re-evaluation");
        }
        holds
    }

    /// Failed assumptions of an UNSAT `formulas ∧ assumptions`, as indices.
    /// `None` (the caller keeps every assumption, which is sound) once the
    /// query's deadline leaves no time.
    fn qsat_kernel_core(
        &mut self,
        formulas: &[TermId],
        assumptions: &[TermId],
        category: LogicCategory,
        deadline: Instant,
    ) -> Option<Vec<usize>> {
        let remaining = millis_until(deadline);
        if remaining == 0 {
            return None;
        }
        let mut probe = self.qsat_probe(formulas, remaining)?;
        let solved = match category {
            LogicCategory::QfLia => probe.solve_lia_with_assumptions(formulas, assumptions),
            LogicCategory::QfLira => probe.solve_lira_with_assumptions(formulas, assumptions),
            LogicCategory::QfLra => {
                probe.solve_with_assumptions_for_theory(formulas, assumptions, TheoryKind::Lra)
            }
            _ => probe.solve_with_assumptions_for_theory(
                formulas,
                assumptions,
                TheoryKind::Propositional,
            ),
        };
        if !matches!(solved, Ok(SolveResult::Unsat(_))) {
            return None;
        }
        let core = probe.last_assumption_core.clone()?;
        let mut indices = Vec::with_capacity(core.len());
        for c in core {
            let i = assumptions.iter().position(|&a| a == c)?;
            if !indices.contains(&i) {
                indices.push(i);
            }
        }
        tracing::debug!(target: "ay::qsat", core = indices.len(), of = assumptions.len(), "kernel core");
        if indices.len() < assumptions.len() {
            // A strict sub-core must re-refute on the plain lane: a lemma
            // built on a wrong core would be unsound.
            let remaining = millis_until(deadline);
            if remaining == 0 {
                return None;
            }
            let mut roots = formulas.to_vec();
            roots.extend(indices.iter().map(|&i| assumptions[i]));
            let mut check = self.qsat_probe(&roots, remaining)?;
            if !matches!(
                check.solve_for_category(category),
                Ok(SolveResult::Unsat(_))
            ) {
                return None;
            }
        }
        Some(indices)
    }
}
