// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Counterexample witnesses read directly off the transition-system BMC lane's
//! own model.
//!
//! `solve_transition_system_incremental` decides `query@k` on ONE persistent
//! executor whose assertion stack is `init@0 ∧ trans@0 ∧ … ∧ trans@k-1 ∧
//! query@k`. When that check is SAT the executor already holds a model of a
//! complete length-`k` path; the lane used to throw it away and re-solve the
//! same depth on the flat level encoding purely to obtain a model it could
//! extract a witness from. On the lustre class that confirmation re-solve
//! costs 10–18 s of CPU for a depth the TS lane decided in 1–3 s and is the
//! step that loses the front probe's budget
//! (the development design notes at `9598c4206`, §5,
//! the development design notes at `9598c4206`, T5).
//!
//! This module turns the TS model into the same `DerivationWitness` shape the
//! flat path produces — one entry per level `k..=0`, canonical predicate-state
//! values plus the fired clause's variable instances — and hands it to the
//! UNCHANGED soundness gate: `verified_unsafe_from_witness` replays the
//! witness against the ORIGINAL clauses with `PdrSolver::try_verify_counterexample`
//! and yields `Unsafe` only for a witness that replays as `Valid`. Nothing here
//! is trusted: a wrong clause attribution, a mis-named local, or a model the
//! lane's encoding satisfies but the original clauses do not all fail closed
//! to `None`, and the caller falls back to the flat confirmation exactly as
//! before.
//!
//! Attribution back to clauses uses `TransitionSystem::clause_disjuncts`, the
//! per-clause canonical constraints `from_chc_problem` folds into `init` /
//! `transition` / `query`, versioned with the SAME functions the lane's
//! scripts are built from (`version_init_expr` / `version_transition_expr` /
//! `version_query_expr`), so every local variable name looked up in the model
//! is the name the lane declared.

use super::BmcSolver;
use crate::engine_result::ChcEngineResult;
use crate::expr::evaluate::evaluate_expr;
use crate::pdr::counterexample::{Counterexample, DerivationWitness, DerivationWitnessEntry};
use crate::smt::executor_adapter::parse_model_into;
use crate::smt::SmtValue;
use crate::transition_system::{TransitionSystem, TsClauseDisjunct, TsClauseDisjuncts};
use crate::{ChcExpr, ClauseHead, HornClause};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};

/// Which of the three transition-system roles a clause plays; decides how its
/// canonical disjunct is versioned and which step's state pins its arguments.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum TsRole {
    /// Fact clause: head arguments are the step-0 state.
    Init,
    /// Self-transition: body arguments are the step-`j` state, head arguments
    /// the step-`j+1` state.
    Transition,
    /// Query clause: body arguments are the step-`k` state.
    Query,
}

impl BmcSolver {
    /// Decide `Unsafe` from the persistent TS executor's model at depth `k`,
    /// where the lane's `query@k` check just returned `sat`.
    ///
    /// Returns `Some(Unsafe)` only when a witness built from that model
    /// replays as `Valid` against the original clauses
    /// (`verified_unsafe_from_witness`); every other outcome — unsupported
    /// sorts, an unreadable model, no clause attributable to a step, a
    /// replay that is `Spurious` or `Unknown` — is `None`, and the caller
    /// proceeds to the flat confirmation re-solve unchanged.
    pub(super) fn ts_model_unsafe_at_depth(
        &self,
        exec: &mut ay_dpll::Executor,
        ts: &TransitionSystem,
        disjuncts: &TsClauseDisjuncts,
        k: usize,
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<ChcEngineResult> {
        // Real-sorted systems are admitted (LRA_BMC_unsafe_2026-09-22): the
        // witness is built over `SmtValue` (Real via `smt_value_expr_for_sort`,
        // fail-closed on i64 overflow) and replayed on the ORIGINAL clauses
        // exactly like an Int witness; nothing here is trusted.
        if self.problem.has_datatype_sorts() || self.problem.has_array_sorts() {
            return None;
        }
        if self.execution_stopped(deadline) {
            return None;
        }
        let model = self.ts_executor_model(exec, deadline)?;
        let witness = self.ts_model_derivation_witness(ts, disjuncts, &model, k)?;
        if self.execution_stopped(deadline) {
            return None;
        }
        let cex = self.ts_witness_counterexample(witness, &model, ts, disjuncts, k);
        match self.verified_unsafe_from_counterexample(cex, "transition-system model") {
            unsafe_result @ ChcEngineResult::Unsafe(_) => {
                tracing::debug!(
                    "BMC-ts: depth {k} counterexample confirmed from the lane's own model"
                );
                Some(unsafe_result)
            }
            _ => {
                tracing::debug!(
                    "BMC-ts: depth {k} model witness did not replay; falling back to flat \
                     confirmation"
                );
                None
            }
        }
    }

    /// A counterexample read off a model of `init_at(0) ∧ transition_at(0..k)
    /// ∧ query_at(k)` over `ts`, the transition system of this solver's
    /// problem — the naming the TS lane and IMC's base check share. `None` when
    /// a step cannot be attributed to a clause. Nothing is trusted: the
    /// caller's acceptance replays the witness (or its ground derivation) on
    /// the original clauses.
    pub(crate) fn counterexample_from_ts_model(
        &self,
        ts: &TransitionSystem,
        model: &FxHashMap<String, SmtValue>,
        k: usize,
    ) -> Option<Counterexample> {
        if self.problem.has_datatype_sorts() || self.problem.has_array_sorts() {
            return None;
        }
        let disjuncts = TransitionSystem::clause_disjuncts(&self.problem).ok()?;
        let witness = self.ts_model_derivation_witness(ts, &disjuncts, model, k)?;
        Some(self.ts_witness_counterexample(witness, model, ts, &disjuncts, k))
    }

    /// `(get-model)` on the persistent executor while the `query@k` frame is
    /// still pushed.
    fn ts_executor_model(
        &self,
        exec: &mut ay_dpll::Executor,
        deadline: Option<ay_core::time::Instant>,
    ) -> Option<FxHashMap<String, SmtValue>> {
        let commands = ay_frontend::parse("(get-model)\n").ok()?;
        let outputs = self.exec_commands_with_deadline(exec, &commands, deadline)?;
        let mut model = FxHashMap::default();
        parse_model_into(
            &mut model,
            Self::model_output(&outputs),
            &FxHashSet::default(),
        );
        (!model.is_empty()).then_some(model)
    }

    /// Build the linear derivation witness `init → … → state@k ⊨ query` from a
    /// model of the lane's unrolling at depth `k`.
    ///
    /// Entry `i` is the fact at level `k - i` (so `entries[0]` is the root, as
    /// in `concrete_derivation_witness`); each entry's `incoming_clause` is
    /// the ORIGINAL clause whose canonical disjunct the model satisfies at
    /// that step and its `premises` is the next entry. Fails closed (`None`)
    /// when any step has no attributable clause or the model lacks a state
    /// value the encoding constrains.
    pub(super) fn ts_model_derivation_witness(
        &self,
        ts: &TransitionSystem,
        disjuncts: &TsClauseDisjuncts,
        model: &FxHashMap<String, SmtValue>,
        k: usize,
    ) -> Option<DerivationWitness> {
        let pred = ts.predicate;
        let arity = self.problem.get_predicate(pred)?.arg_sorts.len();
        let state_vars = ts.state_vars().get(..arity)?;

        // Per-step canonical state. A state variable the lane never declared
        // at some step (it occurs in no asserted formula there) is genuinely
        // unconstrained at that step; give it the sort default so the entry
        // is complete. The replay still checks every clause step, so a wrong
        // choice can only cost this fast path, never a verdict.
        let mut states: Vec<Vec<SmtValue>> = Vec::with_capacity(k + 1);
        let mut eval_model = model.clone();
        for step in 0..=k {
            let mut values = Vec::with_capacity(arity);
            for var in state_vars {
                let name = TransitionSystem::version_var(var, step).name;
                let value = match model.get(&name) {
                    Some(value) => Self::model_smt_value_for_sort(value, &var.sort)?,
                    None => {
                        let default = Self::concrete_value_smt(&var.sort, 0)?;
                        eval_model.insert(name, default.clone());
                        default
                    }
                };
                values.push(value);
            }
            states.push(values);
        }

        // Attribute every step to an original clause.
        let fact = Self::ts_fired_disjunct(&disjuncts.facts, &eval_model, |d| {
            ts.version_init_expr(&d.constraint, 0)
        })?;
        let mut transitions = Vec::with_capacity(k);
        for step in 0..k {
            transitions.push(Self::ts_fired_disjunct(
                &disjuncts.transitions,
                &eval_model,
                |d| ts.version_transition_expr(&d.constraint, step),
            )?);
        }
        let query = Self::ts_fired_disjunct(&disjuncts.queries, &eval_model, |d| {
            ts.version_query_expr(&d.constraint, k)
        })?;

        let mut entries = Vec::with_capacity(k + 1);
        for entry_idx in 0..=k {
            let level = k - entry_idx;
            let (mut instances, state_expr) =
                self.concrete_state_witness_smt(pred, &states[level])?;
            let (incoming, role, step) = if level == 0 {
                (fact, TsRole::Init, 0)
            } else {
                (transitions[level - 1], TsRole::Transition, level - 1)
            };
            let clause = self.problem.clauses().get(incoming.clause_idx)?;
            for (name, value) in
                self.ts_clause_instances(clause, incoming, role, step, &states, &eval_model)
            {
                instances.entry(name).or_insert(value);
            }
            entries.push(DerivationWitnessEntry {
                predicate: pred,
                level,
                state: state_expr,
                incoming_clause: Some(incoming.clause_idx),
                premises: if level == 0 {
                    Vec::new()
                } else {
                    vec![entry_idx + 1]
                },
                instances,
            });
        }

        Some(DerivationWitness {
            query_clause: Some(query.clause_idx),
            root: 0,
            entries,
        })
    }

    /// The first disjunct whose versioned constraint the model evaluates to
    /// `true`. Any satisfied disjunct is a valid derivation step for the
    /// replay; an unevaluable one (a local the model does not bind) is
    /// treated as not fired.
    fn ts_fired_disjunct<'a>(
        candidates: &'a [TsClauseDisjunct],
        model: &FxHashMap<String, SmtValue>,
        version: impl Fn(&TsClauseDisjunct) -> ChcExpr,
    ) -> Option<&'a TsClauseDisjunct> {
        candidates.iter().find(|candidate| {
            matches!(
                evaluate_expr(&version(candidate), model),
                Some(SmtValue::Bool(true))
            )
        })
    }

    /// Concrete values for the variables of `clause` at the step where it
    /// fired, keyed by the clause's OWN variable names — what the replay
    /// substitutes into the clause constraint and what a ground derivation
    /// needs.
    ///
    /// Mirrors `substitute_args_to_canonical_vars` + `rename_local_vars` +
    /// per-step versioning: a variable that is a body-predicate argument takes
    /// the body step's state value (body substitution runs first there), one
    /// that is a head argument takes the head step's, and every other
    /// variable is a clause local named `{local_prefix}{name}` and versioned
    /// with the role's tag. A local the model does not bind is simply left
    /// out — the replay then treats it as existentially bound.
    fn ts_clause_instances(
        &self,
        clause: &HornClause,
        disjunct: &TsClauseDisjunct,
        role: TsRole,
        step: usize,
        states: &[Vec<SmtValue>],
        model: &FxHashMap<String, SmtValue>,
    ) -> FxHashMap<String, SmtValue> {
        let mut instances = FxHashMap::default();
        let body_step = match role {
            TsRole::Init => None,
            TsRole::Transition | TsRole::Query => Some(step),
        };
        let head_step = match role {
            TsRole::Init => Some(0),
            TsRole::Transition => Some(step + 1),
            TsRole::Query => None,
        };

        let arg_value = |args: &[ChcExpr], name: &str, at: usize| -> Option<SmtValue> {
            args.iter().enumerate().find_map(|(pos, arg)| match arg {
                ChcExpr::Var(v) if v.name == name => states.get(at)?.get(pos).cloned(),
                _ => None,
            })
        };

        for var in clause.vars() {
            let from_body = body_step.and_then(|at| {
                clause
                    .body
                    .predicates
                    .first()
                    .and_then(|(_, args)| arg_value(args, &var.name, at))
            });
            let from_head = head_step.and_then(|at| match &clause.head {
                ClauseHead::Predicate(_, args) => arg_value(args, &var.name, at),
                ClauseHead::False => None,
            });
            let value = from_body.or(from_head).or_else(|| {
                let local = format!("{}{}", disjunct.local_prefix, var.name);
                let versioned = match role {
                    TsRole::Init => format!("{local}__i{step}"),
                    TsRole::Transition => format!("{local}__t{step}"),
                    TsRole::Query => format!("{local}__q{step}"),
                };
                model.get(&versioned).cloned()
            });
            let Some(value) = value.and_then(|v| Self::model_smt_value_for_sort(&v, &var.sort))
            else {
                continue;
            };
            instances.insert(var.name.clone(), value);
        }
        instances
    }

    /// Wrap the witness as a counterexample, attaching a fully-ground
    /// derivation when every clause variable on the path is pinned and the
    /// derivation validates by pure evaluation on this problem. The attached
    /// derivation lets `try_verify_counterexample` decide `Valid` without an
    /// SMT replay; it is re-validated there, so attaching it transfers no
    /// trust.
    fn ts_witness_counterexample(
        &self,
        witness: DerivationWitness,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
        disjuncts: &TsClauseDisjuncts,
        k: usize,
    ) -> Counterexample {
        let steps = self.steps_from_derivation_witness(&witness);
        let ground = crate::ground_derivation::ground_backtranslation_enabled()
            .then(|| self.ts_ground_derivation(&witness, model, ts, disjuncts, k))
            .flatten();
        let cex = Counterexample::with_witness(steps, witness);
        match ground {
            Some(derivation) => cex.with_ground_derivation(derivation),
            None => cex,
        }
    }

    fn ts_ground_derivation(
        &self,
        witness: &DerivationWitness,
        model: &FxHashMap<String, SmtValue>,
        ts: &TransitionSystem,
        disjuncts: &TsClauseDisjuncts,
        k: usize,
    ) -> Option<crate::ground_derivation::GroundDerivation> {
        let query_idx = witness.query_clause?;
        let query = disjuncts
            .queries
            .iter()
            .find(|d| d.clause_idx == query_idx)?;
        let arity = self.problem.get_predicate(ts.predicate)?.arg_sorts.len();
        let root_state: Vec<SmtValue> = witness
            .entries
            .get(witness.root)?
            .instances
            .iter()
            .filter_map(|(name, value)| {
                let idx: usize = name
                    .strip_prefix(&format!("__p{}_a", ts.predicate.index()))?
                    .parse()
                    .ok()?;
                (idx < arity).then_some((idx, value.clone()))
            })
            .fold(vec![None; arity], |mut acc, (idx, value)| {
                acc[idx] = Some(value);
                acc
            })
            .into_iter()
            .collect::<Option<Vec<_>>>()?;
        let level_witness = super::LevelDerivationWitness {
            witness: witness.clone(),
            query_roots: vec![witness.root],
        };
        let derivation = self.ground_derivation_from_witness_with(&level_witness, |clause| {
            let states = [root_state];
            let env = self.ts_clause_instances(clause, query, TsRole::Query, 0, &states, model);
            // Every query variable must be pinned for a ground step.
            clause
                .vars()
                .iter()
                .all(|var| env.contains_key(&var.name))
                .then_some(env)
        })?;
        crate::ground_derivation::validate_ground_derivation(&self.problem, &derivation)
            .inspect_err(|err| {
                crate::ground_derivation::log_ground_translation_detail(format_args!(
                    "transition-system model derivation at depth {k} rejected on its own \
                     problem: {err}"
                ));
            })
            .ok()?;
        Some(derivation)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::bmc::BmcConfig;
    use crate::{ChcProblem, ChcSort, ChcVar, ClauseBody};

    /// `P(0)`, `P(x) ∧ y = x + 1 ⇒ P(y)`, `P(x) ∧ x ≥ 3 ⇒ false`: the shortest
    /// counterexample has three transitions (0 → 1 → 2 → 3).
    fn counter_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Int]);
        let x = ChcVar::new("x", ChcSort::Int);
        let y = ChcVar::new("y", ChcSort::Int);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(p, vec![ChcExpr::int(0)]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::eq(
                    ChcExpr::var(y.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::int(1)),
                )),
            ),
            ClauseHead::Predicate(p, vec![ChcExpr::var(y)]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::int(3))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    /// The model the TS lane's executor would hold for `query@3`: canonical
    /// state `v0` at steps 0..=3 (the transition's locals were substituted
    /// away, so there are none to bind).
    fn ts_model(values: &[i128]) -> FxHashMap<String, SmtValue> {
        let v0 = ChcVar::new("v0", ChcSort::Int);
        values
            .iter()
            .enumerate()
            .map(|(step, value)| {
                (
                    TransitionSystem::version_var(&v0, step).name,
                    SmtValue::Int(*value),
                )
            })
            .collect()
    }

    fn fixture() -> (BmcSolver, TransitionSystem, TsClauseDisjuncts) {
        let problem = counter_problem();
        let ts = TransitionSystem::from_chc_problem(&problem).expect("single-pred TS");
        let disjuncts = TransitionSystem::clause_disjuncts(&problem).expect("disjuncts");
        (BmcSolver::new(problem, BmcConfig::default()), ts, disjuncts)
    }

    #[test]
    fn ts_model_witness_replays_as_unsafe_on_the_original_clauses() {
        let (solver, ts, disjuncts) = fixture();
        let model = ts_model(&[0, 1, 2, 3]);
        let witness = solver
            .ts_model_derivation_witness(&ts, &disjuncts, &model, 3)
            .expect("a model of the unrolling yields a witness");
        assert_eq!(witness.entries.len(), 4);
        assert_eq!(witness.query_clause, Some(2));
        assert_eq!(witness.entries[0].level, 3);
        assert_eq!(witness.entries[0].incoming_clause, Some(1));
        assert_eq!(witness.entries[0].premises, vec![1]);
        assert_eq!(witness.entries[3].level, 0);
        assert_eq!(witness.entries[3].incoming_clause, Some(0));
        assert_eq!(witness.entries[3].premises, [] as [usize; 0]);
        // The transition clause's own variables are pinned from the states.
        assert_eq!(
            witness.entries[0].instances.get("x"),
            Some(&SmtValue::Int(2))
        );
        assert_eq!(
            witness.entries[0].instances.get("y"),
            Some(&SmtValue::Int(3))
        );

        let cex = solver.ts_witness_counterexample(witness, &model, &ts, &disjuncts, 3);
        assert!(
            cex.ground_derivation.is_some(),
            "fully pinned path must carry a ground derivation"
        );
        assert!(matches!(
            solver.verified_unsafe_from_counterexample(cex, "test"),
            ChcEngineResult::Unsafe(_)
        ));
    }

    #[test]
    fn ts_model_that_breaks_a_transition_yields_no_witness() {
        let (solver, ts, disjuncts) = fixture();
        // 1 → 5 is not a step of `y = x + 1`: no transition disjunct fires.
        let model = ts_model(&[0, 1, 5, 6]);
        assert!(solver
            .ts_model_derivation_witness(&ts, &disjuncts, &model, 3)
            .is_none());
    }

    #[test]
    fn tampered_ts_witness_is_rejected_by_replay() {
        let (solver, ts, disjuncts) = fixture();
        let model = ts_model(&[0, 1, 2, 3]);
        let mut witness = solver
            .ts_model_derivation_witness(&ts, &disjuncts, &model, 3)
            .expect("witness");
        // Forge the level-2 fact as P(7): its incoming step 1 → 7 is not a
        // transition, so the replay must refuse the whole derivation even
        // though the root still satisfies the query.
        let seven = solver
            .concrete_state_witness_smt(ts.predicate, &[SmtValue::Int(7)])
            .expect("state");
        witness.entries[1].state = seven.1;
        for (name, value) in seven.0 {
            witness.entries[1].instances.insert(name, value);
        }
        witness.entries[1]
            .instances
            .insert("y".to_string(), SmtValue::Int(7));
        witness.entries[0]
            .instances
            .insert("x".to_string(), SmtValue::Int(7));
        let cex = solver.ts_witness_counterexample(witness, &model, &ts, &disjuncts, 3);
        assert!(
            cex.ground_derivation.is_none(),
            "a tampered path must not validate as a ground derivation"
        );
        assert!(!matches!(
            solver.verified_unsafe_from_counterexample(cex, "test"),
            ChcEngineResult::Unsafe(_)
        ));
    }

    /// Real-sorted counter (`LRA_BMC_unsafe_2026-09-22`): `P(0)`,
    /// `P(x) ∧ y = x + 1/2 ⇒ P(y)`, `P(x) ∧ x ≥ 3/2 ⇒ false`. The TS lane must
    /// publish an Unsafe whose witness replays on the original clauses (Real
    /// witnesses used to be refused on every BMC path).
    fn real_counter_problem() -> ChcProblem {
        let mut problem = ChcProblem::new();
        let p = problem.declare_predicate("P", vec![ChcSort::Real]);
        let x = ChcVar::new("x", ChcSort::Real);
        let y = ChcVar::new("y", ChcSort::Real);
        problem.add_clause(HornClause::new(
            ClauseBody::constraint(ChcExpr::Bool(true)),
            ClauseHead::Predicate(p, vec![ChcExpr::Real(0, 1)]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::eq(
                    ChcExpr::var(y.clone()),
                    ChcExpr::add(ChcExpr::var(x.clone()), ChcExpr::Real(1, 2)),
                )),
            ),
            ClauseHead::Predicate(p, vec![ChcExpr::var(y)]),
        ));
        problem.add_clause(HornClause::new(
            ClauseBody::new(
                vec![(p, vec![ChcExpr::var(x.clone())])],
                Some(ChcExpr::ge(ChcExpr::var(x), ChcExpr::Real(3, 2))),
            ),
            ClauseHead::False,
        ));
        problem
    }

    #[test]
    fn real_ts_lane_publishes_a_replayed_unsafe() {
        let problem = real_counter_problem();
        let solver = BmcSolver::new(
            problem.clone(),
            BmcConfig {
                max_depth: 6,
                time_budget: Some(std::time::Duration::from_secs(20)),
                per_depth_timeout: Some(std::time::Duration::from_secs(20)),
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                ..BmcConfig::default()
            },
        );
        let ChcEngineResult::Unsafe(cex) = solver.solve() else {
            panic!("the Real counter reaches 3/2 after three steps");
        };
        let witness = cex.witness.as_ref().expect("witness attached");
        assert_eq!(witness.entries.len(), 4, "shortest path has 3 transitions");
    }

    #[test]
    fn real_model_values_become_exact_fraction_literals_or_fail_closed() {
        use num_bigint::BigInt;
        use num_rational::BigRational;
        let half = SmtValue::Real(BigRational::new(BigInt::from(-1), BigInt::from(2)));
        assert_eq!(
            BmcSolver::smt_value_expr_for_sort(&half, &ChcSort::Real),
            Some(ChcExpr::Real(-1, 2))
        );
        let huge = SmtValue::Real(BigRational::from_integer(BigInt::from(1u128 << 100)));
        assert_eq!(
            BmcSolver::smt_value_expr_for_sort(&huge, &ChcSort::Real),
            None
        );
    }

    #[test]
    fn ts_lane_decides_unsafe_from_its_own_model_end_to_end() {
        let problem = counter_problem();
        let solver = BmcSolver::new(
            problem.clone(),
            BmcConfig {
                max_depth: 6,
                time_budget: Some(std::time::Duration::from_secs(20)),
                // As the front BMC probe configures the lane; a per-depth
                // timeout also keeps the concrete-scalar prepass (which
                // would decide this toy problem first) out of the way.
                per_depth_timeout: Some(std::time::Duration::from_secs(20)),
                enable_k_induction: false,
                enable_adaptive_stepping: false,
                ..BmcConfig::default()
            },
        );
        let ChcEngineResult::Unsafe(cex) = solver.solve() else {
            panic!("the counter reaches 3");
        };
        let witness = cex.witness.as_ref().expect("witness attached");
        assert_eq!(witness.entries.len(), 4, "shortest path has 3 transitions");
        let derivation = cex
            .ground_derivation
            .as_ref()
            .expect("TS-model path pins every variable, so it carries a ground derivation");
        crate::ground_derivation::validate_ground_derivation(&problem, derivation)
            .expect("attached derivation validates on the original clauses");
    }
}
