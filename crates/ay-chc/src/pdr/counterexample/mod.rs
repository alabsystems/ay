// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Counterexample types for PDR solver.

use crate::clause::ActionId;
use crate::smt::SmtValue;
use crate::transition_system::TransitionSystem;
use crate::{ChcError, ChcExpr, ChcProblem, ChcResult, ChcSort, ChcVar, PredicateId};
use ay_core::kani_compat::DetHashMap as FxHashMap;
use std::collections::BTreeMap;

use super::model::{ChcReplayObligation, ChcReplayObligationKind, InvariantModel};

/// Counterexample trace
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct Counterexample {
    /// Steps in the counterexample (initial state -> ... -> bad state)
    pub steps: Vec<CounterexampleStep>,
    /// Optional derivation witness (Golem/Spacer-style)
    pub witness: Option<DerivationWitness>,
    /// Optional fully-ground derivation of `false`.
    ///
    /// When present this is a CANDIDATE proof, never a trusted one: it names
    /// clause indices of *some* problem, and it establishes UNSAFE only for a
    /// problem it validates against. Every consumer re-runs
    /// [`crate::ground_derivation::validate_ground_derivation`] against its own
    /// clause list before believing it, so carrying a stale or transform-space
    /// derivation here can only produce a rejection.
    pub(crate) ground_derivation: Option<crate::ground_derivation::GroundDerivation>,
}

impl Counterexample {
    /// Create a counterexample with steps and no witness.
    pub fn new(steps: Vec<CounterexampleStep>) -> Self {
        Self {
            steps,
            witness: None,
            ground_derivation: None,
        }
    }

    /// Create a counterexample with steps and a derivation witness.
    pub fn with_witness(steps: Vec<CounterexampleStep>, witness: DerivationWitness) -> Self {
        Self {
            steps,
            witness: Some(witness),
            ground_derivation: None,
        }
    }

    /// Whether this counterexample carries a candidate fully-ground
    /// derivation of `false` (see [`Counterexample::ground_derivation`]).
    ///
    /// Read-only observability for consumers/tests that want to distinguish
    /// the ground-witness back-translation landing from search-derived
    /// counterexamples. Presence confers no trust — every consumer
    /// re-validates the derivation against its own clause list.
    pub fn has_ground_derivation(&self) -> bool {
        self.ground_derivation.is_some()
    }

    /// Attach a candidate fully-ground derivation.
    ///
    /// The derivation is evidence only for a problem it validates against; see
    /// [`Counterexample::ground_derivation`].
    pub(crate) fn with_ground_derivation(
        mut self,
        derivation: crate::ground_derivation::GroundDerivation,
    ) -> Self {
        self.ground_derivation = Some(derivation);
        self
    }

    /// Format the counterexample as a machine-readable certificate.
    ///
    /// The certificate includes:
    /// 1. A header identifying the result as UNSAFE
    /// 2. The counterexample trace as concrete variable assignments at each step
    /// 3. If a derivation witness is present, the derivation DAG with state formulas
    pub fn to_certificate(&self, problem: &crate::ChcProblem) -> String {
        use std::fmt::Write;

        let mut out = String::new();
        let _ = writeln!(out, ";; AY CHC Certificate: UNSAFE");
        let _ = writeln!(out, ";; Format: ay-chc-cert v1");
        let _ = writeln!(out, ";;");
        let _ = writeln!(
            out,
            ";; Counterexample trace ({} step{}):",
            self.steps.len(),
            if self.steps.len() == 1 { "" } else { "s" }
        );

        for (i, step) in self.steps.iter().enumerate() {
            let pred_name = problem
                .get_predicate(step.predicate)
                .map_or("?", |p| p.name.as_str());
            // Include TLA+ action name in step header when available (#8215)
            if let Some(action_id) = step.action_id {
                let action_name = problem.action_name(action_id).unwrap_or("?");
                let _ = writeln!(out, ";; Step {i}: {pred_name} (action: {action_name})");
            } else {
                let _ = writeln!(out, ";; Step {i}: {pred_name}");
            }

            if step.assignments.is_empty() {
                let _ = writeln!(out, ";;   (no concrete assignments)");
            } else {
                // Sort assignments by name for deterministic output
                let mut assigns: Vec<_> = step.assignments.iter().collect();
                assigns.sort_by_key(|(k, _)| k.as_str());
                for (var, val) in assigns {
                    let _ = writeln!(out, ";;   {var} = {val}");
                }
            }
        }

        // If we have a derivation witness with concrete instances, emit those too
        if let Some(witness) = &self.witness {
            if witness.entries.iter().any(|e| !e.instances.is_empty()) {
                let _ = writeln!(out, ";;");
                let _ = writeln!(out, ";; Derivation witness:");
                for (i, entry) in witness.entries.iter().enumerate() {
                    let pred_name = problem
                        .get_predicate(entry.predicate)
                        .map_or("?", |p| p.name.as_str());
                    let _ = writeln!(out, ";; [{i}] {pred_name} (level {})", entry.level);
                    if !entry.instances.is_empty() {
                        let mut insts: Vec<_> = entry.instances.iter().collect();
                        insts.sort_by_key(|(k, _)| k.as_str());
                        for (var, val) in insts {
                            let _ = writeln!(out, ";;   {var} = {val:?}");
                        }
                    }
                    // Emit state formula as SMT-LIB
                    let state_str = InvariantModel::expr_to_smtlib(&entry.state);
                    let _ = writeln!(out, ";;   state: {state_str}");
                }
            }
        }

        out
    }

    /// Generate a replayable trace-validity obligation for an unsafe certificate.
    ///
    /// This currently covers concrete single-predicate transition-system traces.
    /// The emitted SMT-LIB query is expected to be SAT: it conjoins the original
    /// init/transition/query unrolling with the concrete assignments printed in
    /// the unsafe certificate. Unsupported trace shapes return an error so callers
    /// can keep the evidence path fail-closed.
    pub fn trace_validity_replay_obligations(
        &self,
        problem: &ChcProblem,
    ) -> ChcResult<Vec<ChcReplayObligation>> {
        let TraceValidity {
            depth,
            formula: obligation_formula,
            env: _,
        } = self.build_trace_validity(problem)?;
        let name = format!("trace-validity-depth-{depth}");
        let smtlib = render_trace_validity_replay_obligation(problem, &name, &obligation_formula);
        Ok(vec![ChcReplayObligation {
            name,
            kind: ChcReplayObligationKind::TraceValidity,
            clause_index: problem_query_clause_index(problem).unwrap_or(0),
            smtlib,
        }])
    }

    /// STEP D (`--strict-proofs` UNSAFE gate): self-contained native ground
    /// check that the counterexample genuinely witnesses reachability of the
    /// bad state (i.e. `false` is derivable from the problem's clauses).
    ///
    /// An UNSAFE certificate is a **SAT witness** — the counterexample pins
    /// concrete reachable state values — so there is no UNSAT proof to re-check
    /// with carcara/Alethe (carcara is N/A for a sat witness). The sound,
    /// self-contained check is DETERMINISTIC GROUND EVALUATION against the
    /// problem's own clauses, in two forms, strongest first:
    ///
    /// 1. **Ground-derivation validation.** When the counterexample carries a
    ///    fully-concrete [`GroundDerivation`](crate::ground_derivation) of
    ///    `false`, re-validate it against `problem` with
    ///    [`validate_ground_derivation`](crate::ground_derivation::validate_ground_derivation):
    ///    every clause constraint must evaluate to `true` and every
    ///    body-predicate argument tuple must be value-identical to its premise's
    ///    head, all under totally concrete assignments, with a well-founded
    ///    premise graph rooted at a query clause. This is a complete DECISION
    ///    (multi-predicate, no transition-system restriction) and no trust is
    ///    transferred by the derivation merely being attached — a stale or
    ///    transform-space derivation simply fails to validate and we fall
    ///    through.
    /// 2. **Transition-trace ground evaluation.** Otherwise fall back to the
    ///    single-predicate transition-system path: bind every state variable at
    ///    every step to its concrete trace value and evaluate
    ///    `init(0) ∧ k_transition(depth) ∧ query(depth)` (the very formula the
    ///    exported obligation renders) via [`Self::trace_validity_ground_evaluates`].
    ///
    /// Returns:
    /// - `Ok(true)`  — the counterexample concretely witnesses reachability of
    ///   the bad state; the UNSAFE verdict is independently confirmed with no
    ///   external solver.
    /// - `Ok(false)` — the transition-trace obligation ground-evaluates to a
    ///   concrete `false` (a corrupted or spurious trace). The caller must NOT
    ///   ship `unsat`.
    /// - `Err(_)`    — the counterexample could not be ground-checked (no
    ///   validating derivation AND the transition trace could not be fully
    ///   ground-evaluated: an unpinned auxiliary variable, an unsupported state
    ///   sort, or a multi-predicate system with no attached derivation). The
    ///   caller fail-closes to `unknown`, the sound direction (BLOCKED-L-style
    ///   completeness hit).
    ///
    /// This mirrors the SAFE-side `--strict-proofs` checked-replay gate: no
    /// external checker (z3/golem/carcara) is ever consulted.
    pub fn ground_checks_unsafe(&self, problem: &ChcProblem) -> ChcResult<bool> {
        // Strongest form: a carried ground derivation, RE-VALIDATED here against
        // `problem` (never trusted for being attached). A validating derivation
        // is a complete, decided proof that `false` is derivable — strictly
        // stronger than the transition-trace path and not restricted to
        // single-predicate systems (this is what confirms multi-predicate
        // counterexamples like the barthe family).
        if let Some(derivation) = &self.ground_derivation {
            if crate::ground_derivation::validate_ground_derivation(problem, derivation).is_ok() {
                return Ok(true);
            }
            // Attached derivation did not validate against this problem
            // (stale / transform-space); fall through to the trace path rather
            // than reject outright — the trace evaluation is independently sound.
        }
        self.trace_validity_ground_evaluates(problem)
    }

    /// Transition-system trace ground evaluation (fallback form of
    /// [`Self::ground_checks_unsafe`]). Public for the CLI `--strict-proofs`
    /// gate and for the ground-check test battery. See `ground_checks_unsafe`
    /// for the soundness contract; this covers the single-predicate case where
    /// no ground derivation is attached.
    pub fn trace_validity_ground_evaluates(&self, problem: &ChcProblem) -> ChcResult<bool> {
        let TraceValidity { formula, env, .. } = self.build_trace_validity(problem)?;
        // `eval_ground_pub` returns the value ONLY when it is a single concrete
        // value (rejecting `Opaque` placeholders), so a `Some(Bool(_))` here is
        // a genuinely decided Boolean — never a fabricated one.
        match crate::ground_derivation::eval_ground_pub(&formula, &env) {
            Some(SmtValue::Bool(true)) => Ok(true),
            Some(SmtValue::Bool(false)) => Ok(false),
            Some(other) => Err(ChcError::Verification(format!(
                "cannot ground-check unsafe trace: obligation evaluated to a \
                 non-Boolean value {other:?}"
            ))),
            None => Err(ChcError::Verification(
                "cannot ground-check unsafe trace: obligation could not be fully \
                 ground-evaluated (unpinned auxiliary variable or unsupported state sort)"
                    .to_string(),
            )),
        }
    }

    /// Build the trace-validity obligation formula together with the concrete
    /// environment the trace pins.
    ///
    /// Shared by [`Self::trace_validity_replay_obligations`] (which renders the
    /// formula to SMT-LIB for the exported obligation) and
    /// [`Self::trace_validity_ground_evaluates`] (which ground-evaluates it
    /// against `env`). Keeping a single source of truth guarantees the exported
    /// obligation and the native ground check see the exact same formula and
    /// the exact same pinned values.
    fn build_trace_validity(&self, problem: &ChcProblem) -> ChcResult<TraceValidity> {
        let ts = TransitionSystem::from_chc_problem(problem).map_err(|reason| {
            ChcError::Verification(format!(
                "cannot export unsafe trace-validity replay obligation: {reason}"
            ))
        })?;
        if self.steps.is_empty() {
            return Err(ChcError::Verification(
                "cannot export unsafe trace-validity replay obligation: trace is empty".to_string(),
            ));
        }

        let depth = self.steps.len() - 1;
        let mut conjuncts = Vec::with_capacity(3 + self.steps.len() * ts.state_vars().len());
        conjuncts.push(ts.init_at(0));
        conjuncts.push(ts.k_transition(depth));
        conjuncts.push(ts.query_at(depth));

        let mut env: FxHashMap<String, SmtValue> = FxHashMap::default();

        for (time, step) in self.steps.iter().enumerate() {
            if step.predicate != ts.predicate {
                return Err(ChcError::Verification(format!(
                    "cannot export unsafe trace-validity replay obligation: \
                     step {time} predicate {} does not match transition-system predicate {}",
                    step.predicate, ts.predicate
                )));
            }
            for (arg_index, var) in ts.state_vars().iter().enumerate() {
                let candidates =
                    trace_assignment_candidates(problem, ts.predicate, arg_index, var, time);
                let Some((matched_name, raw_value)) = trace_assignment_value(step, &candidates)
                else {
                    return Err(ChcError::Verification(format!(
                        "cannot export unsafe trace-validity replay obligation: \
                         missing concrete trace assignment for step {time}, state arg {arg_index}; \
                         tried {candidates:?}"
                    )));
                };
                // SOUNDNESS: at a non-initial step, an unversioned model name (e.g.
                // `x`, `v0`, `__p0_a0`) carries the *source* value of the transition
                // that produced this step, not the time-`time` (successor) value.
                // Conjoining such a stale value would contradict the symbolic
                // `transition` constraint and make a genuinely realizable trace
                // obligation spuriously UNSAT (a false-UNSAFE rejection of a real
                // counterexample). The symbolic init/transition/query unrolling
                // already pins the successor value, so skip the concrete binding
                // when only a stale (non-time-`time`) name is available.
                if time > 0 && !is_time_versioned_name(matched_name, time) {
                    continue;
                }
                let versioned = TransitionSystem::version_var(var, time);
                let value = trace_value_expr(&var.sort, raw_value)?;
                // The SmtValue binding for the same versioned name — the
                // ground-evaluation env sees exactly what the pin conjunct
                // asserts, so a trace that satisfies the obligation binds a
                // consistent value and a corrupted one does not.
                let value_smt = trace_value_smt(&var.sort, raw_value)?;
                env.insert(versioned.name.clone(), value_smt);
                conjuncts.push(ChcExpr::eq(ChcExpr::var(versioned), value));
            }
        }

        Ok(TraceValidity {
            depth,
            formula: ChcExpr::and_all(conjuncts),
            env,
        })
    }
}

/// The trace-validity obligation formula plus the concrete environment the
/// trace pins. See [`Counterexample::build_trace_validity`].
struct TraceValidity {
    depth: usize,
    formula: ChcExpr,
    env: FxHashMap<String, SmtValue>,
}

fn trace_assignment_candidates(
    problem: &ChcProblem,
    predicate: PredicateId,
    arg_index: usize,
    state_var: &ChcVar,
    time: usize,
) -> Vec<String> {
    let mut candidates = Vec::new();
    push_time_candidate(
        &mut candidates,
        &TransitionSystem::version_var(state_var, time).name,
    );
    push_time_candidate(&mut candidates, &state_var.name);
    push_time_candidate(
        &mut candidates,
        &crate::lemma_hints::canonical_var_name(predicate, arg_index),
    );

    for clause in problem.clauses() {
        if let crate::ClauseHead::Predicate(head_predicate, head_args) = &clause.head {
            if *head_predicate == predicate {
                if let Some(ChcExpr::Var(var)) = head_args.get(arg_index) {
                    push_time_candidate(&mut candidates, &var.name);
                }
            }
        }
        for (body_predicate, body_args) in &clause.body.predicates {
            if *body_predicate == predicate {
                if let Some(ChcExpr::Var(var)) = body_args.get(arg_index) {
                    push_time_candidate(&mut candidates, &var.name);
                }
            }
        }
    }

    if time > 0 {
        let mut time_candidates = Vec::with_capacity(candidates.len() * 2);
        for candidate in candidates {
            push_candidate(&mut time_candidates, &format!("{candidate}_{time}"));
            push_candidate(&mut time_candidates, candidate);
        }
        time_candidates
    } else {
        candidates
    }
}

fn push_time_candidate(candidates: &mut Vec<String>, candidate: impl AsRef<str>) {
    push_candidate(candidates, candidate.as_ref());
}

fn push_candidate(candidates: &mut Vec<String>, candidate: impl Into<String>) {
    let candidate = candidate.into();
    if !candidates.iter().any(|existing| existing == &candidate) {
        candidates.push(candidate);
    }
}

fn trace_assignment_value<'a>(
    step: &CounterexampleStep,
    candidates: &'a [String],
) -> Option<(&'a str, i64)> {
    candidates.iter().find_map(|candidate| {
        step.assignments
            .get(candidate)
            .map(|v| (candidate.as_str(), *v))
    })
}

/// Whether `name` is the time-`time` versioned form of a state variable.
///
/// `trace_assignment_candidates` produces, for `time > 0`, an interleaving of
/// time-versioned names (`base_{time}`) and their unversioned fallbacks
/// (`base`). Only the `_{time}` suffixed names denote the value of the state at
/// step `time`; the bare names denote the source value of the transition that
/// produced the step and must not be conjoined into the time-`time` assignment.
fn is_time_versioned_name(name: &str, time: usize) -> bool {
    name.rsplit_once('_')
        .is_some_and(|(_, suffix)| suffix == time.to_string())
}

fn trace_value_expr(sort: &ChcSort, raw: i64) -> ChcResult<ChcExpr> {
    match sort {
        ChcSort::Bool => match raw {
            0 => Ok(ChcExpr::Bool(false)),
            1 => Ok(ChcExpr::Bool(true)),
            _ => Err(ChcError::Verification(format!(
                "cannot encode Bool trace assignment value {raw}; expected 0 or 1"
            ))),
        },
        ChcSort::Int => Ok(ChcExpr::Int(i128::from(raw))),
        ChcSort::Real => Ok(ChcExpr::Real(raw, 1)),
        ChcSort::BitVec(width) => {
            let value = u128::try_from(raw).map_err(|_| {
                ChcError::Verification(format!(
                    "cannot encode negative BitVec trace assignment value {raw}"
                ))
            })?;
            if *width < 128 && value >= (1u128 << width) {
                return Err(ChcError::Verification(format!(
                    "cannot encode BitVec({width}) trace assignment value {raw}: out of range"
                )));
            }
            Ok(ChcExpr::BitVec(value, *width))
        }
        ChcSort::Array(_, _) | ChcSort::Uninterpreted(_) | ChcSort::Datatype { .. } => {
            Err(ChcError::Verification(format!(
                "cannot encode trace assignment for unsupported state sort {sort}"
            )))
        }
    }
}

/// Concrete [`SmtValue`] for a trace assignment `raw` at a state variable of
/// the given `sort`, mirroring [`trace_value_expr`] exactly.
///
/// Kept lockstep with `trace_value_expr` (same accept/reject envelope) so the
/// ground-evaluation env binds precisely the value the pin conjunct asserts.
/// Any sort/range `trace_value_expr` rejects is rejected here too, so the
/// exported obligation and the native ground check never diverge.
fn trace_value_smt(sort: &ChcSort, raw: i64) -> ChcResult<SmtValue> {
    match sort {
        ChcSort::Bool => match raw {
            0 => Ok(SmtValue::Bool(false)),
            1 => Ok(SmtValue::Bool(true)),
            _ => Err(ChcError::Verification(format!(
                "cannot encode Bool trace assignment value {raw}; expected 0 or 1"
            ))),
        },
        ChcSort::Int => Ok(SmtValue::Int(i128::from(raw))),
        ChcSort::Real => Ok(SmtValue::Real(num_rational::BigRational::new(
            raw.into(),
            1.into(),
        ))),
        ChcSort::BitVec(width) => {
            let value = u128::try_from(raw).map_err(|_| {
                ChcError::Verification(format!(
                    "cannot encode negative BitVec trace assignment value {raw}"
                ))
            })?;
            if *width < 128 && value >= (1u128 << width) {
                return Err(ChcError::Verification(format!(
                    "cannot encode BitVec({width}) trace assignment value {raw}: out of range"
                )));
            }
            Ok(SmtValue::BitVec(value, *width))
        }
        ChcSort::Array(_, _) | ChcSort::Uninterpreted(_) | ChcSort::Datatype { .. } => {
            Err(ChcError::Verification(format!(
                "cannot encode trace assignment for unsupported state sort {sort}"
            )))
        }
    }
}

fn render_trace_validity_replay_obligation(
    problem: &ChcProblem,
    name: &str,
    formula: &ChcExpr,
) -> String {
    use std::fmt::Write;

    let mut vars = BTreeMap::new();
    for var in formula.vars() {
        vars.insert(var.name.clone(), var.sort);
    }

    let mut out = String::new();
    let _ = writeln!(out, "; AY CHC certificate replay obligation: {name}");
    let _ = writeln!(out, "; kind: trace-validity");
    let _ = writeln!(out, "; expected-result: sat");
    let _ = writeln!(
        out,
        "; normalized-input-sha256: {}",
        crate::proof_metadata::normalized_chc_input_sha256(problem)
    );
    let _ = writeln!(out, "(set-logic ALL)");
    out.push('\n');
    for (name, sort) in vars {
        let _ = writeln!(
            out,
            "(declare-const {} {})",
            ay_core::quote_symbol(&name),
            sort
        );
    }
    let _ = writeln!(out, "(assert {})", InvariantModel::expr_to_smtlib(formula));
    let _ = writeln!(out, "(check-sat)");
    let _ = writeln!(out, "(exit)");
    out
}

fn problem_query_clause_index(problem: &ChcProblem) -> Option<usize> {
    problem
        .clauses()
        .iter()
        .position(|clause| matches!(clause.head, crate::ClauseHead::False))
}

/// A step in a counterexample
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct CounterexampleStep {
    /// Predicate at this step
    pub predicate: PredicateId,
    /// Variable assignments at this step
    pub assignments: FxHashMap<String, i64>,
    /// Optional TLA+ action that produced this transition step (#8215).
    ///
    /// When set, identifies which action's transition clause was used to derive
    /// this counterexample step. Enables TLA2's CDEMC to report action-annotated
    /// counterexample traces (e.g., "Step 3: Send action violates invariant").
    pub action_id: Option<ActionId>,
    /// Index of the clause used to derive this step, if known (#8215).
    pub clause_index: Option<usize>,
}

impl CounterexampleStep {
    /// Create a counterexample step.
    pub fn new(predicate: PredicateId, assignments: FxHashMap<String, i64>) -> Self {
        Self {
            predicate,
            assignments,
            action_id: None,
            clause_index: None,
        }
    }

    /// Tag this step with the TLA+ action that produced it.
    pub fn with_action(mut self, action_id: ActionId) -> Self {
        self.action_id = Some(action_id);
        self
    }

    /// Tag this step with the clause index that derived it.
    pub fn with_clause(mut self, clause_index: usize) -> Self {
        self.clause_index = Some(clause_index);
        self
    }
}

/// A proof witness for UNSAFE results.
///
/// This mirrors Golem/Spacer's derivation database concept: derived facts are recorded
/// together with the clause ("edge") used to derive them and their premise facts.
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct DerivationWitness {
    /// Clause index (in `ChcProblem::clauses()`) for the violated query, if known.
    pub query_clause: Option<usize>,
    /// Index of the root derived fact in `entries` (typically the "bad" state).
    pub root: usize,
    /// Derived facts in a compact DAG form.
    pub entries: Vec<DerivationWitnessEntry>,
}

/// One derived fact in a witness derivation DAG.
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct DerivationWitnessEntry {
    /// Predicate this fact is about.
    pub predicate: PredicateId,
    /// Level (number of transition steps from init) for this fact.
    pub level: usize,
    /// State formula (over canonical predicate variables).
    pub state: ChcExpr,
    /// Clause index (in `ChcProblem::clauses()`) used to derive this fact.
    /// None indicates an axiom/root (e.g., direct query state without a generating clause).
    pub incoming_clause: Option<usize>,
    /// Premise fact indices in `DerivationWitness.entries`.
    pub premises: Vec<usize>,
    /// Concrete variable instances from SMT model (like Golem's derivedFact).
    /// Maps variable names to their concrete values (Int, Bool, BitVec) at this derivation step.
    pub instances: FxHashMap<String, SmtValue>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub(crate) struct WitnessNodeKey {
    pub(crate) predicate: PredicateId,
    pub(crate) level: usize,
    pub(crate) state_hash: u64,
}

#[derive(Debug, Default)]
pub(crate) struct WitnessBuilder {
    pub(crate) entries: Vec<DerivationWitnessEntry>,
    pub(crate) index: FxHashMap<WitnessNodeKey, usize>,
}

impl WitnessBuilder {
    pub(crate) fn node(
        &mut self,
        predicate: PredicateId,
        level: usize,
        state: &ChcExpr,
        instances: Option<&FxHashMap<String, SmtValue>>,
    ) -> usize {
        let key = WitnessNodeKey {
            predicate,
            level,
            state_hash: state.structural_hash(),
        };
        if let Some(&idx) = self.index.get(&key) {
            // Collision safety (#2860): verify state expression matches.
            // If it doesn't match, treat as a new node (hash collision).
            if self.entries[idx].state == *state {
                if let Some(instances) = instances {
                    if self.entries[idx].instances.is_empty() && !instances.is_empty() {
                        self.entries[idx].instances = instances.clone();
                    }
                }
                return idx;
            }
            // Hash collision: fall through to create a new node.
            // The index entry is overwritten below, but the old entry remains
            // in the entries vec (referenced by its parent's premises list).
        }

        let idx = self.entries.len();
        self.entries.push(DerivationWitnessEntry {
            predicate,
            level,
            state: state.clone(),
            incoming_clause: None,
            premises: Vec::new(),
            instances: instances.cloned().unwrap_or_default(),
        });
        self.index.insert(key, idx);
        idx
    }

    pub(crate) fn set_derivation(
        &mut self,
        head: usize,
        incoming_clause: usize,
        premises: Vec<usize>,
    ) {
        debug_assert!(
            head < self.entries.len(),
            "set_derivation: head index {} out of range (entries len {})",
            head,
            self.entries.len()
        );
        debug_assert!(
            premises.iter().all(|&p| p < self.entries.len()),
            "set_derivation: premise index out of range"
        );
        let entry = &mut self.entries[head];
        if entry.incoming_clause.is_none() {
            entry.incoming_clause = Some(incoming_clause);
        }
        if entry.premises.is_empty() {
            entry.premises = premises;
        }
    }
}

#[allow(clippy::unwrap_used)]
#[cfg(test)]
mod tests;
