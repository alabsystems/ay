// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Integer and Real objective optimization for SMT solving.
//!
//! Implements `(maximize ...)` and `(minimize ...)` directives via
//! exponential-search + binary-search using `check-sat-assuming`.
//! Supports both Int (BigInt) and Real (BigRational) objectives.
//!
//! Extracted from `executor.rs` as part of the executor.rs decomposition
//! design (the development design notes, Split 2).

mod exact_probe;
#[cfg(test)]
pub(in crate::executor) mod maxsmt_test_hooks;

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::{Symbol, TermData, TermEntryStamp};
use ay_core::{Sort, TermId, TheorySolver};
use ay_frontend::ObjectiveDirection;
use ay_lra::{LraSolver, OptimizationResult, OptimizationSense};
use num_bigint::BigInt;
use num_rational::BigRational;
use num_traits::{One, Signed, ToPrimitive, Zero};

use super::check_sat::contains_symbolic_integer_power;
use super::model::{EvalValue, Model};
use super::quantifier_loop::result_mapping::CheckedGroundDecision;
use super::{Executor, QueryAuthorityEpoch};
use crate::ematching::contains_quantifier;
use crate::executor_types::{ExecutorError, Result, SolveResult, UnknownOrigin, UnknownReason};
use crate::logic_detection::LogicCategory;

/// Upper bound on the TOTAL soft weight the core-guided OLL engine will accept
/// before falling back to the binary-search baseline.
///
/// Weighted-at-most-`W` replicates relaxation indicators by weight. This caps
/// the encoding at a few thousand Booleans; larger instances use the fallback.
pub(crate) const MAXSMT_EXACT_MAX_TOTAL_WEIGHT: u64 = 4096;

/// Per-probe ceiling for disposable optimization authority checks. The checked
/// solver also inherits the enclosing solve's earlier deadline and resource
/// controls, so this never extends a public optimization query's budget.
const OPTIMIZATION_AUTHORITY_PROBE_BUDGET_MS: u64 = 2_000;

/// The actual witness selected by a native optimization producer after its
/// private search window has been restored. The obligations pin the published
/// values/partition; they are validation roots, not public assumptions.
pub(in crate::executor) struct OptimizationModelPublication<'a> {
    model: Option<Model>,
    obligations: &'a [TermId],
}

impl<'a> OptimizationModelPublication<'a> {
    pub(in crate::executor) fn into_parts(self) -> (Option<Model>, &'a [TermId]) {
        (self.model, self.obligations)
    }
}

/// One `:id` group's violated weight in an admitted grouped MaxSMT witness,
/// rendered by `(get-objectives)` in Z3's per-group shape.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct SoftGroupCost {
    /// The group's `:id` label; `None` is the anonymous group (softs without
    /// `:id`), which Z3 renders with an empty objective name.
    pub(crate) id: Option<String>,
    /// Total weight of this group's softs violated by the witness. When
    /// `interval` is set this instead holds the group's TOTAL weight (the
    /// interval's upper end).
    pub(crate) cost: u64,
    /// The group follows an unbounded/unattained lexicographic predecessor,
    /// so no scalar optimum exists; Z3 renders `(interval 0 total)`.
    pub(crate) interval: bool,
}

/// `(finite arithmetic values, per-group optima, suffix-interval, relax vars)`.
type JointSteps<'a> = (
    Vec<(usize, BigRational)>,
    Vec<Option<u64>>,
    bool,
    Option<std::borrow::Cow<'a, [TermId]>>,
);

/// `(soft classification roots, (total_cost, violated, group costs))`.
type JointAccounting = (Vec<TermId>, (u64, Vec<usize>, Vec<SoftGroupCost>));

/// Outcome of the joint lex window search.
enum JointCaptured {
    /// The hard base decided the query before any optimization step.
    Verdict(SolveResult),
    /// An optimal witness: finite arithmetic values, soft classification
    /// roots, captured soft accounting `(total_cost, violated, groups)`, and
    /// the arithmetic values the published witness must attain (all of them
    /// under lex; only the first objective's under box, whose independent
    /// optima no single witness realizes jointly).
    Sat(
        Box<(
            Vec<(usize, BigRational)>,
            Vec<TermId>,
            (u64, Vec<usize>, Vec<SoftGroupCost>),
            Vec<(usize, BigRational)>,
        )>,
    ),
}

/// One `:id` partition cell of the soft list: the soft indices sharing a label.
struct SoftGroup {
    id: Option<String>,
    indices: Vec<usize>,
}

/// Partition soft assertions by `:id` in first-appearance order (Z3's group
/// objective order). Softs without `:id` form the anonymous group.
fn partition_soft_groups(softs: &[ay_frontend::SoftAssertion]) -> Vec<SoftGroup> {
    let mut groups: Vec<SoftGroup> = Vec::new();
    for (index, soft) in softs.iter().enumerate() {
        match groups.iter_mut().find(|group| group.id == soft.id) {
            Some(group) => group.indices.push(index),
            None => groups.push(SoftGroup {
                id: soft.id.clone(),
                indices: vec![index],
            }),
        }
    }
    groups
}

/// Per-group violated weights for `(get-objectives)`, derived purely from the
/// admitted violation partition. Always `Some` for a well-formed partition:
/// soft objectives render in Z3's shape for every group layout, including a
/// single anonymous group.
fn soft_group_costs(
    softs: &[ay_frontend::SoftAssertion],
    violated: &[usize],
) -> Option<Vec<SoftGroupCost>> {
    let groups = partition_soft_groups(softs);
    let mut is_violated = vec![false; softs.len()];
    for &index in violated {
        *is_violated.get_mut(index)? = true;
    }
    groups
        .iter()
        .map(|group| {
            let mut cost = 0u64;
            for &index in &group.indices {
                if is_violated[index] {
                    cost = cost.checked_add(softs[index].weight)?;
                }
            }
            Some(SoftGroupCost {
                id: group.id.clone(),
                cost,
                interval: false,
            })
        })
        .collect()
}

/// Multi-objective priority requested via `(set-option :opt.priority ...)`.
///
/// Structured optimum of a single objective after an optimizing `check-sat`.
///
/// This is the structured analogue of one line of `(get-objectives)`: it carries
/// the same value that the SMT-LIB renderer would print, but as data rather than
/// formatted text so the native [`crate::api::Solver`] API (and the FFI built on
/// it) can read an objective's optimum without parsing a string. The resolution
/// order mirrors [`Executor::get_objectives`] exactly (unbounded map → admitted
/// indexed finite outcomes), so the two never diverge and a plain feasibility
/// model can never be mislabeled as an optimum.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum ObjectiveOutcome {
    /// A finite optimum (Int/BitVec optima are whole rationals; Real may be a
    /// proper fraction). For BitVec objectives this is the unsigned integer
    /// value, matching `(get-objectives)`.
    Finite(BigRational),
    /// A finite but UNATTAINED Real optimum `value + eps_coeff·ε`
    /// (#opt-epsilon): the sup/inf of an open face — approached within every
    /// δ>0, never reached. `eps_coeff` is nonzero and sign-matched to the
    /// direction (maximize ⇒ negative, minimize ⇒ positive). This is the
    /// structured form of the `(get-objectives)` epsilon shapes
    /// (`(+ 3.0 (* (- 1.0) epsilon))` etc.).
    Epsilon {
        /// The unattained supremum/infimum (the finite part).
        value: BigRational,
        /// The signed, nonzero epsilon coefficient.
        eps_coeff: BigRational,
    },
    /// `+oo`: an unbounded `maximize` objective (SMT-LIB OMT `oo`).
    PosInfinity,
    /// `-oo`: an unbounded `minimize` objective (SMT-LIB OMT `(* (- 1) oo)`, the z3 shape).
    NegInfinity,
    /// The optimum is not available (e.g. the last solve was not SAT, or the
    /// objective term could not be evaluated against the witnessing model).
    Unavailable,
}

/// All three Z3-compatible priorities are represented; an unknown value is
/// mapped onto `Lex` (with a warning) by [`Executor::opt_priority`].
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum OptPriority {
    /// Lexicographic: optimize objectives in order, committing each optimum.
    Lex,
    /// Box: optimize each objective independently against the hard constraints.
    Box,
    /// Pareto: enumerate the Pareto front, one optimal point per `(check-sat)`.
    Pareto,
}

/// Stateful Pareto-front enumeration state (Guided Improvement Algorithm).
///
/// Lives on the [`Executor`] across consecutive `(check-sat)` calls in pareto
/// mode and is reset by `invalidate_last_check_result` whenever the problem
/// changes. See [`Executor::optimize_pareto`] for the algorithm.
#[derive(Debug, Clone, Default)]
pub(crate) struct ParetoState {
    /// Objective values of every Pareto point already emitted, in emission order.
    /// Each inner `Vec<BigRational>` is indexed by objective declaration order.
    /// New points must NOT be dominated-or-equal by any of these, so each
    /// previously emitted point contributes a "strictly better on >= 1 objective"
    /// blocking constraint to the next-point search.
    emitted: Vec<Vec<BigRational>>,
    /// The most recently emitted point's objective values, for `(get-objectives)`.
    /// Z3 reports the LAST emitted point's objectives after the terminal `unsat`,
    /// so this survives front exhaustion until the next `(check-sat)` restarts.
    /// `pub(crate)` so the `get-objectives` renderer (sibling module) can report
    /// the last point on the terminal `unsat`.
    pub(crate) last_point: Option<Vec<BigRational>>,
}

/// Opaque obligation extension produced by the exact Pareto-front blocker
/// construction that is subsequently probed for infeasibility.
///
/// Its fields are private to this module, so no other executor component can
/// widen an UNSAT proof scope with an arbitrary term (especially `false`). The
/// token also binds the blockers to the active public query, source scope,
/// authored hard roots, and objective inventory.
pub(crate) struct ParetoFrontExhaustionExtension {
    query_epoch: QueryAuthorityEpoch,
    source_context_stamp: ay_frontend::SourceContextStamp,
    hard_roots: Box<[TermId]>,
    hard_root_entries: Box<[TermEntryStamp]>,
    /// The sealed objective inventory authenticated against
    /// `ctx.objectives()` (the caller's real objectives) and copied into
    /// the epoch's declared extension.
    objectives: Box<[ay_frontend::Objective]>,
    objective_entries: Box<[TermEntryStamp]>,
    /// The objective vector the blockers were built over. Identical to
    /// `objectives` in the pure-arithmetic lane; in the joint lane it is
    /// the extended vector (real objectives interleaved with synthesized
    /// soft-group cost objectives), which never enters `ctx`.
    blocking_objectives: Box<[ay_frontend::Objective]>,
    blocking_objective_entries: Box<[TermEntryStamp]>,
    blocking: Box<[TermId]>,
    blocking_entries: Box<[TermEntryStamp]>,
}

impl ParetoFrontExhaustionExtension {
    fn entries_are_current(
        executor: &Executor,
        terms: &[TermId],
        entries: &[TermEntryStamp],
    ) -> bool {
        entries.len() == terms.len()
            && entries.iter().copied().map(Some).eq(terms
                .iter()
                .map(|&term| executor.ctx.terms.entry_stamp(term)))
    }

    fn objective_entries_are_current(&self, executor: &Executor) -> bool {
        self.objective_entries.len() == self.objectives.len()
            && self.objective_entries.iter().copied().map(Some).eq(self
                .objectives
                .iter()
                .map(|objective| executor.ctx.terms.entry_stamp(objective.term)))
            && self.blocking_objective_entries.len() == self.blocking_objectives.len()
            && self
                .blocking_objective_entries
                .iter()
                .copied()
                .map(Some)
                .eq(self
                    .blocking_objectives
                    .iter()
                    .map(|objective| executor.ctx.terms.entry_stamp(objective.term)))
    }

    /// Whether the blocker construction had no objective inventory at
    /// all (the declaration gate's emptiness test).
    pub(in crate::executor) fn inventory_is_empty(&self) -> bool {
        self.blocking_objectives.is_empty()
    }

    pub(in crate::executor) fn is_current(&self, executor: &Executor) -> bool {
        self.query_epoch
            .is_same_epoch(&executor.query_authority_epoch)
            && self.source_context_stamp == executor.ctx.source_context_stamp()
            && self.hard_roots.as_ref() == executor.ctx.assertions.as_slice()
            && Self::entries_are_current(executor, &self.hard_roots, &self.hard_root_entries)
            && self.objectives.as_ref() == executor.ctx.objectives()
            && self.objective_entries_are_current(executor)
            && Self::entries_are_current(executor, &self.blocking, &self.blocking_entries)
    }

    pub(in crate::executor) fn into_current_binding(
        self,
        executor: &Executor,
    ) -> Option<ParetoFrontExhaustionBinding> {
        self.is_current(executor)
            .then_some(ParetoFrontExhaustionBinding {
                hard_roots: self.hard_roots,
                hard_root_entries: self.hard_root_entries,
                objectives: self.objectives,
                objective_entries: self.objective_entries,
                blocking: self.blocking,
                blocking_entries: self.blocking_entries,
            })
    }

    fn blocking(&self) -> &[TermId] {
        &self.blocking
    }
}

/// Exact, already-current Pareto blocker payload transferred into the public
/// UNSAT query epoch.
///
/// Keeping term-entry identities beside every numeric [`TermId`] prevents the
/// UNSAT authority layer from refreshing a blocker, objective, or authored root
/// after speculative rollback reused its slot.
pub(in crate::executor) struct ParetoFrontExhaustionBinding {
    pub(in crate::executor) hard_roots: Box<[TermId]>,
    pub(in crate::executor) hard_root_entries: Box<[TermEntryStamp]>,
    pub(in crate::executor) objectives: Box<[ay_frontend::Objective]>,
    pub(in crate::executor) objective_entries: Box<[TermEntryStamp]>,
    pub(in crate::executor) blocking: Box<[TermId]>,
    pub(in crate::executor) blocking_entries: Box<[TermEntryStamp]>,
}

/// Borrowed per-call data for one joint Pareto search: the sealed real
/// objectives, the extended objective vector with its step map, and the
/// soft relaxation (vars plus unasserted clauses).
struct JointParetoFrame<'a> {
    sealed_objectives: &'a [ay_frontend::Objective],
    sequence: &'a [ay_frontend::ObjectiveStep],
    extended: &'a [ay_frontend::Objective],
    step_map: &'a [ParetoStepKind],
    softs: &'a [ay_frontend::SoftAssertion],
    groups: &'a [SoftGroup],
    soft_terms: &'a [TermId],
    soft_weights: &'a [u64],
    relax_vars: &'a [TermId],
    relax_clauses: &'a [TermId],
}

/// Outcome of one Pareto feasibility probe (see [`Executor::pareto_probe`]).
///
/// Only the verdict matters to the caller: the seed probe just needs to know
/// whether a non-dominated feasible point exists, and the optimal witness +
/// objective values are read from `self.last_model` after the lex-push, not from
/// here. (Carrying the model/values in the variant would otherwise be dead.)
/// One position of the joint Pareto extended objective vector: a real
/// arithmetic objective (by its declaration index) or a soft group (by
/// partition index) whose synthesized cost term sits at this position.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParetoStepKind {
    Arithmetic(usize),
    Group(usize),
}

/// Captured outcome of one joint Pareto search call, mirroring
/// [`JointCaptured`]: publication happens after the transactional cleanup.
enum JointParetoCaptured {
    /// The hard base decided the query, or the front is exhausted.
    Verdict(SolveResult),
    /// An emitted point: finite arithmetic values (real indices), soft
    /// classification roots, and captured soft accounting.
    Sat(
        Box<(
            Vec<(usize, BigRational)>,
            Vec<TermId>,
            (u64, Vec<usize>, Vec<SoftGroupCost>),
        )>,
    ),
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum ParetoProbe {
    /// Feasible under the probe's assumptions.
    Sat,
    /// Infeasible under the probe's assumptions.
    Unsat,
    /// The probe was inconclusive.
    Unknown,
}

/// Result of an exact, disposable optimization feasibility check.
///
/// Unlike [`SolveResult`], this type is constructed only after the checked
/// token has been consumed against the identical ordered assertion vector.
/// No model crosses the isolation boundary.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum CheckedOptimizationDecision {
    Sat,
    Unsat,
    Unknown,
}

/// Outcome of a one-shot LRA simplex optimization attempt.
///
/// Distinguishes a genuine unbounded objective from "simplex could not decide",
/// so the caller does not fall into the iterative strict-improvement loop and
/// report an arbitrary finite value as the optimum.
enum SimplexOpt {
    /// Exact finite optimum, with the dual (Farkas) optimality certificate
    /// when one could be extracted from the simplex (#lra-opt-cert).
    ///
    /// The `bool` is `needs_maximality_twin` (#opt-epsilon soundness gate):
    /// `true` when the standalone tableau saw a STRICT bound and no verified
    /// certificate survived. The Optimal lane's full-solver confirmation
    /// (`check_sat_assuming(obj >= v)` must be Sat) is ONE-SIDED — it proves
    /// attainability, never maximality — and strict-bound problems only
    /// reach this lane since the delta-simplex conversion, so an
    /// UNDERestimating conversion bug would otherwise publish unchecked.
    /// When set, the caller must also prove `obj > v` UNSAT (or fall back).
    Optimal(BigRational, Option<ay_lra::OptimalityCertificate>, bool),
    /// A finite UNATTAINED optimum (#opt-epsilon): the delta-simplex
    /// terminated at `value + eps_coeff·ε` with `eps_coeff != 0` (strict
    /// bounds bind the objective). Emitted only when BOTH faithfulness
    /// audits passed, no Int-sorted term participates, and the ε-sign
    /// matches the sense — the caller must still refute attainability
    /// (`obj >= v` UNSAT for maximize) and confirm δ-closeness via the full
    /// solver before publishing.
    OptimalInf {
        value: BigRational,
        eps_coeff: BigRational,
    },
    /// The objective is unbounded in the requested direction.
    Unbounded,
    /// Simplex is not applicable; fall back to the iterative approach.
    NotApplicable,
}

impl Executor {
    /// Exact ordered roots for one optimization sub-obligation.
    ///
    /// `ctx.assertions` already contains every active hard root plus any
    /// transient lex/Pareto/MaxSMT extension. Assumptions are appended in their
    /// solver order so the disposable proof is about precisely the conjunction
    /// whose feasibility controls the optimization state transition.
    fn optimization_probe_roots(&self, assumptions: &[TermId]) -> Vec<TermId> {
        let mut roots = self.ctx.assertions.clone();
        roots.extend_from_slice(assumptions);
        roots
    }

    /// Decide one exact optimization obligation without importing a model or a
    /// raw nested-solver verdict.
    ///
    /// Ground obligations use the checked ground decision API. Quantified
    /// obligations use the exact two-sided API: SAT crosses the disposable
    /// boundary only as a public-emission certificate, never as a raw model.
    fn checked_optimization_decision(
        &mut self,
        assumptions: &[TermId],
    ) -> CheckedOptimizationDecision {
        let roots = self.optimization_probe_roots(assumptions);
        self.checked_optimization_roots_decision(&roots)
    }

    fn checked_optimization_roots_decision(
        &mut self,
        roots: &[TermId],
    ) -> CheckedOptimizationDecision {
        if roots
            .iter()
            .any(|&root| contains_quantifier(&self.ctx.terms, root))
        {
            return self.checked_optimization_quantified_decision(roots);
        }

        match self.checked_ground_solve(
            roots.to_vec(),
            LogicCategory::Other,
            OPTIMIZATION_AUTHORITY_PROBE_BUDGET_MS,
        ) {
            Some(CheckedGroundDecision::Sat(checked)) => {
                if checked.consume(self, roots) {
                    CheckedOptimizationDecision::Sat
                } else {
                    CheckedOptimizationDecision::Unknown
                }
            }
            Some(CheckedGroundDecision::Unsat(checked)) => {
                if checked.consume(self, roots) {
                    CheckedOptimizationDecision::Unsat
                } else {
                    CheckedOptimizationDecision::Unknown
                }
            }
            _ => CheckedOptimizationDecision::Unknown,
        }
    }

    /// Strictly recheck a proposed optimization UNSAT over the exact active
    /// hard/extension roots and assumptions. This is the only authority used to
    /// move a search bound, accept an OLL core, or terminate an improvement loop
    /// when the SAT side still needs the enclosing executor's model.
    fn checked_optimization_unsat(&mut self, assumptions: &[TermId]) -> bool {
        let roots = self.optimization_probe_roots(assumptions);
        self.checked_optimization_roots_unsat(&roots)
    }

    /// Strict-UNSAT twin for a caller that already captured its full ordered
    /// root window before a raw same-context model probe could rewrite working
    /// assertions.
    fn checked_optimization_roots_unsat(&mut self, roots: &[TermId]) -> bool {
        self.checked_exact_unsat_solve(roots.to_vec(), OPTIMIZATION_AUTHORITY_PROBE_BUDGET_MS)
            .is_some_and(|checked| checked.consume(self, roots))
    }

    /// Same-Context probe for search steps whose SAT arm still needs the raw
    /// validated model. SAT transport remains deliberately local to the
    /// existing caller; an UNSAT result crosses this helper only after a strict
    /// checked re-solve of the pre-probe H + extension + assumptions roots.
    fn optimization_model_probe(&mut self, assumptions: &[TermId]) -> Result<SolveResult> {
        let exact_roots = self.optimization_probe_roots(assumptions);
        let result = self.check_sat_assuming(assumptions)?;
        if result.is_unsat() && !self.checked_optimization_roots_unsat(&exact_roots) {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }
        Ok(result)
    }

    /// Solve a MaxSMT problem from `(assert-soft ...)` soft constraints.
    ///
    /// SOUNDNESS: a soft constraint is NOT a hard constraint. This
    /// minimizes the total weight of *violated* soft constraints subject to the
    /// HARD assertions, returning `sat` with a weight-optimal model whenever the
    /// hard assertions are satisfiable and `unsat` only when the hard assertions
    /// alone are unsatisfiable.
    ///
    /// ## Reduction (shared by SMT-LIB and the native `check_sat_max` API)
    ///
    /// For each soft constraint `i` with term `t_i` and weight `w_i`:
    /// 1. declare a fresh Bool relaxation indicator `relax_i`;
    /// 2. assert the HARD clause `(or t_i relax_i)` — so `relax_i = false`
    ///    forces `t_i` true (satisfied), while `relax_i = true` permits `t_i`
    ///    to be given up (violated).
    ///
    /// Then the minimum total VIOLATED WEIGHT — the assert-soft optimum, i.e. the
    /// sum of the weights of the violated softs (NOT the violation count) — is
    /// found EXACTLY via a weighted-at-most-`W` search over the relaxation
    /// indicators (binary search on the weight budget `W`, sound because
    /// feasibility is monotone in `W`). For a total soft weight above the
    /// tractability cap [`MAXSMT_EXACT_MAX_TOTAL_WEIGHT`] the SMT-LIB engine may
    /// retain a feasible count-minimized/greedily repaired witness, explicitly
    /// marked approximate; the native API has no approximate result variant and
    /// therefore returns honest `Unknown` before entering that lane. Every step
    /// uses the COMPLETE `check_sat()`
    /// pipeline over a purely Boolean cardinality encoding, so the search stays
    /// inside the base logic — crucially, it does NOT introduce an integer cost
    /// objective, which would pull a QF_BV problem into the
    /// (optimization-incomplete) QF_BV+LIA bridge and yield a sound-but-suboptimal
    /// cost. [`crate::api::Solver::check_sat_max`] routes through this same engine
    /// so the two public surfaces cannot drift in accounting or transaction
    /// behavior.
    ///
    /// ## Scoping / idempotency
    ///
    /// Relaxation/cardinality clauses are asserted onto `ctx.assertions` and
    /// reverted via a snapshot/truncate after solving; the internal relaxation
    /// and counter symbols (reserved `__ay_soft_*` prefix, so they cannot
    /// collide with user names) are removed from the symbol table. This keeps a
    /// second `(check-sat)` re-materializing cleanly and `get-assertions` /
    /// `get-model` free of internals. The optimal model and the minimized total
    /// violated weight are captured and re-installed so `(get-model)` /
    /// `(get-value ...)` answer over the optimal model and `(get-objectives)`
    /// reports the optimal cost (via `last_soft_cost`).
    pub(in crate::executor) fn maxsmt_check_sat(&mut self) -> Result<SolveResult> {
        self.last_sat_certificate = None;
        self.last_soft_violations = None;
        self.last_soft_group_costs = None;
        let softs = self.ctx.soft_constraints().to_vec();
        debug_assert!(
            !softs.is_empty(),
            "maxsmt_check_sat called without soft constraints"
        );

        // MaxSMT materializes relaxation/cardinality scaffolding before its
        // first ordinary `check_sat` probe. Apply the dense-BV boundary to the
        // hard and soft DAGs up front so native oversized terms cannot make
        // that preprocessing needlessly expand an unsupported problem.
        let solve_roots = self.public_solve_roots(&[]);
        if let Some(result) = self.reject_array_ext_witness_capture(&solve_roots) {
            return Ok(result);
        }
        if let Some(result) = self.reject_unsupported_bitvector_width(&solve_roots) {
            return Ok(result);
        }
        if let Some(result) = self.reject_unsupported_fp_model_format(&solve_roots) {
            return Ok(result);
        }

        // `:id` is semantic (Z3): it partitions soft assertions into separate
        // group objectives. Under the default (lex) priority they optimize
        // lexicographically in first-appearance order
        // (`maxsmt_solve_grouped_lex`); under `box` each group optimizes
        // independently (`maxsmt_solve_grouped_box`). A single group (named
        // or anonymous) under lex/box is the flat problem the existing
        // engines already solve. Under `pareto` with a multi-objective
        // vector the stateful front enumerator owns the query; a single
        // unified objective degenerates to the flat optimum (z3 too).
        let groups = partition_soft_groups(&softs);
        if self.opt_priority() == OptPriority::Pareto {
            let objectives = self.ctx.objectives().to_vec();
            // A single unified objective degenerates to plain optimization
            // in z3 (optimum re-emitted, never exhausted): the flat engine
            // below already has exactly that behavior for one group.
            if groups.len() > 1 || !objectives.is_empty() {
                return self.joint_optimize_pareto(&objectives);
            }
        }

        // Snapshot the assertion stack so the temporary relaxation clauses (and
        // any leftover probe clauses on a failure path) can be reverted.
        // Relaxation clauses are asserted at the CURRENT scope level so the
        // cardinality probes see them in their base — mirroring `check_sat_max`.
        let assertion_snapshot = self.ctx.assertions.len();

        // Engine selection (`(set-option :ay-maxsmt-engine oll)`; default
        // "binary"). The core-guided OLL engine (`maxsmt_solve_oll`) is opt-in
        // and SOUNDNESS-FIRST: it returns `Ok(None)` whenever it cannot guarantee
        // the binary-search baseline's optimum (quantifiers, non-uniform weights,
        // empty/degenerate cores, unknown probes, overflow), in
        // which case we fall back to the always-sound `maxsmt_solve` over the
        // SAME assertion snapshot. "binary" always uses the baseline. An unknown
        // value is rejected rather than silently ignored.
        let engine = match self.ctx.get_option("ay-maxsmt-engine") {
            Some(ay_frontend::OptionValue::String(s)) => s.clone(),
            _ => "binary".to_string(),
        };
        // Box publication needs the solver's independent per-group optima
        // (the published witness attains only the first group's), so the box
        // arm returns them alongside the usual outcome tuple.
        let mut solver_group_costs: Option<Vec<SoftGroupCost>> = None;
        let outcome = match engine.as_str() {
            // Grouped softs always take a grouped engine (the priority gate
            // above already refused pareto): OLL covers only non-grouped
            // instances, and the flat baseline would optimize the wrong
            // (summed) objective.
            "binary" | "oll" if groups.len() > 1 && self.opt_priority() == OptPriority::Box => {
                match self.maxsmt_solve_grouped_box(&softs, &groups) {
                    Ok((tuple, costs)) => {
                        solver_group_costs = Some(costs);
                        Ok(tuple)
                    }
                    Err(error) => Err(error),
                }
            }
            "binary" | "oll" if groups.len() > 1 => self.maxsmt_solve_grouped_lex(&softs, &groups),
            "binary" => self.maxsmt_solve(&softs),
            "oll" => match self.maxsmt_solve_oll(&softs) {
                // OLL covered the instance: use its optimum directly. Any
                // temporary relaxation/cardinality clauses it asserted are
                // reverted by the snapshot/truncate below, exactly as for the
                // baseline.
                Ok(Some(result)) => Ok(result),
                // OLL declined (fell back): revert anything it touched so the
                // baseline solves over the pristine hard-only snapshot, then run
                // the baseline. The truncate keeps the two engines from
                // double-counting relaxation clauses.
                Ok(None) => {
                    self.ctx.truncate_assertions(assertion_snapshot);
                    let internal: Vec<String> = self
                        .ctx
                        .symbol_iter()
                        .map(|(name, _)| name.clone())
                        .filter(|name| name.starts_with("__ay_soft_"))
                        .collect();
                    self.ctx.remove_symbols(&internal);
                    self.maxsmt_solve(&softs)
                }
                Err(e) => Err(e),
            },
            other => Err(ExecutorError::UnsupportedOptimization(format!(
                "unknown ay-maxsmt-engine '{other}' (expected 'binary' or 'oll')"
            ))),
        };

        // Always revert the temporary relaxation clauses and internal relax /
        // cardinality-counter symbols so a second `(check-sat)` re-materializes
        // cleanly and `get-assertions`/`get-model` stay free of internals.
        self.ctx.truncate_assertions(assertion_snapshot);
        let internal_symbols: Vec<String> = self
            .ctx
            .symbol_iter()
            .map(|(name, _)| name.clone())
            .filter(|name| name.starts_with("__ay_soft_"))
            .collect();
        self.ctx.remove_symbols(&internal_symbols);

        let (captured_result, captured_model, captured_cost, captured_optimal, captured_violations) =
            match outcome {
                Ok(captured) => captured,
                Err(error) => {
                    // An engine can fail after one or more successful internal
                    // probes. Those probes solve the temporary relaxation scope and
                    // may have minted a SAT token/model; none is a public MaxSMT
                    // result once the overall operation errors.
                    self.invalidate_last_check_result();
                    return Err(error);
                }
            };

        // Hard-unsatisfiable: the hard assertions alone are UNSAT (independent of
        // any soft). Re-run a plain check_sat over the restored hard-only
        // assertion set so the UNSAT verdict — and, when enabled, its proof — is
        // established over the user's genuine hard constraints. This keeps
        // `(get-proof)` / proof verification working for hard-unsat MaxSMT inputs.
        if captured_result.is_unsat() {
            // Internal relaxation/counter declarations deliberately advance the
            // frontend source-context revision. They have all been removed above,
            // but a monotonic stamp must never be rewound: restart exact public
            // UNSAT authority on the now-restored hard roots instead. The outer
            // command will certify this fresh hard-only proof before publication.
            self.begin_public_solve(false);
            self.bind_unsat_query_assumptions(&[]);
            let hard_result = self.check_sat();
            if hard_result.is_err() {
                self.invalidate_last_check_result();
            }
            return hard_result;
        }

        // Re-install the captured optimal solve artefacts.
        // The captured model may differ from the most recently validated probe
        // model. Never let that probe's evidence follow a replacement witness
        // into the outer check-sat emission funnel.
        self.last_model_validated = false;
        self.last_model = captured_model;
        self.last_unknown_reason = if captured_result == SolveResult::Sat {
            None
        } else {
            self.last_unknown_reason
        };
        self.last_result = Some(captured_result.clone());
        // The last internal probe's certificate and validation evidence describe
        // that probe's temporary assertion scope and model, not necessarily the
        // captured optimum re-installed above. Revalidate and mint over the
        // restored HARD assertion scope. This is the only point at which the
        // captured MaxSMT witness becomes a public SAT result.
        self.last_soft_cost = None;
        self.last_soft_cost_optimal = false;
        self.last_soft_violations = None;
        self.last_soft_group_costs = None;
        // Bind the public certificate to the exact soft partition established
        // while the relaxation variables still existed.  A satisfied soft is
        // an additional positive root; a violated soft is an additional
        // `(not soft)` root.  Without these roots, output completion or a strict
        // repair in `emit_sat_verdict` could change a soft value while checking
        // only the restored hard scope, after which publishing the old cost and
        // violation vector would attach optimization claims to the wrong model.
        let classification_roots = if captured_result == SolveResult::Sat {
            let Some(roots) = self.maxsmt_classification_roots(&softs, &captured_violations) else {
                return Ok(self.reject_maxsmt_final_witness());
            };
            roots
        } else {
            Vec::new()
        };
        let emitted =
            match self.emit_captured_optimization_witness(captured_result, &classification_roots) {
                Ok(emitted) => emitted,
                Err(error) => {
                    // Errors are also non-admissions. The executor remains usable
                    // after many recoverable command errors, so no partial optimum
                    // or pre-error witness may remain queryable.
                    self.invalidate_last_check_result();
                    return Err(error);
                }
            };
        if emitted == SolveResult::Sat {
            #[cfg(test)]
            if self.forced_maxsmt_post_emit_soft_flip.replace(false) {
                let first_soft = softs
                    .first()
                    .expect("post-emission MaxSMT canary requires a soft")
                    .term;
                let model = self
                    .last_model
                    .as_mut()
                    .expect("post-emission MaxSMT canary requires a model");
                let var = *model
                    .term_to_var
                    .get(&first_soft)
                    .expect("post-emission MaxSMT canary requires a Bool SAT variable");
                let value = model
                    .sat_model
                    .get_mut(var as usize)
                    .expect("post-emission MaxSMT canary SAT variable must be in range");
                *value = !*value;
                super::model::eval_memo_clear();
            }

            // Recompute from the FINAL model using the soft terms themselves —
            // never the now-removed relaxation variables. Every term must be
            // definitively Boolean, and both the cost and complete partition
            // must equal what the optimizing scope certified. This is the final
            // defense against any model mutation inside or after emission.
            let Some(final_accounting) = self.maxsmt_final_witness_accounting(&softs) else {
                return Ok(self.reject_maxsmt_final_witness());
            };
            if final_accounting != (captured_cost, captured_violations.clone()) {
                return Ok(self.reject_maxsmt_final_witness());
            }

            // Publish the objective only after the final witness itself was
            // admitted and re-accounted. Per-group costs are a pure function
            // of the admitted violation partition, so deriving them here (not
            // in the solver) keeps them bound to the final witness by the
            // same equality check above.
            self.last_soft_cost = Some(captured_cost);
            self.last_soft_cost_optimal = captured_optimal;
            // Box group costs are independent optima the published witness
            // need not attain (it attains the first group's), so they come
            // from the solver; every other path derives them from the
            // admitted violation partition.
            self.last_soft_group_costs =
                solver_group_costs.or_else(|| soft_group_costs(&softs, &captured_violations));
            self.last_soft_violations = Some(captured_violations);
        } else {
            // A fail-closed model-validation downgrade admits neither a witness
            // nor an optimum. Clear every optimization artefact that could make
            // a subsequent query imply otherwise.
            self.last_sat_certificate = None;
            self.last_model_validated = false;
            self.last_model = None;
            self.last_soft_cost = None;
            self.last_soft_cost_optimal = false;
            self.last_soft_violations = None;
            self.last_soft_group_costs = None;
            self.finite_objective_values.clear();
            self.unbounded_objectives.clear();
            self.infinitesimal_objectives.clear();
            self.unavailable_objectives.clear();
            self.objective_certificates.clear();
            self.pareto_state = None;
        }

        Ok(emitted)
    }

    /// Turn the relaxation-derived soft partition into validation roots for the
    /// final public model. Returns `None` for malformed (duplicate/out-of-range)
    /// accounting rather than silently changing its meaning.
    fn maxsmt_classification_roots(
        &mut self,
        softs: &[ay_frontend::SoftAssertion],
        violated_softs: &[usize],
    ) -> Option<Vec<TermId>> {
        let mut violated = vec![false; softs.len()];
        for &index in violated_softs {
            let slot = violated.get_mut(index)?;
            if std::mem::replace(slot, true) {
                return None;
            }
        }
        Some(
            softs
                .iter()
                .enumerate()
                .map(|(index, soft)| {
                    if violated[index] {
                        self.ctx.terms.mk_not(soft.term)
                    } else {
                        soft.term
                    }
                })
                .collect(),
        )
    }

    /// Recompute MaxSMT accounting exclusively from the final public model.
    /// Unlike the in-scope relaxation accounting, an unevaluable soft is not a
    /// conservative violation here: the published partition claims an exact
    /// truth value for every soft, so any non-Boolean result must fail closed.
    fn maxsmt_final_witness_accounting(
        &self,
        softs: &[ay_frontend::SoftAssertion],
    ) -> Option<(u64, Vec<usize>)> {
        let model = self.last_model.as_ref()?;
        let mut cost = 0u64;
        let mut violated = Vec::new();
        for (index, soft) in softs.iter().enumerate() {
            match self.evaluate_term(model, soft.term) {
                EvalValue::Bool(true) => {}
                EvalValue::Bool(false) => {
                    cost = cost.checked_add(soft.weight)?;
                    violated.push(index);
                }
                _ => return None,
            }
        }
        Some((cost, violated))
    }

    /// Revoke every partially admitted artifact when the final model does not
    /// realize the partition/cost certified in the temporary MaxSMT scope.
    fn reject_maxsmt_final_witness(&mut self) -> SolveResult {
        self.invalidate_last_check_result();
        self.last_unknown_reason = Some(UnknownReason::InternalError);
        self.last_result = Some(SolveResult::Unknown);
        SolveResult::Unknown
    }

    /// Push a temporary hard assertion for the MaxSMT reduction, keeping
    /// `assertions` and `assertions_parsed` aligned.
    ///
    /// The native API (`try_assert_term`) maintains this alignment for every
    /// assertion; the incremental encoding and proof-rewrite paths depend on it.
    /// Pushing onto `ctx.assertions` alone (without a parallel `assertions_parsed`
    /// entry) desynchronizes the two vectors and makes the theory solve return
    /// spurious `unknown`. A placeholder parsed term keeps them aligned;
    /// `truncate_assertions` reverts both vectors together.
    fn maxsmt_assert(&mut self, term: TermId) {
        self.ctx.add_transient_assertion_with_parsed(
            term,
            ay_frontend::Term::Symbol("__ay_soft_internal__".to_string()),
        );
    }

    /// Push a transient objective-optimization constraint while keeping the
    /// elaborated and parsed assertion stacks aligned. The caller must restore
    /// both stacks with `Context::truncate_assertions` on every exit path.
    fn optimization_assert(&mut self, term: TermId) {
        self.ctx.add_transient_assertion_with_parsed(
            term,
            ay_frontend::Term::Symbol("__ay_opt_internal__".to_string()),
        );
    }

    /// Build the relaxation layer shared by every MaxSMT engine: one fresh
    /// `__ay_soft_relax_{i}` Bool selector per soft, plus the hard clause
    /// `(or soft_i relax_i)`. Returns the selectors in soft order.
    ///
    /// Both the binary-search baseline and the core-guided OLL engine (Phase 2)
    /// build IDENTICAL selectors through this helper, so their optima are
    /// directly comparable by the cross-check oracle. Selectors use the reserved
    /// `__ay_soft_*` prefix (cannot collide with user names) and are reverted by
    /// the snapshot/truncate + `remove_symbols` in `maxsmt_check_sat`.
    fn maxsmt_build_relaxation(&mut self, soft_terms: &[TermId]) -> Vec<TermId> {
        let mut relax_vars: Vec<TermId> = Vec::with_capacity(soft_terms.len());
        for (i, &soft_term) in soft_terms.iter().enumerate() {
            let relax_name = format!("__ay_soft_relax_{i}");
            let relax = self
                .ctx
                .terms
                .mk_fresh_named_var(relax_name.clone(), Sort::Bool);
            self.ctx.register_symbol(relax_name, relax, Sort::Bool);
            relax_vars.push(relax);

            let clause = self.ctx.terms.mk_or(vec![soft_term, relax]);
            self.maxsmt_assert(clause);
        }
        relax_vars
    }

    /// MaxSMT search: exact bounded weighted optimization with a sound,
    /// explicitly approximate count/greedy fallback above the encoding cap.
    ///
    /// Shared by [`crate::api::Solver::check_sat_max`] and parsed SMT-LIB
    /// `(assert-soft ...)`. Asserts the relaxation
    /// clauses at the current scope, finds the minimum violation count via binary
    /// search over an at-most-k cardinality constraint (each probe over a
    /// temporary, non-incremental extension of the assertion stack), then greedily
    /// forces the most expensive softs satisfied at that count. Returns
    /// `(result, optimal_model, total_violated_weight)`.
    ///
    /// SOUNDNESS: violation is decided from the relaxation indicators and the
    /// soft term's model value, never force-counting an unevaluable soft term as
    /// violated (mirroring `find_violated_softs`). The base feasibility check
    /// distinguishes a hard-UNSAT formula (returns UNSAT) from a satisfiable one.
    /// Returns `(result, model, cost, optimal)`. `optimal == false` marks a
    /// resource-limited or weight-incomplete outcome: the model is feasible
    /// and `cost` is its true violated weight (a sound upper bound), but the
    /// value is NOT proven to be the optimum and is reported as approximate.
    fn maxsmt_solve(
        &mut self,
        softs: &[ay_frontend::SoftAssertion],
    ) -> Result<(SolveResult, Option<Model>, u64, bool, Vec<usize>)> {
        let n = softs.len();
        let soft_terms: Vec<TermId> = softs.iter().map(|s| s.term).collect();
        let soft_weights: Vec<u64> = softs.iter().map(|s| s.weight).collect();
        let Some(total_weight) = soft_weights
            .iter()
            .try_fold(0u64, |sum, &weight| sum.checked_add(weight))
        else {
            // Parsed SMT-LIB weights are not pre-gated by the native API. An
            // overflowing total has no representable exact objective value;
            // fail closed before building any relaxation state.
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok((SolveResult::Unknown, None, 0, false, Vec::new()));
        };

        // Relaxation indicators + hard clauses `(or t_i relax_i)` at the current
        // scope level (so probes see them in their base, like `check_sat_max`),
        // built through the shared helper so every engine uses identical
        // selectors.
        let relax_vars = self.maxsmt_build_relaxation(&soft_terms);

        // Base feasibility (all relaxations free): is the hard formula SAT?
        let base = self.maxsmt_scoped_checked_decision(|_| {});
        match base {
            CheckedOptimizationDecision::Sat => {}
            CheckedOptimizationDecision::Unsat => {
                return Ok((SolveResult::unsat(), None, 0, true, Vec::new()));
            }
            CheckedOptimizationDecision::Unknown => {
                return Ok((SolveResult::Unknown, None, 0, false, Vec::new()));
            }
        }

        // === Exact weighted optimum (tractable total weight) ===
        // The assert-soft optimum is the minimum total VIOLATED WEIGHT (the sum of
        // the weights of violated softs), NOT the violation COUNT. Minimizing the
        // count first (as a pure cardinality search does) is weight-suboptimal
        // when weights differ — e.g. violating one weight-5 soft (count 1, weight
        // 5) is worse than violating two weight-1 softs (count 2, weight 2). For a
        // tractable total weight we minimize the WEIGHT exactly via the trusted
        // weighted-at-most-`W` encoding; binary search is sound because feasibility
        // is monotone in the weight budget `W` (a larger budget is strictly more
        // permissive).
        if total_weight <= MAXSMT_EXACT_MAX_TOTAL_WEIGHT {
            let mut lo: u64 = 0;
            let mut hi: u64 = total_weight;
            while lo < hi {
                let mid = lo + (hi - lo) / 2;
                let relax = relax_vars.clone();
                let weights = soft_weights.clone();
                let probe = self.maxsmt_scoped_checked_decision(move |exec| {
                    exec.maxsmt_assert_weighted_at_most_w(&relax, &weights, mid);
                });
                match probe {
                    CheckedOptimizationDecision::Sat => hi = mid,
                    CheckedOptimizationDecision::Unsat => lo = mid + 1,
                    CheckedOptimizationDecision::Unknown => {
                        // Inconclusive probe (resource limit): report the base
                        // model's TRUE violated weight as an approximate
                        // (non-optimal) upper bound. Reporting `total_weight`
                        // here used to masquerade as the optimum — caught by
                        // the maxsmt soundness oracle under memory pressure.
                        let (_, model) = self.maxsmt_scoped_check_sat(|_| {})?;
                        let Some((cost, violated)) = self.maxsmt_violations(
                            &soft_terms,
                            &relax_vars,
                            &soft_weights,
                            model.as_ref(),
                        ) else {
                            return Ok(self.maxsmt_accounting_failure());
                        };
                        return Ok((SolveResult::Sat, model, cost, false, violated));
                    }
                }
            }
            let opt_w = lo;
            let relax = relax_vars.clone();
            let weights = soft_weights.clone();
            let (final_result, model) = self.maxsmt_scoped_check_sat(move |exec| {
                exec.maxsmt_assert_weighted_at_most_w(&relax, &weights, opt_w);
            })?;
            if !final_result.is_sat() {
                // opt_w was proven feasible; defensively fall back soundly.
                let (_, model) = self.maxsmt_scoped_check_sat(|_| {})?;
                let Some((cost, violated)) =
                    self.maxsmt_violations(&soft_terms, &relax_vars, &soft_weights, model.as_ref())
                else {
                    return Ok(self.maxsmt_accounting_failure());
                };
                return Ok((SolveResult::Sat, model, cost, false, violated));
            }
            #[allow(unused_mut)]
            let Some((mut violated_weight, violated_softs)) =
                self.maxsmt_violations(&soft_terms, &relax_vars, &soft_weights, model.as_ref())
            else {
                return Ok(self.maxsmt_accounting_failure());
            };
            #[cfg(test)]
            if let Some(forced) = self.forced_maxsmt_exact_cost.take() {
                violated_weight = forced;
            }
            if violated_weight != opt_w {
                // `opt_w` is the proven least feasible weighted bound. A model
                // whose independently recomputed cost disagrees is not an exact
                // witness; this check is production soundness policy, not a
                // debug-only assertion.
                return Ok(self.maxsmt_accounting_failure());
            }
            return Ok((
                SolveResult::Sat,
                model,
                violated_weight,
                true,
                violated_softs,
            ));
        }

        // === Count-then-weight fallback (total weight above the cap) ===
        // The weighted-at-most-W Boolean-copy encoding is intractable here, so we
        // minimize the violation COUNT and greedily repair weight. This is
        // WEIGHT-INCOMPLETE for non-uniform weights at very large total weight (a
        // known limitation pending a native pseudo-Boolean totalizer): the model
        // is always feasible (never under-reports), but the reported optimum may
        // exceed the true weighted optimum.
        //
        // Phase 1: binary search for the minimum violation count.
        // Invariant: at-most-`hi` violations is feasible; at-most-`lo-1` is not.
        let mut lo: usize = 0;
        let mut hi: usize = n;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let relax = relax_vars.clone();
            let probe = self.maxsmt_scoped_checked_decision(|exec| {
                exec.maxsmt_assert_at_most_k(&relax, mid);
            });
            match probe {
                CheckedOptimizationDecision::Sat => hi = mid,
                CheckedOptimizationDecision::Unsat => lo = mid + 1,
                CheckedOptimizationDecision::Unknown => {
                    // Inconclusive cardinality probe (resource limit): report
                    // the base model's true violated weight, marked approximate.
                    let (_, model) = self.maxsmt_scoped_check_sat(|_| {})?;
                    let Some((cost, violated)) = self.maxsmt_violations(
                        &soft_terms,
                        &relax_vars,
                        &soft_weights,
                        model.as_ref(),
                    ) else {
                        return Ok(self.maxsmt_accounting_failure());
                    };
                    return Ok((SolveResult::Sat, model, cost, false, violated));
                }
            }
        }
        let opt_k = lo;

        // Phase 2: weight-optimal solution at exactly `opt_k` violations. The
        // committed `not_relax` decisions and the at-most-`opt_k` constraint are
        // re-asserted together for each greedy probe (and the final solve), so
        // each greedy step decides feasibility against the already-committed
        // decisions without leaving state behind.
        let mut committed_not_relax: Vec<usize> = Vec::new();
        if opt_k > 0 {
            let mut sorted_by_weight: Vec<usize> = (0..n).collect();
            sorted_by_weight.sort_by_key(|&i| soft_weights[i]);
            for &i in sorted_by_weight.iter().rev() {
                let relax = relax_vars.clone();
                let committed = committed_not_relax.clone();
                let probe = self.maxsmt_scoped_checked_decision(move |exec| {
                    exec.maxsmt_assert_at_most_k(&relax, opt_k);
                    for &c in &committed {
                        let nr = exec.ctx.terms.mk_not(relax[c]);
                        exec.maxsmt_assert(nr);
                    }
                    let nr = exec.ctx.terms.mk_not(relax[i]);
                    exec.maxsmt_assert(nr);
                });
                if probe == CheckedOptimizationDecision::Sat {
                    committed_not_relax.push(i);
                }
            }
        }

        // Final solve with at-most-`opt_k` plus all committed not_relax decisions,
        // capturing the optimal model.
        let relax = relax_vars.clone();
        let committed = committed_not_relax.clone();
        let (final_result, model) = self.maxsmt_scoped_check_sat(move |exec| {
            exec.maxsmt_assert_at_most_k(&relax, opt_k);
            for &c in &committed {
                let nr = exec.ctx.terms.mk_not(relax[c]);
                exec.maxsmt_assert(nr);
            }
        })?;
        if !final_result.is_sat() {
            // Should not happen (opt_k was proven feasible); fall back soundly.
            let (_, model) = self.maxsmt_scoped_check_sat(|_| {})?;
            let Some((cost, violated)) =
                self.maxsmt_violations(&soft_terms, &relax_vars, &soft_weights, model.as_ref())
            else {
                return Ok(self.maxsmt_accounting_failure());
            };
            return Ok((SolveResult::Sat, model, cost, false, violated));
        }
        let Some((violated_weight, violated_softs)) =
            self.maxsmt_violations(&soft_terms, &relax_vars, &soft_weights, model.as_ref())
        else {
            return Ok(self.maxsmt_accounting_failure());
        };
        // Count-then-weight is weight-incomplete for non-uniform weights
        // (documented above): the count is proven minimal but the weight is
        // greedy, so never claim optimality in this regime.
        Ok((
            SolveResult::Sat,
            model,
            violated_weight,
            false,
            violated_softs,
        ))
    }

    /// Assert every committed group pin (a proven per-group optimum bound)
    /// inside a grouped-lex probe scope.
    fn maxsmt_assert_group_pins(&mut self, pins: &[(Vec<TermId>, Vec<u64>, u64)]) {
        for (terms, weights, bound) in pins {
            self.maxsmt_assert_weighted_at_most_w(terms, weights, *bound);
        }
    }

    /// Exact optimum of one group under the committed pins, by binary search
    /// on the group's violated-weight budget (feasibility is monotone in the
    /// budget with pins fixed). `None` when a probe is inconclusive.
    fn maxsmt_group_optimum(
        &mut self,
        pins: &[(Vec<TermId>, Vec<u64>, u64)],
        group_relax: &[TermId],
        group_weights: &[u64],
        group_total: u64,
    ) -> Option<u64> {
        let mut lo: u64 = 0;
        let mut hi: u64 = group_total;
        while lo < hi {
            let mid = lo + (hi - lo) / 2;
            let probe_pins = pins.to_vec();
            let probe_relax = group_relax.to_vec();
            let probe_weights = group_weights.to_vec();
            let probe = self.maxsmt_scoped_checked_decision(move |exec| {
                exec.maxsmt_assert_group_pins(&probe_pins);
                exec.maxsmt_assert_weighted_at_most_w(&probe_relax, &probe_weights, mid);
            });
            match probe {
                CheckedOptimizationDecision::Sat => hi = mid,
                CheckedOptimizationDecision::Unsat => lo = mid + 1,
                CheckedOptimizationDecision::Unknown => return None,
            }
        }
        Some(lo)
    }

    /// Grouped MaxSMT search: Z3 `:id` semantics under lexicographic priority.
    ///
    /// Groups optimize in first-appearance order. Each group's exact optimum
    /// is found with the same trusted weighted-at-most binary search the flat
    /// exact lane uses, then committed as a hard pin (`weighted-at-most-W*`
    /// over that group's relaxation indicators) inside every later probe, so
    /// later groups optimize subject to all earlier optima — exactly Z3's
    /// lexicographic combination of group objectives. The returned tuple has
    /// the flat engine's shape `(result, model, total_cost, optimal,
    /// violated)` where `total_cost` is the sum of the per-group optima, so
    /// the caller's final-witness accounting binds unchanged; per-group
    /// costs are re-derived from `violated` at publication.
    ///
    /// Exactness envelope: the TOTAL soft weight must fit the flat exact
    /// lane's cap ([`MAXSMT_EXACT_MAX_TOTAL_WEIGHT`]), because every probe
    /// re-asserts all pins and the copy encoding is sized by total weight.
    /// Above the cap there is no grouped approximate lane — the flat
    /// count-then-greedy fallback optimizes a different objective — so the
    /// search fails closed to `Unknown` instead.
    fn maxsmt_solve_grouped_lex(
        &mut self,
        softs: &[ay_frontend::SoftAssertion],
        groups: &[SoftGroup],
    ) -> Result<(SolveResult, Option<Model>, u64, bool, Vec<usize>)> {
        debug_assert!(
            groups.len() > 1,
            "grouped lex solver requires multiple groups"
        );
        let soft_terms: Vec<TermId> = softs.iter().map(|s| s.term).collect();
        let soft_weights: Vec<u64> = softs.iter().map(|s| s.weight).collect();
        let Some(total_weight) = soft_weights
            .iter()
            .try_fold(0u64, |sum, &weight| sum.checked_add(weight))
        else {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok((SolveResult::Unknown, None, 0, false, Vec::new()));
        };
        if total_weight > MAXSMT_EXACT_MAX_TOTAL_WEIGHT {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok((SolveResult::Unknown, None, 0, false, Vec::new()));
        }

        let relax_vars = self.maxsmt_build_relaxation(&soft_terms);

        // Base feasibility (all relaxations free): is the hard formula SAT?
        match self.maxsmt_scoped_checked_decision(|_| {}) {
            CheckedOptimizationDecision::Sat => {}
            CheckedOptimizationDecision::Unsat => {
                return Ok((SolveResult::unsat(), None, 0, true, Vec::new()));
            }
            CheckedOptimizationDecision::Unknown => {
                return Ok((SolveResult::Unknown, None, 0, false, Vec::new()));
            }
        }

        // Committed optima of earlier groups, re-asserted in every probe.
        let mut pins: Vec<(Vec<TermId>, Vec<u64>, u64)> = Vec::new();
        for group in groups {
            let group_relax: Vec<TermId> = group.indices.iter().map(|&i| relax_vars[i]).collect();
            let group_weights: Vec<u64> = group.indices.iter().map(|&i| soft_weights[i]).collect();
            let group_total: u64 = group_weights.iter().sum();
            let Some(optimum) =
                self.maxsmt_group_optimum(&pins, &group_relax, &group_weights, group_total)
            else {
                // Inconclusive probe (resource limit): report a feasible
                // model under the committed pins with its TRUE violated
                // weights, marked approximate — never a proven bound
                // masquerading as an optimum.
                let fallback_pins = pins.clone();
                let (_, model) = self.maxsmt_scoped_check_sat(move |exec| {
                    exec.maxsmt_assert_group_pins(&fallback_pins);
                })?;
                let Some((cost, violated)) =
                    self.maxsmt_violations(&soft_terms, &relax_vars, &soft_weights, model.as_ref())
                else {
                    return Ok(self.maxsmt_accounting_failure());
                };
                return Ok((SolveResult::Sat, model, cost, false, violated));
            };
            pins.push((group_relax, group_weights, optimum));
        }

        self.maxsmt_grouped_final_witness(&soft_terms, &soft_weights, &relax_vars, groups, &pins)
    }

    /// Final grouped solve under every committed pin, capturing the
    /// lex-optimal model and verifying it realizes EVERY group's proven
    /// optimum (not merely the summed total — two groups could trade
    /// violations and keep the sum while breaking lex order).
    fn maxsmt_grouped_final_witness(
        &mut self,
        soft_terms: &[TermId],
        soft_weights: &[u64],
        relax_vars: &[TermId],
        groups: &[SoftGroup],
        pins: &[(Vec<TermId>, Vec<u64>, u64)],
    ) -> Result<(SolveResult, Option<Model>, u64, bool, Vec<usize>)> {
        let final_pins = pins.to_vec();
        let (final_result, model) = self.maxsmt_scoped_check_sat(move |exec| {
            exec.maxsmt_assert_group_pins(&final_pins);
        })?;
        if !final_result.is_sat() {
            // Every pin bound was proven feasible in sequence; fall back
            // soundly to a feasible (approximate) witness.
            let (_, model) = self.maxsmt_scoped_check_sat(|_| {})?;
            let Some((cost, violated)) =
                self.maxsmt_violations(soft_terms, relax_vars, soft_weights, model.as_ref())
            else {
                return Ok(self.maxsmt_accounting_failure());
            };
            return Ok((SolveResult::Sat, model, cost, false, violated));
        }
        let Some((violated_weight, violated_softs)) =
            self.maxsmt_violations(soft_terms, relax_vars, soft_weights, model.as_ref())
        else {
            return Ok(self.maxsmt_accounting_failure());
        };
        let mut is_violated = vec![false; soft_terms.len()];
        for &index in &violated_softs {
            is_violated[index] = true;
        }
        for (group, (_, _, bound)) in groups.iter().zip(pins.iter()) {
            let group_cost: u64 = group
                .indices
                .iter()
                .filter(|&&i| is_violated[i])
                .map(|&i| soft_weights[i])
                .sum();
            if group_cost != *bound {
                return Ok(self.maxsmt_accounting_failure());
            }
        }
        Ok((
            SolveResult::Sat,
            model,
            violated_weight,
            true,
            violated_softs,
        ))
    }

    /// Grouped MaxSMT search under Z3's `box` priority: each `:id` group is
    /// optimized INDEPENDENTLY against the hard assertions alone, and the
    /// published witness is the FIRST group's optimum model (z3's box
    /// get-model behavior). Returns the flat outcome tuple (whose cost and
    /// violations describe that witness over ALL softs) plus the independent
    /// per-group optima for `(get-objectives)` — later groups' optima are
    /// generally NOT attained by the witness, exactly as in z3.
    ///
    /// Same exactness envelope as [`Self::maxsmt_solve_grouped_lex`]: total
    /// soft weight must fit the exact lane's cap, else fail closed.
    fn maxsmt_solve_grouped_box(
        &mut self,
        softs: &[ay_frontend::SoftAssertion],
        groups: &[SoftGroup],
    ) -> Result<(
        (SolveResult, Option<Model>, u64, bool, Vec<usize>),
        Vec<SoftGroupCost>,
    )> {
        debug_assert!(groups.len() > 1, "grouped box solver requires groups");
        let unknown = (
            (SolveResult::Unknown, None, 0, false, Vec::new()),
            Vec::new(),
        );
        let soft_terms: Vec<TermId> = softs.iter().map(|s| s.term).collect();
        let soft_weights: Vec<u64> = softs.iter().map(|s| s.weight).collect();
        let Some(total_weight) = soft_weights
            .iter()
            .try_fold(0u64, |sum, &weight| sum.checked_add(weight))
        else {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(unknown);
        };
        if total_weight > MAXSMT_EXACT_MAX_TOTAL_WEIGHT {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(unknown);
        }

        let relax_vars = self.maxsmt_build_relaxation(&soft_terms);
        match self.maxsmt_scoped_checked_decision(|_| {}) {
            CheckedOptimizationDecision::Sat => {}
            CheckedOptimizationDecision::Unsat => {
                return Ok((
                    (SolveResult::unsat(), None, 0, true, Vec::new()),
                    Vec::new(),
                ));
            }
            CheckedOptimizationDecision::Unknown => return Ok(unknown),
        }

        let mut group_costs = Vec::with_capacity(groups.len());
        let mut first_model: Option<Model> = None;
        for (group_index, group) in groups.iter().enumerate() {
            let group_relax: Vec<TermId> = group.indices.iter().map(|&i| relax_vars[i]).collect();
            let group_weights: Vec<u64> = group.indices.iter().map(|&i| soft_weights[i]).collect();
            let group_total: u64 = group_weights.iter().sum();
            // Independent: no pins from other groups, ever.
            let Some(optimum) =
                self.maxsmt_group_optimum(&[], &group_relax, &group_weights, group_total)
            else {
                return Ok(unknown);
            };
            group_costs.push(SoftGroupCost {
                id: group.id.clone(),
                cost: optimum,
                interval: false,
            });
            if group_index == 0 {
                let witness_relax = group_relax.clone();
                let witness_weights = group_weights.clone();
                let (result, model) = self.maxsmt_scoped_check_sat(move |exec| {
                    exec.maxsmt_assert_weighted_at_most_w(
                        &witness_relax,
                        &witness_weights,
                        optimum,
                    );
                })?;
                if !result.is_sat() {
                    return Ok((self.maxsmt_accounting_failure(), Vec::new()));
                }
                first_model = model;
            }
        }

        let Some((total_cost, violated)) = self.maxsmt_violations(
            &soft_terms,
            &relax_vars,
            &soft_weights,
            first_model.as_ref(),
        ) else {
            return Ok((self.maxsmt_accounting_failure(), Vec::new()));
        };
        // The witness must attain the FIRST group's proven optimum.
        let mut is_violated = vec![false; softs.len()];
        for &index in &violated {
            is_violated[index] = true;
        }
        let first_witnessed: u64 = groups[0]
            .indices
            .iter()
            .filter(|&&i| is_violated[i])
            .map(|&i| soft_weights[i])
            .sum();
        if first_witnessed != group_costs[0].cost {
            return Ok((self.maxsmt_accounting_failure(), Vec::new()));
        }
        Ok((
            (SolveResult::Sat, first_model, total_cost, true, violated),
            group_costs,
        ))
    }

    /// Opt-in, SOUNDNESS-FIRST core-guided MaxSMT engine (Phase 2 PR1).
    ///
    /// Returns `Ok(Some((result, model, violated_weight)))` when OLL is confident
    /// the reported optimum equals the binary-search baseline's, and `Ok(None)`
    /// to signal the caller to fall back to [`Self::maxsmt_solve`]. A wrong
    /// optimum is unacceptable, so every case where
    /// OLL cannot *prove* it matches the baseline falls back.
    ///
    /// ## What OLL covers vs. falls back on
    ///
    /// COVERED (returns `Some`): non-grouped, quantifier-free soft sets whose
    /// theory's assumption solver returns a genuine, non-degenerate weighted
    /// UNSAT core (Propositional / QF_UF and any other theory whose
    /// `check_sat_assuming` populates a non-empty assumption core that is a
    /// strict-progress subset of the assumptions). BOTH uniform AND non-uniform
    /// (weighted) soft weights are covered (Phase 2 PR2): the disjoint-core
    /// lower bound is computed in the WEIGHTED stratified style (raise `lb` by the
    /// minimum residual weight over each core, decrement residuals), and the exact
    /// optimum is confirmed against a TRUSTED weighted-at-most-`W` encoding built
    /// only from the same cardinality primitive the baseline trusts.
    ///
    /// FALLS BACK (returns `None`, baseline handles it): any quantified hard/soft
    /// term; a zero-weight soft (degenerate); a total soft
    /// weight above [`MAXSMT_EXACT_MAX_TOTAL_WEIGHT`] (the weighted confirmation
    /// replicates each soft's relax indicator `w_i` times, so an unbounded total
    /// weight would blow up the cardinality encoding); base-feasibility `unknown`;
    /// any `check_sat_assuming` returning `unknown`; an empty core (e.g. QF_BV
    /// always returns an empty assumption core, so QF_BV soft sets always fall
    /// back — that is expected); a degenerate / non-progressing core; or LB
    /// arithmetic overflow.
    ///
    /// ## Algorithm (weighted disjoint-core lower bound + weighted at-most-W confirmation)
    ///
    /// 1. Build the shared relaxation layer (`(or soft_i relax_i)` selectors).
    /// 2. Establish base feasibility (all relax free): hard-UNSAT ⇒ `Unsat`.
    /// 3. Extract DISJOINT weighted UNSAT cores. Maintain a per-soft RESIDUAL
    ///    weight (init = soft weight). Each round, assume `not relax_i` for every
    ///    soft with residual > 0. On UNSAT, read the core, let `wmin` be the
    ///    minimum residual over the core, raise `lb += wmin`, and subtract `wmin`
    ///    from each core member's residual. Softs whose residual hits 0 drop out of
    ///    future assumption sets. The cores are weight-disjoint, so `lb` is a SOUND
    ///    lower bound on the minimum total VIOLATED WEIGHT. (For uniform weights
    ///    every `wmin` is the common weight `w`, recovering PR1's count*w bound.)
    /// 4. Confirm/refine: search upward from `lb` for the least weight bound `W`
    ///    with `weighted-at-most-W` over ALL relax vars feasible. `lb` is a valid
    ///    lower bound, so the first feasible `W` is the EXACT minimum violated
    ///    weight; its model's `maxsmt_violations` accounting is the cost.
    ///
    /// ## Soundness of the weighted confirmation
    ///
    /// `weighted-at-most-W` (`sum_i w_i * relax_i <= W`) is encoded by
    /// [`Self::maxsmt_assert_weighted_at_most_w`] purely from the TRUSTED
    /// `maxsmt_assert_at_most_k` cardinality primitive: each soft `i` contributes
    /// `w_i` fresh Boolean copies, each pinned EQUAL to `relax_i` (`relax_i <=>
    /// copy`), and an `at-most-W` cardinality constraint is asserted over the flat
    /// list of copies. Pinning makes exactly `w_i` copies true iff `relax_i` is
    /// true, so the cardinality of true copies equals `sum_i w_i * relax_i`; hence
    /// `at-most-W` over the copies is EXACTLY `sum_i w_i * relax_i <= W`. No new
    /// (untrusted) pseudo-Boolean encoding is introduced. Because the bound is
    /// exact and `lb` is a valid lower bound, the least feasible `W` searched from
    /// `lb` upward equals the true minimum violated weight — there is no greedy
    /// step to reconcile, so OLL's reported optimum provably matches the baseline.
    pub(in crate::executor) fn maxsmt_solve_oll(
        &mut self,
        softs: &[ay_frontend::SoftAssertion],
    ) -> Result<Option<(SolveResult, Option<Model>, u64, bool, Vec<usize>)>> {
        #[cfg(test)]
        self.last_oll_core_rounds.set(0);

        let n = softs.len();
        debug_assert!(n > 0, "maxsmt_solve_oll called without soft constraints");

        // QF-GATE (REQUIRED). Quantified `check_sat_assuming` over-approximates the
        // UNSAT core to ALL assumptions (solve_quantified_assumptions), which would
        // make every core look maximal and break OLL's disjoint-core lower bound.
        // Fall back if ANY hard assertion or ANY soft term is quantified.
        if self
            .ctx
            .assertions
            .iter()
            .any(|&a| contains_quantifier(&self.ctx.terms, a))
            || softs
                .iter()
                .any(|s| contains_quantifier(&self.ctx.terms, s.term))
        {
            return Ok(None);
        }

        // Defense in depth for direct/internal callers. The public dispatcher
        // rejects grouped softs before choosing an engine because flattening
        // independent `:id` objectives would solve a different problem.
        if softs.iter().any(|s| s.id.is_some()) {
            return Ok(None);
        }

        // WEIGHT-GATE (PR2). OLL now covers non-uniform weights via the weighted
        // disjoint-core lower bound + trusted weighted-at-most-W confirmation
        // (see the doc comment's soundness argument). Two degenerate cases still
        // fall back so the trusted confirmation stays sound and bounded:
        //   * a zero-weight soft has no MaxSMT meaning and would let a violated
        //     soft contribute 0 to the bound (it can never enter a core's `wmin`);
        //   * a total soft weight above MAXSMT_EXACT_MAX_TOTAL_WEIGHT would make the
        //     weighted-at-most-W copy-replication encoding blow up.
        let soft_weights: Vec<u64> = softs.iter().map(|s| s.weight).collect();
        if soft_weights.contains(&0) {
            return Ok(None);
        }
        let total_weight: u64 = match soft_weights.iter().try_fold(0u64, |a, &w| a.checked_add(w)) {
            Some(v) => v,
            None => return Ok(None),
        };
        if total_weight > MAXSMT_EXACT_MAX_TOTAL_WEIGHT {
            return Ok(None);
        }

        let soft_terms: Vec<TermId> = softs.iter().map(|s| s.term).collect();

        // (1) Shared relaxation layer — IDENTICAL selectors to the baseline, so
        // the optima are directly comparable.
        let relax_vars = self.maxsmt_build_relaxation(&soft_terms);

        // (2) Base feasibility (all relaxations free): is the hard formula SAT?
        let base = self.maxsmt_scoped_checked_decision(|_| {});
        match base {
            CheckedOptimizationDecision::Sat => {}
            CheckedOptimizationDecision::Unsat => {
                return Ok(Some((SolveResult::unsat(), None, 0, true, Vec::new())));
            }
            CheckedOptimizationDecision::Unknown => return Ok(None),
        }

        // (3) Weighted disjoint-core lower bound. `residual[i]` is soft `i`'s
        // remaining weight (init = its weight); a soft drops out of the assumption
        // set once its residual hits 0. Each UNSAT core (a subset of the assumed
        // `not relax_i`) raises `lb` by the minimum residual over the core and
        // subtracts that `wmin` from every core member. Cores are weight-disjoint,
        // so `lb` is a SOUND lower bound on the minimum total violated weight.
        let mut residual: Vec<u64> = soft_weights.clone();
        let mut lb: u64 = 0;
        let mut core_rounds: u64 = 0;

        loop {
            // Assume every soft with positive residual satisfied.
            let mut assumptions: Vec<TermId> = Vec::new();
            let mut idx_of_assumption: HashMap<TermId, usize> = HashMap::default();
            for i in 0..n {
                if residual[i] > 0 {
                    let not_relax = self.ctx.terms.mk_not(relax_vars[i]);
                    assumptions.push(not_relax);
                    // Map the assumption literal back to its soft index. Distinct
                    // relax vars give distinct `not relax` terms, so this is 1:1.
                    idx_of_assumption.insert(not_relax, i);
                }
            }

            // All softs already spent by cores: lower bound established.
            if assumptions.is_empty() {
                break;
            }

            let exact_base_roots = self.ctx.assertions.clone();
            let mut exact_round_roots = exact_base_roots.clone();
            exact_round_roots.extend_from_slice(&assumptions);
            let probe = self.check_sat_assuming(&assumptions)?;
            match probe {
                SolveResult::Sat => {
                    if self.checked_optimization_roots_decision(&exact_round_roots)
                        != CheckedOptimizationDecision::Sat
                    {
                        return Ok(None);
                    }
                    // Every soft with positive residual can be satisfied
                    // simultaneously; the disjoint cores already found give the
                    // final lower bound.
                    break;
                }
                SolveResult::Unknown => return Ok(None),
                SolveResult::Unsat(_) => {
                    // Read the UNSAT core. Contract (debug-asserted in
                    // check_sat_assuming/assumption_solving): it is a SUBSET of the
                    // assumptions we passed.
                    #[allow(unused_mut)]
                    let Some(mut core) = self.last_assumption_core.clone() else {
                        // No core to reason about: cannot make sound progress.
                        return Ok(None);
                    };
                    #[cfg(test)]
                    if self.forced_maxsmt_oll_core_anomaly.replace(false) {
                        core.push(self.ctx.terms.true_term());
                    }
                    // Authenticate the ENTIRE returned core against this exact
                    // round's assumptions before using any member in a lower
                    // bound. Silently dropping an unknown literal could turn an
                    // invalid mixed core into a seemingly non-empty valid core
                    // and certify a false bound in release builds.
                    let mut core_indices: Vec<usize> = Vec::new();
                    for &c in &core {
                        let Some(&i) = idx_of_assumption.get(&c) else {
                            return Ok(None);
                        };
                        core_indices.push(i);
                    }
                    core_indices.sort_unstable();
                    core_indices.dedup();

                    // Degenerate cores ⇒ no sound progress. An EMPTY core, or any
                    // non-subset anomaly, means we cannot trust the disjoint-core
                    // bound, so we fall back rather than risk a wrong optimum. (A
                    // singleton core is fine: it forces that one soft relaxed.)
                    if core_indices.is_empty() {
                        return Ok(None);
                    }

                    // The failed-assumption harvest is only a candidate core.
                    // Membership proves where its literals came from, not that
                    // this proper subset is itself inconsistent with H + R.
                    // Re-prove that exact conjunction before it can raise the
                    // weighted lower bound.
                    let mut exact_core_roots = exact_base_roots;
                    exact_core_roots.extend_from_slice(&core);
                    if !self.checked_optimization_roots_unsat(&exact_core_roots) {
                        return Ok(None);
                    }

                    // Weighted stratum: `wmin` is the least residual over the core.
                    // Every core member has residual >= 1 (they were assumed), so
                    // `wmin >= 1` and the bound strictly progresses.
                    let wmin = core_indices
                        .iter()
                        .map(|&i| residual[i])
                        .min()
                        .expect("non-empty core");
                    debug_assert!(wmin >= 1, "core member residual must be positive");

                    // Subtract `wmin` from each core member's residual (saturating
                    // is exact here since wmin <= every member's residual), and
                    // raise the lower bound by exactly `wmin`.
                    for &i in &core_indices {
                        residual[i] = residual[i].saturating_sub(wmin);
                    }
                    lb = match lb.checked_add(wmin) {
                        Some(v) => v,
                        None => return Ok(None),
                    };
                    core_rounds += 1;
                    debug_assert!(
                        lb <= total_weight,
                        "OLL weighted lower bound {lb} exceeded total weight {total_weight}"
                    );
                }
            }
        }

        #[cfg(test)]
        self.last_oll_core_rounds.set(core_rounds);

        // If OLL found NO core, it made no core-guided progress and offers nothing
        // over the baseline; fall back so we never claim coverage we didn't earn.
        if core_rounds == 0 {
            return Ok(None);
        }

        // (4) Confirm/refine the exact optimum weight by searching upward from the
        // sound lower bound `lb`, using the TRUSTED weighted-at-most-W encoding
        // (cardinality over weight-replicated, relax-pinned copies — see doc
        // comment). `lb` is a valid lower bound, so the first feasible `W` is the
        // true minimum violated weight.
        let mut w_bound: u64 = lb;
        loop {
            debug_assert!(
                w_bound <= total_weight,
                "OLL confirmation W={w_bound} exceeded total weight {total_weight}"
            );
            let relax = relax_vars.clone();
            let weights = soft_weights.clone();
            let wb = w_bound;
            let (probe, model) = self.maxsmt_scoped_check_sat(move |exec| {
                exec.maxsmt_assert_weighted_at_most_w(&relax, &weights, wb);
            })?;
            match probe {
                SolveResult::Sat => {
                    let Some((cost, violated)) = self.maxsmt_violations(
                        &soft_terms,
                        &relax_vars,
                        &soft_weights,
                        model.as_ref(),
                    ) else {
                        return Ok(None);
                    };
                    // The model's checked accounting must equal the first
                    // feasible exact bound. Any lower value contradicts either
                    // the disjoint-core lower bound or the minimal-bound search;
                    // any higher value violates the encoded bound. Fall back in
                    // release builds instead of certifying inconsistent data.
                    if cost < lb || cost != w_bound {
                        return Ok(None);
                    }
                    return Ok(Some((SolveResult::Sat, model, cost, true, violated)));
                }
                SolveResult::Unsat(_) => {
                    // weighted-at-most-W infeasible ⇒ optimum weight > W. Tighten.
                    // Increment by 1: costs are integers, so the least feasible W
                    // is exactly the minimum achievable violated weight even if the
                    // optimum jumps over several intermediate W values.
                    w_bound = match w_bound.checked_add(1) {
                        Some(v) if v <= total_weight => v,
                        // Exhausted the weight range without feasibility, which
                        // contradicts base feasibility (all-relaxed costs
                        // total_weight); fall back defensively.
                        _ => return Ok(None),
                    };
                }
                SolveResult::Unknown => return Ok(None),
            }
        }
    }

    /// Decide a model-free MaxSMT feasibility obligation over the exact
    /// temporary assertion extension.
    fn maxsmt_scoped_checked_decision<F>(&mut self, add_clauses: F) -> CheckedOptimizationDecision
    where
        F: FnOnce(&mut Self),
    {
        let snapshot = self.ctx.assertions.len();
        add_clauses(self);
        #[cfg(test)]
        if maxsmt_test_hooks::decline_checked_decision() {
            self.ctx.truncate_assertions(snapshot);
            return CheckedOptimizationDecision::Unknown;
        }
        let decision = self.checked_optimization_decision(&[]);
        self.ctx.truncate_assertions(snapshot);
        decision
    }

    /// Run a MaxSMT probe over a temporary extension of the assertion stack.
    ///
    /// `add_clauses` appends the probe's temporary assertions (cardinality /
    /// `not_relax` decisions) onto `ctx.assertions`; after the solve the stack is
    /// truncated back, isolating the probe. The probe runs NON-incrementally
    /// (incremental state saved/cleared/restored) so each is a fresh, complete
    /// solve: the incremental theory solve is incomplete on this relaxed +
    /// cardinality encoding — notably it returns spurious `unknown` on a purely
    /// Boolean relaxed formula with no user hard constraints. A fresh
    /// non-incremental `check_sat()` over the exact current `ctx.assertions` is
    /// both sound and complete. Returns the result and the captured model.
    fn maxsmt_scoped_check_sat<F>(&mut self, add_clauses: F) -> Result<(SolveResult, Option<Model>)>
    where
        F: FnOnce(&mut Self),
    {
        let snapshot = self.ctx.assertions.len();
        add_clauses(self);
        // Capture before the raw same-context solve: preprocessing may replace
        // its working assertion window, while the bound transition must be
        // justified by the exact H + R + encoder roots built above.
        let exact_roots = self.ctx.assertions.clone();

        let saved_incr_mode = self.incremental_mode;
        let saved_incr_theory = self.incr_theory_state.take();
        let saved_incr_bv = self.incr_bv_state.take();
        self.incremental_mode = false;
        let result = self.check_sat();
        let model = self.last_model.clone();
        self.incremental_mode = saved_incr_mode;
        self.incr_theory_state = saved_incr_theory;
        self.incr_bv_state = saved_incr_bv;

        let result = match result {
            Ok(result) => result,
            Err(error) => {
                self.ctx.truncate_assertions(snapshot);
                return Err(error);
            }
        };
        let result = if result.is_unsat() && !self.checked_optimization_roots_unsat(&exact_roots) {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            SolveResult::Unknown
        } else {
            result
        };

        self.ctx.truncate_assertions(snapshot);
        Ok((result, model))
    }

    /// Total weight of soft constraints violated in `model`.
    ///
    /// SOUNDNESS (mirrors `Solver::find_violated_softs`): a soft is counted
    /// violated only when it is provably given up — its relaxation indicator is
    /// not `false` AND the soft term does not evaluate to `true`. A soft whose
    /// relax indicator is `false` (forced satisfied by the hard clause) or whose
    /// term evaluates to `true` is satisfied; an unevaluable soft term with an
    /// inactive relaxation is therefore correctly treated as satisfied.
    fn maxsmt_violations(
        &self,
        soft_terms: &[TermId],
        relax_vars: &[TermId],
        soft_weights: &[u64],
        model: Option<&Model>,
    ) -> Option<(u64, Vec<usize>)> {
        if soft_terms.len() != relax_vars.len() || soft_terms.len() != soft_weights.len() {
            return None;
        }
        let Some(model) = model else {
            // No model to inspect: be conservative and report the full weight.
            let weight = soft_weights
                .iter()
                .try_fold(0u64, |sum, &item| sum.checked_add(item))?;
            return Some((weight, (0..soft_terms.len()).collect()));
        };
        let mut violated = 0u64;
        let mut violated_softs = Vec::new();
        for i in 0..soft_terms.len() {
            // Provably satisfied: relaxation inactive => hard clause forces soft.
            if matches!(
                self.evaluate_term(model, relax_vars[i]),
                EvalValue::Bool(false)
            ) {
                continue;
            }
            // Provably satisfied: the soft term evaluates to true.
            if matches!(
                self.evaluate_term(model, soft_terms[i]),
                EvalValue::Bool(true)
            ) {
                continue;
            }
            violated = violated.checked_add(soft_weights[i])?;
            violated_softs.push(i);
        }
        Some((violated, violated_softs))
    }

    /// Produce a non-admitted outcome for impossible MaxSMT accounting state.
    fn maxsmt_accounting_failure(&mut self) -> (SolveResult, Option<Model>, u64, bool, Vec<usize>) {
        self.last_unknown_reason = Some(UnknownReason::InternalError);
        (SolveResult::Unknown, None, 0, false, Vec::new())
    }

    /// Assert an at-most-`k` cardinality constraint over Boolean `terms` by
    /// pushing clauses onto `ctx.assertions`. Pure Boolean encoding so it stays
    /// in the base logic. Mirrors `Solver::assert_at_most_k`.
    ///
    /// * `k >= n`: trivially satisfied (no clauses).
    /// * `k == 0`: each term must be false.
    /// * otherwise: direct (k+1)-subset encoding for small `n`/`k`, else a
    ///   sequential counter encoding with fresh counter variables.
    fn maxsmt_assert_at_most_k(&mut self, terms: &[TermId], k: usize) {
        let n = terms.len();
        if k >= n {
            return;
        }
        if k == 0 {
            for &t in terms {
                let not_t = self.ctx.terms.mk_not(t);
                self.maxsmt_assert(not_t);
            }
            return;
        }
        if n <= 10 || k == 1 {
            self.maxsmt_at_most_k_direct(terms, k);
        } else {
            self.maxsmt_at_most_k_sequential(terms, k);
        }
    }

    /// Assert the weighted cardinality constraint `sum_i weights[i] * terms[i] <= w`
    /// over Boolean `terms`, reusing ONLY the trusted [`Self::maxsmt_assert_at_most_k`]
    /// primitive (no new pseudo-Boolean encoding).
    ///
    /// SOUNDNESS: for each `i`, `weights[i]` fresh Boolean copies are created and
    /// each pinned EQUAL to `terms[i]` via the two clauses `(terms[i] => copy)` and
    /// `(copy => terms[i])`. Then `at-most-w` is asserted over the flat list of all
    /// copies. Pinning forces exactly `weights[i]` copies true iff `terms[i]` is
    /// true, so the number of true copies equals `sum_i weights[i] * terms[i]`;
    /// hence `at-most-w` over the copies is EXACTLY the weighted bound. The encoding
    /// is therefore as trusted as the unweighted cardinality primitive it is built
    /// from. `terms` and `weights` must be the same length; a `weights[i] == 0`
    /// contributes no copies (the term is unconstrained by the weighted bound,
    /// matching its zero coefficient).
    fn maxsmt_assert_weighted_at_most_w(&mut self, terms: &[TermId], weights: &[u64], w: u64) {
        if terms.len() != weights.len() {
            let contradiction = self.ctx.terms.false_term();
            self.maxsmt_assert(contradiction);
            return;
        }
        // Total true copies is bounded by the total weight; if W already covers it,
        // the constraint is trivially satisfied and we add nothing.
        let Some(total) = weights
            .iter()
            .try_fold(0u64, |sum, &weight| sum.checked_add(weight))
        else {
            // Fail closed if an internal caller bypasses the total-weight gate.
            let contradiction = self.ctx.terms.false_term();
            self.maxsmt_assert(contradiction);
            return;
        };
        if w >= total {
            return;
        }
        // `w < total <= MAXSMT_EXACT_MAX_TOTAL_WEIGHT` (gated by the caller), so the
        // copy count fits comfortably in `usize` on all supported targets.
        let mut copies: Vec<TermId> = Vec::with_capacity(total as usize);
        for (i, &t) in terms.iter().enumerate() {
            for j in 0..weights[i] {
                let name = format!("__ay_soft_wcopy_{i}_{j}");
                let copy = self.ctx.terms.mk_fresh_named_var(name.clone(), Sort::Bool);
                self.ctx.register_symbol(name, copy, Sort::Bool);
                // Pin copy <=> t: (not t or copy) and (not copy or t).
                let not_t = self.ctx.terms.mk_not(t);
                let fwd = self.ctx.terms.mk_or(vec![not_t, copy]);
                self.maxsmt_assert(fwd);
                let not_copy = self.ctx.terms.mk_not(copy);
                let back = self.ctx.terms.mk_or(vec![not_copy, t]);
                self.maxsmt_assert(back);
                copies.push(copy);
            }
        }
        // `w < total = copies.len()`, so `w` is a meaningful at-most bound.
        self.maxsmt_assert_at_most_k(&copies, w as usize);
    }

    /// Direct at-most-`k`: for each (k+1)-subset assert at least one is false.
    fn maxsmt_at_most_k_direct(&mut self, terms: &[TermId], k: usize) {
        let n = terms.len();
        let r = k + 1;
        if r > n {
            return;
        }
        let mut indices: Vec<usize> = (0..r).collect();
        loop {
            let mut clause = self.ctx.terms.mk_not(terms[indices[0]]);
            for &idx in &indices[1..] {
                let not_t = self.ctx.terms.mk_not(terms[idx]);
                clause = self.ctx.terms.mk_or(vec![clause, not_t]);
            }
            self.maxsmt_assert(clause);

            let Some(pos) = (0..r).rev().find(|&i| indices[i] != i + n - r) else {
                break;
            };
            indices[pos] += 1;
            for j in (pos + 1)..r {
                indices[j] = indices[j - 1] + 1;
            }
        }
    }

    /// Sequential-counter at-most-`k` with fresh counter variables.
    /// Mirrors `Solver::assert_at_most_k_sequential`.
    fn maxsmt_at_most_k_sequential(&mut self, terms: &[TermId], k: usize) {
        let n = terms.len();
        let mut r: Vec<Vec<TermId>> = Vec::with_capacity(n);
        for i in 0..n {
            let mut row = Vec::with_capacity(k);
            for j in 0..k {
                let name = format!("__ay_soft_card_{i}_{j}");
                let aux = self.ctx.terms.mk_fresh_named_var(name.clone(), Sort::Bool);
                self.ctx.register_symbol(name, aux, Sort::Bool);
                row.push(aux);
            }
            r.push(row);
        }

        // Base: r[0][0] <=> terms[0].
        let not_t0 = self.ctx.terms.mk_not(terms[0]);
        let c1 = self.ctx.terms.mk_or(vec![not_t0, r[0][0]]);
        self.maxsmt_assert(c1);
        let not_r00 = self.ctx.terms.mk_not(r[0][0]);
        let c2 = self.ctx.terms.mk_or(vec![not_r00, terms[0]]);
        self.maxsmt_assert(c2);
        for &aux in r[0].iter().take(k).skip(1) {
            let not_r0j = self.ctx.terms.mk_not(aux);
            self.maxsmt_assert(not_r0j);
        }

        for i in 1..n {
            let not_ti = self.ctx.terms.mk_not(terms[i]);

            let not_rprev0 = self.ctx.terms.mk_not(r[i - 1][0]);
            let c_rprev = self.ctx.terms.mk_or(vec![not_rprev0, r[i][0]]);
            self.maxsmt_assert(c_rprev);

            let c_ti = self.ctx.terms.mk_or(vec![not_ti, r[i][0]]);
            self.maxsmt_assert(c_ti);

            let not_ri0 = self.ctx.terms.mk_not(r[i][0]);
            let or_prev = self.ctx.terms.mk_or(vec![r[i - 1][0], terms[i]]);
            let c_back = self.ctx.terms.mk_or(vec![not_ri0, or_prev]);
            self.maxsmt_assert(c_back);

            for j in 1..k {
                let not_rprevj = self.ctx.terms.mk_not(r[i - 1][j]);
                let not_rprev_jm1 = self.ctx.terms.mk_not(r[i - 1][j - 1]);
                let not_rij = self.ctx.terms.mk_not(r[i][j]);

                let d1 = self.ctx.terms.mk_or(vec![not_rprevj, r[i][j]]);
                self.maxsmt_assert(d1);

                let d2a = self.ctx.terms.mk_or(vec![not_ti, not_rprev_jm1]);
                let d2 = self.ctx.terms.mk_or(vec![d2a, r[i][j]]);
                self.maxsmt_assert(d2);

                let d3a = self.ctx.terms.mk_or(vec![r[i - 1][j], terms[i]]);
                let d3 = self.ctx.terms.mk_or(vec![not_rij, d3a]);
                self.maxsmt_assert(d3);

                let d4a = self.ctx.terms.mk_or(vec![r[i - 1][j], r[i - 1][j - 1]]);
                let d4 = self.ctx.terms.mk_or(vec![not_rij, d4a]);
                self.maxsmt_assert(d4);
            }

            let not_rprev_km1 = self.ctx.terms.mk_not(r[i - 1][k - 1]);
            let block = self.ctx.terms.mk_or(vec![not_ti, not_rprev_km1]);
            self.maxsmt_assert(block);
        }
    }

    /// Run optimization if objectives are set, otherwise delegate to check_sat_internal.
    ///
    /// Supports all three Z3-compatible multi-objective priorities, selected by
    /// `(set-option :opt.priority ...)`:
    ///
    /// * `lex` (LEXICOGRAPHIC, default, #4128 Phase 2): objectives are optimized
    ///   in declaration order. After finding the optimal value for objective i,
    ///   that value is committed as a hard constraint before optimizing
    ///   objective i+1.
    /// * `box` (independent / "boxed"): each objective is optimized INDEPENDENTLY
    ///   against the HARD constraints alone — objective i's optimum ignores the
    ///   other objectives entirely (no cross-objective commitment). Each box
    ///   optimum equals what you would get optimizing ONLY that objective with the
    ///   same hard constraints.
    /// * `pareto` (Pareto-front enumeration via the Guided Improvement Algorithm —
    ///   see [`Self::optimize_pareto`]): STATEFUL, one Pareto-optimal point per
    ///   `(check-sat)`, terminal `unsat` on exhaustion, cyclic restart afterward
    ///   (Z3-compatible). Supported for Int/BitVec objectives (finite front); a
    ///   Real objective warns once and falls back to `lex` for soundness.
    ///
    /// Any other unknown priority value is warned and treated as `lex`.
    pub(in crate::executor) fn optimize_check_sat(&mut self) -> Result<SolveResult> {
        self.last_sat_certificate = None;
        // Optimization enters through `check_sat_internal` rather than the
        // ordinary guarded boundary. Scan both hard assertions and objective
        // DAGs here so a native oversized BV objective cannot reach model
        // construction or the finite-domain binary search.
        let solve_roots = self.public_solve_roots(&[]);
        if contains_symbolic_integer_power(&self.ctx.terms, &solve_roots) {
            self.last_model = None;
            self.record_unknown_from_origin(UnknownOrigin::UnsupportedArithmeticFragment);
            self.record_unknown_diagnostic(
                UnknownReason::UnsupportedArithmetic,
                "exponentiation with a symbolic exponent (or a native `^` exponent that is not a positive integer literal) is accepted and typed but has no sound decision procedure",
            );
            return Ok(SolveResult::Unknown);
        }
        if let Some(result) = self.reject_array_ext_witness_capture(&solve_roots) {
            return Ok(result);
        }
        if let Some(result) = self.reject_unsupported_bitvector_width(&solve_roots) {
            return Ok(result);
        }
        if let Some(result) = self.reject_unsupported_fp_model_format(&solve_roots) {
            return Ok(result);
        }
        // Install the executor-level `set_timeout` deadline for the whole
        // optimization run, mirroring `check_sat()`. This path previously
        // bypassed `install_timeout_deadline_for_call` (it enters through
        // `check_sat_internal` directly), so `(set-timeout)`-style API
        // timeouts were silently ignored for objective solves and
        // deadline-aware theory probes (e.g. the IntSat fixpoint) ran
        // unbounded inside the blocking-constraint loop.
        let previous_deadline = self.install_timeout_deadline_for_call();
        let mut result = self.optimize_check_sat_inner();
        self.restore_timeout_deadline_after_call(previous_deadline);
        if result.is_err() {
            // Any objective lane can fail after successful assumption probes.
            // Those probes may leave a model, SAT token, or partial optimum;
            // an errored PUBLIC optimization query admits none of them.
            self.invalidate_last_check_result();
        }
        result = result.map(|solve_result| {
            // `None`: as in `check_sat_assuming`, an optimization query's
            // verdict rests on soft constraints and objectives too, which are
            // not entailed by the hard assertions. No residue rescue here.
            self.quarantine_unverified_nested_array_unsat(&solve_roots, None, solve_result)
        });
        result
    }

    /// Structured optimum of objective `objective_index` after the last
    /// `optimize_check_sat`.
    ///
    /// This is the structured counterpart of one `(get-objectives)` line. Its
    /// resolution order is IDENTICAL to [`Self::get_objectives`] so the data and
    /// the printed form can never disagree:
    /// 1. If `objective_index` follows an unbounded or unattained
    ///    (infinitesimal) lexicographic predecessor, return `Unavailable`
    ///    (AY has no interval-valued outcome).
    /// 2. If `objective_index` is in `unbounded_objectives`, return `PosInfinity`
    ///    (maximize) / `NegInfinity` (minimize).
    /// 3. If it is in `infinitesimal_objectives`, return `Epsilon` — the
    ///    unattained sup/inf plus its ε-coefficient (#opt-epsilon).
    /// 4. Else if an admitted finite outcome was recorded for it, return that
    ///    value. Lex/Pareto values were re-accounted against the final model;
    ///    BOX values are independently authenticated and deliberately have no
    ///    joint witness model.
    ///
    /// Returns [`ObjectiveOutcome::Unavailable`] if the last solve was not SAT or
    /// the objective could not be evaluated to a number.
    pub(crate) fn objective_optimum(&self, objective_index: usize) -> ObjectiveOutcome {
        if self.ctx.objectives().get(objective_index).is_none()
            || !matches!(self.last_result, Some(SolveResult::Sat))
        {
            return ObjectiveOutcome::Unavailable;
        }

        if self.unavailable_objectives.contains(&objective_index) {
            return ObjectiveOutcome::Unavailable;
        }

        // Unbounded objective: report infinity per SMT-LIB OMT (matches the
        // `oo` / `(- oo)` strings get-objectives emits).
        match self.unbounded_objectives.get(&objective_index) {
            Some(ObjectiveDirection::Maximize) => return ObjectiveOutcome::PosInfinity,
            Some(ObjectiveDirection::Minimize) => return ObjectiveOutcome::NegInfinity,
            None => {}
        }

        // Unattained (infinitesimal) optimum: the structured analogue of the
        // `(get-objectives)` epsilon shapes (#opt-epsilon). Checked before the
        // finite map, exactly like the renderer.
        if let Some((value, eps_coeff)) = self.infinitesimal_objectives.get(&objective_index) {
            return ObjectiveOutcome::Epsilon {
                value: value.clone(),
                eps_coeff: eps_coeff.clone(),
            };
        }

        // Every finite public outcome is explicitly recorded only after an
        // optimization query is admitted. Never fall back to evaluating an
        // arbitrary SAT model: native `check_sat()` is a feasibility query even
        // when objectives have been registered, and its model is not an optimum.
        if let Some(value) = self.finite_objective_values.get(&objective_index) {
            return ObjectiveOutcome::Finite(value.clone());
        }
        ObjectiveOutcome::Unavailable
    }

    fn optimize_check_sat_inner(&mut self) -> Result<SolveResult> {
        if self.ctx.objectives().is_empty() {
            return self.check_sat_internal();
        }

        // Fresh optimization: forget any unbounded/infinitesimal objectives,
        // indexed finite outcomes, and optimality certificates from a prior run.
        self.unbounded_objectives.clear();
        self.infinitesimal_objectives.clear();
        self.unavailable_objectives.clear();
        self.finite_objective_values.clear();
        self.objective_certificates.clear();

        let objectives = self.ctx.objectives().to_vec();
        for obj in &objectives {
            let obj_sort = self.ctx.terms.sort(obj.term).clone();
            // Int/Real use exp+binary / simplex search; BitVec uses a finite
            // unsigned-range binary search (see `optimize_bv_objective`). Any
            // other sort has no optimization order AY supports.
            if !matches!(obj_sort, Sort::Int | Sort::Real | Sort::BitVec(_)) {
                return Err(ExecutorError::UnsupportedOptimization(format!(
                    "unsupported objective sort: {obj_sort:?}"
                )));
            }
        }

        // #8694: Detect unbounded optimization variables and warn.
        // Z3 silently returns arbitrary values when optimization variables
        // are unbounded. AY detects this and warns the user. BitVector
        // objectives have a FINITE domain (always bounded), so they are never
        // "unbounded" and are skipped inside `warn_unbounded_objectives`.
        self.warn_unbounded_objectives(&objectives);

        // Soft constraints present: the joint engine owns base feasibility
        // (its relaxation must be in place first) and the whole search.
        if !self.ctx.soft_constraints().is_empty() {
            return match self.opt_priority() {
                OptPriority::Box => self.joint_optimize_box(&objectives),
                OptPriority::Pareto => self.joint_optimize_pareto(&objectives),
                OptPriority::Lex => self.joint_optimize_lex(&objectives),
            };
        }

        let base_result = self.check_sat_internal()?;
        if base_result != SolveResult::Sat {
            // Hard constraints alone are UNSAT/unknown: no Pareto front exists.
            // Drop any stale pareto enumeration so a later sat problem restarts
            // cleanly (assertion edits already reset it, but a bare re-check of an
            // unsat problem should not leave a half-front behind).
            self.pareto_state = None;
            return Ok(base_result);
        }

        // Route by `(set-option :opt.priority ...)`. Box and lex share the EXACT
        // same per-objective solver ([`Self::optimize_one_objective`]); the only
        // difference is whether each objective's optimum is committed as a hard
        // constraint before the next objective (lex) or not (box). Pareto is
        // STATEFUL: it emits one Pareto-optimal point per `(check-sat)`.
        let priority = self.opt_priority();
        // Pareto uses a certified seed's closed weak-dominance cone, including
        // Real and infinite Int fronts. Each call emits at most one point.
        match priority {
            OptPriority::Box => self.optimize_box(&objectives),
            OptPriority::Lex => self.optimize_lex(&objectives),
            OptPriority::Pareto => self.optimize_pareto(&objectives),
        }
    }

    /// Read the `opt.priority` option (Z3-compatible). Defaults to `lex`.
    ///
    /// `lex`, `box`, and `pareto` are all supported. Any other unrecognized value
    /// is reported honestly: a single warning is emitted and the priority falls
    /// back to `lex`.
    fn opt_priority(&self) -> OptPriority {
        match self.ctx.get_option("opt.priority") {
            Some(ay_frontend::OptionValue::String(s)) => match s.as_str() {
                "box" => OptPriority::Box,
                "lex" => OptPriority::Lex,
                "pareto" => OptPriority::Pareto,
                other => {
                    safe_eprintln!(
                        "Warning: unknown opt.priority='{other}' (expected 'lex', 'box', or \
                         'pareto'); falling back to lexicographic."
                    );
                    OptPriority::Lex
                }
            },
            _ => OptPriority::Lex,
        }
    }

    /// Lexicographic multi-objective optimization (#4128 Phase 2).
    ///
    /// Optimizes each objective in declaration order, committing each finite
    /// optimum as a hard constraint before the next objective so later
    /// objectives respect the earlier optima. An unbounded objective terminates
    /// the lex search: there is no attainable infinity to commit, so every later
    /// scalar outcome is recorded unavailable (Z3 uses an interval there).
    /// Caller guarantees the hard constraints are SAT.
    fn optimize_lex(&mut self, objectives: &[ay_frontend::Objective]) -> Result<SolveResult> {
        match self.optimize_lex_search(objectives) {
            Ok(Some(finite_values)) => {
                // Certify the captured optimum witness against the restored USER
                // formula, not against the transient lex commits. Exact value
                // roots bind every attainable finite prefix outcome to the
                // final consumer-visible model.
                self.finalize_optimization(&finite_values, true)
            }
            Ok(None) => Ok(self.optimization_inconclusive()),
            Err(error) => {
                // An internal probe may have minted a certificate before a later
                // objective errored. No partial witness/objective is public.
                self.invalidate_last_check_result();
                Err(error)
            }
        }
    }

    /// The lex search half of [`Self::optimize_lex`] WITHOUT final
    /// publication: runs the commit-as-you-go optimization over
    /// `objectives` transactionally and returns the attained finite
    /// values (keyed by position in `objectives`), leaving the witness
    /// in `last_model`. The joint Pareto lane pushes with this over its
    /// extended objective vector (whose indices are not `ctx` objective
    /// indices) and publishes through the joint finalizer instead.
    fn optimize_lex_search(
        &mut self,
        objectives: &[ay_frontend::Objective],
    ) -> Result<Option<Vec<(usize, BigRational)>>> {
        // Earlier-objective optimum commits constrain only this lexicographic
        // search. They are NOT user assertions: leaking one into the persistent
        // stack makes a later check solve a strictly stronger problem (for
        // example, maximize x to 10, then assert x=0 => false UNSAT). Keep the
        // whole search transactional, including errors and inconclusive probes.
        let assertion_snapshot = self.ctx.assertions.len();
        let mut finite_values = Vec::with_capacity(objectives.len());
        let search = (|| -> Result<bool> {
            for (objective_index, obj) in objectives.iter().enumerate() {
                let obj_sort = self.ctx.terms.sort(obj.term).clone();
                match self.optimize_one_objective(objective_index, obj)? {
                    Some((model, value)) => {
                        self.last_model = Some(model);
                        // An unbounded lexicographic objective has no attainable
                        // value to commit. Consequently no later declaration has
                        // a scalar lex optimum: it would need to optimize inside
                        // the empty set of models attaining +/-infinity. Z3
                        // exposes an interval for that suffix; AY has no interval
                        // result type, so preserve the proven prefix and mark the
                        // entire suffix unavailable rather than optimizing it as
                        // an independent problem and publishing a false scalar.
                        if self.unbounded_objectives.contains_key(&objective_index) {
                            self.unavailable_objectives
                                .extend((objective_index + 1)..objectives.len());
                            return Ok(true);
                        }
                        // An UNATTAINED (infinitesimal) optimum likewise has no
                        // attainable value to commit: committing `obj >= sup`
                        // would make the remaining search infeasible, and
                        // optimizing the suffix un-committed would publish
                        // scalars for a different problem (z3 emits an interval
                        // + a demonstrably false successor scalar here — AY
                        // deliberately deviates, #opt-epsilon). Preserve the
                        // proven prefix, mark the suffix unavailable, stop. In
                        // final position the suffix range is empty and the lex
                        // search simply ends (z3-parity: earlier attained
                        // values stay normal, the final one prints ε-form).
                        if self.infinitesimal_objectives.contains_key(&objective_index) {
                            self.unavailable_objectives
                                .extend((objective_index + 1)..objectives.len());
                            return Ok(true);
                        }
                        finite_values.push((objective_index, value.clone()));
                        // Commit this objective's optimal value as a TEMPORARY hard
                        // constraint so subsequent objectives optimize under it.
                        if objectives.len() > 1 {
                            let commit = match obj.direction {
                                ObjectiveDirection::Maximize => {
                                    self.mk_commit_ge(obj.term, &value, &obj_sort)
                                }
                                ObjectiveDirection::Minimize => {
                                    self.mk_commit_le(obj.term, &value, &obj_sort)
                                }
                            };
                            self.optimization_assert(commit);
                        }
                    }
                    None => return Ok(false),
                }
            }
            Ok(true)
        })();
        self.ctx.truncate_assertions(assertion_snapshot);

        match search {
            Ok(true) => Ok(Some(finite_values)),
            Ok(false) => Ok(None),
            Err(error) => Err(error),
        }
    }

    /// Joint lexicographic optimization over arithmetic objectives AND soft
    /// groups in unified declaration order (Z3's single objective list).
    ///
    /// One transactional window: the soft relaxation is asserted once, then
    /// each step in `objective_sequence` is optimized with all earlier
    /// steps' optima committed — arithmetic optima as bound commits (as in
    /// [`Self::optimize_lex`]), soft-group optima as weighted-at-most pins
    /// over the group's relaxation indicators (as in
    /// [`Self::maxsmt_solve_grouped_lex`]). An unbounded or unattained
    /// arithmetic step ends the search like pure lex: later arithmetic
    /// objectives are unavailable and later soft groups render as
    /// `(interval 0 total)`, matching z3. Only the lex priority is joint for
    /// now; box/pareto and above-cap total soft weight fail closed to
    /// `unknown`. Caller guarantees objectives are sort-valid.
    fn joint_optimize_lex(&mut self, objectives: &[ay_frontend::Objective]) -> Result<SolveResult> {
        self.joint_optimize(objectives, OptPriority::Lex)
    }

    fn joint_optimize_box(&mut self, objectives: &[ay_frontend::Objective]) -> Result<SolveResult> {
        self.joint_optimize(objectives, OptPriority::Box)
    }

    /// Relaxation vars and their `(or soft relax)` clause terms for the
    /// joint Pareto search, created WITHOUT asserting and WITHOUT symbol
    /// registration: the exhaustion extension must be built while
    /// `ctx.assertions` is still exactly the authored set, and registering
    /// a symbol mid-call would advance the source revision and stale the
    /// public query epoch the terminal declaration authenticates against
    /// (the vars are referenced by TermId everywhere in this lane).
    fn pareto_relaxation_terms(&mut self, soft_terms: &[TermId]) -> (Vec<TermId>, Vec<TermId>) {
        let mut relax_vars = Vec::with_capacity(soft_terms.len());
        let mut clauses = Vec::with_capacity(soft_terms.len());
        for (i, &soft_term) in soft_terms.iter().enumerate() {
            let relax = self
                .ctx
                .terms
                .mk_fresh_named_var(format!("__ay_soft_relax_{i}"), Sort::Bool);
            relax_vars.push(relax);
            clauses.push(self.ctx.terms.mk_or(vec![soft_term, relax]));
        }
        (relax_vars, clauses)
    }

    /// The Int term `Σ (ite relax_i w_i 0)` — group `group`'s violated
    /// weight as an objective term for the shared Pareto enumerator.
    fn pareto_group_cost_term(
        &mut self,
        group: &SoftGroup,
        relax_vars: &[TermId],
        soft_weights: &[u64],
    ) -> TermId {
        let mut parts = Vec::with_capacity(group.indices.len());
        for &i in &group.indices {
            let weight = self.ctx.terms.mk_int(BigInt::from(soft_weights[i]));
            let zero = self.ctx.terms.mk_int(BigInt::zero());
            parts.push(self.ctx.terms.mk_ite(relax_vars[i], weight, zero));
        }
        match parts.len() {
            1 => parts[0],
            _ => self.ctx.terms.mk_app(Symbol::named("+"), parts, Sort::Int),
        }
    }

    /// Joint soft + arithmetic Pareto enumeration (Z3's stateful front
    /// protocol over the unified declaration order): each soft group
    /// contributes one synthesized minimize objective (its weighted
    /// violation sum over the relaxation), and the enumerator mirrors
    /// [`Self::optimize_pareto`]'s GIA (seed probe under blockers, lex
    /// push, emit) with joint publication and the same certified seed cone.
    fn joint_optimize_pareto(
        &mut self,
        objectives: &[ay_frontend::Objective],
    ) -> Result<SolveResult> {
        let softs: Vec<ay_frontend::SoftAssertion> = self.ctx.soft_constraints().to_vec();
        let groups = partition_soft_groups(&softs);
        let sequence: Vec<ay_frontend::ObjectiveStep> = self.ctx.objective_sequence().to_vec();
        let soft_weights: Vec<u64> = softs.iter().map(|s| s.weight).collect();
        if !self.joint_pareto_consistent(objectives, &groups, &sequence, &soft_weights) {
            return Ok(self.optimization_inconclusive());
        }
        // Single unified objective never reaches here (routing sends it
        // to the flat/lex lanes, matching z3's degeneration); guard
        // anyway so a stray call cannot engage the enumerator.
        if sequence.len() <= 1 {
            return Ok(self.optimization_inconclusive());
        }

        let soft_terms: Vec<TermId> = softs.iter().map(|s| s.term).collect();
        let (relax_vars, relax_clauses) = self.pareto_relaxation_terms(&soft_terms);
        let Some((extended, step_map)) = self.joint_pareto_extended_objectives(
            objectives,
            &groups,
            &sequence,
            &relax_vars,
            &soft_weights,
        ) else {
            return Ok(self.optimization_inconclusive());
        };
        let frame = JointParetoFrame {
            sealed_objectives: objectives,
            sequence: &sequence,
            extended: &extended,
            step_map: &step_map,
            softs: &softs,
            groups: &groups,
            soft_terms: &soft_terms,
            soft_weights: &soft_weights,
            relax_vars: &relax_vars,
            relax_clauses: &relax_clauses,
        };

        let mut state = self.pareto_state.take().unwrap_or_default();
        if state
            .emitted
            .iter()
            .any(|point| point.len() != extended.len())
        {
            // The objective inventory changed mid-enumeration; restart
            // rather than misalign points.
            state = ParetoState::default();
        }
        let base_assertion_count = self.ctx.assertions.len();
        let outcome = self.joint_pareto_search(&frame, &mut state);
        self.ctx.truncate_assertions(base_assertion_count);
        match outcome {
            Ok(Some(JointParetoCaptured::Sat(captured))) => {
                let (finite_values, soft_roots, soft_publication) = *captured;
                let witness_values = finite_values.clone();
                self.finalize_joint_optimization(
                    &finite_values,
                    &soft_roots,
                    &soft_publication,
                    &witness_values,
                )
            }
            Ok(Some(JointParetoCaptured::Verdict(verdict))) => Ok(verdict),
            Ok(None) => Ok(self.optimization_inconclusive()),
            Err(error) => {
                self.invalidate_last_check_result();
                Err(error)
            }
        }
    }

    /// The extended objective vector in declaration order (real
    /// objectives interleaved with one synthesized group-cost minimize
    /// objective per soft group) plus the per-position map back.
    fn joint_pareto_extended_objectives(
        &mut self,
        objectives: &[ay_frontend::Objective],
        groups: &[SoftGroup],
        sequence: &[ay_frontend::ObjectiveStep],
        relax_vars: &[TermId],
        soft_weights: &[u64],
    ) -> Option<(Vec<ay_frontend::Objective>, Vec<ParetoStepKind>)> {
        let mut extended = Vec::with_capacity(sequence.len());
        let mut step_map = Vec::with_capacity(sequence.len());
        for step in sequence {
            match step {
                ay_frontend::ObjectiveStep::Arithmetic(index) => {
                    extended.push(objectives[*index].clone());
                    step_map.push(ParetoStepKind::Arithmetic(*index));
                }
                ay_frontend::ObjectiveStep::SoftGroup(id) => {
                    let group_index = groups.iter().position(|group| &group.id == id)?;
                    let cost =
                        self.pareto_group_cost_term(&groups[group_index], relax_vars, soft_weights);
                    extended.push(ay_frontend::Objective {
                        direction: ObjectiveDirection::Minimize,
                        term: cost,
                    });
                    step_map.push(ParetoStepKind::Group(group_index));
                }
            }
        }
        Some((extended, step_map))
    }

    /// The joint Pareto gates shared with the lex/box engines: the
    /// declared sequence must exactly recount the live objectives and
    /// soft groups, and the total soft weight must fit the exact lane.
    fn joint_pareto_consistent(
        &self,
        objectives: &[ay_frontend::Objective],
        groups: &[SoftGroup],
        sequence: &[ay_frontend::ObjectiveStep],
        soft_weights: &[u64],
    ) -> bool {
        let arith_steps: Vec<usize> = sequence
            .iter()
            .filter_map(|step| match step {
                ay_frontend::ObjectiveStep::Arithmetic(index) => Some(*index),
                ay_frontend::ObjectiveStep::SoftGroup(_) => None,
            })
            .collect();
        let group_steps: Vec<Option<String>> = sequence
            .iter()
            .filter_map(|step| match step {
                ay_frontend::ObjectiveStep::SoftGroup(id) => Some(id.clone()),
                ay_frontend::ObjectiveStep::Arithmetic(_) => None,
            })
            .collect();
        let total_weight = soft_weights
            .iter()
            .try_fold(0u64, |sum, &weight| sum.checked_add(weight));
        arith_steps == (0..objectives.len()).collect::<Vec<_>>()
            && group_steps
                == groups
                    .iter()
                    .map(|group| group.id.clone())
                    .collect::<Vec<_>>()
            && total_weight.is_some_and(|total| total <= MAXSMT_EXACT_MAX_TOTAL_WEIGHT)
    }

    /// Strict improvement of a soft cost uses its AUTHORED Boolean domain at
    /// the endpoints: nonnegative costs cannot improve below zero, and a cost
    /// is below its total weight exactly when some positive-weight literal is
    /// false. This avoids asking mixed arithmetic to rediscover those Boolean
    /// identities. Interior bounds keep the existing exact Int comparison.
    fn joint_pareto_point_blocker(
        &mut self,
        frame: &JointParetoFrame<'_>,
        point: &[BigRational],
    ) -> Result<TermId> {
        use super::model::evaluation_copies;
        use ay_core::term::{CountedBuiltin, CountedTermBuilder};
        let unavailable = || {
            ExecutorError::UnsupportedOptimization(
                "joint Pareto blocker construction unavailable under original controls".into(),
            )
        };
        if point.len() != frame.extended.len() || point.len() != frame.step_map.len() {
            return Err(unavailable());
        }
        let scope =
            evaluation_copies::EvaluationCopyScope::enter(self).map_err(|_| unavailable())?;
        let metadata = point
            .len()
            .checked_mul(std::mem::size_of::<TermId>() + std::mem::size_of::<(usize, usize)>())
            .and_then(|bytes| {
                frame
                    .relax_vars
                    .len()
                    .checked_mul(std::mem::size_of::<TermId>())
                    .and_then(|vars| bytes.checked_add(vars))
            })
            .ok_or_else(unavailable)?;
        let visits = point
            .len()
            .checked_add(frame.relax_vars.len())
            .and_then(|visits| visits.checked_mul(2))
            .ok_or_else(unavailable)?;
        if !evaluation_copies::pay(visits, metadata) || !evaluation_copies::validate(self) {
            return Err(unavailable());
        }
        let cost_domain = |group_index: usize, value: &BigRational| {
            let total = frame
                .groups
                .get(group_index)?
                .indices
                .iter()
                .try_fold(0u64, |sum, &index| {
                    sum.checked_add(*frame.soft_weights.get(index)?)
                })?;
            let cost = value
                .is_integer()
                .then(|| value.numer().to_u64())
                .flatten()
                .filter(|&cost| cost <= total)?;
            Some((cost, total))
        };
        let mut scalar_bytes = 0usize;
        for (kind, value) in frame.step_map.iter().zip(point) {
            if !evaluation_copies::pay(0, 0) || !evaluation_copies::validate(self) {
                return Err(unavailable());
            }
            let copies_scalar = match kind {
                ParetoStepKind::Arithmetic(_) => true,
                ParetoStepKind::Group(index) => {
                    let (cost, total) = cost_domain(*index, value).ok_or_else(unavailable)?;
                    cost != 0 && cost != total
                }
            };
            // Boolean endpoints borrow a u64 cost and create NO rational
            // buffers. Price only the numeric comparisons actually constructed.
            if copies_scalar {
                scalar_bytes = scalar_bytes
                    .checked_add(std::mem::size_of::<BigRational>())
                    .ok_or_else(unavailable)?;
                for bits in [value.numer().bits(), value.denom().bits()] {
                    let bytes = bits
                        .checked_add(63)
                        .and_then(|bits| usize::try_from(bits / 64).ok())
                        .and_then(|limbs| limbs.checked_mul(8))
                        .ok_or_else(unavailable)?;
                    scalar_bytes = scalar_bytes.checked_add(bytes).ok_or_else(unavailable)?;
                }
            }
        }
        let bytes = scalar_bytes.checked_mul(8).ok_or_else(unavailable)?;
        let work = scalar_bytes.checked_mul(6).ok_or_else(unavailable)?;
        if !evaluation_copies::pay(work, bytes) || !evaluation_copies::validate(self) {
            return Err(unavailable());
        }
        let construction = scope.into_construction(self).map_err(|_| unavailable())?;
        let mut strict = vec![self.ctx.terms.false_term(); point.len()];
        let mut upper_endpoints = Vec::with_capacity(point.len());
        for (position, kind) in frame.step_map.iter().enumerate() {
            match kind {
                ParetoStepKind::Arithmetic(_) => {
                    strict[position] =
                        self.mk_strict_improve_atom(&frame.extended[position], &point[position])?;
                }
                ParetoStepKind::Group(group_index) => {
                    let value = &point[position];
                    let (cost, total) = cost_domain(*group_index, value).ok_or_else(unavailable)?;
                    if cost == 0 {
                        // The default false literal is EXACT for this domain.
                    } else if cost == total {
                        upper_endpoints.push((position, *group_index));
                    } else {
                        strict[position] =
                            self.mk_strict_improve_atom(&frame.extended[position], value)?;
                    }
                }
            }
        }
        if !construction.validate(self) {
            return Err(unavailable());
        }
        let mut builder =
            CountedTermBuilder::with_admission(&mut self.ctx.terms, construction.term_admission())
                .map_err(|_| unavailable())?;
        for (position, group_index) in upper_endpoints {
            let group = &frame.groups[group_index];
            let mut positive = Vec::with_capacity(group.indices.len());
            for &index in &group.indices {
                if frame.soft_weights[index] != 0 {
                    positive.push(frame.relax_vars[index]);
                }
            }
            let all = match positive.as_slice() {
                [] => return Err(unavailable()), // Positive total requires a positive coefficient.
                [only] => *only,
                _ => builder
                    .apply(CountedBuiltin::And, &positive)
                    .map_err(|_| unavailable())?,
            };
            strict[position] = builder
                .apply(CountedBuiltin::Not, &[all])
                .map_err(|_| unavailable())?;
        }
        let blocker = builder
            .apply(CountedBuiltin::Or, &strict)
            .map_err(|_| unavailable())?;
        builder.finish().map_err(|_| unavailable())?;
        if !construction.validate(self) {
            return Err(unavailable());
        }
        Ok(blocker)
    }

    /// One joint Pareto call inside its transactional frame: base
    /// feasibility over the hard problem, exhaustion-extension
    /// construction, and the seed probe (delegating emission to
    /// [`Self::joint_pareto_push_point`]). `Ok(None)` is inconclusive.
    fn joint_pareto_search(
        &mut self,
        frame: &JointParetoFrame<'_>,
        state: &mut ParetoState,
    ) -> Result<Option<JointParetoCaptured>> {
        // Base feasibility over the HARD problem (relaxation free = the
        // same verdict): also installs the unsat-query epoch over exactly
        // the authored assertions for the exhaustion declaration.
        let base_result = self.check_sat_internal()?;
        if base_result != SolveResult::Sat {
            return Ok(match base_result {
                SolveResult::Unknown => None,
                other => Some(JointParetoCaptured::Verdict(other)),
            });
        }
        // The relaxation clauses are folded into the extension's blocking
        // vector: the certified terminal obligation is
        // authored ∧ relaxation ∧ point-blockers — exactly the refuted
        // scope. The per-point blockers alone come first (the seed probe
        // assumes exactly those; the clauses are asserted separately).
        let Ok(exhaustion) = self.build_pareto_front_exhaustion_extension_with(
            frame.extended,
            &state.emitted,
            frame.relax_clauses,
            frame.sealed_objectives,
            |executor, point| executor.joint_pareto_point_blocker(frame, point),
        ) else {
            return Ok(None);
        };
        let point_blockers: Vec<TermId> = exhaustion.blocking()[..state.emitted.len()].to_vec();

        // The seed probe assumes the blockers AND the relaxation clauses
        // (asserting the clauses first would make the probe bind its
        // unsat epoch over authored+relaxation, which the exhaustion
        // declaration then rejects; as assumptions they line up exactly
        // with the extension's folded blocking vector).
        let snapshot = self.ctx.assertions.len();
        let mut seed_assumptions = point_blockers.clone();
        seed_assumptions.extend_from_slice(frame.relax_clauses);
        let seed = self.pareto_probe(&seed_assumptions)?;
        match seed {
            ParetoProbe::Sat => {}
            ParetoProbe::Unknown => return Ok(None),
            ParetoProbe::Unsat => {
                // Front exhausted: declare the extended obligation while
                // assertions/objectives are still exactly the exhausted
                // scope's, then reset the enumeration (Z3 cycles).
                if !self.declare_pareto_front_exhaustion_extension(exhaustion) {
                    return Ok(None);
                }
                let last = state.last_point.clone();
                self.pareto_state = Some(ParetoState {
                    emitted: Vec::new(),
                    last_point: last,
                });
                self.last_assumptions = None;
                self.last_assumption_core = None;
                self.last_model = None;
                self.last_result = Some(SolveResult::unsat());
                return Ok(Some(JointParetoCaptured::Verdict(SolveResult::unsat())));
            }
        }
        self.joint_pareto_push_point(frame, state, &seed_assumptions, snapshot)
    }

    /// Lex-push under the blockers and capture the emitted point (a
    /// lex-optimal point is Pareto-optimal). The relaxation clauses live
    /// only inside this push frame.
    fn joint_pareto_push_point(
        &mut self,
        frame: &JointParetoFrame<'_>,
        state: &mut ParetoState,
        seed_assumptions: &[TermId],
        snapshot: usize,
    ) -> Result<Option<JointParetoCaptured>> {
        let push_snapshot = self.ctx.assertions.len();
        let Some(cone) = self.pareto_seed_cone(frame.extended, seed_assumptions)? else {
            return Ok(None);
        };
        for &clause in frame.relax_clauses {
            self.maxsmt_assert(clause);
        }
        for &b in &cone {
            self.optimization_assert(b);
        }
        // A soft group has a known nonnegative weighted Boolean domain. Reuse
        // its maintained bounded optimizer rather than sending a synthetic Int
        // ITE through generic arithmetic (including impossible negative probes).
        // Arithmetic steps retain their ACTUAL declared certificate indices.
        let push_result = self.joint_optimize_steps(
            frame.sealed_objectives,
            frame.groups,
            frame.sequence,
            frame.soft_terms,
            frame.soft_weights,
            Some(frame.relax_vars),
        );
        if !self.unbounded_objectives.is_empty() || !self.infinitesimal_objectives.is_empty() {
            // Unbounded/unattained coordinate: no finite front (fail
            // closed, exactly like the arithmetic lane).
            self.unbounded_objectives.clear();
            self.infinitesimal_objectives.clear();
            self.unavailable_objectives.clear();
            self.ctx.truncate_assertions(snapshot);
            return Ok(None);
        }
        let point = match push_result {
            Ok(Some(_)) => self.joint_pareto_capture_point(frame),
            Ok(None) => None,
            Err(error) => {
                self.ctx.truncate_assertions(snapshot);
                self.invalidate_last_check_result();
                return Err(error);
            }
        };
        self.ctx.truncate_assertions(push_snapshot);
        let Some((values, finite_values, soft_roots, publication)) = point else {
            self.ctx.truncate_assertions(snapshot);
            return Ok(None);
        };
        debug_assert!(
            !state.emitted.iter().any(|e| e == &values),
            "joint pareto: emitted a duplicate point {values:?}"
        );
        state.emitted.push(values.clone());
        state.last_point = Some(values);
        self.pareto_state = Some(ParetoState {
            emitted: state.emitted.clone(),
            last_point: state.last_point.clone(),
        });
        self.ctx.truncate_assertions(snapshot);
        Ok(Some(JointParetoCaptured::Sat(Box::new((
            finite_values,
            soft_roots,
            publication,
        )))))
    }

    /// Capture the lex-pushed witness as a Pareto point: extended values,
    /// the real-indexed finite arithmetic values, and the joint soft
    /// accounting (which also verifies the witness realizes every group
    /// cost). `None` rejects the push.
    fn joint_pareto_capture_point(
        &mut self,
        frame: &JointParetoFrame<'_>,
    ) -> Option<(
        Vec<BigRational>,
        Vec<(usize, BigRational)>,
        Vec<TermId>,
        (u64, Vec<usize>, Vec<SoftGroupCost>),
    )> {
        let model = self.last_model.clone()?;
        let mut values = Vec::with_capacity(frame.extended.len());
        for obj in frame.extended {
            values.push(self.eval_objective_value(&model, obj.term).ok()?);
        }
        let mut finite_values = Vec::new();
        let mut group_optima: Vec<Option<u64>> = vec![None; frame.groups.len()];
        for (position, kind) in frame.step_map.iter().enumerate() {
            match kind {
                ParetoStepKind::Arithmetic(index) => {
                    finite_values.push((*index, values[position].clone()));
                }
                ParetoStepKind::Group(group_index) => {
                    group_optima[*group_index] =
                        Some(u64::try_from(values[position].to_integer()).ok()?);
                }
            }
        }
        let (soft_roots, publication) = self.joint_capture_soft_accounting(
            frame.softs,
            frame.groups,
            frame.soft_terms,
            frame.soft_weights,
            frame.relax_vars,
            &group_optima,
            false,
        )?;
        Some((values, finite_values, soft_roots, publication))
    }

    /// Shared joint-entry discipline: the declared objective sequence must
    /// exactly recount the live objectives and soft groups, the priority
    /// must be the one this entry implements, and the window's assertion
    /// additions plus internal relaxation symbols are rolled back before
    /// publication.
    fn joint_optimize(
        &mut self,
        objectives: &[ay_frontend::Objective],
        priority: OptPriority,
    ) -> Result<SolveResult> {
        let softs: Vec<ay_frontend::SoftAssertion> = self.ctx.soft_constraints().to_vec();
        let groups = partition_soft_groups(&softs);
        let sequence: Vec<ay_frontend::ObjectiveStep> = self.ctx.objective_sequence().to_vec();
        // The sequence is authoritative only when it exactly recounts the
        // live objectives and soft groups (a native-API soft replacement or
        // any other out-of-band mutation leaves it stale; fail closed).
        let arith_steps: Vec<usize> = sequence
            .iter()
            .filter_map(|step| match step {
                ay_frontend::ObjectiveStep::Arithmetic(index) => Some(*index),
                ay_frontend::ObjectiveStep::SoftGroup(_) => None,
            })
            .collect();
        let group_steps: Vec<Option<String>> = sequence
            .iter()
            .filter_map(|step| match step {
                ay_frontend::ObjectiveStep::SoftGroup(id) => Some(id.clone()),
                ay_frontend::ObjectiveStep::Arithmetic(_) => None,
            })
            .collect();
        let consistent = arith_steps == (0..objectives.len()).collect::<Vec<_>>()
            && group_steps
                == groups
                    .iter()
                    .map(|group| group.id.clone())
                    .collect::<Vec<_>>();
        let soft_terms: Vec<TermId> = softs.iter().map(|s| s.term).collect();
        let soft_weights: Vec<u64> = softs.iter().map(|s| s.weight).collect();
        let total_weight = soft_weights
            .iter()
            .try_fold(0u64, |sum, &weight| sum.checked_add(weight));
        if !consistent
            || self.opt_priority() != priority
            || total_weight.is_none_or(|total| total > MAXSMT_EXACT_MAX_TOTAL_WEIGHT)
        {
            return Ok(self.optimization_inconclusive());
        }

        let base_assertion_count = self.ctx.assertions.len();
        let outcome = match priority {
            OptPriority::Box => {
                self.joint_optimize_box_window(objectives, &softs, &groups, &sequence)
            }
            _ => self.joint_optimize_lex_window(objectives, &softs, &groups, &sequence),
        };
        self.ctx.truncate_assertions(base_assertion_count);
        let internal_symbols: Vec<String> = self
            .ctx
            .symbol_iter()
            .map(|(name, _)| name.clone())
            .filter(|name| name.starts_with("__ay_soft_"))
            .collect();
        self.ctx.remove_symbols(&internal_symbols);
        match outcome {
            Ok(Some(JointCaptured::Sat(captured))) => {
                let (finite_values, soft_roots, soft_publication, witness_values) = *captured;
                self.finalize_joint_optimization(
                    &finite_values,
                    &soft_roots,
                    &soft_publication,
                    &witness_values,
                )
            }
            Ok(Some(JointCaptured::Verdict(verdict))) if verdict.is_unsat() => {
                // The window verdict was over the relaxed scope; re-establish
                // UNSAT over the restored hard assertions so its proof is
                // certifiable, exactly as the pure MaxSMT path does.
                self.begin_public_solve(false);
                self.bind_unsat_query_assumptions(&[]);
                let hard_result = self.check_sat();
                if hard_result.is_err() {
                    self.invalidate_last_check_result();
                }
                hard_result
            }
            Ok(Some(JointCaptured::Verdict(verdict))) => Ok(verdict),
            Ok(None) => Ok(self.optimization_inconclusive()),
            Err(error) => {
                self.invalidate_last_check_result();
                Err(error)
            }
        }
    }

    /// The joint search inside its transactional window. `Ok(None)` means
    /// inconclusive; `Ok(Some(..))` carries everything publication needs:
    /// finite arithmetic values, soft classification roots, and the captured
    /// soft accounting `(total_cost, violated, group_costs)`.
    fn joint_optimize_lex_window(
        &mut self,
        objectives: &[ay_frontend::Objective],
        softs: &[ay_frontend::SoftAssertion],
        groups: &[SoftGroup],
        sequence: &[ay_frontend::ObjectiveStep],
    ) -> Result<Option<JointCaptured>> {
        let soft_terms: Vec<TermId> = softs.iter().map(|s| s.term).collect();
        let soft_weights: Vec<u64> = softs.iter().map(|s| s.weight).collect();
        let base_result = self.check_sat_internal()?;
        if base_result != SolveResult::Sat {
            return Ok(match base_result {
                SolveResult::Unknown => None,
                other => return Ok(Some(JointCaptured::Verdict(other))),
            });
        }
        let Some((finite_values, group_optima, suffix_interval, mut relax_vars)) = self
            .joint_optimize_steps(
                objectives,
                groups,
                sequence,
                &soft_terms,
                &soft_weights,
                None,
            )?
        else {
            return Ok(None);
        };
        // Capture soft accounting against the final in-window witness. The
        // relaxation may never have been built (search stopped at an
        // unbounded arithmetic step); build it now — accounting falls back
        // to term evaluation where the witness lacks relax values.
        if relax_vars.is_none() {
            relax_vars = Some(self.maxsmt_build_relaxation(&soft_terms).into());
        }
        let Some(relax_vars) = relax_vars else {
            return Ok(None);
        };
        let Some((soft_roots, publication)) = self.joint_capture_soft_accounting(
            softs,
            groups,
            &soft_terms,
            &soft_weights,
            &relax_vars,
            &group_optima,
            suffix_interval,
        ) else {
            return Ok(None);
        };
        // Lex: the published witness attains every finite arithmetic value.
        let witness_values = finite_values.clone();
        Ok(Some(JointCaptured::Sat(Box::new((
            finite_values,
            soft_roots,
            publication,
            witness_values,
        )))))
    }

    /// Joint `box` window: every objective (arithmetic or soft group) is
    /// optimized INDEPENDENTLY against the hard assertions alone, and the
    /// published witness attains the FIRST declared objective's optimum
    /// (z3's box behavior). Same capture contract as the lex window, except
    /// `witness_values` holds only the first objective's finite value when
    /// it is arithmetic.
    fn joint_optimize_box_window(
        &mut self,
        objectives: &[ay_frontend::Objective],
        softs: &[ay_frontend::SoftAssertion],
        groups: &[SoftGroup],
        sequence: &[ay_frontend::ObjectiveStep],
    ) -> Result<Option<JointCaptured>> {
        let soft_terms: Vec<TermId> = softs.iter().map(|s| s.term).collect();
        let soft_weights: Vec<u64> = softs.iter().map(|s| s.weight).collect();
        let base_result = self.check_sat_internal()?;
        if base_result != SolveResult::Sat {
            return Ok(match base_result {
                SolveResult::Unknown => None,
                other => return Ok(Some(JointCaptured::Verdict(other))),
            });
        }
        let Some((finite_values, group_optima, relax_vars)) = self.joint_optimize_box_steps(
            objectives,
            groups,
            sequence,
            &soft_terms,
            &soft_weights,
        )?
        else {
            return Ok(None);
        };
        // The first declared objective selects the witness requirement.
        let (witness_values, first_group) = match sequence.first() {
            Some(ay_frontend::ObjectiveStep::Arithmetic(index)) => (
                finite_values
                    .iter()
                    .filter(|(i, _)| i == index)
                    .cloned()
                    .collect::<Vec<_>>(),
                None,
            ),
            Some(ay_frontend::ObjectiveStep::SoftGroup(id)) => {
                (Vec::new(), groups.iter().position(|group| &group.id == id))
            }
            None => return Ok(None),
        };
        let Some((soft_roots, publication)) = self.joint_capture_box_accounting(
            softs,
            groups,
            &soft_terms,
            &soft_weights,
            &relax_vars,
            &group_optima,
            first_group,
        ) else {
            return Ok(None);
        };
        Ok(Some(JointCaptured::Sat(Box::new((
            finite_values,
            soft_roots,
            publication,
            witness_values,
        )))))
    }

    /// Independent per-step optima for joint `box`. Nothing is committed
    /// between steps, so each step sees exactly the hard problem; afterwards
    /// the FIRST step's optimum is pinned and the witness refreshed so the
    /// published model attains it, as in z3. Arithmetic optima are computed
    /// BEFORE the soft relaxation exists (independence makes the order
    /// irrelevant, and the relaxation's disjunctions make the arithmetic
    /// optimizer decline — the same reason lex builds it lazily). Returns
    /// finite values, per-group optima and the relaxation; `None` is
    /// inconclusive.
    fn joint_optimize_box_steps(
        &mut self,
        objectives: &[ay_frontend::Objective],
        groups: &[SoftGroup],
        sequence: &[ay_frontend::ObjectiveStep],
        soft_terms: &[TermId],
        soft_weights: &[u64],
    ) -> Result<Option<(Vec<(usize, BigRational)>, Vec<Option<u64>>, Vec<TermId>)>> {
        let mut finite_values: Vec<(usize, BigRational)> = Vec::new();
        let mut group_optima: Vec<Option<u64>> = vec![None; groups.len()];
        // Pass 1: independent arithmetic optima, before any relaxation.
        for step in sequence {
            if let ay_frontend::ObjectiveStep::Arithmetic(objective_index) = step {
                let obj = &objectives[*objective_index];
                let Some((model, value)) = self.optimize_one_objective(*objective_index, obj)?
                else {
                    return Ok(None);
                };
                self.last_model = Some(model);
                // Unbounded/infinitesimal outcomes do not stop the other
                // independent steps (unlike lex's suffix rule).
                if !self.unbounded_objectives.contains_key(objective_index)
                    && !self.infinitesimal_objectives.contains_key(objective_index)
                {
                    finite_values.push((*objective_index, value));
                }
            }
        }
        // Pass 2: independent soft-group optima over the relaxation.
        let relax_vars = self.maxsmt_build_relaxation(soft_terms);
        for step in sequence {
            if let ay_frontend::ObjectiveStep::SoftGroup(id) = step {
                let Some(group_index) = groups.iter().position(|group| &group.id == id) else {
                    return Ok(None);
                };
                let group = &groups[group_index];
                let group_relax: Vec<TermId> =
                    group.indices.iter().map(|&i| relax_vars[i]).collect();
                let group_weights: Vec<u64> =
                    group.indices.iter().map(|&i| soft_weights[i]).collect();
                let group_total: u64 = group_weights.iter().sum();
                let Some(optimum) =
                    self.maxsmt_group_optimum(&[], &group_relax, &group_weights, group_total)
                else {
                    return Ok(None);
                };
                group_optima[group_index] = Some(optimum);
            }
        }
        // Pin the first step's optimum and refresh: the published witness
        // attains the first declared objective, as in z3's box mode.
        match sequence.first() {
            Some(ay_frontend::ObjectiveStep::Arithmetic(index)) => {
                if let Some((_, value)) = finite_values.iter().find(|(i, _)| i == index).cloned() {
                    let obj = &objectives[*index];
                    let obj_sort = self.ctx.terms.sort(obj.term).clone();
                    let commit = match obj.direction {
                        ObjectiveDirection::Maximize => {
                            self.mk_commit_ge(obj.term, &value, &obj_sort)
                        }
                        ObjectiveDirection::Minimize => {
                            self.mk_commit_le(obj.term, &value, &obj_sort)
                        }
                    };
                    self.optimization_assert(commit);
                }
            }
            Some(ay_frontend::ObjectiveStep::SoftGroup(id)) => {
                let Some(group_index) = groups.iter().position(|group| &group.id == id) else {
                    return Ok(None);
                };
                let Some(optimum) = group_optima[group_index] else {
                    return Ok(None);
                };
                let group = &groups[group_index];
                let group_relax: Vec<TermId> =
                    group.indices.iter().map(|&i| relax_vars[i]).collect();
                let group_weights: Vec<u64> =
                    group.indices.iter().map(|&i| soft_weights[i]).collect();
                self.maxsmt_assert_weighted_at_most_w(&group_relax, &group_weights, optimum);
            }
            None => return Ok(None),
        }
        if !self.joint_refresh_witness()? {
            return Ok(None);
        }
        Ok(Some((finite_values, group_optima, relax_vars)))
    }

    /// Box counterpart of [`Self::joint_capture_soft_accounting`]: group
    /// costs are the INDEPENDENT optima (the witness generally attains only
    /// the first group's, and only when a soft group is declared first);
    /// violations and total cost describe the published witness.
    fn joint_capture_box_accounting(
        &mut self,
        softs: &[ay_frontend::SoftAssertion],
        groups: &[SoftGroup],
        soft_terms: &[TermId],
        soft_weights: &[u64],
        relax_vars: &[TermId],
        group_optima: &[Option<u64>],
        first_group: Option<usize>,
    ) -> Option<JointAccounting> {
        let (total_cost, violated) = self.maxsmt_violations(
            soft_terms,
            relax_vars,
            soft_weights,
            self.last_model.as_ref(),
        )?;
        let mut is_violated = vec![false; softs.len()];
        for &index in &violated {
            *is_violated.get_mut(index)? = true;
        }
        let mut group_costs = Vec::with_capacity(groups.len());
        for (group_index, group) in groups.iter().enumerate() {
            let optimum = group_optima[group_index]?;
            if first_group == Some(group_index) {
                let witnessed: u64 = group
                    .indices
                    .iter()
                    .filter(|&&i| is_violated[i])
                    .map(|&i| soft_weights[i])
                    .sum();
                if witnessed != optimum {
                    return None;
                }
            }
            group_costs.push(SoftGroupCost {
                id: group.id.clone(),
                cost: optimum,
                interval: false,
            });
        }
        let soft_roots = self.maxsmt_classification_roots(softs, &violated)?;
        Some((soft_roots, (total_cost, violated, group_costs)))
    }

    /// Run the lex steps in declaration order inside the window, committing
    /// each optimum (arithmetic bounds; soft weighted-at-most pins). The
    /// soft relaxation is built LAZILY at the first soft step: its
    /// `(or soft relax)` clauses are disjunctions, under which the arithmetic
    /// optimizer's simplex unboundedness proof declines, so an arithmetic
    /// step before any soft step must see the pristine hard+commits problem.
    /// Returns finite values, per-group optima, the suffix-interval flag,
    /// and the (maybe built) relaxation vars; `None` is inconclusive.
    fn joint_optimize_steps<'a>(
        &mut self,
        objectives: &[ay_frontend::Objective],
        groups: &[SoftGroup],
        sequence: &[ay_frontend::ObjectiveStep],
        soft_terms: &[TermId],
        soft_weights: &[u64],
        prepared_relaxation: Option<&'a [TermId]>,
    ) -> Result<Option<JointSteps<'a>>> {
        if prepared_relaxation.is_some_and(|vars| vars.len() != soft_terms.len()) {
            return Ok(None);
        }
        // Pareto already owns these exact variables and their clauses. Borrow
        // them: a fresh relaxation would describe a different cost coordinate.
        let mut relax_vars = prepared_relaxation.map(std::borrow::Cow::Borrowed);
        let mut finite_values: Vec<(usize, BigRational)> = Vec::new();
        let mut group_optima: Vec<Option<u64>> = vec![None; groups.len()];
        let mut suffix_interval = false;
        for (step_pos, step) in sequence.iter().enumerate() {
            let last_step = step_pos + 1 == sequence.len();
            match step {
                ay_frontend::ObjectiveStep::Arithmetic(objective_index) => {
                    let obj = &objectives[*objective_index];
                    let Some((model, value)) =
                        self.optimize_one_objective(*objective_index, obj)?
                    else {
                        return Ok(None);
                    };
                    self.last_model = Some(model);
                    if self.unbounded_objectives.contains_key(objective_index)
                        || self.infinitesimal_objectives.contains_key(objective_index)
                    {
                        // No attainable value to commit: later arithmetic
                        // objectives are unavailable, later soft groups take
                        // z3's interval outcome, and the search stops here.
                        for later in &sequence[step_pos + 1..] {
                            if let ay_frontend::ObjectiveStep::Arithmetic(index) = later {
                                self.unavailable_objectives.insert(*index);
                            }
                        }
                        suffix_interval = true;
                        break;
                    }
                    finite_values.push((*objective_index, value.clone()));
                    if !last_step {
                        let obj_sort = self.ctx.terms.sort(obj.term).clone();
                        let commit = match obj.direction {
                            ObjectiveDirection::Maximize => {
                                self.mk_commit_ge(obj.term, &value, &obj_sort)
                            }
                            ObjectiveDirection::Minimize => {
                                self.mk_commit_le(obj.term, &value, &obj_sort)
                            }
                        };
                        self.optimization_assert(commit);
                    }
                }
                ay_frontend::ObjectiveStep::SoftGroup(id) => {
                    let Some(group_index) = groups.iter().position(|group| &group.id == id) else {
                        return Ok(None);
                    };
                    if relax_vars.is_none() {
                        relax_vars = Some(self.maxsmt_build_relaxation(soft_terms).into());
                        // The warm witness predates the relaxation vars;
                        // refresh it so later accounting sees their values.
                        if !self.joint_refresh_witness()? {
                            return Ok(None);
                        }
                    }
                    let Some(relax_vars_ref) = relax_vars.as_ref() else {
                        return Ok(None);
                    };
                    let group = &groups[group_index];
                    let group_relax: Vec<TermId> =
                        group.indices.iter().map(|&i| relax_vars_ref[i]).collect();
                    let group_weights: Vec<u64> =
                        group.indices.iter().map(|&i| soft_weights[i]).collect();
                    let group_total: u64 = group_weights.iter().sum();
                    // Earlier commits are live assertions in this window, so
                    // the binary search needs no separate pin set.
                    let Some(optimum) =
                        self.maxsmt_group_optimum(&[], &group_relax, &group_weights, group_total)
                    else {
                        return Ok(None);
                    };
                    group_optima[group_index] = Some(optimum);
                    // Commit and refresh even on the last step: unlike an
                    // arithmetic step (which returns its attaining model), a
                    // soft step's binary search leaves the warm witness at an
                    // arbitrary feasible point, so final accounting needs a
                    // witness that attains this group's optimum too.
                    self.maxsmt_assert_weighted_at_most_w(&group_relax, &group_weights, optimum);
                    if !self.joint_refresh_witness()? {
                        return Ok(None);
                    }
                }
            }
        }
        Ok(Some((
            finite_values,
            group_optima,
            suffix_interval,
            relax_vars,
        )))
    }

    /// Re-solve the window as committed so far and install its witness.
    fn joint_refresh_witness(&mut self) -> Result<bool> {
        let (result, model) = self.maxsmt_scoped_check_sat(|_| {})?;
        if result.is_sat() && model.is_some() {
            self.last_model = model;
        }
        Ok(result.is_sat())
    }

    /// Verify the final in-window witness realizes every decided group's
    /// proven optimum, and build the publication triple plus classification
    /// roots. Groups past a suffix-interval break get interval outcomes.
    fn joint_capture_soft_accounting(
        &mut self,
        softs: &[ay_frontend::SoftAssertion],
        groups: &[SoftGroup],
        soft_terms: &[TermId],
        soft_weights: &[u64],
        relax_vars: &[TermId],
        group_optima: &[Option<u64>],
        suffix_interval: bool,
    ) -> Option<JointAccounting> {
        let (total_cost, violated) = self.maxsmt_violations(
            soft_terms,
            relax_vars,
            soft_weights,
            self.last_model.as_ref(),
        )?;
        let mut is_violated = vec![false; softs.len()];
        for &index in &violated {
            *is_violated.get_mut(index)? = true;
        }
        let mut group_costs = Vec::with_capacity(groups.len());
        for (group_index, group) in groups.iter().enumerate() {
            let group_total: u64 = group.indices.iter().map(|&i| soft_weights[i]).sum();
            match group_optima[group_index] {
                Some(optimum) => {
                    let witnessed: u64 = group
                        .indices
                        .iter()
                        .filter(|&&i| is_violated[i])
                        .map(|&i| soft_weights[i])
                        .sum();
                    if witnessed != optimum {
                        return None;
                    }
                    group_costs.push(SoftGroupCost {
                        id: group.id.clone(),
                        cost: optimum,
                        interval: false,
                    });
                }
                None if suffix_interval => group_costs.push(SoftGroupCost {
                    id: group.id.clone(),
                    cost: group_total,
                    interval: true,
                }),
                None => return None,
            }
        }
        let soft_roots = self.maxsmt_classification_roots(softs, &violated)?;
        Some((soft_roots, (total_cost, violated, group_costs)))
    }

    /// Joint counterpart of [`Self::finalize_optimization`]: certify the
    /// captured witness with arithmetic value roots AND soft classification
    /// roots, re-account both objective classes against the final model,
    /// then publish both outcome families together.
    fn finalize_joint_optimization(
        &mut self,
        finite_values: &[(usize, BigRational)],
        soft_roots: &[TermId],
        soft_publication: &(u64, Vec<usize>, Vec<SoftGroupCost>),
        witness_values: &[(usize, BigRational)],
    ) -> Result<SolveResult> {
        self.last_assumptions = None;
        self.last_assumption_core = None;
        self.last_result = Some(SolveResult::Sat);
        self.last_unknown_reason = None;
        self.last_model_validated = false;
        self.finite_objective_values.clear();
        self.last_soft_cost = None;
        self.last_soft_violations = None;
        self.last_soft_group_costs = None;

        // Roots certify the published witness, so they cover only the
        // values it attains; under box the other independent optima are
        // published without a witness attaining them (as in `optimize_box`).
        let Some(mut value_roots) = self.optimization_value_roots(witness_values) else {
            return Ok(self.reject_optimization_final_witness());
        };
        value_roots.extend_from_slice(soft_roots);
        let emitted = match self.emit_captured_optimization_witness(SolveResult::Sat, &value_roots)
        {
            Ok(result) => result,
            Err(error) => {
                self.invalidate_last_check_result();
                return Err(error);
            }
        };
        if emitted != SolveResult::Sat {
            return Ok(self.optimization_inconclusive());
        }
        // Only the witness-attained values are re-checked against the final
        // model: under box the remaining finite values are independent
        // optima no single witness realizes (just as in `optimize_box`).
        if !self.optimization_final_values_match(witness_values) {
            return Ok(self.reject_optimization_final_witness());
        }
        let softs: Vec<ay_frontend::SoftAssertion> = self.ctx.soft_constraints().to_vec();
        let (total_cost, violated, group_costs) = soft_publication;
        match self.maxsmt_final_witness_accounting(&softs) {
            Some((final_cost, final_violated))
                if final_cost == *total_cost && &final_violated == violated => {}
            _ => return Ok(self.reject_optimization_final_witness()),
        }
        self.finite_objective_values
            .extend(finite_values.iter().cloned());
        self.last_soft_cost = Some(*total_cost);
        self.last_soft_cost_optimal = true;
        self.last_soft_group_costs = Some(group_costs.clone());
        self.last_soft_violations = Some(violated.clone());
        Ok(emitted)
    }

    /// BOX (independent) multi-objective optimization.
    ///
    /// Each objective is optimized INDEPENDENTLY against the HARD constraints
    /// alone: no prior objective's optimum is committed, so objective i's box
    /// optimum equals what optimizing ONLY objective i (same hard constraints)
    /// would give. SOUNDNESS: because nothing is committed between
    /// objectives, [`Self::optimize_one_objective`] sees exactly the user's hard
    /// assertion set for every objective — identical to a standalone
    /// single-objective run — so a box optimum can never be wrong relative to its
    /// independent optimum.
    ///
    /// The per-objective box optima are recorded in `finite_objective_values` (and
    /// unbounded ones in `unbounded_objectives` as usual) so `(get-objectives)`
    /// reports each independent optimum directly — there is no single model that
    /// achieves all box optima simultaneously, so the final `last_model` (which
    /// only witnesses the last objective) cannot be used to recover them.
    fn optimize_box(&mut self, objectives: &[ay_frontend::Objective]) -> Result<SolveResult> {
        // The base SAT model is the feasibility witness for `(check-sat)`.
        let base_model = self.last_model.clone();
        let mut finite_values = Vec::with_capacity(objectives.len());
        for (objective_index, obj) in objectives.iter().enumerate() {
            match self.optimize_one_objective(objective_index, obj)? {
                Some((model, value)) => {
                    // Capture the independent optimum, but do not publish it
                    // until the public feasibility witness is admitted.
                    // Unbounded objectives have no useful finite value here
                    // (reported via `unbounded_objectives`), and infinitesimal
                    // ones are reported via `infinitesimal_objectives` in
                    // ε-form (#opt-epsilon).
                    if !self.unbounded_objectives.contains_key(&objective_index)
                        && !self.infinitesimal_objectives.contains_key(&objective_index)
                    {
                        finite_values.push((objective_index, value));
                    }
                    // Keep the model around as a feasibility witness; it is only
                    // used as fallback (get-objectives reads box optima directly).
                    self.last_model = Some(model);
                }
                None => return Ok(self.optimization_inconclusive()),
            }
        }
        // Restore the plain base SAT model so `(get-model)` reflects a feasible
        // assignment to the hard constraints rather than the last objective's
        // bound-pushed witness. `(get-objectives)` uses `finite_objective_values`,
        // so it does not depend on which feasible model is installed here.
        if base_model.is_some() {
            self.last_model = base_model;
        }
        // BOX has no joint optimum model: authenticate the hard-formula witness
        // but deliberately do not require it to attain all independent values.
        self.finalize_optimization(&finite_values, false)
    }

    /// PARETO multi-objective optimization via the Guided Improvement Algorithm
    /// (GIA) — Z3-compatible `(set-option :opt.priority pareto)`.
    ///
    /// ## Protocol (matches Z3 4.x, verified empirically 2026-06-15)
    ///
    /// Pareto mode is STATEFUL. Each `(check-sat)` returns `sat` and emits the
    /// NEXT Pareto-optimal point, whose objective values `(get-objectives)` then
    /// reports. Once the front is exhausted, `(check-sat)` returns `unsat` (and
    /// `(get-objectives)` keeps reporting the LAST emitted point). A FURTHER
    /// `(check-sat)` after that terminal `unsat` RESTARTS the enumeration from the
    /// first point (Z3's cyclic behavior — confirmed: a 3-point front over 8
    /// `(check-sat)` calls yields `sat sat sat unsat sat sat sat unsat`). The
    /// checked finite exhaustion establishes the complete Pareto set. AY's emission ORDER is its own
    /// deterministic GIA discovery order (Z3's order is algorithm-specific and not
    /// a clean sort, so per the task we match the SET, not the sequence).
    ///
    /// ## Supported objective sorts (LIMITATION)
    ///
    /// Int, Real and unsigned BitVec objectives share the checked lex push.
    /// Infinite fronts are emitted incrementally; exhaustion is not promised.
    /// A push with an unbounded or unattained coordinate remains inconclusive.
    ///
    /// ## Algorithm (Guided Improvement Algorithm with checked lex pushes)
    ///
    /// A point p DOMINATES q iff p is at-least-as-good as q on EVERY objective (in
    /// each objective's optimize direction) and STRICTLY better on at least one.
    /// The state ([`ParetoState`]) holds every point already emitted this front.
    ///
    /// To produce the next point per `(check-sat)`:
    /// 1. SEED feasibility: is there a feasible solution NOT dominated-or-equal by
    ///    any already emitted point? We assume, for each emitted point `e`, the
    ///    blocking constraint "strictly better than `e` on >= 1 objective" (= NOT
    ///    dominated-or-equal by `e`). If UNSAT, the front is exhausted → return
    ///    `unsat` and CLEAR the emitted set so the next `(check-sat)` restarts (Z3
    ///    cyclic behavior).
    /// 2. PUSH to a Pareto-optimal point by LEXICOGRAPHIC optimization subject to
    ///    a certified seed's weak-dominance cone: temporarily assert its bounds onto
    ///    the hard stack and run the tested [`Self::optimize_lex`] (maximize obj0,
    ///    then obj1 under obj0's optimum, ...). A lex-optimal point is ALWAYS
    ///    Pareto-optimal. Reusing lex makes the push sound for every supported sort
    ///    and mixed min/max when an attained finite lex optimum is established.
    ///    An inconclusive or unattained push withholds a point. The
    ///    temporary blocking + lex's committed optima are reverted afterward.
    /// 3. EMIT it: record its objective values in `emitted` and `last_point`, and
    ///    install its witness model so `(get-objectives)` reports it.
    ///
    /// SOUNDNESS: a lex-optimal point cannot be dominated (improving
    /// any objective without worsening an earlier one is impossible by lex
    /// construction; improving a later one without worsening an earlier one is
    /// blocked by the committed earlier optima), so every emitted point is
    /// genuinely Pareto-optimal — a debug re-probe also rejects any certified
    /// strict dominator. Step 1's blocking guarantees each new point
    /// is not dominated-or-equal by any prior emitted point, and (being
    /// Pareto-optimal) it cannot dominate a prior point either, so the emitted set
    /// is duplicate-free and dominated-free. Step 1 UNSAT means every feasible
    /// point is dominated-or-equal by some emitted point — the front is truly
    /// exhausted. Any un-emitted Pareto point
    /// satisfies the seed's "not dominated-or-equal by any emitted" constraint
    /// (emitted points are all Pareto, none dominates-or-equals a distinct Pareto
    /// point), so step 1 stays SAT until every Pareto point is emitted. A
    /// non-Pareto point is NEVER emitted.
    fn optimize_pareto(&mut self, objectives: &[ay_frontend::Objective]) -> Result<SolveResult> {
        // Z3 degenerates single-objective `pareto` to plain optimization:
        // the optimum is re-emitted on every call and the front never
        // exhausts (measured against z3 4.16 for both directions).
        if objectives.len() <= 1 {
            self.pareto_state = None;
            return self.optimize_lex(objectives);
        }
        // Take the persisted enumeration (or start fresh). We move it out so the
        // borrow checker lets us mutate `self` during probing; it is written back
        // before returning on every path.
        let mut state = self.pareto_state.take().unwrap_or_default();

        // (1) SEED: a feasible point not dominated-or-equal by any emitted point.
        // Blocking literal per emitted point `e`: "strictly better than e on >= 1
        // objective" — the negation of "e dominates-or-equals this solution".
        let exhaustion =
            self.build_pareto_front_exhaustion_extension(objectives, &state.emitted)?;
        let seed = self.pareto_probe(exhaustion.blocking())?;
        match seed {
            ParetoProbe::Sat => {}
            ParetoProbe::Unknown => {
                // Inconclusive seed probe: cannot soundly continue or declare the
                // front exhausted. The partial front is not a public optimum and
                // is revoked with the other partial objective artefacts; a retry
                // starts a fresh enumeration.
                return Ok(self.optimization_inconclusive());
            }
            ParetoProbe::Unsat => {
                // Front exhausted: every feasible point is dominated-or-equal by an
                // emitted one. Match Z3: return unsat and RESET the emitted set so
                // the next `(check-sat)` restarts the front from the first point.
                // Keep `last_point` for `(get-objectives)` after the terminal unsat.
                let last = state.last_point.clone();
                // #pareto-terminal-obligation — the claim this `unsat` makes is
                // "no feasible point escapes the emitted front", i.e. a
                // refutation of `authored AND block`, and `block` is what the
                // seed probe just refuted with. Declare it so the mandatory
                // certification certifies THAT property instead of rejecting a
                // correct refutation for assuming a term the authored
                // assertions do not contain. Declared BEFORE `state` is reset,
                // since `block` was built from the emitted points.
                if !self.declare_pareto_front_exhaustion_extension(exhaustion) {
                    return Ok(self.optimization_inconclusive());
                }
                self.pareto_state = Some(ParetoState {
                    emitted: Vec::new(),
                    last_point: last,
                });
                // Left as `None` deliberately: the blocking conjuncts travel in
                // the epoch's own extension slot, and `(get-unsat-assumptions)`
                // must keep reporting nothing for a plain `(check-sat)`.
                self.last_assumptions = None;
                self.last_assumption_core = None;
                self.last_model = None;
                self.last_result = Some(SolveResult::unsat());
                return Ok(SolveResult::unsat());
            }
        }

        let Some(block) = self.pareto_seed_cone(objectives, exhaustion.blocking())? else {
            return Ok(self.optimization_inconclusive());
        };

        // (2) PUSH TO PARETO-OPTIMALITY by LEXICOGRAPHIC optimization subject to
        // the certified seed's closed cone. A lex-optimal point (maximize obj0, then
        // obj1 under obj0's optimum, ...) is ALWAYS Pareto-optimal: improving any
        // objective without worsening an earlier one is impossible by construction,
        // and improving a later one without worsening an earlier one is impossible
        // because the earlier optima are committed. Reusing the tested `optimize_lex`
        // machinery (Int exp+binary / Real simplex / BV binary) makes the push sound
        // for supported sorts and mixed min/max. An attained finite lex optimum
        // avoids an epsilon climb that approaches but never reaches a supremum;
        // unsupported, unbounded and unattained pushes remain inconclusive.
        //
        // The weak cone replaces old strict blockers during this push. Every
        // cone point still escapes every prior point, while the closed boundary
        // avoids an unattained optimum caused solely by an old strict blocker.
        // These bounds (and `optimize_lex`'s committed optima) are reverted by
        // the snapshot/truncate below, leaving `ctx.assertions` pristine.
        let snapshot = self.ctx.assertions.len();
        for &b in &block {
            self.optimization_assert(b);
        }
        let push_result = self.optimize_lex(objectives);
        // Capture the lex-pushed witness + its objective values BEFORE reverting.
        let lex_outcome = match push_result {
            Ok(SolveResult::Sat) => {
                let model = self.last_model.clone();
                match model {
                    Some(m) => {
                        let mut vals = Vec::with_capacity(objectives.len());
                        let mut ok = true;
                        for obj in objectives {
                            match self.eval_objective_value(&m, obj.term) {
                                Ok(v) => vals.push(v),
                                Err(_) => {
                                    ok = false;
                                    break;
                                }
                            }
                        }
                        if ok {
                            Some((m, vals))
                        } else {
                            None
                        }
                    }
                    None => None,
                }
            }
            // A SAT seed but a non-SAT / errored lex-push is an internal anomaly
            // (the blocking region was just shown feasible). Treat as inconclusive.
            Ok(_) => None,
            Err(_) => None,
        };
        // Revert blocking constraints + optimize_lex's committed optima.
        self.ctx.truncate_assertions(snapshot);

        // An objective unbounded inside this improvement cone prevents the lex
        // push from establishing an attained finite vector. Withhold the point
        // instead of emitting an infinity placeholder as a Pareto optimum.
        // `unbounded_objectives` is cleared so the structured API
        // (`objective_optimum`, which consults it BEFORE `last_result`) cannot
        // report PosInfinity/NegInfinity alongside an unknown verdict. Later
        // pushes are inert anyway: the blocking constraints are `or` terms on
        // `ctx.assertions`, so the faithfulness audit forces NotApplicable.
        if !self.unbounded_objectives.is_empty() || !self.infinitesimal_objectives.is_empty() {
            self.unbounded_objectives.clear();
            // A strict authored Real bound can still make a coordinate's
            // optimum unattained. It must not become a public Pareto point.
            self.infinitesimal_objectives.clear();
            self.pareto_state = Some(state);
            return Ok(self.optimization_inconclusive());
        }

        let Some((cur_model, cur_vals)) = lex_outcome else {
            // The lex push did not establish a point. No partial enumeration or
            // optimum remains public after an inconclusive result.
            return Ok(self.optimization_inconclusive());
        };

        // (3) EMIT the Pareto-optimal point.
        debug_assert!(
            !state.emitted.iter().any(|e| e == &cur_vals),
            "pareto: emitted a duplicate point {cur_vals:?}"
        );
        // Debug soundness check: the lex-pushed point must NOT be strictly
        // dominated by any feasible solution (i.e. it is genuinely Pareto-optimal).
        #[cfg(debug_assertions)]
        {
            let probe = self.mk_strictly_dominates_value(objectives, &cur_vals)?;
            let dominated = self.pareto_probe(&[probe])? == ParetoProbe::Sat;
            debug_assert!(
                !dominated,
                "pareto: emitted a non-Pareto-optimal point {cur_vals:?} (a feasible \
                 solution strictly dominates it)"
            );
        }
        state.emitted.push(cur_vals.clone());
        state.last_point = Some(cur_vals.clone());
        self.pareto_state = Some(state);

        self.last_model = Some(cur_model);
        let finite_values: Vec<_> = cur_vals.iter().cloned().enumerate().collect();
        // Bind the emitted point to the final model after the temporary Pareto
        // blocking scope has been restored. If emission repairs or completes a
        // different point, finalization revokes both the point and enumeration.
        self.finalize_optimization(&finite_values, true)
    }

    /// Run one Pareto feasibility probe under `assumptions`, returning only a
    /// verdict corroborated by a disposable exact-scope token. The raw solve is
    /// retained because a SAT seed supplies the same-Context candidate model to
    /// the lex push, while terminal front exhaustion needs its proof state for
    /// the outer Pareto-extension publication funnel. Its bare tri-state is
    /// never sufficient to change the enumeration state.
    fn pareto_probe(&mut self, assumptions: &[TermId]) -> Result<ParetoProbe> {
        let exact_roots = self.optimization_probe_roots(assumptions);
        let raw = self.check_sat_assuming(assumptions)?;
        let checked = self.checked_optimization_roots_decision(&exact_roots);
        match (raw, checked) {
            (SolveResult::Sat, CheckedOptimizationDecision::Sat) => Ok(ParetoProbe::Sat),
            (SolveResult::Unsat(_), CheckedOptimizationDecision::Unsat) => Ok(ParetoProbe::Unsat),
            _ => Ok(ParetoProbe::Unknown),
        }
    }

    /// GIA's improvement region is the CLOSED weak-dominance cone of a feasible
    /// seed, not the open complement of the already emitted front. A seed escapes
    /// every old point strictly somewhere; all points no worse than that seed do
    /// too. Consequently a lex optimum inside this cone is globally Pareto.
    /// This also applies to infinite integer fronts (Int does not imply finite).
    /// See Z3 5.3.3 `src/opt/opt_pareto.cpp`, `gia_pareto::operator()`.
    ///
    /// The raw search model is not imported from the independent SAT decision.
    /// Certify its EXACT objective vector with the original blockers before
    /// discarding them, so the cone cannot acquire authority from another model.
    fn pareto_seed_cone(
        &mut self,
        objectives: &[ay_frontend::Objective],
        blockers: &[TermId],
    ) -> Result<Option<Vec<TermId>>> {
        use super::model::evaluation_copies;
        let Some(model) = self.last_model.as_ref() else {
            return Ok(None);
        };
        let Ok(scope) = evaluation_copies::EvaluationCopyScope::enter(self) else {
            return Ok(None);
        };
        let Some(metadata) = objectives
            .len()
            .checked_mul(std::mem::size_of::<BigRational>())
        else {
            return Ok(None);
        };
        if !evaluation_copies::pay(objectives.len(), metadata) || !evaluation_copies::validate(self)
        {
            return Ok(None);
        }
        let mut values = Vec::with_capacity(objectives.len());
        let mut payload = metadata;
        for objective in objectives {
            let Ok(value) = self.eval_objective_value(model, objective.term) else {
                return Ok(None);
            };
            let sort = self.ctx.terms.sort(objective.term);
            if matches!(sort, Sort::Int | Sort::BitVec(_)) && !value.is_integer() {
                return Ok(None);
            }
            if let Sort::BitVec(bv) = sort {
                if value.is_negative() || value.numer().bits() > u64::from(bv.width) {
                    return Ok(None);
                }
            }
            let limb_bytes = |bits: u64| {
                bits.checked_add(63)
                    .and_then(|bits| usize::try_from(bits / 64).ok())
                    .and_then(|limbs| limbs.checked_mul(8))
            };
            let Some(bytes) = limb_bytes(value.numer().bits())
                .and_then(|numerator| {
                    limb_bytes(value.denom().bits())
                        .and_then(|denominator| numerator.checked_add(denominator))
                })
                .and_then(|bytes| bytes.checked_add(2 * std::mem::size_of::<BigInt>()))
            else {
                return Ok(None);
            };
            let Some(total) = payload.checked_add(bytes) else {
                return Ok(None);
            };
            payload = total;
            values.push(value);
        }
        if !evaluation_copies::validate(self) {
            return Ok(None);
        }
        // Three scalar constants per objective (two exact bounds and the cone
        // bound), the retained vector, and up to four concurrent scalar buffers
        // for integer quotient, bound conversion and term interning. This prices
        // occupied payload, never the declared BV width.
        let scalar_buffers = 1usize + 3 + 4;
        let Some(root_slots) = self
            .ctx
            .assertions
            .len()
            .checked_add(blockers.len())
            .and_then(|base| {
                objectives
                    .len()
                    .checked_mul(3)
                    .and_then(|extra| base.checked_add(extra))
            })
        else {
            return Ok(None);
        };
        let Some(bytes) = payload.checked_mul(scalar_buffers).and_then(|bytes| {
            root_slots
                .checked_mul(std::mem::size_of::<TermId>())
                .and_then(|metadata| bytes.checked_add(metadata))
        }) else {
            return Ok(None);
        };
        let Ok(_arena) = self.admit_evaluation_scratch(bytes) else {
            return Ok(None);
        };
        // Three bound constants read their scalar; integer/BV conversion may
        // additionally scan it to obtain the integral quotient. Pay both passes
        // on the retained original functional counter before constructing terms.
        let Some(work) = payload
            .checked_mul(3 + 3)
            .and_then(|work| work.checked_add(root_slots))
        else {
            return Ok(None);
        };
        if !evaluation_copies::pay(work, 0) {
            return Ok(None);
        }
        // Retain the same-attempt construction arena BEFORE releasing the read
        // scope's scalar charges. No new store snapshot is captured after growth.
        if !evaluation_copies::validate(self) {
            return Ok(None);
        }
        let Ok(construction) = scope.into_construction(self) else {
            return Ok(None);
        };
        let mut exact = Vec::with_capacity(root_slots - objectives.len());
        exact.extend_from_slice(&self.ctx.assertions);
        exact.extend_from_slice(blockers);
        let mut cone = Vec::with_capacity(objectives.len());
        for (objective, value) in objectives.iter().zip(&values) {
            let sort = self.ctx.terms.sort(objective.term).clone();
            exact.push(self.mk_commit_ge(objective.term, value, &sort));
            exact.push(self.mk_commit_le(objective.term, value, &sort));
            cone.push(self.mk_at_least_as_good_atom(objective, value)?);
        }
        let constructed = self.ctx.terms.snapshot_stamp();
        if _arena
            .check_usage(
                self.ctx.terms.true_memory_bytes(),
                bytes,
                self.evaluation_term_memory_limit(),
            )
            .is_err()
            || !matches!(
                self.checked_optimization_roots_decision(&exact),
                CheckedOptimizationDecision::Sat
            )
            || !construction.validate(self)
            || constructed != self.ctx.terms.snapshot_stamp()
        {
            return Ok(None);
        }
        Ok(Some(cone))
    }

    /// Build the exact blocker vector used by the next-front feasibility probe
    /// and seal it to the current public optimization query.
    fn build_pareto_front_exhaustion_extension(
        &mut self,
        objectives: &[ay_frontend::Objective],
        emitted: &[Vec<BigRational>],
    ) -> Result<ParetoFrontExhaustionExtension> {
        self.build_pareto_front_exhaustion_extension_with(
            objectives,
            emitted,
            &[],
            objectives,
            |executor, point| executor.mk_not_dominated_or_equal_by(objectives, point),
        )
    }

    /// [`Self::build_pareto_front_exhaustion_extension`] over a blocker
    /// objective vector (`blocking_objectives`) that may extend the sealed
    /// inventory, with extra conjuncts appended to the blocking vector.
    /// The joint Pareto lane builds blockers over its extended vector
    /// (with synthesized soft-group cost objectives), folds its
    /// soft-relaxation clauses in as extra conjuncts (so the certified
    /// terminal obligation is authored ∧ relaxation ∧ point-blockers),
    /// and seals the caller's REAL objectives — the extended vector
    /// never enters `ctx`. The per-point blockers always come first, in
    /// emission order.
    fn build_pareto_front_exhaustion_extension_with(
        &mut self,
        blocking_objectives: &[ay_frontend::Objective],
        emitted: &[Vec<BigRational>],
        extra_conjuncts: &[TermId],
        sealed_objectives: &[ay_frontend::Objective],
        mut point_blocker: impl FnMut(&mut Self, &[BigRational]) -> Result<TermId>,
    ) -> Result<ParetoFrontExhaustionExtension> {
        let objectives = blocking_objectives;
        let mut blocking = Vec::with_capacity(emitted.len() + extra_conjuncts.len());
        for point in emitted {
            blocking.push(point_blocker(self, point)?);
        }
        blocking.extend_from_slice(extra_conjuncts);
        let hard_root_entries = self
            .ctx
            .assertions
            .iter()
            .map(|&root| self.ctx.terms.entry_stamp(root))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                ExecutorError::UnsupportedOptimization(
                    "Pareto exhaustion roots contain a stale term entry".to_string(),
                )
            })?;
        let objective_entries = sealed_objectives
            .iter()
            .map(|objective| self.ctx.terms.entry_stamp(objective.term))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                ExecutorError::UnsupportedOptimization(
                    "Pareto exhaustion objectives contain a stale term entry".to_string(),
                )
            })?;
        let blocking_objective_entries = objectives
            .iter()
            .map(|objective| self.ctx.terms.entry_stamp(objective.term))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                ExecutorError::UnsupportedOptimization(
                    "Pareto exhaustion objectives contain a stale term entry".to_string(),
                )
            })?;
        let blocking_entries = blocking
            .iter()
            .map(|&term| self.ctx.terms.entry_stamp(term))
            .collect::<Option<Vec<_>>>()
            .ok_or_else(|| {
                ExecutorError::UnsupportedOptimization(
                    "Pareto exhaustion blockers contain a stale term entry".to_string(),
                )
            })?;
        Ok(ParetoFrontExhaustionExtension {
            query_epoch: self.query_authority_epoch.clone(),
            source_context_stamp: self.ctx.source_context_stamp(),
            hard_roots: self.ctx.assertions.clone().into_boxed_slice(),
            hard_root_entries: hard_root_entries.into_boxed_slice(),
            objectives: sealed_objectives.into(),
            objective_entries: objective_entries.into_boxed_slice(),
            blocking_objectives: objectives.into(),
            blocking_objective_entries: blocking_objective_entries.into_boxed_slice(),
            blocking: blocking.into_boxed_slice(),
            blocking_entries: blocking_entries.into_boxed_slice(),
        })
    }

    /// Evaluate an objective term to its scalar value as a `BigRational`,
    /// dispatching on its sort (Int / Real / BitVec). BitVec is read as its
    /// UNSIGNED integer value (the quantity Z3 optimizes — see
    /// [`Self::optimize_bv_objective`]).
    fn eval_objective_value(&self, model: &Model, term: TermId) -> Result<BigRational> {
        match self.ctx.terms.sort(term) {
            Sort::Int => Ok(BigRational::from(self.evaluate_int_term(model, term)?)),
            Sort::Real => self.evaluate_real_term(model, term),
            Sort::BitVec(_) => self
                .try_evaluate_bv_unsigned(model, term)
                .map(BigRational::from)
                .ok_or_else(|| {
                    ExecutorError::UnsupportedOptimization(
                        "BitVector objective could not be evaluated during pareto enumeration"
                            .to_string(),
                    )
                }),
            other => Err(ExecutorError::UnsupportedOptimization(format!(
                "unsupported pareto objective sort: {other:?}"
            ))),
        }
    }

    /// Build the assumption literal asserting the current solution is NOT
    /// dominated-or-equal by the emitted point `point` — i.e. STRICTLY better than
    /// `point` on at least one objective. This is the per-emitted-point blocking
    /// constraint: any new Pareto point must improve on each prior one somewhere.
    ///
    /// "dominated-or-equal by `point`" means `point` is at-least-as-good on every
    /// objective; its negation is "this solution is strictly better than `point`
    /// on >= 1 objective", encoded as the OR over objectives of the strict-improve
    /// atom relative to `point`'s value for that objective.
    fn mk_not_dominated_or_equal_by(
        &mut self,
        objectives: &[ay_frontend::Objective],
        point: &[BigRational],
    ) -> Result<TermId> {
        debug_assert_eq!(objectives.len(), point.len());
        let mut disj: Vec<TermId> = Vec::with_capacity(objectives.len());
        for (obj, val) in objectives.iter().zip(point.iter()) {
            disj.push(self.mk_strict_improve_atom(obj, val)?);
        }
        Ok(self.ctx.terms.mk_or(disj))
    }

    /// Build the assumption literal asserting the current solution STRICTLY
    /// DOMINATES the point `value` — at-least-as-good on EVERY objective AND
    /// strictly better on >= 1. Used to push a seed up to Pareto-optimality.
    #[cfg(debug_assertions)]
    fn mk_strictly_dominates_value(
        &mut self,
        objectives: &[ay_frontend::Objective],
        value: &[BigRational],
    ) -> Result<TermId> {
        debug_assert_eq!(objectives.len(), value.len());
        // Weakly-improve EVERY objective (a conjunction of at-least-as-good atoms).
        let mut conj: Vec<TermId> = Vec::with_capacity(objectives.len() + 1);
        for (obj, val) in objectives.iter().zip(value.iter()) {
            conj.push(self.mk_at_least_as_good_atom(obj, val)?);
        }
        // AND strictly-improve at least ONE objective.
        let strict = self.mk_not_dominated_or_equal_by(objectives, value)?;
        conj.push(strict);
        Ok(self.ctx.terms.mk_and(conj))
    }

    /// Atom: objective `obj` is at-least-as-good as `value` (weak improvement in
    /// `obj`'s optimize direction). Maximize → `obj >= value`; minimize →
    /// `obj <= value`. Dispatches on the objective's sort.
    fn mk_at_least_as_good_atom(
        &mut self,
        obj: &ay_frontend::Objective,
        value: &BigRational,
    ) -> Result<TermId> {
        let sort = self.ctx.terms.sort(obj.term).clone();
        Ok(match (obj.direction, &sort) {
            (ObjectiveDirection::Maximize, Sort::Int) => {
                self.mk_int_ge(obj.term, &value.to_integer())
            }
            (ObjectiveDirection::Minimize, Sort::Int) => {
                self.mk_int_le(obj.term, &value.to_integer())
            }
            (ObjectiveDirection::Maximize, Sort::Real) => self.mk_real_ge(obj.term, value),
            (ObjectiveDirection::Minimize, Sort::Real) => self.mk_real_le(obj.term, value),
            (ObjectiveDirection::Maximize, Sort::BitVec(bv)) => {
                self.mk_bv_uge(obj.term, &value.to_integer(), bv.width)
            }
            (ObjectiveDirection::Minimize, Sort::BitVec(bv)) => {
                self.mk_bv_ule(obj.term, &value.to_integer(), bv.width)
            }
            (_, other) => {
                return Err(ExecutorError::UnsupportedOptimization(format!(
                    "unsupported pareto objective sort: {other:?}"
                )));
            }
        })
    }

    /// Atom: objective `obj` is STRICTLY better than `value` (strict improvement
    /// in `obj`'s optimize direction). Maximize → `obj > value`; minimize →
    /// `obj < value`. Dispatches on the objective's sort.
    fn mk_strict_improve_atom(
        &mut self,
        obj: &ay_frontend::Objective,
        value: &BigRational,
    ) -> Result<TermId> {
        let sort = self.ctx.terms.sort(obj.term).clone();
        Ok(match (obj.direction, &sort) {
            // Strict integer improvement: `> v` is `>= v+1`, `< v` is `<= v-1`.
            (ObjectiveDirection::Maximize, Sort::Int) => {
                self.mk_int_ge(obj.term, &(value.to_integer() + BigInt::one()))
            }
            (ObjectiveDirection::Minimize, Sort::Int) => {
                self.mk_int_le(obj.term, &(value.to_integer() - BigInt::one()))
            }
            (ObjectiveDirection::Maximize, Sort::Real) => self.mk_real_gt(obj.term, value),
            (ObjectiveDirection::Minimize, Sort::Real) => self.mk_real_lt(obj.term, value),
            // Strict BV improvement via unsigned strict comparators.
            (ObjectiveDirection::Maximize, Sort::BitVec(bv)) => {
                let c = self.ctx.terms.mk_bitvec(value.to_integer(), bv.width);
                self.ctx.terms.mk_bvugt(obj.term, c)
            }
            (ObjectiveDirection::Minimize, Sort::BitVec(bv)) => {
                let c = self.ctx.terms.mk_bitvec(value.to_integer(), bv.width);
                self.ctx.terms.mk_bvult(obj.term, c)
            }
            (_, other) => {
                return Err(ExecutorError::UnsupportedOptimization(format!(
                    "unsupported pareto objective sort: {other:?}"
                )));
            }
        })
    }

    /// Find the optimum of ONE objective against the CURRENT hard constraints,
    /// using the exact same exponential+binary search (Int) / simplex+iterative
    /// (Real) routine for both lex and box priorities — there is no divergent
    /// per-objective optimization logic.
    ///
    /// Returns `Some((witness_model, optimum_value))` on success, or `None` if
    /// the objective was inconclusive (`unknown`). Unbounded objectives are
    /// recorded in `unbounded_objectives` and return the current feasible model
    /// with its (finite, non-optimal) value, exactly as the lex path did.
    fn optimize_one_objective(
        &mut self,
        objective_index: usize,
        obj: &ay_frontend::Objective,
    ) -> Result<Option<(Model, BigRational)>> {
        let obj_sort = self.ctx.terms.sort(obj.term).clone();

        // Current model for this objective's initial value (warm start).
        let best_model = self.last_model.clone().unwrap_or_else(Model::empty);

        let optimized = match obj_sort {
            Sort::Int => {
                let sense = match obj.direction {
                    ObjectiveDirection::Maximize => OptimizationSense::Maximize,
                    ObjectiveDirection::Minimize => OptimizationSense::Minimize,
                };
                // Unbounded Int detection via the audited LP relaxation
                // (#unbounded-oo). SOUNDNESS (Meyer's theorem on rational
                // polyhedra): SimplexOpt::Unbounded is only returned when the
                // feasible set is EXACTLY a conjunction of non-strict rational
                // linear constraints (faithfulness audits in
                // `try_optimize_real_via_simplex`, plus the strict-bound /
                // disequality / unsupported gates inside `optimize_impl`) and
                // the objective parsed faithfully too. An integer-feasible
                // point exists (the caller only optimizes after
                // `check_sat_internal` returned Sat), so the LP's rational
                // recession ray with positive objective growth can be scaled
                // to integer components — the INTEGER problem is unbounded as
                // well. Fail-safe: every other verdict falls through to the
                // exact exponential+binary search unchanged.
                //
                // Probed BEFORE `evaluate_int_term`: evaluation can fail on
                // the base model precisely when nothing constrained the
                // objective (the lex case `(maximize x)(maximize y)` with only
                // `y` bounded), which previously surfaced as an
                // "objective could not be evaluated" error.
                if matches!(
                    self.try_optimize_real_via_simplex(obj.term, sense),
                    SimplexOpt::Unbounded
                ) {
                    self.unbounded_objectives
                        .insert(objective_index, obj.direction);
                    // The value is a placeholder: every consumer of an
                    // unbounded objective reads `unbounded_objectives`, never
                    // this number (lex skips the commit, box skips the record,
                    // `objective_optimum` returns Pos/NegInfinity, and
                    // `get-objectives` prints the infinity shape).
                    return Ok(Some((best_model, BigRational::zero())));
                }
                let best_value = self.evaluate_int_term(&best_model, obj.term)?;
                match obj.direction {
                    ObjectiveDirection::Maximize => self.maximize_int_objective(
                        objective_index,
                        obj.term,
                        best_model,
                        best_value,
                    )?,
                    ObjectiveDirection::Minimize => self.minimize_int_objective(
                        objective_index,
                        obj.term,
                        best_model,
                        best_value,
                    )?,
                }
                .map(|(m, v)| (m, BigRational::from(v)))
            }
            Sort::Real => {
                let sense = match obj.direction {
                    ObjectiveDirection::Maximize => OptimizationSense::Maximize,
                    ObjectiveDirection::Minimize => OptimizationSense::Minimize,
                };
                // Probe the audited unbounded verdict BEFORE `evaluate_real_term`,
                // mirroring the Int branch above (#unbounded-oo, #opt-epsilon):
                // evaluation fails on the base model precisely when nothing
                // constrained the objective — the exact shape of an unbounded
                // Real objective (`(assert (< y 100.0)) (maximize x)`), which
                // previously surfaced as an "objective could not be evaluated"
                // error instead of `oo`.
                if matches!(
                    self.try_optimize_real_via_simplex(obj.term, sense),
                    SimplexOpt::Unbounded
                ) {
                    self.unbounded_objectives
                        .insert(objective_index, obj.direction);
                    // Placeholder value: consumers of an unbounded objective
                    // read `unbounded_objectives`, never this number.
                    return Ok(Some((best_model, BigRational::zero())));
                }
                let best_value = self.evaluate_real_term(&best_model, obj.term)?;
                match obj.direction {
                    ObjectiveDirection::Maximize => self.maximize_real_objective(
                        objective_index,
                        obj.term,
                        best_model,
                        best_value,
                    )?,
                    ObjectiveDirection::Minimize => self.minimize_real_objective(
                        objective_index,
                        obj.term,
                        best_model,
                        best_value,
                    )?,
                }
            }
            // BitVector objective: optimize the UNSIGNED value over the finite
            // domain [0, 2^width-1] (matches Z3 — see `optimize_bv_objective`).
            // The optimum is an integer, so it is returned as a whole
            // `BigRational` exactly like the Int path; `finite_objective_values`,
            // `mk_commit_le`/`mk_commit_ge`, and the get-objectives renderer all
            // round-trip it back to the BV decimal.
            Sort::BitVec(bv) => {
                let width = bv.width;
                self.optimize_bv_objective(obj.term, width, obj.direction, best_model)?
                    .map(|(m, v)| (m, BigRational::from(v)))
            }
            _ => unreachable!(),
        };
        Ok(optimized)
    }

    /// Optimize a BitVector objective over its finite UNSIGNED domain.
    ///
    /// ## Z3 semantics (verified empirically, Z3 4.x, 2026-06-15)
    ///
    /// Z3 optimizes the UNSIGNED integer value of a BV objective, NOT the signed
    /// (two's-complement) value. Decisive experiment on `(_ BitVec 4)` with `x`
    /// restricted to `{#x7 (=7), #xf (=15 unsigned / -1 signed)}`:
    /// ```text
    ///   (minimize x) -> (objectives (x 7))   ; picks 7, not -1  => UNSIGNED
    ///   (maximize x) -> (objectives (x 15))  ; picks 15, not 7  => UNSIGNED
    /// ```
    /// Z3 reports the optimum in `(get-objectives)` as a DECIMAL numeral
    /// (`(x 7)`), while `(get-value (x))` reports the bitvector literal
    /// (`((x #x7))`). AY matches both shapes.
    ///
    /// ## Algorithm
    ///
    /// The domain is the finite unsigned range `[0, 2^width - 1]`, so the optimum
    /// always EXISTS (there is no unbounded/oo case for a BV objective). We binary
    /// search the value range, asserting constant unsigned bound atoms via
    /// `check_sat_assuming` (maximize: largest `c` with `bvuge(obj, c)` feasible;
    /// minimize: smallest `c` with `bvule(obj, c)` feasible).
    ///
    /// Feasibility is monotone in the bound (a looser bound is strictly more
    /// permissive), so the binary search converges on the true optimum. Each probe
    /// re-reads the model's actual objective value (never trusting the bound) and
    /// uses it to tighten, so the returned model genuinely achieves the reported
    /// optimum.
    ///
    /// SOUNDNESS: the reported optimum equals the true unsigned min/max
    /// over all models of the hard constraints. For small widths (`width <= 4`) a
    /// debug-assert brute-forces all `2^width` values to cross-check the optimum
    /// (see `bv_brute_force_optimum`). Caller guarantees the hard constraints are
    /// SAT, so a feasible objective value always exists.
    fn optimize_bv_objective(
        &mut self,
        objective: TermId,
        width: u32,
        direction: ObjectiveDirection,
        best_model: Model,
    ) -> Result<Option<(Model, BigInt)>> {
        debug_assert!(width >= 1, "BitVec objective width must be positive");
        // Unsigned domain bounds: [0, 2^width - 1].
        let domain_max: BigInt = (BigInt::one() << width) - BigInt::one();

        let result = match direction {
            ObjectiveDirection::Maximize => {
                self.maximize_bv_objective(objective, width, &domain_max, best_model)?
            }
            ObjectiveDirection::Minimize => {
                self.minimize_bv_objective(objective, width, &domain_max, best_model)?
            }
        };

        // Brute-force cross-check on small widths: enumerate every value in the
        // finite domain and confirm AY's optimum equals the true optimum. Only
        // compiled in debug builds and only for width <= 4 (<= 16 probes), so it
        // never affects release performance.
        #[cfg(debug_assertions)]
        if let Some((_, ref opt_value)) = result {
            if width <= 4 {
                if let Some(true_opt) =
                    self.bv_brute_force_optimum(objective, width, &domain_max, direction)?
                {
                    debug_assert_eq!(
                        *opt_value, true_opt,
                        "BV {direction:?} optimum {opt_value} != brute-force optimum {true_opt} \
                         (width {width})"
                    );
                }
            }
        }

        Ok(result)
    }

    /// Maximize the unsigned value of a BV objective via binary search.
    ///
    /// Invariant: `lo` is a feasible (achievable) value; `hi` is an upper bound on
    /// the optimum (initially the domain max, always feasible to be `<=`). We probe
    /// `bvuge(obj, mid)`: SAT raises `lo` to the witnessed value, UNSAT lowers `hi`.
    fn maximize_bv_objective(
        &mut self,
        objective: TermId,
        width: u32,
        domain_max: &BigInt,
        mut best_model: Model,
    ) -> Result<Option<(Model, BigInt)>> {
        // Seed `lo` from the current feasible model (warm start). The caller
        // guarantees SAT, but an UNCONSTRAINED objective variable may be left
        // unassigned in the base model (no `bv_model` entry), so a warm-start
        // evaluation can be `Unknown`. Fall back to the trivially-feasible
        // minimum 0 (every unsigned value is `>= 0`) and let the binary search
        // drive the objective up; the first SAT probe re-establishes a concrete
        // best_model. This keeps unconstrained BV objectives working (Z3 reports
        // the domain max), rather than erroring.
        let mut best_value = self
            .try_evaluate_bv_unsigned(&best_model, objective)
            .unwrap_or_else(|| BigInt::from(0));
        let mut lo = best_value.clone();
        let mut hi = domain_max.clone();

        while lo < hi {
            // Bias the midpoint UP so a SAT probe makes progress (ceil).
            let mid = (&lo + &hi + BigInt::one()) / BigInt::from(2);
            let bound = self.mk_bv_uge(objective, &mid, width);
            match self.optimization_model_probe(&[bound])? {
                SolveResult::Sat => {
                    let model = self.bv_probe_model()?;
                    let value = self.eval_bv_probe(&model, objective)?;
                    debug_assert!(
                        value >= mid,
                        "BV maximize: model value {value} below asserted bound {mid}"
                    );
                    best_model = model;
                    best_value = value.clone();
                    lo = value;
                }
                SolveResult::Unsat(_) => hi = &mid - BigInt::one(),
                SolveResult::Unknown => {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    return Ok(None);
                }
            }
        }

        Ok(Some((best_model, best_value)))
    }

    /// Minimize the unsigned value of a BV objective via binary search.
    ///
    /// Invariant: `hi` is a feasible (achievable) value; `lo` is a lower bound on
    /// the optimum (initially 0). We probe `bvule(obj, mid)`: SAT lowers `hi` to the
    /// witnessed value, UNSAT raises `lo`.
    fn minimize_bv_objective(
        &mut self,
        objective: TermId,
        width: u32,
        domain_max: &BigInt,
        mut best_model: Model,
    ) -> Result<Option<(Model, BigInt)>> {
        // Warm start; an unconstrained objective may be unassigned in the base
        // model, so fall back to the trivially-feasible maximum (every unsigned
        // value is `<= 2^width-1`) and let the binary search drive it down.
        let mut best_value = self
            .try_evaluate_bv_unsigned(&best_model, objective)
            .unwrap_or_else(|| domain_max.clone());
        let mut lo = BigInt::from(0);
        let mut hi = best_value.clone();

        while lo < hi {
            // Bias the midpoint DOWN so a SAT probe makes progress (floor).
            let mid = (&lo + &hi) / BigInt::from(2);
            let bound = self.mk_bv_ule(objective, &mid, width);
            match self.optimization_model_probe(&[bound])? {
                SolveResult::Sat => {
                    let model = self.bv_probe_model()?;
                    let value = self.eval_bv_probe(&model, objective)?;
                    debug_assert!(
                        value <= mid,
                        "BV minimize: model value {value} above asserted bound {mid}"
                    );
                    best_model = model;
                    best_value = value.clone();
                    hi = value;
                }
                SolveResult::Unsat(_) => lo = &mid + BigInt::one(),
                SolveResult::Unknown => {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    return Ok(None);
                }
            }
        }

        Ok(Some((best_model, best_value)))
    }

    /// Brute-force the true unsigned optimum of a BV objective by enumerating
    /// every value in the finite domain and probing feasibility (debug-only
    /// soundness oracle for small widths).
    ///
    /// Returns the true optimum, or `None` if any probe was inconclusive (so the
    /// debug-assert is skipped rather than firing on an `unknown`). Used ONLY by
    /// `optimize_bv_objective`'s `debug_assert_eq!` cross-check.
    #[cfg(debug_assertions)]
    fn bv_brute_force_optimum(
        &mut self,
        objective: TermId,
        width: u32,
        domain_max: &BigInt,
        direction: ObjectiveDirection,
    ) -> Result<Option<BigInt>> {
        // Enumerate the whole domain. For maximize, the first feasible value seen
        // scanning DOWN from the max is the optimum; for minimize, scanning UP from
        // 0. We pin obj == candidate via bvule && bvuge and check feasibility.
        let mut candidate = match direction {
            ObjectiveDirection::Maximize => domain_max.clone(),
            ObjectiveDirection::Minimize => BigInt::from(0),
        };
        loop {
            let le = self.mk_bv_ule(objective, &candidate, width);
            let ge = self.mk_bv_uge(objective, &candidate, width);
            match self.checked_optimization_decision(&[le, ge]) {
                CheckedOptimizationDecision::Sat => return Ok(Some(candidate)),
                CheckedOptimizationDecision::Unknown => return Ok(None),
                CheckedOptimizationDecision::Unsat => match direction {
                    ObjectiveDirection::Maximize => {
                        if candidate == BigInt::from(0) {
                            return Ok(None); // exhausted (no feasible value)
                        }
                        candidate -= BigInt::one();
                    }
                    ObjectiveDirection::Minimize => {
                        if candidate >= *domain_max {
                            return Ok(None);
                        }
                        candidate += BigInt::one();
                    }
                },
            }
        }
    }

    /// Capture the model from the most recent `check_sat_assuming` SAT probe.
    fn bv_probe_model(&self) -> Result<Model> {
        self.last_model.clone().ok_or_else(|| {
            ExecutorError::UnsupportedOptimization(
                "SAT without model during BV optimization".to_string(),
            )
        })
    }

    /// Read the UNSIGNED integer value of a BV-sorted objective term from a model,
    /// or `None` if the model does not assign it a concrete bitvector value.
    ///
    /// `evaluate_term` returns the bitvector value as a non-negative `BigInt` in
    /// `[0, 2^width)` (the unsigned interpretation), which is exactly the quantity
    /// Z3 optimizes. An unconstrained objective variable can be left unassigned in
    /// the base SAT model; callers treat that as "no warm start" rather than an
    /// error and let the binary search seed from a domain endpoint instead.
    fn try_evaluate_bv_unsigned(&self, model: &Model, term: TermId) -> Option<BigInt> {
        match self.evaluate_term(model, term) {
            EvalValue::BitVec { value, .. } => Some(value),
            _ => None,
        }
    }

    /// Read the unsigned BV value from a PROBE model that just satisfied a bound
    /// atom on the objective. Such a model must assign the objective (the bound
    /// constrains it), so a missing value is a genuine internal inconsistency and
    /// is surfaced as an error rather than silently mis-driving the search.
    fn eval_bv_probe(&self, model: &Model, term: TermId) -> Result<BigInt> {
        self.try_evaluate_bv_unsigned(model, term).ok_or_else(|| {
            ExecutorError::UnsupportedOptimization(
                "BitVector objective could not be evaluated in a bound-satisfying model"
                    .to_string(),
            )
        })
    }

    /// Build `bvule(lhs, const)` with a `width`-bit constant `rhs`.
    fn mk_bv_ule(&mut self, lhs: TermId, rhs: &BigInt, width: u32) -> TermId {
        let c = self.ctx.terms.mk_bitvec(rhs.clone(), width);
        self.ctx.terms.mk_bvule(lhs, c)
    }

    /// Build `bvuge(lhs, const)` with a `width`-bit constant `rhs`.
    fn mk_bv_uge(&mut self, lhs: TermId, rhs: &BigInt, width: u32) -> TermId {
        let c = self.ctx.terms.mk_bitvec(rhs.clone(), width);
        self.ctx.terms.mk_bvuge(lhs, c)
    }

    /// Reset user-facing state for an inconclusive (`unknown`) objective solve.
    fn optimization_inconclusive(&mut self) -> SolveResult {
        self.last_assumptions = None;
        self.last_assumption_core = None;
        if self.last_unknown_reason.is_none() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
        }
        // A prior objective/probe may have produced a valid optimum and SAT
        // token before a later objective became inconclusive. Those are partial
        // search artefacts, not a result for the public multi-objective query.
        self.last_sat_certificate = None;
        self.last_model_validated = false;
        self.last_model = None;
        self.unbounded_objectives.clear();
        self.infinitesimal_objectives.clear();
        self.unavailable_objectives.clear();
        self.finite_objective_values.clear();
        self.objective_certificates.clear();
        self.pareto_state = None;
        self.last_result = Some(SolveResult::Unknown);
        SolveResult::Unknown
    }

    /// Finalize a fully-optimized SAT run and publish its indexed finite
    /// outcomes only after the public witness is admitted.
    ///
    /// `bind_final_model` is true for lex/Pareto, whose finite values describe
    /// one joint witness. BOX deliberately passes false because its independent
    /// optima need not be simultaneously attainable by any model.
    fn finalize_optimization(
        &mut self,
        finite_values: &[(usize, BigRational)],
        bind_final_model: bool,
    ) -> Result<SolveResult> {
        // Internal optimization uses the assumption API; hide it from user-facing state.
        self.last_assumptions = None;
        self.last_assumption_core = None;

        // All objectives optimized successfully.
        self.last_result = Some(SolveResult::Sat);
        self.last_unknown_reason = None;
        // Optimization installs captured objective witnesses after multiple
        // assumption probes. `last_model_validated` may describe the most recent
        // probe rather than the installed final model, so invalidate it before
        // the one public validation+mint boundary.
        self.last_model_validated = false;
        // Do not expose values captured by internal probes while emission is
        // still fallible. This map is the sole finite-outcome authority for all
        // public readers.
        self.finite_objective_values.clear();

        let value_roots = if bind_final_model {
            let Some(roots) = self.optimization_value_roots(finite_values) else {
                return Ok(self.reject_optimization_final_witness());
            };
            roots
        } else {
            Vec::new()
        };
        // SINGLE SAT-EMISSION CHOKEPOINT (#sat-chokepoint): funnel the optimized
        // SAT through `emit_sat_verdict` so it runs the strict + independent +
        // authoritative-failclosed gates (previously it ran the strict gate via
        // finalize_sat_model_validation only, never the independent gate) and
        // mints the SatCertificate (#4642 D5).
        let emitted = match self.emit_captured_optimization_witness(SolveResult::Sat, &value_roots)
        {
            Ok(result) => result,
            Err(error) => {
                self.invalidate_last_check_result();
                return Err(error);
            }
        };
        if emitted != SolveResult::Sat {
            return Ok(self.optimization_inconclusive());
        }

        #[cfg(test)]
        if bind_final_model
            && self
                .forced_optimization_post_emit_objective_flip
                .replace(false)
        {
            let objective_index = finite_values
                .first()
                .expect("objective canary requires one finite objective")
                .0;
            let term = self
                .ctx
                .objectives()
                .get(objective_index)
                .expect("objective canary index must be valid")
                .term;
            let model = self
                .last_model
                .as_mut()
                .expect("objective canary requires a final model");
            let value = model
                .lia_model
                .as_mut()
                .and_then(|lia| lia.values.get_mut(&term))
                .expect("objective canary requires a direct LIA objective");
            *value += BigInt::one();
            super::model::eval_memo_clear();
        }

        // Emission may complete or strictly repair a model. Re-account every
        // exact finite lex/Pareto value against that FINAL model before making
        // any outcome queryable. The roots above constrain emission itself;
        // this comparison also detects any mutation after the funnel.
        if bind_final_model && !self.optimization_final_values_match(finite_values) {
            return Ok(self.reject_optimization_final_witness());
        }

        self.finite_objective_values
            .extend(finite_values.iter().cloned());
        Ok(emitted)
    }

    /// Construct exact-value roots for the finite objective declarations.
    /// Both directional bounds are used so the final witness is tied to the
    /// captured scalar, independently of the objective direction.
    fn optimization_value_roots(
        &mut self,
        finite_values: &[(usize, BigRational)],
    ) -> Option<Vec<TermId>> {
        let mut seen = HashSet::default();
        let mut roots = Vec::with_capacity(finite_values.len());
        for (objective_index, value) in finite_values {
            if !seen.insert(*objective_index) {
                return None;
            }
            let objective = self.ctx.objectives().get(*objective_index)?.clone();
            let sort = self.ctx.terms.sort(objective.term).clone();
            if matches!(sort, Sort::Int | Sort::BitVec(_)) && !value.is_integer() {
                return None;
            }
            let lower = self.mk_commit_ge(objective.term, value, &sort);
            let upper = self.mk_commit_le(objective.term, value, &sort);
            roots.push(self.ctx.terms.mk_and(vec![lower, upper]));
        }
        Some(roots)
    }

    /// Re-evaluate the captured finite outcomes against the final public model.
    fn optimization_final_values_match(&self, finite_values: &[(usize, BigRational)]) -> bool {
        let Some(model) = self.last_model.as_ref() else {
            return false;
        };
        finite_values.iter().all(|(objective_index, expected)| {
            let Some(objective) = self.ctx.objectives().get(*objective_index) else {
                return false;
            };
            self.eval_objective_value(model, objective.term)
                .is_ok_and(|actual| actual == *expected)
        })
    }

    /// Revoke every optimization/SAT artefact after a final witness mismatch.
    fn reject_optimization_final_witness(&mut self) -> SolveResult {
        self.invalidate_last_check_result();
        self.last_unknown_reason = Some(UnknownReason::InternalError);
        self.last_result = Some(SolveResult::Unknown);
        SolveResult::Unknown
    }

    fn emit_captured_optimization_witness(
        &mut self,
        proposed: SolveResult,
        obligations: &[TermId],
    ) -> Result<SolveResult> {
        if proposed != SolveResult::Sat {
            return self.emit_sat_verdict(proposed, obligations);
        }
        let model = self.last_model.take();
        self.emit_optimization_sat_verdict(OptimizationModelPublication { model, obligations })
    }

    /// Create `lhs >= value` for committing an optimal value as a hard constraint.
    fn mk_commit_ge(&mut self, lhs: TermId, value: &BigRational, sort: &Sort) -> TermId {
        match sort {
            Sort::Int => self.mk_int_ge(lhs, &value.to_integer()),
            Sort::Real => self.mk_real_ge(lhs, value),
            // Lex commit for a BV objective: pin the unsigned value with
            // `bvuge` (its optimum is a whole, in-domain integer).
            Sort::BitVec(bv) => self.mk_bv_uge(lhs, &value.to_integer(), bv.width),
            _ => unreachable!(),
        }
    }

    /// Create `lhs <= value` for committing an optimal value as a hard constraint.
    fn mk_commit_le(&mut self, lhs: TermId, value: &BigRational, sort: &Sort) -> TermId {
        match sort {
            Sort::Int => self.mk_int_le(lhs, &value.to_integer()),
            Sort::Real => self.mk_real_le(lhs, value),
            // Lex commit for a BV objective: pin the unsigned value with `bvule`.
            Sort::BitVec(bv) => self.mk_bv_ule(lhs, &value.to_integer(), bv.width),
            _ => unreachable!(),
        }
    }

    fn maximize_int_objective(
        &mut self,
        objective_index: usize,
        objective: TermId,
        mut best_model: Model,
        mut best_value: BigInt,
    ) -> Result<Option<(Model, BigInt)>> {
        let max_rounds: usize = 128;
        let mut lo = best_value.clone();
        let mut hi: Option<BigInt> = None;
        let mut delta = BigInt::one();

        // Find an infeasible upper bound with exponential search.
        for _ in 0..max_rounds {
            let candidate = &lo + &delta;
            let ge = self.mk_int_ge(objective, &candidate);
            match self.check_sat_assuming(&[ge])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_int_term(&model, objective)?;
                    if value < candidate {
                        return Err(ExecutorError::UnsupportedOptimization(format!(
                            "objective did not satisfy bound: got {value}, expected >= {candidate}"
                        )));
                    }
                    best_model = model;
                    best_value = value.clone();
                    lo = value;
                    delta <<= 1;
                }
                SolveResult::Unsat(_) => {
                    if !self.checked_optimization_unsat(&[ge]) {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        return Ok(None);
                    }
                    hi = Some(candidate);
                    break;
                }
                SolveResult::Unknown => return Ok(None),
            }
        }

        let Some(mut hi) = hi else {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(None);
        };

        // Binary search between lo (feasible) and hi (infeasible).
        while hi > &lo + BigInt::one() {
            let mid = (&lo + &hi) / BigInt::from(2);
            let ge = self.mk_int_ge(objective, &mid);
            match self.check_sat_assuming(&[ge])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_int_term(&model, objective)?;
                    best_model = model;
                    best_value = value.clone();
                    lo = value;
                }
                SolveResult::Unsat(_) => {
                    if !self.checked_optimization_unsat(&[ge]) {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        return Ok(None);
                    }
                    hi = mid;
                }
                SolveResult::Unknown => {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    return Ok(None);
                }
            }
        }

        self.try_emit_int_optimality_certificate(
            objective_index,
            objective,
            OptimizationSense::Maximize,
            &best_value,
        );
        Ok(Some((best_model, best_value)))
    }

    fn minimize_int_objective(
        &mut self,
        objective_index: usize,
        objective: TermId,
        mut best_model: Model,
        mut best_value: BigInt,
    ) -> Result<Option<(Model, BigInt)>> {
        let max_rounds: usize = 128;
        let mut hi = best_value.clone();
        let mut lo: Option<BigInt> = None;
        let mut delta = BigInt::one();

        // Find an infeasible lower bound with exponential search.
        for _ in 0..max_rounds {
            let candidate = &hi - &delta;
            let le = self.mk_int_le(objective, &candidate);
            match self.check_sat_assuming(&[le])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_int_term(&model, objective)?;
                    if value > candidate {
                        return Err(ExecutorError::UnsupportedOptimization(format!(
                            "objective did not satisfy bound: got {value}, expected <= {candidate}"
                        )));
                    }
                    best_model = model;
                    best_value = value.clone();
                    hi = value;
                    delta <<= 1;
                }
                SolveResult::Unsat(_) => {
                    if !self.checked_optimization_unsat(&[le]) {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        return Ok(None);
                    }
                    lo = Some(candidate);
                    break;
                }
                SolveResult::Unknown => return Ok(None),
            }
        }

        let Some(mut lo) = lo else {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(None);
        };

        // Binary search between lo (infeasible) and hi (feasible).
        while hi > &lo + BigInt::one() {
            let mid = (&lo + &hi) / BigInt::from(2);
            let le = self.mk_int_le(objective, &mid);
            match self.check_sat_assuming(&[le])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_int_term(&model, objective)?;
                    best_model = model;
                    best_value = value.clone();
                    hi = value;
                }
                SolveResult::Unsat(_) => {
                    if !self.checked_optimization_unsat(&[le]) {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        return Ok(None);
                    }
                    lo = mid;
                }
                SolveResult::Unknown => {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    return Ok(None);
                }
            }
        }

        self.try_emit_int_optimality_certificate(
            objective_index,
            objective,
            OptimizationSense::Minimize,
            &best_value,
        );
        Ok(Some((best_model, best_value)))
    }

    /// Emit a dual (Farkas) optimality certificate for an INTEGER objective when
    /// the LP relaxation's dual bound is TIGHT at the integer optimum
    /// (#lra-opt-cert, LIA extension — geometry_consumer MD-7).
    ///
    /// The branch-and-bound above returns the exact IP optimum `ip_optimum` with
    /// a witnessing integer model, so `objective <= ip_optimum` (minimize) /
    /// `objective >= ip_optimum` (maximize) is already attained. The HARD half is
    /// the opposite bound. Running the LRA simplex on the LP RELAXATION (Int vars
    /// relaxed to reals — a SUPERSET of the integer feasible set) yields a dual
    /// Farkas certificate that proves `objective >= lp_bound` (minimize) /
    /// `objective <= lp_bound` (maximize) from the asserted inequality atoms,
    /// valid for every real point and hence for every integer point. When
    /// `lp_bound == ip_optimum` that certificate proves exactly the hard half, so
    /// with the integer witness it certifies the IP optimum — emit it (the same
    /// checkable object the Real path emits; it already passed its own
    /// independent verifier inside `try_optimize_real_via_simplex`).
    ///
    /// When the LP bound is NOT tight — an integrality gap, e.g. `lp_bound <
    /// ip_optimum` for minimize — the LP duals prove only the weaker
    /// `objective >= lp_bound`, which does not entail the strictly better integer
    /// bound. We do NOT fabricate a certificate for it: nothing is inserted, and
    /// `(get-objective-certificates)` keeps the honest "no objective certificates
    /// available" error. Sound either way: a certificate is stored only when an
    /// independently-checkable dual proves the reported integer optimum.
    fn try_emit_int_optimality_certificate(
        &mut self,
        objective_index: usize,
        objective: TermId,
        sense: OptimizationSense,
        ip_optimum: &BigInt,
    ) {
        let ip_rational = BigRational::from(ip_optimum.clone());
        if let SimplexOpt::Optimal(lp_bound, Some(cert), _) =
            self.try_optimize_real_via_simplex(objective, sense)
        {
            // Tight LP relaxation: the dual bound equals the integer optimum, so
            // the certificate proves the objective cannot cross the achieved
            // integer value. `cert.bound == lp_bound` and the certificate already
            // passed its independent verifier upstream; re-assert both here so an
            // integrality gap (lp_bound strictly weaker) can never be emitted.
            if lp_bound == ip_rational && cert.bound == ip_rational {
                self.objective_certificates.insert(objective_index, cert);
            }
        }
    }

    fn mk_int_ge(&mut self, lhs: TermId, rhs: &BigInt) -> TermId {
        let rhs = self.ctx.terms.mk_int(rhs.clone());
        self.ctx
            .terms
            .mk_app(Symbol::named(">="), vec![lhs, rhs], Sort::Bool)
    }

    fn mk_int_le(&mut self, lhs: TermId, rhs: &BigInt) -> TermId {
        let rhs = self.ctx.terms.mk_int(rhs.clone());
        self.ctx
            .terms
            .mk_app(Symbol::named("<="), vec![lhs, rhs], Sort::Bool)
    }

    // --- Real (BigRational) objective optimization ---

    /// Evaluate a term that should return a rational value.
    fn evaluate_real_term(&self, model: &Model, term: TermId) -> Result<BigRational> {
        use super::model::EvalValue;
        match self.evaluate_term(model, term) {
            EvalValue::Rational(r) => Ok(r),
            EvalValue::Unknown => Err(ExecutorError::UnsupportedOptimization(
                "Real objective could not be evaluated".to_string(),
            )),
            _ => Err(ExecutorError::UnsupportedOptimization(
                "Real objective did not evaluate to a number".to_string(),
            )),
        }
    }

    /// Try to find the optimal value of a Real objective using the LRA simplex
    /// optimizer directly (#8278). This avoids the iterative strict-improvement
    /// loop which converges poorly for multi-variable objectives: asserting
    /// `obj > best` may be satisfied by epsilon improvement in one variable,
    /// never reaching the true optimum across all variables simultaneously.
    ///
    /// Creates a standalone LRA solver, asserts all current constraints, parses
    /// the objective into a `LinearExpr`, and runs simplex optimization in one
    /// shot.
    ///
    /// Returns:
    /// * [`SimplexOpt::Optimal`] — the exact finite optimum.
    /// * [`SimplexOpt::Unbounded`] — the objective is unbounded in `sense`'s
    ///   direction, AND the standalone tableau provably saw the WHOLE problem
    ///   (both faithfulness audits below passed). This MUST be propagated
    ///   rather than discarded: the iterative strict-improvement fallback
    ///   would otherwise walk off to an arbitrary finite value and report it
    ///   as the optimum (#wrong-optimization-result).
    /// * [`SimplexOpt::NotApplicable`] — simplex could not decide (non-linear
    ///   terms, unsupported atoms, skipped Boolean structure, opaque objective
    ///   sub-terms, iteration limit); caller should fall back to the iterative
    ///   approach.
    fn try_optimize_real_via_simplex(
        &mut self,
        objective: TermId,
        sense: OptimizationSense,
    ) -> SimplexOpt {
        let mut lra = LraSolver::new(&self.ctx.terms);
        // This is a standalone simplex query, not a DPLL(T) final check. Keep
        // disequality/unsupported-atom soundness gates, but suppress
        // propagation and speculative model-equality requests that require a
        // Boolean driver to replay. Those requests can leave the LRA state
        // dirty and are not optimization constraints.
        lra.set_standalone_simplex_mode();

        // Assert all current constraints into the standalone LRA solver,
        // FLATTENING Boolean conjunction structure exactly (#opt-epsilon):
        // a positive `(and a b)` is the constraint set {a, b}; a `(not t)`
        // flips polarity; a NEGATIVE `(or a b)` is {¬a, ¬b} (De Morgan).
        // Each rewrite preserves the exact constraint set — no relaxation is
        // ever introduced — and any leaf the LRA cannot parse (positive `or`,
        // xor, Bool vars, ...) still lands in `asserted`, where the
        // faithfulness audits below account for it. Without this, a top-level
        // conjunction hid its bounds from the standalone tableau entirely
        // (`(assert (and (<= x 3) (>= x 0))) (maximize x)` returned unknown).
        let mut work: Vec<(TermId, bool)> = self
            .ctx
            .assertions
            .iter()
            .rev()
            .map(|&assertion| (assertion, true))
            .collect();
        while let Some((term, polarity)) = work.pop() {
            match self.ctx.terms.get(term) {
                TermData::Not(inner) => work.push((*inner, !polarity)),
                TermData::App(sym, args) if polarity && sym.name() == "and" => {
                    work.extend(args.iter().rev().map(|&arg| (arg, true)));
                }
                TermData::App(sym, args) if !polarity && sym.name() == "or" => {
                    work.extend(args.iter().rev().map(|&arg| (arg, false)));
                }
                _ => lra.assert_literal(term, polarity),
            }
        }

        // Parse the objective term into a LinearExpr using the LRA solver's
        // variable interning, then run the simplex optimizer. The optimizer
        // performs the feasibility check itself; checking here as well was not
        // merely redundant because LRA checks can emit model-equality requests
        // and deliberately keep the solver dirty for the driver's next pass.
        let linear_expr = lra.parse_linear_expr(objective);
        match lra.optimize_with_certificate(&linear_expr, sense) {
            (OptimizationResult::Optimal(value), certificate) => {
                // Fail closed: only surface a certificate the independent
                // checker accepts, so `(get-objective-certificates)` can never
                // report an unverified combination.
                let certificate = certificate
                    .filter(|cert| cert.bound == value && cert.verify(&self.ctx.terms, objective));
                // #opt-epsilon soundness gate (strict bounds newly reach this
                // lane): without a verified dual certificate, maximality of
                // `value` is unproven — the caller's attainability confirm is
                // one-sided — so demand the full-solver maximality twin.
                let needs_maximality_twin = lra.has_strict_var_bound() && certificate.is_none();
                SimplexOpt::Optimal(value, certificate, needs_maximality_twin)
            }
            (OptimizationResult::OptimalInf { value, eps_coeff }, _) => {
                // An unattained-optimum claim gets no full-solver attainment
                // confirmation (there is nothing to attain), so like
                // `Unbounded` it is only meaningful if the standalone tableau
                // provably saw the WHOLE problem (same audits, same reason).
                let incomplete_problem =
                    !(lra.all_asserted_atoms_parsed() && lra.all_interned_vars_are_declared_vars());
                let contains_integer_var = lra
                    .term_to_var()
                    .keys()
                    .any(|term| matches!(self.ctx.terms.sort(*term), Sort::Int));
                if incomplete_problem || contains_integer_var {
                    SimplexOpt::NotApplicable
                }
                // Int guard: a strict bound over an integer-valued quantity
                // tightens to a CLOSED integer bound (`i < 3` ⇒ `i <= 2`), so
                // the LP delta-sup over-estimates the true sup (`maximize x,
                // x < i, i < 3` reads 3−2ε where the truth is 2−ε). The LP
                // relaxation proves nothing here; fail closed to the
                // iterative fallback.
                // Sign guard (theorem: minimize ⇒ k > 0, maximize ⇒ k < 0;
                // the LRA already fail-closes on violation, re-checked here so
                // this lane never trusts a wrong-signed shape).
                else if match sense {
                    OptimizationSense::Maximize => !eps_coeff.is_negative(),
                    OptimizationSense::Minimize => !eps_coeff.is_positive(),
                } {
                    debug_assert!(
                        false,
                        "OptimalInf ε-sign violates the sense theorem: {sense:?} k={eps_coeff}"
                    );
                    SimplexOpt::NotApplicable
                } else {
                    SimplexOpt::OptimalInf { value, eps_coeff }
                }
            }
            (OptimizationResult::Unbounded, _) => {
                // Unbounded is trusted WITHOUT full-solver confirmation (there
                // is no finite optimum to confirm), so it is sound ONLY if the
                // standalone LRA saw the whole assertion set AND the whole
                // objective:
                // * skipped Boolean structure (or/and/xor/=>, Bool `=`, Bool
                //   vars — deliberately unmarked in DPLL(T) lanes, #8452/#8003)
                //   makes the polyhedron a RELAXATION, and a relaxation being
                //   unbounded proves nothing (#wrong-optimization-result);
                // * opaque sub-terms (nonlinear `*`, div/mod, abs, term ITEs,
                //   unknown functions) intern as FRESH FREE variables, so a
                //   bounded `(maximize (* x x))` would read as maximizing a
                //   free variable — trivially "unbounded".
                // (SimplexOpt::Optimal needs no audit: both Real callers
                // re-confirm it via check_sat_assuming before reporting, and
                // the Int certificate path additionally requires cert.verify().)
                if lra.all_asserted_atoms_parsed() && lra.all_interned_vars_are_declared_vars() {
                    SimplexOpt::Unbounded
                } else {
                    SimplexOpt::NotApplicable
                }
            }
            // Infeasible/Unknown: simplex disagrees with the full solver's SAT
            // verdict or could not finish. Defer to the iterative fallback.
            (OptimizationResult::Infeasible | OptimizationResult::Unknown, _) => {
                SimplexOpt::NotApplicable
            }
        }
    }

    /// Maximize a Real objective.
    ///
    /// First tries the LRA simplex optimizer for an exact one-shot answer
    /// (#8278). Falls back to iterative strict improvement if simplex is not
    /// applicable (non-linear terms, unsupported atoms, etc.).
    fn maximize_real_objective(
        &mut self,
        objective_index: usize,
        objective: TermId,
        mut best_model: Model,
        mut best_value: BigRational,
    ) -> Result<Option<(Model, BigRational)>> {
        // Try simplex-based optimization first (#8278).
        match self.try_optimize_real_via_simplex(objective, OptimizationSense::Maximize) {
            SimplexOpt::Optimal(optimal, certificate, needs_maximality_twin) => {
                // Assert obj >= optimal and re-solve to get a proper model at the optimum.
                let ge = self.mk_real_ge(objective, &optimal);
                match self.check_sat_assuming(&[ge])? {
                    SolveResult::Sat => {
                        let model = self.last_model.clone().ok_or_else(|| {
                            ExecutorError::UnsupportedOptimization(
                                "SAT without model during optimization".to_string(),
                            )
                        })?;
                        let value = self.evaluate_real_term(&model, objective)?;
                        // #opt-epsilon soundness gate: with strict bounds in
                        // the tableau and no verified certificate, the confirm
                        // above is one-sided (attainability only) — an
                        // UNDERestimated `optimal` would go out unchecked.
                        // Publish only with a full-solver maximality proof
                        // (`obj > optimal` UNSAT); anything else distrusts the
                        // simplex and falls back (the fallback only ever
                        // decides on its own full-solver UNSAT).
                        let publish = if needs_maximality_twin {
                            value == optimal && {
                                let gt = self.mk_real_gt(objective, &optimal);
                                self.checked_optimization_unsat(&[gt])
                            }
                        } else {
                            true
                        };
                        if publish {
                            // The full solver confirmed the simplex optimum:
                            // record its dual certificate (#lra-opt-cert).
                            if value == optimal {
                                if let Some(cert) = certificate {
                                    self.objective_certificates.insert(objective_index, cert);
                                }
                            }
                            return Ok(Some((model, value)));
                        }
                        // Fall through to iterative approach.
                    }
                    SolveResult::Unsat(_) | SolveResult::Unknown => {
                        // Simplex found an optimum but the full solver disagrees.
                        // Fall through to iterative approach.
                    }
                }
            }
            SimplexOpt::OptimalInf { value, eps_coeff } => {
                // Unattained supremum `value` (approached within every ε>0 but
                // never reached). Publish `value + eps_coeff·ε` only under TWO
                // full-solver twins (#opt-epsilon):
                // 1. Refutation: nothing may attain (or exceed) the finite
                //    part — `obj >= value` must be UNSAT.
                // 2. δ-closeness: a feasible point within 1 of the sup must
                //    exist — `obj > value - 1` must be SAT. Twin 1 alone is
                //    one-directional (an OVERestimating delta-simplex bug
                //    passes it); twin 2 bounds any overestimate below 1.
                // Residual trust: exactness beyond δ=1 rests on the same
                // audited-tableau class as the `oo` path. On any other outcome
                // distrust the simplex and fall through to the iterative
                // fallback, which only decides on a full-solver UNSAT.
                let ge = self.mk_real_ge(objective, &value);
                if self.checked_optimization_unsat(&[ge]) {
                    let near = &value - BigRational::one();
                    let gt_near = self.mk_real_gt(objective, &near);
                    if self.checked_optimization_decision(&[gt_near])
                        == CheckedOptimizationDecision::Sat
                    {
                        self.infinitesimal_objectives
                            .insert(objective_index, (value, eps_coeff));
                        // The returned scalar is a placeholder exactly like the
                        // Unbounded arm's: every consumer of an infinitesimal
                        // objective reads `infinitesimal_objectives`, never
                        // this number, and the model is an ordinary feasible
                        // witness (z3 parity: no near-sup model exists).
                        return Ok(Some((best_model, best_value)));
                    }
                }
                // Fall through to iterative approach.
            }
            SimplexOpt::Unbounded => {
                // The objective is unbounded above. Record it so `get-objectives`
                // reports `oo`, and return the current feasible model so the
                // problem stays SAT (the unbounded direction does not change the
                // feasibility verdict). Do NOT fall into the iterative loop,
                // which would walk off to an arbitrary finite value.
                self.unbounded_objectives
                    .insert(objective_index, ObjectiveDirection::Maximize);
                return Ok(Some((best_model, best_value)));
            }
            SimplexOpt::NotApplicable => {
                // Fall through to iterative approach.
            }
        }

        // Iterative fallback: assert strict improvement until UNSAT.
        let max_rounds: usize = 128;
        for _ in 0..max_rounds {
            let gt = self.mk_real_gt(objective, &best_value);
            match self.check_sat_assuming(&[gt])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_real_term(&model, objective)?;
                    if value <= best_value {
                        return Err(ExecutorError::UnsupportedOptimization(format!(
                            "Real objective did not strictly improve: got {value}, expected > {best_value}"
                        )));
                    }
                    best_model = model;
                    best_value = value;
                }
                SolveResult::Unsat(_) => {
                    if !self.checked_optimization_unsat(&[gt]) {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        return Ok(None);
                    }
                    return Ok(Some((best_model, best_value)));
                }
                SolveResult::Unknown => return Ok(None),
            }
        }

        // Round budget exhausted WITHOUT an UNSAT proof that no better value
        // exists: `best_value` is a feasible value, NOT the optimum. Claiming
        // it as the optimum is the wrong-value failure the ny P0 tests caught
        // (epsilon-crawl reported -1/2^128 where the true maximum was 1; #R1,
        // the development design notes). Fail closed: the caller
        // maps None to `unknown`.
        Ok(None)
    }

    /// Minimize a Real objective.
    ///
    /// First tries the LRA simplex optimizer for an exact one-shot answer
    /// (#8278). Falls back to iterative strict improvement if simplex is not
    /// applicable.
    fn minimize_real_objective(
        &mut self,
        objective_index: usize,
        objective: TermId,
        mut best_model: Model,
        mut best_value: BigRational,
    ) -> Result<Option<(Model, BigRational)>> {
        // Try simplex-based optimization first (#8278).
        match self.try_optimize_real_via_simplex(objective, OptimizationSense::Minimize) {
            SimplexOpt::Optimal(optimal, certificate, needs_maximality_twin) => {
                // Assert obj <= optimal and re-solve to get a proper model at the optimum.
                let le = self.mk_real_le(objective, &optimal);
                match self.check_sat_assuming(&[le])? {
                    SolveResult::Sat => {
                        let model = self.last_model.clone().ok_or_else(|| {
                            ExecutorError::UnsupportedOptimization(
                                "SAT without model during optimization".to_string(),
                            )
                        })?;
                        let value = self.evaluate_real_term(&model, objective)?;
                        // #opt-epsilon soundness gate — minimality twin (see
                        // the maximize twin for the full argument): strict
                        // bounds + no verified certificate ⇒ require the
                        // full-solver `obj < optimal` UNSAT proof.
                        let publish = if needs_maximality_twin {
                            value == optimal && {
                                let lt = self.mk_real_lt(objective, &optimal);
                                self.checked_optimization_unsat(&[lt])
                            }
                        } else {
                            true
                        };
                        if publish {
                            // The full solver confirmed the simplex optimum:
                            // record its dual certificate (#lra-opt-cert).
                            if value == optimal {
                                if let Some(cert) = certificate {
                                    self.objective_certificates.insert(objective_index, cert);
                                }
                            }
                            return Ok(Some((model, value)));
                        }
                        // Fall through to iterative approach.
                    }
                    SolveResult::Unsat(_) | SolveResult::Unknown => {
                        // Simplex found an optimum but the full solver disagrees.
                        // Fall through to iterative approach.
                    }
                }
            }
            SimplexOpt::OptimalInf { value, eps_coeff } => {
                // Unattained infimum: mirror of the maximize arm's two
                // full-solver twins (#opt-epsilon): `obj <= value` must be
                // UNSAT (refutation) and `obj < value + 1` must be SAT
                // (δ-closeness, bounding any underestimate below 1).
                let le = self.mk_real_le(objective, &value);
                if self.checked_optimization_unsat(&[le]) {
                    let near = &value + BigRational::one();
                    let lt_near = self.mk_real_lt(objective, &near);
                    if self.checked_optimization_decision(&[lt_near])
                        == CheckedOptimizationDecision::Sat
                    {
                        self.infinitesimal_objectives
                            .insert(objective_index, (value, eps_coeff));
                        // Placeholder scalar; consumers read the map (see the
                        // maximize arm).
                        return Ok(Some((best_model, best_value)));
                    }
                }
                // Fall through to iterative approach.
            }
            SimplexOpt::Unbounded => {
                // The objective is unbounded below. Record it so `get-objectives`
                // reports `(* (- 1) oo)`, and return the current feasible model so the
                // problem stays SAT. Do NOT fall into the iterative loop.
                self.unbounded_objectives
                    .insert(objective_index, ObjectiveDirection::Minimize);
                return Ok(Some((best_model, best_value)));
            }
            SimplexOpt::NotApplicable => {
                // Fall through to iterative approach.
            }
        }

        // Iterative fallback: assert strict improvement until UNSAT.
        let max_rounds: usize = 128;
        for _ in 0..max_rounds {
            let lt = self.mk_real_lt(objective, &best_value);
            match self.check_sat_assuming(&[lt])? {
                SolveResult::Sat => {
                    let model = self.last_model.clone().ok_or_else(|| {
                        ExecutorError::UnsupportedOptimization(
                            "SAT without model during optimization".to_string(),
                        )
                    })?;
                    let value = self.evaluate_real_term(&model, objective)?;
                    if value >= best_value {
                        return Err(ExecutorError::UnsupportedOptimization(format!(
                            "Real objective did not strictly improve: got {value}, expected < {best_value}"
                        )));
                    }
                    best_model = model;
                    best_value = value;
                }
                SolveResult::Unsat(_) => {
                    if !self.checked_optimization_unsat(&[lt]) {
                        self.last_unknown_reason = Some(UnknownReason::Incomplete);
                        return Ok(None);
                    }
                    return Ok(Some((best_model, best_value)));
                }
                SolveResult::Unknown => return Ok(None),
            }
        }

        // Round budget exhausted without an optimality proof: fail closed
        // (see the maximize twin above; #R1).
        Ok(None)
    }

    /// Create `lhs > rhs` for Real values: `(not (<= lhs rhs))`.
    fn mk_real_gt(&mut self, lhs: TermId, rhs: &BigRational) -> TermId {
        let le = self.mk_real_le(lhs, rhs);
        self.ctx.terms.mk_not(le)
    }

    /// Create `lhs < rhs` for Real values: `(not (>= lhs rhs))`.
    fn mk_real_lt(&mut self, lhs: TermId, rhs: &BigRational) -> TermId {
        let ge = self.mk_real_ge(lhs, rhs);
        self.ctx.terms.mk_not(ge)
    }

    fn mk_real_ge(&mut self, lhs: TermId, rhs: &BigRational) -> TermId {
        let rhs = self.ctx.terms.mk_rational(rhs.clone());
        self.ctx
            .terms
            .mk_app(Symbol::named(">="), vec![lhs, rhs], Sort::Bool)
    }

    fn mk_real_le(&mut self, lhs: TermId, rhs: &BigRational) -> TermId {
        let rhs = self.ctx.terms.mk_rational(rhs.clone());
        self.ctx
            .terms
            .mk_app(Symbol::named("<="), vec![lhs, rhs], Sort::Bool)
    }

    // --- Unbounded variable detection (#8694) ---

    /// Warn about optimization variables that lack appropriate bounds.
    ///
    /// For minimize objectives, a variable needs a lower bound (>=, >).
    /// For maximize objectives, a variable needs an upper bound (<=, <).
    /// Without bounds, the optimizer may return arbitrary values (Z3 does
    /// this silently; AY warns explicitly).
    fn warn_unbounded_objectives(&self, objectives: &[ay_frontend::Objective]) {
        // Not under `--z3-mode` (or in the z3 C API library), whose stderr
        // stays as empty as z3's.
        if ay_core::misc_cli_flags().z3_transcript {
            return;
        }
        // Collect all variables in each objective and check bounds.
        for obj in objectives {
            // BitVector objectives are over a FINITE domain, so they are always
            // bounded — there is no "no bound" case to warn about. (The bound
            // scan below only recognizes Int/Real `<=`/`>=` atoms anyway.)
            if matches!(self.ctx.terms.sort(obj.term), Sort::BitVec(_)) {
                continue;
            }
            let mut vars = HashSet::default();
            self.collect_term_vars(obj.term, &mut vars);

            for &var_id in &vars {
                let var_name = match self.ctx.terms.get(var_id) {
                    TermData::Var(name, _) => name.clone(),
                    _ => continue,
                };
                // A native API constant's private identity (`!ay.z3-const!0`)
                // is not a name its caller knows; z3's API warns about none.
                if var_name.starts_with('!') {
                    continue;
                }
                let var_sort = self.ctx.terms.sort(var_id).clone();

                let (needs_lower, needs_upper) = match obj.direction {
                    ObjectiveDirection::Minimize => (true, false),
                    ObjectiveDirection::Maximize => (false, true),
                };

                let (has_lower, has_upper) = self.check_var_bounds(var_id);

                if needs_lower && !has_lower {
                    let dir = "minimize";
                    let bound_kind = "lower";
                    let sort_name = match var_sort {
                        Sort::Int => "Int",
                        Sort::Real => "Real",
                        _ => "numeric",
                    };
                    safe_eprintln!(
                        "Warning: {dir} variable '{var_name}' ({sort_name}) has no {bound_kind} bound. Results may be unexpected."
                    );
                }
                if needs_upper && !has_upper {
                    let dir = "maximize";
                    let bound_kind = "upper";
                    let sort_name = match var_sort {
                        Sort::Int => "Int",
                        Sort::Real => "Real",
                        _ => "numeric",
                    };
                    safe_eprintln!(
                        "Warning: {dir} variable '{var_name}' ({sort_name}) has no {bound_kind} bound. Results may be unexpected."
                    );
                }
            }
        }
    }

    /// Recursively collect all `Var` term IDs appearing in a term.
    fn collect_term_vars(&self, term: TermId, vars: &mut HashSet<TermId>) {
        match self.ctx.terms.get(term) {
            TermData::Var(_, _) => {
                vars.insert(term);
            }
            TermData::App(_, args) => {
                for &arg in args {
                    self.collect_term_vars(arg, vars);
                }
            }
            TermData::Not(inner) => {
                self.collect_term_vars(*inner, vars);
            }
            TermData::Ite(c, t, e) => {
                self.collect_term_vars(*c, vars);
                self.collect_term_vars(*t, vars);
                self.collect_term_vars(*e, vars);
            }
            TermData::Let(bindings, body) => {
                for (_, val) in bindings {
                    self.collect_term_vars(*val, vars);
                }
                self.collect_term_vars(*body, vars);
            }
            TermData::Const(_) | TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => {}
            _ => {}
        }
    }

    /// Check whether a variable has lower and/or upper bounds in the assertions.
    ///
    /// Scans all current assertions for patterns like:
    /// - `(>= var expr)` or `(> var expr)` or `(<= expr var)` or `(< expr var)` => lower bound
    /// - `(<= var expr)` or `(< var expr)` or `(>= expr var)` or `(> expr var)` => upper bound
    ///
    /// Returns `(has_lower_bound, has_upper_bound)`.
    fn check_var_bounds(&self, var_id: TermId) -> (bool, bool) {
        let mut has_lower = false;
        let mut has_upper = false;

        // Walk the assertions, flattening Boolean conjunction structure the
        // same way the standalone simplex does (#opt-epsilon): a positive
        // `and` contributes each conjunct, `not` flips polarity, a negative
        // `or` contributes each negated disjunct. Without this, a bound
        // inside `(assert (and (< x 3) ...))` was invisible here and produced
        // a spurious "no upper bound" warning (#8694).
        let mut work: Vec<(TermId, bool)> = self
            .ctx
            .assertions
            .iter()
            .rev()
            .map(|&assertion| (assertion, false))
            .collect();
        while let Some((term, negated)) = work.pop() {
            let inner = match self.ctx.terms.get(term) {
                TermData::Not(inner) => {
                    work.push((*inner, !negated));
                    continue;
                }
                TermData::App(sym, args) if !negated && sym.name() == "and" => {
                    work.extend(args.iter().rev().map(|&arg| (arg, false)));
                    continue;
                }
                TermData::App(sym, args) if negated && sym.name() == "or" => {
                    work.extend(args.iter().rev().map(|&arg| (arg, true)));
                    continue;
                }
                _ => term,
            };

            if let TermData::App(sym, args) = self.ctx.terms.get(inner) {
                if args.len() != 2 {
                    continue;
                }
                let name = sym.name();
                let lhs = args[0];
                let rhs = args[1];

                let lhs_contains_var = self.term_contains_var(lhs, var_id);
                let rhs_contains_var = self.term_contains_var(rhs, var_id);

                // Only consider assertions that involve exactly the variable
                // on one side (not both, which would be a relational constraint
                // between two occurrences of the same variable).
                if !lhs_contains_var && !rhs_contains_var {
                    continue;
                }

                match (name, negated) {
                    // (>= var expr) => var >= expr => lower bound on var
                    (">=" | ">", false) if lhs_contains_var => has_lower = true,
                    // (<= var expr) => var <= expr => upper bound on var
                    ("<=" | "<", false) if lhs_contains_var => has_upper = true,
                    // (>= expr var) => expr >= var => upper bound on var
                    (">=" | ">", false) if rhs_contains_var => has_upper = true,
                    // (<= expr var) => expr <= var => lower bound on var
                    ("<=" | "<", false) if rhs_contains_var => has_lower = true,
                    // (not (<= var expr)) => var > expr => lower bound on var
                    ("<=", true) if lhs_contains_var => has_lower = true,
                    // (not (>= var expr)) => var < expr => upper bound on var
                    (">=", true) if lhs_contains_var => has_upper = true,
                    // (not (<= expr var)) => expr > var => upper bound on var
                    ("<=", true) if rhs_contains_var => has_upper = true,
                    // (not (>= expr var)) => expr < var => lower bound on var
                    (">=", true) if rhs_contains_var => has_lower = true,
                    // (not (< var expr)) => var >= expr => lower bound on var
                    ("<", true) if lhs_contains_var => has_lower = true,
                    // (not (> var expr)) => var <= expr => upper bound on var
                    (">", true) if lhs_contains_var => has_upper = true,
                    // (not (< expr var)) => expr >= var => upper bound on var
                    ("<", true) if rhs_contains_var => has_upper = true,
                    // (not (> expr var)) => expr <= var => lower bound on var
                    (">", true) if rhs_contains_var => has_lower = true,
                    _ => {}
                }

                if has_lower && has_upper {
                    return (true, true);
                }
            }
        }

        (has_lower, has_upper)
    }

    /// Check if a term contains a reference to a specific variable.
    fn term_contains_var(&self, term: TermId, var_id: TermId) -> bool {
        if term == var_id {
            return true;
        }
        match self.ctx.terms.get(term) {
            TermData::Var(_, _) | TermData::Const(_) => false,
            TermData::App(_, args) => args.iter().any(|&arg| self.term_contains_var(arg, var_id)),
            TermData::Not(inner) => self.term_contains_var(*inner, var_id),
            TermData::Ite(c, t, e) => {
                self.term_contains_var(*c, var_id)
                    || self.term_contains_var(*t, var_id)
                    || self.term_contains_var(*e, var_id)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, val)| self.term_contains_var(*val, var_id))
                    || self.term_contains_var(*body, var_id)
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                self.term_contains_var(*body, var_id)
            }
            _ => false,
        }
    }
}

#[cfg(test)]
mod admission_state_tests {
    use super::*;

    fn pareto_stamp_executor() -> (Executor, Vec<ay_frontend::Objective>) {
        let mut exec = Executor::new();
        let hard_root = exec
            .ctx
            .terms
            .mk_fresh_var("pareto_stamp_hard_root", Sort::Bool);
        let objective_term = exec
            .ctx
            .terms
            .mk_fresh_var("pareto_stamp_objective", Sort::Int);
        exec.ctx.assertions = vec![hard_root];
        exec.ctx.add_objective(ay_frontend::Objective {
            direction: ObjectiveDirection::Maximize,
            term: objective_term,
        });
        exec.begin_public_solve(false);
        exec.bind_unsat_query_assumptions(&[]);
        let objectives = exec.ctx.objectives().to_vec();
        (exec, objectives)
    }

    #[test]
    fn pareto_extension_survives_append_only_term_growth() {
        let (mut exec, objectives) = pareto_stamp_executor();
        let extension = exec
            .build_pareto_front_exhaustion_extension(
                &objectives,
                &[vec![BigRational::from_integer(BigInt::from(0))]],
            )
            .expect("live Pareto blocker package");
        assert!(extension.is_current(&exec));

        let _suffix = exec
            .ctx
            .terms
            .mk_fresh_var("pareto_stamp_unrelated_suffix", Sort::Bool);
        assert!(
            extension.is_current(&exec),
            "append-only growth preserves every captured entry identity"
        );
    }

    #[test]
    fn pareto_extension_rejects_rollback_reuse_of_numeric_slots() {
        let mut exec = Executor::new();
        let checkpoint = exec.ctx.terms.rollback_checkpoint();
        let hard_root = exec
            .ctx
            .terms
            .mk_fresh_var("pareto_rolled_hard_root", Sort::Bool);
        let objective_term = exec
            .ctx
            .terms
            .mk_fresh_var("pareto_rolled_objective", Sort::Int);
        exec.ctx.assertions = vec![hard_root];
        exec.ctx.add_objective(ay_frontend::Objective {
            direction: ObjectiveDirection::Maximize,
            term: objective_term,
        });
        exec.begin_public_solve(false);
        exec.bind_unsat_query_assumptions(&[]);
        let objectives = exec.ctx.objectives().to_vec();
        let extension = exec
            .build_pareto_front_exhaustion_extension(
                &objectives,
                &[vec![BigRational::from_integer(BigInt::from(0))]],
            )
            .expect("live Pareto blocker package");
        let max_slot = extension
            .blocking()
            .iter()
            .copied()
            .chain([hard_root, objective_term])
            .map(|term| term.index())
            .max()
            .expect("the package contains terms");

        exec.ctx.terms.rollback_to(checkpoint);
        while exec.ctx.terms.len() <= max_slot {
            let replacement_index = exec.ctx.terms.len();
            let _replacement = exec.ctx.terms.mk_fresh_var(
                &format!("pareto_replacement_{replacement_index}"),
                Sort::Bool,
            );
        }
        assert!(exec.ctx.terms.entry_stamp(hard_root).is_some());
        assert!(exec.ctx.terms.entry_stamp(objective_term).is_some());
        assert!(extension.blocking().iter().all(|&term| exec
            .ctx
            .terms
            .entry_stamp(term)
            .is_some()));
        assert!(
            !extension.is_current(&exec),
            "repopulating identical numeric slots cannot refresh Pareto authority"
        );
    }

    #[test]
    fn pareto_extension_authenticates_objective_entry_independently() {
        let mut exec = Executor::new();
        let hard_root = exec
            .ctx
            .terms
            .mk_fresh_var("pareto_objective_stamp_hard_root", Sort::Bool);
        exec.ctx.assertions = vec![hard_root];
        let checkpoint = exec.ctx.terms.rollback_checkpoint();
        let objective_term = exec
            .ctx
            .terms
            .mk_fresh_var("pareto_objective_stamp_term", Sort::Int);
        exec.ctx.add_objective(ay_frontend::Objective {
            direction: ObjectiveDirection::Maximize,
            term: objective_term,
        });
        exec.begin_public_solve(false);
        exec.bind_unsat_query_assumptions(&[]);
        let objectives = exec.ctx.objectives().to_vec();
        let mut extension = exec
            .build_pareto_front_exhaustion_extension(
                &objectives,
                &[vec![BigRational::from_integer(BigInt::from(0))]],
            )
            .expect("live Pareto blocker package");
        let max_slot = extension
            .blocking()
            .iter()
            .copied()
            .chain([objective_term])
            .map(|term| term.index())
            .max()
            .expect("the package contains an objective and blocker");

        exec.ctx.terms.rollback_to(checkpoint);
        while exec.ctx.terms.len() <= max_slot {
            let replacement_index = exec.ctx.terms.len();
            let _replacement = exec.ctx.terms.mk_fresh_var(
                &format!("pareto_objective_replacement_{replacement_index}"),
                Sort::Bool,
            );
        }
        // Refresh the blocker stamps deliberately so the objective stamp is
        // the only failing identity check in this low-level attack canary.
        extension.blocking_entries = extension
            .blocking
            .iter()
            .map(|&term| {
                exec.ctx
                    .terms
                    .entry_stamp(term)
                    .expect("replacement blocker slot is live")
            })
            .collect::<Vec<_>>()
            .into_boxed_slice();
        assert!(ParetoFrontExhaustionExtension::entries_are_current(
            &exec,
            &extension.blocking,
            &extension.blocking_entries,
        ));
        assert!(
            !extension.is_current(&exec),
            "a replacement objective cannot inherit the old Pareto construction authority"
        );
    }

    #[test]
    fn transferred_pareto_blocker_stamps_reject_later_slot_reuse() {
        let (mut exec, objectives) = pareto_stamp_executor();
        let checkpoint = exec.ctx.terms.rollback_checkpoint();
        let extension = exec
            .build_pareto_front_exhaustion_extension(
                &objectives,
                &[vec![BigRational::from_integer(BigInt::from(0))]],
            )
            .expect("live Pareto blocker package");
        let blocking = extension.blocking().to_vec();
        assert!(exec.declare_pareto_front_exhaustion_extension(extension));

        let _suffix = exec
            .ctx
            .terms
            .mk_fresh_var("pareto_declared_unrelated_suffix", Sort::Bool);
        assert_eq!(exec.declared_obligation_extension(), blocking);

        let max_slot = blocking
            .iter()
            .map(|term| term.index())
            .max()
            .expect("one emitted point creates one blocker");
        exec.ctx.terms.rollback_to(checkpoint);
        while exec.ctx.terms.len() <= max_slot {
            let replacement_index = exec.ctx.terms.len();
            let _replacement = exec.ctx.terms.mk_fresh_var(
                &format!("pareto_declared_replacement_{replacement_index}"),
                Sort::Bool,
            );
        }
        assert!(
            exec.declared_obligation_extension().is_empty(),
            "the UNSAT epoch must retain the blocker birth identities"
        );
    }

    #[test]
    fn raw_unsat_cannot_authorize_a_satisfiable_optimization_bound() {
        let commands = ay_frontend::parse(
            "(set-logic QF_UF)\n\
             (declare-const p Bool)\n\
             (assert p)",
        )
        .expect("setup script parses");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("setup commands execute");
        let p = exec.ctx.assertions[0];

        // Model a forged/provisional nested verdict: the bare enum says UNSAT,
        // but H + p is satisfiable and therefore cannot move an optimization
        // bound through the checked authority gate.
        let raw = SolveResult::unsat();
        assert!(raw.is_unsat());
        assert!(!exec.checked_optimization_unsat(&[p]));

        // The identical gate does accept a genuine exact contradiction.
        let not_p = exec.ctx.terms.mk_not(p);
        assert!(exec.checked_optimization_unsat(&[not_p]));
    }

    #[test]
    fn inconclusive_optimization_revokes_partial_witness_and_objectives() {
        let mut exec = Executor::new();
        exec.last_model = Some(Model::empty());
        exec.last_model_validated = true;
        exec.last_result = Some(SolveResult::Sat);
        let emitted = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("trivial SAT seed");
        assert_eq!(emitted, SolveResult::Sat);
        exec.unbounded_objectives
            .insert(0, ObjectiveDirection::Maximize);
        exec.finite_objective_values
            .insert(0, BigRational::from_integer(BigInt::from(7)));
        exec.unavailable_objectives.insert(1);
        exec.pareto_state = Some(ParetoState::default());

        let result = exec.optimization_inconclusive();

        assert_eq!(result, SolveResult::Unknown);
        assert_eq!(exec.last_result, Some(SolveResult::Unknown));
        assert!(exec.last_model.is_none());
        assert!(!exec.last_model_validated);
        assert!(exec.last_sat_certificate.is_none());
        assert!(exec.unbounded_objectives.is_empty());
        assert!(exec.finite_objective_values.is_empty());
        assert!(exec.unavailable_objectives.is_empty());
        assert!(exec.objective_certificates.is_empty());
        assert!(exec.pareto_state.is_none());
        assert_eq!(exec.objective_optimum(0), ObjectiveOutcome::Unavailable);
    }

    #[test]
    fn maxsmt_engine_error_revokes_all_seeded_admission_state() {
        let commands = ay_frontend::parse(
            "(set-option :ay-maxsmt-engine invalid)\n\
             (declare-const a Bool)\n\
             (assert-soft a :weight 1)",
        )
        .expect("setup script parses");
        let mut exec = Executor::new();
        exec.execute_all(&commands).expect("setup commands execute");
        exec.last_model = Some(Model::empty());
        exec.last_model_validated = true;
        exec.last_result = Some(SolveResult::Sat);
        let emitted = exec
            .emit_sat_verdict(SolveResult::Sat, &[])
            .expect("trivial SAT seed");
        assert_eq!(emitted, SolveResult::Sat);
        exec.last_soft_cost = Some(1);
        exec.last_soft_cost_optimal = true;
        exec.last_soft_violations = Some(vec![0]);
        exec.unbounded_objectives
            .insert(0, ObjectiveDirection::Maximize);
        exec.finite_objective_values
            .insert(0, BigRational::from_integer(BigInt::from(1)));
        exec.unavailable_objectives.insert(1);
        exec.pareto_state = Some(ParetoState::default());

        let error = exec
            .maxsmt_check_sat()
            .expect_err("invalid engine must be rejected");

        assert!(matches!(error, ExecutorError::UnsupportedOptimization(_)));
        assert!(exec.last_result.is_none());
        assert!(exec.last_model.is_none());
        assert!(!exec.last_model_validated);
        assert!(exec.last_sat_certificate.is_none());
        assert!(exec.last_soft_cost.is_none());
        assert!(exec.last_soft_violations.is_none());
        // With no cost present, the companion flag is reset to its ordinary
        // vacuous/default value and cannot publish an optimum on its own.
        assert!(exec.last_soft_cost_optimal);
        assert!(exec.unbounded_objectives.is_empty());
        assert!(exec.finite_objective_values.is_empty());
        assert!(exec.unavailable_objectives.is_empty());
        assert!(exec.objective_certificates.is_empty());
        assert!(exec.pareto_state.is_none());
        assert_eq!(exec.objective_optimum(0), ObjectiveOutcome::Unavailable);
    }
}
