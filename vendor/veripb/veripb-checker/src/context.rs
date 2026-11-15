//! Proof context for the [`ForwardsChecker`] storing the state of the checker.

use std::{
    num::Saturating,
    time::{Duration, Instant},
};

use ahash::{AHashMap, AHashSet};
use colored::Colorize;
use itertools::Itertools;
use log::warn;
use malachite_bigint::BigInt;
use num_traits::Zero;
use veripb_formula::{prelude::*, propagation::RUPHint};
use veripb_propagator::propagation_engine::PropagationEngine;
use veripb_rules::{ObjectiveUpdateType, elaboration::Elaborator};

use crate::{
    order_context::{OrderContext, ReflexivityContext, SpecificationContext, TransitivityContext},
    prelude::*,
    proofgoal_context::ProofgoalContext,
};

/// Index of temporary propagation sets for autoproving.
pub const AUTOPROVING: usize = 4;

/// Constant for heuristic trying RUP for `red`-rule or deletion before generating proofgoals.
pub const REQUIRED_RUP_STREAK: Saturating<u8> = Saturating(5);

/// A [`Subcontext`] stores information that is specific to an environment in the proof.
///
/// The meaning and usage of each variant of [`Subcontext`] are described below.
#[derive(Debug)]
pub enum Subcontext {
    /// A top-level subproof for a proof rule started with the keyword `subproof`.
    Subproof(SubproofContext),
    /// A subproof for a proofgoal inside a top-level subproof. `Proofgoal` subproofs are started by the `proofgoal`-rule.
    Proofgoal(ProofgoalContext),
    /// Subcontext for defining an order.
    Order(OrderContext),
    /// Subcontext for showing that an order is transitive.
    Transitivity(TransitivityContext),
    /// Subcontext for showing that an order is reflexive.
    Reflexivity(ReflexivityContext),
    /// Subcontext for deriving the auxiliary specification for and order.
    Specification(SpecificationContext),
}

impl Subcontext {
    /// Check if the subcontext is a top-level subproof or proofgoal subproof.
    #[inline]
    pub fn is_subproof(&self) -> bool {
        matches!(self, Subcontext::Subproof(_) | Subcontext::Proofgoal(_))
    }

    /// `true` for the four subcontexts that an order definition opens.
    ///
    /// These are exactly the subcontexts in which the installed constraint
    /// database is *not* the problem's: `def_order`/`pre_order` and `spec`
    /// swap in a fresh empty one ([`crate::rules::Checkable::swaps_database`])
    /// and `transitivity`/`reflexivity` run their proofs inside it. Rules are
    /// filtered here by
    /// [`crate::rules::CheckableRule::order_definition_placement`].
    #[inline]
    pub fn is_order_definition(&self) -> bool {
        !self.is_subproof()
    }

    /// The context's name, for diagnostics.
    pub fn kind_name(&self) -> &'static str {
        match self {
            Subcontext::Subproof(_) => "subproof",
            Subcontext::Proofgoal(_) => "proofgoal",
            Subcontext::Order(_) => "order definition",
            Subcontext::Transitivity(_) => "transitivity",
            Subcontext::Reflexivity(_) => "reflexivity",
            Subcontext::Specification(_) => "order specification",
        }
    }
}

/// Context to store the state of the [`ForwardsChecker`].
///
/// This can be thought of as the configuration maintained by the checker.
#[derive(Debug, Default)]
pub struct Context {
    /// Static configuration options (e.g. from command-line arguments)
    pub config: CheckerConfig,
    /// Counters for `--kernel-verify` (see [`crate::kernel_bridge`]).
    pub kernel_stats: crate::kernel_bridge::KernelStats,
    /// The shadow database that composes the per-step kernel checks into a
    /// run-level `DbOk`/`checker_sound` claim, present only under
    /// `--kernel-verify` (see [`crate::kernel_bridge::KernelShadowDb`]).
    pub kernel_shadow: Option<crate::kernel_bridge::KernelShadowDb>,
    /// Stronger guarantees that solutions to current problem are solutions to original problem.
    pub strong_solution_guarantees: bool,
    /// Storage of variable names and used variables.
    pub var_names: VarNameManager,
    /// How many variables `var_names` held before the rule currently being
    /// executed was *parsed*.
    ///
    /// Names are interned by the parser as it reads a rule, so a variable whose
    /// index is at least this is one the current rule introduced: it has been
    /// seen nowhere earlier in the proof, and nowhere in the formula. That is
    /// what [`crate::checker::give_version3_auxiliary_names`] needs before it
    /// may rename an auxiliary variable for the elaborated proof — see there.
    /// Maintained at the end of [`crate::checker::ForwardsChecker::execute_rule`];
    /// it starts at the number of variables the formula introduced.
    pub vars_known_before_rule: usize,
    /// Original formula.
    pub original_constraints: Vec<PBConstraintEnum>,
    /// Original objective.
    pub original_objective: Option<PBObjective>,
    /// Current objective.
    pub objective: Option<PBObjective>,
    /// The currently best objective value logged while checked deletion was enabled.
    pub best_valid_objective_value: Option<BigInt>,
    /// The currently best objective value over all.
    pub best_objective_value: Option<BigInt>,
    /// A lower bound on the objective value of every assignment that a
    /// solution-logging rule has removed from the database, or [`None`] while
    /// nothing has been removed.
    ///
    /// [`Context::best_objective_value`] is the value of the logged
    /// *representative*. For `soli`/`obji` the two coincide: the constraint they
    /// store is `obj <= v - 1`, which removes exactly `{ obj >= v }`. For `solx`
    /// they do not — it removes the whole class of assignments agreeing with the
    /// logged solution on the preserved variables, and that class' minimum lies
    /// below the representative's value as soon as the objective mentions a
    /// variable outside the preserved set. The `conclusion BOUNDS` lower-bound
    /// guard and the `output EQUIOPTIMAL` qualifier both need the class bound,
    /// not the representative; see
    /// [`Context::objective_guarantee_ceiling`].
    pub excluded_objective_lower_bound: Option<BigInt>,
    /// Stack of currently used subproof contexts.
    pub subcontexts: Vec<Subcontext>,
    /// A flag to determine if we are inside a strengthening subproof, where some rules are not allowed.
    pub inside_strengthening_subproof: bool,
    /// Propagation engine for checks by propagation.
    pub propagation_engine: PropagationEngine,
    /// All orders known to checker.
    pub orders: AHashMap<String, Order>,
    /// The currently active order.
    pub active_order: Option<ActiveOrder>,
    /// Current streak autoproving red rules by the constraint being RUP.
    pub rup_streak: Saturating<u8>,
    /// Stored assignment for annotated RUP steps.
    pub annotated_rup_assignment: Assignment<BooleanVar>,
    /// Stored hints for annotated RUP steps.
    pub annotated_rup_hints: Vec<RUPHint>,
    /// Proof major version.
    pub major_version: Option<u8>,
    /// Proof minor version.
    pub minor_version: Option<u8>,
    /// Output has been checked.
    pub has_output: bool,
    /// Conclusion has been checked
    pub has_conclusion: bool,
    /// End of proof has been encountered
    pub has_end_proof: bool,
    /// An assertion rule has been used in the proof.
    pub assertion_used: bool,
    /// Elaborator
    pub elaborator: Option<Elaborator>,
    /// The current level that is set
    pub current_level: Option<usize>,
    /// The storage of constraint IDs for each level
    pub level_ids: Vec<Vec<usize>>,
    /// Store if only core constraints can be used for proof.
    pub only_core: bool,
    /// Stores if the strengthening to core is more is enabled.
    pub is_strengthening_to_core: bool,
    /// The current set of preserved variables.
    pub preserved_variables: Option<AHashSet<VarIdx>>,
    /// If witnesses have been used before the preserved set has been initialized.
    pub witnesses_used: bool,
    /// A solution has been logged, which introduced an excluding constraint.
    pub solution_logged: bool,
    /// An objective-improving constraint (`soli` / `obji`) has been stored.
    ///
    /// The constraint `obj <= v - 1` those rules store is
    /// satisfiability-preserving but *not* entailed: it removes every assignment
    /// whose objective value is at least `v` and, unlike `solx`, never
    /// increments [`Context::num_excluded_solutions`]. A contradiction in the
    /// database therefore no longer establishes "there are no further
    /// solutions", which is exactly what `conclusion ENUMERATION_COMPLETE`
    /// claims, so that conclusion is refused once this is set. `output
    /// EQUIENUMERABLE` and `output DERIVABLE` refuse on it for the same
    /// reason: the stored constraint changes the solution count and is not
    /// input-entailed, and `obji` reaches both arms without setting
    /// [`Context::solution_logged`] (ported from the ay repo's patch
    /// 0002-ay-post-fork-soundness-fixes, defect 20 there).
    ///
    /// Tracked separately from [`Context::solution_logged`] on purpose: that
    /// flag is also set by `solx`, which every legitimate enumeration proof
    /// uses, so keying the guard on it would reject correct proofs.
    pub objective_improving_used: bool,
    /// A witnessed strengthening (`red` or `dom`) stored its constraint.
    ///
    /// Same hazard as [`Context::objective_improving_used`], reached by a
    /// different rule: redundance- and dominance-based strengthening store a
    /// constraint that is satisfiability-preserving but NOT input-entailed.
    /// `output DERIVABLE` claims every model of the input is a model of the
    /// output and establishes it by matching the output against the core set,
    /// so one non-entailed core constraint makes that claim false.
    ///
    /// Set only on the WITNESSED path. Both rules have shortcuts -- the
    /// constraint is already in the database, or is RUP-implied -- and those
    /// store an entailed copy, so setting the flag there would reject correct
    /// proofs.
    ///
    /// Set regardless of whether the constraint lands in core or derived: a
    /// later `core id` can move a derived constraint into the core set, which
    /// is exactly how the reproducer for this reached `check_file`.
    pub witnessed_strengthening_used: bool,
    /// The preserved set has been changed.
    pub preserved_set_changed: bool,
    /// The number of solutions excluded by `solx`.
    pub num_excluded_solutions: i64,
    /// The `s ...` verification result lines that have been decided but not yet
    /// printed.
    ///
    /// They are only printed once the whole run has completed, so that a proof
    /// that is rejected *after* its `conclusion` line — or whose elaborated
    /// proof could not be written out — never leaves a success verdict on
    /// stdout. See [`Context::take_verification_results`].
    pub pending_verification_results: Vec<crate::checked_result::CheckedStatement>,
    /// Set when VeriPB had to fall back from checked to unchecked deletion in
    /// the middle of the proof, i.e. when a proof obligation was dropped that
    /// the user did not ask to have dropped (that is the case where
    /// `--unchecked-deletion` was *not* passed).
    pub unchecked_deletion_fallback: bool,
    /// Set when a conclusion whose meaning depends on solutions of the original
    /// problem (`SAT`, `BOUNDS`, enumeration) was reached while the solution
    /// guarantees were weakened by unchecked deletion.
    pub weakened_verdict: bool,
    /// Whether tracing is currently active for the rule being processed.
    ///
    /// This is recomputed for each rule (see [`Context::should_trace`]) so that
    /// the `--trace-lines` and `--trace-ids` options can enable tracing only for
    /// selected lines or constraint IDs.
    pub trace_enabled: bool,
    /// Mapping from [`String`] of a running timer to the [`Instant`] they were started.
    pub running_timers: AHashMap<String, Instant>,
    /// Mapping from [`String`] of a timer to its total elapsed duration.
    pub timer_totals: AHashMap<String, Duration>,
}

impl Context {
    /// Construct a new [`Context`] from the checker `config` and the mapping of labels to IDs in `var_names`.
    pub fn new(
        config: impl Into<CheckerConfig>,
        var_names: VarNameManager,
        preserved_variables: Option<AHashSet<VarIdx>>,
    ) -> Context {
        let config: CheckerConfig = config.into();
        let strong_solution_guarantees = !config.unchecked_deletion;
        let mut propagation_engine = new_veripb_propagation_engine();
        propagation_engine.collect_kernel_certificate = config.kernel_verify;
        let kernel_shadow = crate::kernel_bridge::new_shadow(config.kernel_verify);
        Context {
            config,
            kernel_shadow,
            strong_solution_guarantees,
            vars_known_before_rule: var_names.len(),
            var_names,
            preserved_variables,
            propagation_engine,
            rup_streak: REQUIRED_RUP_STREAK - Saturating(1),
            ..Default::default()
        }
    }

    /// Take the verification result lines decided so far, leaving none behind.
    ///
    /// The caller is expected to print them, which must only happen after the
    /// run has completed without error.
    pub fn take_verification_results(&mut self) -> Vec<String> {
        self.take_checked_statements()
            .into_iter()
            .filter(crate::checked_result::CheckedStatement::should_emit)
            .map(|statement| statement.to_string())
            .collect()
    }

    /// Take typed results only after the complete proof and elaboration succeed.
    pub fn take_checked_statements(&mut self) -> Vec<crate::checked_result::CheckedStatement> {
        std::mem::take(&mut self.pending_verification_results)
    }

    /// Record that a solution-logging rule removed a set of assignments from the
    /// database whose objective values are all at least `bound`.
    ///
    /// Folding by minimum keeps
    /// [`Context::excluded_objective_lower_bound`] a lower bound over
    /// *everything* removed so far, which is what its readers need.
    pub fn note_excluded_objective_bound(&mut self, bound: BigInt) {
        if self
            .excluded_objective_lower_bound
            .as_ref()
            .is_none_or(|current| bound < *current)
        {
            self.excluded_objective_lower_bound = Some(bound);
        }
    }

    /// The objective value from which upwards the proof no longer speaks for the
    /// original problem, or [`None`] when no solution has been logged at all.
    ///
    /// Below it, the database still describes the original problem faithfully;
    /// at or above it, solution logging may have removed solutions the proof
    /// never accounted for. That makes it both the largest lower bound
    /// `conclusion BOUNDS` may claim (see
    /// [`crate::rules::conclusion::validate_lower_bound`], which reports the two
    /// sources separately) and the `FOR obj < ...` qualifier
    /// `output EQUIOPTIMAL` has to print.
    ///
    /// It is the minimum of the two records because either can be the smaller:
    /// [`Context::best_objective_value`] is a solution the proof exhibited (so
    /// the optimum is no larger), while
    /// [`Context::excluded_objective_lower_bound`] bounds what was deleted.
    pub fn objective_guarantee_ceiling(&self) -> Option<&BigInt> {
        [
            self.best_objective_value.as_ref(),
            self.excluded_objective_lower_bound.as_ref(),
        ]
        .into_iter()
        .flatten()
        .min()
    }

    /// Whether the run should report that it could not give the full guarantee
    /// it was asked for, i.e. a solution-dependent verdict was reached only
    /// because VeriPB silently downgraded to unchecked deletion.
    pub fn guarantee_was_silently_weakened(&self) -> bool {
        self.weakened_verdict && self.unchecked_deletion_fallback
    }

    /// Check if the current `line` or constraint ID `next_id` should be traced.
    pub fn should_trace(&self, line: usize, next_id: isize) -> bool {
        should_trace(
            self.config.trace,
            self.config.trace_lines.as_ref(),
            self.config.trace_ids.as_ref(),
            line,
            next_id,
        )
    }

    /// Update the objective to a new objective.
    ///
    /// The `update_type` specifies how the objective should be updated and `objective_update` contains the data of the objective updaet.
    pub fn update_objective(
        &mut self,
        mut objective_update: PBObjective,
        update_type: ObjectiveUpdateType,
    ) {
        match update_type {
            ObjectiveUpdateType::New => self.objective = Some(objective_update),
            ObjectiveUpdateType::Diff => {
                // Change the objective by the diff.
                let objective = self.objective.as_mut().unwrap();
                objective.constant += objective_update.constant;
                while let Some((var, term)) = objective_update.terms.pop_first() {
                    if let Some(existing_term) = objective.terms.get_mut(&var) {
                        objective.constant += existing_term.add_with(term);
                        if existing_term.coeff.is_zero() {
                            objective.terms.remove(&var);
                        }
                    } else {
                        objective.terms.insert(var, term);
                    }
                }
            }
        }

        // Trace objective change.
        if self.trace_enabled {
            println!(
                "  {} updated to: {}",
                "Objective".bright_green(),
                self.objective
                    .as_ref()
                    .unwrap()
                    .to_pretty_string(&self.var_names)
                    .green()
            );
        }
    }

    /// Pretty print the current preserved set, in ascending variable order.
    ///
    /// Sorted, not iterated in hash order. `preserved_variables` is an
    /// `AHashSet`, whose `RandomState` seeds itself from runtime randomness
    /// once per process, so iterating it prints a different permutation on
    /// every run: measured before this, `--trace` on
    /// `add_preserved_var_trivial` produced twenty distinct outputs over
    /// twenty runs, differing only in the order of this line. The *set* is a
    /// function of the input; the order it was printed in was not. See
    /// `tests/observable_output_deterministic.rs`.
    #[inline]
    pub fn print_preserved_set(&self) {
        let mut vars: Vec<VarIdx> = self
            .preserved_variables
            .as_ref()
            .unwrap()
            .iter()
            .copied()
            .collect();
        vars.sort_unstable();
        println!(
            "{}: {}",
            "Preserved set".magenta(),
            vars.iter()
                .map(|v| v.to_pretty_string(&self.var_names))
                .join(" ")
                .blue()
        );
    }

    /// Check if the witness satisfies the following conditions:
    /// - If a preserved set is loaded, then the domain of the witness can not contain any preserved variables.
    #[inline]
    pub fn check_witness(&mut self, witness: &Substitution) -> Result<(), CheckingError> {
        if witness.is_empty() {
            return Ok(());
        }
        if let Some(preserved_vars) = &self.preserved_variables {
            for var in witness.syntactic_support() {
                if preserved_vars.contains(var) {
                    return Err(CheckingError::WitnessContainsPreservedVar(
                        var.to_pretty_string(&self.var_names).bold(),
                    ));
                }
            }
        } else {
            self.witnesses_used = true;
        }
        Ok(())
    }

    /// Collect custom timer diagnostics after the whole check completed.
    pub fn custom_timer_lines(&self) -> Vec<String> {
        let lines = self
            .timer_totals
            .iter()
            .sorted_unstable_by_key(|t| t.0)
            .map(|(name, elapsed)| {
                format!(
                    "c statistic: custom timer '{name}': {} s",
                    elapsed.as_secs_f64()
                )
            })
            .collect();
        for name in self.running_timers.keys() {
            warn!("The timer with name '{name}' is still running!");
        }
        lines
    }

    /// Print total time of custom timers in a formatted form.
    pub fn print_custom_timers(&self) {
        for line in self.custom_timer_lines() {
            println!("{line}");
        }
    }
}

/// Determine whether the rule on (0-based) proof file line `line` that will
/// derive constraints starting at ID `next_id` should be traced.
pub fn should_trace(
    trace_all: bool,
    trace_lines: Option<&RangeSet>,
    trace_ids: Option<&RangeSet>,
    line: usize,
    next_id: isize,
) -> bool {
    if trace_all {
        return true;
    }
    if let Some(lines) = trace_lines {
        // Proof file lines are presented to the user as 1-based.
        if lines.contains(line + 1) {
            return true;
        }
    }
    if next_id >= 0
        && let Some(ids) = trace_ids
        && ids.contains(next_id as usize)
    {
        return true;
    }
    false
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Nothing logged, nothing removed: the proof still speaks for the whole
    /// original problem, so there is no ceiling at all.
    #[test]
    fn an_untouched_context_has_no_objective_ceiling() {
        assert_eq!(Context::default().objective_guarantee_ceiling(), None);
    }

    /// The fold keeps the smallest bound seen, which is what makes the field a
    /// lower bound over *everything* removed so far.
    #[test]
    fn the_excluded_bound_folds_by_minimum() {
        let mut context = Context::default();

        context.note_excluded_objective_bound(BigInt::from(7));
        context.note_excluded_objective_bound(BigInt::from(9));
        assert_eq!(
            context.excluded_objective_lower_bound,
            Some(BigInt::from(7)),
            "a later, weaker bound must not raise the recorded one"
        );

        context.note_excluded_objective_bound(BigInt::from(-2));
        assert_eq!(
            context.excluded_objective_lower_bound,
            Some(BigInt::from(-2))
        );
    }

    /// A context whose only interesting state is the best logged solution.
    fn context_with_best(best: i64) -> Context {
        Context {
            best_objective_value: Some(BigInt::from(best)),
            ..Default::default()
        }
    }

    /// The `solx` shape: the logged representative is worth 100, but the class
    /// that was actually removed reaches down to 0. The ceiling has to follow
    /// the class, not the representative.
    #[test]
    fn the_ceiling_follows_whichever_record_is_smaller() {
        let mut context = context_with_best(100);
        context.note_excluded_objective_bound(BigInt::zero());

        assert_eq!(context.objective_guarantee_ceiling(), Some(&BigInt::zero()));

        // ... and the other way round, so the best logged solution is not lost
        // when it is the tighter of the two.
        let mut context = context_with_best(3);
        context.note_excluded_objective_bound(BigInt::from(11));

        assert_eq!(
            context.objective_guarantee_ceiling(),
            Some(&BigInt::from(3))
        );
    }
}
