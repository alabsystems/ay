// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! check-sat-assuming entry point extraction.

// #8529: Use deterministic hash sets in all builds.
use ay_core::time::Instant;

use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, TermId};
use ay_frontend::OptionValue;

use super::check_sat::{contains_symbolic_integer_power, has_only_uf_lia_theories};
use super::dt_axioms::DtSolverDispatch;
use super::theories::bv_cnf_dump;
use super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor_types::{
    ExecutorError, Result, SolveResult, Statistics, UnknownOrigin, UnknownReason,
};
use crate::logic_detection::{LogicCategory, TheoryKind};

#[path = "check_sat_assuming/publication.rs"]
mod publication;

/// Floor of the wall budget for re-checking a harvested proper-subset core.
const HARVEST_RECHECK_FLOOR: std::time::Duration = std::time::Duration::from_secs(2);

/// Wall budget for the strict re-check of a harvested core
/// ([`Executor::certify_assumption_core`]): a third of the time left before
/// the solve deadline, never less than [`HARVEST_RECHECK_FLOOR`]; the floor
/// alone without a deadline.
///
/// The verdict is already decided when this runs, so the budget only buys
/// a reduced core, and two thirds of what is left stay for the minimizer and
/// the output. A fixed 2 s was too little for a proof-carrying re-check over
/// thousands of assertions: SMT-COMP 2026 uc-qf-linearintarith QF_LIA/bbd20ad3
/// (2,863 named) harvested a 523-member core whose re-check took 5.4 s on
/// the loaded host, so the harvest was discarded and the core padded to all
/// 2,863 assertions (AY-SMT-4). The probe is still bounded by the caller's
/// deadline, and a re-check that does not finish still pads.
fn harvest_recheck_budget(remaining: Option<std::time::Duration>) -> std::time::Duration {
    remaining.map_or(HARVEST_RECHECK_FLOOR, |left| {
        (left / 3).max(HARVEST_RECHECK_FLOOR)
    })
}
pub(in crate::executor) use publication::AssumptionSatPublication;
#[path = "check_sat_assuming/fragile_lra_gate.rs"]
mod fragile_lra_gate;
mod scoped_authority;
#[path = "check_sat_assuming/stateless_subsolve.rs"]
mod stateless_subsolve;
pub(in crate::executor) use stateless_subsolve::ScopedWindowLanes;

/// Which wrapper owns the one final nested-array UNSAT quarantine.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum AssumptionNestedArrayQuarantine {
    Local,
    DeferToCaller,
}

// Own the actual original assumption buffer while a scoped solver lowers it
// into assertions and hides last_assumptions from lane dispatch. This is query
// identity DATA, never a grant or a late retarget of an existing model.
pub(in crate::executor) struct OriginalModelAssumptions(
    pub(in crate::executor) Option<Vec<TermId>>,
);

impl Executor {
    /// Run check-sat with assumptions.
    ///
    /// The assumptions are temporary - they are only used for this check-sat call
    /// and do not affect the assertion stack.
    ///
    /// `pub(crate)`: External consumers MUST use `api::Solver::check_sat_assuming()`
    /// which returns `VerifiedSolveResult`. Part of #5787 (Phase 6).
    pub(crate) fn check_sat_assuming(&mut self, assumptions: &[TermId]) -> Result<SolveResult> {
        self.check_sat_assuming_with_publication(
            assumptions,
            AssumptionSatPublication::EmitHere,
            AssumptionNestedArrayQuarantine::Local,
        )
    }

    /// Named-core redirect used from inside plain `check-sat`.
    ///
    /// The caller owns the ordinary SAT funnel after this returns, so a SAT
    /// result here must retain Pending certificate transport and carry no
    /// already-minted public SAT token.
    pub(in crate::executor) fn check_sat_assuming_deferred_to_plain_check_sat(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        self.check_sat_assuming_with_publication(
            assumptions,
            AssumptionSatPublication::DeferToPlainCheckSat,
            AssumptionNestedArrayQuarantine::DeferToCaller,
        )
    }

    /// Inner solve for the direct public named-core wrapper. SAT still emits
    /// here, but the outer wrapper owns nested-array authority after restoring
    /// assertions and completing core work.
    fn check_sat_assuming_deferred_to_named_outer(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        self.check_sat_assuming_with_publication(
            assumptions,
            AssumptionSatPublication::EmitHere,
            AssumptionNestedArrayQuarantine::DeferToCaller,
        )
    }

    fn check_sat_assuming_with_publication(
        &mut self,
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
        quarantine: AssumptionNestedArrayQuarantine,
    ) -> Result<SolveResult> {
        self.with_scope_root_depths(|this| {
            this.check_sat_assuming_with_captured_roots(assumptions, publication, quarantine)
        })
    }

    fn check_sat_assuming_with_captured_roots(
        &mut self,
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
        quarantine: AssumptionNestedArrayQuarantine,
    ) -> Result<SolveResult> {
        // Evidence policy P1: a checking re-solve's nested probes run no
        // strengthening either (`strengthening.rs`).
        let _checking_scope = self.enter_checking_solve_scope();
        if let Some(result) = self.reject_pending_fp_namespace_refusal() {
            Self::invalidate_bv_cnf_export_for_rejected_check()?;
            return Ok(result);
        }
        self.last_sat_certificate = None;
        self.pending_nested_array_bool_bv_unsat = None;
        self.pending_bounded_bv_lia_unsat = None;
        self.clear_strict_native_bundle_states();
        let mut symbolic_power_roots = self.ctx.assertions.clone();
        symbolic_power_roots.extend_from_slice(assumptions);
        if contains_symbolic_integer_power(&self.ctx.terms, &symbolic_power_roots) {
            self.last_model = None;
            self.record_unknown_from_origin(UnknownOrigin::UnsupportedArithmeticFragment);
            self.record_unknown_diagnostic(
                UnknownReason::UnsupportedArithmetic,
                "exponentiation with a symbolic exponent (or a native `^` exponent that is not a positive integer literal) is accepted and typed but has no sound decision procedure",
            );
            return Ok(SolveResult::Unknown);
        }
        // Deferred public wrappers already own an unsplit root snapshot. Avoid
        // cloning a second, temporarily stripped window on those paths.
        let decision_roots = matches!(quarantine, AssumptionNestedArrayQuarantine::Local)
            .then(|| self.public_solve_roots(assumptions));
        let export_requested = bv_cnf_dump::requested();
        let mut dump_roots = if export_requested {
            self.ctx.assertions.clone()
        } else {
            Vec::new()
        };
        if export_requested {
            dump_roots.extend_from_slice(assumptions);
        }
        let dump_transaction = bv_cnf_dump::prepare_for_check()?;
        self.validate_bv_cnf_export_roots(&dump_roots)?;
        let solve_started_at = Instant::now();
        let assembly_started_at = super::proof::assembly_observations::thread_observations();
        let previous_deadline = self.install_timeout_deadline_for_call();
        let check = self.open_check_node();
        let _in_check = check.enter();
        // A direct assumption query captures its exact pre-solve base just as
        // plain `check-sat` does. A nested named-core redirect retains the
        // already-installed outer authored snapshot; replacing it with the
        // stripped unnamed base would bind Pending theorem transport to the
        // redirect's reordered working set instead of the public query.
        // `last_assumptions`, installed by the inner call, is appended (with
        // exact-TermId deduplication) by `independent_gate_query_roots`.
        let saved_independent_gate_authored = self.independent_gate_authored_assertions.take();
        let active_authored_roots = saved_independent_gate_authored
            .clone()
            .unwrap_or_else(|| self.ctx.assertions.clone());
        self.independent_gate_authored_assertions = Some(active_authored_roots);
        // (#quantifier-ce-free-resolve) The counterexample-free probe is
        // PARKED by the quantifier loop and fired at the executor, at the one
        // site in `check_sat_guarded` that runs after every pass which could
        // still publish. This path never reaches that site -- it has no CEGAR
        // loop, no deep-QE or trace-arming retry, no finite-model last chance
        // and no model-rejection re-solve behind it -- so a stash parked by a
        // solve under this call must not survive it. Two reasons, and the
        // first is soundness: an assumption query's pre-dispatch vector is not
        // the plain query's, and letting an outer `check_sat_guarded` fire a
        // stash an assumption solve parked would re-solve the wrong problem
        // and publish its refutation as the outer verdict. The second is that
        // an OUTER stash must survive a nested assumption probe (optimization
        // bound probes and the MaxSMT disjoint-core lower bound call
        // `check_sat_assuming` from inside a plain solve), which a bare clear
        // would destroy. Save and restore, exactly like the gate window above.
        let saved_ce_free_stash = self.cegqi_ce_free_stash.take();
        let result = self.check_sat_assuming_with_array_refutation_retry(assumptions, publication);
        self.cegqi_ce_free_stash = saved_ce_free_stash;
        self.independent_gate_authored_assertions = saved_independent_gate_authored;
        self.restore_timeout_deadline_after_call(previous_deadline);
        self.record_z3_resource_statistics(solve_started_at, assembly_started_at, &check);
        let result = result.and_then(|result| {
            bv_cnf_dump::finish_check(dump_transaction, &self.ctx.terms, &dump_roots)?;
            Ok(result)
        })?;
        match (quarantine, decision_roots) {
            (AssumptionNestedArrayQuarantine::Local, Some(decision_roots)) => {
                // `None`: an assumption literal is not a hard constraint, so
                // the nested-array-free residue rescue is unavailable here.
                Ok(self.quarantine_unverified_nested_array_unsat(&decision_roots, None, result))
            }
            (AssumptionNestedArrayQuarantine::DeferToCaller, None) => Ok(result),
            _ => unreachable!("quarantine ownership and root snapshot must agree"),
        }
    }

    /// `check-sat-assuming` entry for USER-FACING queries (the SMT-LIB
    /// command and the public API), with named-assertion core tracking
    /// (#unsat-core-assumptions).
    ///
    /// When `:produce-unsat-cores` is enabled and named assertions exist,
    /// named assertions are moved out of the base assertion set and
    /// assumption-tracked ALONGSIDE the user's assumption literals —
    /// replicating the proven plain-check-sat named-core redirect
    /// (check_sat.rs). Without this, the SAT-level failed-assumption core
    /// cannot contain named participants and `(get-unsat-core)` after a
    /// direct `(check-sat-assuming ...)` printed a set that can be
    /// SATISFIABLE together with the unnamed assertions (unsound output;
    /// the verdicts themselves were correct).
    ///
    /// INTERNAL solver probes (optimization bound probes and the MaxSMT
    /// disjoint-core lower bound) deliberately call `check_sat_assuming`
    /// directly instead:
    /// they authenticate harvested cores against exactly the assumption set
    /// they passed, and injecting named assertions there would disable
    /// those sound-progress checks (and with them e.g. the MaxSMT
    /// disjoint-core lower bound) whenever cores + named assertions are
    /// both active. The verdict is identical either way — the checked
    /// conjunction is the same set.
    pub(crate) fn check_sat_assuming_with_named_cores(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if let Some(result) = self.reject_pending_fp_namespace_refusal() {
            Self::invalidate_bv_cnf_export_for_rejected_check()?;
            return Ok(result);
        }
        // Capture the public query before named assertions move into the
        // solver-assumption slot. The inner solve, rescue, and minimizer can
        // all grow the term store; finite-array evidence is therefore sealed
        // only by this wrapper's final quarantine after they finish.
        let decision_roots = self.public_solve_roots(assumptions);
        // The redirect below strips named roots out of `ctx.assertions`: the
        // scope-tracked stack is read before it does.
        let result = self.with_scope_root_depths(|this| {
            this.check_sat_assuming_with_named_cores_inner(assumptions)
        })?;
        Ok(self.quarantine_unverified_nested_array_unsat(&decision_roots, None, result))
    }

    fn check_sat_assuming_with_named_cores_inner(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if let Some((term_to_name, named_assumptions, unnamed_assertions)) =
            self.named_core_redirect_partition()
        {
            return self.run_named_core_redirect(
                assumptions,
                term_to_name,
                named_assumptions,
                unnamed_assertions,
            );
        }

        let result = self.check_sat_assuming_deferred_to_named_outer(assumptions);
        // #A7: `(get-unsat-assumptions)` publishes the harvest as a
        // CERTIFICATE — SMT-LIB 2.6 requires the returned subset to be
        // unsatisfiable together with the asserted formulas, and a consumer
        // (MUS extraction, assumption-based CEGAR, BMC) that trusts a
        // satisfiable "core" draws exactly the conclusion a wrong `unsat`
        // would licence. The named-core branch above already gates its
        // harvest; this branch (`:produce-unsat-assumptions` WITHOUT
        // `:produce-unsat-cores`) published the raw harvest, which
        // `unsat_assumptions` then only membership-filtered. Route it through
        // the same fail-closed re-solve: a proper-subset harvest must re-prove
        // UNSAT on its own or it is discarded, after which the full assumption
        // set — always a sound core when the query is UNSAT — prints instead.
        // Gated on the option so plain solving and internal probes pay
        // nothing.
        if self.produce_unsat_assumptions_enabled() {
            let certified = self.certify_assumption_core(assumptions, result);
            // The gate's re-solves overwrite `last_assumptions` with whatever
            // set they checked; narrow it back to the USER literals so
            // `get-unsat-assumptions` keeps its SMT-LIB subset contract.
            self.last_assumptions = Some(assumptions.to_vec());
            return certified;
        }
        result
    }

    /// Partition the authored stack for the named-to-assumption redirect.
    fn named_core_redirect_partition(
        &self,
    ) -> Option<(HashMap<TermId, String>, Vec<TermId>, Vec<TermId>)> {
        if !self.produce_unsat_cores_enabled() {
            return None;
        }
        let term_to_name: HashMap<TermId, String> = self
            .ctx
            .named_terms_iter()
            .map(|(name, tid)| (tid, name.to_string()))
            .collect();
        if term_to_name.is_empty() {
            return None;
        }

        let (named, unnamed): (Vec<TermId>, Vec<TermId>) = self
            .ctx
            .assertions
            .iter()
            .copied()
            .partition(|assertion| term_to_name.contains_key(assertion));
        (!named.is_empty()).then_some((term_to_name, named, unnamed))
    }

    /// Run the stripped named-core transaction and restore the authored stack
    /// before its result or error can escape.
    fn run_named_core_redirect(
        &mut self,
        assumptions: &[TermId],
        term_to_name: HashMap<TermId, String>,
        named_assumptions: Vec<TermId>,
        unnamed_assertions: Vec<TermId>,
    ) -> Result<SolveResult> {
        // Named terms precede user assumptions; exact TermId duplicates retain
        // the first occurrence so the solver never receives one literal twice.
        let mut seen: HashSet<TermId> = HashSet::default();
        let combined: Vec<TermId> = named_assumptions
            .into_iter()
            .chain(assumptions.iter().copied())
            .filter(|term| seen.insert(*term))
            .collect();
        let original_assertions = std::mem::replace(&mut self.ctx.assertions, unnamed_assertions);
        let result = self.complete_named_core_redirect(&combined);

        // Restoration precedes propagation of any error. Core bookkeeping is
        // then narrowed back to the caller's literals for the SMT-LIB subset
        // contract; the name snapshot remains available to get-unsat-core.
        self.ctx.assertions = original_assertions;
        self.last_core_term_to_name = Some(term_to_name);
        self.last_assumptions = Some(assumptions.to_vec());
        result
    }

    /// Certify, rescue, and minimize while named roots remain in the temporary
    /// solver-assumption slot. No nested-array quarantine is allowed here.
    fn complete_named_core_redirect(&mut self, combined: &[TermId]) -> Result<SolveResult> {
        // What the verdict cost to decide and certify: the minimizer's
        // affordability gate (#uc-minimize-entry-cost) is keyed on it.
        let entry_started = Instant::now();
        let result = self.check_sat_assuming_deferred_to_named_outer(combined);
        let result = self.certify_assumption_core(combined, result);
        let entry_elapsed = entry_started.elapsed();
        let (result, rescue_elapsed) = match result {
            Ok(SolveResult::Unknown) => {
                let rescue_started = Instant::now();
                let rescued = self.rescue_named_core_redirect_unknown(
                    combined,
                    AssumptionSatPublication::EmitHere,
                );
                (rescued, Some(rescue_started.elapsed()))
            }
            other => (other, None),
        };
        self.minimize_assumption_core(combined, result, rescue_elapsed, entry_elapsed)
    }

    /// Check if produce-unsat-assumptions is enabled (SMT-LIB 2.6 §4.1.7).
    fn produce_unsat_assumptions_enabled(&self) -> bool {
        matches!(
            self.ctx.get_option("produce-unsat-assumptions"),
            Some(OptionValue::Bool(true))
        )
    }

    /// Certificate gate for assumption-core harvests (#unsat-core-miscount).
    ///
    /// The SAT-literal -> TermId failed-assumption harvest can misattribute
    /// core members when an assumption literal is complementary to a named
    /// assertion's literal on the same variable and base assertions
    /// unit-propagate (order-dependent): the harvest is then a
    /// wrong-but-AUTHENTIC subset, which the print-time membership
    /// authentication in `unsat_core_entries` cannot catch. The printed-core
    /// contract ("core + unnamed assertions must be unsatisfiable") is
    /// therefore enforced here by construction, never assumed:
    ///
    /// - harvest == the full assumption set: certified by the solve itself;
    /// - harvest is a proper subset: re-solve with exactly the harvested
    ///   members against the SAME (stripped) base. UNSAT certifies the
    ///   harvest -- the recheck state (including its proof) is a valid UNSAT
    ///   state for the original query, and the certified harvest is pinned
    ///   back explicitly because the recheck's own sub-harvest is itself
    ///   uncertified. Anything else discards the harvest (the conservative
    ///   padded superset prints downstream) after restoring the original
    ///   solve state deterministically by re-solving the original query.
    ///
    /// Runs only on the core-producing paths (`:produce-unsat-cores` and, per
    /// #A7, `:produce-unsat-assumptions`), so plain solving pays nothing.
    /// Callers must invoke it against the SAME base assertion set the harvest
    /// was produced under — on the named-core path that means while the
    /// named/unnamed split is still in effect; on the plain
    /// produce-unsat-assumptions path the base is simply the full assertion
    /// set.
    pub(crate) fn certify_assumption_core(
        &mut self,
        combined: &[TermId],
        result: Result<SolveResult>,
    ) -> Result<SolveResult> {
        if !matches!(result, Ok(SolveResult::Unsat(_))) {
            return result;
        }
        let Some(core) = self.last_assumption_core.clone() else {
            return result;
        };
        if core.is_empty() {
            // Lost-provenance empty harvest: padded downstream (rule 1 of
            // `unsat_core_entries`).
            return result;
        }
        let combined_set: HashSet<TermId> = combined.iter().copied().collect();
        let core_set: HashSet<TermId> = core.iter().copied().collect();
        if core_set.len() == combined_set.len() && core_set.iter().all(|t| combined_set.contains(t))
        {
            // Harvest is the full assumption set: the original solve is the
            // certificate.
            return result;
        }
        // A bare same-engine UNSAT is not a certificate for a reduced public
        // core. Reconstruct the exact base + harvested assumptions in a
        // disposable public-query transaction and require a strict proof token
        // bound to this outer epoch/source/root/term snapshot. The cloned probe
        // cannot clobber the outer proof or model state, so no restorative
        // re-solve or provenance rerooting is needed.
        let mut obligation = self.ctx.assertions.clone();
        obligation.extend(core.iter().copied());
        let remaining = self
            .solve_deadline
            .get()
            .map(|deadline| deadline.saturating_duration_since(Instant::now()));
        let budget_ms =
            u64::try_from(harvest_recheck_budget(remaining).as_millis()).unwrap_or(u64::MAX);
        let rechecked = self
            .checked_exact_unsat_solve(obligation.clone(), budget_ms)
            .is_some_and(|checked| checked.consume(self, &obligation));
        if ay_core::misc_cli_flags().phase_trace {
            eprintln!(
                "c phase-trace uc-certify harvest={} of={} rechecked={rechecked}",
                core_set.len(),
                combined_set.len()
            );
        }
        if rechecked {
            self.last_assumption_core = Some(core);
            return result;
        }
        // Uncertified harvest—the exact defect class this gate exists for.
        // Discard it so downstream prints the conservative padded superset.
        self.last_assumption_core = None;
        result
    }

    /// Rebase whatever provenance a nested same-executor re-solve left behind
    /// onto the outer query's authored authority.
    ///
    /// Soundness: this only ever NARROWS the authored set. When the nested
    /// solve left a provenance, `preserving_authority_from` replaces its roots
    /// with the outer roots and admits an inner premise or source path only if
    /// it is already expressed entirely in those outer roots. When the nested
    /// solve cleared provenance outright, the outer authority is reinstated
    /// verbatim. Either way no solver-generated term becomes an authored
    /// `assume`.
    fn reroot_proof_authority(
        &mut self,
        outer: Option<&super::theories::solve_harness::ProofProblemAssertionProvenance>,
    ) {
        let Some(outer) = outer else {
            return;
        };
        self.proof_problem_assertion_provenance =
            Some(match self.proof_problem_assertion_provenance.take() {
                Some(inner) => inner.preserving_authority_from(Some(outer)),
                None => outer.clone(),
            });
    }

    /// Completeness rescue for the named→assumption core redirect
    /// (#named-cores-ground-sat).
    ///
    /// The redirect (the plain-check-sat redirect in check_sat.rs and
    /// [`Self::check_sat_assuming_with_named_cores`]) moves EVERY named
    /// assertion into the assumption set so the SAT-level failed-assumption
    /// harvest can name core participants. That is a core-TRACKING strategy,
    /// not a verdict authority: the assumption lanes are incomplete on
    /// combinations the plain pipeline decides (observed: a trivially-SAT
    /// ground mixed Int/BV/Array query — deductive-checks's standard encoding —
    /// classified QfBvLiaIndep; `solve_bv_core` disables preprocessing
    /// whenever assumptions are present (#5581) and the resulting
    /// trusted-BV-model Sat fails the emission gates, demoting to Unknown,
    /// while the identical un-named query is sat). The redirect must never
    /// cost completeness relative to the un-named equivalent, so on a final
    /// Unknown re-solve `base ∧ assumptions` through the PLAIN pipeline via
    /// the scoped fallback (`check-sat-assuming A` ≡ `check-sat (base ∧ A)`:
    /// verdict-identical, SAT models re-validated, conservative
    /// all-assumptions core on UNSAT) and mint any Sat through the single
    /// SAT-emission chokepoint so the API boundary accepts the verdict
    /// (#sat-chokepoint). Re-solving an Unknown can only improve
    /// completeness, never flip a decided verdict.
    ///
    /// UNSAT-core soundness is preserved by construction: a rescue UNSAT
    /// records the FULL assumption set as the core (reduction 0), which is
    /// exactly the checked set minus the unnamed base — always unsatisfiable
    /// together with the unnamed assertions.
    ///
    /// PRECONDITION: `self.ctx.assertions` still holds the STRIPPED
    /// (unnamed-only) base and `assumptions` is the combined
    /// named-plus-user-literal set of the failed redirected check.
    pub(in crate::executor) fn rescue_named_core_redirect_unknown(
        &mut self,
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        if ay_core::misc_cli_flags().phase_trace {
            eprintln!("c phase-trace named-core-redirect direct=unknown rescue=scoped");
        }
        // Fresh per-call deadline, mirroring the raw `check_sat_assuming`
        // entry: the rescue is a full second solve and must honor the
        // configured timeout rather than inherit an exhausted budget.
        let previous_deadline = self.install_timeout_deadline_for_call();
        let base_assertions = self.ctx.assertions.clone();
        // The rescue is a full second solve of the SAME public decision
        // problem, but it runs while the outer epoch is PARKED (check_sat.rs
        // parks it so nested finalizers cannot destroy it) and binds none of
        // its own — so every proof-authority lane (checked-SAT sidecar, qpf
        // instance authority, the quantifier UNSAT funnel) consulted a missing
        // scope and a rescue UNSAT needing a quantifier-instance proof always
        // demoted to unknown (the deductive-checks letleak shape: every VC assert is
        // `:named`, the redirect strips them into assumptions).
        //
        // Bind the rescue the exact identity its solve decides:
        // `check-sat-assuming A` == `check-sat (base && A)`, and
        // `solve_scoped_assumptions` folds the assumptions into the assertion
        // view — so the query is roots = base ++ A with an EMPTY bound
        // assumption set, every root caller-authored. Not borrowed authority:
        // certificates minted against it are re-verified by the ordinary
        // publication funnel, and the caller restores (and re-authenticates)
        // the parked outer authority after this returns.
        let mut rescue_roots = base_assertions.clone();
        rescue_roots.extend_from_slice(assumptions);
        self.begin_unsat_query_epoch(&rescue_roots);
        self.install_proof_source_provenance(&rescue_roots);
        self.bind_unsat_query_assumptions(&[]);
        let result = self.solve_scoped_assumptions_with_publication(
            &base_assertions,
            assumptions,
            Self::solve_current_assertions_with_quantifier_support,
            publication,
        );
        let result = match result {
            // SINGLE SAT-EMISSION CHOKEPOINT (#sat-chokepoint): this path
            // returns to the redirect callers (not through the main dispatch's
            // funnel call), so it MUST funnel its own proposed Sat through
            // `emit_sat_verdict` to run the model gates and mint the
            // SatCertificate — an unminted Sat is fail-closed to Unknown at
            // the API boundary.
            Ok(SolveResult::Sat) => self.publish_or_defer_assumption_sat(assumptions, publication),
            other => other,
        };
        self.restore_timeout_deadline_after_call(previous_deadline);
        result
    }

    /// `check_sat_assuming_with_controls`, then the assumption-query form of
    /// the #array-refutation-retry re-solve (see
    /// `array_refutation_resolve`): an `unknown` left by a refuted
    /// or unvalidated model on a query with an asserted store-chain equality
    /// is re-solved ONCE with the array fixpoint asserting the written-index
    /// read instances. A call made from inside an armed re-solve (a nested
    /// assumption probe) leaves the outer re-solve's flags alone.
    fn check_sat_assuming_with_array_refutation_retry(
        &mut self,
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        if self.array_refutation_instances_armed {
            return self.check_sat_assuming_with_controls(assumptions, publication);
        }
        self.array_model_refuted = false;
        self.array_refutation_retry_done = false;
        let first = self.check_sat_assuming_with_controls(assumptions, publication)?;
        if !self.array_refutation_retry_armed(&first, assumptions) {
            return Ok(first);
        }
        self.array_refutation_retry_done = true;
        self.array_refutation_instances_armed = true;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.last_model = None;
        let retry = self.check_sat_assuming_with_controls(assumptions, publication);
        // Never let the fixpoint-facing flag outlive the re-solve.
        self.array_refutation_instances_armed = false;
        let retry = retry?;
        self.last_statistics
            .set_int("model_validation.array_refutation_retry", 1);
        Ok(retry)
    }

    fn check_sat_assuming_with_controls(
        &mut self,
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        // Scope-transience for the RM domain axioms the inner gate may push
        // (#P0.2 Pass B): the assumption routes have no
        // `scope_tracked_assertions` restore of their own, so restore the exact
        // entry vector on EVERY exit path. This must not be length-only: an
        // inner combined/array solve may destructively rewrite the prefix while
        // retaining its length.
        let base_assertions_exact = self.ctx.assertions.clone();
        let result = self.check_sat_assuming_with_controls_inner(assumptions, publication);
        self.ctx.assertions = base_assertions_exact;
        result
    }

    /// Per-check reset for `check-sat-assuming` and unsat-core subset re-solves (#uc-core-minimize).
    ///
    /// FACTORED OUT for the minimization loop: `solve_scoped_assumptions`
    /// assumes it runs right after this reset (the rescue calls it exactly
    /// once per check). Repeated scoped re-solves WITHOUT the reset let
    /// per-check scratch state (array axiom scope, ROW seeding, delegated
    /// validation sets, ...) compound across attempts — measured as an RSS
    /// blow-up/hang on QF_AX swap subset re-solves that are trivially cheap
    /// in a fresh process.
    pub(in crate::executor) fn reset_solve_session_state(&mut self) {
        self.clear_active_solve_phase();
        // Clear any previous model/proof
        self.last_model = None;
        self.last_proof = None;
        self.clear_finite_enum_proof_state();
        self.last_unsat_proof_reconstruction_suppressed = false;
        self.last_proof_surface_withheld = None;
        self.proof_source_work.reset();
        self.best_effort_rebuild_refutation_spent = 0;
        self.last_lrat_certificate = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.last_clause_trace = None;
        self.report_checked_refutation_clear("reset_solve_session_state");
        self.last_checked_sat_refutation = None;
        self.pending_nested_array_bool_bv_unsat = None;
        self.pending_bounded_bv_lia_unsat = None;
        self.clear_strict_native_bundle_states();
        self.last_var_to_term = None;
        self.last_trail_provenance = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.injected_axiom_theory_kinds.clear();
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.model_validation_delegated_assertions.clear();
        self.last_unknown_reason = None;
        self.last_statistics = Statistics::default();
        self.last_statistics.num_assertions = self.ctx.assertions.len() as u64;
        // M0(a): strict-check attribution counters are per-publication; they
        // share the statistics reset so a solve's dump never carries counts
        // from an earlier public query.
        self.strict_check_invocations.set(0);
        self.strict_check_steps_validated.set(0);
        // #strict-walk-memo: verdicts are per-publication too. The currency
        // key would already retire cross-query entries (any interning changes
        // the snapshot stamp), but clearing here bounds retained memory and
        // keeps the memo's lifetime exactly the counters' lifetime.
        self.strict_check_memo_hits.set(0);
        self.strict_walk_memo.borrow_mut().clear();
        // Keep public-query authority immutable: subset re-solves must not
        // promote temporary assertion windows to authored premises.
        self.clear_preprocessing_proof_records();
        self.last_proof_rebuild_originals.clear();
        self.last_proof_raw_original_assertions.clear();
        self.last_proof_expanded_let_sources.clear();
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        self.nra_algebraic_model.clear();
        self.clear_dt_theory_model();
        self.recorded_var_substitutions.clear();
        self.defer_model_validation = false;
        self.defer_counterexample_minimization = false;
        self.bypass_string_tautology_guard = false;
        self.slia_accepted_unknown = false;
        // Result-authorization markers are scoped to one public solve. The
        // assumption path and core-minimization subset re-solves share this
        // reset and must earn every authorization independently.
        self.sat_validated_by_mod_div_or_branch = false;
        self.nested_array_row_reduction_unsat = false;
        self.clear_quantified_sat_authority();
        self.ho_seq_unfold_array_free_unsat = false;
        self.simplifier_refutation_unsat = false;
        self.nested_array_free_justification_unsat = false;
        self.justified_obligation_has_nested_arrays = None;
        self.array_axiom_scope = None;
        self.array_axiom_dead_skolems.clear();
        self.row_seeded_terms.clear();
        self.proof_check_result = None;
    }

    fn check_sat_assuming_with_controls_inner(
        &mut self,
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        self.reset_solve_session_state();

        // Establish the new proof session before any route-independent
        // preprocessing emits certified axioms. In particular, RM finite-domain
        // coverage below records theory lemmas through the shared axiom site;
        // resetting afterward used to erase those certificates and later
        // reconstruct the generated roots as unauthorized free assumptions.
        if matches!(
            self.ctx.get_option("produce-proofs"),
            Some(OptionValue::Bool(true))
        ) {
            self.proof_tracker.enable();
        }
        self.proof_tracker.reset_session();

        // Store assumptions for potential get-unsat-assumptions call
        self.last_assumptions = Some(assumptions.to_vec());

        // Honor external stop conditions before any structural preflight, then
        // reject unsupported native BV widths before datatype/array footprint
        // analysis or theory routing can allocate from them.
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let solve_roots = self.public_solve_roots(assumptions);
        if let Some(result) = self.reject_array_ext_witness_capture(&solve_roots) {
            return Ok(result);
        }
        if let Some(result) = self.reject_unsupported_bitvector_width(&solve_roots) {
            return Ok(result);
        }
        if let Some(result) = self.reject_unsupported_fp_model_format(&solve_roots) {
            return Ok(result);
        }
        // Match plain check-sat's public W7 admission boundary over the exact
        // caller-authored base-plus-assumption window. This must precede RM
        // coverage, singleton-sort axioms, and every direct theory route so a
        // generated simplification cannot erase the feature that caused the
        // closed validator to decline. Optimization/soft roots are not part of
        // the first satisfiability-only slice.
        if self.named_bv_lia_authored_slice_declined(&solve_roots) {
            self.last_statistics
                .set_string("solver.logic_category", "Other");
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(self.finalize_assumption_unknown(publication));
        }
        // Datatype-carrying-array degrade-gate bypass for the assumption
        // routes: computed at ENTRY (assertions + assumptions still in their
        // original shape, before preprocessing erases array structure) and
        // ONLY via the route-independent observational-completeness argument —
        // the bridge-axiom bypass stays exclusive to `solve_with_dt_axioms`,
        // which actually emits those axioms.
        self.dt_array_injectivity_gate_bypass = !self
            .problem_has_uncovered_dt_element_array(assumptions)
            && (self.dt_array_footprint_observationally_complete(assumptions)
                || self.dt_array_extensionality_modeled(assumptions));
        // Perf-backstop flag (#dt-array-degrade-backstop): cleared per solve.
        self.last_degrade_was_datatype_array = false;

        // Set-cardinality fail-closed gate (#capi-set-has-size): see
        // `terms_contain_set_has_size` in check_sat.rs. Covers both the base
        // assertions and the passed assumptions.
        if self.terms_contain_set_has_size(&solve_roots) {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(self.finalize_assumption_unknown(publication));
        }

        // Direct assumption routes also require Complex product reconstruction.
        let complex_axioms = self.complex_product_axioms(&solve_roots);
        if !complex_axioms.is_empty() {
            let authored_base = self.ctx.assertions.clone();
            self.install_proof_source_provenance(&authored_base);
            for axiom in complex_axioms {
                self.push_array_axiom_assertion_site(axiom, "complex_product_reconstruct");
            }
        }

        // RoundingMode finite-domain axioms (#P0.2 symbolic RoundingMode,
        // Pass B) for the ASSUMPTION routes: the QfUf/QfAx/propositional
        // assumption arms dispatch straight to
        // `solve_with_assumptions_for_theory` and never run check_sat.rs
        // preprocessing, so without this gate
        // `(check-sat-assuming ((distinct a b c d e f)))` over six RM consts
        // was a live wrong `sat` (z3: unsat). Covers base assertions AND
        // assumptions, BEFORE category dispatch. Pushed into `ctx.assertions`
        // (so `base_assertions` below picks them up on every arm) and made
        // scope-transient by the wrapper's truncate. Fail-closes to `unknown`
        // on any RM shape the pass cannot fully cover.
        let mut rm_roots = self.ctx.assertions.clone();
        rm_roots.extend_from_slice(assumptions);
        match self.rm_domain_axioms(&rm_roots) {
            crate::executor::rm_domain::RmDomainAxioms::NoMention => {}
            crate::executor::rm_domain::RmDomainAxioms::Axioms(axioms) => {
                // Freeze the caller-authored base before adding these theory
                // axioms. Native API assertions have no parsed-source prefix,
                // so the legacy fallback otherwise treats the current
                // assertion stack as authored; after this scoped solve restores
                // the stack, strict export correctly sees the generated roots
                // as foreign assumptions. Keeping explicit provenance here
                // makes proof reconstruction derive/certify them instead.
                let authored_assertions = self.ctx.assertions.clone();
                self.install_proof_source_provenance(&authored_assertions);
                for axiom in axioms {
                    self.push_array_axiom_assertion_site(axiom, "rm_domain_coverage");
                }
            }
            crate::executor::rm_domain::RmDomainAxioms::FailClose => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                return Ok(self.finalize_assumption_unknown(publication));
            }
        }

        // The direct assumption routes bypass check_sat.rs preprocessing.
        // Replay the route-independent singleton-sort soundness pass over BOTH
        // base assertions and assumptions, pushing its model-preserving facts
        // into the scope-transient base. This is needed even for QfUf/QfAx:
        // singleton-sorted terms may occur only as UF arguments, where an
        // equality fact is what exposes the congruence conflict.
        let mut singleton_roots = self.ctx.assertions.clone();
        singleton_roots.extend_from_slice(assumptions);
        if !self
            .add_ground_singleton_sort_equalities(&singleton_roots)
            .is_complete()
        {
            // The wrapper truncates any already-emitted scope-transient facts.
            // Never route assumptions against only a prefix of the closure.
            return Ok(SolveResult::Unknown);
        }

        // Snapshot the pre-route base. Exact finite-array owners may append
        // route-local axioms below; quantified fallback needs this authored
        // window, while direct ground dispatch receives the post-gate snapshot.
        let initial_base_assertions = self.ctx.assertions.clone();

        let mut all_assertions = initial_base_assertions.clone();
        all_assertions.extend(assumptions.iter().copied());
        let mut field_roots = all_assertions.clone();
        field_roots.extend(self.ctx.objectives().iter().map(|o| o.term));
        field_roots.extend(self.ctx.soft_constraints().iter().map(|o| o.term));
        if let Some(result) = self.try_finite_field(&field_roots) {
            let result = if result.is_sat() {
                self.publish_or_defer_assumption_sat(assumptions, publication)?
            } else {
                result
            };
            if result.is_unsat() {
                self.last_assumption_core = Some(assumptions.to_vec());
            }
            return Ok(self.finish_check_sat_assuming_result(assumptions, result, publication));
        }

        if initial_base_assertions.is_empty() && assumptions.is_empty() {
            // SOUNDNESS: No assertions and no assumptions means the formula is
            // trivially satisfiable (empty conjunction = true). This fast path
            // bypasses check_sat_guarded() and finalize_sat_model_validation(),
            // which is correct because there are no assertions to validate against.
            // Part of #7912 (Gap A).
            debug_assert!(
                self.ctx.assertions.is_empty(),
                "BUG: base_assertions empty but ctx.assertions non-empty"
            );
            debug_assert!(
                assumptions.is_empty(),
                "BUG: entered empty-assertions fast path with non-empty assumptions"
            );
            // SINGLE SAT-EMISSION CHOKEPOINT (#sat-chokepoint): even the trivial
            // all-empty SAT is minted through `emit_sat_verdict` so it carries a
            // SatCertificate; with no assertions/assumptions the funnel takes its
            // nothing-to-validate fast path.
            return self.publish_or_defer_assumption_sat(assumptions, publication);
        }

        let (pre_quantifier_category, pre_quantifier_features) =
            self.detect_logic_category(&all_assertions);
        let named_bv_lia_logic = self.declares_named_bv_lia_combination();
        // Preserve the authored live-window admission decision before either
        // the BV/LIA bridge or quantifier preprocessing can erase the feature
        // which caused the dedicated validator to decline.
        if named_bv_lia_logic && pre_quantifier_category == LogicCategory::Other {
            self.last_statistics
                .set_string("solver.logic_category", "Other");
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(self.finish_check_sat_assuming_result(
                assumptions,
                SolveResult::Unknown,
                publication,
            ));
        }
        let route_admitted =
            !named_bv_lia_logic || pre_quantifier_category == LogicCategory::QfBvLia;
        if route_admitted && (named_bv_lia_logic || pre_quantifier_features.has_bv_int_conversion) {
            let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
            if bridge_result.is_unsat() {
                return Ok(self.finish_check_sat_assuming_result(
                    assumptions,
                    bridge_result,
                    publication,
                ));
            }
        }

        if all_assertions
            .iter()
            .copied()
            .any(|assertion| contains_quantifier(&self.ctx.terms, assertion))
        {
            let result = self.solve_quantified_assumptions(
                &initial_base_assertions,
                assumptions,
                publication,
            )?;
            return Ok(self.finish_check_sat_assuming_result(assumptions, result, publication));
        }

        let (category, features) = self.detect_logic_category(&all_assertions);
        self.last_statistics
            .set_string("solver.logic_category", format!("{category:?}"));
        if ay_core::misc_cli_flags().phase_trace {
            eprintln!("c phase-trace check-sat-assuming category={category:?}");
        }
        self.set_active_solve_phase("assumption-solving", format!("theory:{category:?}"));

        if let Some(result) =
            self.try_solve_via_bounded_scalar_mod(category, &features, assumptions)
        {
            return Ok(self.finish_check_sat_assuming_result(assumptions, result, publication));
        }

        // One route-aware assumption boundary covers base and temporary roots.
        // Dedicated array routes defer here because they must enumerate after
        // substitution/fixpoint preprocessing; every other array category gets
        // exact closure before its assertion snapshot is handed to the solver.
        if features.has_arrays {
            if self.should_defer_finite_array_extensionality_to_route(category) {
                self.record_finite_array_extensionality_route_deferral();
            } else {
                let _ = self.add_finite_index_array_closure_with_roots(assumptions);
            }
        }
        // Include any route-independent generated axioms in the direct solver's
        // base window. Post-preprocessing owners add their axioms internally.
        let base_assertions = self.ctx.assertions.clone();

        // Use assumption-based solving for supported theories
        let result = match category {
            LogicCategory::Propositional => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Propositional,
            ),
            LogicCategory::QfUf => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Euf,
            ),
            LogicCategory::QfS => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Strings,
            ),
            LogicCategory::QfAx => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::ArrayEuf,
            ),
            LogicCategory::QfLra => {
                // The direct route runs a bare `DpllT::solve_with_assumptions`,
                // whose final check maps LRA's model-equality requests
                // (assume_eqs / fixed-term / ITE links, #6617/#8901) to Unknown
                // — no split loop runs under assumptions. Observed (#R1,
                // the development design notes): a tight
                // assumption through an equality row (x,y in [0,1], x+y-z=1,
                // assume z>=1) fixes several vars to one value, LRA's final
                // check emits NeedModelEqualities, and a trivially-SAT query
                // answers unknown — which silently disabled the OMT simplex
                // confirm-solve and produced wrong (maximize) optima. Same
                // remedy as the QfNia arm below: on Unknown, retry through the
                // scoped-assumption fallback (`check-sat-assuming A` ≡
                // `check-sat (base ∧ A)`: verdict-identical, SAT models
                // re-validated, conservative all-assumptions core). Retrying
                // an Unknown can only improve completeness, never flip a
                // decided verdict.
                let direct = self.solve_with_assumptions_for_theory(
                    &base_assertions,
                    assumptions,
                    TheoryKind::Lra,
                )?;
                if matches!(direct, SolveResult::Unknown) {
                    self.solve_scoped_assumptions_with_publication(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                        publication,
                    )
                } else {
                    Ok(direct)
                }
            }
            LogicCategory::QfLia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
                    if bridge_result.is_unsat() {
                        return Ok(self.finish_check_sat_assuming_result(
                            assumptions,
                            bridge_result,
                            publication,
                        ));
                    }
                }
                self.solve_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfNia | LogicCategory::QfEia => {
                // The direct theory-assumption route runs a bare
                // `DpllT::solve_with_assumptions`, which returns Unknown as
                // soon as the theory requests a split (branch-and-bound
                // NeedSplit and friends are handled only by the full
                // pipeline's solve_step loop). QF_NIA queries whose proof
                // needs integer splitting — e.g. the truncating-`mul`
                // range-collapse goals of upstream Verus nonlinear.rs test5
                // (#2778) — therefore came back Unknown here even though the
                // plain check-sat pipeline decides them. Keep the fast direct
                // route, but on Unknown retry through the scoped-assumption
                // fallback (`check-sat-assuming A` ≡ `check-sat (base ∧ A)`:
                // verdict-identical, SAT models re-validated, conservative
                // all-assumptions core — the same contract as the
                // QfUfnia/QfUfnira arm below). Retrying an Unknown can only
                // improve completeness, never flip a decided verdict.
                let direct = self.solve_with_assumptions_for_theory(
                    &base_assertions,
                    assumptions,
                    TheoryKind::Nia,
                )?;
                if matches!(direct, SolveResult::Unknown) {
                    self.solve_scoped_assumptions_with_publication(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                        publication,
                    )
                } else {
                    Ok(direct)
                }
            }
            LogicCategory::QfNra => {
                // Mirrors the QfNia arm above (and QfLra below): the direct
                // theory-assumption route runs a bare
                // `DpllT::solve_with_assumptions`, which returns Unknown as soon
                // as the theory requests work only the full pipeline's
                // solve_step loop performs — for NRA that is the ICP / lifting /
                // model-repair escalation, none of which runs under a bare
                // assumption solve. The arm previously returned that Unknown
                // directly, so a QF_NRA `check-sat-assuming` could answer
                // unknown on a query the plain check-sat pipeline decides, while
                // its QfNia sibling retried and decided. Keep the fast direct
                // route, but on Unknown retry through the scoped-assumption
                // fallback (`check-sat-assuming A` ≡ `check-sat (base ∧ A)`:
                // verdict-identical, SAT models re-validated by the strict gate,
                // conservative all-assumptions core). Retrying an Unknown can
                // only improve completeness, never flip a decided verdict.
                let direct = self.solve_with_assumptions_for_theory(
                    &base_assertions,
                    assumptions,
                    TheoryKind::Nra,
                )?;
                if matches!(direct, SolveResult::Unknown) {
                    self.solve_scoped_assumptions_with_publication(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                        publication,
                    )
                } else {
                    Ok(direct)
                }
            }
            LogicCategory::QfNira => {
                if features.has_real {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_with_assumptions_for_theory(
                        &base_assertions,
                        assumptions,
                        TheoryKind::Nia,
                    )
                }
            }
            LogicCategory::QfUfnra | LogicCategory::QfUfnia | LogicCategory::QfUfnira => {
                // UF + nonlinear arithmetic has no dedicated assumption
                // solver, but the regular pipeline handles these
                // quantifier-free conjunctions (EUF+LIA/LRA with NIA/NRA
                // incremental linearization). Route through the scoped-
                // assumption fallback — verdict-identical semantics
                // (`check-sat-assuming A` ≡ `check-sat (base ∧ A)`), SAT
                // models re-validated by `finalize_sat_assumption_
                // validation`, conservative all-assumptions core on UNSAT
                // (same contract as the quantified fallback) — instead of
                // hard-failing closed to Unknown. The pipeline itself stays
                // fail-closed (Unknown) for anything it cannot decide.
                //
                // Motivating shape (#uf-nia-assuming): a named-core-mode
                // client (deductive-checks) asserts ground divisor-guarded Euclidean
                // div/mod axioms over uninterpreted `div`/`mod` functions;
                // the reconstruction lemma carries one nonlinear product
                // `q*d`, flipping the category from QfUflia to QfUfnia, yet
                // the goals are decided by the EUF+LIA layer alone. The old
                // hard Unknown made every such query incomplete precisely
                // when `produce-unsat-cores` redirected named assertions
                // here.
                self.solve_scoped_assumptions_with_publication(
                    &base_assertions,
                    assumptions,
                    Self::solve_current_assertions_with_quantifier_support,
                    publication,
                )
            }
            LogicCategory::QfUflia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
                    if bridge_result.is_unsat() {
                        return Ok(self.finish_check_sat_assuming_result(
                            assumptions,
                            bridge_result,
                            publication,
                        ));
                    }
                }
                // QF_UFLIA's ordinary pipeline uses the dedicated ground
                // UF+LIA solver. The AUFLIA assumption solver instead selects
                // the array-capable combiner, bypassing that pipeline's
                // preprocessing and model construction even when there are no
                // arrays. Compound named assertions can therefore exhaust the
                // deadline or leave a model the independent gate rejects.
                // Solve the same conjunction through fresh scoped lanes, as
                // for UF+nonlinear arithmetic above. This preserves the base
                // and temporary-assumption boundary, revalidates SAT models,
                // and returns a conservative full assumption core on UNSAT.
                if has_only_uf_lia_theories(&features) {
                    self.solve_scoped_assumptions_with_publication(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                        publication,
                    )
                } else {
                    // Match the plain dispatcher's pure-theory boundary.
                    // Integer div/mod/rem still need the broader lane's
                    // assumption-aware lowering and alias substitution.
                    self.solve_auf_lia_with_assumptions(&base_assertions, assumptions)
                }
            }
            LogicCategory::QfSeq => self.solve_seq_with_assumptions(&base_assertions, assumptions),
            // Route Seq<BitVec> through the scoped-assertion Seq path so every
            // assumption participates in Seq axiom injection and BV comparison
            // transitivity before solving (#7656).
            LogicCategory::QfSeqBv => {
                self.solve_seq_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfSeqlia => {
                self.solve_seq_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfSet | LogicCategory::QfSetlia => {
                self.solve_set_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfMultiset | LogicCategory::QfMslia => {
                self.solve_multiset_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfMap | LogicCategory::QfMaplia => {
                self.solve_map_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfSlia => {
                self.solve_strings_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfSnia => {
                if features.has_nonlinear_int {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    self.solve_strings_lia_with_assumptions(&base_assertions, assumptions)
                }
            }
            LogicCategory::QfUflra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::UfLra,
            ),
            LogicCategory::QfAuflia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
                    if bridge_result.is_unsat() {
                        return Ok(self.finish_check_sat_assuming_result(
                            assumptions,
                            bridge_result,
                            publication,
                        ));
                    }
                }
                self.solve_auf_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfAuflra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::AufLra,
            ),
            LogicCategory::QfLira => {
                self.solve_lira_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfAuflira => {
                self.solve_auflira_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfFp => {
                self.solve_fp_with_scoped_assumptions(&base_assertions, assumptions, publication)
            }
            LogicCategory::QfBvfp => {
                self.solve_bvfp_with_scoped_assumptions(&base_assertions, assumptions, publication)
            }
            LogicCategory::QfAbvfp => {
                self.solve_abvfp_with_scoped_assumptions(&base_assertions, assumptions, publication)
            }
            LogicCategory::QfBv => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Bv,
            ),
            LogicCategory::QfAbv => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::ArrayBv,
            ),
            LogicCategory::QfUfbv => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::UfBv,
            ),
            LogicCategory::QfAufbv => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::AufBv,
            ),
            LogicCategory::QfBvLia => {
                let direct = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
                if direct.is_unknown() {
                    // The direct bridge sees assumptions separately. A forced
                    // Boolean definition can therefore hide the top-level
                    // arithmetic facts needed by an exact bounded bridge.
                    // Retry the identical conjunction through ordinary
                    // preprocessing on query-local lanes. The existing scoped
                    // helper preserves authored assumption authority, the live
                    // deadline, and final model/proof validation; its temporary
                    // units never enter the session's persistent encoders.
                    self.solve_scoped_assumptions_with_publication(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                        publication,
                    )
                } else {
                    Ok(direct)
                }
            }
            LogicCategory::QfBvLiaIndep => {
                self.solve_bv_lia_indep_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::Lia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
                    if bridge_result.is_unsat() {
                        return Ok(self.finish_check_sat_assuming_result(
                            assumptions,
                            bridge_result,
                            publication,
                        ));
                    }
                }
                self.solve_auf_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::Lra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Lra,
            ),
            LogicCategory::Nia | LogicCategory::Nra => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Ufnia | LogicCategory::Ufnra | LogicCategory::Ufnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Uf => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Euf,
            ),
            LogicCategory::Uflia | LogicCategory::Auflia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
                    if bridge_result.is_unsat() {
                        return Ok(self.finish_check_sat_assuming_result(
                            assumptions,
                            bridge_result,
                            publication,
                        ));
                    }
                }
                self.solve_auf_lia_with_assumptions(&base_assertions, assumptions)
            }
            // Same LRA final-check model-equality degrade as the QfLra arm
            // (the combined solvers embed the same LraSolver): retry Unknown
            // through the scoped fallback.
            LogicCategory::Auflra => {
                let direct = self.solve_with_assumptions_for_theory(
                    &base_assertions,
                    assumptions,
                    TheoryKind::AufLra,
                )?;
                if matches!(direct, SolveResult::Unknown) {
                    self.solve_scoped_assumptions_with_publication(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                        publication,
                    )
                } else {
                    Ok(direct)
                }
            }
            LogicCategory::Uflra => {
                let direct = self.solve_with_assumptions_for_theory(
                    &base_assertions,
                    assumptions,
                    TheoryKind::UfLra,
                )?;
                if matches!(direct, SolveResult::Unknown) {
                    self.solve_scoped_assumptions_with_publication(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                        publication,
                    )
                } else {
                    Ok(direct)
                }
            }
            LogicCategory::Lira => self.solve_lira_with_assumptions(&base_assertions, assumptions),
            LogicCategory::Auflira => {
                self.solve_auflira_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::Nira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::QfDt => 'dt_fd: {
                // Fast direct theory-assumption route first; on Unknown retry
                // through the scoped-assumption fallback (mirrors the QfNia
                // arm above). Named-core mode (produce-unsat-cores) redirects
                // EVERY named assertion here as an assumption, but the direct
                // DT assumption engine misses plain-pipeline passes (e.g. the
                // finite-enum pigeonhole preprocessing), so instances the
                // plain check-sat decides (20230720-blocksworld) came back
                // unknown in named mode. `check-sat-assuming A` ≡
                // `check-sat (base ∧ A)`: verdict-identical, SAT models
                // re-validated, conservative all-assumptions core on UNSAT
                // (reduction 0, error-free). Retrying an Unknown can only
                // improve completeness, never flip a decided verdict.
                // The finite-domain lane decides what its gate admits first
                // (#dt-fd-session, `dt_finite/assuming.rs`).
                if let Some(decided) =
                    self.try_dt_finite_domain_assuming(&base_assertions, assumptions)?
                {
                    break 'dt_fd Ok(decided);
                }
                let direct = self.solve_with_assumptions_for_theory(
                    &base_assertions,
                    assumptions,
                    TheoryKind::Dt,
                )?;
                let direct = self.reverify_minimized_dt_assumption_core(
                    direct,
                    &base_assertions,
                    assumptions,
                )?;
                if matches!(direct, SolveResult::Unknown) {
                    if ay_core::misc_cli_flags().phase_trace {
                        eprintln!("c phase-trace qfdt-assuming direct=unknown retry=scoped");
                    }
                    self.solve_scoped_assumptions_with_publication(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                        publication,
                    )
                } else {
                    Ok(direct)
                }
            }
            LogicCategory::DtAuflia => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                Some(Sort::Int),
                DtSolverDispatch::AufLia,
            ),
            LogicCategory::DtAuflra => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                Some(Sort::Real),
                DtSolverDispatch::Theory(TheoryKind::AufLra),
            ),
            LogicCategory::DtAuflira => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                Some(Sort::Int),
                DtSolverDispatch::AufLira,
            ),
            LogicCategory::DtUfbv => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                None,
                DtSolverDispatch::Theory(TheoryKind::UfBv),
            ),
            LogicCategory::DtAufbv => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                None,
                DtSolverDispatch::Theory(TheoryKind::AufBv),
            ),
            LogicCategory::DtAx => 'dt_fd: {
                // Same Unknown-retry contract as the QfDt arm above: the
                // 20230720-blocksworld QF_DT instances (recursive Tower +
                // 21-ctor enum) classify as DtAx and, in named-core mode,
                // arrive here with every assertion as an assumption; the
                // combined route returns Unknown on instances the plain
                // pipeline decides. Retrying through the scoped fallback
                // turns those into answered verdicts (conservative
                // all-assumptions core on UNSAT — reduction 0, error-free).
                // The finite-domain lane decides what its gate admits first
                // (#dt-fd-session, `dt_finite/assuming.rs`).
                if let Some(decided) =
                    self.try_dt_finite_domain_assuming(&base_assertions, assumptions)?
                {
                    break 'dt_fd Ok(decided);
                }
                let direct = self.dt_combined_check_sat_assuming(
                    &base_assertions,
                    assumptions,
                    None,
                    DtSolverDispatch::Theory(TheoryKind::ArrayEuf),
                )?;
                let direct = self.reverify_minimized_dt_assumption_core(
                    direct,
                    &base_assertions,
                    assumptions,
                )?;
                if matches!(direct, SolveResult::Unknown) {
                    if ay_core::misc_cli_flags().phase_trace {
                        eprintln!("c phase-trace dtax-assuming direct=unknown retry=scoped");
                    }
                    self.solve_scoped_assumptions_with_publication(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                        publication,
                    )
                } else {
                    Ok(direct)
                }
            }
            // Quantified DT logics (#7150): keep array-free UFDT on the pure
            // DT assumption engine. AUFDT must use the array-aware DT flow so
            // DT-generated finite cell equalities receive final exact closure.
            LogicCategory::Ufdt => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Dt,
            ),
            LogicCategory::Aufdt => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                None,
                DtSolverDispatch::Theory(TheoryKind::ArrayEuf),
            ),
            LogicCategory::Ufdtlia | LogicCategory::Aufdtlia => self
                .dt_combined_check_sat_assuming(
                    &base_assertions,
                    assumptions,
                    Some(Sort::Int),
                    DtSolverDispatch::AufLia,
                ),
            LogicCategory::Ufdtlra => self.dt_combined_check_sat_assuming(
                &base_assertions,
                assumptions,
                Some(Sort::Real),
                DtSolverDispatch::Theory(TheoryKind::AufLra),
            ),
            LogicCategory::Ufdtlira | LogicCategory::Aufdtlira => self
                .dt_combined_check_sat_assuming(
                    &base_assertions,
                    assumptions,
                    Some(Sort::Int),
                    DtSolverDispatch::AufLira,
                ),
            LogicCategory::Ufdtnia | LogicCategory::Ufdtnra | LogicCategory::Ufdtnira => {
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            LogicCategory::Other => {
                // Match plain check-sat: a theory mix with no combined
                // decision procedure returns the standard SMT-LIB `unknown`,
                // never an error (see the plain path's `Other` arm).
                let _ = features;
                Ok(self.refuse_theory_mix_without_a_lane())
            }
        }?;
        let result = self.fail_close_incomplete_finite_array_sat(Ok(result))?;
        let result = self.refuse_unsat_held_by_evaluation_stop(result);

        let result = if result == SolveResult::Sat {
            // Direct queries emit here. A named-core redirect nested under
            // plain check-sat leaves the affine model Pending for that outer
            // query's sole SAT funnel.
            self.publish_or_defer_assumption_sat(assumptions, publication)?
        } else {
            result
        };

        if result == SolveResult::Sat {
            let public_roots = match self.independent_gate_query_roots() {
                Ok(roots) => roots,
                Err(_) => {
                    return Ok(SolveResult::Unknown);
                }
            };
            debug_assert!(
                self.last_model.is_some()
                    || (publication == AssumptionSatPublication::DeferToPlainCheckSat
                        && self.has_current_pending_certificate_model_transport(&public_roots)),
                "BUG: assumption solve returned SAT without a model or exact Pending transport"
            );
        }
        if result.is_unsat() {
            debug_assert!(
                self.last_assumption_core.is_some(),
                "BUG: check_sat_assuming returned UNSAT without populating assumption core"
            );
        }

        // #7912 postcondition: every SAT result has been validated at some level.
        // Mirrors the postcondition in check_sat_guarded(). A deferred
        // named-core solve is deliberately still a proposal: an ordinary
        // candidate model (or an affine Pending model) is its transport to the
        // outer plain-check-sat funnel, which performs the sole public
        // validation after restoring the authored assertion stack.
        debug_assert!(
            result != SolveResult::Sat
                || self.last_model_validated
                || self.skip_model_eval
                || (publication == AssumptionSatPublication::DeferToPlainCheckSat
                    && (self.last_model.is_some()
                        || self.has_current_pending_certificate_model_transport(&match self
                            .independent_gate_query_roots()
                        {
                            Ok(roots) => roots,
                            Err(_) => return Ok(SolveResult::Unknown),
                        },)))
                || (self.ctx.assertions.is_empty() && assumptions.is_empty()),
            "BUG: check_sat_assuming returned SAT without any model validation path — \
             last_model_validated={}, skip_model_eval={}, assertions={}, assumptions={}",
            self.last_model_validated,
            self.skip_model_eval,
            self.ctx.assertions.len(),
            assumptions.len(),
        );

        // Capture trail provenance for SAT results (#8153)
        if result == SolveResult::Sat {
            self.capture_trail_provenance();
        }

        Ok(self.finish_check_sat_assuming_result(assumptions, result, publication))
    }

    /// Quantified `check-sat-assuming` fallback.
    ///
    /// The dedicated assumption solvers do not understand quantified formulas;
    /// routing quantified assertions there bypasses E-matching/CEGQI entirely
    /// and can return false SAT. For quantified assumption checks, temporarily
    /// solve over `base_assertions ∪ assumptions` using the regular quantifier
    /// pipeline, then restore the original assertion stack.
    ///
    /// UNSAT assumption cores are conservative: derived instantiations lose the
    /// SAT selector provenance of the assumptions that triggered them, so we
    /// report all active assumptions as the core rather than a potentially
    /// unsound subset.
    ///
    /// The solve runs in an isolated incremental window. The merged vector is
    /// an ordinary assertion set to every lane below, and the lanes that keep
    /// a persistent SAT solver (`solve_propositional`, `solve_nia`,
    /// `solve_nra`, the BV lane) encode what they are handed into it at the
    /// current scope depth — at depth 0 as a PERMANENT unit. Once the universal
    /// is handled by instantiation, a ground remainder of free Boolean
    /// assumptions is exactly such a propositional solve: `(check-sat-assuming
    /// (g1))` left `g1` asserted for good, and the next query refuted
    /// `(not g1)` (D10(b), `--z3-mode` wrong UNSAT). The window hands those
    /// lanes a fresh state and restores the outer one afterwards, so the
    /// assumptions live exactly as long as this query. It isolates in every
    /// mode: the predecessor's conditional isolation missed non-incremental
    /// sessions, while `solve_scoped_window` always forks this state. The
    /// D10(b) witness (two `check-sat-assuming`, no `push`) is not incremental.
    fn solve_quantified_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        let mut combined_assertions = base_assertions.to_vec();
        combined_assertions.extend(assumptions.iter().copied());

        let solve_result = self
            .with_isolated_incremental_state(Some(combined_assertions), |exec| {
                exec.solve_current_assertions_with_quantifier_support()
            });

        match solve_result? {
            SolveResult::Sat => {
                // SINGLE SAT-EMISSION CHOKEPOINT (#sat-chokepoint): this path
                // early-returns (it does not flow through the main dispatch's
                // funnel call), so it MUST funnel its own proposed Sat through
                // `emit_sat_verdict` to run the model gates and mint the
                // SatCertificate. Quantified logics are non-authoritative, so the
                // authoritative-failclosed gate keeps genuine quantifier coverage
                // gaps as Sat.
                self.publish_or_defer_assumption_sat(assumptions, publication)
            }
            SolveResult::Unsat(_) => {
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::unsat())
            }
            SolveResult::Unknown => Ok(SolveResult::Unknown),
        }
    }

    /// FP/BVFP `check-sat-assuming` fallback.
    ///
    /// FP assumptions are solved by temporarily extending the assertion stack
    /// and running the regular FP pipeline so supported predicates no longer
    /// fail closed as `unknown`.
    fn solve_fp_with_scoped_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        self.solve_scoped_assumptions_with_publication(
            base_assertions,
            assumptions,
            Self::solve_fp,
            publication,
        )
    }

    fn solve_bvfp_with_scoped_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        self.solve_scoped_assumptions_with_publication(
            base_assertions,
            assumptions,
            Self::solve_bvfp,
            publication,
        )
    }

    fn solve_abvfp_with_scoped_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        self.solve_scoped_assumptions_with_publication(
            base_assertions,
            assumptions,
            Self::solve_abvfp,
            publication,
        )
    }

    /// FAIL-CLOSED re-verification of minimized DT assumption cores
    /// (#uc-qfdt). The direct DT assumption engines can return UNSAT with a
    /// `last_assumption_core` that is a PROPER subset of the assumptions; a
    /// core is only allowed out of the executor after an in-process
    /// re-verification, so re-solve `base ∧ core` through the plain pipeline
    /// before trusting it:
    ///
    /// - re-solve UNSAT: the minimized core is confirmed — keep it.
    /// - re-solve SAT/Unknown/Err: the core (and hence the direct verdict
    ///   that produced it) is suspect — drop the core and demote to
    ///   `Unknown`, so the caller's scoped retry re-solves the FULL problem
    ///   and, on UNSAT, records the conservative all-assumptions core
    ///   (reduction 0, error-free under 2025 UC scoring).
    ///
    /// Full (non-minimized) cores skip re-verification: they claim nothing
    /// beyond the verdict itself.
    fn reverify_minimized_dt_assumption_core(
        &mut self,
        result: SolveResult,
        base_assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if !result.is_unsat() {
            return Ok(result);
        }
        let Some(core) = self.last_assumption_core.clone() else {
            return Ok(result);
        };
        let distinct_assumptions: HashSet<TermId> = assumptions.iter().copied().collect();
        let core_set: HashSet<TermId> = core.iter().copied().collect();
        if core_set.len() >= distinct_assumptions.len() {
            return Ok(result); // nothing was minimized away
        }
        let mut combined_assertions = base_assertions.to_vec();
        combined_assertions.extend(core.iter().copied());
        let verified = self
            .checked_exact_unsat_solve(combined_assertions.clone(), 2_000)
            .is_some_and(|checked| checked.consume(self, &combined_assertions));
        if verified {
            // Confirmed. Restore the core (the verify pass may have
            // been preceded by an untrusted direct-engine nomination) and
            // drop any model from that nomination. The checked verifier is
            // isolated and transports no solver state.
            self.last_assumption_core = Some(core);
            self.last_model = None;
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!("c phase-trace dt-assumption-core reverify=confirmed");
            }
            Ok(result)
        } else {
            self.last_assumption_core = None;
            self.last_model = None;
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            if ay_core::misc_cli_flags().phase_trace {
                eprintln!("c phase-trace dt-assumption-core reverify=FAILED demote=unknown");
            }
            Ok(SolveResult::Unknown)
        }
    }

    /// `pub(in crate::executor)`: also the subset-solve engine of the
    /// unsat-core minimization pass (#uc-core-minimize, core_minimize.rs)
    /// for verdicts obtained through the scoped-plain rescue.
    ///
    /// The merged vector is an ordinary assertion set to every lane below, and
    /// the lanes that keep a persistent SAT solver (`solve_nia`, `solve_nra`,
    /// the LRA and propositional lanes, the BV lane) encode what they are
    /// handed into the SESSION's state at the current depth — at depth 0 a
    /// PERMANENT unit. So `(assert (is_int r0)) (check-sat-assuming (p1))
    /// (check-sat-assuming ((not p1)))` answered the second query under `p1`,
    /// and `(assert (>= (* y y x) 3)) (check-sat-assuming ((= (mod x 6) 6)))
    /// (check-sat)` the plain query under the unsatisfiable assumption
    /// (D10(a), `--z3-mode` wrong UNSAT; the default posture's certification
    /// rejected the refutation). The solve now runs on lanes that are never
    /// the session's own (`solve_scoped_window`), in EVERY session. A warm
    /// retry of an undecided window on the session's own lanes (a private
    /// scope inside a user scope, discarded lanes at depth 0) was measured and
    /// withdrawn: the window's residue left later queries `incomplete`, and a
    /// churning retry spent the query's whole time budget (2026-09-29
    /// scope-leak fix-up report).
    pub(in crate::executor) fn solve_scoped_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
        solve: fn(&mut Self) -> Result<SolveResult>,
    ) -> Result<SolveResult> {
        // Legacy callers own their assumption validation here. In particular,
        // core-subset probes and the finite-DT assumption helper keep this
        // behavior; no deferred policy is inferred from session flags.
        self.solve_scoped_assumptions_with_publication(
            base_assertions,
            assumptions,
            solve,
            AssumptionSatPublication::EmitHere,
        )
    }

    /// Solve the exact scoped conjunction, respecting the caller that owns
    /// publication. Only the private named-core plain-check caller can select
    /// deferred publication; an inner SAT is then a proposal for the restored
    /// outer SAT funnel, with no validation claim or public certificate.
    fn solve_scoped_assumptions_with_publication(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
        solve: fn(&mut Self) -> Result<SolveResult>,
        publication: AssumptionSatPublication,
    ) -> Result<SolveResult> {
        let mut combined_assertions = base_assertions.to_vec();
        combined_assertions.extend(assumptions.iter().copied());

        // Belt for R1: this route merges query-local ASSUMPTIONS into the
        // assertion vector. The persistent FP lane would encode each one into
        // `encoded_assertions` and install its activation unit at the current
        // scope depth — at depth 0 a PERMANENT unit, so the next check-sat is
        // solved under the previous query's assumptions (wrong UNSAT at once,
        // wrong SAT as soon as a negated assumption is retained). The primary
        // dispatch already declines to arm while `last_assumptions` is set;
        // this makes the sub-solve stateless no matter how it was reached.
        // (`solve_scoped_window` below does not cover the FP lane, so this
        // belt stays.)
        self.fp_persistent_armed = false;
        // The scoped route merges the assumptions INTO `ctx.assertions`, so
        // the inner solve sees the complete problem exactly as a plain
        // `check-sat (base ∧ A)` would. Clear `last_assumptions` for the
        // duration: lanes that bail when assumptions are carried SEPARATELY
        // (e.g. the enum finite-domain SAT lane) are needlessly disabled
        // here — their bail exists because they read only `ctx.assertions`,
        // which on THIS route is the full conjunction. Restored afterward
        // for `get-unsat-assumptions`.
        // Proof authority and model DATA both retain the actual original
        // assumption window while solver lanes see the lowered assertions.
        let saved_authority = self.install_scoped_assumption_authority(assumptions);
        let saved_window = self
            .model_construction_assumptions
            .replace(OriginalModelAssumptions(self.last_assumptions.take()));
        if ay_core::misc_cli_flags().phase_trace {
            eprintln!("c phase-trace scoped-assumptions window=fresh-lanes every-session");
        }
        let original_assertions = std::mem::replace(&mut self.ctx.assertions, combined_assertions);
        let solve_result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.solve_scoped_window(solve)
        }));
        self.ctx.assertions = original_assertions;
        let original = self.model_construction_assumptions.take();
        self.model_construction_assumptions = saved_window;
        let Some(original) = original else {
            self.proof_problem_assertion_provenance = saved_authority;
            return Err(ExecutorError::ModelValidation(
                crate::executor_types::ModelValidationError::incomplete(
                    ay_core::VerificationBoundary::SmtAssumption,
                    "scoped query lost its original assumption window",
                ),
            ));
        };
        self.last_assumptions = original.0;
        // Restore original proof authority after the separate assumption slot
        // is live again, and before propagating an error or unwind.
        if matches!(&solve_result, Ok(Ok(_))) {
            self.reroot_proof_authority(saved_authority.as_ref());
        } else {
            self.proof_problem_assertion_provenance = saved_authority;
        }
        let solve_result = solve_result.unwrap_or_else(|panic| std::panic::resume_unwind(panic));

        match solve_result? {
            SolveResult::Sat => {
                self.last_result = Some(SolveResult::Sat);
                match publication {
                    AssumptionSatPublication::EmitHere => {
                        self.finalize_sat_assumption_validation(assumptions)
                    }
                    AssumptionSatPublication::DeferToPlainCheckSat => {
                        // Keep the former finalizer's stop boundary. A stop is
                        // terminal even though ordinary validation belongs to
                        // the caller after it restores the original roots.
                        if self.publish_evaluation_stop() {
                            return Ok(SolveResult::Unknown);
                        }
                        // Do not complete, evaluate, fabricate or certify this
                        // candidate in the stripped base/assumption view.
                        self.last_model_validated = false;
                        self.last_sat_certificate = None;
                        Ok(SolveResult::Sat)
                    }
                }
            }
            SolveResult::Unsat(_) => {
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::unsat())
            }
            SolveResult::Unknown => Ok(SolveResult::Unknown),
        }
    }

    fn finish_check_sat_assuming_result(
        &mut self,
        assumptions: &[TermId],
        result: SolveResult,
        publication: AssumptionSatPublication,
    ) -> SolveResult {
        let result = self.refuse_unsat_held_by_evaluation_stop(result);
        if result.is_sat() {
            let public_roots = match self.independent_gate_query_roots() {
                Ok(roots) => roots,
                Err(_) => {
                    return SolveResult::Unknown;
                }
            };
            debug_assert!(
                self.last_model.is_some()
                    || (publication == AssumptionSatPublication::DeferToPlainCheckSat
                        && self.has_current_pending_certificate_model_transport(&public_roots)),
                "BUG: assumption solve returned SAT without a model or exact Pending transport"
            );
        }
        if result.is_unsat() {
            debug_assert!(
                self.last_assumption_core.is_some(),
                "BUG: check_sat_assuming returned UNSAT without populating last_assumption_core"
            );
            debug_assert!(
                self.last_assumption_core.as_ref().is_none_or(|core| {
                    let assumption_set: HashSet<TermId> = assumptions.iter().copied().collect();
                    core.iter().all(|t| assumption_set.contains(t))
                }),
                "BUG: UNSAT assumption core contains terms not in the original assumptions"
            );
        }
        // SOUNDNESS (QF_LRA false-UNSAT, multi-path): a disequality/ite/or
        // bearing QF_LRA/LRA assumption UNSAT publishes only with an
        // independent checked certificate; otherwise it fails closed to
        // `unknown`. The scan covers the assumption literals as well as
        // `ctx.assertions` (named assertions live in the assumption set under
        // `:produce-unsat-cores`). See `fragile_lra_gate.rs`.
        if result.is_unsat() && self.fragile_lra_assumption_unsat_uncertified(assumptions) {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            let result = self.finalize_assumption_unknown(publication);
            if publication == AssumptionSatPublication::EmitHere {
                self.finalize_unknown_diagnostics();
            }
            return result;
        }
        // PROOF NET (mirrors the plain path's `check_sat.rs:2388` / `:3608`).
        //
        // The mandatory UNSAT funnel refuses to publish `unsat` without a
        // certificate, and `begin_public_solve` (lifecycle.rs:302) turns proof
        // tracking on for EVERY public decision precisely so that guarantee
        // cannot be switched off. The plain path backs that up with two
        // `last_proof.is_none()` nets plus UNSAT-implies-proof debug_asserts.
        //
        // This path had neither. Most assumption routes do build a proof —
        // `solve_with_assumptions_for_theory`'s `AssumeResult::Unsat` arm goes
        // through `solve_and_store_model_full` (theories/model_helpers.rs:318),
        // which is why QF_LIA and QF_UF assumption refutations were already
        // fine — but any lane that returns a bare `Ok(SolveResult::unsat())`
        // (e.g. the strings/LIA lane) reached the funnel with
        // `last_proof == None`, and a CORRECT refutation was published as
        // `unknown` ("the provisional UNSAT verdict has no proof"). Measured:
        // `(assert (= (str.len s) 3))` + `(check-sat-assuming ((= s "ab")))`
        // returned `unknown`, while the same conjunction under plain
        // `check-sat` returned `unsat` with a full Alethe proof.
        //
        // `last_proof.is_none()` is load-bearing, not defensive:
        // `build_unsat_proof` is NOT idempotent — it `take_proof()`s the
        // tracker and `take()`s `last_clause_trace` / `last_var_to_term` /
        // `last_negations`, so calling it twice silently degrades the second
        // proof to a trust-closed, assertion-only one.
        //
        // This runs AFTER the LRA fail-closed gate above, so a verdict that
        // gate downgrades never pays for a proof it will not use. It cannot
        // manufacture an UNSAT: it only supplies the certificate for a verdict
        // the solver already reached, and the funnel still validates it
        // independently and still fails closed if it does not check out.
        if result.is_unsat() && self.produce_proofs_enabled() && self.last_proof.is_none() {
            self.build_unsat_proof();
        }

        let result = self.finalize_assumption_result(result, publication);
        self.last_result = Some(result);
        // Output completion is part of emit_sat_verdict and therefore precedes
        // certificate minting. Keep this post-emission path model-immutable.
        self.finalize_unknown_diagnostics();
        // Return reference-based clone from last_result since we just stored it.
        self.last_result.clone().expect("just stored")
    }
}

#[cfg(test)]
mod solve_session_reset_tests {
    use super::*;

    #[test]
    fn solve_session_reset_revokes_result_authorization_markers() {
        let mut exec = Executor::new();
        exec.sat_validated_by_mod_div_or_branch = true;
        exec.nested_array_row_reduction_unsat = true;
        exec.dt_cert_grant_active = true;
        exec.finite_table_cert_grant_active = true;
        exec.const_interp_cert_grant_active = true;
        exec.mbqi_sat_cert_grant_active = true;
        exec.bv_quantifier_full_domain_proof = true;
        let pin = exec.ctx.terms.true_term();
        let mut pins = HashMap::default();
        pins.insert(pin, crate::executor::model::EvalValue::Bool(true));
        let finite_package = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &exec,
            &exec.ctx.assertions,
            crate::executor::model::Model::empty(),
            pins,
        )
        .expect("live finite-table pin package");
        exec.finite_table_cert_witness_state = Some(finite_package);

        exec.reset_solve_session_state();

        assert!(!exec.sat_validated_by_mod_div_or_branch);
        assert!(!exec.nested_array_row_reduction_unsat);
        assert!(!exec.dt_cert_grant_active);
        assert!(!exec.finite_table_cert_grant_active);
        assert!(!exec.const_interp_cert_grant_active);
        assert!(!exec.mbqi_sat_cert_grant_active);
        assert!(!exec.bv_quantifier_full_domain_proof);
        assert!(exec.finite_table_cert_witness_state.is_none());
        assert!(exec.const_interp_cert_witness_state.is_none());
    }

    #[test]
    fn internal_retry_revokes_orphaned_finite_table_witness() {
        let mut exec = Executor::new();
        exec.finite_table_cert_grant_active = true;
        let finite_package = crate::executor::mbqi::FiniteTableWitnessState::for_test(
            &exec,
            &exec.ctx.assertions,
            crate::executor::model::Model::empty(),
            Default::default(),
        )
        .expect("empty finite-table pin package");
        exec.finite_table_cert_witness_state = Some(finite_package);

        assert!(!exec.prepare_check_sat_internal_state());

        assert!(!exec.finite_table_cert_grant_active);
        assert!(
            exec.finite_table_cert_witness_state.is_none(),
            "a later retry must not consume an earlier attempt's parked model"
        );
    }

    #[test]
    fn solve_session_reset_cannot_defer_quantified_gate_to_stale_dt_grant() {
        let mut exec = Executor::new();
        let body = exec.ctx.terms.mk_bool(true);
        let forall = exec
            .ctx
            .terms
            .mk_forall(vec![("x".to_string(), Sort::Int)], body);
        exec.ctx.assertions.push(forall);
        exec.dt_cert_grant_active = true;

        exec.reset_solve_session_state();
        let result = exec.apply_quantified_model_failclosed_gate(SolveResult::Sat);

        assert_eq!(result, SolveResult::Unknown);
        assert_ne!(
            exec.last_statistics
                .get_string("model_check_gate.quantified"),
            Some("deferred-certified-dt")
        );
    }
}

include!("check_sat_assuming/nested_recheck_authority_tests.rs");
#[cfg(test)]
mod nested_publication_tests;

#[cfg(test)]
#[path = "check_sat_assuming/scoped_publication_tests.rs"]
mod scoped_publication_tests;

#[cfg(test)]
mod harvest_recheck_budget_tests {
    use super::{harvest_recheck_budget, HARVEST_RECHECK_FLOOR};
    use std::time::Duration;

    #[test]
    fn budget_is_a_third_of_the_remaining_wall_with_a_floor() {
        assert_eq!(harvest_recheck_budget(None), HARVEST_RECHECK_FLOOR);
        assert_eq!(
            harvest_recheck_budget(Some(Duration::from_secs(42))),
            Duration::from_secs(14)
        );
        assert_eq!(
            harvest_recheck_budget(Some(Duration::from_secs(3))),
            HARVEST_RECHECK_FLOOR
        );
        assert_eq!(
            harvest_recheck_budget(Some(Duration::ZERO)),
            HARVEST_RECHECK_FLOOR
        );
    }
}
