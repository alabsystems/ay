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

use super::dt_axioms::DtSolverDispatch;
use super::theories::bv_cnf_dump;
use super::Executor;
use crate::ematching::contains_quantifier;
use crate::executor_types::{ExecutorError, Result, SolveResult, Statistics, UnknownReason};
use crate::logic_detection::{LogicCategory, TheoryKind};

impl Executor {
    /// Run check-sat with assumptions.
    ///
    /// The assumptions are temporary - they are only used for this check-sat call
    /// and do not affect the assertion stack.
    ///
    /// `pub(crate)`: External consumers MUST use `api::Solver::check_sat_assuming()`
    /// which returns `VerifiedSolveResult`. Part of #5787 (Phase 6).
    pub(crate) fn check_sat_assuming(&mut self, assumptions: &[TermId]) -> Result<SolveResult> {
        self.last_sat_certificate = None;
        // Keep the original assertion+assumption roots for the shared
        // nested-array UNSAT authorization boundary. The inner solver may
        // rewrite either collection while deriving its raw result.
        let decision_roots = self.public_solve_roots(assumptions);
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
        let previous_deadline = self.install_timeout_deadline_for_call();
        let result = self.check_sat_assuming_with_controls(assumptions);
        self.restore_timeout_deadline_after_call(previous_deadline);
        self.record_z3_resource_statistics(solve_started_at);
        let result = result.and_then(|result| {
            bv_cnf_dump::finish_check(dump_transaction, &self.ctx.terms, &dump_roots)?;
            Ok(result)
        })?;
        Ok(self.quarantine_unverified_nested_array_unsat(&decision_roots, result))
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
    /// INTERNAL solver probes (optimization bound probes, the MaxSMT
    /// disjoint-core lower bound, get-consequences/get-abduct entailment
    /// checks) deliberately call `check_sat_assuming` directly instead:
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
        if self.produce_unsat_cores_enabled() {
            let term_to_name: HashMap<TermId, String> = self
                .ctx
                .named_terms_iter()
                .map(|(name, tid)| (tid, name.to_string()))
                .collect();

            if !term_to_name.is_empty() {
                // Split assertions: named become assumptions, unnamed stay as base
                // (mirrors the plain check-sat redirect in check_sat.rs).
                let mut named_assumptions = Vec::new();
                let mut unnamed_assertions = Vec::new();
                for &assertion in &self.ctx.assertions {
                    if term_to_name.contains_key(&assertion) {
                        named_assumptions.push(assertion);
                    } else {
                        unnamed_assertions.push(assertion);
                    }
                }

                if !named_assumptions.is_empty() {
                    // combined = named ++ user assumptions, deduplicated by
                    // TermId with the first occurrence winning: an assumption
                    // literal textually identical to a named assertion shares
                    // its TermId and must not be passed twice.
                    let mut seen: HashSet<TermId> = HashSet::default();
                    let mut combined: Vec<TermId> =
                        Vec::with_capacity(named_assumptions.len() + assumptions.len());
                    for &term in named_assumptions.iter().chain(assumptions.iter()) {
                        if seen.insert(term) {
                            combined.push(term);
                        }
                    }

                    // Temporarily replace assertions with unnamed-only.
                    let original_assertions =
                        std::mem::replace(&mut self.ctx.assertions, unnamed_assertions);

                    let result = self.check_sat_assuming(&combined);
                    // Certificate gate while the base is still stripped: a
                    // harvested proper-subset core must re-prove UNSAT on its
                    // own or it is discarded (#unsat-core-miscount).
                    let result = self.certify_assumption_core(&combined, result);

                    // Completeness rescue (#named-cores-ground-sat): the
                    // named→assumption redirect is a core-TRACKING strategy,
                    // not a verdict authority — on Unknown, re-solve the
                    // un-named equivalent (base ∧ named ∧ literals through
                    // the plain pipeline) while the base is still stripped.
                    // See `rescue_named_core_redirect_unknown`.
                    let (result, rescue_elapsed) = match result {
                        Ok(SolveResult::Unknown) => {
                            let rescue_started = Instant::now();
                            let rescued = self.rescue_named_core_redirect_unknown(&combined);
                            (rescued, Some(rescue_started.elapsed()))
                        }
                        other => (other, None),
                    };

                    // Deletion-based EUF/ArrayEuf core minimization while the
                    // base is still stripped (#uc-core-minimize): shrinks the
                    // certified core — including the empty-harvest→pad-all
                    // theory-refutation case AND the rescue's conservative
                    // all-assumptions core — by re-solving subsets, budget-
                    // aware and fail-closed (only solve-verified subsets are
                    // adopted). Runs AFTER the rescue: the measured
                    // reduction-0 families (QG-classification, storecomm)
                    // reach unsat through it.
                    let result = self.minimize_assumption_core(&combined, result, rescue_elapsed);

                    // Restore original assertions BEFORE propagating any error:
                    // internal callers `?` through this path and a lost
                    // assertion stack would corrupt subsequent commands.
                    self.ctx.assertions = original_assertions;

                    // Set the core bookkeeping AFTER check_sat_assuming (which
                    // clears both fields as part of its own state reset):
                    // - the name snapshot lets get-unsat-core print named core
                    //   members as their labels;
                    // - last_assumptions is narrowed back to the USER literals
                    //   so get-unsat-assumptions keeps its SMT-LIB subset
                    //   contract (⊆ the literals the user passed).
                    self.last_core_term_to_name = Some(term_to_name);
                    self.last_assumptions = Some(assumptions.to_vec());

                    return result;
                }
            }
        }

        let result = self.check_sat_assuming(assumptions);
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
        let recheck = self.check_sat_assuming(&core);
        if matches!(recheck, Ok(SolveResult::Unsat(_))) {
            self.last_assumption_core = Some(core);
            return recheck;
        }
        // Uncertified harvest -- the exact defect class this gate exists
        // for. Restore the original solve state (deterministic re-solve),
        // then discard the harvest so the padded superset prints.
        let restored = self.check_sat_assuming(combined);
        self.last_assumption_core = None;
        restored
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
    ) -> Result<SolveResult> {
        if std::env::var_os("AY_PHASE_TRACE").is_some() {
            eprintln!("c phase-trace named-core-redirect direct=unknown rescue=scoped");
        }
        // Fresh per-call deadline, mirroring the raw `check_sat_assuming`
        // entry: the rescue is a full second solve and must honor the
        // configured timeout rather than inherit an exhausted budget.
        let previous_deadline = self.install_timeout_deadline_for_call();
        let base_assertions = self.ctx.assertions.clone();
        let result = self.solve_scoped_assumptions(
            &base_assertions,
            assumptions,
            Self::solve_current_assertions_with_quantifier_support,
        );
        let result = match result {
            // SINGLE SAT-EMISSION CHOKEPOINT (#sat-chokepoint): this path
            // returns to the redirect callers (not through the main dispatch's
            // funnel call), so it MUST funnel its own proposed Sat through
            // `emit_sat_verdict` to run the model gates and mint the
            // SatCertificate — an unminted Sat is fail-closed to Unknown at
            // the API boundary.
            Ok(SolveResult::Sat) => self.emit_sat_verdict(SolveResult::Sat, assumptions),
            other => other,
        };
        self.restore_timeout_deadline_after_call(previous_deadline);
        result
    }

    fn check_sat_assuming_with_controls(&mut self, assumptions: &[TermId]) -> Result<SolveResult> {
        // Scope-transience for the RM domain axioms the inner gate may push
        // (#P0.2 Pass B): the assumption routes have no
        // `scope_tracked_assertions` restore of their own, so truncate back to
        // the entry length on EVERY exit path. Inner paths that grow the
        // assertion vector restore it themselves (e.g. the BV arm), so the
        // entry length is exactly the pre-axiom length.
        let base_len = self.ctx.assertions.len();
        let result = self.check_sat_assuming_with_controls_inner(assumptions);
        self.ctx.assertions.truncate(base_len);
        result
    }

    /// Per-check solve-session state reset shared by the
    /// `check-sat-assuming` entry and the unsat-core minimization pass's
    /// scoped subset re-solves (#uc-core-minimize).
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
        self.last_lrat_certificate = None;
        self.last_proof_term_overrides = None;
        self.last_proof_quality = None;
        self.last_clause_trace = None;
        self.last_var_to_term = None;
        self.last_trail_provenance = None;
        self.last_clausification_proofs = None;
        self.last_original_clause_theory_proofs = None;
        self.last_assumption_core = None;
        self.last_core_term_to_name = None;
        self.last_model_validated = false;
        self.last_validation_stats = None;
        self.model_validation_delegated_assertions.clear();
        self.last_unknown_reason = None;
        self.last_statistics = Statistics::default();
        self.last_statistics.num_assertions = self.ctx.assertions.len() as u64;
        // Keep the immutable authority snapshot installed at the public-query
        // boundary. Core minimization and scoped subset re-solves must not
        // promote their temporary assertion windows to authored premises.
        self.quant_expansion_records.clear();
        self.last_proof_rebuild_originals.clear();
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
        // reset and must earn both authorizations independently.
        self.sat_validated_by_mod_div_or_branch = false;
        self.nested_array_row_reduction_unsat = false;
        self.array_axiom_scope = None;
        self.row_seeded_terms.clear();
        self.proof_check_result = None;
    }

    fn check_sat_assuming_with_controls_inner(
        &mut self,
        assumptions: &[TermId],
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
            self.last_result = Some(SolveResult::Unknown);
            return Ok(SolveResult::Unknown);
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
                self.last_result = Some(SolveResult::Unknown);
                return Ok(SolveResult::Unknown);
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

        // Use the base assertions from context, assumptions are passed separately
        let base_assertions = self.ctx.assertions.clone();

        if base_assertions.is_empty() && assumptions.is_empty() {
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
            return self.emit_sat_verdict(SolveResult::Sat, assumptions);
        }

        let mut all_assertions = base_assertions.clone();
        all_assertions.extend(assumptions.iter().copied());

        let (_, pre_quantifier_features) = self.detect_logic_category(&all_assertions);
        if pre_quantifier_features.has_bv_int_conversion {
            let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
            if bridge_result.is_unsat() {
                return Ok(self.finish_check_sat_assuming_result(assumptions, bridge_result));
            }
        }

        if all_assertions
            .iter()
            .copied()
            .any(|assertion| contains_quantifier(&self.ctx.terms, assertion))
        {
            let result = self.solve_quantified_assumptions(&base_assertions, assumptions)?;
            return Ok(self.finish_check_sat_assuming_result(assumptions, result));
        }

        let (category, features) = self.detect_logic_category(&all_assertions);
        self.last_statistics
            .set_string("solver.logic_category", format!("{category:?}"));
        if std::env::var_os("AY_PHASE_TRACE").is_some() {
            eprintln!("c phase-trace check-sat-assuming category={category:?}");
        }
        self.set_active_solve_phase("assumption-solving", format!("theory:{category:?}"));

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
                    self.solve_scoped_assumptions(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                    )
                } else {
                    Ok(direct)
                }
            }
            LogicCategory::QfLia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
                    if bridge_result.is_unsat() {
                        return Ok(
                            self.finish_check_sat_assuming_result(assumptions, bridge_result)
                        );
                    }
                }
                self.solve_lia_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfNia => {
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
                    self.solve_scoped_assumptions(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                    )
                } else {
                    Ok(direct)
                }
            }
            LogicCategory::QfNra => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Nra,
            ),
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
                self.solve_scoped_assumptions(
                    &base_assertions,
                    assumptions,
                    Self::solve_current_assertions_with_quantifier_support,
                )
            }
            LogicCategory::QfUflia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
                    if bridge_result.is_unsat() {
                        return Ok(
                            self.finish_check_sat_assuming_result(assumptions, bridge_result)
                        );
                    }
                }
                self.solve_auf_lia_with_assumptions(&base_assertions, assumptions)
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
                        return Ok(
                            self.finish_check_sat_assuming_result(assumptions, bridge_result)
                        );
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
                self.solve_fp_with_scoped_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfBvfp => {
                self.solve_bvfp_with_scoped_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::QfAbvfp => {
                self.solve_abvfp_with_scoped_assumptions(&base_assertions, assumptions)
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
            LogicCategory::QfBvLia => self.solve_bv_lia_bridge_with_assumptions(assumptions),
            LogicCategory::QfBvLiaIndep => {
                self.solve_bv_lia_indep_with_assumptions(&base_assertions, assumptions)
            }
            LogicCategory::Lia => {
                if features.has_bv_int_conversion {
                    let bridge_result = self.solve_bv_lia_bridge_with_assumptions(assumptions)?;
                    if bridge_result.is_unsat() {
                        return Ok(
                            self.finish_check_sat_assuming_result(assumptions, bridge_result)
                        );
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
                        return Ok(
                            self.finish_check_sat_assuming_result(assumptions, bridge_result)
                        );
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
                    self.solve_scoped_assumptions(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
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
                    self.solve_scoped_assumptions(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
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
            LogicCategory::QfDt => {
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
                    if std::env::var_os("AY_PHASE_TRACE").is_some() {
                        eprintln!("c phase-trace qfdt-assuming direct=unknown retry=scoped");
                    }
                    self.solve_scoped_assumptions(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
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
            LogicCategory::DtAx => {
                // Same Unknown-retry contract as the QfDt arm above: the
                // 20230720-blocksworld QF_DT instances (recursive Tower +
                // 21-ctor enum) classify as DtAx and, in named-core mode,
                // arrive here with every assertion as an assumption; the
                // combined route returns Unknown on instances the plain
                // pipeline decides. Retrying through the scoped fallback
                // turns those into answered verdicts (conservative
                // all-assumptions core on UNSAT — reduction 0, error-free).
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
                    if std::env::var_os("AY_PHASE_TRACE").is_some() {
                        eprintln!("c phase-trace dtax-assuming direct=unknown retry=scoped");
                    }
                    self.solve_scoped_assumptions(
                        &base_assertions,
                        assumptions,
                        Self::solve_current_assertions_with_quantifier_support,
                    )
                } else {
                    Ok(direct)
                }
            }
            // Quantified DT logics (#7150): route to DT-combined solvers
            LogicCategory::Ufdt | LogicCategory::Aufdt => self.solve_with_assumptions_for_theory(
                &base_assertions,
                assumptions,
                TheoryKind::Dt,
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
                // DT + FP has no sound combined solver yet (#8728). Return
                // Unknown+Incomplete rather than an error so callers see the
                // soundness-preserving standard SMT-LIB `unknown`.
                if features.has_fpa && self.ctx.datatype_iter().next().is_some() {
                    self.last_unknown_reason = Some(UnknownReason::Incomplete);
                    Ok(SolveResult::Unknown)
                } else {
                    Err(ExecutorError::UnsupportedLogic(
                        self.ctx.logic().unwrap_or("<unspecified>").to_string(),
                    ))
                }
            }
        }?;

        let result = if result == SolveResult::Sat {
            // SINGLE SAT-EMISSION CHOKEPOINT (#sat-chokepoint): the assumption
            // path funnels through the SAME combined validation boundary as
            // plain check-sat. emit_sat_verdict temporarily installs
            // `base_assertions + assumptions`, completes the final model, runs
            // every gate, mints the certificate, then restores the base stack.
            // There is deliberately NO assumption completion/validation after
            // emission: that used to mutate the already-certified witness.
            self.emit_sat_verdict(result, assumptions)?
        } else {
            result
        };

        if result == SolveResult::Sat {
            debug_assert!(
                self.last_model.is_some(),
                "BUG: check_sat_assuming returned SAT without populating last_model"
            );
        }
        if result.is_unsat() {
            debug_assert!(
                self.last_assumption_core.is_some(),
                "BUG: check_sat_assuming returned UNSAT without populating assumption core"
            );
        }

        // #7912 postcondition: every SAT result has been validated at some level.
        // Mirrors the postcondition in check_sat_guarded().
        debug_assert!(
            result != SolveResult::Sat
                || self.last_model_validated
                || self.skip_model_eval
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

        Ok(self.finish_check_sat_assuming_result(assumptions, result))
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
    fn solve_quantified_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        let mut combined_assertions = base_assertions.to_vec();
        combined_assertions.extend(assumptions.iter().copied());

        let original_assertions = std::mem::replace(&mut self.ctx.assertions, combined_assertions);
        let solve_result = self.solve_current_assertions_with_quantifier_support();
        self.ctx.assertions = original_assertions;

        match solve_result? {
            SolveResult::Sat => {
                // SINGLE SAT-EMISSION CHOKEPOINT (#sat-chokepoint): this path
                // early-returns (it does not flow through the main dispatch's
                // funnel call), so it MUST funnel its own proposed Sat through
                // `emit_sat_verdict` to run the model gates and mint the
                // SatCertificate. Quantified logics are non-authoritative, so the
                // authoritative-failclosed gate keeps genuine quantifier coverage
                // gaps as Sat.
                self.emit_sat_verdict(SolveResult::Sat, assumptions)
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
    ) -> Result<SolveResult> {
        self.solve_scoped_assumptions(base_assertions, assumptions, Self::solve_fp)
    }

    fn solve_bvfp_with_scoped_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        self.solve_scoped_assumptions(base_assertions, assumptions, Self::solve_bvfp)
    }

    fn solve_abvfp_with_scoped_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        self.solve_scoped_assumptions(base_assertions, assumptions, Self::solve_abvfp)
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
        let original_assertions = std::mem::replace(&mut self.ctx.assertions, combined_assertions);
        let saved_assumptions = self.last_assumptions.take();
        let verify = self.solve_current_assertions_with_quantifier_support();
        self.last_assumptions = saved_assumptions;
        self.ctx.assertions = original_assertions;
        match verify {
            Ok(SolveResult::Unsat(_)) => {
                // Confirmed. Restore the core (the verify pass may have
                // clobbered executor state) and drop any model the verify
                // solve left behind — it would describe the reduced problem.
                self.last_assumption_core = Some(core);
                self.last_model = None;
                if std::env::var_os("AY_PHASE_TRACE").is_some() {
                    eprintln!("c phase-trace dt-assumption-core reverify=confirmed");
                }
                Ok(result)
            }
            _ => {
                self.last_assumption_core = None;
                self.last_model = None;
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                if std::env::var_os("AY_PHASE_TRACE").is_some() {
                    eprintln!("c phase-trace dt-assumption-core reverify=FAILED demote=unknown");
                }
                Ok(SolveResult::Unknown)
            }
        }
    }

    /// `pub(in crate::executor)`: also the subset-solve engine of the
    /// unsat-core minimization pass (#uc-core-minimize, core_minimize.rs)
    /// for verdicts obtained through the scoped-plain rescue.
    pub(in crate::executor) fn solve_scoped_assumptions(
        &mut self,
        base_assertions: &[TermId],
        assumptions: &[TermId],
        solve: fn(&mut Self) -> Result<SolveResult>,
    ) -> Result<SolveResult> {
        let mut combined_assertions = base_assertions.to_vec();
        combined_assertions.extend(assumptions.iter().copied());

        let original_assertions = std::mem::replace(&mut self.ctx.assertions, combined_assertions);
        // The scoped route merges the assumptions INTO `ctx.assertions`, so
        // the inner solve sees the complete problem exactly as a plain
        // `check-sat (base ∧ A)` would. Clear `last_assumptions` for the
        // duration: lanes that bail when assumptions are carried SEPARATELY
        // (e.g. the enum finite-domain SAT lane) are needlessly disabled
        // here — their bail exists because they read only `ctx.assertions`,
        // which on THIS route is the full conjunction. Restored afterward
        // for `get-unsat-assumptions`.
        let saved_assumptions = self.last_assumptions.take();
        let solve_result = solve(self);
        self.last_assumptions = saved_assumptions;
        self.ctx.assertions = original_assertions;

        match solve_result? {
            SolveResult::Sat => {
                self.last_result = Some(SolveResult::Sat);
                self.finalize_sat_assumption_validation(assumptions)
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
    ) -> SolveResult {
        if result.is_sat() {
            debug_assert!(
                self.last_model.is_some(),
                "BUG: check_sat_assuming returned SAT without populating last_model"
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

        // SOUNDNESS (QF_LRA false-UNSAT, multi-path): the check-sat-assuming
        // path does NOT route through solve_lra_incremental, so it bypasses the
        // plain-check-sat disequality/distinct re-verify guard. A differential
        // fuzz vs z3 found QF_LRA false-UNSATs here on `distinct`-involving
        // formulas (AY unsat where z3 sat). Mirror the plain-path defense as a
        // uniform fail-closed gate: for QF_LRA/LRA, when the result is UNSAT and
        // the active assertions contain a fragile construct (distinct,
        // (not (= ..)), ite, or — the constructs implicated in the QF_LRA DPLL(T)
        // false-UNSATs), downgrade the suspect UNSAT to a sound `unknown`. Pure-
        // conjunctive-linear QF_LRA (k-induction hybrid_networks: no ite/or/
        // distinct) never trips this, so its completeness/throughput is
        // unaffected; only the fragile-construct cases (the buggy ones) fail
        // closed. The gate is UNCONDITIONAL: the former
        // AY_NO_LRA_CSA_UNSAT_GUARD=1 kill switch is removed — no environment
        // variable may turn off a soundness guard.
        // The scan MUST cover the assumption literals as well as
        // `ctx.assertions`: with `:produce-unsat-cores`, named assertions are
        // moved out of the base assertion set into the assumption set for the
        // duration of the check (by the plain-check-sat named-core redirect
        // and by `check_sat_assuming_with_named_cores`), and user assumption
        // literals feed the same fragile solving path — scanning the stripped
        // base alone would let a suspect UNSAT through this fail-close gate
        // whenever the only fragile construct lives in a named assertion or
        // an assumption literal.
        if result.is_unsat()
            && self.logic().is_some_and(|l| l == "QF_LRA" || l == "LRA")
            && self.lra_roots_contain_disequality(assumptions)
        {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            self.last_result = Some(SolveResult::Unknown);
            self.finalize_unknown_diagnostics();
            return SolveResult::Unknown;
        }

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

        exec.reset_solve_session_state();

        assert!(!exec.sat_validated_by_mod_div_or_branch);
        assert!(!exec.nested_array_row_reduction_unsat);
    }
}
