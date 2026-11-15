// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Top-level UNSAT proof assembly: `build_unsat_proof`, the entry point that
//! turns a solved query's clause trace into a candidate proof and hands it to
//! the finalizer.

use super::*;
use crate::executor::proof::check::EmptyClauseDerivation;

mod farkas_metadata;
mod interpolation;
mod open;
mod stop;

/// Whether [`Executor::open_unsat_proof_assembly`] authorized a fresh proof build.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum AssemblyGate {
    /// Every guard passed: the caller seeds a proof and runs the assembly pipeline.
    Proceed,
    /// A guard already settled this query's proof state (reconstruction suppressed,
    /// a sealed bounded proof retained, a bounded pigeonhole installed, or an
    /// uncertifiable-source poison installed). The caller must return immediately
    /// and must NOT seed or publish a proof.
    Stop,
}

impl Executor {
    /// Builds an Alethe-compatible UNSAT proof from assumptions to the empty clause.
    ///
    /// The assembly runs in a Certify node (DR-39, GuardTree step S2),
    /// entered on this thread for its extent: its stop polls read that node
    /// (`stop.rs`), and a check-sat a pass runs is a `Full` child of it, so
    /// it obeys the certification envelope and the cancels above it and not
    /// the search's deadline.
    pub(in crate::executor) fn build_unsat_proof(&mut self) {
        let certify = self.proof_assembly_certify_node();
        let _in_certify = certify.enter();
        // Every strict decision of the build shares one memo of the
        // exact-division sweeps that failed, so no other spelling of a
        // divider obligation sweeps it again (`ay_proof::ExactDivisionSweepMemo`).
        let _divider_sweeps = self.exact_division_sweeps.begin_build();
        let outer = std::mem::replace(&mut self.assembly_certify, certify.downgrade());
        self.assemble_unsat_proof();
        self.assembly_certify = outer;
    }

    /// [`Self::build_unsat_proof`]'s work inside its Certify node: the gate,
    /// the passes, and the certify-before-presentation decline.
    fn assemble_unsat_proof(&mut self) {
        self.last_proof_surface_withheld = None;
        // A stop already observed skips seeding and the LRAT export too.
        if self.open_unsat_proof_assembly() == AssemblyGate::Stop
            || self.abandon_proof_assembly_on_stop()
        {
            return;
        }
        self.run_unsat_proof_passes();
        // #certify-before-presentation. Later presentation passes record
        // their own declines against the surface that was withheld
        // (`authored-source-authority-invalid`,
        // `authored-assume-surface-unavailable`); the decline line must name
        // the bound that withheld it, which is the actual cause.
        if let Some(mechanism) = self.last_proof_surface_withheld {
            if !self.last_unsat_proof_reconstruction_suppressed {
                // A later lane installed its own authored proof and lifted the
                // suppression: the kept derivation is no longer the proof.
                self.last_proof_surface_withheld = None;
                return;
            }
            self.record_proof_decline(mechanism);
            // The bound refused to collect SPELLINGS for the canonical roots;
            // it said nothing about the document of what was finally
            // assembled. When every reachable `assume` of that proof
            // authenticates against its authored source — the exporter's own
            // criterion — AND none is a premise AY's provenance does not back
            // (the certificate line's own foreign-assume detector), the
            // document is published as it stands and the certificate line
            // judges it like any other. Measured on the D7 list: UF
            // `sledgehammer/TypeSafe/uf.1083624` keeps the carcara-VALID
            // document it had when the poison let a later repair rebuild it;
            // without the second test AUFDTLIA `german10`/`german135` printed
            // a quantified `assume` with canonical binder names that carcara
            // cannot match (holey -> invalid).
            if self
                .last_proof
                .as_ref()
                .is_some_and(|proof| self.proof_has_authenticated_alethe_surface(proof))
            {
                self.last_unsat_proof_reconstruction_suppressed = false;
                if self.unsat_proof_terminal_foreign_assume() {
                    self.last_unsat_proof_reconstruction_suppressed = true;
                }
            }
        }
    }

    /// The bound that withheld the authored-surface document of the current
    /// UNSAT proof, when the derivation was kept for certification without it
    /// (#certify-before-presentation). `None` whenever the document was not
    /// withheld this way.
    #[must_use]
    pub fn last_unsat_document_withheld_by(&self) -> Option<ProofDeclineMechanism> {
        self.last_proof_surface_withheld
            .filter(|_| self.last_unsat_proof_reconstruction_suppressed)
    }

    /// The assembly pipeline behind [`Self::assemble_unsat_proof`]'s gate.
    fn run_unsat_proof_passes(&mut self) {
        let mut proof = if self.proof_tracker.num_steps() > 0 {
            self.seed_proof_from_tracker()
        } else {
            self.seed_proof_from_assertions()
        };

        // Capture the SAT-level LRAT bytes before SAT proof reconstruction
        // consumes `last_clause_trace`. This is best-effort: traces with
        // truncation or non-contiguous original clause IDs do not export a
        // standalone LRAT certificate.
        self.last_lrat_certificate = self
            .last_clause_trace
            .as_ref()
            .and_then(clause_trace_to_lrat_bytes);

        // Every pass boundary observes the interrupt and the certification
        // deadline: a stopped assembly is discarded, never finished (`stop.rs`).
        let passes: [fn(&mut Self, &mut Proof); 12] = [
            Self::derive_empty_clause,
            Self::capture_interpolation_proof,
            Self::rewrite_derived_empty_clause,
            Self::select_empty_clause_root,
            Self::promote_certified_theory_lemma_kinds,
            Self::reconstruct_folded_assertion_collapses,
            Self::rescue_residual_trust_steps,
            Self::certify_euf_and_array_leaves,
            Self::reassert_final_promotion_boundaries,
            Self::apply_authored_replacements_and_derivations,
            Self::retain_checked_sat_proof_for_wire_gap,
            // LAST, so it never displaces a renderable proof an earlier route
            // built; see `proof_divmod_def`.
            Self::promote_divmod_definitions_last_resort,
        ];
        for pass in passes {
            if self.abandon_proof_assembly_on_stop() {
                return;
            }
            pass(self, &mut proof);
        }
        if self.abandon_proof_assembly_on_stop() {
            return;
        }
        self.finalize_bv_source_proof(proof);
    }

    /// Recheck the retained checked SAT-refutation's query authority after any
    /// nested reconstruction, and use its materialized proof only for a
    /// remaining presentation gap — and only when doing so cannot cost this
    /// query its verdict.
    ///
    /// THE SUBSTITUTION MAY ONLY ADD AN ARTIFACT; IT MAY NEVER TURN A
    /// CERTIFIABLE UNSAT INTO A WITHHELD ONE. The wire-gap screen
    /// (`proof_has_known_wire_gap`) asks about Alethe/Carcara EXPORTABILITY,
    /// not about validity, so a document it flags can still be exactly the one
    /// that certifies the result: under `:produce-proofs` — and under every
    /// other promised-artifact mode —
    /// `independent_sidecar_blocked_by_presentation` bars the independent
    /// sidecar lanes, leaving `check_strict_unsat_presentation` over THIS
    /// document as `mint_unsat_certificate`'s only remaining route. Handing
    /// that unchanged checker a materialized reconstruction it rejects (a
    /// non-deferred `hole` closer, say) in place of one it accepts does not
    /// weaken a claim: it withholds a correct `unsat` outright, as
    /// `Unknown("(incomplete self-check-rejected)")`.
    ///
    /// So the replacement is adopted only when it is at least as certifiable
    /// as what it displaces. A candidate the strict checker accepts is always
    /// eligible; one it rejects is eligible only when the assembled proof was
    /// already being rejected too, which is the gap this retention was added
    /// to close. The sidecar's copy is consumed only on adoption, so a
    /// declined candidate leaves it in place for a later ask.
    ///
    /// Monotonicity of the ADOPTED document is not enough: the candidate's own
    /// cascade can cost the query its verdict as a side effect, so a candidate
    /// that would is declined before that cascade runs
    /// (`checked_sat_candidate_would_cost_the_assembled_proof`).
    fn retain_checked_sat_proof_for_wire_gap(&mut self, proof: &mut Proof) {
        if self.skips_trust_elimination_repairs() || !self.proof_has_known_wire_gap(proof) {
            return;
        }
        let Some(mut candidate) = self.current_checked_sat_proof_cloned() else {
            return;
        };
        if self.checked_sat_candidate_would_cost_the_assembled_proof(proof, &candidate) {
            crate::executor::unsat_cert::probe_cert_reject(|| {
                "checked-sat retention: DECLINE swap (replacement has no authored-source \
                 presentation; its cascade would suppress the certifying assembled proof)"
                    .to_string()
            });
            return;
        }
        self.apply_authored_replacements_and_derivations(&mut candidate);
        // The exact-fragment reconstruction may re-prove an arithmetic leaf
        // intrinsically without the assembled proof's interpolation witness.
        // Preserve only independently replayed, exactly rebound metadata; the
        // candidate's original-clause/query authority and theorem are unchanged.
        let stopped = self.make_proof_assembly_should_stop();
        farkas_metadata::retain_verified_farkas_annotations(
            &self.ctx.terms,
            proof,
            &mut candidate,
            &stopped,
        );
        if stopped() {
            return;
        }
        if !self.checked_sat_substitution_is_monotone(proof, &candidate) {
            crate::executor::unsat_cert::probe_cert_reject(|| {
                "checked-sat retention: DECLINE swap (replacement is strictly \
                 less certifiable than the assembled proof)"
                    .to_string()
            });
            return;
        }
        // Adopted: consume the sidecar's copy so nothing re-uses it.
        let _adopted = self.take_current_checked_sat_proof();
        *proof = candidate;
    }

    /// Whether replacing `current` with `replacement` cannot cost this query
    /// its certification, judged by the same strict checker
    /// `check_strict_unsat_presentation` runs at mint time.
    fn checked_sat_substitution_is_monotone(&self, current: &Proof, replacement: &Proof) -> bool {
        self.check_proof_strict_with_datatypes(replacement).is_ok()
            || self.check_proof_strict_with_datatypes(current).is_err()
    }

    /// Whether running the authored cascade over `candidate` would cost this
    /// query a LIVE, CERTIFIABLE `assembled` proof.
    ///
    /// The cascade ends in `restore_reachable_authored_assume_surface_overrides`,
    /// whose refusal calls `suppress_unsat_proof_reconstruction`: sticky for the
    /// whole query, whether or not the candidate is then adopted. The
    /// exact-original fragment `assume`s an original unit that is a CONJUNCT of
    /// an authored root as-is (`emit_basic_original_unit`), which is exactly
    /// what the lazy QF_DT lane's `FlattenAnd` image hands it. The strict
    /// checker admits that `assume` through its `and` expansion, so
    /// `checked_sat_substitution_is_monotone` cannot see the loss, but no
    /// `(assert ...)` row spells a bare conjunct (`AuthoredSourceAuthorityInvalid`).
    /// Since 779076535 that withheld a correct `unsat` as "has no proof" on
    /// `test_qf_dt_exhaustiveness_emits_firewall_lean` and, measured
    /// 2026-09-22, on 13 QF_LRA/QF_DT corpus benchmarks under
    /// `:produce-proofs`, while the displaced proof (the authored root plus
    /// `and_pos` projections) certifies as `unsat_admission=strict-proof`.
    ///
    /// All three conjuncts are side-effect free and load-bearing:
    /// - reconstruction is still live; once suppressed there is no
    ///   presentation left to protect;
    /// - consequence replay's preflight refuses the candidate's `assume`
    ///   scope, so its restoration would suppress;
    /// - `assembled` passes the strict check the monotone gate and mint time
    ///   run. When it does not, the swap is the gap this retention exists to
    ///   close: both retentions of
    ///   `model_checker_consumer_quantified_safety/uf_record_unsat.smt2` under
    ///   `:produce-proofs` (inside its consequence-replay probes) and nine
    ///   library tests whose cascade repairs the raw candidate have a
    ///   strict-rejected assembled proof, and declining the `uf_record`
    ///   candidates withheld it (`step t13 uses unverified trust rule`).
    ///
    /// Cheapest first: the strict check runs only for a candidate the other
    /// two already mark.
    fn checked_sat_candidate_would_cost_the_assembled_proof(
        &self,
        assembled: &Proof,
        candidate: &Proof,
    ) -> bool {
        !self.last_unsat_proof_reconstruction_suppressed
            && !self.candidate_authored_surface_is_available(candidate)
            && self.check_proof_strict_with_datatypes(assembled).is_ok()
    }

    /// Seeds the candidate proof from the proof tracker's recorded steps.
    ///
    /// Assumes `self.proof_tracker.num_steps() > 0`; consumes the tracker's proof.
    fn seed_proof_from_tracker(&mut self) -> Proof {
        let mut tracker_proof = self.proof_tracker.take_proof();
        // (#7913 Phase C) When LIA preprocessing substituted variables,
        // the tracker's Assume terms may be degenerate (e.g. `true`,
        // `false`) rather than the original user assertions. This happens
        // when VariableSubstitution replaces `(= x 3)` -> `(= 3 3)` ->
        // `true`, making the SAT solver see trivial constants instead of
        // the original equality atoms. Detect this by checking if ALL
        // assume terms are boolean constants, and if so replace them with
        // the original problem assertions.
        let true_id = self.ctx.terms.true_term();
        let false_id = self.ctx.terms.false_term();
        let assume_terms: Vec<TermId> = tracker_proof
            .steps
            .iter()
            .filter_map(|s| match s {
                ProofStep::Assume(t) => Some(*t),
                _ => None,
            })
            .collect();
        let all_degenerate = !assume_terms.is_empty()
            && assume_terms.iter().all(|t| *t == true_id || *t == false_id);
        if all_degenerate {
            let original_assertions = self.proof_original_problem_assertions();
            if !original_assertions.is_empty() {
                let non_assume_steps: Vec<_> = tracker_proof
                    .steps
                    .into_iter()
                    .filter(|s| !matches!(s, ProofStep::Assume(_)))
                    .collect();
                tracker_proof = Proof::new();
                for (idx, assertion) in original_assertions.into_iter().enumerate() {
                    tracker_proof.add_assume(assertion, Some(format!("h{idx}")));
                }
                for step in non_assume_steps {
                    tracker_proof.add_step(step);
                }
            }
        }
        tracker_proof
    }

    /// Seeds the candidate proof with one `Assume` leaf per problem assertion.
    ///
    /// Assumes the proof tracker recorded nothing, so the leaves must come from the
    /// problem itself (plus any `check-sat-assuming` assumptions).
    fn seed_proof_from_assertions(&mut self) -> Proof {
        let mut proof = Proof::new();
        let problem_assertions = self.proof_problem_assertions();
        let mut assertions = if problem_assertions.is_empty() {
            self.proof_original_problem_assertions()
        } else {
            problem_assertions
        };
        // (#h10/b22) check-sat-assuming holds the assumptions in
        // `last_assumptions`, not in `ctx.assertions`. When the UNSAT verdict
        // comes from a trivial fold of contradictory assumptions (e.g. two
        // `(= x ..)` BV equalities) the SAT solver records no clause-level
        // conflict, so the proof reconstructs with no Assume leaves at all and
        // every empty-clause strategy fails, yielding an empty proof. Seed the
        // assumptions as Assume steps so the contradictory-assumption /
        // trust-lemma fallbacks can close the proof.
        if let Some(assumptions) = self.last_assumptions.clone() {
            for assumption in assumptions {
                if !assertions.contains(&assumption) {
                    assertions.push(assumption);
                }
            }
        }
        for (idx, assertion) in assertions.into_iter().enumerate() {
            proof.add_assume(assertion, Some(format!("h{idx}")));
        }
        proof
    }

    /// Derives the empty clause from the seeded leaves.
    ///
    /// Assumes `proof` still carries its seeded leaves and that the SAT clause trace
    /// is available for the first `ensure_empty_clause_derivation` (which consumes it).
    fn derive_empty_clause(&mut self, proof: &mut Proof) {
        // Decompose single Generic/trust theory lemmas for combined real
        // conflicts into EUF + arithmetic bridge pairs (#6756 Packet 2).
        // Must run BEFORE ensure_empty_clause_derivation so the two-lemma
        // closer (Packet 3) can find both lemmas.
        Self::decompose_combined_real_conflict_lemmas(&mut self.ctx.terms, proof);

        // Build initial empty clause derivation (pre-rewrite).
        self.ensure_empty_clause_derivation(proof);
    }

    /// Applies the input-syntax rewrites to the derivation and re-establishes the
    /// Farkas certificates and the derivation on both sides of that rewrite.
    ///
    /// On return `proof` may still contain more than one empty-clause root.
    fn rewrite_derived_empty_clause(&mut self, proof: &mut Proof) {
        let hidden_equality_assertions = self.collect_hidden_problem_equality_assertions();

        // Reconstruct missing Farkas coefficients for arithmetic theory lemmas
        // (#6757). Must run AFTER ensure_empty_clause_derivation (which may
        // create new TheoryLemma steps via SAT resolution reconstruction) but
        // BEFORE apply_input_syntax_rewrites_to_proof (which can simplify
        // linking equalities like `(= (select a 0) x)` to `true`, destroying
        // the constraint that makes the conjunction infeasible for Farkas).
        self.reconstruct_missing_farkas_and_demote(proof, &hidden_equality_assertions);

        if !crate::executor::proof_resolution::proof_structure_is_well_formed(proof) {
            tracing::warn!("proof contains dangling premise IDs before rewrite");
        }
        self.apply_input_syntax_rewrites_to_proof(proof);
        if self.proof_assembly_stop_requested() {
            return;
        }

        // Rewriting changes arithmetic rows and can merge literals. Transport
        // preserves a positional certificate only when rebinding plus exact
        // replay succeeds; this whole-proof sanitation is the final authority
        // boundary for any annotation created outside that chokepoint. Clear
        // and demote stale certificates before attempting reconstruction on the
        // final syntax (#6757).
        self.sanitize_rewritten_farkas_and_demote(proof);

        // Post-rewrite promotion (#6756): theory lemmas that were classified as
        // Generic before surface-syntax rewrites may now have clause terms that
        // match a more specific kind (e.g., LIA integer equality after array
        // select/store rewriting). Re-infer the kind from the rewritten clause.
        // #trust->0 C3: supply the datatype registries so DT shapes promote too.
        let c3_dt_data = crate::theory_inference::dt_funnel_registry_data(&self.ctx);
        let c3_dt = c3_dt_data
            .as_ref()
            .map(crate::theory_inference::DatatypeRegistries::from_data);
        Self::promote_generic_theory_lemma_kinds_after_rewrite(
            &self.ctx.terms,
            proof,
            c3_dt.as_ref(),
        );
        // Post-rewrite Farkas for lemmas just promoted from Generic (#6756).
        // Note: may fail for combined-theory clauses where rewriting simplified
        // linking equalities; the pre-rewrite pass above is primary.
        self.reconstruct_missing_farkas_and_demote(proof, &hidden_equality_assertions);

        // Term rewriting can merge distinct auxiliary variables into the same
        // surface term, invalidating pre-rewrite resolution chains. Strip
        // stale resolution steps and rebuild from the rewritten proof.
        //
        // #diagnostic-envelope AMENDMENT — REBUILD ONLY ON A VERDICT. This is a
        // REPAIR, and a repair needs a diagnosis. `Undetermined` is not one: it
        // says the caller-owned envelope stopped the checker before it learned
        // anything about this chain, which is a statement about our remaining
        // time and memory, not about the proof. Rebuilding on it means entering
        // `strip_resolution_steps` -> the ten-strategy `ensure_empty_clause_derivation`
        // ladder -> a whole `reconstruct_missing_farkas_and_demote` — none of
        // them cheap, the ladder not cancellable at all — precisely BECAUSE the
        // solve was told to stop. Measured on deductive-checks's
        // `datatype_ne_refutation::t_dbl_one_eq` that was 12 rebuilds per solve,
        // all 12 `Cancelled`, the largest on a 199,149-step proof.
        //
        // What declining the repair means, limb by limb — stated precisely
        // because the two `Undetermined` causes have OPPOSITE publication
        // consequences and an earlier draft overclaimed here:
        //
        //  * `Cancelled`: the same four stop signals make
        //    `stop_declines_unsat_publication` convert the solve to `unknown`,
        //    so nothing downstream publishes and the declined repair is pure
        //    saved work.
        //  * `BudgetRefused`: no stop signal — the solve PUBLISHES, through
        //    `check_strict_unsat_presentation`'s own separately-metered
        //    re-validation of whatever chain is presented. On this limb,
        //    declining the repair RETAINS the original chain where the old
        //    strip-and-rebuild could have replaced part of it with a trust
        //    head (`ensure_empty_clause_derivation`'s last resort) that the
        //    certification gate rejects. A valid-but-large chain can therefore
        //    certify here where the rebuild path answered `unknown`. That is
        //    an ACCEPTING-direction difference, and it is safe for the same
        //    reason it was safe before the envelope existed: this is exactly
        //    the pre-envelope (f1f93ed25) outcome for a valid chain — the
        //    envelope's refusal never becomes acceptance by itself, because
        //    nothing is published on this walk's say-so; acceptance still
        //    requires the publication gate's fresh, full re-check to PASS on
        //    the retained chain.
        if self.empty_clause_derivation_status(proof) == EmptyClauseDerivation::Invalid {
            crate::executor::proof_resolution::strip_resolution_steps(proof);
            self.ensure_empty_clause_derivation(proof);
            // Reconstruct Farkas for any trust lemmas created by rebuild (#6757).
            self.reconstruct_missing_farkas_and_demote(proof, &hidden_equality_assertions);
        }
    }

    /// Prunes `proof` to a single empty-clause dependency cone, preferring the first
    /// cone the independent strict checker accepts.
    ///
    /// Assumes `proof` derives at least one empty clause. Falls back to the historical
    /// final-empty pruning whenever no candidate cone is strictly checkable, so the
    /// selection remains fail closed.
    fn select_empty_clause_root(&mut self, proof: &mut Proof) {
        // More than one subsystem may close the same solve. In particular, a
        // quantified-instance producer can derive an authored `forall_inst`
        // refutation before the ground solver later appends a weaker
        // `Assume(instance) + trust` contradiction. Selecting the last empty
        // clause would discard the certified proof and retain the foreign
        // assumption. Prefer the first dependency cone that the independent
        // strict checker accepts; bounded failure falls back to the historical
        // final-empty selection and therefore remains fail closed.
        const MAX_STRICT_EMPTY_CANDIDATES: usize = 32;
        let empty_clause_roots: Vec<usize> = proof
            .steps
            .iter()
            .enumerate()
            .filter_map(|(index, step)| match step {
                ProofStep::Resolution { clause, .. } | ProofStep::Step { clause, .. }
                    if clause.is_empty() =>
                {
                    Some(index)
                }
                _ => None,
            })
            .collect();
        let mut selected_strict_root = false;
        if empty_clause_roots.len() > 1 {
            for target in empty_clause_roots
                .iter()
                .copied()
                .take(MAX_STRICT_EMPTY_CANDIDATES)
            {
                let mut candidate = proof.clone();
                if crate::executor::proof_resolution::prune_to_empty_clause_derivation_at(
                    &mut candidate,
                    target,
                ) {
                    match self.check_proof_strict_with_datatypes(&candidate) {
                        Ok(_) => {
                            *proof = candidate;
                            selected_strict_root = true;
                            break;
                        }
                        Err(error) if ay_core::misc_cli_flags().trace_cegqi_attr => {
                            eprintln!(
                                "[quant-proof] empty root {target} strict selection declined: {error}"
                            );
                            for (index, step) in candidate.steps.iter().take(64).enumerate() {
                                eprintln!("[quant-proof] candidate[{index}] = {step:?}");
                            }
                        }
                        Err(_) => {}
                    }
                }
            }
        }
        if !selected_strict_root {
            crate::executor::proof_resolution::prune_to_empty_clause_derivation(proof);
        }
    }

    /// Re-tags leaves of the pruned proof whose kind the strict checker's own
    /// recognizers independently confirm: finite-domain pigeonholes, contextual ROW2,
    /// datatype distinctness, LIA divisibility, the FP families, and str.len axioms.
    ///
    /// Assumes `proof` is already pruned to its load-bearing empty-clause cone, so
    /// these decisions are made on exactly the steps that will be published. Every
    /// pass is fail-closed: an unrecognized leaf keeps its existing Generic/trust kind.
    fn promote_certified_theory_lemma_kinds(&mut self, proof: &mut Proof) {
        // RoundingMode finite-domain certification. The core represents
        // SMT-LIB's built-in five-element sort as uninterpreted and injects its
        // domain axioms before solving. SAT reconstruction can surface those
        // roots either as Generic theory lemmas or as premiseless `trust`
        // leaves. Promote only exact instances accepted by the proof checker's
        // own five-mode recognizer; every other generated leaf remains trust.
        self.rebuild_finite_enum_pigeonhole_refutation(proof);
        // The generic rebuild gets one ownership-checked opportunity. Do not
        // retain a potentially large detector graph beside the final proof.
        self.clear_finite_enum_proof_state();
        self.rebuild_rounding_mode_pigeonhole_refutation(proof);
        Self::promote_rounding_mode_domain_lemmas(&self.ctx.terms, proof);

        // Contextual ROW2 repair (#trust-count→0): the eager array lane can
        // record the context-dependent unit `select(store(a,i,v),j)=select(a,j)`
        // and let SAT use the separate `i≠j` assertion.  A unit ROW2 equality
        // is not a theorem.  Rebuild the load-bearing proof from the two original
        // assertions with the self-contained guarded ROW2 clause before any
        // quality/strictness decisions are made.
        self.promote_contextual_array_row2_lemmas(proof);
        self.replace_with_exact_authored_array_row2_refutation(proof);

        // Datatype constructor-distinctness promotion (#8419 / trust_count→0).
        // The live conflict classifier emits `(not (= C1(..) C2(..)))` for
        // distinct constructors as Generic/trust because it does not carry the
        // datatype registry. Now — on the pruned, load-bearing proof, with the
        // elaboration context's declarations available — promote the confirmed
        // distinctness lemmas to the strict-checkable `DatatypeDistinct` kind so
        // the strict checker validates them and the terminal-trust gate no
        // longer downgrades these UNSATs to unknown. Mirrors the existing
        // `promote_generic_theory_lemma_kinds_after_rewrite` pass.
        self.promote_datatype_distinct_lemmas(proof);

        // Integer-divisibility promotion (#trust-count→0): a linear conflict that
        // is RATIONALLY satisfiable but INTEGER-infeasible (`2y = 7`: gcd 2 ∤ 7)
        // is missed by Farkas reconstruction (rational) and, in a nonlinear
        // context, emitted as `Generic`/trust. Promote each such single-literal
        // lemma the checker's own recognizer confirms to the strict-checkable
        // `LiaGeneric` + `Divisibility`. SOUND: the recognizer IS the strict
        // checker's `validate_divisibility` (gcd test with an integer-sort guard),
        // so a promoted step is independently re-validated; non-matching lemmas
        // stay trust. No verdict change — the lemma is already a valid tautology.
        Self::promote_lia_divisibility_lemmas(&self.ctx.terms, proof);

        // FP classification promotion (#trust-count→0): re-tag a Generic/trust FP
        // classification/identity lemma to the strict-checkable `FpClassification`
        // kind iff the checker's own recognizer confirms it (exhaustive bounded
        // exact-IEEE evaluation). SOUND + fail-closed; see method.
        Self::promote_fp_classification_lemmas(&self.ctx.terms, proof);

        // FP forward-error promotion (#trust-count→0): re-tag the Generic/trust
        // lemma that closes a forward-error refutation (negated input facts +
        // negated rounding-error goal) to the strict-checkable `FpForwardError`
        // kind iff the checker's own analytic recognizer confirms it (full
        // exact-rational re-derivation of the enclosure/error propagation).
        // SOUND + fail-closed; see method.
        Self::promote_fp_forward_error_lemmas(&self.ctx.terms, proof);

        // RoundingMode finite-domain proof promotion. The solve path injects
        // exact five-value distinctness/coverage axioms because the core stores
        // `RoundingMode` as an uninterpreted sort. Those formulas are FP-theory
        // theorems, not authored assumptions. Promote only units accepted by
        // the strict checker's exact schema recognizer; malformed or partial
        // lookalikes remain trust/unauthorized and fail closed.
        Self::promote_fp_rounding_mode_domain_axioms(&self.ctx.terms, proof);

        // Packed propositional clauses introduced by top-level connective
        // flattening are generated tautologies, not authored assumptions.
        // Promote only units accepted by the strict checker's structural
        // complement/and-projection recognizer. This is deliberately separate
        // from the RM-domain rule: one certifies Boolean clausification, the
        // other certifies the fixed IEEE domain.
        Self::promote_bool_tautology_leaves(&self.ctx.terms, proof);

        // str.len length-axiom promotion (#selfcert-strlen): the solver injects
        // universally-valid str.len theorems (concat-length sum, empty↔zero,
        // non-negativity, constant/equal length, containment bounds) during
        // QF_SLIA/QF_S preprocessing. Being no authored premise, they surfaced as
        // foreign `assume` leaves the #8821 provenance gate rejected, degrading a
        // correct UNSAT to `unknown`. Re-tag each such leaf as the strict
        // checker's independently re-derived `StringLengthLemma` rule; malformed
        // lookalikes stay `assume` and fail closed.
        Self::promote_string_length_lemma_axioms(&self.ctx.terms, proof);
    }

    /// Reconstructs the proofs that degenerated to a single empty-clause `trust` step
    /// because an assertion folded to `false` during elaboration.
    ///
    /// Each pass assumes the same degenerate shape and rebuilds `assume` + a strict-
    /// checkable theory lemma + resolution from the parsed assertion. Order matters:
    /// the specific reconstructions run before the general bounded Boolean fallback so
    /// each keeps its own dedicated certificate. All are SOUND + fail-closed.
    fn reconstruct_folded_assertion_collapses(&mut self, proof: &mut Proof) {
        // Array read-over-write collapse (#trust-count→0): an assertion that is
        // the negation of a ROW1 instance folds to `false` during elaboration,
        // degenerating the UNSAT proof to a single empty-clause `trust` step.
        // Reconstruct the assume + strict-checkable `ArraySelectStore` lemma +
        // resolution from the parsed assertion. SOUND + fail-closed; see method.
        self.promote_array_row_collapse(proof);
        self.promote_array_row_value_mismatch(proof);

        // Datatype selector-projection collapse (#trust-count→0): an assertion
        // `(not (= (sel_i (C a..)) a_i))` folds to `false` during elaboration,
        // degenerating the proof to a single empty-clause trust step.
        // Reconstruct assume + strict-checkable `DatatypeSelectorProject` lemma +
        // resolution from the parsed assertion. SOUND + fail-closed; see method.
        self.promote_dt_selector_collapse(proof);

        self.promote_reflexive_collapse_family(proof);

        // Bitvector identity collapse (#trust-count→0): a small-width BV assertion
        // `(not (= (OP a b) c))` whose equality is a bounded tautology folds to
        // `false`, degenerating the proof to a single empty-clause trust step.
        // Reconstruct assume + strict-checkable `BvBitBlast` lemma (re-validated
        // by exhaustive bounded evaluation) + resolution. SOUND + fail-closed;
        // see method.
        self.promote_bv_identity_collapse(proof);

        // Linear-arithmetic identity collapse (#trust-count→0): an integer
        // assertion `(not (= L R))` whose equality is a linear tautology (e.g.
        // `(* x 0) = 0`) folds to `false`, degenerating the proof to a single
        // empty-clause trust step. Reconstruct assume + strict-checkable
        // `LiaGeneric`/`LinearIdentity` lemma + resolution. SOUND + fail-closed;
        // see method.
        self.promote_nia_linear_identity_collapse(proof);

        // Euclidean `mod` range collapse (#trust-count→0): an authored
        // equality such as `(= (mod x 3) 4)` is rejected by the LIA encoder
        // before a checkable range certificate survives, leaving a trust-backed
        // terminal derivation. Rebuild the exact authored equality plus a
        // strict-checkable `LiaModRange` theorem. The checker independently
        // requires a non-zero constant divisor and an out-of-range constant
        // remainder.
        self.promote_lia_mod_range_collapse(proof);

        // If-then-else identical-branches collapse (#trust-count→0): an assertion
        // `(not (= (ite c x x) x))` folds to `false`, degenerating the proof to a
        // single empty-clause trust step. Reconstruct assume + strict-checkable
        // `IteSame` lemma (raw `mk_ite_raw` keeps the ite) + resolution. SOUND +
        // fail-closed; see method.
        self.promote_ite_same_collapse(proof);

        // Boolean tautology collapse (#trust-count→0): a propositional
        // contradiction assertion (e.g. `(not (= (not (not p)) p))`) folds to
        // `false`, degenerating the proof to a single empty-clause trust step.
        // Run this general bounded fallback after the more specific IteSame
        // reconstruction so the latter retains its dedicated certificate and
        // Lean firewall artifact. Reconstruct assume(A) + strict-checkable
        // `BoolTautology` lemma `(not A)` (re-validated by exhaustive bounded
        // evaluation) + resolution. SOUND + fail-closed; see method.
        self.promote_bool_tautology_collapse(proof);
    }

    /// Rescues the residual `trust` steps that the per-assertion collapse
    /// reconstructions above cannot reach: the whole-proof QF_BV bit-blast collapse and
    /// the NIA pin-substitution step.
    ///
    /// Assumes the collapse promotions have already run (the BV rescue fires only on
    /// what they left behind) and that LIA divisibility promotion has already run (the
    /// pin-substitution detection keys on `step[1]` being LiaGeneric/Divisibility).
    fn rescue_residual_trust_steps(&mut self, proof: &mut Proof) {
        // BV bit-blast whole-proof collapse (C5): a QF_BV UNSAT established
        // through the eager bit-blast + SAT lane whose reconstructed proof
        // degenerated to the single empty-clause `trust` step (and that none
        // of the specific collapse promotions above could reconstruct).
        // Faithfully rebuild every parsed assertion, then prefer an internal
        // `BvBitBlast` lemma only when the checker independently recognizes
        // the joint-negation clause and the assembled proof replays strict-
        // complete. The Alethe printer still lowers this general lemma to an
        // attributed `hole`: carcara's BV support requires cvc5's `@bbterm`
        // convention, which ay's blaster does not produce.
        // If either gate declines, preserve real `assume`s plus ONE attributed
        // `hole` for the exact joint negation/closing chain. Every checkable
        // step remains valid, and the unchecked gap remains explicit.
        // Fail-closed: fires only on the degenerate shape, only when EVERY
        // assertion faithfully rebuilds inside the QF_BV bool/BV fragment
        // (per-node raw-application guards), and only when BV content is
        // present. The strict gate rejects the fallback hole while accepting
        // the independently checked `BvBitBlast` candidate.
        self.rescue_bv_bitblast_collapse(proof);

        // NIA pin-substitution collapse (#trust-count→0): the residual trust step
        // in pinned-multiplication infeasibility. After divisibility promotion the
        // proof is trust(= k (* v c)) + divisibility(¬…) + resolution; the trust
        // step derives the substituted equation from (= (* a b) k) ∧ (= a c).
        // Reconstruct it as assume + eq_congruent + LinearIdentity bridge +
        // eq_transitive + resolution. MUST run after promote_lia_divisibility_lemmas
        // (the detection keys on step[1] already being LiaGeneric/Divisibility) and
        // is orthogonal to split_euf_congruence_lemmas (that pass rewrites trust
        // *TheoryLemma*s; this trust step is a *Step*). SOUND + fail-closed with a
        // whole-proof check_proof_strict revert gate; see method.
        self.promote_nia_pin_substitution(proof);
    }

    /// Lowers the equality-reasoning leaves to derivations an external checker can
    /// re-run: the fused-congruence split, the Shannon ITE guard clauses, the certified
    /// generic EUF leaves, the shadowed-store expansion, and extensionality provenance.
    ///
    /// The order inside is load-bearing and documented per pass: the ITE guard rebuild
    /// must precede `promote_certified_generic_euf_leaves` (whose whole-proof atomic
    /// gate reverts while those trust leaves remain), and the extensionality pass runs
    /// last because it appends steps that must survive every prune.
    fn certify_euf_and_array_leaves(&mut self, proof: &mut Proof) {
        // EUF fused-congruence split (#trust-count→0): the congruence closure
        // emits `a=b ∧ b=c → f(a)=f(c)` as ONE `trust` lemma; split it into a
        // checker-validated `eq_transitive` + `eq_congruent` + their resolution
        // so the proof carries no trust step here. Fail-safe: only fires on the
        // recognized unary-congruence-over-chain shape, reproduces the original
        // clause exactly, and leaves any other lemma untouched.
        let euf_split_should_stop = self.make_strict_check_stop();
        let euf_split_memory_limit = self.memory_limit();
        Self::split_euf_congruence_lemmas(
            &mut self.ctx.terms,
            proof,
            &self.ground_conflict_decomp_meters,
            &euf_split_should_stop,
            euf_split_memory_limit,
        );

        // General certified EUF-leaf promotion. Unlike the all-or-nothing
        // original-assertion surgery, this replaces only individually
        // recognized Generic EUF leaves and preserves every Assume verbatim.
        // That keeps independent proof obligations separate: an unrelated
        // preprocessing-authority gap remains visible, while the EUF clause
        // itself carries eq_congruent/eq_transitive/eq_congruent_pred plus an
        // explicit weakening for unused conflict literals. Atomic strict
        // validation prevents partial promotion from masking any other trust.
        // Authenticated array-extensionality leaves are deferred: the EUF pass
        // promotes them only on its strict clone; the final pass stays below.
        // Boolean-ITE guard-clause rebuild (#ite-guard-promotion): an
        // asserted Shannon-lifted `(ite c A B)` — the recorded update-axiom
        // instance shape the consequence-replay probe re-solves — is
        // clausified into the two guard clauses, whose assumes the demotion
        // pass exported as premiseless `trust` steps. Re-derive each
        // recognized guard clause from its authored root with
        // `ite1`/`ite2`/`eq_symmetric` steps the strict checker re-validates;
        // each chain is strict-checked in isolation before it may replace its
        // leaf, and a declined chain leaves the `trust` step byte-identical.
        // MUST run before `promote_certified_generic_euf_leaves`: that pass's
        // whole-proof atomic gate reverts while these trust leaves remain,
        // and this pass's output is what lets it commit. This is what lets
        // the same-context probe certify frame-quantifier UNSAT (#mbqi-completeness Q2).
        self.promote_shannon_ite_guard_trust_leaves(proof);

        self.promote_bool_finite_select_expansion_surface(proof);
        self.promote_certified_generic_euf_leaves(proof);

        // Shadowed-store equality expansion: the eager array fixpoint uses the
        // compact, solve-friendly theorem
        //
        //   store(store(a,i,v),j,x) = store(store(a,i,w),j,x)
        //     -> i=j OR v=w.
        //
        // It is a derived theorem, not a primitive ROW rule.  Replace only the
        // exact Generic schema with a strict proof composed from equality
        // congruence, ROW1/ROW2, transitivity, and resolution.  This runs after
        // the generic EUF splitter so the whole-proof strict/revert gate is not
        // defeated by another congruence lemma that the preceding pass can
        // already discharge.
        self.split_shadowed_store_equality_lemmas(proof);

        // Array extensionality certification (#ext-diff-cert). The eager array
        // lane INJECTS the Skolemized extensionality axiom
        // `(= a b) ∨ ¬(= (select a k) (select b k))` as an assertion; being no
        // problem premise, it ended up either demoted to `trust` or rejected at
        // export as a non-problem `assume`, and the `--self-check` gate degraded
        // the whole (correct) UNSAT to `unknown`.
        //
        // The clause is NOT a tautology, so it cannot simply be relabelled a
        // theory lemma. This pass instead records the WITNESS PROVENANCE as
        // proof content — an `array_ext_diff_intro` step binding `k` to the
        // pair it was minted for — which `ay-proof` then independently checks
        // (bound once, not self-referential, and FRESH against the problem's
        // own symbols). This second, idempotent call runs last: it appends steps
        // that must survive every prune and matches the axiom in whichever shape
        // the passes above left it. Fail-closed; see `proof_array_ext`.
        self.promote_array_extensionality_axioms(proof);
    }

    /// Re-runs the promotion recognizers that late proof surgery can undo, and admits
    /// the semantically checked BV lemmas.
    ///
    /// Assumes every surgery pass has already run: this is the final authority boundary
    /// before validation, so a re-materialized RM conflict or str.len `assume` leaf is
    /// caught here. Re-running is idempotent and each recognizer stays fail-closed.
    fn reassert_final_promotion_boundaries(&mut self, proof: &mut Proof) {
        // Final RM authority boundary. Late proof surgery may retain the
        // solver's weakened six-term conflict clause even after the injected
        // domain/Boolean assumptions above were individually certified. The
        // exact checker recognizes its load-bearing literal only when it is the
        // complete K6 pairwise-distinct negation over the five-value RM domain.
        // Re-run the same producer/checker predicate here, after every surgery;
        // malformed, partial, or wrong-sort conflicts remain Generic and fail
        // strict validation.
        Self::promote_fp_rounding_mode_domain_axioms(&self.ctx.terms, proof);

        // Final str.len length-axiom boundary (#selfcert-strlen): mirror the RM
        // boundary above — a late collapse/rebuild pass can re-materialize an
        // injected length axiom as an `assume` leaf, so re-run the promotion here,
        // after every surgery and immediately before proof validation, so no
        // certified length theorem is left as a foreign assume.
        Self::promote_string_length_lemma_axioms(&self.ctx.terms, proof);

        // A re-decision whose proof feeds only a trust-accepting screen reads
        // no promotion below (`unsat_cert/screened_reconfirmation.rs`).
        if self.skips_trust_elimination_repairs() {
            return;
        }

        // A search that kept no SAT-level refutation (a session whose proof
        // bookkeeping is budgeted, such as `ay --incremental`, exhausts it)
        // leaves one Generic lemma, the whole query's negation, which the
        // promotion below re-derives by bit-blasting the whole query. On a pure
        // bit-vector query the raw ground closure decides it word by word
        // first, as it does for the one-trust collapse the unbudgeted route
        // leaves (`rescue_bv_bitblast_collapse`): measured on external-codegen's imul
        // overflow body (consumer corpus `b32ed068cb36`), the one-shot route
        // certified in 2.2 s and the resident route spent its whole 30 s
        // deadline here. A decline leaves `proof` untouched. It goes before
        // the guarded collapse below, which never applies where it does (that
        // stage needs an array-reading root and steps aside for a pure
        // bit-vector closure). The closure raw re-interns the parsed roots, so
        // it is asked only when the elaborated assertions are pure bit-vector,
        // a question that interns nothing: on any other query this pass leaves
        // the term store as it found it. Asked unconditionally, it renumbered
        // the terms of the session's next check on `group_proofs`'
        // `frame_ite_lift` u64 fixture, whose Skolemized re-solve then took
        // another SAT trace and ended `unknown (QuantifierUnhandled)`.
        // A closure it commits here is an authored replacement like one the
        // cascade head commits, so it lifts the presentation bound's
        // withholding by the same rule.
        if Self::proof_rests_on_one_generic_lemma(proof)
            && self.elaborated_assertions_are_pure_bit_vector()
            && self.try_pure_bit_vector_ground_closure_first(proof)
        {
            self.publish_replacement_over_withheld_derivation(proof);
        }

        // Where promoting the Generic BV lemmas could not make this proof
        // publishable, the cascade's head asks the guarded collapse about the
        // authored roots whatever the promotion decides. Ask it first: it can
        // certify an authored root in a fraction of what the producer may
        // spend refusing a lemma
        // (`bv_identity_promotion/guarded/before_promotion.rs`). Only the
        // order changes: a proof it does not replace is promoted below as
        // before.
        self.promote_bv_guarded_collapse_before_promotion(proof);
        // So is the BvUremBound joint, where the promotion would pay for an
        // exact divider (`bv_identity_promotion/guarded/urem_bound/before_division.rs`).
        let _replaced = self.promote_urem_bound_before_generic_promotion(proof);

        // Generic BV conflicts are promoted only after the strict checker's
        // own semantic recognizer produces and replays a bit-blast/LRAT
        // refutation of the exact clause. This covers both the small exhaustive
        // lane and scalable width-32 identities while leaving SAT, unsupported,
        // or unsurfaceable clauses Generic (and therefore fail-closed).
        self.promote_semantically_checked_bv_lemmas(proof);
    }

    /// An authored replacement committed over a derivation the presentation
    /// bound withheld (#certify-before-presentation) carries its own authored
    /// surface, so its document is published exactly as it was when the bound
    /// installed the poison, once that surface authenticates. Asked where a
    /// replacement commits: the cascade head
    /// ([`Self::apply_authored_replacements_and_derivations`]), the pure
    /// bit-vector closure the Generic promotion tries first
    /// ([`Self::reassert_final_promotion_boundaries`]), and the BvUremBound
    /// joint asked ahead of an exact divider
    /// (`bv_identity_promotion/guarded/urem_bound/before_division.rs`).
    pub(in crate::executor::proof) fn publish_replacement_over_withheld_derivation(
        &mut self,
        proof: &Proof,
    ) {
        if self.last_proof_surface_withheld.is_some()
            && self.proof_has_authenticated_alethe_surface(proof)
        {
            self.last_unsat_proof_reconstruction_suppressed = false;
            self.last_proof_surface_withheld = None;
        }
    }

    /// Whether the only theory lemma of `proof` is Generic: the shape a
    /// refutation with no recorded SAT-level derivation is seeded into. Only a
    /// trigger: the closure decides from the raw authored roots alone and
    /// commits only a candidate the strict checker replays.
    fn proof_rests_on_one_generic_lemma(proof: &Proof) -> bool {
        let mut lemmas = proof.steps.iter().filter_map(|step| match step {
            ProofStep::TheoryLemma { kind, .. } => Some(kind),
            _ => None,
        });
        matches!(
            (lemmas.next(), lemmas.next()),
            (Some(TheoryLemmaKind::Generic), None)
        )
    }

    /// Runs the authored-root replacement cascade and the arithmetic fallbacks, then
    /// lowers the remaining certified leaves to re-runnable derivations and demotes
    /// whatever cannot be rendered.
    ///
    /// Assumes `proof` is otherwise final; every replacement here has its own atomic
    /// commit gate over the exact authored premise scope, so a declined replacement
    /// leaves `proof` unchanged. Leaves `proof` ready for `finalize_unsat_proof`.
    fn apply_authored_replacements_and_derivations(&mut self, proof: &mut Proof) {
        // Exact authored `false` premise (#verification-consumer-proof-assert-authority).
        //
        // A native consumer can legitimately assert the Boolean constant
        // `false` after independently simplifying an obligation.  SAT proof
        // reconstruction used to keep exploring unrelated theory conflicts in
        // that case, leaving Generic/trust leaves on the terminal path even
        // though the problem itself already contains the empty contradiction.
        // Replace that defective detour with the smallest strict proof, but
        // ONLY when the exact canonical `false` TermId is present in the
        // independently assembled authored premise scope.  The replacement is
        // committed only after the strict checker validates every step and the
        // premise authorization against that same scope.
        let withheld_derivation = self.last_proof_surface_withheld.map(|_| proof.clone());
        self.replace_with_exact_authored_false_refutation(proof);
        // A pure bit-vector query gets the word-level ground closure before
        // the cascade's bit-level members, which can spend the whole query
        // budget on one multiplier (`try_pure_bit_vector_ground_closure_first`).
        if !self.skips_trust_elimination_repairs()
            && !self.try_authenticated_native_bv_refutation(proof)
            && !self.try_pure_bit_vector_ground_closure_first(proof)
        {
            self.run_authored_replacement_cascade(proof);
        }
        if withheld_derivation.is_some_and(|derivation| derivation.steps != proof.steps) {
            self.publish_replacement_over_withheld_derivation(proof);
        }
        if self.proof_assembly_stop_requested() {
            return;
        }

        self.run_arithmetic_reconstruction_fallbacks(proof);
        // Some native certificate kinds are intentionally not surfaceable on
        // the pinned Alethe wire (for example `BvLiaTautology`). They are
        // valid internal certificates, but must not suppress an authored-root
        // reconstruction that can produce a fully checkable document. Give
        // the conjunction planner one final opportunity after the internal
        // fallback; its atomic commit gate still requires a complete strict
        // proof over the exact authored scope.
        if !self.skips_trust_elimination_repairs() && self.proof_has_known_wire_gap(proof) {
            self.replace_with_exact_authored_conjunct_refutation(proof, RepairEntry::Check);
        }
        let _promoted_intrinsic_leaves = self.promote_intrinsic_tautology_leaves(proof);
        // ... then the ones blocked only by ORDER; see `packed_euf_reordering`.
        let _derived_packed_euf = self.derive_packed_euf_transitive_reorderings(proof);
        // ... then lower every certified congruence-closure EXPLANATION to a
        // derivation an external checker can re-run; see
        // `congruence_explanation`.
        let _derived_congruence = self.derive_congruence_explanations(proof);
        if self.proof_assembly_stop_requested() {
            return;
        }
        // ... then the PACKED Boolean tautologies; see the module docs.
        let _derived_packed_tautologies = self.derive_packed_boolean_tautologies(proof);
        // ... then the GUARDED-EQUALITY arithmetic leaves whose KIND has no
        // wire spelling. Runs last of the derivation family and only on what
        // every authored replacement above declined, so a lane that already
        // produces a complete authored document keeps its byte-identical
        // output. It never widens the clause: the derivation's terminal
        // resolution reproduces the leaf's own clause, so every downstream
        // consumer is untouched. See `la_disequality_split`.
        let _derived_la_disequality_splits = self.derive_la_disequality_split_lemmas(proof);
        // A document that still carries NO derivation — a bare `trust`/`hole`
        // closer, as a solve with no clause trace or a poisoned rewrite leaves
        // it — is refuted exactly when the authored roots hold a complementary
        // pair `t` / `(not t)`; see `authored_complementary_roots`. An
        // incomplete candidate with no empty clause is eligible too; a
        // retained assume is not a refutation. Existing closed derivations
        // keep the original guard and are untouched.
        let _replaced_complementary_roots =
            self.replace_bare_closure_with_authored_complementary_roots_refutation(proof);
        false_source::demote_unattributed_assumed_false(self, proof);
        self.demote_unrenderable_eq_transitive_lemmas(proof);
        // Reintroduce exact source spellings only after every replacement and
        // demotion is complete. The printer confines these entries to their
        // own reachable `assume` and proves a checked bridge back to identity
        // spelling before any synthesized clause consumes them.
        // Replace an assumed elaborated conjunction by its exact authored
        // spelling plus checked transports, before the presentation pass
        // decides which assumes need an authored override.
        self.rehome_elaborated_conjunction_assumes(proof);
        self.restore_reachable_authored_assume_surface_overrides(proof);
    }
}
