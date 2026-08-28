// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof term rewriting for surface-syntax preservation.
//! Canonical operators need authenticated source syntax for external assumes.

// #8529: Use deterministic hash maps in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::term::TermData;
use ay_core::{AletheRule, Proof, ProofStep, Symbol, TermId};

use super::proof_surface_syntax::{
    collect_surface_term_overrides, format_forall_instance_surface, strip_frontend_annotations,
    surface_override_map_is_bounded,
};
use super::Executor;

mod ordered_tail;
mod surface_pairs;
use surface_pairs::{MAX_OVERRIDE_PAIRS, MAX_OVERRIDE_SOURCE_SCAN};

impl Executor {
    /// Whether a valid arithmetic `evaluate` is outside Carcara's portable evaluator.
    ///
    /// Carcara has no integer `rem` operator, and its current `div`/`mod`
    /// evaluator uses host truncating remainder semantics for negative inputs.
    /// AY's strict checker follows SMT-LIB/Z3 Euclidean semantics.  Keep those
    /// internally certified verdicts, but suppress a printable certificate rather
    /// than emit a rule whose external meaning differs. The traversal
    /// is bounded and fails closed on excessive proof terms.
    fn proof_has_nonportable_ground_evaluate(terms: &ay_core::TermStore, proof: &Proof) -> bool {
        const WORK_LIMIT: usize = 100_000;
        for step in &proof.steps {
            let ProofStep::Step {
                rule: AletheRule::Evaluate,
                clause,
                ..
            } = step
            else {
                continue;
            };
            let [equality] = clause.as_slice() else {
                continue;
            };
            let TermData::App(Symbol::Named(name), args) = terms.get(*equality) else {
                continue;
            };
            if name != "=" || args.len() != 2 {
                continue;
            }
            let mut stack = vec![args[0]];
            let mut seen = HashSet::default();
            while let Some(term) = stack.pop() {
                if !seen.insert(term) {
                    continue;
                }
                if seen.len() > WORK_LIMIT {
                    return true;
                }
                if matches!(
                    terms.get(term),
                    TermData::App(Symbol::Named(name), _) if matches!(name.as_str(), "div" | "mod" | "rem")
                ) {
                    return true;
                }
                stack.extend(terms.children(term));
            }
        }
        false
    }

    /// Original problem assertions that still have source-syntax provenance.
    pub(crate) fn proof_problem_assertions(&self) -> Vec<TermId> {
        if let Some(provenance) = &self.proof_problem_assertion_provenance {
            return provenance.problem_assertions.clone();
        }
        self.proof_original_problem_assertions()
    }

    /// Original assertion stack aligned with `assertions_parsed()`.
    pub(crate) fn proof_original_problem_assertions(&self) -> Vec<TermId> {
        if let Some(provenance) = &self.proof_problem_assertion_provenance {
            return provenance.original_problem_assertions.clone();
        }
        let parsed_len = self.ctx.assertions_parsed().len();
        if parsed_len == 0 {
            self.ctx.assertions.clone()
        } else {
            let prefix_len = parsed_len.min(self.ctx.assertions.len());
            self.ctx.assertions[..prefix_len].to_vec()
        }
    }

    /// Build the demotion whitelist for proof export.
    ///
    /// When provenance is active (combined deferred-postprocessing routes),
    /// the whitelist is restricted to problem assertions and their De Morgan
    /// duals — temporary derived constraints (mod/div side conditions, array
    /// axioms) are excluded so they get demoted to `trust` (#6759).
    ///
    /// When provenance is inactive, the legacy #6365 behavior is preserved:
    /// all current `self.ctx.assertions` plus their duals are whitelisted.
    fn proof_exportable_assertions(&mut self, rewrites: &HashMap<TermId, TermId>) -> Vec<TermId> {
        let mut exportable: Vec<TermId> = self.proof_problem_assertions();
        for assertion in self.proof_original_problem_assertions() {
            if !exportable.contains(&assertion) {
                exportable.push(assertion);
            }
        }

        if self.proof_problem_assertion_provenance.is_none() {
            // Legacy path: union all current assertions (#6365).
            // FlattenAnd preprocessing can expand one parsed assertion into
            // multiple solver-visible assertions; these are still legitimate
            // problem assertions and must not be demoted.
            for &assertion in &self.ctx.assertions {
                if !exportable.contains(&assertion) {
                    exportable.push(assertion);
                }
            }
        }

        // Tseitin activation clauses for `and`-assertions use the De Morgan
        // dual form produced by normalize_positive_literal. Compute duals from
        // the exportable subset only — not from raw temporary assertions when
        // provenance is active (#6365 Phase 2, narrowed by #6759).
        let dual_source: Vec<TermId> = if self.proof_problem_assertion_provenance.is_some() {
            exportable.clone()
        } else {
            self.ctx.assertions.clone()
        };
        for assertion in dual_source {
            if let TermData::App(sym, args) = self.ctx.terms.get(assertion).clone() {
                if sym.name() == "and" {
                    let negated_args: Vec<TermId> = args
                        .into_iter()
                        .map(|arg| self.ctx.terms.mk_not(arg))
                        .collect();
                    let disjunction = self.ctx.terms.mk_or(negated_args);
                    let dual = self.ctx.terms.mk_not_raw(disjunction);
                    exportable.push(dual);
                }
            }
        }

        if let Some(assumptions) = &self.last_assumptions {
            for &assumption in assumptions {
                if !exportable.contains(&assumption) {
                    exportable.push(assumption);
                }
            }
        }

        if !rewrites.is_empty() {
            let mut cache = HashMap::default();
            let rewritten: Vec<TermId> = exportable
                .iter()
                .copied()
                .map(|a| Self::rewrite_term(&mut self.ctx.terms, a, rewrites, &mut cache))
                .collect();
            for assertion in rewritten {
                if !exportable.contains(&assertion) {
                    exportable.push(assertion);
                }
            }
        }

        exportable
    }

    /// Rewrite proof terms to use surface syntax for canonicalized operators,
    /// then run the ASSUME-AUTHORIZATION tail.
    ///
    /// Only the surface-override collection needs the parsed AST. The tail —
    /// `demote_auxiliary_non_problem_assumptions`,
    /// `derive_conjunct_assumptions_from_problem_roots`,
    /// `demote_non_problem_assumptions` and
    /// `rebuild_trust_leaf_proof_from_original_assertions` — reasons purely
    /// over canonical `TermId`s and decides whether the certificate that
    /// `66538b006f` made MANDATORY can be minted at all. Skipping the whole
    /// tail with the parsed AST is therefore wrong; running ALL of it without
    /// the parsed AST is also wrong (see the NARROWED subset below). With no
    /// parsed prefix this function delegates to
    /// [`Self::run_assumption_authority_passes_without_parsed_syntax`].
    ///
    /// #retain-parsed-verdict-divergence. Retaining the parsed AST is a
    /// peak-RSS optimization the CLI turns OFF whenever no proof artifact can
    /// be emitted (`--no-proof`, `--z3-mode`, competition mode —
    /// `crates/ay/src/run.rs`), on the documented premise that "verdicts are
    /// unaffected; every consumer degrades gracefully on an empty prefix".
    /// That premise was false BECAUSE of this early return: skipping it also
    /// skipped the demotion pass, so an `assume` leaf left behind by an
    /// in-place preprocessing rewrite (e.g. the QF_ABV dense finite-array
    /// initializer rewrite) stayed a bare `assume` instead of becoming a
    /// `trust` step, and strict certification HARD-REJECTED the whole
    /// refutation with "assumes term outside the supplied problem obligation".
    /// Measured on this commit: six QF_ABV instances that z3, the library API
    /// and default CLI mode all decide `unsat` published `unknown` under
    /// `--z3-mode`/`--no-proof` — i.e. exactly the mode used for z3 parity.
    /// Moving the same `(set-option :produce-proofs true/false)` toggle from
    /// AFTER the assertions to BEFORE them (the only effect of which is to
    /// retain the parsed stack) flipped the verdict back to `unsat`.
    ///
    /// This grants no new authority: a demoted assume becomes a `trust` step
    /// that `mint_unsat_certificate` must still discharge INDEPENDENTLY (the
    /// forged-UNSAT fresh re-solve, full strict validation of every non-trust
    /// step, and per-clause confirmation) before the verdict may publish. It
    /// only makes the two CLI modes agree on the reference behaviour the
    /// library API and default mode already have.
    ///
    /// The overrides themselves still degrade to nothing without a parsed
    /// stack: both `override_pairs` arms zip against `parsed_assertions`, so
    /// an empty parsed stack yields no pairs and no term overrides.
    ///
    /// # The retention-off path is a NARROWED subset, not this whole function
    ///
    /// #cause-b-narrow-split. Running the *entire* tail with no parsed prefix
    /// was originally measured over 2,166 non-QF_Datatypes instances at
    /// **+301 gained, 12 LOST, 0 wrong**, and both recorded causes were
    /// attributed to ONE pass in the tail,
    /// [`Self::derive_conjunct_assumptions_from_problem_roots`]: 8 losses to a
    /// re-validation blowup it triggers by restructuring the proof (all
    /// `QF_IDL/parity`), and 4 to a CORRECTNESS DEFECT — a malformed `and_pos`
    /// ("clause must contain the and gate literal and the indexed conjunct")
    /// that it then rejects itself.
    ///
    /// **All three of those figures have since been REFUTED by measurement**
    /// (the development design notes, and the same
    /// refutation independently in
    /// the development design notes §4). Re-derived on
    /// 2,215 files, paired and interleaved: the split is **+11 gained / 7 LOST**,
    /// not +301/−12; the malformed `and_pos` produces **0 diagnostics in 2,215
    /// files**; and **not one `QF_IDL/parity` file flips** — that family is now
    /// a beneficiary (`01.100.graph` `trust` 54 → 1, `02.200.graph` 34 → 2,
    /// both still `unsat` under 3 s). Do not re-derive from the old numbers.
    ///
    /// The exclusion stands on the MEASURED reason instead. Re-run three reps,
    /// serially, with committed binaries, five of the seven SMT-LIB losses are
    /// noise (four are `sat` verdicts, which never enter this path at all) and
    /// **two are real and reproduce 3/3**: `QF_LRA/miplib/danoint-50` (`unsat`
    /// 3.9 s → `unknown`, because the pass derives all 66 leaves and the
    /// presentation goes REJECTED → CERTIFIED at +35 s of mandatory
    /// corroboration) and `QF_LIA/convert/convert-jpg2gif-query-1141` (`unsat`
    /// 7.0 s → `unknown`, +7 s for 946 of 1,020 leaves). Both files publish
    /// `unsat` under the demotion path anyway, via
    /// `discharge_trust_steps_for_certification`, so the reduction buys no
    /// verdict there and costs one. A ROOT-WEIGHT budget reusing
    /// `authored_conjunct_leaf::MAX_CONJUNCT_ROOT_WORK` fixes `danoint-50`
    /// exactly and costs the whole reduction (−21.3% → −1.6%); the two are not
    /// separable by root weight.
    ///
    /// And it is not needed for the loss the split exists to fix: measured on
    /// the cause-B exemplar and on the tracked reduced repro,
    /// [`Self::demote_non_problem_assumptions`] alone restores the verdict.
    /// So the retention-off configuration runs
    /// [`Self::run_assumption_authority_passes_without_parsed_syntax`] — the
    /// demotion passes and the trust-leaf rebuild, and NOT the derivation pass.
    /// It is gated there exactly as it was before 540fe30fb, i.e. it still only
    /// ever runs when a parsed prefix was retained.
    pub(super) fn apply_input_syntax_rewrites_to_proof(&mut self, proof: &mut Proof) {
        self.last_proof_term_overrides = None;
        if Self::proof_has_nonportable_ground_evaluate(&self.ctx.terms, proof) {
            self.suppress_unsat_proof_reconstruction();
        }
        if self.ctx.assertions.is_empty() {
            return;
        }
        // Main's fail-closed source-work audit runs FIRST so the retention-off
        // path below is still governed by it: budget exhaustion must poison the
        // proof regardless of which authority subset would have run.
        if !self.proof_source_work.spend(
            super::proof_trust_surgery_surface_audit::ProofSourcePass::InputSyntaxRewrite,
            self.ctx.assertions_parsed(),
        ) {
            let mut poisoned = Proof::new();
            poisoned.add_rule_step(AletheRule::Trust, Vec::new(), Vec::new(), Vec::new());
            *proof = poisoned;
            return;
        }
        if self.ctx.assertions_parsed().is_empty() {
            // cause-b-narrow-authority-split-v1
            self.run_assumption_authority_passes_without_parsed_syntax(proof);
            return;
        }

        let aux_assume_steps =
            Self::collect_assume_steps_with_aux_mod_div_vars(&self.ctx.terms, proof);
        let mut rewrites: HashMap<TermId, TermId> = HashMap::default();
        let Some((override_pairs, mut term_overrides)) = self.prepare_surface_overrides() else {
            Self::poison_input_syntax_rewrite(proof);
            return;
        };

        self.add_forall_instance_surface_overrides(proof, &override_pairs, &mut term_overrides);

        Self::infer_auxiliary_division_rewrites(&mut self.ctx.terms, proof, &mut rewrites);

        self.drop_rewrites_that_break_assumption_authority(proof, &mut rewrites);

        if !rewrites.is_empty() {
            let step_count_before = proof.steps.len();
            Self::rewrite_proof_terms(&mut self.ctx.terms, proof, &rewrites);
            debug_assert_eq!(
                proof.steps.len(),
                step_count_before,
                "BUG: proof rewriting changed step count from {} to {}",
                step_count_before,
                proof.steps.len()
            );
            Self::fixup_resolution_conclusions(&self.ctx.terms, proof);
        }

        self.finish_input_syntax_rewrite(proof, &rewrites, term_overrides, &aux_assume_steps);
    }

    /// The ASSUMPTION-AUTHORITY subset of
    /// [`Self::apply_input_syntax_rewrites_to_proof`] that is safe to run with
    /// no parsed-assertion prefix.
    ///
    /// # Why this function exists at all (#cause-b-parsed-gate)
    ///
    /// `66538b006f` made the strict UNSAT certificate MANDATORY: every
    /// published `unsat` now goes through the certification funnel. Separately,
    /// the #rss-vs-z3 optimization has the CLI call
    /// `set_retain_parsed_assertions(false)` whenever the session can emit no
    /// proof artifact — `--no-proof`, `--z3-mode`, competition mode
    /// (`crates/ay/src/run.rs:7969` and `:8582`) — because the parsed-AST clone
    /// was ~190 MB of a 318 MB peak. Those two features interact:
    /// `apply_input_syntax_rewrites_to_proof` used to bail wholesale on an
    /// empty parsed prefix, which switched off not only the COSMETIC
    /// surface-syntax half (which genuinely needs the frontend ASTs) but also
    /// the authority passes, which reason purely over canonical `TermId`s and
    /// need no parse tree. Foreign leaves therefore stayed bare `Assume`s;
    /// `ProofCheckError::UnauthorizedAssumption` is NOT trust-eligible in
    /// `unsat_cert.rs`, so `discharge_trust_steps_for_certification` — the
    /// funnel's own rescue — was never reached, and a computed, correct
    /// refutation published as `unknown`. Measured 89 such discarded UNSATs.
    ///
    /// # Why the derivation pass is deliberately absent
    ///
    /// See the re-derived measurement on
    /// [`Self::apply_input_syntax_rewrites_to_proof`] — NOT the `QF_IDL/parity`
    /// blowup and NOT the malformed `and_pos`, both of which are refuted there.
    /// `derive_conjunct_assumptions_from_problem_roots` reduces the premiseless
    /// `Trust` class by a real 21.3% off the in-tree corpus and by exactly 0%
    /// on it, and it loses two SMT-LIB verdicts that survive three interleaved
    /// serial reps with the committed binaries. Cause B does not need it: the
    /// demotion below is sufficient on the cause-B exemplar and on the tracked
    /// reduced repro.
    /// Leaving it out keeps the retention-off path strictly narrower than the
    /// retention-on path it was measured against. `proof_rewrite_tests.rs`
    /// pins that absence so a later refactor cannot silently re-enable it.
    ///
    /// # This grants no authority
    ///
    /// Demotion turns an unauthorized `assume` into a `trust` step that
    /// `mint_unsat_certificate` must still discharge INDEPENDENTLY (forged-
    /// UNSAT fresh re-solve, full strict validation of every non-trust step,
    /// per-clause confirmation). `problem_assertions_for_strict_proof()` is not
    /// touched, so nothing solver-generated enters the frozen obligation.
    pub(in crate::executor) fn run_assumption_authority_passes_without_parsed_syntax(
        &mut self,
        proof: &mut Proof,
    ) {
        debug_assert!(
            self.ctx.assertions_parsed().is_empty(),
            "BUG: the narrowed authority subset is only for the retention-off configuration"
        );
        tracing::debug!(
            "cause-b-narrow-authority-split-v1: no parsed prefix retained; running the \
             assumption-authority subset (demote + trust-leaf rebuild) and skipping both the \
             COSMETIC surface-syntax half and derive_conjunct_assumptions_from_problem_roots"
        );

        let aux_assume_steps =
            Self::collect_assume_steps_with_aux_mod_div_vars(&self.ctx.terms, proof);
        // No surface rewrites are collected on this path, so the exportable
        // whitelist is built against an empty rewrite map.
        let no_rewrites: HashMap<TermId, TermId> = HashMap::default();
        let extended_assertions = self.proof_exportable_assertions(&no_rewrites);
        Self::demote_auxiliary_non_problem_assumptions(
            proof,
            &extended_assertions,
            &aux_assume_steps,
        );
        // DELIBERATELY NOT `derive_conjunct_assumptions_from_problem_roots`.
        Self::demote_non_problem_assumptions(proof, &extended_assertions);
        // #fresh-def-eq — the fresh-definition promotion DOES belong here, by
        // this function's own criterion: it reasons purely over canonical
        // `TermId`s and needs no parse tree. It is not the derivation pass and
        // carries none of its cost: two DAG traversals over the assertion
        // scope and the candidate definientia, plus one `FreshDefRegistry`
        // collect, all skipped outright when no candidate `trust` leaf exists.
        //
        // Leaving it out was measured, not assumed, to make the whole
        // capability unreachable in the census regime: the CLI turns retention
        // OFF for `--no-proof` / `--z3-mode` / competition mode, which is
        // exactly the mandatory-certificate regime, and all 4 corpus files that
        // carry a genuine fresh definitional EQUALITY are plain SMT files in it.
        // Before this call they reached `check_strict_unsat_presentation` with
        // the definition still a premiseless `trust` step.
        //
        // It grants no authority for the same reason the demotion above does
        // not: the promoted step is re-validated from scratch by the UNTOUCHED
        // strict checker through `ay_proof`'s `FreshDefRegistry`, and this
        // lane's own Gate-2 reverts the whole rewrite if that registry
        // declines. `problem_assertions_for_strict_proof()` is not touched.
        self.promote_fresh_definitional_bounds(proof, &extended_assertions);
        // (#4751) `EqDiffVar`-REWRITTEN assertions — the residual the promotion
        // above correctly declines, because a rewritten assertion is not a
        // definition. It belongs here by this function's own criterion: it
        // reasons purely over canonical `TermId`s against provenance the
        // preprocessing pass minted, and needs no parse tree. It is NOT
        // `derive_conjunct_assumptions_from_problem_roots` and carries none of
        // that pass's cost: its first guard is an emptiness test on the
        // `EqDiffVar` record store, so a solve the pass never ran on pays one
        // `is_empty()`.
        //
        // Leaving it out was MEASURED, not assumed, to make the whole
        // capability unreachable in the regime that produces the population —
        // the same finding `#fresh-def-eq` records two calls above, and for the
        // same structural reason. The `EqDiffVar` pass runs only when the
        // CALLER did not ask for a proof (`!is_producing_proofs()`, see
        // `Executor::eq_diffvar_pass_enabled`), and the CLI turns parsed
        // retention OFF for exactly that case (`--no-proof`, `--z3-mode`,
        // competition mode). So every difference variable AY mints in the
        // mandatory-certificate regime reaches this function, and before this
        // call not one of them could be discharged here. Measured on the
        // SMT-LIB QF_IDL `mathsat/fischer` family: 25 of the 146 premiseless
        // `trust` leaves of `FISCHER7-3-ninc` mention `__ay_eqdv`, and the lane
        // was never entered — `derive_eq_diffvar_rewritten_assertions` logged
        // no call at all while the store held 45 atom folds and 454 rewrites.
        //
        // It grants no authority. Every step it emits is re-validated from
        // scratch by the UNTOUCHED strict checker — `fresh_def_bound` through
        // `ay_proof`'s `FreshDefRegistry`, the arithmetic lemmas through the
        // same Farkas and `la_disequality` validators the strict `lra_farkas`
        // path uses — and the lane's own Gate-2 re-runs `FreshDefRegistry`
        // over the spliced result and declines the WHOLE lane if the registry
        // does, so a promotion it cannot justify never becomes a hard
        // `InvalidTheoryLemma` in place of the rescuable `trust` it replaced.
        // `problem_assertions_for_strict_proof()` is not touched.
        //
        // THE COMMIT GATE IS NOT A LATENCY NICETY — it is what keeps this
        // wiring from LOSING correct `unsat` verdicts.
        //
        // Mechanism, measured end to end on `ay solve --no-proof -T:10`. The
        // derivations do their job — they remove premiseless `trust` leaves —
        // and on a LARGE proof that is precisely the harm: with the early trust
        // leaf gone, the strict checker no longer fails fast on it and instead
        // walks (and meters) the whole document, on EVERY proof assembly. Two
        // measured failure shapes follow (SMT-LIB QF_IDL 900-file paired
        // sample, 2026-08-27, with the `and_pos` charge fix already in):
        //
        //  * the walk runs out of the aggregate WORK envelope: the
        //    presentation degrades from a rescuable trust-family rejection to
        //    `ProofCheckError::ResourceLimit`, `unsat_cert`'s deferred lane
        //    reaches `discharge_trust_steps_for_certification` with NOTHING
        //    collected, and the mint falls through to a whole-problem re-solve
        //    (`planning/plan-8..14`, `sal/lpsat-goal-7`: correct `unsat`s
        //    published `unknown`);
        //  * the walk SUCCEEDS but is expensive, and the pipeline re-runs it
        //    ~60 times across assemblies (`sal/bakery/inf-bakery-mutex-18`:
        //    60 walks x 287-295M work = +6.4s, crossing `-T:10` with no
        //    refusal anywhere).
        //
        // This wiring used to carry a 4,096-step call-site size bound against
        // the first shape (2026-08-25: 44 of 900 files degraded unbounded).
        // The bound is gone: the dominant mis-billing was fixed at its source
        // (`ay-proof`'s `and_pos_is_emitted_identity_shape` — 39.7M-511.5M
        // work units per O(1) `and_pos` step), and the residual is decided by
        // the commit gate BELOW, which prices the exact publication walk of
        // the FINISHED document and reverts the splice when that walk refuses
        // or is too expensive to keep re-running. A SIZE bound cannot express
        // that criterion: `mathsat/fischer/FISCHER5-3-ninc` (5,117 pre-splice
        // steps) was the smallest degrader under the old charge model and now
        // commits, while `planning/plan-7.cvc` must revert however small it
        // starts.
        //
        // The gate CANNOT sit inside the lane: at this point of the subset the
        // proof still carries the premiseless leaves the passes BELOW derive,
        // so a strict walk here fails fast on one of those and prices nothing
        // (measured: every `sal/bakery` splice looked cheap mid-subset and
        // cost 287M+ per walk once the tail lanes had cleared the early
        // leaves). It prices the SUBSET'S OWN OUTPUT instead, after
        // `rebuild_trust_leaf_proof_from_original_assertions`, and on a revert
        // re-runs the tail exactly as the never-spliced path would have.
        let eqdv_snapshot = (!self.eq_diffvar_retention_off_decline_covers(proof)
            && self.eq_diffvar_lane_would_consider(proof))
        .then(|| proof.clone());
        let eqdv_spliced = if eqdv_snapshot.is_some() {
            self.derive_eq_diffvar_rewritten_assertions(proof, &extended_assertions)
        } else {
            false
        };
        self.run_post_eqdv_authority_tail(proof, &extended_assertions);
        if let (Some(snapshot), true) = (eqdv_snapshot, eqdv_spliced) {
            match self.eq_diffvar_presentation_commit_decision(proof) {
                super::proof_propagated_rewrite::EqDiffVarCommitDecision::Commit => {}
                super::proof_propagated_rewrite::EqDiffVarCommitDecision::Revert { remember } => {
                    *proof = snapshot;
                    if remember {
                        // Record the PRE-SPLICE size the decline was priced
                        // at; see the field's doc for the scope rule.
                        self.eqdv_retention_off_declined_at_steps
                            .set(proof.steps.len().max(1));
                    }
                    // The tail's work above was built on the discarded splice;
                    // rebuild it from the restored proof, exactly as the
                    // never-spliced path would have.
                    self.run_post_eqdv_authority_tail(proof, &extended_assertions);
                }
            }
        }
    }

    /// The authority passes that run AFTER the `EqDiffVar` lane in the
    /// retention-off subset — factored out so the commit gate can re-run them
    /// verbatim on the restored pre-splice proof when it reverts.
    fn run_post_eqdv_authority_tail(&mut self, proof: &mut Proof, extended_assertions: &[TermId]) {
        // #rewritten-assertion-bridge — the residual the promotion above
        // correctly declines: a REWRITTEN authored assertion, whose definiendum
        // is an AUTHORED symbol, so no freshness argument applies to it at all.
        // It is DERIVED instead, by congruence, from the authored assertions it
        // was rewritten from plus any CHECKED definition it now mentions. It
        // runs after the promotion so a `fresh_def_eq` step exists to cite.
        // Like the promotion it reasons purely over canonical `TermId`s and
        // needs no parse tree, and it grants no authority: every emitted step
        // is re-validated by the UNTOUCHED strict checker, and the lane reverts
        // the whole rewrite if the rebuilt proof does not check or loses a
        // certification the original had.
        self.derive_rewritten_assertions_by_congruence(proof, extended_assertions);
        // #rewritten-nonequality-bridge — the same repair for the rewritten
        // assertions whose goal is NOT a binary `=`, which the lane above
        // cannot take as a congruence-explanation conclusion. It runs after it
        // and never competes for a leaf it serves.
        self.derive_rewritten_nonequality_assertions(proof, extended_assertions);
        // #authored-conjunct-leaf — the residual BOTH bridges decline: a leaf
        // whose clause IS a nested `and`-conjunct of an authored assertion,
        // which is not a REWRITE of anything and so has no congruence to
        // explain. It is derived by `and_pos` from an `assume` of the authored
        // root. It runs last of the three so it never competes for a leaf a
        // bridge serves. See `proof/authored_conjunct_leaf`.
        self.derive_authored_conjunct_leaves(proof, extended_assertions);
        // #minted-definition-leaf — the LAST residual: a leaf that is an
        // authored assertion with a FRESH symbol substituted in, whose
        // definition the proof does not contain at all. The definition is
        // MINTED as a checked `fresh_def_eq` step, vetted by the checker's own
        // `FreshDefRegistry` over the FINISHED proof (Gate 2), which is why it
        // runs last of every derivation lane. See `proof/minted_definition_leaf`.
        self.derive_leaves_over_minted_definitions(proof, extended_assertions);
        // #conjunct-decomposition-leaf — the residual the lane above
        // cannot reach: an `and`-headed leaf that differs from its
        // authored root at a position UNDER a `not`, which
        // `ay_proof::congruence_forest` deliberately never descends. It is
        // derived CONJUNCT BY CONJUNCT instead, where `mk_eq`'s lifting
        // `(= (not x) (not y)) -> (= x y)` puts the differing position back
        // under an `App` head, and reassembled with one `and_neg`. It runs
        // after the whole-term lane and never competes for a leaf that one
        // serves. See `proof/conjunct_decomposition_leaf`.
        self.derive_conjunctwise_decomposed_leaves(proof, extended_assertions);
        // #ite-definition-leaf — the ITE-DEFINITION guard clauses
        // `name_non_bool_ites_all` appends over a fresh `__ay_ite_def_*`. Same
        // placement rule as the two lanes above and for the same reason: the
        // checker decides freshness against the FINISHED `assume` set. See
        // `proof/ite_definition_leaf`.
        self.derive_ite_definition_guard_leaves(proof, extended_assertions);
        self.rebuild_trust_leaf_proof_from_original_assertions(proof);
    }
}

include!("proof_rewrite/surface_planning.rs");

#[cfg(test)]
#[path = "proof_rewrite_tests.rs"]
mod proof_rewrite_tests;
