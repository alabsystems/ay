// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof checking, validation, and quality measurement.
//!
//! Contains the internal proof checker integration, proof quality metrics,
//! and proof predicate helpers (derives_empty_clause, etc.).
//!
//! Extracted from `proof.rs` for code health (#5970).

use ay_core::TermStore;
use ay_core::{AletheRule, Proof, ProofStep};
#[cfg(feature = "proof-checker")]
use ay_proof::{check_proof_partial, PartialProofCheck};
use ay_proof::{ProofCheckError, ProofQuality};

use super::super::Executor;

#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_FAILURES_KEY: &str = "proof_checker_failures";
#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY: &str = "proof_checker_skipped_hole_steps";
#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_CHECKED_STEPS_KEY: &str = "proof_checker_checked_steps";
#[cfg(feature = "proof-checker")]
pub(super) const PROOF_CHECKER_TOTAL_STEPS_KEY: &str = "proof_checker_total_steps";

impl Executor {
    /// Populate statistics extra map with proof quality metrics.
    pub(super) fn populate_proof_quality_stats(&mut self, quality: &ProofQuality) {
        use crate::executor_types::StatValue;
        let extra = &mut self.last_statistics.extra;
        extra.insert(
            "proof_steps".to_string(),
            StatValue::Int(u64::from(quality.total_steps)),
        );
        extra.insert(
            "proof_verified".to_string(),
            StatValue::Int(u64::from(quality.verified_count())),
        );
        extra.insert(
            "proof_trust".to_string(),
            StatValue::Int(u64::from(quality.trust_count)),
        );
        extra.insert(
            "proof_complete".to_string(),
            StatValue::String(if quality.is_complete() {
                "true".to_string()
            } else {
                "false".to_string()
            }),
        );
    }

    /// Datatype constructor registry for strict proof validation:
    /// `(datatype_name, [constructor_name, ..])` from the elaboration context.
    ///
    /// Runtime datatype terms carry `Sort::Uninterpreted`, so the proof checker
    /// cannot recover constructor membership from the `TermStore` alone — it is
    /// supplied here, where the `declare-datatype` declarations are known.
    fn datatype_decls_for_strict_proof(&self) -> Vec<(String, Vec<String>)> {
        self.ctx
            .datatype_iter()
            .map(|(name, ctors)| (name.to_string(), ctors.to_vec()))
            .collect()
    }

    /// Emit verified-firewall Lean proofs — one per theory lemma in `proof` that
    /// a per-theory emitter supports — grounding each in the verified
    /// `AySoundness.firewall_combined_unsat` theorem (half (1) of the
    /// formal-verification goal).
    ///
    /// Supported so far: datatype constructor-distinctness (`dt_distinct`) and
    /// linear-arithmetic conflicts (`la_generic` / `lia_generic`, all-negated
    /// comparison lemmas). Each returned string is a self-contained Lean 4 file
    /// that imports the verified `AySoundness` theorems and kernel-checks (axioms
    /// ⊆ {propext, Classical.choice, Quot.sound}); see `lean_firewall.rs` and the
    /// `AySoundness.CombinedDatatype` proof-of-concept. This is the runtime
    /// counterpart that automatically emits the import-the-verified-theorem shape
    /// instead of a hand-written instance.
    pub fn emit_datatype_firewall_lean(&self, proof: &Proof) -> Vec<String> {
        use ay_core::TheoryLemmaKind as K;
        let decls = self.datatype_decls_for_strict_proof();
        let mut out: Vec<String> = proof
            .steps
            .iter()
            .filter_map(|step| {
                let ProofStep::TheoryLemma { kind, clause, .. } = step else {
                    return None;
                };
                match kind {
                    K::DatatypeDistinct if !decls.is_empty() => {
                        crate::executor::lean_firewall::emit_datatype_distinct_firewall_lean(
                            &self.ctx.terms,
                            &decls,
                            clause,
                        )
                    }
                    K::LraFarkas | K::LiaGeneric => {
                        // Farkas / bound conflicts go through the LIA emitter; a
                        // single-variable LINEAR IDENTITY (e.g. `(* x 0) = 0`,
                        // the `LinearIdentity` annotation) is a different shape —
                        // the LIA emitter declines it, so fall through to the
                        // identity emitter.
                        crate::executor::lean_firewall::emit_lia_firewall_lean(
                            &self.ctx.terms,
                            clause,
                        )
                        .or_else(|| {
                            crate::executor::lean_firewall::emit_nia_identity_firewall_lean(
                                &self.ctx.terms,
                                clause,
                            )
                        })
                    }
                    K::EufTransitive => crate::executor::lean_firewall::emit_euf_firewall_lean(
                        &self.ctx.terms,
                        clause,
                    ),
                    K::EufCongruent => {
                        crate::executor::lean_firewall::emit_euf_congruence_firewall_lean(
                            &self.ctx.terms,
                            clause,
                        )
                    }
                    K::EufCongruentPred => {
                        crate::executor::lean_firewall::emit_euf_pred_congruence_firewall_lean(
                            &self.ctx.terms,
                            clause,
                        )
                    }
                    // Array read-over-write-NEG: the proof carries the
                    // self-contained guarded theorem
                    // `(i = j) ∨ (= (select (store a i v) j) (select a j))`.
                    // The emitter independently recognizes that exact clause
                    // and grounds the generic ROW2 theorem (a/i/j/v modeled as
                    // opaque components). Guard-less contextual units are
                    // declined.
                    K::ArraySelectStore { index_eq: false } => {
                        crate::executor::lean_firewall::emit_array_row2_firewall_lean(
                            &self.ctx.terms,
                            clause,
                        )
                    }
                    // If-then-else identical branches `(= (ite c x x) x)`: holds
                    // for any condition and any branch sort; ground via `ite_self`
                    // over `Val = branch_sort × Bool`.
                    K::IteSame => crate::executor::lean_firewall::emit_ite_same_firewall_lean(
                        &self.ctx.terms,
                        clause,
                    ),
                    // FP sign-bit identities (`fp.abs` idempotence / `fp.neg`
                    // involution). Classification EXCLUSIVITY is a different shape
                    // handled by the from-parsed FP emitter below — this declines
                    // it (returns None), so the two are complementary.
                    K::FpClassification { .. } => {
                        crate::executor::lean_firewall::emit_fp_identity_firewall_lean(
                            &self.ctx.terms,
                            clause,
                        )
                    }
                    // Small-width BV IDENTITY lemma `(= L R)` over BV variables
                    // (e.g. `(= (bvand x x) x)`) — refuted by `decide` over the
                    // `BitVec w` model (width from the variable's sort).
                    K::BvBitBlast => {
                        crate::executor::lean_firewall::emit_bv_identity_firewall_lean(
                            &self.ctx.terms,
                            clause,
                        )
                    }
                    // Datatype selector projection `(= (sel_i (C f0 f1)) f_i)`:
                    // model the datatype as a product, the selector as `.1`/`.2`.
                    K::DatatypeSelectorProject => {
                        crate::executor::lean_firewall::emit_dt_selector_projection_firewall_lean(
                            &self.ctx.terms,
                            clause,
                        )
                    }
                    // Remaining: array ROW-same (bare-trust reconstruction),
                    // strings/BV/FP (surface-rewrite-trivialized / non-tautology
                    // lemmas) — need lemma reconstruction first. See memory
                    // `project_formally_verifying_ay`.
                    _ => None,
                }
            })
            .collect();

        // String length-vs-literal conflicts: ay's lemma AND the TermId-level
        // assertions are surface-rewrite-trivialized before emit, so reconstruct
        // from the FRONTEND parsed assertions (where the `s = L` / `str.len s = K`
        // structure survives). Appended separately — not driven by a per-step
        // theory-lemma kind.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_string_length_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Sequence length-over-concat conflicts: `seq.len (seq.++ X Y) =
        // seq.len X + seq.len Y + K` (K>0) is unsatisfiable by the verified
        // `SeqThy.len_concat` axiom. ay reduces seq.len/seq.++ eagerly (bare
        // trust), so reconstruct from the frontend assertions and ground the
        // sequence length-additivity axiom over `Val = Seq Int × Seq Int`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_seq_len_concat_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // String length-over-concat conflicts: `str.len (str.++ X Y) =
        // str.len X + str.len Y + K` (K>0) is unsatisfiable by the verified
        // `StringThy.len_cat` axiom. ay reduces str.len/str.++ eagerly (bare
        // trust), so reconstruct from the frontend assertions and ground the
        // string length-additivity axiom over `Val = StringThy.Str × StringThy.Str`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_str_len_concat_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // String empty-length conflicts: `str.len s = 0 ∧ s ≠ ""` is
        // unsatisfiable by the verified `StringThy.len_zero_iff` axiom
        // (`len s = 0 ↔ s = ε`). ay reduces str.len eagerly (bare trust), so
        // reconstruct from the frontend assertions and ground the empty-string
        // characterization over `Val = StringThy.Str`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_str_len_zero_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Small-width bit-vector conflicts: ay bit-blasts BV eagerly (bare-trust
        // refutation), so reconstruct from the frontend assertions and refute the
        // conjunction directly by curried `decide` over a `BitVec w` model.
        if let Some(lean) = crate::executor::lean_firewall::emit_bv_firewall_lean_from_parsed(
            self.ctx.assertions_parsed(),
        ) {
            out.push(lean);
        }

        // Propositional contradictions (e.g. `(not (= (not (not p)) p))`,
        // `(= p (not p))`): ay refutes the Boolean conflict eagerly (bare-trust);
        // reconstruct from the frontend assertions and refute by `decide` over a
        // `Bool` model.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_bool_tautology_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Array read-over-write-same: `select (store a i v) i ≠ v` is bare-trust
        // (ay refutes arrays eagerly); reconstruct from the frontend assertions
        // and ground the generic McCarthy ROW-same theorem.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_array_row1_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Floating-point classification conflict: a float in two mutually-exclusive
        // IEEE classes (e.g. `(fp.isInfinite x) ∧ (fp.isNaN x)`) is UNSAT. ay reduces
        // FP to bit-vectors and refutes eagerly (bare-trust), so reconstruct from the
        // frontend assertions and ground the verified `FpThy` exclusivity partition.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_fp_classification_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Set subset ground-witness refutation: ay decides set.subset via member
        // saturation (no proof-step theory lemma), so reconstruct from the
        // frontend assertions `(set.member x s) (not (set.member x t))
        // (set.subset s t)` and ground the subset-definition-at-witness lemma.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_set_subset_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Set subset transitivity `(set.subset A B) (set.subset B C)
        // (not (set.subset A C))`: the certificate grounds ⊆-transitivity
        // directly (no Skolemization — unlike the Alethe proof).
        if let Some(lean) =
            crate::executor::lean_firewall::emit_set_subset_transitivity_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Datatype selector congruence: ay's QF_DT pipeline refutes eagerly and
        // folds the term structure away (bare `(cl …) :rule trust`), so
        // reconstruct from the frontend assertions `(= (sel A) v) (= A B)
        // (not (= (sel B) v))` and ground the selector-congruence lemma.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_dt_selector_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // Datatype constructor injectivity: `(= (C a …) (C c …)) (not (= a c))`
        // over a genuine constructor `C`. Sound only for real constructors
        // (injectivity is their datatype-theory axiom), so pass the constructor
        // names from the datatype registry.
        if !decls.is_empty() {
            let ctor_names: Vec<String> = decls
                .iter()
                .flat_map(|(_, ctors)| ctors.iter().cloned())
                .collect();
            if let Some(lean) =
                crate::executor::lean_firewall::emit_dt_injective_firewall_lean_from_parsed(
                    self.ctx.assertions_parsed(),
                    &ctor_names,
                )
            {
                out.push(lean);
            }
        }

        // EUF congruence over a transitive chain: `(= x m) (= m y)
        // (not (= (f x) (f y)))`. The executor's trust-split produces
        // eq_transitive/eq_congruent STEPS (not theory-lemma kinds), so the
        // proof-step dispatch above emits nothing for it; reconstruct from the
        // frontend assertions and ground the fused congruence-over-transitivity
        // lemma.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_euf_cong_trans_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // NIA conflict that becomes a single linear equality after substituting
        // constant-pinned variables (e.g. `(* x y)=7 ∧ x=2` ⟶ `2*y=7`): ay
        // treats it as nonlinear bare-trust; reconstruct from the frontend and
        // ground the linear conflict by `omega`.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_nia_linear_firewall_lean_from_parsed(
                self.ctx.assertions_parsed(),
            )
        {
            out.push(lean);
        }

        // GENERAL whole-DAG firewall: ground the ENTIRE refutation (all `Assume`
        // inputs + all arithmetic/equality `TheoryLemma`s + the resolution DAG)
        // as a SINGLE certificate over one shared `Nat → Int` model — the
        // Nelson–Oppen composition shape generalised from `CombinedExample`.
        // Complementary to the per-lemma emitters above (which ground each lemma
        // in isolation); only fires for fully-renderable arithmetic/equality
        // proofs, declining otherwise.
        if let Some(lean) =
            crate::executor::lean_firewall::emit_general_firewall_lean(&self.ctx.terms, proof)
        {
            out.push(lean);
        }
        out
    }

    /// Strict proof check that also validates datatype constructor-distinctness
    /// lemmas (#8419 / trust_count→0).
    ///
    /// `DatatypeDistinct` steps (promoted from `Generic` at proof finalization
    /// by `promote_datatype_distinct_lemmas`) cannot be validated from the
    /// `TermStore` alone — runtime datatype terms carry `Sort::Uninterpreted`.
    /// This supplies the `declare-datatype` registry so the strict checker can
    /// semantically validate them against the actual constructor declarations
    /// instead of failing closed.
    pub(super) fn check_proof_strict_with_datatypes(
        &self,
        proof: &Proof,
    ) -> Result<ProofQuality, ProofCheckError> {
        let decls = self.datatype_decls_for_strict_proof();
        let selectors = self.ctor_selector_decls_for_strict_proof();
        if decls.is_empty() && selectors.is_empty() {
            return ay_proof::check_proof_strict(proof, &self.ctx.terms);
        }
        ay_proof::check_proof_strict_with_datatypes_and_selectors(
            proof,
            &self.ctx.terms,
            Some(&decls),
            Some(&selectors),
        )
    }

    /// Constructor→selector registry for strict proof validation:
    /// `(constructor_name, [selector_name in field order])` from the elaboration
    /// context. Like the distinctness registry, the field positions cannot be
    /// recovered from the `TermStore` (datatype terms carry `Sort::Uninterpreted`),
    /// so they are supplied here for `DatatypeSelectorProject` validation.
    fn ctor_selector_decls_for_strict_proof(&self) -> Vec<(String, Vec<String>)> {
        self.ctx
            .ctor_selectors_iter()
            .map(|(ctor, selectors)| (ctor.clone(), selectors.clone()))
            .collect()
    }

    /// Validate proof and collect quality metrics.
    ///
    /// In debug builds, runs the full proof checker (rejects invalid proofs via
    /// warning). In all builds, collects [`ProofQuality`] step-type counts for
    /// diagnostic reporting via `(get-info :all-statistics)`.
    pub(super) fn validate_and_measure_proof(&self, proof: &Proof) -> Option<ProofQuality> {
        let has_hole = proof.steps.iter().any(|s| {
            matches!(
                s,
                ProofStep::Step {
                    rule: AletheRule::Hole,
                    ..
                }
            )
        });
        if has_hole {
            return None;
        }

        // Use strict checker when enabled (#4420).
        let result = if self.strict_proofs_enabled() {
            self.check_proof_strict_with_datatypes(proof)
        } else {
            ay_proof::check_proof_with_quality(proof, &self.ctx.terms)
        };

        match result {
            Ok(quality) => {
                tracing::debug!(
                    %quality,
                    complete = quality.is_complete(),
                    "UNSAT proof quality"
                );
                if !quality.is_complete() {
                    tracing::warn!(
                        trust = quality.trust_count,
                        hole = quality.hole_count,
                        total = quality.total_steps,
                        "UNSAT proof has unverified fallback steps"
                    );
                }
                Some(quality)
            }
            Err(e) => {
                tracing::warn!(
                    error = %e,
                    steps = proof.len(),
                    "internal proof checker rejected UNSAT proof"
                );
                None
            }
        }
    }

    pub(crate) fn proof_derives_empty_clause(proof: &Proof) -> bool {
        proof.steps.iter().any(|step| match step {
            ProofStep::Step { clause, .. } | ProofStep::Resolution { clause, .. } => {
                clause.is_empty()
            }
            _ => false,
        })
    }

    /// Check that the proof derives empty clause AND the resolution chain is
    /// valid (each ThResolution step's conclusion matches its premises).
    pub(super) fn proof_derives_valid_empty_clause(terms: &TermStore, proof: &Proof) -> bool {
        if !Self::proof_derives_empty_clause(proof) {
            return false;
        }
        // Quick check: run the partial checker. If it finds no errors, the
        // chain is valid.
        #[cfg(feature = "proof-checker")]
        {
            let (_, error) = check_proof_partial(proof, terms);
            error.is_none()
        }
        #[cfg(not(feature = "proof-checker"))]
        {
            let _ = terms;
            true
        }
    }

    #[cfg(feature = "proof-checker")]
    pub(super) fn run_internal_proof_check(&mut self, proof: &Proof) {
        // Strict mode (#4420): when enabled, reject trust and hole steps.
        // This gates on the SMT-LIB option `(set-option :check-proofs-strict true)`.
        if self.strict_proofs_enabled() {
            match self.check_proof_strict_with_datatypes(proof) {
                Ok(_quality) => {
                    let shape = Self::proof_shape_summary(proof);
                    self.proof_check_result = Some(PartialProofCheck {
                        checked_steps: shape.total_steps,
                        skipped_hole_steps: 0,
                        total_steps: shape.total_steps,
                    });
                    self.record_proof_check_stats(0, Self::proof_shape_summary(proof));
                }
                Err(error) => {
                    let shape = Self::proof_shape_summary(proof);
                    let checked = shape.checked_steps;
                    let skipped = shape.skipped_hole_steps;
                    let total = shape.total_steps;
                    self.proof_check_result = Some(shape.clone());
                    self.record_proof_check_stats(1, shape);
                    tracing::error!(
                        error = %error,
                        checked_steps = checked,
                        skipped_hole_steps = skipped,
                        total_steps = total,
                        "strict proof checker rejected UNSAT proof"
                    );
                }
            }
            return;
        }

        let (summary, error) = check_proof_partial(proof, &self.ctx.terms);
        self.proof_check_result = Some(summary.clone());
        if let Some(error) = error {
            let shape = Self::proof_shape_summary(proof);
            let checked = shape.checked_steps;
            let skipped = shape.skipped_hole_steps;
            let total = shape.total_steps;
            self.record_proof_check_stats(1, shape);

            tracing::error!(
                error = %error,
                checked_steps = checked,
                skipped_hole_steps = skipped,
                total_steps = total,
                "internal proof checker rejected UNSAT proof"
            );
        } else {
            self.record_proof_check_stats(0, summary);
        }
    }

    /// Whether the last UNSAT was backed by a refutation proof that AY's own
    /// internal checker fully verified: the checker reported no errors
    /// (`proof_check_ok`), the proof has at least one step, and no step is a
    /// trust/`Hole` placeholder (`skipped_hole_steps == 0`). This is the
    /// certification `--self-check` requires before emitting `unsat`.
    ///
    /// When the `proof-checker` feature is compiled out there is no internal
    /// checker to certify with, so this conservatively returns `false` (every
    /// UNSAT degrades to `unknown` under self-check).
    pub(in crate::executor) fn unsat_proof_self_certified(&self) -> bool {
        #[cfg(feature = "proof-checker")]
        {
            let Some(proof) = self.last_proof.as_ref() else {
                return false;
            };
            // Every step must be a real, checked derivation: no `Hole`
            // placeholders and no `Trust` steps (a Trust step means "believe the
            // solver, no derivation" — exactly what self-certification must
            // reject; e.g. the LIA `not-exists` residue wrong-UNSAT emits a
            // single Trust step). Assume steps are fine (problem hypotheses).
            //
            // A `TheoryLemma` whose `kind.is_trust()` (i.e. `Generic`) is ALSO
            // an untrusted step: the Alethe printer renders it as `:rule trust`
            // (alethe_printer.rs), so it is a certificate-free "believe the
            // solver" claim exactly like `Step{Trust}`. The original check
            // missed it, so `--self-check` emitted a bare `unsat` alongside a
            // carcara-INVALID `:rule trust` proof — a direct violation of the
            // "only emit what AY can verify itself" contract (#selfcert-leak).
            let has_untrusted_step = proof.steps.iter().any(|s| {
                matches!(
                    s,
                    ProofStep::Step {
                        rule: AletheRule::Hole,
                        ..
                    } | ProofStep::Step {
                        rule: AletheRule::Trust,
                        ..
                    }
                ) || matches!(
                    s,
                    ProofStep::TheoryLemma { kind, .. } if kind.is_trust()
                )
            });
            if has_untrusted_step {
                return false;
            }
            // Leak-2: an `assume` on the empty-clause path whose term is not
            // backed by the problem's provenance (not an original asserted
            // formula, and not a quantifier instantiation tracing back to an
            // asserted `forall`) is a laundered free axiom — an external
            // checker accepts it blindly, so it is exactly as unverified as a
            // `trust` step. Reject it so `--self-check` degrades to `unknown`
            // instead of emitting a bare `unsat` alongside an uncheckable
            // proof (e.g. an injected `seq.len` identity assumed as `true`).
            if self.unsat_proof_terminal_foreign_assume() {
                return false;
            }
            // TIER-0 leak: a proof referencing sequence-theory content
            // (`Seq`-sorted terms) is not independently checkable — carcara
            // rejects the `Seq` sort, no firewall-Lean lemma covers sequences,
            // and there is no DRAT lane. A clean `la_generic`/`resolution`
            // refutation over `seq.nth` terms (zero hole/trust, no foreign
            // assume) would otherwise self-certify and ship a bare `unsat`
            // alongside a proof no external checker can confirm. Degrade to
            // `unknown` instead.
            if self.unsat_proof_references_uncheckable_seq_theory() {
                return false;
            }
            // The internal checker accepted it AND it genuinely derives the
            // empty clause (false) from the assumptions.
            self.proof_check_ok
                && self
                    .proof_check_result
                    .as_ref()
                    .is_some_and(|c| c.total_steps > 0)
                && Self::proof_derives_valid_empty_clause(&self.ctx.terms, proof)
        }
        #[cfg(not(feature = "proof-checker"))]
        {
            false
        }
    }

    #[cfg(feature = "proof-checker")]
    fn proof_shape_summary(proof: &Proof) -> PartialProofCheck {
        let total_steps = proof.steps.len() as u32;
        let skipped_hole_steps = proof
            .steps
            .iter()
            .filter(|step| {
                matches!(
                    step,
                    ProofStep::Step {
                        rule: AletheRule::Hole,
                        ..
                    }
                )
            })
            .count() as u32;

        PartialProofCheck {
            checked_steps: total_steps.saturating_sub(skipped_hole_steps),
            skipped_hole_steps,
            total_steps,
        }
    }

    #[cfg(feature = "proof-checker")]
    fn record_proof_check_stats(&mut self, failures: u64, summary: PartialProofCheck) {
        // Record whether the internal checker accepted the refutation with no
        // errors. `--self-check` consults this (plus hole-freeness) before it
        // will emit `unsat` rather than a sound `unknown`.
        self.proof_check_ok = failures == 0;
        self.last_statistics
            .set_int(PROOF_CHECKER_FAILURES_KEY, failures);
        self.last_statistics.set_int(
            PROOF_CHECKER_SKIPPED_HOLE_STEPS_KEY,
            u64::from(summary.skipped_hole_steps),
        );
        self.last_statistics.set_int(
            PROOF_CHECKER_CHECKED_STEPS_KEY,
            u64::from(summary.checked_steps),
        );
        self.last_statistics.set_int(
            PROOF_CHECKER_TOTAL_STEPS_KEY,
            u64::from(summary.total_steps),
        );
    }
}
