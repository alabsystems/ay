// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-verdict memoization for the authored-replacement cascade.
//!
//! The memo is scoped to one publication flow. A committed wholesale proof
//! replacement changes the fingerprint and invalidates it; final proof checks
//! and certificate minting remain unconditional correctness authorities.

use ay_core::Proof;

use super::bv_identity_promotion::GuardedCollapseStage;
use super::Executor;

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum RepairEntry {
    Check,
    CascadeKnownUnpublishable,
    NativeStrictWireGap,
}

impl Executor {
    /// A native proof is publishable only when its external spelling is known
    /// to preserve every theorem. A strict proof with a wire gap must continue
    /// through the authored replacement cascade.
    pub(super) fn authored_cascade_publishable(&mut self, proof: &Proof) -> bool {
        // #certify-before-presentation: a derivation whose document a
        // presentation bound withheld is not a publishable PRESENTATION, so
        // the authored replacements still get the chance to produce one —
        // exactly the chance they had when the bound installed the
        // unpublishable `(cl)` poison instead. Measured: without this, UF
        // `sledgehammer/TypeSafe/uf.1083624` kept its strict derivation and
        // lost the carcara-VALID authored document the cascade had built.
        if self.last_proof_surface_withheld.is_some() {
            return false;
        }
        !self.proof_has_known_wire_gap(proof)
            && self
                .check_proof_strict_with_datatypes(proof)
                .is_ok_and(|quality| quality.is_complete())
    }

    /// Whether `proof` renders, under the current presentation state, as a
    /// problem-scoped Alethe document with no `hole` or `trust` step.
    ///
    /// This is the document-level question the known-wire-gap screen answers
    /// conservatively. It is asked only to choose between two proofs the
    /// strict checker accepts; it never admits anything, and a refused,
    /// over-budget or stopped render counts as not clean. Asked from inside
    /// the solve, the render's complete bit-blast polls the solve's stop
    /// while it runs, and a lemma the decision's screen already declined is
    /// not lowered again
    /// (`ay_proof::try_export_alethe_with_authored_surfaces_within_solve`).
    pub(super) fn proof_renders_without_unproved_step(&self, proof: &Proof) -> bool {
        self.clean_render_len(proof).is_some()
    }

    /// The byte length of that clean render, or `None` when
    /// [`Self::proof_renders_without_unproved_step`] says no. Two certified
    /// derivations of one theorem are compared by it
    /// (`guarded/rederive.rs`).
    pub(super) fn clean_render_len(&self, proof: &Proof) -> Option<usize> {
        /// The largest render these choices pay for. A measured 32-bit
        /// multiplier conflict clause renders to 1.1 MB.
        const MAX_CHOICE_RENDER_WORK: u64 = 16 * 1024 * 1024;
        let scope = self.proof_export_scope_assertions_for(proof)?;
        let overrides = self.proof_export_term_overrides();
        let surfaces = self.authored_export_surfaces();
        let stop = self.make_proof_assembly_should_stop();
        let solve = ay_proof::AskingSolve {
            stop: &stop,
            declines: self.wire_gap_screen_declines(),
        };
        // In this executor's dialect, as the published document is: a
        // selector projection is `dt_project` only in the Clean dialect and
        // the hole in the pinned one.
        self.in_alethe_dialect(|| {
            ay_proof::try_export_alethe_with_authored_surfaces_within_solve(
                proof,
                &self.ctx.terms,
                &scope,
                overrides.as_ref(),
                surfaces.channels(),
                Some(MAX_CHOICE_RENDER_WORK),
                solve,
            )
        })
        .ok()
        .filter(|document| !document.contains(":rule hole") && !document.contains(":rule trust"))
        .map(|document| document.len())
    }

    /// Whether every presentation gate this publication applies passes
    /// `proof` with no unproved step: once it does, a wire-gap repair has
    /// nothing left to repair.
    ///
    /// Two gates judge an observable document, and this is their conjunction.
    /// The document gate (`ay`'s `strict_document_refusal` for either strict
    /// spelling, and every `(get-proof)` reader) reads the render, which is
    /// asked directly. The library strict gate,
    /// `decline_trust_bearing_unsat_under_strict_proofs`, runs only under
    /// `(set-option :check-proofs-strict true)` (`strict_proofs_enabled`; the
    /// `--strict-proofs` flag does not set it) and reads the known-wire-gap
    /// screen, not the render: there a screened gap withholds the UNSAT
    /// however cleanly the document renders, so a screened proof still has
    /// something to repair. Measured on
    /// `(assert (bvult x y)) (assert (bvult y x))` over 8-bit `x`, `y` with
    /// that option: judged by the render alone, the native multi-literal
    /// `BvBitBlast` conflict clause (which renders clean) was kept in place of
    /// the guarded joint collapse (whose single-literal lemma the screen
    /// admits), and `unsat` became `unknown (incomplete proof-trusted)`, as
    /// did nine `benchmarks/smt/QF_BV` puzzles.
    pub(super) fn proof_presents_without_unproved_step(&self, proof: &Proof) -> bool {
        (!self.strict_proofs_enabled() || !self.proof_has_known_wire_gap(proof))
            && self.proof_renders_without_unproved_step(proof)
    }

    /// The admission rule of every wire-gap repair candidate: it prints
    /// without an unproved step. The known-wire-gap screen admits first; it
    /// deliberately reports every multi-literal bit-blast lemma as a gap
    /// (`ay_proof::alethe_printer::complete_blast::clause` explains why), so
    /// when a document is observable a screened candidate is asked whether
    /// every presentation gate passes it instead
    /// (`proof_presents_without_unproved_step`; under `:check-proofs-strict`
    /// the screen is itself a gate, so there the screen alone decides). Only
    /// an observable document pays for that render.
    pub(super) fn wire_repair_candidate_prints_clean(&self, candidate: &Proof) -> bool {
        !self.proof_has_known_wire_gap(candidate)
            || (self.proof_document_observable()
                && self.proof_presents_without_unproved_step(candidate))
    }

    /// Proofs were requested, or a strict presentation is required.
    pub(super) fn proof_document_observable(&self) -> bool {
        self.is_producing_proofs() || self.strict_unsat_presentation_required()
    }

    /// The last wire-gap retry: trade a native-strict proof whose document
    /// still prints an unproved step for a refutation of the authored roots
    /// that prints none (`wire_repair_candidate_prints_clean`). The
    /// refutation comes from one of three sources, in order:
    ///
    /// - the authored roots re-interned RAW
    ///   (`repair_wire_gap_with_authored_bv_bitblast_refutation`): a pure
    ///   bit-vector root folded under a wire override prints as a hole over
    ///   the internal roots, and blasts exactly the surface it prints over the
    ///   raw ones;
    /// - the concrete authored roots
    ///   (`repair_wire_gap_with_exact_authored_bv_refutation`), where
    ///   elaboration already folded an authored read-over-write that the raw
    ///   lane, which declines array roots, cannot blast. Its bit-blast is paid
    ///   only for an observable document;
    /// - when neither bit-vector source replaced the incumbent, the raw-root
    ///   ground closure (`replace_with_raw_authored_ground_closure_refutation`),
    ///   which commits only a candidate whose published document has no
    ///   `hole` or `trust` step. The main cascade asks it only about a proof
    ///   the strict checker rejects, so without this retry a native-strict
    ///   proof never reaches it. Measured on a constant-array read the
    ///   propagation replay closes with the `ArrayRowChain` (E) lemma, which
    ///   pinned Carcara cannot spell, beside a guard universal the closure
    ///   instantiates (`group_proofs`, `carcara_external_check/
    ///   ground_closure.rs`): the (E) `hole` was published in place of the
    ///   closure's Carcara-`valid` refutation.
    ///
    /// An observable incumbent that every presentation gate already passes
    /// (`proof_presents_without_unproved_step`) has nothing to repair and is
    /// kept: the screen that routed it here is conservative, and any of these
    /// would only trade one clean document for another (or, for a
    /// guarded-collapse lemma over an authored array read, for a `hole`; see
    /// `guarded_repair_worth_checking`). Under `:check-proofs-strict` the
    /// screen is itself a gate, so a screened incumbent is never kept here.
    fn repair_wire_gap_with_authored_root_refutation(&mut self, proof: &mut Proof) {
        let observable = self.proof_document_observable();
        if observable && self.proof_presents_without_unproved_step(proof) {
            return;
        }
        if self.repair_wire_gap_with_authored_bv_bitblast_refutation(proof) || !observable {
            return;
        }
        let incumbent = Self::strict_verdict_memo_fingerprint(proof);
        self.repair_wire_gap_with_exact_authored_bv_refutation(proof);
        if Self::strict_verdict_memo_fingerprint(proof) == incumbent {
            self.replace_with_raw_authored_ground_closure_refutation(proof);
        }
    }

    /// Give a native-strict proof with an external wire gap only the generic
    /// retries that can change it, in their established cascade order.
    ///
    /// Every other cascade member deliberately returns immediately when the
    /// native checker already accepts the proof. Running through all of them
    /// therefore only repeats the same expensive strict check. Each generic
    /// repair runs only while the actual wire gap survives. Once the bounded
    /// attempts finish, the ordinary publication funnel accepts the resulting
    /// presentation or fails closed. Artifact-shaped repairs run before this
    /// strict-native classification in `run_authored_replacement_cascade`.
    ///
    /// A bit-vector or ground-closure refutation of the authored roots goes
    /// last (`repair_wire_gap_with_authored_root_refutation`).
    fn retry_native_strict_wire_gap(&mut self, proof: &mut Proof) -> bool {
        if !self.proof_has_known_wire_gap(proof)
            || !self
                .check_proof_strict_with_datatypes(proof)
                .is_ok_and(|quality| quality.is_complete())
        {
            return false;
        }
        // This existing classification already established a complete proof
        // with an external wire gap. Try the shared native source producer
        // before the historical raw-root fallbacks and early return below.
        if self.replace_with_native_source_quantifier_refutation(proof)
            && !self.proof_has_known_wire_gap(proof)
        {
            return true;
        }
        self.replace_with_exact_authored_conjunct_refutation(
            proof,
            RepairEntry::NativeStrictWireGap,
        );
        if self.proof_has_known_wire_gap(proof) {
            self.replace_with_exact_authored_poly_refutation(
                proof,
                RepairEntry::NativeStrictWireGap,
            );
        }
        if self.proof_has_known_wire_gap(proof) {
            self.replace_with_exact_authored_equality_chain_refutation(
                proof,
                RepairEntry::NativeStrictWireGap,
            );
        }
        if self.proof_has_known_wire_gap(proof) {
            self.replace_with_exact_authored_divisibility_refutation(
                proof,
                RepairEntry::NativeStrictWireGap,
            );
        }
        if self.proof_has_known_wire_gap(proof) {
            self.repair_wire_gap_with_authored_root_refutation(proof);
        }
        true
    }

    /// The artifact-shaped repairs that must see a native-strict proof
    /// before the publishable fast path classifies it. A datatype proof over
    /// frontend field constants can likewise be native-strict complete while
    /// its assumes have no authored surface; the datatype planner's own decl
    /// gate keeps non-datatype proofs free.
    fn run_authored_artifact_prepass(&mut self, proof: &mut Proof) {
        self.promote_bv_guarded_collapse(proof, GuardedCollapseStage::Cascade);
        self.replace_with_exact_authored_bv_high_zero_refutation(proof);
        self.replace_with_exact_authored_negated_conjunct_bridge(proof);
        self.replace_with_exact_authored_datatype_refutation(proof);
        self.replace_with_authored_skeleton_refutation(proof);
    }

    /// Run every authored replacement while reusing verdicts for unchanged proofs.
    ///
    /// The three artifact-shaped repairs run first. These historical replay
    /// shapes can arrive as native-strict proofs whose only defect is their
    /// Alethe spelling. Run their exact, independently checked planners before
    /// classifying that native proof; the generic retry fast path otherwise
    /// returns before the ordinary cascade reaches either artifact-shaped
    /// member. They depend only on the immutable authored/raw scope, so the two
    /// authored refutations run only here: retrying later cannot expose a new
    /// source shape and would merely reset their proof-wide resource budgets.
    /// The guarded collapse runs again at the final boundary, where it
    /// re-purges the presentation of what it installed and may rescue a
    /// rejected proof.
    pub(super) fn run_authored_replacement_cascade(&mut self, proof: &mut Proof) {
        self.run_authored_artifact_prepass(proof);
        if self.retry_native_strict_wire_gap(proof) {
            return;
        }
        let mut strict_verdict = Some(self.authored_cascade_publishable(proof));
        let mut fingerprint = Self::strict_verdict_memo_fingerprint(proof);
        macro_rules! strict_gated_cascade_member {
            ($member:ident $(, $extra:expr)?) => {{
                if self.proof_assembly_stop_requested() {
                    return;
                }
                let verdict = match strict_verdict {
                    Some(verdict) => verdict,
                    None => {
                        let verdict = self.authored_cascade_publishable(proof);
                        strict_verdict = Some(verdict);
                        verdict
                    }
                };
                if !verdict {
                    self.$member(proof $(, $extra)?);
                    let next = Self::strict_verdict_memo_fingerprint(proof);
                    if next != fingerprint {
                        fingerprint = next;
                        if self.retry_native_strict_wire_gap(proof) {
                            return;
                        }
                        strict_verdict = None;
                    }
                }
            }};
        }
        strict_gated_cascade_member!(replace_with_native_source_quantifier_refutation);
        strict_gated_cascade_member!(
            replace_with_exact_authored_conjunct_refutation,
            RepairEntry::Check
        );
        strict_gated_cascade_member!(replace_with_exact_authored_string_length_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_datatype_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_order_ite_refutation);
        strict_gated_cascade_member!(
            replace_with_exact_authored_poly_refutation,
            RepairEntry::CascadeKnownUnpublishable
        );
        strict_gated_cascade_member!(
            replace_with_exact_authored_equality_chain_refutation,
            RepairEntry::Check
        );
        strict_gated_cascade_member!(replace_with_exact_authored_guarded_linear_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_linear_refutation);
        strict_gated_cascade_member!(
            replace_with_exact_authored_divisibility_refutation,
            RepairEntry::Check
        );
        strict_gated_cascade_member!(replace_with_exact_authored_affine_euf_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_bv_refutation);
        // The same bit-blast refutation over the authored roots RE-INTERNED
        // RAW (`authored_bv_bitblast_refutation`): where the internal roots
        // were folded under a wire override — a definitional `bvsdiv` query's
        // constant sign tests — the printer can only blast the surface it
        // prints, and refuses the folded term.
        strict_gated_cascade_member!(replace_with_exact_authored_bv_bitblast_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_store_permutation_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_array_row_value_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_congruence_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_string_length_arith_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_ground_substitution_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_word_identity_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_negated_exists_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_nested_forall_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_forall_inst_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_forall_inst_equality_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_forall_inst_conflict_refutation);
        strict_gated_cascade_member!(
            replace_with_exact_authored_witnessed_forall_conflict_refutation
        );
        strict_gated_cascade_member!(replace_with_exact_authored_congruence_value_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_activated_equality_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_equality_closure_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_collection_subset_refutation);
        // Closed FP roots need neither a quantified instance nor a probe.
        // The bounded independent evaluator supplies the checked negation.
        strict_gated_cascade_member!(replace_with_closed_authored_fp_refutation);
        // The consequence-replay member runs a bounded same-context probe
        // solve (#consequence-replay); it runs after every cheap authored
        // shape, requires at least one recorded `forall_inst` instance, and
        // consumes one of the per-check-sat replay attempts.
        strict_gated_cascade_member!(replace_with_authored_consequence_replay_refutation);
        strict_gated_cascade_member!(collapse_double_negated_trust_lemma_literals);
        // After every repair above (none of their proofs moves); wire-clean only.
        strict_gated_cascade_member!(replace_with_authored_instance_closure_refutation);
        // The general raw-root fallback, before the hole-wired member below.
        strict_gated_cascade_member!(replace_with_raw_authored_ground_closure_refutation);
        // This exact internal proof uses `qnt_neg_exists`, whose external wire
        // spelling is deliberately `hole`. Run it only after every wire-clean
        // authored alternative so it cannot preempt a publishable certificate.
        strict_gated_cascade_member!(
            replace_with_exact_authored_negated_exists_forall_inst_refutation
        );
        let _ = (strict_verdict, fingerprint);
    }

    /// Fingerprint wholesale proof replacement without serving as authority.
    fn strict_verdict_memo_fingerprint(proof: &Proof) -> (usize, usize, usize) {
        (
            proof.steps.as_ptr() as usize,
            proof.steps.len(),
            proof.named_steps.len(),
        )
    }
}
