// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Strict-verdict memoization for the authored-replacement cascade.
//!
//! The memo is scoped to one publication flow. A committed wholesale proof
//! replacement changes the fingerprint and invalidates it; final proof checks
//! and certificate minting remain unconditional correctness authorities.

use ay_core::Proof;

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
        !self.proof_has_known_wire_gap(proof)
            && self
                .check_proof_strict_with_datatypes(proof)
                .is_ok_and(|quality| quality.is_complete())
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
    fn retry_native_strict_wire_gap(&mut self, proof: &mut Proof) -> bool {
        if !self.proof_has_known_wire_gap(proof)
            || !self
                .check_proof_strict_with_datatypes(proof)
                .is_ok_and(|quality| quality.is_complete())
        {
            return false;
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
        true
    }

    /// Run every authored replacement while reusing verdicts for unchanged proofs.
    pub(super) fn run_authored_replacement_cascade(&mut self, proof: &mut Proof) {
        // These two historical replay shapes can arrive as native-strict
        // proofs whose only defect is their Alethe spelling. Run their exact,
        // independently checked planners before classifying that native proof;
        // the generic retry fast path otherwise returns before the ordinary
        // cascade reaches either artifact-shaped member. Both planners depend
        // only on the immutable authored/raw scope, so this is also their sole
        // invocation: retrying later cannot expose a new source shape and would
        // merely reset their proof-wide resource budgets.
        self.replace_with_exact_authored_bv_high_zero_refutation(proof);
        self.replace_with_exact_authored_negated_conjunct_bridge(proof);
        if self.retry_native_strict_wire_gap(proof) {
            return;
        }
        let mut strict_verdict = Some(self.authored_cascade_publishable(proof));
        let mut fingerprint = Self::strict_verdict_memo_fingerprint(proof);
        macro_rules! strict_gated_cascade_member {
            ($member:ident $(, $extra:expr)?) => {{
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
        strict_gated_cascade_member!(replace_with_exact_authored_equality_closure_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_collection_subset_refutation);
        // The consequence-replay member runs a bounded same-context probe
        // solve (#consequence-replay); it runs after every cheap authored
        // shape, requires at least one recorded `forall_inst` instance, and
        // consumes one of the per-check-sat replay attempts.
        strict_gated_cascade_member!(replace_with_authored_consequence_replay_refutation);
        strict_gated_cascade_member!(collapse_double_negated_trust_lemma_literals);
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
