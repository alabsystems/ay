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

impl Executor {
    /// Run every authored replacement while reusing verdicts for unchanged proofs.
    pub(super) fn run_authored_replacement_cascade(&mut self, proof: &mut Proof) {
        let mut strict_verdict = Some(self.check_proof_strict_with_datatypes(proof).is_ok());
        let mut fingerprint = Self::strict_verdict_memo_fingerprint(proof);
        macro_rules! strict_gated_cascade_member {
            ($member:ident) => {{
                let verdict = match strict_verdict {
                    Some(verdict) => verdict,
                    None => {
                        let verdict = self.check_proof_strict_with_datatypes(proof).is_ok();
                        strict_verdict = Some(verdict);
                        verdict
                    }
                };
                if !verdict {
                    self.$member(proof);
                    let next = Self::strict_verdict_memo_fingerprint(proof);
                    if next != fingerprint {
                        fingerprint = next;
                        strict_verdict = None;
                    }
                }
            }};
        }
        strict_gated_cascade_member!(replace_with_exact_authored_conjunct_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_string_length_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_datatype_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_order_ite_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_equality_chain_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_guarded_linear_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_linear_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_divisibility_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_affine_euf_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_bv_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_store_permutation_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_array_row_value_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_congruence_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_string_length_arith_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_ground_substitution_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_word_identity_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_forall_inst_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_forall_inst_equality_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_forall_inst_conflict_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_congruence_value_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_equality_closure_refutation);
        strict_gated_cascade_member!(replace_with_exact_authored_collection_subset_refutation);
        strict_gated_cascade_member!(collapse_double_negated_trust_lemma_literals);
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
