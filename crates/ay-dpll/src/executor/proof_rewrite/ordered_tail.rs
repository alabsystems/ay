// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
use ay_core::{Proof, TermId};

use super::super::Executor;

impl Executor {
    pub(super) fn finish_input_syntax_rewrite(
        &mut self,
        proof: &mut Proof,
        rewrites: &HashMap<TermId, TermId>,
        term_overrides: HashMap<TermId, String>,
        aux_assume_steps: &HashSet<u32>,
    ) {
        if !term_overrides.is_empty() {
            self.last_proof_term_overrides = Some(term_overrides);
        }
        let extended_assertions = self.proof_exportable_assertions(rewrites);
        // Conjunct assumes introduced by top-level and-flattening are DERIVED
        // from their asserted conjunction before demotion can turn them into
        // unverified `trust` steps and fail-close the strict checker.
        Self::derive_conjunct_assumptions_from_problem_roots(
            &mut self.ctx.terms,
            proof,
            &extended_assertions,
        );
        // Replay propagation rewrites before demotion; a missing or invalid
        // record still falls through to the existing fail-closed path.
        self.derive_propagated_value_assumptions(proof, &extended_assertions);
        // #4751 `_mod_q` class — the auxiliary demotion runs AFTER the two
        // derivation lanes, not before them.
        //
        // Both orders demote exactly the same assumes; what the original order
        // changed was whether the lanes ever SAW an auxiliary assume. Running
        // first, `demote_auxiliary_non_problem_assumptions` had already turned
        // every `_mod_q`/`_div_q`/`_divmod_q`-mentioning assume into a
        // premiseless `trust` Step, so `derive_propagated_value_assumptions`
        // found no `Assume` to plan from and the whole class was unreachable
        // by construction — measured on `dillig12_m` as 100% of the surviving
        // `_mod_q_*` rejections.
        //
        // Deriving such an assume is NOT the thing #6759 excluded. That change
        // narrowed the ASSUME whitelist so a preprocessing temporary can never
        // be presented as though the user had authored it; a derivation makes
        // no such claim — it discharges the temporary from authored roots
        // through steps the UNTOUCHED strict checker re-derives, and declines
        // (leaving today's demotion) on any mismatch. Anything the lanes do
        // not derive is still an `Assume` here and is demoted exactly as
        // before.
        //
        // The index set is RECOMPUTED because both lanes splice steps into the
        // proof, which invalidates the caller's positional set. It is a pure
        // function of the proof, and is skipped entirely when the caller found
        // no auxiliary assume to begin with, so the no-aux fast path pays
        // nothing.
        if !aux_assume_steps.is_empty() {
            let aux_after_derivation =
                Self::collect_assume_steps_with_aux_mod_div_vars(&self.ctx.terms, proof);
            Self::demote_auxiliary_non_problem_assumptions(
                proof,
                &extended_assertions,
                &aux_after_derivation,
            );
        }
        Self::demote_non_problem_assumptions(proof, &extended_assertions);
        // #eq-diffvar-uncertifiable — promote the demotions that are a FRESH
        // symbol's definitional bound to a checked `fresh_def_bound` step.
        //
        // AFTER the demotion, not before, and that ordering is the whole point:
        // the checker decides freshness against the finished proof's `assume`
        // set, so this lane has to see the same set. Before the demotion the
        // preprocessed assertions that MENTION the fresh symbol are still
        // `Assume` steps and every promotion would decline. See
        // `proof_fresh_def` for the admission test and `ay_proof`'s
        // `FreshDefRegistry` for the soundness argument the checker re-runs.
        self.promote_fresh_definitional_bounds(proof, &extended_assertions);
        // (#4751) Derive the assertions `EqDiffVar` REWROTE — the residual the
        // promotion above correctly declines, because a rewritten assertion is
        // not a definition. It runs here, after both the demotion and the
        // promotion, for two reasons the lane's own module docs give in full:
        // the checker decides freshness against the finished `assume` set, and
        // a definiens already bound by a promoted step must be ADOPTED rather
        // than competed with. Its own Gate-2 reverts the whole lane if the
        // checker's `FreshDefRegistry` declines the result.
        self.derive_eq_diffvar_rewritten_assertions(proof, &extended_assertions);
        // #rewritten-assertion-bridge — the same repair for the assertions
        // `VariableSubstitution` rewrote, which carry no `EqDiffVar` record and
        // no fresh definiendum: DERIVE the rewrite from the authored
        // assertions, by congruence. See `proof/rewritten_assertion_bridge`.
        self.derive_rewritten_assertions_by_congruence(proof, &extended_assertions);
        // #rewritten-nonequality-bridge — the same repair for a rewritten
        // assertion whose goal is not a binary `=`.
        self.derive_rewritten_nonequality_assertions(proof, &extended_assertions);
        // #authored-conjunct-leaf — a leaf that IS a conjunct of an authored
        // assertion; `and_pos`, not congruence. See the lane's module docs.
        self.derive_authored_conjunct_leaves(proof, &extended_assertions);
        // #minted-definition-leaf — a leaf over a FRESH symbol the proof never
        // defines. It runs LAST: the checker decides freshness against the
        // finished `assume` set. See the lane's module docs for Gate 2.
        self.derive_leaves_over_minted_definitions(proof, &extended_assertions);
        // #conjunct-decomposition-leaf, then #ite-definition-leaf; same rule.
        self.derive_conjunctwise_decomposed_leaves(proof, &extended_assertions);
        self.derive_ite_definition_guard_leaves(proof, &extended_assertions);
        // Last resort: rebuild from the original assertions only. Failure keeps
        // the existing proof unchanged.
        self.rebuild_trust_leaf_proof_from_original_assertions(proof);
    }
}
