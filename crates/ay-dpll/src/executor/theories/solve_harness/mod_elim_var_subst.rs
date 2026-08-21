// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! The second `VariableSubstitution` round of LIA preprocessing (#8736).
//!
//! Split out of `preprocess_lia_artifacts` so this round's completeness
//! rationale and its proof-provenance mint sit together at one reviewable
//! size instead of adding to that function's length.

use ay_core::TermId;

use crate::executor::Executor;
use crate::preprocess::{PreprocessingPass, VariableSubstitution};

impl Executor {
    /// #8736 completeness: re-run variable substitution over the
    /// mod/div-eliminated assertions.
    ///
    /// Constant-divisor elimination rewrites `(= (mod x k) c)` into a fresh
    /// remainder var `r` with the decomposition `x = k*q + r ∧ 0 ≤ r < |k|`
    /// plus a separate unit `(= r c)`. Because elimination runs AFTER the
    /// first `VariableSubstitution` pass, neither that `r = c` unit NOR the
    /// decomposition's definition of the dividend `x` is ever folded: `x`
    /// stays a solver variable ranging over its original (often wide) box
    /// while `x = k*q + r` ties it to the fresh quotient `q`. The LP
    /// relaxation of that coupling drifts and trips the branch-and-bound
    /// oscillation guard (`check_split_oscillation`), so a genuinely UNSAT
    /// problem (e.g. the #8736 ring cascade: `x ≡ 0 (mod 3)` over a 16-bit
    /// carry chain forced to residue 1) is abandoned as `incomplete`.
    ///
    /// Folding `r = c` ALONE is not enough — the dividend `x` must also be
    /// eliminated (`x → k*q + c`) so the search runs in quotient space, where
    /// the box is tight and divisibility is implicit. Both eliminations are
    /// exactly what `VariableSubstitution` performs on `x = k*q + r` and
    /// `r = c`, so we simply run it a second time on the eliminated set,
    /// REUSING the caller's `var_subst` accumulator so model recovery
    /// (`recover_substituted_lia_values`) restores the eliminated user
    /// variables from the quotient/remainder model.
    ///
    /// SOUND (equisatisfiable — cannot flip a verdict): every substitution is
    /// a top-level defining equality `v = e` (with `v` not in `e`), which
    /// holds in every model, so inlining it changes no assertion's truth;
    /// conflicting definitions are left in place and refute as before. This
    /// is the same transform already trusted for the first-round pass.
    /// `VariableSubstitution::apply` rewrites in place (defining equalities
    /// collapse to reflexive tautologies, the assertion count is unchanged),
    /// so `preprocessed_sources` stays positionally aligned.
    ///
    /// Gated under `!is_producing_proofs()` (like the `EqDiffVar` and
    /// `GuardedEqMining` passes): this round inlines the mod/div decomposition
    /// and dissolves the rewritten `(= r c)` mod-result assertions (which the
    /// proof reconstructor maps back to the original `(= (mod x k) c)`
    /// premises), so running it when the caller asked for a proof artifact
    /// would detach the proof's `assume` leaves from the original mod
    /// assertions and force extra trust steps (#6759). Completeness — not
    /// soundness — is what is traded off under proofs, so this only affects
    /// how many `incomplete` results a proof-producing run reports, never a
    /// verdict.
    pub(super) fn rerun_var_subst_after_mod_elimination(
        &mut self,
        var_subst: &mut VariableSubstitution,
        preprocessed: &mut Vec<TermId>,
        preprocessed_sources: &mut Vec<Vec<TermId>>,
    ) {
        // Kept in the NEGATED spelling the proof-gate census inventories, so
        // relocating this round out of `preprocess_lia_artifacts` moves the
        // vetted site rather than hiding it (#proof-capability B2).
        if !self.is_producing_proofs() {
            self.apply_second_var_subst_round(var_subst, preprocessed, preprocessed_sources);
        }
    }

    /// The round proper, once the explicit-demand gate above has admitted it.
    fn apply_second_var_subst_round(
        &mut self,
        var_subst: &mut VariableSubstitution,
        preprocessed: &mut Vec<TermId>,
        preprocessed_sources: &mut Vec<Vec<TermId>>,
    ) {
        // Clear the first round's substitution cache: reusing `var_subst`
        // adds new definitions (e.g. `x -> k*q + c`) to the map, but the
        // cache memoizes the OLD map (where `x` mapped to itself), so without
        // a reset the second `apply` would return stale, unsubstituted terms.
        var_subst.reset();
        // (#4751) Snapshot the pre-substitution artifact list so this SECOND
        // in-place rewrite can be REPLAYED into proof steps, exactly as the
        // first round already is. Measured on dillig12_m: this round rewrites
        // at least one artifact in 240 of 1099 calls, and it is the producer
        // of BOTH residual premiseless `trust` steps (the 28-ary rule-body
        // `or` and the `_mod_q` disequality) — they reach
        // `demote_non_problem_assumptions` with no `before -> after` record,
        // so `propagation_replay_candidates` never nominates them.
        //
        // The two predicates are deliberately DIFFERENT and both are
        // load-bearing: the ROUND runs under `!is_producing_proofs()` ("the
        // caller did not ask for a proof artifact"), while the MINT runs under
        // `produce_proofs_enabled()` ("a proof tracker is recording"). On the
        // CHC route those are `false` and `true` respectively for 1075 of 1099
        // probed calls — precisely the window in which the rewrite happens AND
        // its provenance is needed.
        let before = self.produce_proofs_enabled().then(|| preprocessed.clone());
        let changed =
            var_subst.apply_with_sources(&mut self.ctx.terms, preprocessed, preprocessed_sources);
        if !changed {
            return;
        }
        if let Some(before) = before {
            self.extend_propagated_value_provenance_from_var_subst(
                &before,
                preprocessed,
                var_subst,
            );
        }
        // Record the newly eliminated definitions for model completion at
        // finalize time (model/completion.rs), mirroring the first-round
        // `record_var_substitutions` call.
        self.record_var_substitutions(var_subst);
    }
}
