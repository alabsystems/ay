// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Generic sequence theory (Seq T) solving.
//!
//! Handles QF_SEQ and QF_SEQLIA logics. QF_SEQ uses the combined EUF+Seq
//! solver for Nelson-Oppen equality exchange (see #5951). QF_SEQLIA adds
//! LIA for `seq.len` reasoning with injected length axioms (see #5958).

// #8529: Use deterministic hash sets in all builds.
use ay_core::kani_compat::DetHashSet as HashSet;
mod axioms_core;
mod axioms_indexof;
mod axioms_replace;
mod axioms_search;
mod bv_transitivity;
mod classify;
mod ground;
mod ho_unfold;
mod scan;
mod solve_seq;
#[cfg(test)]
mod tests;

use super::super::Executor;
use super::solve_harness::TheoryModels;
use super::MAX_SPLITS_LIA;
use crate::combined_solvers::UfSeqLiaSolver;
use crate::executor_types::{Result, SolveResult, UnknownOrigin, UnknownReason};
use crate::features::StaticFeatures;
use ay_core::term::TermId;

impl Executor {
    /// Solve using the combined EUF+Seq+LIA theory (QF_SEQLIA).
    ///
    /// Injects `seq.len` axioms then solves with `UfSeqLiaSolver` (#5958).
    pub(in crate::executor) fn solve_seq_lia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // GROUND + BOUNDED-UNFOLDING of the HO seq combinators (#ho-seq);
        // see solve_seq. No-op when none are present.
        self.unfold_ho_seq_ops();
        // Guard: return Unknown for unsupported Seq operations (#5985).
        if self.assertions_contain_unsupported_seq_ops() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // Determined-value inlining (#seq-det-var): a seq variable a top-level
        // conjunct pins to a GROUND seq literal (`(= (seq.unit 3) s)`) is
        // substituted by that literal, so ground predicates over it
        // (`(seq.contains s (seq.unit -3))`) become fully ground and the existing
        // ground refutation path decides them. Closes a wrong-SAT where the seq
        // model left the var unresolved so the strict oracle could not refute the
        // predicate. Equisatisfiable; runs FIRST on pristine assertions.
        self.inline_determined_ground_seq_vars();

        // Bounded word-equation decision (#seq-word-eq): when every word-equation
        // seq variable has a provable length bound, enumerate the finitely many
        // length tuples and assert the disjunction of per-tuple unit expansions,
        // so the downstream unit-decomposition decides multi-variable word
        // equations (e.g. `s0.s2.[0].[1] = [-1].s0.[1]` with len(s2.s1.s0.s1)=2).
        // Sound + complete for the bounded fragment; no-op when any var is
        // unbounded. Runs FIRST so the single-var expansion / length abstraction
        // process the (possibly disjunctive) result.
        // Fold provably-empty `seq.extract` (constant negative start / non-positive
        // length) to `seq.empty` FIRST, so `(= (seq.extract s -2 3) s)` collapses to
        // `(= empty s)` and the alias/length/word-eq passes see the forced empties.
        self.fold_provably_empty_seq_extracts();

        // Inline GROUND-resolvable `seq.extract`/`seq.at` terms to their literal
        // value (#seq-ite-eq-operand): `(seq.at v 0)` over a ground `v` becomes a
        // concrete `seq.unit`/`seq.empty`, so the opaque EUF extract node is
        // removed and the branch equalities of a distributed `ite` reduce to pure
        // unit/empty equalities the injectivity + length passes refute. Runs after
        // determined-ground inlining (so the base resolves) and before the ite /
        // unit passes. Equisatisfiable.
        self.inline_ground_seq_extracts();

        // Re-run determined-ground inlining now that the GROUND-resolvable
        // extract/at terms above were folded away (#seq-extract-var-source).
        // `inline_determined_ground_seq_vars` deliberately EXCLUDES a seq var
        // read by a skolem-decomposition op (extract/indexof/replace/...), to
        // preserve completeness of those ops' own decision procedures (#6033).
        // But once a var's only extract/at uses are GROUND and have just been
        // resolved to concrete literals, that var is no longer read by any such
        // op, so the exclusion no longer applies — and leaving it as a variable
        // makes `expand_determined_length_seq_vars` blow `(= s [1,2,3])` up into
        // a fresh-element word equation the in-loop combined seq theory cannot
        // confirm SAT (fail-closing extract/at-over-var-source to Unknown).
        // Re-inlining collapses `(= s GROUND)` to a trivial truth instead.
        // Equisatisfiable; any var still read by a REMAINING (symbolic) extract
        // stays excluded (recomputed from the post-fold assertions), so the
        // #6033 completeness guard is preserved.
        self.inline_determined_ground_seq_vars();

        // Transitive chaining (#seq-transitive-wordeq): combine two definitions
        // `(= X v)`,`(= Y v)` of the same seq var into the derived word equation
        // `(= X Y)` so the decomposition/length passes can refute a conflict
        // (e.g. `s2.s0.[-2] = s1 & s0.s0.[2] = s1`). Sound (transitivity); runs
        // first so the bounded decider and expansion see the derived equations.
        let transitive_axioms = self.collect_seq_transitive_equality_axioms();
        if !transitive_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                transitive_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        self.decide_bounded_seq_word_equations();

        // Determined-length expansion (#seq-word-eq): substitute a sequence
        // variable whose length is forced to a concrete k (by the linear length
        // system of the DEFINITELY-TRUE seq equalities, or a direct (seq.len v)=k)
        // with k fresh element units, so the unit-decomposition pass can refute
        // pure word equations like `(unit 0) ++ s ++ (unit 2) = s ++ (unit 1) ++ s`.
        // Sound (equisatisfiable, length facts only from definitely-true equalities)
        // and gated to skip vars used in rich seq ops. Runs FIRST on pristine
        // user assertions.
        self.expand_determined_length_seq_vars();

        // Length abstraction for word equations (#seq-len-abstraction): emit
        // length congruence + emptiness biconditionals so the LIA backend can
        // refute length-infeasible sequence equalities (a var equated to a concat
        // otherwise has no seq.len term and the contradiction stays invisible).
        // Runs on the (possibly expanded) user assertions, scoped to genuine
        // var-concat word equations, so the rich seq procedures are untouched.
        let len_constraint_axioms = self.collect_seq_length_constraint_axioms();
        if !len_constraint_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                len_constraint_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Length congruence for definitely-true seq equalities (#seq-len-congruence):
        // `(= s0 s1)` ⟹ `(= (seq.len s0) (seq.len s1))`, so a var=var alias feeds
        // the concat length-sum system (refutes e.g. `len(s0++s1)=3 ∧ s0=s1`).
        let len_cong_axioms = self.collect_seq_definite_length_congruence_axioms();
        if !len_cong_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                len_cong_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        let seq_len_axioms = self.collect_seq_len_axioms();
        if !seq_len_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                seq_len_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Second transitive-chaining pass (#seq-transitive-wordeq): the seq
        // axiom generation above emits DEFINITE equalities anchored on rich-op
        // applications — e.g. `(= (seq.replace u empty d) (seq.++ d u))` for a
        // provably-empty pattern. Chaining those with the user's own definite
        // equalities over the same pivot term derives the word equations
        // (`(= (seq.++ d u) <user concat>)`) that the unit-decomposition pass
        // below refutes. The first pass ran before axiom generation and could
        // not see them (qf_slia_seqextract_oob_false_sat: wrong SAT).
        let transitive_axioms = self.collect_seq_transitive_equality_axioms();
        if !transitive_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                transitive_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Inject seq.++ associativity/identity normalization (#seq-assoc).
        let concat_axioms = self.collect_seq_concat_normalization_axioms();
        if !concat_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                concat_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // ITE-lifting for seq-sorted equalities (#seq-ite-eq-operand): when an
        // asserted `(= L R)` over sequences has an `(ite c t e)` operand, EUF
        // treats the ite as one opaque seq value and never case-splits the
        // branches, so it can unify `L` with the opaque ite even when BOTH
        // branches mismatch — a wrong-SAT (seq_falsesat_iteofseq_eq_operand).
        // Emit the tautology `(= (= L (ite c t e)) (and (=> c (= L t)) (=> (not
        // c) (= L e))))` so the branch equalities reach the unit-decomposition /
        // length passes below. Runs BEFORE those passes so the new per-branch
        // equality atoms are visible when they re-collect from the assertions.
        let ite_eq_axioms = self.collect_seq_ite_equality_lifting_axioms();
        if !ite_eq_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                ite_eq_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Unit prefix/suffix decomposition for sequence concat equalities
        // (#bug15): derive element equalities the word-equation solver missed.
        let unit_decomp_axioms = self.collect_seq_unit_decomposition_axioms();
        if !unit_decomp_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                unit_decomp_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // `seq.unit` injectivity (#seq-ite-eq-operand): EUF treats `seq.unit` as
        // uninterpreted, so it cannot derive `(seq.unit a) != (seq.unit b)` from
        // `a != b`. Emit `(= (= (seq.unit a) (seq.unit b)) (= a b))` for every
        // unit pair so a single-element CONTENT mismatch is refuted (e.g. the
        // then-branch `(seq.at [false,false] 0) = (seq.unit true)` after ground
        // extraction equates it to `(seq.unit false)`). Runs after the seq
        // axiom passes so any units synthesized by ground extraction are scanned.
        let unit_inj_axioms = self.collect_seq_unit_injectivity_axioms();
        if !unit_inj_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                unit_inj_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Inject base predicate tautology axioms (contains/prefixof/suffixof over
        // empty or reflexive operands) so their negations are refuted (#seq-pred-taut).
        let pred_axioms = self.collect_seq_predicate_tautology_axioms();
        if !pred_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx
                .assertions
                .extend(pred_axioms.into_iter().filter(|axiom| seen.insert(*axiom)));
        }

        // Inject BV comparison transitivity axioms for Seq<BitVec> formulas (#7587, #7579).
        let bv_trans_axioms = self.collect_bv_transitivity_axioms();
        if !bv_trans_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                bv_trans_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        let features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
        if features.has_int_div_mod {
            if let Some(result) = self.try_sat_via_mod_free_or_branch()? {
                return Ok(result);
            }
            if !self.assertions_contain_native_seq_ops() {
                if let Some(result) = self.try_sat_via_known_divisor_preprocessing()? {
                    return Ok(result);
                }
            }
        }

        // #8456: Model validation now runs for SeqLIA theories.
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        let result = solve_incremental_split_loop_pipeline!(self,
            tag: "SeqLIA",
            persistent_sat_field: lia_persistent_sat,
            create_theory: UfSeqLiaSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                let (euf_model, seq_model, lia_model) = theory.extract_models();
                TheoryModels {
                    euf: Some(euf_model),
                    seq: Some(seq_model),
                    lia: lia_model,
                    ..TheoryModels::default()
                }
            },
            max_splits: MAX_SPLITS_LIA,
            pre_theory_import: |theory, lc, hc, ds| {
                theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                theory.import_dioph_state(std::mem::take(ds));
            },
            post_theory_export: |_theory| {
                let (lc, hc) = _theory.take_learned_state();
                let ds = _theory.take_dioph_state();
                (lc, hc, ds)
            },
            pre_iter_check: |_s| {
                solve_interrupt
                    .as_ref()
                    .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                    || solve_deadline.expired()
            }
        );
        result
    }

    /// Solve mixed live Seq terms with AUFLIA by injecting bounded Seq axioms
    /// and preserving the array/LIA route for map/set-style obligations.
    pub(in crate::executor) fn solve_seq_auflia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // GROUND + BOUNDED-UNFOLDING of the HO seq combinators (#ho-seq);
        // see solve_seq. The unfolded form is plain select/nth/len content the
        // AUFLIA route below already handles. No-op when none are present.
        self.unfold_ho_seq_ops();
        if self.assertions_contain_unsupported_seq_ops() {
            self.record_mixed_collection_unsupported_fragment_diagnostics("seq-array-ops");
            self.record_unknown_from_origin(UnknownOrigin::UnsupportedMixedCollection);
            return Ok(SolveResult::Unknown);
        }

        let base_assertions_exact = self.ctx.assertions.clone();

        let seq_len_axioms = self.collect_seq_len_axioms();
        if !seq_len_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                seq_len_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        let bv_trans_axioms = self.collect_bv_transitivity_axioms();
        if !bv_trans_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                bv_trans_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // This wrapper can add sequence/array bridge terms before delegating
        // to AUFLIA (or its mod/div rescue). Close the final wrapper surface so
        // an early rescue SAT cannot skip finite-index array equalities.
        let _ = self.add_finite_index_array_closure();

        let features = StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions);
        let result = if features.has_int_div_mod {
            if let Some(result) = self.try_sat_via_mod_free_or_branch()? {
                Ok(result)
            } else {
                self.solve_uf_nia()
            }
        } else {
            self.solve_auf_lia()
        };
        self.ctx.assertions = base_assertions_exact;
        result
    }

    /// Solve QF_SEQ with check-sat-assuming (#5994, #7656).
    ///
    /// Mirrors `solve_seq()` but temporarily adds assumptions to assertions,
    /// using UfSeqSolver (not bare SeqSolver) for correct Nelson-Oppen reasoning.
    ///
    /// Uses `with_isolated_incremental_state` to prevent assumption-scoped
    /// clauses from leaking into the persistent SAT solver. Without isolation,
    /// contradictory assumptions encoded as permanent unit clauses poison the
    /// incremental state, causing subsequent calls to return false UNSAT (#7656).
    pub(in crate::executor) fn solve_seq_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let mut scoped_assertions = Vec::with_capacity(assertions.len() + assumptions.len());
        scoped_assertions.extend(assertions.iter().copied());
        scoped_assertions.extend(assumptions.iter().copied());

        let result = self.with_isolated_incremental_state(Some(scoped_assertions), Self::solve_seq);

        match result {
            Ok(SolveResult::Unsat(_)) => {
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::unsat())
            }
            Ok(SolveResult::Sat) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unknown) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Unknown)
            }
            Err(err) => {
                self.last_assumption_core = None;
                Err(err)
            }
        }
    }

    /// Solve QF_SEQLIA with check-sat-assuming (#5994, #7656).
    ///
    /// Mirrors `solve_seq_lia()` but temporarily adds assumptions to assertions,
    /// using UfSeqLiaSolver with axiom injection for correct Seq+LIA reasoning.
    ///
    /// Uses `with_isolated_incremental_state` to prevent assumption-scoped
    /// clauses from leaking into the persistent SAT solver (#7656).
    pub(in crate::executor) fn solve_seq_lia_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let mut scoped_assertions = Vec::with_capacity(assertions.len() + assumptions.len());
        scoped_assertions.extend(assertions.iter().copied());
        scoped_assertions.extend(assumptions.iter().copied());

        let result =
            self.with_isolated_incremental_state(Some(scoped_assertions), Self::solve_seq_lia);

        match result {
            Ok(SolveResult::Unsat(_)) => {
                self.last_assumption_core = Some(assumptions.to_vec());
                Ok(SolveResult::unsat())
            }
            Ok(SolveResult::Sat) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Sat)
            }
            Ok(SolveResult::Unknown) => {
                self.last_assumption_core = None;
                Ok(SolveResult::Unknown)
            }
            Err(err) => {
                self.last_assumption_core = None;
                Err(err)
            }
        }
    }
}
