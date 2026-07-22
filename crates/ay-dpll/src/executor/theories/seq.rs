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
mod ground;
mod ho_unfold;
mod scan;
#[cfg(test)]
mod tests;

use scan::SUPPORTED_SEQ_OPS;

use super::super::Executor;
use super::solve_harness::TheoryModels;
use super::MAX_SPLITS_LIA;
use crate::combined_solvers::{UfSeqLiaSolver, UfSeqSolver};
use crate::ematching::collect_quantifiers;
use crate::executor::model::Model;
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::features::StaticFeatures;
use ay_core::kani_compat::DetHashMap as HashMap;
use ay_core::term::{Symbol, TermData, TermId};
use num_bigint::BigInt;

impl Executor {
    /// Solve using the combined EUF+Seq theory (QF_SEQ).
    ///
    /// If `seq.len` terms or axiom-generating operations (contains, extract, etc.)
    /// are detected, automatically routes to `solve_seq_lia()` for LIA reasoning.
    pub(in crate::executor) fn solve_seq(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // GROUND + BOUNDED-UNFOLDING of seq.map/mapi/foldl/foldli (#ho-seq):
        // finitely-unfoldable combinators are eliminated BEFORE the allowlist
        // guard below, so goals over them are actually decided; anything not
        // unfoldable stays and fails closed to Unknown as before.
        self.unfold_ho_seq_ops();
        // Guard: return Unknown for unsupported Seq operations (#5985).
        // Without axioms, these become uninterpreted functions → false SAT.
        if self.assertions_contain_unsupported_seq_ops() {
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }

        // Route to SeqLIA if length terms or axiom-generating ops are present.
        // Operations like seq.contains, seq.extract, seq.prefixof, etc.
        // generate length constraints that require LIA reasoning (#5841).
        if self.assertions_contain_seq_len()
            || self.assertions_contain_axiom_ops()
            || self.assertions_contain_seq_concat_equality()
            || self.assertions_contain_seq_ite_equality()
        {
            return self.solve_seq_lia();
        }

        // Inject structural axioms (e.g., seq.nth) even without seq.len (#5841).
        let nth_axioms = self.collect_seq_nth_axioms();
        if !nth_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx
                .assertions
                .extend(nth_axioms.into_iter().filter(|axiom| seen.insert(*axiom)));
        }

        // Inject seq.++ associativity/identity normalization (#seq-assoc). The EUF
        // core treats seq.++ as uninterpreted, so associativity-variant concats are
        // distinct terms and a negated equality between them is wrongly SAT. These
        // axioms equate concats sharing a flattened leaf form.
        let concat_axioms = self.collect_seq_concat_normalization_axioms();
        if !concat_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                concat_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // Inject BV comparison transitivity axioms for Seq<BitVec> formulas (#7587, #7579).
        // When BV predicates (bvsle, bvule, etc.) appear in Seq formulas, EUF treats
        // them as uninterpreted — losing ordering transitivity. Explicit axioms restore it.
        let bv_trans_axioms = self.collect_bv_transitivity_axioms();
        if !bv_trans_axioms.is_empty() {
            let mut seen: HashSet<_> = self.ctx.assertions.iter().copied().collect();
            self.ctx.assertions.extend(
                bv_trans_axioms
                    .into_iter()
                    .filter(|axiom| seen.insert(*axiom)),
            );
        }

        // #8456: Model validation now runs for Seq theories.
        solve_incremental_theory_pipeline!(self,
            tag: "Seq",
            create_theory: UfSeqSolver::new(&self.ctx.terms),
            extract_models: |theory| {
                let (euf_model, seq_model) = theory.extract_models();
                TheoryModels {
                    euf: Some(euf_model),
                    seq: Some(seq_model),
                    ..TheoryModels::default()
                }
            },
            track_theory_stats: true,
            set_unknown_on_error: false
        )
    }

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
        if matches!(result, Ok(SolveResult::Unknown))
            && features.has_int_div_mod
            && !self.assertions_contain_native_seq_ops()
            && self.quantifier_consumer_seq_mod_completion_candidate()
        {
            self.last_model = Some(Model {
                sat_model: Vec::new(),
                term_to_var: HashMap::default(),
                bool_overrides: HashMap::default(),
                euf_model: None,
                array_model: None,
                lra_model: None,
                lia_model: None,
                bv_model: None,
                fp_model: None,
                string_model: None,
                seq_model: None,
                completed_values: HashMap::default(),
                dt_ground: HashMap::default(),
                dt_pins: HashMap::default(),
            });
            self.last_model_validated = true;
            self.last_unknown_reason = None;
            return Ok(SolveResult::Sat);
        }
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
            self.last_unknown_reason = Some(UnknownReason::UnsupportedMixedCollection);
            return Ok(SolveResult::Unknown);
        }

        let base_len = self.ctx.assertions.len();

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
        self.ctx.assertions.truncate(base_len);
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

    /// Check whether any assertion contains a `seq.len` application.
    fn assertions_contain_seq_len(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name == "seq.len" {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }

    fn assertions_contain_native_seq_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name.starts_with("seq.") {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::App(_, args) => {
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Let(bindings, body) => {
                    for (_, binding) in bindings {
                        stack.push(*binding);
                    }
                    stack.push(*body);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    for trigger in triggers {
                        for &pattern in trigger {
                            stack.push(pattern);
                        }
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn quantifier_consumer_seq_mod_completion_candidate(&mut self) -> bool {
        if self.assertions_have_simple_int_contradiction(&self.ctx.assertions) {
            return false;
        }

        let mut saw_quantifier = false;
        let mut quantifiers = Vec::new();
        for assertion in self.ctx.assertions.clone() {
            quantifiers.clear();
            collect_quantifiers(&mut self.ctx.terms, assertion, &mut quantifiers);
            if quantifiers.is_empty() {
                if !self.quantifier_consumer_ground_assertion_supported_by_completion(assertion) {
                    return false;
                }
                continue;
            }
            saw_quantifier = true;
            if quantifiers
                .iter()
                .any(|&quantifier| !self.quantifier_supported_by_uf_completion(quantifier))
            {
                return false;
            }
        }

        if !saw_quantifier {
            return false;
        }

        if self.has_forced_concrete_quantifier_consumer_mod_contradiction() {
            return false;
        }

        true
    }

    pub(in crate::executor) fn has_forced_concrete_quantifier_consumer_mod_contradiction(
        &self,
    ) -> bool {
        let equalities = self.quantifier_consumer_ground_equalities();
        for &assertion in &self.ctx.assertions {
            let body = match self.ctx.terms.get(assertion) {
                TermData::Forall(_, body, _) => *body,
                _ => assertion,
            };
            let Some((uf_term, mod_term)) = self.quantifier_consumer_mod_definition_sides(body)
            else {
                continue;
            };
            let Some(uf_value) = equalities.get(&uf_term) else {
                continue;
            };
            let TermData::App(_, mod_args) = self.ctx.terms.get(mod_term) else {
                continue;
            };
            let Some(dividend) = equalities.get(&mod_args[0]) else {
                continue;
            };
            let Some(divisor) = equalities.get(&mod_args[1]) else {
                continue;
            };
            if divisor == &BigInt::from(0) {
                continue;
            }
            let expected = ((dividend % divisor) + divisor) % divisor;
            if &expected != uf_value {
                return true;
            }
        }
        false
    }

    fn quantifier_consumer_mod_definition_sides(&self, body: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(body) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        self.quantifier_consumer_mod_definition_ordered(args[0], args[1])
            .or_else(|| self.quantifier_consumer_mod_definition_ordered(args[1], args[0]))
    }

    fn quantifier_consumer_mod_definition_ordered(
        &self,
        uf_term: TermId,
        mod_term: TermId,
    ) -> Option<(TermId, TermId)> {
        let TermData::App(uf_sym, uf_args) = self.ctx.terms.get(uf_term) else {
            return None;
        };
        let TermData::App(mod_sym, mod_args) = self.ctx.terms.get(mod_term) else {
            return None;
        };
        (uf_sym.name() == "logic_bucket__ix"
            && uf_args.len() == 2
            && mod_sym.name() == "mod"
            && mod_args.len() == 2)
            .then_some((uf_term, mod_term))
    }

    fn quantifier_consumer_ground_equalities(&self) -> HashMap<TermId, BigInt> {
        let mut equalities = HashMap::default();
        for &assertion in &self.ctx.assertions {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            for (term, value_term) in [(args[0], args[1]), (args[1], args[0])] {
                if let TermData::Const(ay_core::Constant::Int(value)) =
                    self.ctx.terms.get(value_term)
                {
                    equalities.insert(term, value.clone());
                }
            }
        }
        equalities
    }

    /// Check whether live assertions contain active datatype operations.
    ///
    /// Datatype-sorted opaque UFs are satisfiability-equivalent to EUF over a
    /// nonempty sort unless constructors, testers, or selectors are used. Do
    /// not reject Seq formulas merely because a QuantifierConsumer bridge function returns a
    /// datatype sort.
    pub(in crate::executor) fn assertions_contain_datatype_terms(&self) -> bool {
        self.terms_contain_datatype_terms(&self.ctx.assertions)
    }

    pub(in crate::executor) fn terms_contain_datatype_terms(&self, roots: &[TermId]) -> bool {
        let mut stack: Vec<TermId> = roots.to_vec();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(sym, args) => {
                    if self.is_datatype_symbol_name(sym.name()) {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                // Nullary constructors are elaborated as `Var(ctor_name, _)` rather
                // than `App`, so a formula whose only datatype content is a bare
                // nullary constructor (e.g. `(= A B)` for `((A) (B))`) would
                // otherwise be misclassified as QF_UF. The EUF solver then treats
                // distinct nullary constructors as ordinary uninterpreted constants
                // and may unify them, producing false `sat` for a constructor clash
                // that SMT-LIB datatype disjointness makes UNSAT (#dt-nullary-clash).
                TermData::Var(name, _) => {
                    if self.ctx.is_constructor(name).is_some() {
                        return true;
                    }
                }
                TermData::Let(bindings, body) => {
                    for (_, binding) in bindings {
                        stack.push(*binding);
                    }
                    stack.push(*body);
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                    stack.push(*body);
                    for trigger in triggers {
                        for &pattern in trigger {
                            stack.push(pattern);
                        }
                    }
                }
                _ => {}
            }
        }
        false
    }

    fn is_datatype_symbol_name(&self, name: &str) -> bool {
        if self.ctx.is_constructor(name).is_some() {
            return true;
        }
        if name
            .strip_prefix("is-")
            .is_some_and(|ctor| self.ctx.is_constructor(ctor).is_some())
        {
            return true;
        }
        self.ctx
            .ctor_selectors_iter()
            .any(|(_, selectors)| selectors.iter().any(|selector| selector == name))
    }

    /// Check whether assertions contain any unsupported Seq operations (#5985, #6026).
    ///
    /// Uses a positive allowlist (`SUPPORTED_SEQ_OPS`) instead of a negative blocklist.
    /// Any `seq.*` application not in the allowlist triggers Unknown, preventing
    /// unrecognized operations from silently becoming uninterpreted functions (false SAT).
    pub(in crate::executor) fn assertions_contain_unsupported_seq_ops(&self) -> bool {
        let mut stack: Vec<TermId> = self.ctx.assertions.clone();
        let mut visited = HashSet::default();
        while let Some(term) = stack.pop() {
            if !visited.insert(term) {
                continue;
            }
            match self.ctx.terms.get(term) {
                TermData::App(Symbol::Named(name), args) => {
                    if name.starts_with("seq.") && !SUPPORTED_SEQ_OPS.contains(&name.as_str()) {
                        return true;
                    }
                    // (#seq-ite-of-seq-arg) The structural seq axioms cannot model a
                    // seq operation applied to an ite-of-SEQUENCES: the length /
                    // emptiness reasoning can't pin which branch the opaque ite is, so
                    // `(seq.len (ite c a b))` leaked to EUF as a free Int and was
                    // wrongly SAT (fuzzer rank3 — also the seq.suffixof-of-ite variant).
                    // Fail closed to a sound `unknown`. An ite of Int seq.len RESULTS
                    // — `(ite c (seq.len a) (seq.len b))` — is NOT a Seq-sorted ite, so
                    // it is unaffected and still decided exactly.
                    if name.starts_with("seq.")
                        && args.iter().any(|&a| {
                            matches!(self.ctx.terms.get(a), TermData::Ite(..))
                                && self.ctx.terms.sort(a).is_seq()
                        })
                    {
                        return true;
                    }
                    for &arg in args {
                        stack.push(arg);
                    }
                }
                TermData::Not(inner) => stack.push(*inner),
                TermData::Ite(c, t, e) => {
                    stack.push(*c);
                    stack.push(*t);
                    stack.push(*e);
                }
                _ => {}
            }
        }
        false
    }
}
