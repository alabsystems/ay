// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! QF_SEQ entry point for the combined EUF+Seq theory.

use ay_core::kani_compat::DetHashSet as HashSet;

use super::super::super::Executor;
use crate::combined_solvers::UfSeqSolver;
use crate::executor_types::{Result, SolveResult, UnknownReason};

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
}
