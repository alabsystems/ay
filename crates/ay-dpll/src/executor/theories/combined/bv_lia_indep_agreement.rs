// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-lane agreement for the independent BV + LIA category
//! (`_BV_LIA_INDEP`, `solve_bv_lia_indep`).
//!
//! The category solves one assertion set through two lanes. The BV lane
//! bit-blasts the BitVec predicates and treats every arithmetic atom and Bool
//! variable as a free opaque literal; the AUFLIA lane decides the arithmetic,
//! the arrays and the propositional skeleton and treats the BitVec predicates
//! as uninterpreted. Each lane is free to satisfy a MIXED disjunction through
//! a different branch:
//!
//! ```text
//! (or (and a (= (select m i) #x00000002)) (= l 1))
//! ```
//!
//! The BV lane took `(= l 1)` (opaque, so `l` stays unvalued) with
//! `select m i = 0`; AUFLIA took `a ∧ select m i = 2` with `l = 0`. No merge
//! of the two witnesses satisfies the root: the BV predicate is false with
//! the BV lane's bits and `(= l 1)` is false with AUFLIA's arithmetic. The
//! merge ladder (`restore_indep_bv_model_with_arith_graft`) then restored
//! the BV model alone and returned `sat`, so the independent model gate
//! caught an invalid model and the query, which z3 decides `sat` at once,
//! came back `unknown` (model-checker-consumer `safe_symbolic_from_elem`: every TPA
//! interpolant check over the SingleLoop encoding of its seeded memory).
//!
//! Agreement: when the independent gate refutes the merged witness, the
//! AUFLIA lane is re-decided with the BV lane's own truth values for its
//! BitVec predicates as assumptions. Its new witness then takes, on every atom
//! the BV lane owns, exactly the value the BV lane's bits give it, and the
//! ladder merges the two witnesses again. When the lanes still cannot agree
//! the BV witness alone is published only if the gate does not refute it,
//! else the lane answers `unknown` itself: no witness the gate refutes leaves
//! this lane. The re-decision never answers `unsat`: it is conditional on one
//! BV witness.
//!
//! The same step runs when the AUFLIA cross-check answers `unknown`
//! (#bv-lia-indep-unknown-agreement). That arm used to publish the BV
//! witness alone, unchecked, although it values no Int term:
//!
//! ```text
//! (or (and (= l 0) (= a c) (= m n)) (and (= l 1) (not (= b #x0000000000000000))))
//! ```
//!
//! The BV lane took the second branch (`(= l 1)` opaque, `l` unvalued, so
//! read as 0). AUFLIA's own validation refused its witness, which values the
//! BitVec `b` of the disequality at 0, so it answered `unknown`, and the gate
//! caught the published BV witness (model-checker-consumer's per-row route over
//! `safe_wide_array_as_bytes` and the two `safe_static_*` harnesses: every
//! catch a TPA reachability check over the SingleLoop encoding). An `unknown`
//! supplies no AUFLIA witness, so the first merge is the BV witness alone:
//! published when the gate's evaluator does not refute it, exactly as before;
//! otherwise AUFLIA is re-decided under the BV lane's BitVec-predicate values,
//! and only a merge the evaluator accepts leaves the lane.
//!
//! Pinning goes both ways (#bv-lia-indep-pinned-bv-lane). AUFLIA pinned to
//! the BV lane's predicates can still leave a merge the gate refutes: the BV
//! lane chose its arithmetic atoms freely, as opaque literals, and nothing
//! made them agree with any AUFLIA witness. So when even the BV witness alone
//! is refuted, the BV lane is re-decided in turn with an AUFLIA witness's
//! truth values for its arithmetic atoms (an `=`/`distinct` or order
//! comparison over Int or Real operands) as assumptions, and its new witness
//! is merged with that AUFLIA witness. The AUFLIA witness is the pinned
//! re-decision's when that answered `sat`: it agrees with the BV lane on
//! every BitVec predicate, so its arithmetic is one the BV lane can meet.
//! Otherwise it is the cross-check's own; after an AUFLIA `unknown` with no
//! `sat` re-decision there is none, and the step does not run. Every atom of
//! the merge then has the value the pinned BV skeleton gave it. Like the
//! other re-decision this one never answers `unsat` (it is conditional on one
//! AUFLIA witness), and its merge faces the same evaluator check. It runs
//! last, only where the lane would otherwise answer `unknown`.

use ay_core::kani_compat::DetHashSet as HashSet;
use ay_core::{Sort, TermData, TermId};

use crate::executor::model::{CandidateOwner, EvalValue, Model};
use crate::executor::theories::bv::BvSolveConfig;
use crate::executor::Executor;
use crate::executor_types::{ExecutorError, Result, SolveResult, UnknownOrigin, UnknownReason};

enum AgreementFailure {
    Stopped(UnknownOrigin),
    Executor(ExecutorError),
}

impl From<UnknownOrigin> for AgreementFailure {
    fn from(origin: UnknownOrigin) -> Self {
        Self::Stopped(origin)
    }
}

impl From<ExecutorError> for AgreementFailure {
    fn from(error: ExecutorError) -> Self {
        Self::Executor(error)
    }
}

type AgreementResult<T> = std::result::Result<T, AgreementFailure>;

enum AtomLane {
    BitVec,
    Arithmetic,
}

#[cfg(test)]
mod tests;

/// Outcome of one pass of the merge ladder.
pub(super) enum IndepMerge {
    /// A witness was installed in `last_model`.
    Installed,
    /// The BV lane's skeleton is refuted under the AUFLIA arithmetic; nothing
    /// was installed.
    LanesDisagree,
}

impl Executor {
    /// Publish the result of a `_BV_LIA_INDEP` solve whose BV lane answered
    /// `sat`; `last_model` holds the AUFLIA witness when the cross-check
    /// answered `sat`, and nothing after [`Self::finish_indep_bv_lia_after_unknown`]
    /// (see module docs).
    pub(super) fn finish_indep_bv_lia_sat(
        &mut self,
        bv_model: Option<Model>,
        bv_model_validated: bool,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        let mut deferred_reason = self.last_unknown_reason;
        let outcome = (|| {
            let mut owner = CandidateOwner::capture(self)?;
            let _nested_owner = owner.enter_nested();
            self.retain_indep_retry_stop(&mut owner)?;
            let result = self.agree_indep_lanes(
                bv_model,
                bv_model_validated,
                assertions,
                assumptions,
                &mut owner,
                &mut deferred_reason,
            )?;
            owner.finish(self.ctx.terms.true_memory_bytes())?;
            Ok(result)
        })();
        match outcome {
            Ok(result) => {
                if matches!(result, SolveResult::Unknown) {
                    self.remember_indep_refusal(&mut deferred_reason);
                    self.last_unknown_reason = deferred_reason.or(Some(UnknownReason::Incomplete));
                }
                Ok(result)
            }
            Err(AgreementFailure::Executor(error)) => Err(error),
            Err(AgreementFailure::Stopped(origin)) => {
                self.record_evaluation_stop(origin);
                self.publish_evaluation_stop();
                Ok(SolveResult::Unknown)
            }
        }
    }

    fn agree_indep_lanes(
        &mut self,
        bv_model: Option<Model>,
        bv_model_validated: bool,
        assertions: &[TermId],
        assumptions: &[TermId],
        owner: &mut CandidateOwner,
        deferred_reason: &mut Option<UnknownReason>,
    ) -> AgreementResult<SolveResult> {
        owner.entries(assertions.len())?;
        owner.entries(assumptions.len())?;
        let mut roots = assertions.to_vec();
        roots.extend_from_slice(assumptions);
        // The AUFLIA witness the BV lane is pinned to when nothing else
        // leaves the lane (#bv-lia-indep-pinned-bv-lane).
        let mut arithmetic = self.last_model.clone();
        owner.poll()?;
        if self.merge_indep_witnesses(bv_model.clone(), bv_model_validated, &roots) {
            return Ok(SolveResult::Sat);
        }
        owner.poll()?;
        let Some(bv) = bv_model else {
            return Ok(self.indep_lanes_disagree());
        };
        let pins = self.indep_atom_literals(&bv, &roots, AtomLane::BitVec, owner)?;
        if !pins.is_empty() {
            owner.entries(assumptions.len())?;
            owner.entries(pins.len())?;
            let mut pinned = assumptions.to_vec();
            pinned.extend(pins);
            let solved = self.solve_auf_lia_with_assumptions(assertions, &pinned)?;
            if matches!(solved, SolveResult::Unknown) {
                self.remember_indep_refusal(deferred_reason);
            }
            self.retain_indep_retry_stop(owner)?;
            if matches!(solved, SolveResult::Sat) {
                // This witness agrees with the BV lane on every BitVec
                // predicate, so its arithmetic is one the BV lane can meet.
                let agreeing = self.last_model.clone();
                owner.poll()?;
                if self.merge_indep_witnesses(Some(bv.clone()), bv_model_validated, &roots) {
                    return Ok(SolveResult::Sat);
                }
                if agreeing.is_some() {
                    arithmetic = agreeing;
                }
            }
        }
        owner.poll()?;
        // Still disagreeing: the BV witness alone, as before, unless the
        // independent gate refutes it too.
        self.last_model = Some(bv);
        self.last_model_validated = bv_model_validated;
        if !self.installed_witness_refuted(&roots)? {
            return Ok(SolveResult::Sat);
        }
        // Refuted too: the BV lane pinned to AUFLIA's arithmetic, last, only
        // where the lane would otherwise answer `unknown`.
        if let Some(auflia) = arithmetic {
            if self.merge_with_bv_lane_pinned_to(auflia, assumptions, &roots, owner)? {
                return Ok(SolveResult::Sat);
            }
            self.remember_indep_refusal(deferred_reason);
        }
        self.retain_indep_retry_stop(owner)?;
        Ok(self.indep_lanes_disagree())
    }

    /// A retry does not erase a typed resource refusal.
    /// In particular, conditional UNSAT is merely disagreement; it grants no
    /// new allowance and is never a verdict for the original assertions.
    fn retain_indep_retry_stop(&self, owner: &mut CandidateOwner) -> AgreementResult<()> {
        owner.poll()?;
        if let Some(
            reason @ (UnknownReason::Timeout
            | UnknownReason::ResourceLimit
            | UnknownReason::MemoryLimit
            | UnknownReason::Interrupted),
        ) = self.last_unknown_reason
        {
            return Err(owner.refuse(reason.origin()).into());
        }
        Ok(())
    }

    /// A rejected candidate is not a revoked search allowance. Keep its
    /// diagnostic if alternatives all fail, but allow a new independently
    /// checked witness under the same original owner.
    fn remember_indep_refusal(&self, saved: &mut Option<UnknownReason>) {
        if let Some(reason) = self.last_unknown_reason {
            if !matches!(reason, UnknownReason::Incomplete | UnknownReason::Unknown) {
                *saved = Some(reason);
            }
        }
    }

    /// Re-decide the BV lane with `auflia`'s truth values for its arithmetic
    /// atoms as assumptions, then merge its new witness with `auflia`
    /// (#bv-lia-indep-pinned-bv-lane); `true` when the merge installed a
    /// witness the independent gate does not refute. A BV lane that cannot
    /// meet those values says nothing about the query: its `unsat` is
    /// conditional on one AUFLIA witness and is never published.
    fn merge_with_bv_lane_pinned_to(
        &mut self,
        auflia: Model,
        assumptions: &[TermId],
        roots: &[TermId],
        owner: &mut CandidateOwner,
    ) -> AgreementResult<bool> {
        let pins = self.indep_atom_literals(&auflia, roots, AtomLane::Arithmetic, owner)?;
        if pins.is_empty() {
            return Ok(false);
        }
        owner.entries(assumptions.len())?;
        owner.entries(pins.len())?;
        let mut pinned = assumptions.to_vec();
        pinned.extend(pins);
        let solved = match self.solve_bv_core(BvSolveConfig::qf_bv(), &pinned) {
            Ok(result) => result,
            // The pinned BV lane's own validation refused its witness: there
            // is no witness to merge.
            Err(ExecutorError::ModelValidation(_)) => {
                self.retain_indep_retry_stop(owner)?;
                return Ok(false);
            }
            Err(error) => return Err(error.into()),
        };
        self.retain_indep_retry_stop(owner)?;
        if !matches!(solved, SolveResult::Sat) {
            return Ok(false);
        }
        let pinned_bv = self.last_model.take();
        let pinned_bv_validated = self.last_model_validated;
        self.last_model = Some(auflia);
        Ok(self.merge_indep_witnesses(pinned_bv, pinned_bv_validated, roots))
    }

    /// [`Self::finish_indep_bv_lia_sat`] after the AUFLIA cross-check answered
    /// `unknown` for a reason other than unsupported arithmetic. An `unknown`
    /// supplies no witness: a candidate AUFLIA's own validation refused is
    /// withdrawn, never grafted, so the BV witness alone is the first merge.
    pub(super) fn finish_indep_bv_lia_after_unknown(
        &mut self,
        bv_model: Option<Model>,
        bv_model_validated: bool,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        self.withdraw_rejected_model();
        self.finish_indep_bv_lia_sat(bv_model, bv_model_validated, assertions, assumptions)
    }

    /// Run the merge ladder over the BV witness and the AUFLIA witness in
    /// `last_model`; `true` when it installed a witness the independent gate
    /// does not refute.
    ///
    /// The ladder's own refutation check reads an opaque atom's SAT value
    /// (`(= l 1)` stays `true` in the BV lane's skeleton next to the grafted
    /// `l = 0`) and answers `Unknown` for array reads, so a merge it keeps can
    /// still be false; the gate evaluates every assertion from its leaves.
    fn merge_indep_witnesses(
        &mut self,
        bv_model: Option<Model>,
        bv_model_validated: bool,
        roots: &[TermId],
    ) -> bool {
        matches!(
            self.restore_indep_bv_model_with_arith_graft(bv_model, bv_model_validated, roots),
            IndepMerge::Installed
        ) && self
            .installed_witness_refuted(roots)
            .is_ok_and(|refuted| !refuted)
    }

    /// Whether the independent gate's evaluator falsifies one of `roots`
    /// under the installed witness. `CannotConfirm` is not a refutation.
    fn installed_witness_refuted(
        &self,
        roots: &[TermId],
    ) -> std::result::Result<bool, UnknownOrigin> {
        let refuted = match self.last_model.as_ref() {
            Some(model) => self.independent_evaluator_refutes(model, roots),
            None => Ok(false),
        };
        crate::executor::model::eval_memo_clear();
        refuted
    }

    fn indep_lanes_disagree(&mut self) -> SolveResult {
        // A refuted witness of the substitution-carrying BV lane: arm the one
        // preprocessing-free re-solve, exactly as the gate's refutation of it
        // would have (#abv-subst-model-retry in `check_sat_guarded`).
        if self.bv_subst_lane {
            self.bv_subst_model_rejected = true;
        }
        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = Some(UnknownReason::Incomplete);
        SolveResult::Unknown
    }

    /// Deterministically pin only atoms the selected witness actually values.
    /// Both directions retain the SAME owner across scans, retries and merges.
    fn indep_atom_literals(
        &mut self,
        witness: &Model,
        roots: &[TermId],
        lane: AtomLane,
        owner: &mut CandidateOwner,
    ) -> AgreementResult<Vec<TermId>> {
        let _memo = crate::executor::model::EvalMemoSession::new();
        let mut atoms = Vec::new();
        let mut seen: HashSet<TermId> = HashSet::default();
        owner.entries(roots.len())?;
        let mut stack = roots.to_vec();
        while let Some(term) = stack.pop() {
            owner.entries(2)?;
            if !seen.insert(term) {
                continue;
            }
            if match lane {
                AtomLane::BitVec => self.is_bitvec_predicate(term),
                AtomLane::Arithmetic => self.is_arithmetic_atom(term),
            } {
                atoms.push(term);
            }
            stack.extend(owner.children(&self.ctx.terms, term)?);
        }
        owner.sort(atoms.len())?;
        atoms.sort_unstable();
        owner.entries(atoms.len())?;
        let mut literals = Vec::with_capacity(atoms.len());
        for atom in atoms {
            owner.pay(1, 0)?;
            let value = self.evaluate_term(witness, atom);
            owner.poll()?;
            match value {
                EvalValue::Bool(true) => literals.push(atom),
                EvalValue::Bool(false) => {
                    owner.entries(1)?;
                    literals.push(self.ctx.terms.mk_not(atom));
                }
                _ => {}
            }
        }
        owner.finish(self.ctx.terms.true_memory_bytes())?;
        Ok(literals)
    }

    fn is_arithmetic_atom(&self, term: TermId) -> bool {
        if !matches!(self.ctx.terms.sort(term), Sort::Bool) {
            return false;
        }
        let TermData::App(symbol, args) = self.ctx.terms.get(term) else {
            return false;
        };
        let Some(&first) = args.first() else {
            return false;
        };
        matches!(self.ctx.terms.sort(first), Sort::Int | Sort::Real)
            && matches!(symbol.name(), "=" | "distinct" | "<" | "<=" | ">" | ">=")
    }

    fn is_bitvec_predicate(&self, term: TermId) -> bool {
        if !matches!(self.ctx.terms.sort(term), Sort::Bool) {
            return false;
        }
        let TermData::App(symbol, args) = self.ctx.terms.get(term) else {
            return false;
        };
        let Some(&first) = args.first() else {
            return false;
        };
        let bitvec_operands = matches!(self.ctx.terms.sort(first), Sort::BitVec(_));
        match symbol.name() {
            "=" | "distinct" => bitvec_operands,
            "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge" => {
                bitvec_operands
            }
            _ => false,
        }
    }
}
