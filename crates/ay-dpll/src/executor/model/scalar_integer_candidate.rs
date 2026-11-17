// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Bounded scalar assignment DATA for a rejected ground integer model.
//! Every proposed replacement must still pass the ordinary SAT publication gates.

use super::evaluation_copies::{EvaluationCopyScope, EvaluationReadAdmission};
use super::recovery_admission::{RecoveryAdmission, RecoveryScope};
use super::{EvalValue, Executor, Model};
use ay_core::original_query::{CountedAdmissionError, OriginalAdmissionError};
use ay_core::term::{reserve_counted, reserve_map_counted, TermConstructionAdmission};
use ay_core::{Sort, TermData};
use num_bigint::{BigInt, Sign};
use num_rational::BigRational;
use std::mem::size_of;
use std::sync::Arc;

const MAX_NODES: usize = 4096;
const MAX_LEAVES: usize = 64;
const MAX_INTEGER_LEAVES: usize = 8;

struct ClearModelCaches;

impl Drop for ClearModelCaches {
    fn drop(&mut self) {
        super::eval_memo_clear();
        super::independent_gate::invalidate_functional_model_caches();
    }
}

/// Allocation and evaluation borrow both the original read owner and one
/// aggregate recovery allowance. Neither candidate changes nor rollback renew it.
struct Admission<'a> {
    read: EvaluationReadAdmission<'a>,
    recovery: RecoveryAdmission,
}

impl TermConstructionAdmission for Admission<'_> {
    fn admit(&self, work: usize, bytes: usize) -> Result<(), CountedAdmissionError> {
        self.read.admit(work, bytes)?;
        if !self.recovery.pay(work, bytes) {
            return Err(self.refuse(OriginalAdmissionError::ObserverStopped.into()));
        }
        self.read.check()
    }

    fn refuse(&self, error: CountedAdmissionError) -> CountedAdmissionError {
        self.recovery.refuse();
        self.read.refuse(error)
    }
}

impl Executor {
    /// Build a fresh scalar-only candidate, keeping the seed's other leaf
    /// values and trying -1/0/1 for one original free Int leaf at a time.
    /// These values are search hints, never a finite-domain validity argument.
    /// In particular, raw quantifiers and lets decline rather than treating a
    /// bound variable as an independently assignable model constant.
    pub(in crate::executor) fn prepare_scalar_integer_candidate(&self) -> Option<Model> {
        if super::independent_gate::shared_gate_view_cache_active() {
            return None;
        }
        let seed = self.last_model.as_ref()?;
        let _clear_caches = ClearModelCaches;
        super::eval_memo_clear();
        super::independent_gate::invalidate_functional_model_caches();
        let recovery = RecoveryScope::enter(self, 200_000, 8 * 1024 * 1024)?;
        let copies = EvaluationCopyScope::enter(self).ok()?;
        let owner = Admission {
            read: copies.read_admission(self),
            recovery: recovery.admission(),
        };
        let roots = self.independent_gate_query_roots().ok()?;
        if roots.is_empty() || roots.len() > MAX_NODES {
            return None;
        }
        let mut stack = Vec::new();
        reserve_counted(&mut stack, roots.len(), &owner).ok()?;
        stack.extend_from_slice(&roots);
        let mut seen = ay_core::kani_compat::DetHashMap::default();
        let mut leaves = Vec::new();
        let mut has_modulo = false;
        let mut integers = 0;
        while let Some(term) = stack.pop() {
            owner.admit(1, 0).ok()?;
            if seen.contains_key(&term) {
                continue;
            }
            if seen.len() == MAX_NODES {
                return None;
            }
            reserve_map_counted(&mut seen, 1, &owner).ok()?;
            seen.insert(term, ());
            match self.ctx.terms.get(term) {
                TermData::Forall(..) | TermData::Exists(..) | TermData::Let(..) => return None,
                TermData::Var(..) => {
                    let sort = self.ctx.terms.sort(term);
                    if !matches!(sort, Sort::Bool | Sort::Int | Sort::BitVec(_))
                        || leaves.len() == MAX_LEAVES
                    {
                        return None;
                    }
                    integers += usize::from(matches!(sort, Sort::Int));
                    if integers > MAX_INTEGER_LEAVES {
                        return None;
                    }
                    reserve_counted(&mut leaves, 1, &owner).ok()?;
                    leaves.push(term);
                }
                TermData::App(symbol, args) => {
                    has_modulo |=
                        symbol.name() == "mod" && !self.ctx.terms.is_declared_function("mod");
                    if stack.len().checked_add(args.len())? > MAX_NODES {
                        return None;
                    }
                    reserve_counted(&mut stack, args.len(), &owner).ok()?;
                    stack.extend_from_slice(args);
                }
                TermData::Not(child) => {
                    reserve_counted(&mut stack, 1, &owner).ok()?;
                    stack.push(*child);
                }
                TermData::Ite(condition, yes, no) => {
                    reserve_counted(&mut stack, 3, &owner).ok()?;
                    stack.extend_from_slice(&[*condition, *yes, *no]);
                }
                TermData::Const(_) => {}
                _ => return None,
            }
        }
        if !has_modulo || integers == 0 {
            return None;
        }
        if super::debug_model() {
            eprintln!(
                "[model] scalar recovery: {} original roots, {} leaves, {integers} integers",
                roots.len(),
                leaves.len()
            );
        }
        // Exact term identity fixes order and preserves anonymous free Skolem
        // constants as well as user declarations. No rendered-name rebinding.
        owner.admit(leaves.len().checked_mul(8)?, 0).ok()?;
        leaves.sort_unstable();
        let mut candidate = Model::empty();
        if !self.bind_model_construction_owner(&mut candidate) {
            return None;
        }
        for &term in &leaves {
            let value = self.evaluate_term(seed, term);
            owner.check().ok()?;
            let exact = match (self.ctx.terms.sort(term), &value) {
                (Sort::Bool, EvalValue::Bool(_)) => true,
                (Sort::Int, EvalValue::Rational(value)) => value.is_integer(),
                (
                    Sort::BitVec(width),
                    EvalValue::BitVec {
                        value,
                        width: actual,
                    },
                ) => {
                    *actual == width.width
                        && value.sign() != Sign::Minus
                        && value.bits() <= u64::from(width.width)
                }
                _ => false,
            };
            if !exact {
                if super::debug_model() {
                    eprintln!(
                        "[model] scalar recovery: seed leaf {term:?} has no exact scalar value"
                    );
                }
                return None;
            }
            reserve_map_counted(&mut candidate.completed_values, 1, &owner).ok()?;
            candidate.completed_values.insert(term, value);
        }
        for &term in &leaves {
            if self.ctx.terms.sort(term) != &Sort::Int {
                continue;
            }
            let original = candidate.completed_values.remove(&term)?;
            for integer in [-1, 0, 1] {
                owner.admit(1, 128).ok()?;
                candidate.completed_values.insert(
                    term,
                    EvalValue::Rational(BigRational::from_integer(BigInt::from(integer))),
                );
                super::eval_memo_clear();
                super::independent_gate::invalidate_functional_model_caches();
                // This is only a prefilter. The ordinary strict, independent,
                // authoritative and certificate gates still check the SAME
                // original question after this immutable read ends.
                if self
                    .independent_evaluator_confirms(&candidate, &roots)
                    .ok()?
                {
                    if super::debug_model() {
                        eprintln!("[model] scalar recovery: complete candidate confirmed at {term:?}={integer}");
                    }
                    owner.check().ok()?;
                    owner
                        .admit(
                            1,
                            size_of::<super::evaluation_copies::RetainedEvaluationMemory>()
                                + 2 * size_of::<usize>(),
                        )
                        .ok()?;
                    candidate._scalar_candidate_memory =
                        Some(Arc::new(copies.retain_data_memory(self)?));
                    owner.check().ok()?;
                    return Some(candidate);
                }
            }
            candidate.completed_values.insert(term, original);
            super::eval_memo_clear();
            super::independent_gate::invalidate_functional_model_caches();
        }
        None
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_frontend::parse;
    use std::sync::atomic::AtomicBool;

    fn seed(divisor: i32, extra: &str) -> Executor {
        let mut exec = Executor::new();
        let source = format!(
            "(set-logic ALL) (declare-const n Int)
             (declare-const pc Bool) (declare-const v (_ BitVec 32))
             (assert pc) (assert (=> pc (= v #x0000000a)))
             (assert (< (ite (>= n 0) (mod n {divisor})
                            (- (mod (- n) {divisor}))) 0)) {extra}"
        );
        exec.execute_all(&parse(&source).unwrap()).unwrap();
        exec.begin_external_decision_query(false);
        exec.independent_gate_authored_assertions = Some(exec.ctx.assertions.clone());
        let mut model = Model::empty();
        assert!(exec.bind_model_construction_owner(&mut model));
        for (name, value) in [
            (
                "n",
                EvalValue::Rational(BigRational::from_integer(0.into())),
            ),
            ("pc", EvalValue::Bool(true)),
            (
                "v",
                EvalValue::BitVec {
                    value: 10.into(),
                    width: 32,
                },
            ),
        ] {
            let term = exec
                .ctx
                .symbol_info_by_identity(name)
                .unwrap()
                .term
                .unwrap();
            model.completed_values.insert(term, value);
        }
        exec.last_model = Some(model);
        exec
    }

    #[test]
    fn scalar_candidate_checks_both_remainder_signs_and_all_other_roots() {
        for divisor in [5, -5] {
            let exec = seed(divisor, "");
            let candidate = exec.prepare_scalar_integer_candidate().unwrap();
            let roots = exec.independent_gate_query_roots().unwrap();
            assert!(exec
                .independent_evaluator_confirms(&candidate, &roots)
                .unwrap());
            assert!(
                !exec.last_model_validated,
                "DATA construction grants no SAT authority"
            );
            assert!(exec.last_proof.is_none());
            assert!(candidate._scalar_candidate_memory.is_some());
        }
    }

    #[test]
    fn scalar_candidate_keeps_unrepresented_original_assertions() {
        let mut exec = seed(5, "(assert (>= n 0))");
        exec.ctx.assertions.pop();
        assert!(exec.prepare_scalar_integer_candidate().is_none());
    }

    #[test]
    fn scalar_candidate_keeps_assumption_only_constraints() {
        let mut exec = seed(5, "(assert (>= n 0))");
        let assumption = exec.ctx.assertions.pop().unwrap();
        exec.independent_gate_authored_assertions = Some(exec.ctx.assertions.clone());
        exec.last_assumptions = Some(vec![assumption]);
        let mut model = exec.last_model.take().unwrap();
        assert!(exec.bind_model_construction_owner(&mut model));
        exec.last_model = Some(model);
        assert!(exec.prepare_scalar_integer_candidate().is_none());
    }

    #[test]
    fn scalar_candidate_does_not_assign_a_quantified_binder() {
        let exec = seed(5, "(assert (forall ((k Int)) (>= k 0)))");
        assert!(exec.prepare_scalar_integer_candidate().is_none());
    }

    #[test]
    fn scalar_candidate_preserves_the_original_stop() {
        let mut exec = seed(5, "");
        exec.set_interrupt(Arc::new(AtomicBool::new(true)));
        assert!(exec.prepare_scalar_integer_candidate().is_none());
        assert!(!exec.last_model_validated);
    }

    #[test]
    fn scalar_candidate_cannot_replace_a_live_fixed_model_view() {
        let exec = seed(5, "");
        {
            let _view = super::super::independent_gate::GateViewCacheSession::new();
            assert!(exec.prepare_scalar_integer_candidate().is_none());
        }
        assert!(exec.prepare_scalar_integer_candidate().is_some());
    }

    #[test]
    fn scalar_payload_copy_prepays_the_same_recovery_ledger() {
        let exec = seed(5, "");
        let value = BigInt::from(1) << 4096usize;
        let _recovery = RecoveryScope::enter(&exec, usize::MAX, 0).unwrap();
        let _copies = EvaluationCopyScope::enter(&exec).unwrap();
        assert!(!super::super::evaluation_copies::integer(&value));
        assert!(RecoveryScope::enter(&exec, usize::MAX, usize::MAX).is_none());
    }
}
