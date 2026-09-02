// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Independent, bounded validation for closed bit-vector `evaluate` steps.
//!
//! This is deliberately a small semantic island.  It exists for ground terms
//! that the external Alethe checker can validate with `evaluate`, but which are
//! too wide for the `u64` concat evaluator.  Only the operators needed by the
//! checked lowering are admitted: indexed `zero_extend`, named `bvmul`, and
//! indexed `extract`, over canonical bit-vector literals.  Every result is
//! computed with exact [`BigInt`] arithmetic and reduced modulo its recorded
//! bit width.

use ay_core::kani_compat::DetHashMap;
use ay_core::{Constant, ProofId, Sort, Symbol, TermData, TermId, TermStore};
use num_bigint::BigInt;
use num_traits::{One, Signed};
use std::mem::size_of;

use super::ProofCheckError;

/// Largest individual bit-vector admitted by the closed evaluator.
const MAX_CLOSED_BV_WIDTH: u32 = 4_096;
/// Largest number of distinct expression DAG nodes evaluated in one step.
const MAX_CLOSED_BV_NODES: u32 = 256;
/// Largest recursive expression depth admitted in one step.
const MAX_CLOSED_BV_DEPTH: u32 = 64;
/// Sum of result widths over distinct evaluated DAG nodes.
const MAX_CLOSED_BV_VALUE_BITS: u64 = 256 * 1_024;
/// Conservative quadratic work charge for exact multiplications.
const MAX_CLOSED_BV_MUL_WORK: u64 = 64 * 1_024 * 1_024;

/// Maximum proof-wide work charge for one admitted closed-BV evaluation.
///
/// This includes every local meter forwarded to the caller: one unit per
/// distinct node, one per materialized value bit, and the quadratic
/// multiplication charge.
pub(crate) const MAX_CLOSED_BV_EVALUATE_WORK_PER_LEMMA: u64 =
    MAX_CLOSED_BV_MUL_WORK + MAX_CLOSED_BV_VALUE_BITS + MAX_CLOSED_BV_NODES as u64;
/// Conservative private allocation reserve for one closed-BV evaluation.
pub(crate) const MAX_CLOSED_BV_EVALUATE_BYTES_PER_LEMMA: usize = 1024 * 1024;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
enum ClosedBvEvalError {
    Invalid(&'static str),
    ResourceLimit,
}

impl From<&'static str> for ClosedBvEvalError {
    fn from(reason: &'static str) -> Self {
        Self::Invalid(reason)
    }
}

#[derive(Clone)]
struct EvaluatedBv {
    value: BigInt,
    width: u32,
    contains_operation: bool,
}

struct EvalBudget<'a> {
    nodes: u32,
    value_bits: u64,
    mul_work: u64,
    progress: &'a mut dyn FnMut(usize, usize) -> bool,
}

impl EvalBudget<'_> {
    fn charge_progress(&mut self, work: u64, bytes: usize) -> Result<(), ClosedBvEvalError> {
        let work = usize::try_from(work)
            .map_err(|_| ClosedBvEvalError::Invalid("closed BV work does not fit usize"))?;
        if !(self.progress)(work, bytes) {
            return Err(ClosedBvEvalError::ResourceLimit);
        }
        Ok(())
    }

    fn charge_node(&mut self, width: u32) -> Result<(), ClosedBvEvalError> {
        self.nodes = self
            .nodes
            .checked_add(1)
            .ok_or("closed BV node counter overflow")?;
        if self.nodes > MAX_CLOSED_BV_NODES {
            return Err("closed BV expression exceeds the node limit".into());
        }
        let node_bytes = size_of::<TermId>()
            .checked_add(size_of::<EvaluatedBv>())
            .and_then(|bytes| bytes.checked_add(64))
            .ok_or("closed BV node byte charge overflow")?;
        self.charge_progress(1, node_bytes)?;
        self.value_bits = self
            .value_bits
            .checked_add(u64::from(width))
            .ok_or("closed BV value-size counter overflow")?;
        if self.value_bits > MAX_CLOSED_BV_VALUE_BITS {
            return Err("closed BV expression exceeds the aggregate value-size limit".into());
        }
        let value_bytes = usize::try_from(u64::from(width).div_ceil(8))
            .map_err(|_| ClosedBvEvalError::Invalid("closed BV value byte charge overflow"))?;
        self.charge_progress(u64::from(width), value_bytes)?;
        Ok(())
    }

    fn charge_mul(&mut self, width: u32) -> Result<(), ClosedBvEvalError> {
        let width = u64::from(width);
        let work = width
            .checked_mul(width)
            .ok_or("closed BV multiplication work overflow")?;
        self.mul_work = self
            .mul_work
            .checked_add(work)
            .ok_or("closed BV multiplication work overflow")?;
        if self.mul_work > MAX_CLOSED_BV_MUL_WORK {
            return Err("closed BV expression exceeds the multiplication work limit".into());
        }
        let scratch_bytes = usize::try_from(width.div_ceil(8))
            .ok()
            .and_then(|bytes| bytes.checked_mul(8))
            .ok_or("closed BV multiplication byte charge overflow")?;
        self.charge_progress(work, scratch_bytes)?;
        Ok(())
    }
}

struct ClosedBvEvaluator<'a, 'p> {
    terms: &'a TermStore,
    memo: DetHashMap<TermId, EvaluatedBv>,
    budget: EvalBudget<'p>,
}

impl<'a, 'p> ClosedBvEvaluator<'a, 'p> {
    fn new(terms: &'a TermStore, progress: &'p mut dyn FnMut(usize, usize) -> bool) -> Self {
        Self {
            terms,
            memo: DetHashMap::default(),
            budget: EvalBudget {
                nodes: 0,
                value_bits: 0,
                mul_work: 0,
                progress,
            },
        }
    }

    fn eval(&mut self, term: TermId, depth: u32) -> Result<EvaluatedBv, ClosedBvEvalError> {
        if depth > MAX_CLOSED_BV_DEPTH {
            return Err("closed BV expression exceeds the depth limit".into());
        }
        if let Some(value) = self.memo.get(&term) {
            return Ok(value.clone());
        }
        let width = checked_width(self.terms.sort(term))?;
        self.budget.charge_node(width)?;

        let result = match self.terms.get(term) {
            TermData::Const(Constant::BitVec {
                value,
                width: literal_width,
            }) => {
                if *literal_width != width || value.is_negative() || value >= &modulus(width) {
                    return Err("malformed or non-canonical BV literal".into());
                }
                EvaluatedBv {
                    value: value.clone(),
                    width,
                    contains_operation: false,
                }
            }
            TermData::App(Symbol::Indexed(name, indices), args) if name == "zero_extend" => {
                let ([added], [arg]) = (indices.as_slice(), args.as_slice()) else {
                    return Err("zero_extend must have one index and one operand".into());
                };
                let inner = self.eval(*arg, depth + 1)?;
                if inner.width.checked_add(*added) != Some(width) {
                    return Err("zero_extend result sort does not match its index".into());
                }
                EvaluatedBv {
                    value: inner.value,
                    width,
                    contains_operation: true,
                }
            }
            TermData::App(Symbol::Named(name), args) if name == "bvmul" => {
                let [left, right] = args.as_slice() else {
                    return Err("bvmul must have exactly two operands".into());
                };
                let left = self.eval(*left, depth + 1)?;
                let right = self.eval(*right, depth + 1)?;
                if left.width != width || right.width != width {
                    return Err("bvmul operands and result must have one width".into());
                }
                self.budget.charge_mul(width)?;
                EvaluatedBv {
                    value: (left.value * right.value) % modulus(width),
                    width,
                    contains_operation: true,
                }
            }
            TermData::App(Symbol::Indexed(name, indices), args) if name == "extract" => {
                let ([high, low], [arg]) = (indices.as_slice(), args.as_slice()) else {
                    return Err("extract must have two indices and one operand".into());
                };
                let inner = self.eval(*arg, depth + 1)?;
                if high < low || *high >= inner.width {
                    return Err("extract indices are outside the operand width".into());
                }
                let extracted_width = high
                    .checked_sub(*low)
                    .and_then(|span| span.checked_add(1))
                    .ok_or("extract width overflow")?;
                if extracted_width != width {
                    return Err("extract result sort does not match its indices".into());
                }
                EvaluatedBv {
                    value: (inner.value >> *low) % modulus(width),
                    width,
                    contains_operation: true,
                }
            }
            _ => return Err("left side is outside the closed BV evaluate fragment".into()),
        };
        self.memo.insert(term, result.clone());
        Ok(result)
    }
}

fn checked_width(sort: &Sort) -> Result<u32, ClosedBvEvalError> {
    let Sort::BitVec(sort) = sort else {
        return Err("closed BV expression contains a non-BV term".into());
    };
    if sort.width == 0 || sort.width > MAX_CLOSED_BV_WIDTH {
        return Err("closed BV width is outside the supported range".into());
    }
    Ok(sort.width)
}

fn modulus(width: u32) -> BigInt {
    BigInt::one() << width
}

/// Cheap whole-proof census predicate for the separate closed-BV evaluator.
///
/// The legacy BV `evaluate` route accepts only a `concat` root and is bounded
/// by 64 bits. The newer exact evaluator can enter its much larger private
/// work envelope only when the directional equality's left root is one of its
/// three operation families. This O(1) shape check deliberately includes
/// malformed instances of those families: strict replay may still traverse a
/// costly first operand before discovering a later shape error, so the budget
/// preflight must conservatively count the attempt.
pub(super) fn requires_expensive_budget(
    terms: &TermStore,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
) -> bool {
    if premise_count != 0 || !args.is_empty() {
        return false;
    }
    let [equality] = clause else {
        return false;
    };
    if equality.index() >= terms.len() {
        return false;
    }
    let TermData::App(Symbol::Named(name), equality_args) = terms.get(*equality) else {
        return false;
    };
    let [evaluated, _] = equality_args.as_slice() else {
        return false;
    };
    if name != "=" || evaluated.index() >= terms.len() {
        return false;
    }
    matches!(
        terms.get(*evaluated),
        TermData::App(Symbol::Named(operator), _) if operator == "bvmul"
    ) || matches!(
        terms.get(*evaluated),
        TermData::App(Symbol::Indexed(operator, _), _)
            if operator == "zero_extend" || operator == "extract"
    )
}

/// Strictly validate one ground BV evaluation equality.
///
/// The conclusion must be `(= expression literal)`, where `expression`
/// contains at least one supported operation.  Premises, rule arguments,
/// variables, user functions, alternate equality spellings, and every other
/// BV operator fail closed.
pub(super) fn validate_closed_bv_evaluate(
    terms: &TermStore,
    step_id: ProofId,
    clause: &[TermId],
    premise_count: usize,
    args: &[TermId],
    progress: &mut dyn FnMut(usize, usize) -> bool,
) -> Result<(), ProofCheckError> {
    let invalid = |reason: &str| ProofCheckError::InvalidTheoryLemma {
        step: step_id,
        reason: format!("evaluate: {reason}"),
    };
    if premise_count != 0 {
        return Err(invalid("closed BV evaluation must not have premises"));
    }
    if !args.is_empty() {
        return Err(invalid("closed BV evaluation must not have arguments"));
    }
    let [equality] = clause else {
        return Err(invalid(
            "closed BV evaluation must conclude one equality literal",
        ));
    };
    if terms.sort(*equality) != &Sort::Bool {
        return Err(invalid("conclusion equality must have Bool sort"));
    }
    let TermData::App(Symbol::Named(name), equality_args) = terms.get(*equality) else {
        return Err(invalid("conclusion must be a named equality application"));
    };
    if name != "=" || equality_args.len() != 2 {
        return Err(invalid("conclusion must be a binary equality"));
    }
    let map_eval_error = |error| match error {
        ClosedBvEvalError::Invalid(reason) => invalid(reason),
        ClosedBvEvalError::ResourceLimit => ProofCheckError::ResourceLimit,
    };
    let mut evaluator = ClosedBvEvaluator::new(terms, progress);
    let actual = evaluator
        .eval(equality_args[0], 0)
        .map_err(map_eval_error)?;
    if !actual.contains_operation {
        return Err(invalid(
            "left side must contain a supported closed BV operation",
        ));
    }
    if !matches!(
        terms.get(equality_args[1]),
        TermData::Const(Constant::BitVec { .. })
    ) {
        return Err(invalid("right side must be a canonical BV literal"));
    }
    let expected = evaluator
        .eval(equality_args[1], 0)
        .map_err(map_eval_error)?;
    if actual.width != expected.width || actual.value != expected.value {
        return Err(invalid(
            "closed BV expression does not evaluate to the asserted literal",
        ));
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use ay_core::{AletheRule, ProofStep};

    fn validate_unbounded(
        terms: &TermStore,
        clause: &[TermId],
        premise_count: usize,
        args: &[TermId],
    ) -> Result<(), ProofCheckError> {
        let mut progress = |_: usize, _: usize| true;
        validate_closed_bv_evaluate(
            terms,
            ProofId(0),
            clause,
            premise_count,
            args,
            &mut progress,
        )
    }

    fn exact_clause47_ground_term(terms: &mut TermStore) -> TermId {
        let zero64 = terms.mk_bitvec(BigInt::from(0_u8), 64);
        let zero_extended = terms.mk_app(
            Symbol::indexed("zero_extend", vec![64]),
            [zero64],
            Sort::bitvec(128),
        );
        let eight = terms.mk_bitvec(BigInt::from(8_u8), 128);
        let product = terms.mk_app(
            Symbol::named("bvmul"),
            [zero_extended, eight],
            Sort::bitvec(128),
        );
        let high_half = terms.mk_app(
            Symbol::indexed("extract", vec![127, 64]),
            [product],
            Sort::bitvec(64),
        );
        terms.mk_app(Symbol::named("="), [high_half, zero64], Sort::Bool)
    }

    #[test]
    fn accepts_exact_wide_extract_mul_zero_extend_evaluation() {
        let mut terms = TermStore::new();
        let equality = exact_clause47_ground_term(&mut terms);
        validate_unbounded(&terms, &[equality], 0, &[])
            .expect("the exact closed 128-bit expression evaluates to zero");
        assert!(super::super::bv_bitblast::recognize_bv_ground_evaluate(
            &terms,
            &[equality]
        ));
        let step = ProofStep::Step {
            rule: AletheRule::Evaluate,
            clause: vec![equality],
            premises: Vec::new(),
            args: Vec::new(),
        };
        super::super::validate_step(&terms, &mut Vec::new(), ProofId(0), &step, true, None)
            .expect("strict Evaluate dispatch must admit the independently checked expression");
    }

    #[test]
    fn multiplication_uses_exact_modular_semantics() {
        let mut terms = TermStore::new();
        let max64 = terms.mk_bitvec((BigInt::one() << 64_u32) - BigInt::one(), 64);
        let extended = terms.mk_app(
            Symbol::indexed("zero_extend", vec![64]),
            [max64],
            Sort::bitvec(128),
        );
        let max128 = terms.mk_bitvec((BigInt::one() << 128_u32) - BigInt::one(), 128);
        let product = terms.mk_app(
            Symbol::named("bvmul"),
            [extended, max128],
            Sort::bitvec(128),
        );
        let high_half = terms.mk_app(
            Symbol::indexed("extract", vec![127, 64]),
            [product],
            Sort::bitvec(64),
        );
        let equality = terms.mk_app(Symbol::named("="), [high_half, max64], Sort::Bool);
        validate_unbounded(&terms, &[equality], 0, &[])
            .expect("128-bit multiplication must be reduced modulo 2^128 exactly");
    }

    #[test]
    fn rejects_wrong_value_symbolic_leaf_and_spoofed_operator_identity() {
        let mut terms = TermStore::new();
        let valid = exact_clause47_ground_term(&mut terms);
        let TermData::App(_, valid_args) = terms.get(valid).clone() else {
            panic!("test equality must remain a raw application");
        };
        let one = terms.mk_bitvec(BigInt::from(1_u8), 64);
        let wrong = terms.mk_app(Symbol::named("="), [valid_args[0], one], Sort::Bool);
        assert!(validate_unbounded(&terms, &[wrong], 0, &[]).is_err());

        let symbolic = terms.mk_var("x", Sort::bitvec(64));
        let symbolic_ext = terms.mk_app(
            Symbol::indexed("zero_extend", vec![64]),
            [symbolic],
            Sort::bitvec(128),
        );
        let zero128 = terms.mk_bitvec(BigInt::from(0_u8), 128);
        let symbolic_eq = terms.mk_app(Symbol::named("="), [symbolic_ext, zero128], Sort::Bool);
        assert!(validate_unbounded(&terms, &[symbolic_eq], 0, &[]).is_err());

        let zero64 = terms.mk_bitvec(BigInt::from(0_u8), 64);
        let named_spoof = terms.mk_app(Symbol::named("zero_extend"), [zero64], Sort::bitvec(128));
        let spoof_eq = terms.mk_app(Symbol::named("="), [named_spoof, zero128], Sort::Bool);
        assert!(validate_unbounded(&terms, &[spoof_eq], 0, &[]).is_err());
    }

    #[test]
    fn rejects_bad_extract_sort_premises_and_arguments() {
        let mut terms = TermStore::new();
        let zero128 = terms.mk_bitvec(BigInt::from(0_u8), 128);
        let bad_extract = terms.mk_app(
            Symbol::indexed("extract", vec![127, 64]),
            [zero128],
            Sort::bitvec(65),
        );
        let zero65 = terms.mk_bitvec(BigInt::from(0_u8), 65);
        let bad_eq = terms.mk_app(Symbol::named("="), [bad_extract, zero65], Sort::Bool);
        assert!(validate_unbounded(&terms, &[bad_eq], 0, &[]).is_err());

        let valid = exact_clause47_ground_term(&mut terms);
        assert!(validate_unbounded(&terms, &[valid], 1, &[]).is_err());
        assert!(validate_unbounded(&terms, &[valid], 0, &[valid]).is_err());
    }

    #[test]
    fn rejects_expression_beyond_width_and_depth_caps() {
        let mut wide_terms = TermStore::new();
        let wide_width = MAX_CLOSED_BV_WIDTH + 1;
        let wide_zero = wide_terms.mk_bitvec(BigInt::from(0_u8), wide_width);
        let wide_expression = wide_terms.mk_app(
            Symbol::indexed("zero_extend", vec![0]),
            [wide_zero],
            Sort::bitvec(wide_width),
        );
        let wide_equality =
            wide_terms.mk_app(Symbol::named("="), [wide_expression, wide_zero], Sort::Bool);
        assert!(validate_unbounded(&wide_terms, &[wide_equality], 0, &[]).is_err());

        let mut terms = TermStore::new();
        let mut expression = terms.mk_bitvec(BigInt::from(0_u8), 8);
        for _ in 0..=MAX_CLOSED_BV_DEPTH {
            expression = terms.mk_app(
                Symbol::indexed("zero_extend", vec![0]),
                [expression],
                Sort::bitvec(8),
            );
        }
        let zero = terms.mk_bitvec(BigInt::from(0_u8), 8);
        let equality = terms.mk_app(Symbol::named("="), [expression, zero], Sort::Bool);
        assert!(validate_unbounded(&terms, &[equality], 0, &[]).is_err());
    }

    fn maximum_mul_work_equality(terms: &mut TermStore) -> TermId {
        let width = MAX_CLOSED_BV_WIDTH;
        let zero = terms.mk_bitvec(BigInt::from(0_u8), width);
        let mut expression = zero;
        // Four 4096-bit products consume exactly the local multiplication-work
        // allowance. Reusing `zero` keeps the rest of the expression tiny and
        // makes this a deterministic aggregate-meter regression.
        for _ in 0..4 {
            expression = terms.mk_app(
                Symbol::named("bvmul"),
                [expression, zero],
                Sort::bitvec(width),
            );
        }
        terms.mk_app(Symbol::named("="), [expression, zero], Sort::Bool)
    }

    #[test]
    fn repeated_maximum_mul_work_obeys_the_shared_progress_envelope() {
        let mut terms = TermStore::new();
        let equality = maximum_mul_work_equality(&mut terms);
        let mut remaining = usize::try_from(MAX_CLOSED_BV_EVALUATE_WORK_PER_LEMMA)
            .expect("the published per-lemma work bound must fit this test platform");
        let mut progress = |work: usize, _: usize| {
            let Some(next) = remaining.checked_sub(work) else {
                return false;
            };
            remaining = next;
            true
        };

        validate_closed_bv_evaluate(&terms, ProofId(0), &[equality], 0, &[], &mut progress)
            .expect("one locally maximal multiplication expression fits the aggregate allowance");
        assert!(matches!(
            validate_closed_bv_evaluate(&terms, ProofId(1), &[equality], 0, &[], &mut progress,),
            Err(ProofCheckError::ResourceLimit)
        ));
    }

    #[test]
    fn cancellation_interrupts_closed_evaluation_at_its_first_charge() {
        let mut terms = TermStore::new();
        let equality = exact_clause47_ground_term(&mut terms);
        let mut calls = 0_usize;
        let mut cancelled = |_: usize, _: usize| {
            calls += 1;
            false
        };

        assert!(matches!(
            validate_closed_bv_evaluate(&terms, ProofId(0), &[equality], 0, &[], &mut cancelled,),
            Err(ProofCheckError::ResourceLimit)
        ));
        assert_eq!(calls, 1, "cancellation must stop before a second charge");
    }
}
