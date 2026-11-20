// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::*;
use ay_model_check::{EvalOutcome, GateVerdict, ModelView};
use ay_sat::{CandidateSolver, Literal, Variable};
use std::collections::HashMap;

mod scalar;
pub(super) use scalar::{copy_value, Encoding};

struct ScalarView<'a> {
    assignment: &'a HashMap<TermId, Scalar>,
    owner: &'a CountedAdmission,
}

pub(super) struct CandidateMap {
    pub(super) projection: Vec<Encoding>,
    pub(super) leaves: Vec<(TermId, Encoding)>,
}

pub(super) struct Witness {
    pub(super) values: Vec<Scalar>,
    pub(super) leaves: Vec<(Term, Scalar)>,
    pub(super) validation_work: u64,
}

fn literal_index(literal: i32) -> Result<usize> {
    literal
        .checked_abs()
        .filter(|value| *value != 0)
        .map(|value| value as usize - 1)
        .ok_or(Failure::Incomplete(UnknownReason::SelfCheckRejected))
}

impl CandidateMap {
    /// This is the sole row admission gate. Neither circuit-model provenance
    /// nor a projection value can replace evaluation in the original source.
    pub(super) fn validate(
        &self,
        original: &Solver,
        roots: &[TermId],
        projection: &[Term],
        model: &[bool],
        owner: &CountedAdmission,
    ) -> Result<Witness> {
        if self.projection.len() != projection.len() {
            return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
        }
        let before = owner.usage()?.work_admitted;
        // Each row supplies its own sparse witness. No value can survive a
        // preceding candidate, and unused original terms cost no row scan.
        let mut assignment = HashMap::new();
        let entry_bytes = std::mem::size_of::<(TermId, Scalar)>()
            .checked_mul(4)
            .and_then(|bytes| bytes.checked_mul(self.leaves.len()))
            .ok_or_else(|| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        owner.admit(self.leaves.len(), entry_bytes)?;
        assignment
            .try_reserve(self.leaves.len())
            .map_err(|_| owner.refuse(CountedAdmissionError::StorageExhausted))?;
        let mut leaves = Vec::new();
        reserve(&mut leaves, self.leaves.len(), owner)?;
        for (id, encoding) in &self.leaves {
            owner.admit(1, 0)?;
            if id.index() >= original.terms().len()
                || !matches!(original.terms().get(*id), TermData::Var(..))
                || !matches!(
                    (original.terms().sort(*id), encoding),
                    (Sort::Bool, Encoding::Bool(_)) | (Sort::Int, Encoding::Int(_))
                )
            {
                return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
            }
            let value = encoding.decode(model, owner)?;
            if assignment
                .insert(*id, scalar::copy_value(&value, owner)?)
                .is_some()
            {
                return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
            }
            leaves.push((original.wrap_term(*id), value));
        }
        let view = ScalarView {
            assignment: &assignment,
            owner,
        };
        match ay_model_check::confirm_model(original.terms(), &view, roots) {
            GateVerdict::ConfirmedSat => {}
            GateVerdict::ModelViolates { .. } => {
                return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected))
            }
            GateVerdict::CannotConfirm { .. } => {
                return Err(Failure::Incomplete(UnknownReason::Incomplete))
            }
        }
        let mut values = Vec::new();
        reserve(&mut values, projection.len(), owner)?;
        let evaluator = ay_model_check::Evaluator::new(original.terms(), &view);
        for (&term, encoding) in projection.iter().zip(&self.projection) {
            owner.admit(1, 0)?;
            original.resolve_term(OPERATION, term)?;
            let value = encoding.decode(model, owner)?;
            let same = match (&value, evaluator.evaluate(term.id())) {
                (
                    Scalar::Bool(expected),
                    EvalOutcome::Value(ay_model_check::ModelValue::Bool(actual)),
                ) => *expected == actual,
                (
                    Scalar::Int(expected),
                    EvalOutcome::Value(ay_model_check::ModelValue::Int(actual)),
                ) => {
                    owner.admit(
                        usize::try_from(expected.bits().max(actual.bits()).div_ceil(64))
                            .map_err(|_| owner.refuse(CountedAdmissionError::WorkExhausted))?,
                        0,
                    )?;
                    *expected == actual
                }
                (_, EvalOutcome::Value(_)) => false,
                _ => return Err(Failure::Incomplete(UnknownReason::Incomplete)),
            };
            if !same {
                return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
            }
            values.push(value);
        }
        drop(evaluator);
        owner.check()?;
        let validation_work = owner.usage()?.work_admitted.saturating_sub(before);
        Ok(Witness {
            values,
            leaves,
            validation_work,
        })
    }
}

impl ModelView for ScalarView<'_> {
    fn has_evaluation_admission(&self) -> bool {
        true
    }
    fn refuse_evaluation_work(&self, _reason: &str) {
        self.owner.refuse(CountedAdmissionError::WorkExhausted);
    }
    fn admit_evaluation_work(&self, work: usize, bytes: usize) -> std::result::Result<(), String> {
        self.owner
            .admit(work, bytes)
            .map_err(|error| error.to_string())
    }
    fn leaf_value(&self, id: TermId) -> Option<ay_model_check::ModelValue> {
        self.owner.admit(1, 0).ok()?;
        match scalar::copy_value(self.assignment.get(&id)?, self.owner).ok()? {
            Scalar::Bool(value) => Some(ay_model_check::ModelValue::Bool(value)),
            Scalar::Int(value) => Some(ay_model_check::ModelValue::Int(value)),
        }
    }
    fn functional_array_interrupted(&self) -> bool {
        self.owner.check().is_err()
    }
}

pub(super) fn circuit(
    compiled: &Compiled,
    owner: &CountedAdmission,
) -> Result<(CandidateSolver, CandidateMap)> {
    let bv_error = |error: ay_bv::CountedBvError| match error {
        ay_bv::CountedBvError::Stopped(error) => Failure::Stopped(error),
        _ => Failure::Incomplete(UnknownReason::SelfCheckRejected),
    };
    let mut encoder = ay_bv::CountedBvEncoder::new(&compiled.terms, owner).map_err(bv_error)?;
    encoder.assert_roots(&compiled.roots).map_err(bv_error)?;
    encoder
        .encode_terms(&compiled.projection)
        .map_err(bv_error)?;
    let mut leaf_terms = Vec::new();
    reserve(&mut leaf_terms, compiled.leaves.len(), owner)?;
    leaf_terms.extend(compiled.leaves.iter().map(|&(_, translated)| translated));
    // Source validation visits dead arms too. Their Bool leaves can have
    // disappeared from the folded circuit, but still receive real assignments.
    encoder.encode_terms(&leaf_terms).map_err(bv_error)?;
    let encoding = |id: TermId| -> Result<Encoding> {
        match compiled.terms.sort(id) {
            Sort::Bool => Ok(Encoding::Bool(encoder.literal(id).map_err(bv_error)?)),
            Sort::BitVec(_) => {
                let bits = encoder.bits(id).map_err(bv_error)?;
                if bits.len() != compiled.signed_width as usize {
                    return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
                }
                let mut result = Vec::new();
                reserve(&mut result, bits.len(), owner)?;
                owner.admit(bits.len(), 0)?;
                result.extend_from_slice(bits);
                Ok(Encoding::Int(result))
            }
            _ => Err(Failure::Incomplete(UnknownReason::SelfCheckRejected)),
        }
    };
    let mut projection = Vec::new();
    reserve(&mut projection, compiled.projection.len(), owner)?;
    for &id in &compiled.projection {
        projection.push(encoding(id)?);
    }
    let mut leaves = Vec::new();
    reserve(&mut leaves, compiled.leaves.len(), owner)?;
    for &(source, id) in &compiled.leaves {
        leaves.push((source, encoding(id)?));
    }
    let num_vars = encoder.num_vars().map_err(bv_error)? as usize;
    let mut solver = CandidateSolver::try_new(num_vars, owner.clone())?;
    for clause in encoder.clauses().map_err(bv_error)? {
        let mut literals = Vec::new();
        reserve(&mut literals, clause.literals().len(), owner)?;
        for &literal in clause.literals() {
            owner.admit(1, 0)?;
            if literal_index(literal)? >= num_vars {
                return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
            }
            literals.push(Literal::from_dimacs(literal));
        }
        solver.add_clause(literals)?;
    }
    for encoding in projection
        .iter()
        .chain(leaves.iter().map(|(_, encoding)| encoding))
    {
        for &literal in encoding.literals() {
            owner.admit(1, 0)?;
            let index = literal_index(literal)?;
            if index >= num_vars {
                return Err(Failure::Incomplete(UnknownReason::SelfCheckRejected));
            }
            solver.freeze(Variable::new(index as u32))?;
        }
    }
    encoder.finish().map_err(bv_error)?;
    owner.check()?;
    Ok((solver, CandidateMap { projection, leaves }))
}
