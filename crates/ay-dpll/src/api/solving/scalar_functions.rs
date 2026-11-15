// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Complete closed interpretations from one immutable accepted native model.

use ay_core::Sort;
use std::sync::atomic::Ordering;

use crate::api::{model_parse, ScalarFunctionModel, Solver, SolverError, MAX_API_BITVECTOR_WIDTH};

const MAX_FUNCTIONS: usize = 1_024;
const MAX_REQUEST_BYTES: usize = 8 * 1024 * 1024;
const MAX_SIGNATURE_WORK: usize = 1_048_576;
const MAX_SIGNATURE_BYTES: usize = 16 * 1024 * 1024;

fn invalid(message: &str) -> SolverError {
    SolverError::InvalidArgument {
        operation: "get_named_scalar_function_models",
        message: message.to_owned(),
    }
}

impl Solver {
    /// Read complete typed scalar function definitions from one accepted model.
    ///
    /// Names are decoded source symbols, not SMT expressions. Requests are
    /// unique and retain their order; every name must have one live direct-source
    /// declaration with Bool/BV arguments and a BV result. Original declared UFs
    /// adopted as definitions remain eligible, but native declarations, genuine
    /// `define-fun` commands, aliases and overloaded names refuse. Missing,
    /// open, malformed or unsupported printed definitions refuse the whole
    /// batch: no defaults or function bodies are synthesized by this getter.
    ///
    /// Requires current SAT plus accepted model validation. This data is NOT a
    /// SAT capability: retain and check the originating `VerifiedSolveResult`'s
    /// emission witness and independently replay the claimed source witness.
    /// The getter neither consumes nor mints that one-shot authority.
    ///
    /// Request/signature inspection and decoding have cumulative fixed bounds.
    /// These do not bound the existing native model printer or process RSS.
    #[must_use = "the complete model batch may be unavailable or refused"]
    pub fn try_get_named_scalar_function_models(
        &self,
        names: &[&str],
    ) -> Result<Vec<ScalarFunctionModel>, SolverError> {
        self.with_model_evaluation_read(|| self.try_get_named_scalar_function_models_in_read(names))
    }

    fn try_get_named_scalar_function_models_in_read(
        &self,
        names: &[&str],
    ) -> Result<Vec<ScalarFunctionModel>, SolverError> {
        self.ensure_last_sat_model_accepted_for_consumer()?;
        self.scalar_model_controls()?;
        let expected = self.scalar_function_requests(names)?;
        if expected.is_empty() {
            return Ok(Vec::new());
        }
        // Only one printing pass, through the same immutable Executor/Context.
        // The strict decoder authenticates every requested signature and closed
        // body; this is not the best-effort whole-model parser.
        let output = self.executor.model_for_decoder();
        self.scalar_model_controls()?;
        let result = model_parse::parse_scalar_function_models(&output, &expected);
        drop(output);
        drop(expected);
        self.ensure_last_sat_model_accepted_for_consumer()?;
        self.scalar_model_controls()?;
        result.ok_or_else(|| {
            SolverError::ModelGenerationFailed(
                "scalar function model is missing, open, ill-sorted, unsupported or over budget"
                    .into(),
            )
        })
    }

    fn scalar_function_requests<'a>(
        &'a self,
        names: &'a [&'a str],
    ) -> Result<Vec<(&'a str, &'a [Sort], &'a Sort)>, SolverError> {
        let mut budget = SignatureBudget::default();
        budget.names(names)?;
        let mut expected = Vec::new();
        budget.charge(
            0,
            names.len() * std::mem::size_of::<(&str, &[Sort], &Sort)>(),
        )?;
        expected
            .try_reserve_exact(names.len())
            .map_err(|_| invalid("request allocation refused"))?;
        for &name in names {
            self.scalar_model_controls()?;
            let context = self.executor.context();
            let (arguments, result) = context
                .source_function_for_model(name)
                .ok_or_else(|| invalid("not a unique live ordinary source declaration"))?;
            budget.charge(
                arguments.len(),
                arguments
                    .len()
                    .checked_mul(std::mem::size_of::<Sort>())
                    .ok_or_else(|| invalid("signature size overflow"))?,
            )?;
            budget.sort(result)?;
            if !matches!(result, Sort::BitVec(_)) {
                return Err(invalid("ordinary scalar function result must be BV"));
            }
            for sort in arguments {
                budget.sort(sort)?;
            }
            if arguments.is_empty() {
                let (term, declared) = context
                    .source_constant_for_value(name)
                    .ok_or_else(|| invalid("nullary source carrier is unavailable"))?;
                let actual = self.terms().sort(term);
                budget.sort(actual)?;
                if actual != declared || declared != result {
                    return Err(invalid("nullary source carrier sort mismatch"));
                }
            }
            expected.push((name, arguments, result));
        }
        Ok(expected)
    }

    fn scalar_model_controls(&self) -> Result<(), SolverError> {
        let limit = self
            .executor
            .term_memory_limit()
            .into_iter()
            .chain(self.term_memory_limit)
            .min();
        if self.interrupt.load(Ordering::Relaxed)
            || ay_core::TermStore::global_memory_exceeded()
            || limit.is_some_and(|limit| self.terms().true_memory_bytes() > limit)
        {
            return Err(SolverError::ModelGenerationFailed(
                "scalar model extraction interrupted or over memory budget".into(),
            ));
        }
        Ok(())
    }
}

#[derive(Default)]
struct SignatureBudget {
    work: usize,
    bytes: usize,
}

impl SignatureBudget {
    fn charge(&mut self, work: usize, bytes: usize) -> Result<(), SolverError> {
        self.work = self
            .work
            .checked_add(work)
            .ok_or_else(|| invalid("signature work overflow"))?;
        self.bytes = self
            .bytes
            .checked_add(bytes)
            .ok_or_else(|| invalid("signature copy overflow"))?;
        if self.work > MAX_SIGNATURE_WORK || self.bytes > MAX_SIGNATURE_BYTES {
            return Err(invalid("signature work/copy allowance exceeded"));
        }
        Ok(())
    }

    fn names(&mut self, names: &[&str]) -> Result<(), SolverError> {
        if names.len() > MAX_FUNCTIONS {
            return Err(invalid("more than 1024 requested functions"));
        }
        let mut bytes = 0usize;
        for (index, name) in names.iter().enumerate() {
            bytes = bytes
                .checked_add(
                    name.len()
                        .checked_mul(2)
                        .and_then(|n| n.checked_add(2))
                        .ok_or_else(|| invalid("request text overflow"))?,
                )
                .ok_or_else(|| invalid("request text overflow"))?;
            if name.is_empty() || bytes > MAX_REQUEST_BYTES {
                return Err(invalid("empty name or request text over 8 MiB"));
            }
            self.charge(1 + name.len().div_ceil(64), 0)?;
            for previous in &names[..index] {
                self.charge(name.len().min(previous.len()).div_ceil(64).max(1), 0)?;
                if name == previous {
                    return Err(invalid("duplicate requested function name"));
                }
            }
        }
        self.charge(0, bytes)
    }

    fn sort(&mut self, sort: &Sort) -> Result<(), SolverError> {
        let payload = match sort {
            Sort::Bool => 0,
            Sort::BitVec(width) if (1..=MAX_API_BITVECTOR_WIDTH).contains(&width.width) => {
                usize::try_from(width.width.div_ceil(8)).map_err(|_| invalid("scalar width"))?
            }
            _ => return Err(invalid("expected scalar Bool or bounded BV sort")),
        };
        self.charge(1 + payload.div_ceil(64), 128 + payload)
    }
}

#[cfg(test)]
mod tests;
