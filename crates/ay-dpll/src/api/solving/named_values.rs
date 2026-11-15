// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Exact source-constant requests, including declarations parsed from SMT-LIB.

use ay_core::{quote_symbol, Sort, TermId};

use crate::api::model_parse;
use crate::api::{ModelValue, Solver, SolverError};

const MAX_REQUEST_BYTES: usize = 8 * 1024 * 1024;
const MAX_SORT_WORK: usize = 1_048_576;
const MAX_SORT_DEPTH: usize = 64;

fn invalid(message: &str) -> SolverError {
    SolverError::InvalidArgument {
        operation: "get_named_values",
        message: message.to_owned(),
    }
}

impl Solver {
    /// Retrieve exact typed values for constants declared in parsed SMT-LIB.
    ///
    /// Names are decoded symbol names, not SMT expressions or quoted source
    /// text. Every name must have one live nullary direct-source declaration;
    /// missing names, ambiguous overloads, definitions and internal/native
    /// aliases refuse the complete batch. Use [`Self::try_get_values`] for
    /// native builder handles. Input order and duplicate names are preserved.
    ///
    /// Requests are bounded before allocation, and all values use the existing
    /// cumulative typed decoder. This does not redeclare symbols, grow the term
    /// arena, or use the best-effort whole-model parser. SAT validation and
    /// independent witness replay remain separate caller obligations. Request
    /// and decoding allowances do not bound native model printing or process RSS.
    #[must_use = "typed value extraction can refuse the complete batch"]
    pub fn try_get_named_values(&self, names: &[&str]) -> Result<Vec<ModelValue>, SolverError> {
        self.with_model_evaluation_read(|| self.try_get_named_values_in_read(names))
    }

    fn try_get_named_values_in_read(&self, names: &[&str]) -> Result<Vec<ModelValue>, SolverError> {
        admit_names(names)?;
        let last = self.executor.last_result().ok_or(SolverError::NoResult)?;
        if !last.is_sat() {
            return Err(SolverError::NotSat);
        }
        if names.is_empty() {
            return Ok(Vec::new());
        }
        let requests = self.named_value_requests(names)?;
        let output = self.executor.values_for_decoder(&requests);
        model_parse::parse_get_value_output(
            &output,
            &requests,
            self.terms(),
            self.executor.context(),
        )
        .ok_or_else(|| {
            SolverError::ModelGenerationFailed(
                "named get-value output is unavailable, malformed, ill-sorted or over budget"
                    .into(),
            )
        })
    }

    fn named_value_requests(&self, names: &[&str]) -> Result<Vec<(String, TermId)>, SolverError> {
        admit_names(names)?;
        let mut requests = Vec::new();
        requests
            .try_reserve_exact(names.len())
            .map_err(|_| invalid("request allocation refused"))?;
        let mut work = MAX_SORT_WORK;
        for &name in names {
            let (term, declared) = self
                .executor
                .context()
                .source_constant_for_value(name)
                .ok_or_else(|| invalid("name is not a unique live source constant"))?;
            // The frontend checked liveness without indexing first. Metadata
            // scans bound derived equality before it visits any recursive sort.
            let actual = self.terms().sort(term);
            matching_sorts(declared, actual, &mut work)
                .ok_or_else(|| invalid("declaration sort inspection or exact match refused"))?;
            // Echo the original constant, not an eager datatype constructor
            // DAG or its solver-invented fields. Quoting preserves identity.
            requests.push((quote_symbol(name), term));
        }
        Ok(requests)
    }
}

fn admit_names(names: &[&str]) -> Result<(), SolverError> {
    if names.len() > model_parse::MAX_GET_VALUE_TERMS {
        return Err(invalid("named value batch exceeds 4096 requests"));
    }
    let mut remaining = MAX_REQUEST_BYTES;
    for name in names {
        // Even every byte requiring escaping plus both quote delimiters fits
        // this bound. Charge the complete batch before any owned request text.
        let cost = name
            .len()
            .checked_mul(2)
            .and_then(|bytes| bytes.checked_add(2))
            .ok_or_else(|| invalid("request text size overflow"))?;
        remaining = remaining
            .checked_sub(cost)
            .ok_or_else(|| invalid("request text exceeds 8 MiB allowance"))?;
    }
    Ok(())
}

fn charge(work: &mut usize, amount: usize) -> Option<()> {
    *work = work.checked_sub(amount)?;
    Some(())
}

fn matching_sorts(declared: &Sort, actual: &Sort, work: &mut usize) -> Option<()> {
    admit_sort(declared, 0, work)?;
    admit_sort(actual, 0, work)?;
    (declared == actual).then_some(())
}

fn admit_sort(sort: &Sort, depth: usize, work: &mut usize) -> Option<()> {
    charge(work, 1)?;
    if depth > MAX_SORT_DEPTH {
        return None;
    }
    match sort {
        Sort::Bool | Sort::Int | Sort::Real | Sort::String => Some(()),
        Sort::BitVec(width) => (width.width > 0).then_some(()),
        Sort::FloatingPoint(exponent, significand) => {
            (*exponent >= 2 && *significand >= 2).then_some(())
        }
        Sort::Uninterpreted(name) => charge(work, name.len()),
        Sort::Array(array) => {
            admit_sort(&array.index_sort, depth + 1, work)?;
            admit_sort(&array.element_sort, depth + 1, work)
        }
        Sort::Seq(element) => admit_sort(element, depth + 1, work),
        Sort::Datatype(datatype) => {
            charge(work, datatype.name.len())?;
            for constructor in &datatype.constructors {
                charge(work, constructor.name.len().checked_add(1)?)?;
                for field in &constructor.fields {
                    charge(work, field.name.len().checked_add(1)?)?;
                    admit_sort(&field.sort, depth + 1, work)?;
                }
            }
            Some(())
        }
        _ => None,
    }
}

mod complete;

#[cfg(test)]
mod tests;
