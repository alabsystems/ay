// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use ay_core::Sort;

/// Refusal to decode a complete retained scalar-function model inventory.
#[derive(Debug, Clone, Copy, PartialEq, Eq, thiserror::Error)]
#[error("scalar function models are malformed, incomplete, unsupported or over budget")]
pub struct ScalarFunctionModelDecodeError;

/// An exactly decoded, closed total scalar function model.
///
/// The signature and every body node were checked, including all branches and
/// unused parameters. This is model data, not proof of SAT or source validity;
/// a consumer must still validate its complete pinned original obligation.
/// The model may come from native output or checked retained text; this type
/// does not by itself attest either origin or a particular solver invocation.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct ScalarFunctionModel {
    name: String,
    arguments: Vec<Sort>,
    result: Sort,
    definition: String,
}

impl ScalarFunctionModel {
    /// Decode complete retained definitions against the caller's declarations.
    ///
    /// Accepts exactly one `(model (define-fun ...) ...)` response. The decoded
    /// symbol/signature inventory must match `expected` exactly, including
    /// unused and nullary functions; extra, missing or duplicate definitions
    /// refuse the whole batch. Returned models follow `expected` order, not
    /// printed definition order, and each complete definition is canonicalized.
    /// All arguments are Bool/BV and results are BV; bodies must be closed,
    /// well-typed total expressions in the existing scalar decoder's grammar.
    ///
    /// Names are decoded symbols, not SMT expressions. At most 1024 functions
    /// are admitted. An allocation-free 8 MiB/128-depth lexical envelope and
    /// shared work/copy/output limits precede and constrain parsing; body depth
    /// is at most 64. Refusal returns no partial prefix or invented default.
    /// These are fixed admission bounds, not total RSS or latency guarantees.
    ///
    /// This method does not run a solver, authenticate the supplied source,
    /// attest native-model provenance, or mint a SAT/proof capability. Durable
    /// replay must bind declarations to its own retained source and freshly
    /// validate the complete original obligation with these definitions pinned.
    pub fn decode_smtlib(
        input: &str,
        expected: &[(&str, &[Sort], &Sort)],
    ) -> Result<Vec<Self>, ScalarFunctionModelDecodeError> {
        crate::api::model_parse::decode_scalar_function_models(input, expected)
            .ok_or(ScalarFunctionModelDecodeError)
    }

    pub(crate) fn from_decoded(
        name: String,
        arguments: Vec<Sort>,
        result: Sort,
        definition: String,
    ) -> Self {
        Self {
            name,
            arguments,
            result,
            definition,
        }
    }

    /// Decoded declaration symbol, without SMT quoting.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// Exact ordered scalar parameter sorts.
    pub fn arg_sorts(&self) -> &[Sort] {
        &self.arguments
    }

    /// Exact bitvector result sort.
    pub fn result_sort(&self) -> &Sort {
        &self.result
    }

    /// Canonical complete `define-fun`, with no trailing newline.
    ///
    /// All body references are lexical parameters or let bindings, never free
    /// globals. The body fixes every argument point, not just sampled calls.
    pub fn definition_smtlib(&self) -> &str {
        &self.definition
    }
}

#[cfg(test)]
mod tests;
