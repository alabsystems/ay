// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

//! Operation-local Rust raw words, not the `fp.to_ieee_bv` total-function extension.

mod construct;
mod nan;

use ay_bindings::{Expr, ExprValue, SortInner};
use ay_chc::ChcProblem;
use ay_core::original_query::WorkBudget;

use super::{
    build, source, typed, FpAdapterError, FpExprClauseEncoding, FpExprClauseSource,
    FpExprInputBinding,
};

/// Target-specific extra QUIET payload set from Rust's documented NaN rules.
/// The caller authenticates the actual target/ABI; this is not host detection,
/// a solver configuration flag, or permission to weaken an unknown target.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustNanPolicy {
    /// No extra payloads (e.g. x86/x86_64 and aarch64 in the cited Rust contract).
    NoExtra,
    /// Every quiet payload is an extra option (including unlisted targets).
    AllQuietPayloads,
    /// Only the all-one quiet payload is an extra option (sparc/sparc64).
    AllOnesQuietPayload,
    /// All quiet extras iff some original input NaN is not preferred (wasm).
    WasmConditional,
}

/// Supported same-format top-level arithmetic with Rust's RNE semantics.
/// `%` is explicitly truncating; IEEE `fp.rem` is not a substitute.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum RustFpArithmetic {
    Add,
    Subtract,
    Multiply,
    Divide,
    TruncatingRemainder,
    SquareRoot,
    FusedMultiplyAdd,
}

impl RustFpArithmetic {
    fn arity(self) -> usize {
        match self {
            Self::SquareRoot => 1,
            Self::FusedMultiplyAdd => 3,
            _ => 2,
        }
    }
}

/// Original raw operand provenance for ONE SSA execution.
/// Generic computed FP expressions, non-RNE casts, algebraic operators and
/// payload-losing intermediate aliases are deliberately not accepted by this API.
#[derive(Clone, Copy, Debug)]
pub enum FpRawOperation<'a> {
    Copy(&'a Expr),
    Negate(&'a Expr),
    AbsoluteValue(&'a Expr),
    /// Signed BV8..64 integer to FP32/64, literal RNE; output format follows the SSA word.
    SignedIntegerToFpRne(&'a Expr),
    /// Unsigned BV8..64 integer to FP32/64, literal RNE; no NaN choice or target policy.
    UnsignedIntegerToFpRne(&'a Expr),
    Arithmetic {
        operation: RustFpArithmetic,
        inputs: &'a [&'a Expr],
        nan_policy: RustNanPolicy,
    },
}

impl<'a> FpRawOperation<'a> {
    fn operands(self) -> impl Iterator<Item = &'a Expr> {
        let inputs = match self {
            Self::Copy(input)
            | Self::Negate(input)
            | Self::AbsoluteValue(input)
            | Self::SignedIntegerToFpRne(input)
            | Self::UnsignedIntegerToFpRne(input) => [Some(input), None, None],
            Self::Arithmetic { inputs, .. } => [
                inputs.first().copied(),
                inputs.get(1).copied(),
                inputs.get(2).copied(),
            ],
        };
        inputs.into_iter().flatten()
    }
}

/// One original BV32/64 SSA output Var and its operation-local relation.
/// Repeated observations reuse this Var, not a second descriptor. Independent
/// executions use distinct output Vars even when their operand Exprs coincide.
#[derive(Clone, Copy, Debug)]
pub struct FpRawResultRelation<'a> {
    pub operation: FpRawOperation<'a>,
    pub output: &'a Expr,
}

/// Lower all authored roots AND raw-result relations in one native construction.
///
/// Non-NaN words, integer RNE conversions and bitwise paths are exact.
/// Integer inputs retain their original BV leaf (or direct extract's base);
/// all admitted integers are finite and integer zero produces positive zero.
/// Arithmetic NaN sign is independent,
/// while quiet/payload choices follow the explicit documented policy and all
/// ORIGINAL raw operands. This is a relation, not a globally shared NaN function.
/// The caller retains SSA/target/source authentication and must carry raw output
/// Vars unchanged through predicate/state/head arguments across rules. It may
/// not project outputs or choose a favourable payload to turn Unsafe into Safe.
/// No native answer, model, Rust replay or source credential is supplied here.
pub fn lower_fp_raw_result_clause<'a, 'budget, 'owner>(
    roots: &'a [Expr],
    results: &'a [FpRawResultRelation<'a>],
    bindings: &'a [FpExprInputBinding<'a>],
    namespace: &'a ChcProblem,
    budget: &'budget mut WorkBudget<'owner>,
) -> Result<FpExprClauseEncoding<'a, 'budget, 'owner>, FpAdapterError> {
    budget.charge(0)?;
    let result = lower(roots, results, bindings, namespace, budget);
    // The helper drops all synthetic Expr/root/census/arena scratch first.
    budget.charge(0)?;
    let data = result?;
    Ok(FpExprClauseEncoding {
        data,
        source: FpExprClauseSource {
            roots,
            bindings,
            namespace,
            raw_results: results,
        },
        budget,
    })
}

fn lower(
    roots: &[Expr],
    results: &[FpRawResultRelation<'_>],
    bindings: &[FpExprInputBinding<'_>],
    namespace: &ChcProblem,
    budget: &mut WorkBudget<'_>,
) -> Result<ay_chc::fp_adapter::FpClauseData, FpAdapterError> {
    prepay(roots.len(), results.len(), bindings.len(), budget)?;
    let mut combined = Vec::new();
    combined
        .try_reserve_exact(roots.len() + results.len())
        .map_err(|_| budget.refuse_exhaustion())?;
    for root in roots {
        budget.charge(0)?;
        if typed::scalar(root)? != typed::Scalar::Bool {
            return Err(FpAdapterError::Invalid(
                "raw-result authored root is not Bool",
            ));
        }
        combined.push(root.clone());
    }
    for (index, result) in results.iter().enumerate() {
        budget.charge(0)?;
        let width = validate(result, index, results, bindings)?;
        combined.push(construct::relation(result, width)?);
    }
    let data = build::lower(&combined, bindings, namespace, budget);
    drop(combined);
    budget.charge(0)?;
    data
}

fn prepay(r: usize, n: usize, b: usize, budget: &mut WorkBudget<'_>) -> Result<(), FpAdapterError> {
    if n == 0
        || r > source::MAX_NODES
        || n > source::MAX_NODES
        || b > source::MAX_NODES
        || r.checked_add(n)
            .is_none_or(|total| total > source::MAX_NODES)
    {
        return Err(FpAdapterError::Unsupported("raw-result population"));
    }
    // Independent constructor/scratch fee, not native/translator fee reuse.
    let work = n
        .checked_mul(n + b)
        .and_then(|v| v.checked_mul(1024))
        .and_then(|v| n.checked_mul(262_144).and_then(|w| v.checked_add(w)))
        .and_then(|v| r.checked_mul(1024).and_then(|w| v.checked_add(w)))
        .and_then(|v| v.checked_add(65_536))
        .ok_or_else(|| budget.refuse_exhaustion())?;
    let bytes = n
        .checked_mul(1_048_576)
        .and_then(|v| r.checked_mul(128).and_then(|w| v.checked_add(w)))
        .and_then(|v| v.checked_add(65_536))
        .ok_or_else(|| budget.refuse_exhaustion())?;
    budget.admit(work, bytes)?;
    if std::mem::size_of::<usize>() > 8
        || std::mem::size_of::<Expr>() > 64
        || std::mem::size_of::<ExprValue>() > 256
        || std::mem::size_of::<SortInner>() > 256
        || std::mem::align_of::<ExprValue>() > 16
        || std::mem::align_of::<SortInner>() > 16
    {
        return Err(FpAdapterError::Unsupported(
            "raw-result logical layout envelope",
        ));
    }
    Ok(())
}

fn validate(
    result: &FpRawResultRelation<'_>,
    index: usize,
    all: &[FpRawResultRelation<'_>],
    bindings: &[FpExprInputBinding<'_>],
) -> Result<u32, FpAdapterError> {
    let width = raw_word(result.output)?;
    if !matches!(result.output.value(), ExprValue::Var { .. })
        || !bindings
            .iter()
            .any(|b| source::identity(b.source) == source::identity(result.output))
        || all[..index]
            .iter()
            .any(|r| source::identity(r.output) == source::identity(result.output))
    {
        return Err(FpAdapterError::Invalid(
            "raw-result missing/duplicate SSA output Var",
        ));
    }
    if let FpRawOperation::Arithmetic {
        operation, inputs, ..
    } = result.operation
    {
        if inputs.len() != operation.arity() {
            return Err(FpAdapterError::Invalid("raw-result arithmetic arity"));
        }
    }
    for input in result.operation.operands() {
        let original = match result.operation {
            FpRawOperation::SignedIntegerToFpRne(_) | FpRawOperation::UnsignedIntegerToFpRne(_) => {
                numeric_operand(input)?
            }
            _ => {
                if raw_word(input)? != width {
                    return Err(FpAdapterError::Invalid("raw-result operand width"));
                }
                input
            }
        };
        if all[index..]
            .iter()
            .any(|r| source::identity(r.output) == source::identity(original))
        {
            return Err(FpAdapterError::Invalid(
                "raw-result cyclic/nonpreceding SSA input",
            ));
        }
    }
    Ok(width)
}

// Return the original base identity, never a slice alias, for the SSA fence.
fn numeric_operand(expr: &Expr) -> Result<&Expr, FpAdapterError> {
    if !matches!(typed::scalar(expr)?, typed::Scalar::Bv(8..=64)) {
        return Err(FpAdapterError::Unsupported("raw-result integer width"));
    }
    let original = match expr.value() {
        ExprValue::Var { .. } | ExprValue::BitVecConst { .. } => expr,
        ExprValue::BvExtract { expr: base, .. } => base,
        _ => return Err(FpAdapterError::Unsupported("raw-result compound integer")),
    };
    // Existing typed admission checks the complete extract range and permits
    // only an original BV32/64 leaf base; canonical constants are checked too.
    typed::describe(expr)?;
    typed::describe(original)?;
    Ok(original)
}

fn raw_word(expr: &Expr) -> Result<u32, FpAdapterError> {
    let width = match typed::scalar(expr)? {
        typed::Scalar::Bv(w @ (32 | 64)) => w,
        _ => return Err(FpAdapterError::Unsupported("raw-result word format")),
    };
    if !matches!(
        expr.value(),
        ExprValue::Var { .. } | ExprValue::BitVecConst { .. }
    ) {
        return Err(FpAdapterError::Unsupported("raw-result compound operand"));
    }
    typed::describe(expr)?;
    Ok(width)
}
