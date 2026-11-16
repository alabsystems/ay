// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Thin adapter dispatching array-containing SMT queries to ay-dpll's Executor.
//!
//! When the CHC solver's internal DPLL(T) loop (`check_sat.rs`) encounters
//! formulas with array operations (select, store, const-array), the loop lacks
//! proper array axiom generation and returns Unknown. This adapter converts the
//! ChcExpr to SMT-LIB text and delegates to ay-dpll's Executor, which has full
//! array theory support (eager axioms, extensionality, ROW lemmas, N-O fixpoint).
//!
//! Design: the development design notes
//! Approach C — thin adapter, array logics only.

mod interrupt_observer;
pub(crate) use interrupt_observer::InterruptObserver;
mod logic_detection;
mod model_parsing;
mod replay_cancellation;
mod replay_limit;
mod replay_memory;
mod strict_unsat;
mod verdict_only;
pub(crate) use verdict_only::ScopedVerdictOnlySearch;
#[cfg(test)]
pub(crate) use verdict_only::{shed_search_executors_built, verdict_only_search_active};

// Re-export for sibling modules (persistent.rs) and crate-level re-export (smt/mod.rs #7983).
#[cfg(test)]
use logic_detection::collect_dt_declarations;
pub(crate) use logic_detection::{
    collect_dt_declarations_for_expr, collect_dt_declarations_for_exprs,
    collect_uninterpreted_function_applications_for_exprs,
    collect_uninterpreted_function_declarations,
    collect_uninterpreted_function_declarations_for_exprs,
    collect_uninterpreted_function_declarations_for_problem, detect_logic, emit_declare_datatypes,
    emit_declare_uninterpreted_function, quote_symbol, sort_to_smtlib,
    UninterpretedFunctionDeclaration,
};
#[cfg(test)]
pub(super) use logic_detection::{
    collect_uninterpreted_function_applications, emit_declare_datatype,
};
pub(crate) use model_parsing::parse_model_into;
pub(crate) use replay_cancellation::ReplayCancellation;
pub(crate) use replay_limit::ReplayLimit;
#[cfg(test)]
pub(crate) use strict_unsat::smtlib_strict_unsat_cert_via_executor_until;
pub(crate) use strict_unsat::{
    check_plain_unsat_native_with_limit, check_plain_unsat_retained_native_with_progress,
    BoundRetainedProofBytes, RetainedReplayProgress,
};

// Re-export test-visible helpers (tests.rs uses super::*).
#[cfg(test)]
pub(super) use model_parsing::{
    parse_decimal_to_rational, parse_model_simple, parse_simple_value, term_body_to_smt_value,
};

use super::context::{SmtContext, SmtLane};
use super::executor_sort_guard::unsupported_executor_expr_reason;
use super::model_verify::verify_sat_model_conjunction_strict_with_mod_retry;
use super::types::{ModelVerifyResult, SmtResult, SmtValue};
use crate::pdr::model::InvariantModel;
use crate::{ChcExpr, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;
use replay_memory::ReplayMemory;
use std::panic::AssertUnwindSafe;

/// One fresh scalar constant constrained to equal an ordinary-UF application.
///
/// The executor prints declared constants in `(get-model)`, while its model
/// printer intentionally emits (and our parser intentionally skips) a
/// parameterized function definition.  These finite observation aliases let
/// SAT validation recover the value of every application that actually occurs
/// in the query without attempting to interpret an arbitrary function body.
#[derive(Clone, Debug)]
pub(crate) struct UfApplicationAlias {
    alias: String,
    application: ChcExpr,
}

/// Why finite-UF observation aliases could not be emitted safely.
#[derive(Debug, PartialEq, Eq, thiserror::Error)]
pub(crate) enum UfApplicationAliasEmissionError {
    #[error("executor UF alias emission resource limit exceeded: {0}")]
    ResourceLimit(&'static str),
    #[error("executor UF alias emission deadline expired")]
    DeadlineExpired,
    #[error("executor array lambda has mismatched capture sorts")]
    InvalidArrayLambda,
}

#[derive(Clone, Copy)]
struct UfApplicationAliasEmissionLimits {
    emitted_bytes: usize,
    serializer_work: usize,
}

impl UfApplicationAliasEmissionLimits {
    const PRODUCTION: Self = Self {
        emitted_bytes: logic_detection::MAX_EXECUTOR_UF_ALIAS_EMITTED_BYTES,
        serializer_work: logic_detection::MAX_EXECUTOR_UF_ALIAS_EMIT_WORK,
    };
}

fn scalar_uf_sort(sort: &ChcSort) -> bool {
    matches!(
        sort,
        ChcSort::Bool | ChcSort::Int | ChcSort::Real | ChcSort::BitVec(_)
    )
}

fn collect_expr_symbol_names<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
) -> Result<FxHashSet<String>, String> {
    let mut names = FxHashSet::default();
    let mut stack = Vec::new();
    for expr in exprs {
        if stack.len() >= logic_detection::MAX_EXECUTOR_EXPR_ROOTS {
            return Err(
                "executor expression root cap exceeded while collecting symbols".to_string(),
            );
        }
        stack.push(expr);
    }
    let mut nodes = 0usize;
    let mut name_bytes = 0usize;
    // Charge each distinct node once, including closed lambda code.
    let mut visited: FxHashSet<usize> = FxHashSet::default();
    while let Some(expr) = stack.pop() {
        if !visited.insert(logic_detection::expr_key(expr)) {
            continue;
        }
        nodes = nodes
            .checked_add(1)
            .filter(|count| *count <= logic_detection::MAX_DT_EXPR_NODES)
            .ok_or_else(|| {
                "executor expression node cap exceeded while collecting symbols".to_string()
            })?;
        match expr {
            ChcExpr::Var(var) => collect_symbol_name(&var.name, &mut names, &mut name_bytes)?,
            ChcExpr::PredicateApp(name, _, _) | ChcExpr::FuncApp(name, _, _) => {
                collect_symbol_name(name, &mut names, &mut name_bytes)?;
            }
            ChcExpr::ArrayLambda(lambda) => {
                for variable in std::iter::once(lambda.binder()).chain(lambda.formals()) {
                    collect_symbol_name(&variable.name, &mut names, &mut name_bytes)?;
                }
            }
            _ => {}
        }
        let children = logic_detection::expr_children(expr);
        if nodes
            .checked_add(stack.len())
            .and_then(|pending| pending.checked_add(children.len()))
            .is_none_or(|pending| pending > logic_detection::MAX_DT_EXPR_NODES)
        {
            return Err(
                "executor expression node cap exceeded while collecting symbols".to_string(),
            );
        }
        stack.extend(children.iter().map(AsRef::as_ref));
    }
    Ok(names)
}

fn collect_symbol_name(
    name: &str,
    names: &mut FxHashSet<String>,
    bytes: &mut usize,
) -> Result<(), String> {
    *bytes = bytes
        .checked_add(name.len())
        .filter(|bytes| *bytes <= logic_detection::MAX_EXECUTOR_SURFACE_NAME_BYTES)
        .ok_or_else(|| {
            "executor symbol name-byte cap exceeded while collecting symbols".to_string()
        })?;
    names.insert(name.to_string());
    Ok(())
}

/// Allocate fresh, query-local aliases for every syntactic scalar-UF
/// application in `exprs`.  `next_alias` is monotonic for persistent sessions;
/// standalone callers may seed it with zero.
pub(crate) fn build_uf_application_aliases<'a>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    next_alias: &mut usize,
) -> Result<Vec<UfApplicationAlias>, String> {
    build_uf_application_aliases_avoiding(exprs, next_alias, std::iter::empty::<&'static str>())
}

/// Persistent executor sessions retain declarations across `pop`. Avoid every
/// symbol already declared in that session in addition to names in this query;
/// otherwise a user constant from an earlier query can collide with a later
/// finite-UF observation alias and spuriously force the session to `Unknown`.
pub(crate) fn build_uf_application_aliases_avoiding<'a, 'b>(
    exprs: impl IntoIterator<Item = &'a ChcExpr>,
    next_alias: &mut usize,
    previously_declared: impl IntoIterator<Item = &'b str>,
) -> Result<Vec<UfApplicationAlias>, String> {
    let mut roots = Vec::new();
    for expr in exprs {
        if roots.len() >= logic_detection::MAX_EXECUTOR_EXPR_ROOTS {
            return Err(
                "executor expression root cap exceeded while building UF aliases".to_string(),
            );
        }
        roots.push(expr);
    }
    let applications = collect_uninterpreted_function_applications_for_exprs(roots.iter().copied())
        .map_err(|error| error.to_string())?;
    let mut occupied = collect_expr_symbol_names(roots.iter().copied())?;
    let mut occupied_name_bytes = occupied.iter().try_fold(0usize, |bytes, name| {
        bytes
            .checked_add(name.len())
            .filter(|total| *total <= logic_detection::MAX_EXECUTOR_SURFACE_NAME_BYTES)
            .ok_or_else(|| "executor occupied-symbol name-byte cap exceeded".to_string())
    })?;
    for name in previously_declared {
        occupied_name_bytes = occupied_name_bytes
            .checked_add(name.len())
            .filter(|bytes| *bytes <= logic_detection::MAX_EXECUTOR_SURFACE_NAME_BYTES)
            .ok_or_else(|| "executor occupied-symbol name-byte cap exceeded".to_string())?;
        if occupied.len() >= logic_detection::MAX_DT_EXPR_NODES && !occupied.contains(name) {
            return Err("executor occupied-symbol count cap exceeded".to_string());
        }
        occupied.insert(name.to_owned());
    }
    let mut aliases = Vec::with_capacity(applications.len());
    for application in applications {
        let ChcExpr::FuncApp(_, return_sort, args) = &application else {
            return Err("ordinary-UF application collector returned a non-application".to_string());
        };
        if !scalar_uf_sort(return_sort) || !args.iter().all(|arg| scalar_uf_sort(&arg.sort())) {
            return Err(
                "finite UF application model extraction supports scalar signatures only"
                    .to_string(),
            );
        }
        let alias = loop {
            let candidate = format!("ay!uf!value!{}", *next_alias);
            *next_alias = (*next_alias)
                .checked_add(1)
                .ok_or_else(|| "executor UF alias counter exhausted".to_string())?;
            if !occupied.contains(&candidate) {
                occupied_name_bytes = occupied_name_bytes
                    .checked_add(candidate.len())
                    .filter(|bytes| *bytes <= logic_detection::MAX_EXECUTOR_SURFACE_NAME_BYTES)
                    .ok_or_else(|| "executor occupied-symbol name-byte cap exceeded".to_string())?;
                occupied.insert(candidate.clone());
                break candidate;
            }
        };
        aliases.push(UfApplicationAlias { alias, application });
    }
    Ok(aliases)
}

/// Emit aliases before the query assertions that use them.
///
/// Alias collection admits the original expression DAG once, but an application
/// at every level of a nested UF chain is an observation point. Naively
/// serializing every full prefix therefore repeats both node visits and source
/// names quadratically. Bound those repeated costs independently before the
/// generated script can amplify a route-admitted query by hundreds of MiB.
pub(crate) fn emit_uf_application_aliases(
    aliases: &[UfApplicationAlias],
    deadline: Option<ay_core::time::Instant>,
) -> Result<String, UfApplicationAliasEmissionError> {
    emit_uf_application_aliases_with_limits(
        aliases,
        deadline,
        UfApplicationAliasEmissionLimits::PRODUCTION,
    )
}

fn alias_emission_deadline_expired(deadline: Option<ay_core::time::Instant>) -> bool {
    crate::smt::smt_deadline_expired()
        || deadline.is_some_and(|limit| ay_core::time::Instant::now() >= limit)
        || crate::smt::current_thread_solve_deadline()
            .is_some_and(|limit| ay_core::time::Instant::now() >= limit)
}

enum UfAliasSmtPart<'a> {
    Expr(&'a ChcExpr),
    Argument(&'a ChcExpr),
    Lambda(&'a crate::expr::ChcArrayLambda),
    Capture(&'a ChcVar, &'a ChcExpr),
    Text(&'static str),
    Close,
}

fn uf_alias_operator_smtlib(operator: &crate::ChcOp) -> std::borrow::Cow<'static, str> {
    use crate::ChcOp;
    use std::borrow::Cow;

    match operator {
        ChcOp::Not => Cow::Borrowed("not"),
        ChcOp::And => Cow::Borrowed("and"),
        ChcOp::Or => Cow::Borrowed("or"),
        ChcOp::Implies => Cow::Borrowed("=>"),
        ChcOp::Iff | ChcOp::Eq => Cow::Borrowed("="),
        ChcOp::Add => Cow::Borrowed("+"),
        ChcOp::Sub | ChcOp::Neg => Cow::Borrowed("-"),
        ChcOp::Mul => Cow::Borrowed("*"),
        ChcOp::Div => Cow::Borrowed("div"),
        ChcOp::Mod => Cow::Borrowed("mod"),
        ChcOp::Ne => Cow::Borrowed("distinct"),
        ChcOp::Lt => Cow::Borrowed("<"),
        ChcOp::Le => Cow::Borrowed("<="),
        ChcOp::Gt => Cow::Borrowed(">"),
        ChcOp::Ge => Cow::Borrowed(">="),
        ChcOp::Ite => Cow::Borrowed("ite"),
        ChcOp::Select => Cow::Borrowed("select"),
        ChcOp::Store => Cow::Borrowed("store"),
        ChcOp::BvAdd => Cow::Borrowed("bvadd"),
        ChcOp::BvSub => Cow::Borrowed("bvsub"),
        ChcOp::BvMul => Cow::Borrowed("bvmul"),
        ChcOp::BvUDiv => Cow::Borrowed("bvudiv"),
        ChcOp::BvURem => Cow::Borrowed("bvurem"),
        ChcOp::BvSDiv => Cow::Borrowed("bvsdiv"),
        ChcOp::BvSRem => Cow::Borrowed("bvsrem"),
        ChcOp::BvSMod => Cow::Borrowed("bvsmod"),
        ChcOp::BvAnd => Cow::Borrowed("bvand"),
        ChcOp::BvOr => Cow::Borrowed("bvor"),
        ChcOp::BvXor => Cow::Borrowed("bvxor"),
        ChcOp::BvNand => Cow::Borrowed("bvnand"),
        ChcOp::BvNor => Cow::Borrowed("bvnor"),
        ChcOp::BvXnor => Cow::Borrowed("bvxnor"),
        ChcOp::BvNot => Cow::Borrowed("bvnot"),
        ChcOp::BvNeg => Cow::Borrowed("bvneg"),
        ChcOp::BvShl => Cow::Borrowed("bvshl"),
        ChcOp::BvLShr => Cow::Borrowed("bvlshr"),
        ChcOp::BvAShr => Cow::Borrowed("bvashr"),
        ChcOp::BvULt => Cow::Borrowed("bvult"),
        ChcOp::BvULe => Cow::Borrowed("bvule"),
        ChcOp::BvUGt => Cow::Borrowed("bvugt"),
        ChcOp::BvUGe => Cow::Borrowed("bvuge"),
        ChcOp::BvSLt => Cow::Borrowed("bvslt"),
        ChcOp::BvSLe => Cow::Borrowed("bvsle"),
        ChcOp::BvSGt => Cow::Borrowed("bvsgt"),
        ChcOp::BvSGe => Cow::Borrowed("bvsge"),
        ChcOp::BvComp => Cow::Borrowed("bvcomp"),
        ChcOp::BvConcat => Cow::Borrowed("concat"),
        ChcOp::Bv2Nat => Cow::Borrowed("bv2nat"),
        ChcOp::BvExtract(high, low) => Cow::Owned(format!("(_ extract {high} {low})")),
        ChcOp::BvZeroExtend(width) => Cow::Owned(format!("(_ zero_extend {width})")),
        ChcOp::BvSignExtend(width) => Cow::Owned(format!("(_ sign_extend {width})")),
        ChcOp::BvRotateLeft(width) => Cow::Owned(format!("(_ rotate_left {width})")),
        ChcOp::BvRotateRight(width) => Cow::Owned(format!("(_ rotate_right {width})")),
        ChcOp::BvRepeat(width) => Cow::Owned(format!("(_ repeat {width})")),
        ChcOp::Int2Bv(width) => Cow::Owned(format!("(_ int2bv {width})")),
    }
}

struct BoundedUfAliasScript {
    text: String,
    emitted_bytes_limit: usize,
}

impl BoundedUfAliasScript {
    fn new(emitted_bytes_limit: usize) -> Self {
        Self {
            text: String::new(),
            emitted_bytes_limit,
        }
    }

    fn push_str(&mut self, text: &str) -> Result<(), UfApplicationAliasEmissionError> {
        if self
            .text
            .len()
            .checked_add(text.len())
            .is_none_or(|bytes| bytes > self.emitted_bytes_limit)
        {
            return Err(UfApplicationAliasEmissionError::ResourceLimit(
                "emitted bytes",
            ));
        }
        self.text.push_str(text);
        Ok(())
    }

    fn push_char(&mut self, character: char) -> Result<(), UfApplicationAliasEmissionError> {
        let mut encoded = [0u8; 4];
        self.push_str(character.encode_utf8(&mut encoded))
    }

    fn charge_work(
        serializer_work: &mut usize,
        serializer_work_limit: usize,
        deadline: Option<ay_core::time::Instant>,
    ) -> Result<(), UfApplicationAliasEmissionError> {
        *serializer_work = serializer_work
            .checked_add(1)
            .filter(|next| *next <= serializer_work_limit)
            .ok_or(UfApplicationAliasEmissionError::ResourceLimit(
                "serializer work",
            ))?;
        if (*serializer_work == 1 || *serializer_work % 1_024 == 0)
            && alias_emission_deadline_expired(deadline)
        {
            return Err(UfApplicationAliasEmissionError::DeadlineExpired);
        }
        Ok(())
    }

    fn charge_sort_work(
        root: &ChcSort,
        serializer_work: &mut usize,
        serializer_work_limit: usize,
        deadline: Option<ay_core::time::Instant>,
    ) -> Result<(), UfApplicationAliasEmissionError> {
        let mut stack = vec![root];
        while let Some(sort) = stack.pop() {
            Self::charge_work(serializer_work, serializer_work_limit, deadline)?;
            if let ChcSort::Array(key, value) = sort {
                stack.push(value);
                stack.push(key);
            }
        }
        Ok(())
    }

    fn schedule_expr_sort_operator_dependencies<'a>(
        operator: &crate::ChcOp,
        arguments: &'a [std::sync::Arc<ChcExpr>],
        stack: &mut Vec<&'a ChcExpr>,
    ) {
        use crate::ChcOp;

        match operator {
            ChcOp::Add
            | ChcOp::Sub
            | ChcOp::Mul
            | ChcOp::Div
            | ChcOp::Mod
            | ChcOp::Neg
            | ChcOp::Select
            | ChcOp::Store
            | ChcOp::BvAdd
            | ChcOp::BvSub
            | ChcOp::BvMul
            | ChcOp::BvUDiv
            | ChcOp::BvURem
            | ChcOp::BvSDiv
            | ChcOp::BvSRem
            | ChcOp::BvSMod
            | ChcOp::BvAnd
            | ChcOp::BvOr
            | ChcOp::BvXor
            | ChcOp::BvNand
            | ChcOp::BvNor
            | ChcOp::BvXnor
            | ChcOp::BvNot
            | ChcOp::BvNeg
            | ChcOp::BvShl
            | ChcOp::BvLShr
            | ChcOp::BvAShr
            | ChcOp::BvRotateLeft(_)
            | ChcOp::BvRotateRight(_) => {
                stack.extend(arguments.first().map(AsRef::as_ref));
            }
            ChcOp::Ite => stack.extend(arguments.get(1).map(AsRef::as_ref)),
            ChcOp::BvConcat => {
                // Malformed operands make `sort()` inspect the first operand
                // again on its fallback path.
                stack.extend(arguments.first().map(AsRef::as_ref));
                stack.extend(arguments.get(1).map(AsRef::as_ref));
                stack.extend(arguments.first().map(AsRef::as_ref));
            }
            ChcOp::BvZeroExtend(_) | ChcOp::BvSignExtend(_) | ChcOp::BvRepeat(_) => {
                // These also retry the first operand on a malformed
                // non-bitvector input.
                stack.extend(arguments.first().map(AsRef::as_ref));
                stack.extend(arguments.first().map(AsRef::as_ref));
            }
            ChcOp::Not
            | ChcOp::And
            | ChcOp::Or
            | ChcOp::Implies
            | ChcOp::Iff
            | ChcOp::Eq
            | ChcOp::Ne
            | ChcOp::Lt
            | ChcOp::Le
            | ChcOp::Gt
            | ChcOp::Ge
            | ChcOp::BvULt
            | ChcOp::BvULe
            | ChcOp::BvUGt
            | ChcOp::BvUGe
            | ChcOp::BvSLt
            | ChcOp::BvSLe
            | ChcOp::BvSGt
            | ChcOp::BvSGe
            | ChcOp::BvComp
            | ChcOp::Bv2Nat
            | ChcOp::BvExtract(_, _)
            | ChcOp::Int2Bv(_) => {}
        }
    }

    fn charge_expr_sort_work(
        root: &ChcExpr,
        serializer_work: &mut usize,
        serializer_work_limit: usize,
        deadline: Option<ay_core::time::Instant>,
    ) -> Result<(), UfApplicationAliasEmissionError> {
        let mut stack = vec![root];
        while let Some(expr) = stack.pop() {
            Self::charge_work(serializer_work, serializer_work_limit, deadline)?;
            match expr {
                ChcExpr::Var(variable) => Self::charge_sort_work(
                    &variable.sort,
                    serializer_work,
                    serializer_work_limit,
                    deadline,
                )?,
                ChcExpr::FuncApp(_, sort, _) => {
                    Self::charge_sort_work(sort, serializer_work, serializer_work_limit, deadline)?
                }
                ChcExpr::Op(operator, arguments) => {
                    Self::schedule_expr_sort_operator_dependencies(operator, arguments, &mut stack);
                }
                ChcExpr::ArrayLambda(lambda) => {
                    Self::charge_sort_work(
                        &lambda.binder().sort,
                        serializer_work,
                        serializer_work_limit,
                        deadline,
                    )?;
                    stack.push(lambda.body());
                }
                ChcExpr::ConstArray(key_sort, value) => {
                    Self::charge_sort_work(
                        key_sort,
                        serializer_work,
                        serializer_work_limit,
                        deadline,
                    )?;
                    stack.push(value);
                }
                ChcExpr::Bool(_)
                | ChcExpr::Int(_)
                | ChcExpr::Real(_, _)
                | ChcExpr::BitVec(_, _)
                | ChcExpr::PredicateApp(_, _, _)
                | ChcExpr::ConstArrayMarker(_)
                | ChcExpr::IsTesterMarker(_) => {}
            }
        }
        Ok(())
    }

    fn schedule_arguments<'a>(
        stack: &mut Vec<UfAliasSmtPart<'a>>,
        arguments: &'a [std::sync::Arc<ChcExpr>],
    ) {
        stack.push(UfAliasSmtPart::Close);
        stack.extend(
            arguments
                .iter()
                .rev()
                .map(|argument| UfAliasSmtPart::Argument(argument.as_ref())),
        );
    }

    fn write_named_application<'a>(
        &mut self,
        name: &str,
        arguments: &'a [std::sync::Arc<ChcExpr>],
        stack: &mut Vec<UfAliasSmtPart<'a>>,
    ) -> Result<(), UfApplicationAliasEmissionError> {
        if arguments.is_empty() {
            self.push_str(name)
        } else {
            self.push_char('(')?;
            self.push_str(name)?;
            Self::schedule_arguments(stack, arguments);
            Ok(())
        }
    }

    fn write_operator_application<'a>(
        &mut self,
        operator: &str,
        arguments: &'a [std::sync::Arc<ChcExpr>],
        stack: &mut Vec<UfAliasSmtPart<'a>>,
    ) -> Result<(), UfApplicationAliasEmissionError> {
        self.push_char('(')?;
        self.push_str(operator)?;
        if arguments.is_empty() {
            // Preserve `InvariantModel::expr_to_smtlib`'s historical zero-arity
            // operator spelling, which includes the separator before `)`.
            self.push_char(' ')?;
        }
        Self::schedule_arguments(stack, arguments);
        Ok(())
    }

    fn write_array_lambda<'a>(
        &mut self,
        lambda: &'a crate::expr::ChcArrayLambda,
        stack: &mut Vec<UfAliasSmtPart<'a>>,
        serializer_work: &mut usize,
        serializer_work_limit: usize,
        deadline: Option<ay_core::time::Instant>,
    ) -> Result<(), UfApplicationAliasEmissionError> {
        for value in lambda.captures() {
            Self::charge_expr_sort_work(value, serializer_work, serializer_work_limit, deadline)?;
        }
        if !lambda.captures_are_well_typed() {
            return Err(UfApplicationAliasEmissionError::InvalidArrayLambda);
        }
        if lambda.captures().is_empty() {
            stack.push(UfAliasSmtPart::Lambda(lambda));
        } else {
            self.push_str("(let (")?;
            stack.push(UfAliasSmtPart::Close);
            stack.push(UfAliasSmtPart::Lambda(lambda));
            stack.push(UfAliasSmtPart::Text(") "));
            for (formal, value) in lambda.formals().iter().zip(lambda.captures()).rev() {
                stack.push(UfAliasSmtPart::Capture(formal, value));
            }
        }
        Ok(())
    }

    fn write_const_array<'a>(
        &mut self,
        key_sort: &ChcSort,
        value: &'a std::sync::Arc<ChcExpr>,
        stack: &mut Vec<UfAliasSmtPart<'a>>,
        serializer_work: &mut usize,
        serializer_work_limit: usize,
        deadline: Option<ay_core::time::Instant>,
    ) -> Result<(), UfApplicationAliasEmissionError> {
        // The established spelling asks `ChcExpr::sort()` for the
        // value sort. Account for the key-sort rendering, that hidden
        // recursive walk, and the value-sort rendering before doing
        // any of those operations.
        Self::charge_sort_work(key_sort, serializer_work, serializer_work_limit, deadline)?;
        Self::charge_expr_sort_work(value, serializer_work, serializer_work_limit, deadline)?;
        let value_sort = value.sort();
        if alias_emission_deadline_expired(deadline) {
            return Err(UfApplicationAliasEmissionError::DeadlineExpired);
        }
        Self::charge_sort_work(
            &value_sort,
            serializer_work,
            serializer_work_limit,
            deadline,
        )?;
        self.push_str("((as const (Array ")?;
        self.push_str(&key_sort.to_string())?;
        self.push_char(' ')?;
        self.push_str(&value_sort.to_string())?;
        self.push_str("))")?;
        stack.push(UfAliasSmtPart::Close);
        stack.push(UfAliasSmtPart::Argument(value.as_ref()));
        Ok(())
    }

    fn write_expr_node<'a>(
        &mut self,
        expr: &'a ChcExpr,
        stack: &mut Vec<UfAliasSmtPart<'a>>,
        serializer_work: &mut usize,
        serializer_work_limit: usize,
        deadline: Option<ay_core::time::Instant>,
    ) -> Result<(), UfApplicationAliasEmissionError> {
        match expr {
            ChcExpr::Bool(true) => self.push_str("true"),
            ChcExpr::Bool(false) => self.push_str("false"),
            ChcExpr::Int(value) if *value < 0 => {
                self.push_str("(- ")?;
                self.push_str(&value.unsigned_abs().to_string())?;
                self.push_char(')')
            }
            ChcExpr::Int(value) => self.push_str(&value.to_string()),
            ChcExpr::Real(numerator, denominator) if *numerator < 0 => {
                self.push_str("(/ (- ")?;
                self.push_str(&numerator.unsigned_abs().to_string())?;
                self.push_str(") ")?;
                self.push_str(&denominator.to_string())?;
                self.push_char(')')
            }
            ChcExpr::Real(numerator, denominator) => {
                self.push_str("(/ ")?;
                self.push_str(&numerator.to_string())?;
                self.push_char(' ')?;
                self.push_str(&denominator.to_string())?;
                self.push_char(')')
            }
            ChcExpr::BitVec(value, width) => {
                self.push_str("(_ bv")?;
                self.push_str(&value.to_string())?;
                self.push_char(' ')?;
                self.push_str(&width.to_string())?;
                self.push_char(')')
            }
            ChcExpr::Var(variable) => self.push_str(&quote_symbol(&variable.name)),
            ChcExpr::PredicateApp(name, _, arguments) => {
                self.write_named_application(&quote_symbol(name), arguments, stack)
            }
            ChcExpr::FuncApp(name, sort, arguments) => {
                let qualified_name = match sort {
                    ChcSort::Uninterpreted(sort_name)
                    | ChcSort::Datatype {
                        name: sort_name, ..
                    } => format!("(as {} {})", quote_symbol(name), quote_symbol(sort_name)),
                    _ => quote_symbol(name),
                };
                self.write_named_application(&qualified_name, arguments, stack)
            }
            ChcExpr::Op(operator, arguments) => {
                let operator = uf_alias_operator_smtlib(operator);
                self.write_operator_application(operator.as_ref(), arguments, stack)
            }
            ChcExpr::ConstArrayMarker(_) => self.push_str("(as const)"),
            ChcExpr::IsTesterMarker(name) => {
                self.push_str("(_ is ")?;
                self.push_str(&quote_symbol(name))?;
                self.push_char(')')
            }
            ChcExpr::ArrayLambda(lambda) => self.write_array_lambda(
                lambda,
                stack,
                serializer_work,
                serializer_work_limit,
                deadline,
            ),
            ChcExpr::ConstArray(key_sort, value) => self.write_const_array(
                key_sort,
                value,
                stack,
                serializer_work,
                serializer_work_limit,
                deadline,
            ),
        }
    }

    fn write_expr(
        &mut self,
        root: &ChcExpr,
        serializer_work: &mut usize,
        serializer_work_limit: usize,
        deadline: Option<ay_core::time::Instant>,
    ) -> Result<(), UfApplicationAliasEmissionError> {
        let mut stack = vec![UfAliasSmtPart::Expr(root)];
        while let Some(part) = stack.pop() {
            let expr = match part {
                UfAliasSmtPart::Argument(expr) => {
                    self.push_char(' ')?;
                    expr
                }
                UfAliasSmtPart::Expr(expr) => expr,
                UfAliasSmtPart::Lambda(lambda) => {
                    Self::charge_work(serializer_work, serializer_work_limit, deadline)?;
                    Self::charge_sort_work(
                        &lambda.binder().sort,
                        serializer_work,
                        serializer_work_limit,
                        deadline,
                    )?;
                    self.push_str("(lambda ((")?;
                    self.push_str(&quote_symbol(&lambda.binder().name))?;
                    self.push_char(' ')?;
                    self.push_str(&sort_to_smtlib(&lambda.binder().sort))?;
                    self.push_str(")) ")?;
                    stack.push(UfAliasSmtPart::Close);
                    stack.push(UfAliasSmtPart::Expr(lambda.body()));
                    continue;
                }
                UfAliasSmtPart::Capture(formal, value) => {
                    Self::charge_work(serializer_work, serializer_work_limit, deadline)?;
                    self.push_char('(')?;
                    self.push_str(&quote_symbol(&formal.name))?;
                    self.push_char(' ')?;
                    stack.push(UfAliasSmtPart::Close);
                    stack.push(UfAliasSmtPart::Expr(value));
                    continue;
                }
                UfAliasSmtPart::Text(text) => {
                    Self::charge_work(serializer_work, serializer_work_limit, deadline)?;
                    self.push_str(text)?;
                    continue;
                }
                UfAliasSmtPart::Close => {
                    self.push_char(')')?;
                    continue;
                }
            };
            Self::charge_work(serializer_work, serializer_work_limit, deadline)?;
            self.write_expr_node(
                expr,
                &mut stack,
                serializer_work,
                serializer_work_limit,
                deadline,
            )?;
        }
        Ok(())
    }
}

fn emit_uf_application_aliases_with_limits(
    aliases: &[UfApplicationAlias],
    deadline: Option<ay_core::time::Instant>,
    limits: UfApplicationAliasEmissionLimits,
) -> Result<String, UfApplicationAliasEmissionError> {
    if aliases.is_empty() {
        return Ok(String::new());
    }
    if alias_emission_deadline_expired(deadline) {
        return Err(UfApplicationAliasEmissionError::DeadlineExpired);
    }

    let mut script = BoundedUfAliasScript::new(limits.emitted_bytes);
    let mut serializer_work = 0usize;
    for alias in aliases {
        let quoted_alias = quote_symbol(&alias.alias);
        let sort = sort_to_smtlib(&alias.application.sort());
        script.push_str("(declare-const ")?;
        script.push_str(&quoted_alias)?;
        script.push_char(' ')?;
        script.push_str(&sort)?;
        script.push_str(")\n(assert (= ")?;
        script.push_str(&quoted_alias)?;
        script.push_char(' ')?;
        script.write_expr(
            &alias.application,
            &mut serializer_work,
            limits.serializer_work,
            deadline,
        )?;
        script.push_str("))\n")?;
        if alias_emission_deadline_expired(deadline) {
            return Err(UfApplicationAliasEmissionError::DeadlineExpired);
        }
    }
    Ok(script.text)
}

fn scalar_value_matches_sort(value: &SmtValue, sort: &ChcSort) -> bool {
    match (value, sort) {
        (SmtValue::Bool(_), ChcSort::Bool)
        | (SmtValue::Int(_) | SmtValue::BigInt(_), ChcSort::Int)
        | (SmtValue::Real(_), ChcSort::Real) => true,
        (
            SmtValue::BitVec(_, value_width) | SmtValue::BigBitVec(_, value_width),
            ChcSort::BitVec(sort_width),
        ) => value_width == sort_width,
        _ => false,
    }
}

/// Install exact alias values into the model and independently check the
/// finite-function consistency condition: applications of one UF at equal
/// concrete argument tuples must have equal results.
///
/// Missing/unparseable aliases, unevaluable arguments, or an inconsistent
/// result all fail closed.  No default function value is ever invented.
pub(crate) fn install_uf_application_alias_values(
    model: &mut FxHashMap<String, SmtValue>,
    aliases: &[UfApplicationAlias],
) -> bool {
    if aliases.is_empty() {
        return true;
    }
    let mut observed = Vec::with_capacity(aliases.len());
    for alias in aliases {
        let Some(value) = model.remove(&alias.alias) else {
            return false;
        };
        observed.push((alias.application.clone(), value.clone()));
    }
    install_observed_uf_application_values(model, &observed)
}

/// Install exact values returned by `(get-value (f ...))` observations.
///
/// This is the alias-independent half of [`install_uf_application_alias_values`]
/// and is used by BMC's post-SAT trace observation pass. Every observed value
/// is type-checked, and all concretely equal argument tuples are checked for
/// congruent results before the enriched model can participate in replay.
pub(crate) fn install_observed_uf_application_values(
    model: &mut FxHashMap<String, SmtValue>,
    observed: &[(ChcExpr, SmtValue)],
) -> bool {
    use crate::expr::evaluate::{
        uf_application_concrete_model_key, uf_application_model_key,
        UF_APPLICATION_MODEL_MARKER_KEY, UF_APPLICATION_MODEL_MARKER_VALUE,
    };

    if observed.is_empty() {
        return true;
    }
    let mut keyed_values = Vec::with_capacity(observed.len());
    for (application, value) in observed {
        let ChcExpr::FuncApp(_, return_sort, args) = application else {
            return false;
        };
        if !scalar_uf_sort(return_sort)
            || !args.iter().all(|argument| scalar_uf_sort(&argument.sort()))
            || !scalar_value_matches_sort(value, return_sort)
        {
            return false;
        }
        let Some(key) = uf_application_model_key(application) else {
            return false;
        };
        keyed_values.push((key, value.clone()));
    }
    for (key, value) in keyed_values {
        model.insert(key, value);
    }
    model.insert(
        UF_APPLICATION_MODEL_MARKER_KEY.to_string(),
        SmtValue::Opaque(UF_APPLICATION_MODEL_MARKER_VALUE.to_string()),
    );

    for (application, value) in observed {
        let ChcExpr::FuncApp(_, _, arguments) = application else {
            return false;
        };
        let argument_values = arguments
            .iter()
            .map(|argument| crate::expr::evaluate::evaluate_expr(argument, model))
            .collect::<Option<Vec<_>>>();
        let Some(argument_values) = argument_values else {
            return false;
        };
        let Some(key) = uf_application_concrete_model_key(application, &argument_values) else {
            return false;
        };
        if let Some(previous) = model.get(&key) {
            if crate::expr::evaluate::smt_values_equal(previous, value) != Some(true) {
                return false;
            }
        } else {
            model.insert(key, value.clone());
        }
    }
    true
}

/// Per-call executor trace (inc-13 per-check cost attribution): active at
/// `--chc-checksat-trace>=2`. Logs construction/execute split plus the
/// executor-internal phase timers so the 0.3-0.7s per-check fallback cost
/// can be attributed to a concrete sink.
fn exec_trace_enabled() -> bool {
    super::check_sat::checksat_trace_level() >= 2
}

/// Inc-18 SAT-direction EqDiffVar retry gate (`AY_EXEC_DV_RETRY`, default
/// ON; `0`/`false` disables). Read per call so A/B harnesses can toggle it
/// within a process.
pub(super) fn dv_unknown_retry_enabled() -> bool {
    crate::ab_switches::get().exec_dv_retry // B27: CLI-owned; env retired.
}

/// Declared consumer of one ay-dpll sub-query's verdict
/// (#cert-accounting item 3).
///
/// This selects between two ay-dpll entrypoints that decide, certify, and
/// publish IDENTICALLY. It changes no gate and no verdict; ay-dpll reads it
/// only to attribute certification cost to the channel that paid it
/// (`ay_dpll::CertificationAccounting`).
///
/// The split is nonetheless kept honest: `InternalLemma` may be declared ONLY
/// where CHC search re-derives its published claim from scratch. Every channel
/// on which raw `"unsat"` BECOMES the published claim stays `Published`, including
/// `smtlib_first_verdict_via_executor_until` (the ghost-pair quantified
/// certification and checked-replay obligation re-execution) and the
/// strict-unsat-cert obligation lane, none of which may ever be relabelled
/// without re-auditing what backs their claim.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum ExecutorQueryRole {
    /// The verdict is (or becomes) a published claim.
    Published,
    /// The verdict is consumed only as CHC search guidance.
    #[cfg(test)]
    InternalLemma,
}

#[derive(Clone, Copy, Default)]
struct ExecutorResourceLimits<'a> {
    /// One already-elapsing deadline covering caller construction, parsing,
    /// execution, and publication.  Unlike `Executor::set_timeout`, this is
    /// never renewed when `check-sat` is reached.
    deadline: Option<Instant>,
    /// Per-executor term-store ceiling. This is deliberately distinct from the
    /// process-RSS `:max-memory` control.
    term_memory_limit: Option<usize>,
    cancellation: Option<&'a ReplayCancellation>,
}

impl ExecutorResourceLimits<'_> {
    fn stopped(self) -> bool {
        self.cancellation
            .is_some_and(ReplayCancellation::is_cancelled)
            || self
                .deadline
                .is_some_and(|deadline| Instant::now() >= deadline)
    }
}

/// Build the executor for a CHC SEARCH query: one whose verdict only guides
/// the engines (PDR consecution / blocking, BMC depth checks, k-induction,
/// Houdini candidates, replay probes) and is never itself the published
/// claim — the CHC verdict is re-verified independently (`portfolio::accept`,
/// `adaptive_validation`) before it is printed.
///
/// Every `ay_dpll::Executor` ay-chc constructs for such a query comes from
/// here, so the per-query posture inherits the process-level one the CLI
/// applies to its own executor (`run::new_executor`, T8): under
/// `--competition` / `--no-proof` / `--z3-mode` with no proof or certificate
/// demand in scope (`MiscCliFlags::search_executor_sheds_proof_cycle`) the
/// executor sheds the internal proof cycle exactly as the CLI executor does
/// (`Executor::set_competition_mode`: no search-time proof recording, no
/// post-UNSAT certificate mint, UNSAT through the scope-authenticated raw
/// lane). A plain solve, `--strict-proofs`, `--self-check`, `--proof`,
/// `--chc-checked-replay`, and every library consumer that never installs
/// CLI flags keep the default proof-carrying posture — including the
/// `--strict-proofs`-only checked replay (`proof_metadata::replay_check`),
/// which reaches the same posture through
/// `smtlib_first_verdict_via_executor_with_limit` ([`new_script_executor`]).
///
/// One scope sheds in every posture: a search marked verdict-only by a live
/// [`ScopedVerdictOnlySearch`] guard on this thread, whose verdicts back no
/// claim at all (the counterexample replay; see `verdict_only`). The raw
/// SMT-LIB script channels never consult it.
///
/// NOT for the certificate lanes: `strict_unsat` (the checked native bundle)
/// and `interpolation::proof_backed` (proof-derived interpolants) build their
/// own `api::Solver` with `set_produce_proofs(true)` and never pass through
/// here.
pub(crate) fn new_search_executor() -> ay_dpll::Executor {
    executor_in_posture(verdict_only::search_sheds_proof_cycle())
}

/// The executor of the raw SMT-LIB script channel
/// ([`smtlib_first_verdict_via_executor_with_limit`], including its absolute
/// deadline wrapper). Its `unsat` can be the published claim (the ghost-pair
/// quantified certification, the `--strict-proofs` checked replay), so it
/// takes the process posture alone: a [`ScopedVerdictOnlySearch`] on this
/// thread does not reach it.
fn new_script_executor() -> ay_dpll::Executor {
    executor_in_posture(false)
}

/// Test seam for assigning a query role without exposing an unbounded
/// production entry point.
#[cfg(test)]
fn execute_commands_via_executor(
    commands: &[ay_frontend::Command],
    role: ExecutorQueryRole,
) -> Result<Vec<String>, ()> {
    execute_commands_via_executor_with_limits(
        commands,
        role,
        ExecutorResourceLimits::default(),
        new_script_executor,
    )
}

/// A search executor in the process posture, shedding the proof cycle in
/// every posture when `verdict_only`.
fn executor_in_posture(verdict_only: bool) -> ay_dpll::Executor {
    let mut exec = ay_dpll::Executor::new();
    exec.set_term_memory_limit(SmtContext::current_thread_term_memory_budget());
    if verdict_only || ay_core::misc_cli_flags().search_executor_sheds_proof_cycle {
        exec.set_competition_mode(true);
    }
    // On a portfolio lane thread, the lane's interrupt stops an in-flight
    // check as soon as the portfolio cancels its workers (a caller that owns
    // a finer cancellation replaces it with `set_interrupt`).
    if let Some(flag) = crate::smt::deadline::lane_interrupt_flag() {
        exec.set_interrupt(flag);
    }
    exec
}

/// Execute `commands` on a fresh executor from `new_executor`: the search
/// constructor ([`new_search_executor`]) for the `ChcExpr` query channels,
/// the script constructor ([`new_script_executor`]) for the raw SMT-LIB ones.
fn execute_commands_via_executor_with_limits(
    commands: &[ay_frontend::Command],
    role: ExecutorQueryRole,
    limits: ExecutorResourceLimits<'_>,
    new_executor: impl FnOnce() -> ay_dpll::Executor,
) -> Result<Vec<String>, ()> {
    let memory = ReplayMemory::capture(limits.term_memory_limit);
    let inherited = crate::smt::deadline::current_lane_token();
    let inherited_observed = inherited.as_ref().map(ReplayCancellation::new);
    let limits = ExecutorResourceLimits {
        deadline: limits
            .deadline
            .into_iter()
            .chain(crate::smt::deadline::effective_thread_deadline())
            .min(),
        term_memory_limit: memory.term_limit(),
        cancellation: limits.cancellation.or(inherited_observed.as_ref()),
    };
    if memory.check().is_none() || limits.stopped() {
        return Err(());
    }
    // Declare the observer first so unwinding destroys the executor before
    // stopping and joining its owned interrupt observer. No borrowed caller
    // callback is moved onto that worker.
    let mut observer = limits
        .cancellation
        .map(interrupt_observer::InterruptObserver::new)
        .transpose()
        .map_err(|error| {
            tracing::debug!("executor_adapter: {error}");
        })?;
    let trace = exec_trace_enabled();
    let t_new = ay_core::time::Instant::now();
    let mut exec = new_executor();
    // Charge executor construction to the same absolute wall and reject it if
    // it consumed the final share.  Installing the absolute deadline (rather
    // than a relative timeout computed before parsing) prevents `check-sat`
    // from launching with a freshly renewed stale budget.
    if memory.check_terms(exec.terms()).is_none() || limits.stopped() {
        return Err(());
    }
    exec.set_deadline(limits.deadline);
    exec.set_term_memory_limit(limits.term_memory_limit);
    if let Some(observer) = &observer {
        exec.set_interrupt(observer.interrupt());
    }
    let new_dt = t_new.elapsed();
    let t_exec = ay_core::time::Instant::now();
    let result = ay_core::catch_ay_panics(
        AssertUnwindSafe(|| {
            // Both entrypoints decide, certify, and publish identically; the
            // declaration only attributes this channel's certification cost.
            let executed = match role {
                ExecutorQueryRole::Published => exec.execute_all(commands),
                #[cfg(test)]
                ExecutorQueryRole::InternalLemma => exec.execute_all_internal_lemma(commands),
            };
            match executed {
                Ok(out) => Ok(out),
                Err(e) => {
                    tracing::debug!("executor_adapter: execution error: {e}");
                    Err(())
                }
            }
        }),
        |reason| {
            tracing::debug!("executor_adapter: ay panic: {reason}");
            Err(())
        },
    );
    if trace {
        trace_executor_phases(&exec, new_dt, t_exec.elapsed());
    }
    if memory.check_executor(&exec).is_none() || limits.stopped() {
        return Err(());
    }
    // Keep observing during destruction, then join before a successful result
    // leaves this frame. The enclosing ReplayLimit phase additionally charges
    // parsed-command/output cleanup and repeats cancellation/deadline checks.
    drop(exec);
    if observer.as_mut().is_some_and(|observer| !observer.finish())
        || limits.stopped()
        || memory.check().is_none()
    {
        return Err(());
    }
    result
}

/// `--chc-checksat-trace>=2` line for one executor run: construction and execution
/// wall, the phase split and the search counters.
fn trace_executor_phases(
    exec: &ay_dpll::Executor,
    new_dt: std::time::Duration,
    exec_dt: std::time::Duration,
) {
    let stats = exec.statistics();
    let phase = |name: &str| stats.get_float(name).unwrap_or(0.0);
    safe_eprintln!(
        "[EXEC-TRACE {:?}] new={:.1}ms exec={:.1}ms (quant={:.1}ms logic={:.1}ms dispatch={:.1}ms map={:.1}ms) conflicts={} decisions={}",
        std::thread::current().id(),
        new_dt.as_secs_f64() * 1e3,
        exec_dt.as_secs_f64() * 1e3,
        phase("phase.quantifier_preprocess.seconds") * 1e3,
        phase("phase.logic_detection.seconds") * 1e3,
        phase("phase.solver_dispatch.seconds") * 1e3,
        phase("phase.quantifier_result_mapping.seconds") * 1e3,
        stats.conflicts,
        stats.decisions
    );
}

/// Deterministic verdict of the closed, ground SAT oracle used by constant-fold
/// differential tests.
#[cfg(test)]
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum CountedOracleVerdict {
    /// The independent executor model gate confirmed the asserted closed ground proposition.
    Confirmed,
    /// The executor proved the asserted closed ground proposition false.
    Disagreed,
    /// Parsing, execution, publication, or a deterministic resource bound refused.
    Refused,
}

#[cfg(test)]
fn classify_counted_oracle_output(output: Result<Vec<String>, ()>) -> CountedOracleVerdict {
    match output.as_deref() {
        Ok([result]) if result == "sat" => CountedOracleVerdict::Confirmed,
        Ok([result]) if result == "unsat" => CountedOracleVerdict::Disagreed,
        _ => CountedOracleVerdict::Refused,
    }
}

#[cfg(test)]
fn run_counted_oracle_commands(
    commands: &[ay_frontend::Command],
    conflicts: u64,
    decisions: u64,
) -> CountedOracleVerdict {
    const TERM_MEMORY_LIMIT: usize = 16 * 1024 * 1024;

    classify_counted_oracle_output(execute_commands_via_executor_with_limits(
        commands,
        ExecutorQueryRole::Published,
        ExecutorResourceLimits {
            deadline: None,
            term_memory_limit: Some(TERM_MEMORY_LIMIT),
            cancellation: None,
        },
        || {
            let mut executor = new_script_executor();
            executor.set_random_seed(0);
            executor.set_resource_limit(Some(conflicts));
            executor.set_decision_limit(Some(decisions));
            executor.set_ground_budget_enabled(false);
            executor
        },
    ))
}

/// Check one canonical closed ground BV assertion with fixed, deterministic
/// solver effort. Unknown/resource exhaustion is refusal, never disagreement.
#[cfg(test)]
pub(crate) fn check_ground_sat_smtlib_via_counted_executor(smt: &str) -> CountedOracleVerdict {
    let Ok(commands) = ay_frontend::parse(smt) else {
        return CountedOracleVerdict::Refused;
    };
    match commands.as_slice() {
        [ay_frontend::Command::SetLogic(logic), ay_frontend::Command::Assert(_), ay_frontend::Command::CheckSat]
            if logic == "QF_BV" =>
        {
            run_counted_oracle_commands(&commands, 1, 1)
        }
        _ => CountedOracleVerdict::Refused,
    }
}

/// Finite test oracle for raw quantified scripts; production callers use the
/// bounded script channel directly.
#[cfg(test)]
pub(crate) fn check_unsat_smtlib_via_executor(smt: &str) -> bool {
    let deadline = Instant::now() + std::time::Duration::from_mins(1);
    smtlib_first_verdict_via_executor_until(smt, deadline, None).as_deref() == Some("unsat")
}

/// Execute a generated SMT-LIB obligation under one absolute wall-clock
/// deadline and an optional per-executor term-store ceiling.
///
/// The deadline is checked before and after parsing and installed directly on
/// the executor.  Thus parser/executor construction consumes the caller's
/// original allowance, and reaching `check-sat` cannot create a fresh relative
/// timeout window. Frontend parsing operates on the caller's already-bounded
/// generated surface; assertion elaboration and all solver-created terms land
/// in the executor's `TermStore`, whose capacity-aware instance accounting is
/// polled at theory-loop boundaries. Crossing that ceiling never publishes a
/// verdict.
///
/// A script-local `:timeout` is rejected so the absolute caller deadline remains
/// the single authoritative wall. `:max-memory` is a separate process-RSS
/// control and does not alter the term-store ceiling. Any expired/exceeded
/// resource limit, parse or execution error, panic, or empty output fails closed
/// to `None`. An inherited CHC thread-local term cap is intersected with the
/// explicit cap; supplying `None` or a larger limit cannot remove that owner.
pub(crate) fn smtlib_first_verdict_via_executor_until(
    smt: &str,
    deadline: Instant,
    term_memory_limit: Option<usize>,
) -> Option<String> {
    smtlib_first_verdict_via_executor_with_limit(
        smt,
        ReplayLimit::Until(deadline),
        term_memory_limit,
    )
}

/// Preserve published-query authority while carrying a caller-owned deadline
/// and optional cancellation attempt through active ordinary SMT execution.
/// The owned observer is cooperative, not a hard response-time guarantee.
pub(crate) fn smtlib_first_verdict_via_executor_with_limit(
    smt: &str,
    limit: ReplayLimit<'_>,
    term_memory_limit: Option<usize>,
) -> Option<String> {
    let memory = ReplayMemory::capture(term_memory_limit);
    // The phase boundary is outside the parsed commands, executor and output
    // collection: their destruction is charged before a verdict may escape.
    memory.phase(|| {
        limit.phase(|| {
            let limits = ExecutorResourceLimits {
                deadline: limit.deadline(),
                term_memory_limit: memory.term_limit(),
                cancellation: limit.cancellation(),
            };
            limit.check()?;
            let commands = match ay_frontend::parse(smt) {
                Ok(commands) => commands,
                Err(error) => {
                    tracing::debug!("executor_adapter: bounded obligation parse error: {error}");
                    return None;
                }
            };
            limit.check()?;
            if limit.deadline().is_some()
                && commands.iter().any(|command| {
                    let keyword = match command {
                        ay_frontend::Command::SetOption(keyword, _)
                        | ay_frontend::Command::SetOptionAttribute(keyword) => keyword,
                        _ => return false,
                    };
                    keyword.trim_start_matches(':') == "timeout"
                })
            {
                tracing::debug!("executor_adapter: bounded obligation contains a timeout override");
                return None;
            }
            match execute_commands_via_executor_with_limits(
                &commands,
                ExecutorQueryRole::Published,
                limits,
                new_script_executor,
            ) {
                Ok(outputs) => outputs.first().cloned(),
                Err(()) => None,
            }
        })
    })
}

/// Re-export of the shared splitter that lives with the `Solver` API it
/// exists to serve; see [`ay_dpll::api::split_leading_set_logic`].
pub(crate) use ay_dpll::api::split_leading_set_logic;

fn needs_strict_reparsed_validation(exprs: &[&ChcExpr]) -> bool {
    exprs
        .iter()
        .any(|expr| expr.contains_array_ops() || expr.contains_dt_ops() || expr.has_mod_aux_vars())
}

/// Axiomatize integer div/mod with constant divisors before executor dispatch (#A3).
///
/// ay-dpll's AUFLIA/ALIA fragments reject raw integer `div`/`mod` terms with
/// "(unsupported arithmetic)", which turns satisfiable validator replays
/// (counterexample verification on original clauses) into Unknown and rejects
/// valid Unsafe results. Rewriting `(div x k)` / `(mod x k)` for literal `k`
/// into fresh quotient/remainder variables constrained by
/// `x = k*q + r ∧ 0 ≤ r < |k|` (SMT-LIB Euclidean semantics — the #1362
/// transform in `ChcExpr::eliminate_mod`) is equisatisfiable: the constraints
/// are total in `x`, so every model of the original extends to the rewritten
/// form and every model of the rewritten form restricts to the original.
///
/// Returns `None` when the expression contains no mod/div (no rewrite needed).
/// SAT models must still be validated against the ORIGINAL expression — the
/// caller keeps using the untransformed expr for `accept_reparsed_sat_model`.
pub(crate) fn axiomatize_mod_div_for_executor(expr: &ChcExpr) -> Option<ChcExpr> {
    if !expr.contains_mod_or_div() {
        return None;
    }
    // Callers immediately run the iterative resource admission over this
    // transformed surface.  Do not recursively rescan it here: elimination can
    // expand the term, and that expansion has not passed the executor gate yet.
    // Non-constant divisors simply survive and remain fail-closed downstream.
    Some(expr.eliminate_mod())
}

pub(super) fn accept_reparsed_sat_model(
    exprs: &[&ChcExpr],
    model: FxHashMap<String, SmtValue>,
    source: &'static str,
) -> Option<FxHashMap<String, SmtValue>> {
    let verify_result =
        verify_sat_model_conjunction_strict_with_mod_retry(exprs.iter().copied(), &model);
    let requires_strict = needs_strict_reparsed_validation(exprs);
    match verify_result {
        ModelVerifyResult::Invalid => {
            tracing::warn!(
                "{source}: reparsed SAT model violates original CHC expression; returning Unknown"
            );
            None
        }
        ModelVerifyResult::Indeterminate if requires_strict => {
            tracing::debug!(
                "{source}: reparsed SAT model is indeterminate for array/DT/mod query; returning Unknown"
            );
            None
        }
        ModelVerifyResult::Indeterminate => {
            // FAIL-CLOSED (2026-07-08, wishlist rank 1 — the executor twin of the
            // `sat_or_unknown` fix): an Indeterminate verification whose model is
            // MISSING an assignment for a variable in an evaluable theory position
            // is the dropped-definition signature — the model then says nothing
            // about the original expression. In the model-checker-consumer midpoint repro the
            // internal DPLL(T) loop's bad models were demoted by `sat_or_unknown`,
            // and the EXECUTOR fallback then shipped an under-assigned model
            // through this very arm, surfacing as a spurious CHC refutation.
            // Fully-assigned models with only predicate/UF-caused indeterminacy
            // are still accepted (#4712 semantics), as before.
            // PRECISION (FIX 5, aychc-completeness): the executor twin of the
            // `sat_or_unknown` bindings completion, tried BEFORE the
            // scalar-defaults attempt. Derive the missing evaluable-position
            // variables from their SSA defining equalities present in `exprs`
            // (forced values, never defaults), then require a strict `Valid`
            // conjunction verdict before accepting — the SAME verifier as the
            // acceptance gate above, so no new acceptance channel. On any other
            // outcome fall through (with the ORIGINAL model) to the defaults
            // attempt and the unchanged fail-closed None.
            {
                let mut derived = model.clone();
                let mut changed = false;
                for e in exprs {
                    changed |= super::check_sat::complete_model_from_bindings(e, &mut derived);
                }
                if changed
                    && matches!(
                        verify_sat_model_conjunction_strict_with_mod_retry(
                            exprs.iter().copied(),
                            &derived,
                        ),
                        ModelVerifyResult::Valid
                    )
                {
                    tracing::debug!(
                        "{source}: reparsed SAT model completed from SSA defining-equality \
                         bindings and strict-verified Valid; accepting"
                    );
                    return Some(derived);
                }
            }
            if let Some((completed, missing)) =
                super::check_sat::complete_model_with_scalar_defaults(exprs.iter().copied(), &model)
            {
                // Model-completion-then-strict-reverify (2026-07), the executor
                // twin of the identical path in `sat_or_unknown`: fill every
                // missing evaluable-position scalar with a type-appropriate
                // default (BitVec→0, Int→0, Bool→false, Real→0), then re-run
                // the SAME strict conjunction verifier used at the acceptance
                // gate above.
                //
                // SOUNDNESS INVARIANT (non-negotiable): this path may only ever
                // emit Sat-with-verified-witness (`Some(completed)`) or Unknown
                // (`None`), NEVER Unsat. Acceptance is gated EXCLUSIVELY on the
                // strict verifier evaluating the ORIGINAL expressions to
                // Bool(true) under the completed model
                // (`ModelVerifyResult::Valid`). Accepting a completed model
                // WITHOUT re-verification would reopen the under-assigned-model
                // fail-open described above (spurious CHC refutation, model-checker-consumer
                // midpoint repro). Invalid AND Indeterminate completions both
                // fall through to Unknown.
                if matches!(
                    verify_sat_model_conjunction_strict_with_mod_retry(
                        exprs.iter().copied(),
                        &completed
                    ),
                    ModelVerifyResult::Valid
                ) {
                    tracing::debug!(
                        "{source}: reparsed SAT model was missing {} evaluable-position scalar \
                         assignment(s); default-completed model strictly verifies against the \
                         original expression(s); accepting",
                        missing.len()
                    );
                    return Some(completed);
                }
                let (first_missing, _) = &missing[0];
                tracing::warn!(
                    "{source}: reparsed SAT model is missing an assignment for free \
                     variable `{first_missing}` (in an evaluable theory position); \
                     default-value completion was attempted but the completed model did \
                     not strictly verify; returning Unknown instead of accepting"
                );
                return None;
            }
            tracing::debug!("{source}: reparsed SAT model verification indeterminate; accepting");
            Some(model)
        }
        ModelVerifyResult::Valid => {
            debug_assert!(
                !requires_strict || matches!(verify_result, ModelVerifyResult::Valid),
                "BUG: reparsed SAT model for array/DT/mod query must validate before acceptance"
            );
            Some(model)
        }
    }
}

/// Datatype declarations admitted for one executor query, with its tree size.
type AdmittedQuery<'a> = (Vec<(&'a str, &'a [crate::ChcDtConstructor])>, usize);

/// Executor admission of one query expression (bridge item D-1, CHC-COMP 2026
/// Workstream D): the pointer-memoised walk of `logic_detection` (unique-node,
/// depth and tree caps), with the decision counted on the ITP-BOARD by lane
/// and stage. Same verdict semantics as `collect_dt_declarations_for_expr`;
/// also returns the admitted tree size (it selects the script printer).
fn admit_for_executor<'a>(
    lane: SmtLane,
    stage: &'static str,
    expr: &'a ChcExpr,
) -> Result<AdmittedQuery<'a>, logic_detection::DatatypeDeclarationError> {
    use crate::interpolation::stats::{record_admission, AdmissionOutcome};
    match logic_detection::collect_dt_declarations_for_expr_sized(&[], expr) {
        Ok((declarations, sizes)) => {
            record_admission(
                lane,
                stage,
                AdmissionOutcome::Admitted {
                    unique_nodes: sizes.unique_nodes,
                    tree_nodes: sizes.tree_nodes,
                },
            );
            Ok((declarations, sizes.tree_nodes))
        }
        Err(error) => {
            let outcome = match &error {
                logic_detection::DatatypeDeclarationError::ResourceLimit(
                    "datatype expression nodes",
                ) => AdmissionOutcome::RefusedUniqueNodes,
                logic_detection::DatatypeDeclarationError::ResourceLimit(
                    "datatype expression nesting depth",
                ) => AdmissionOutcome::RefusedDepth,
                logic_detection::DatatypeDeclarationError::ResourceLimit(
                    "executor expression tree nodes",
                ) => AdmissionOutcome::RefusedTreeSize,
                _ => AdmissionOutcome::RefusedOther,
            };
            record_admission(lane, stage, outcome);
            Err(error)
        }
    }
}

/// Append one `(assert …)` per conjunct.
///
/// Search lane, and only for a query whose tree expansion exceeds the old
/// admission cap (`MAX_DT_EXPR_NODES` tree nodes — exactly the queries the
/// tree-counting admission used to refuse): DAG-linear (`smt::dag_smtlib`,
/// `let`-shared; bridge item D-1). Everything else keeps the tree printer, so
/// every query the executor accepted before is printed byte for byte as
/// before. Measured reason for the size gate (2026-09-22): the executor is
/// slower on `let` scripts of small queries — the tte_synchro IMC k=3 query
/// (SAT) takes `ay --competition` 5.0–5.4 s with its `let`s and 0.7–0.8 s
/// let-expanded, and in-portfolio the DAG-printed Search-lane checks turned
/// that `sat` into `unknown` at IMC's 5 s cap — while a wide query printed as
/// a tree costs megabytes (om1_general_4_6 k=1: 1.09 MB, 0.73 s vs 0.04 s
/// as a DAG). Verification lane: the tree printer, unchanged until the INV-12
/// differential gate covers it. A DAG-printer refusal falls back to the tree
/// printer.
fn write_executor_asserts(
    smt: &mut String,
    conjuncts: &[&ChcExpr],
    lane: SmtLane,
    tree_nodes: usize,
) {
    use crate::interpolation::stats::{record_script_print, ScriptPrint};
    let before = smt.len();
    if lane == SmtLane::Search && tree_nodes > logic_detection::MAX_DT_EXPR_NODES {
        let caps = crate::smt::dag_smtlib::DagCaps {
            max_unique_nodes: logic_detection::MAX_DT_EXPR_NODES,
            max_depth: logic_detection::MAX_DT_NESTING_DEPTH,
        };
        match crate::smt::dag_smtlib::write_asserts_dag(smt, conjuncts, caps) {
            Ok(stats) => {
                record_script_print(ScriptPrint::Dag {
                    bytes: smt.len() - before,
                    shared_nodes: stats.shared_nodes,
                });
                return;
            }
            Err(_) => record_script_print(ScriptPrint::DagFallback),
        }
    }
    for c in conjuncts {
        let c_str = InvariantModel::expr_to_smtlib(c);
        smt.push_str(&format!("(assert {c_str})\n"));
    }
    record_script_print(ScriptPrint::Tree {
        bytes: smt.len() - before,
    });
}

impl SmtContext {
    /// Dispatch an array-containing formula to ay-dpll's Executor for full
    /// array theory support. Falls back to SmtResult::Unknown on any error.
    ///
    /// The `propagated_model` contains var=value bindings discovered during
    /// preprocessing (constant propagation, singleton bounds). These are merged
    /// into the executor's model on Sat so PDR cube extraction has access to all
    /// known bindings.
    pub(crate) fn check_sat_via_executor(
        &self,
        expr: &ChcExpr,
        propagated_model: &FxHashMap<String, SmtValue>,
        timeout: std::time::Duration,
    ) -> SmtResult {
        // Rung 0: Search-lane scripts run EqDiffVar-off (see
        // `SmtContext::executor_disables_eq_diffvar`); Verification unchanged.
        self.check_sat_via_executor_with_opts(
            expr,
            propagated_model,
            timeout,
            self.executor_disables_eq_diffvar(),
        )
    }

    /// `check_sat_via_executor` with per-run executor options (inc-18).
    ///
    /// `disable_eq_diffvar` emits `(set-option :ay-eq-diffvar false)` into the
    /// executor script, disabling the inc-14 EqDiffVar preprocessing pass for
    /// THIS run only. Used by the SAT-direction retry in `check_sat`: on
    /// IMC-class itp-strengthened transition checks the reduction defeats the
    /// model search that the plain pipeline decides in milliseconds.
    /// Soundness: identical adapter pipeline — UNSAT carries the same trust as
    /// every executor verdict at this call site, and SAT models pass the same
    /// strict validation against the ORIGINAL expression below.
    pub(crate) fn check_sat_via_executor_with_opts(
        &self,
        expr: &ChcExpr,
        propagated_model: &FxHashMap<String, SmtValue>,
        timeout: std::time::Duration,
        disable_eq_diffvar: bool,
    ) -> SmtResult {
        // Under an effort the executor route is closed (P4a slice 8): an
        // executor session's work is outside the run's count before GuardTree
        // S6, so its answer would be the clock's, not the count's.
        if crate::run_meter::close_route() {
            return SmtResult::Unknown;
        }
        #[cfg(test)]
        super::check_sat::record_executor_session_for_tests(timeout);
        // Under a counted allowance (`smt::executor_work`) the run is bounded
        // by its work; a spent allowance answers as an expired deadline does.
        let _work = match super::executor_work::draw_executor_work() {
            super::executor_work::ExecutorDraw::Spent => return SmtResult::Unknown,
            super::executor_work::ExecutorDraw::Open(draw) => Some(draw),
            super::executor_work::ExecutorDraw::Unmetered => None,
        };
        // Start one absolute envelope before admission, rewriting, SMT-LIB
        // construction, and parsing. The script's relative `:timeout` is kept
        // for compatibility, but Executor combines it with this earlier wall
        // rather than renewing the full allowance at `check-sat`.
        let Some(timeout_deadline) = Instant::now().checked_add(timeout) else {
            return SmtResult::Unknown;
        };
        let executor_deadline = [
            self.current_global_deadline(),
            crate::smt::current_thread_solve_deadline(),
            super::deadline::current_smt_deadline(),
        ]
        .into_iter()
        .flatten()
        .fold(timeout_deadline, |deadline, outer| deadline.min(outer));
        if Instant::now() >= executor_deadline || self.exact_term_memory_exceeded() {
            if exec_trace_enabled() {
                safe_eprintln!(
                    "[EXEC-TRACE {:?}] adapter early-return: deadline/term-memory before admission",
                    std::thread::current().id()
                );
            }
            return SmtResult::Unknown;
        }

        let lane = self.lane();
        // Search lane: solve top-level equalities first (`smt::solve_eqs`).
        // The residual is equisatisfiable; a SAT model of it is completed
        // (eliminated variables from their definitions) and validated against
        // the ORIGINAL `expr` below, like every executor model. The pass is
        // DAG-memoised and budgeted, so it runs ahead of admission: a wide
        // unrolling whose tree expansion the admission would refuse is often
        // small once its init constants and frame equalities are substituted.
        let solved = if lane == SmtLane::Search {
            super::solve_eqs::for_search_executor(expr)
        } else {
            None
        };
        if let Some((solved, original_vars)) = &solved {
            if exec_trace_enabled() {
                safe_eprintln!(
                    "[EXEC-TRACE {:?}] solve-eqs eliminated={} rounds={} decided={}",
                    std::thread::current().id(),
                    solved.eliminated(),
                    solved.rounds,
                    matches!(solved.residual, ChcExpr::Bool(_))
                );
            }
            match solved.residual {
                ChcExpr::Bool(false) => return SmtResult::Unsat,
                ChcExpr::Bool(true) => {
                    let mut model = propagated_model.clone();
                    if !solved.complete_model(original_vars, &mut model) {
                        return SmtResult::Unknown;
                    }
                    return accept_reparsed_sat_model(&[expr], model, "executor_adapter")
                        .map_or(SmtResult::Unknown, SmtResult::Sat);
                }
                _ => {}
            }
        }
        let original_expr = expr;
        let expr = solved.as_ref().map_or(expr, |(solved, _)| &solved.residual);

        // Step 0: Admit the original expression before any recursive
        // preprocessing (`contains_mod_or_div`, `eliminate_mod`, or `vars`).
        // The collector is iterative and owns aggregate node/depth/name/sort
        // caps, so a hostile typed term fails closed before those helpers run.
        if let Err(reason) = admit_for_executor(lane, "pre", expr) {
            tracing::debug!(
                "executor_adapter: {reason}; returning Unknown before recursive preprocessing"
            );
            if exec_trace_enabled() {
                safe_eprintln!(
                    "[EXEC-TRACE {:?}] adapter early-return: dt admission (pre): {reason}",
                    std::thread::current().id()
                );
            }
            return SmtResult::Unknown;
        }

        // Step 1 (#A3): Axiomatize div/mod before serialization so the
        // executor's AUFLIA/ALIA fragments never see raw integer div/mod.
        // Equisatisfiable; SAT models are still validated against the
        // ORIGINAL expression below.
        let trace = exec_trace_enabled();
        let t_build = ay_core::time::Instant::now();
        let mod_div_axiomatized = axiomatize_mod_div_for_executor(expr);
        let solve_expr = mod_div_axiomatized.as_ref().unwrap_or(expr);

        // Admit the transformed surface too: mod/div elimination can introduce
        // auxiliary variables and constraints. Datatype declarations are
        // collected here before the now-bounded `vars` traversal and reused
        // below rather than rewalking variable sorts a second time.
        let (dt_decls, admitted_tree_nodes) = match admit_for_executor(lane, "post", solve_expr) {
            Ok(admitted) => admitted,
            Err(reason) => {
                tracing::debug!(
                    "executor_adapter: {reason}; returning Unknown after bounded preprocessing"
                );
                if exec_trace_enabled() {
                    safe_eprintln!(
                        "[EXEC-TRACE {:?}] adapter early-return: dt admission (post): {reason}",
                        std::thread::current().id()
                    );
                }
                return SmtResult::Unknown;
            }
        };

        // Step 2: Collect free variables and their sorts from the admitted expression.
        let vars = solve_expr.vars();
        if vars.is_empty() {
            // No variables -- constant expression. Let the normal path handle it.
            if exec_trace_enabled() {
                safe_eprintln!(
                    "[EXEC-TRACE {:?}] adapter early-return: no variables (constant expression)",
                    std::thread::current().id()
                );
            }
            return SmtResult::Unknown;
        }

        // Step 2b (Rung 0): sort-unique names. One query can carry `J:Int` and
        // `J:Bool`; emitting both as `(declare-const J ..)` made the frontend
        // reject the script (78–89 % of DRAGON_10's executor Unknowns). The
        // rank-losing sort is renamed `J!Int` in declarations AND body; the
        // model maps back through `lookup_model_value`, and SAT validation
        // below still runs against the ORIGINAL `expr`.
        let sort_renaming = super::sort_unique::SortUniqueRenaming::plan(&vars);
        let sort_renamed_expr;
        let (solve_expr, vars) = match &sort_renaming {
            Some(renaming) => {
                sort_renamed_expr = renaming.apply(solve_expr);
                (&sort_renamed_expr, renaming.renamed_vars(&vars))
            }
            None => (solve_expr, vars),
        };

        // Step 3: Detect the appropriate logic based on sorts present.
        let logic = detect_logic(&vars, solve_expr);

        // Step 4: Build SMT-LIB text.
        let mut smt = String::with_capacity(512);
        smt.push_str(&format!("(set-logic {logic})\n"));
        smt.push_str("(set-option :produce-models true)\n");

        // Set timeout if available -- ay-dpll uses :timeout option in ms.
        let timeout_ms = timeout.as_millis();
        if timeout_ms > 0 && timeout_ms < u128::from(u64::MAX) {
            smt.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
        }

        // Inc-18: per-run EqDiffVar opt-out (see method docs). The extra
        // option line also changes the memo fingerprint, so dv-on and dv-off
        // attempts are memoised independently.
        if disable_eq_diffvar {
            smt.push_str("(set-option :ay-eq-diffvar false)\n");
        }

        // Declare datatypes before any constants that use them.
        match emit_declare_datatypes(&dt_decls) {
            Ok(declarations) => smt.push_str(&declarations),
            Err(reason) => {
                tracing::debug!(
                    "executor_adapter: {reason}; returning Unknown instead of emitting invalid datatype declarations"
                );
                if exec_trace_enabled() {
                    safe_eprintln!(
                        "[EXEC-TRACE {:?}] adapter early-return: datatype declarations: {reason}",
                        std::thread::current().id()
                    );
                }
                return SmtResult::Unknown;
            }
        }

        let uf_decls = match collect_uninterpreted_function_declarations(solve_expr) {
            Ok(declarations) => declarations,
            Err(reason) => {
                tracing::debug!(
                    "executor_adapter: {reason}; returning Unknown instead of emitting ambiguous declarations"
                );
                if exec_trace_enabled() {
                    safe_eprintln!(
                        "[EXEC-TRACE {:?}] adapter early-return: uf declarations: {reason}",
                        std::thread::current().id()
                    );
                }
                return SmtResult::Unknown;
            }
        };
        for declaration in &uf_decls {
            smt.push_str(&emit_declare_uninterpreted_function(declaration));
        }

        // Declare variables.
        for var in &vars {
            let sort_str = sort_to_smtlib(&var.sort);
            let name = quote_symbol(&var.name);
            smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
        }

        // Observe the value of every finite scalar-UF application through a
        // fresh constant. Parameterized `define-fun` entries in get-model are
        // intentionally not interpreted; aliases give strict SAT validation
        // exact application values without fabricating a total function.
        let mut alias_counter = 0usize;
        let uf_application_aliases =
            match build_uf_application_aliases(std::iter::once(solve_expr), &mut alias_counter) {
                Ok(aliases) => aliases,
                Err(reason) => {
                    tracing::debug!("executor_adapter: {reason}; returning Unknown");
                    if exec_trace_enabled() {
                        safe_eprintln!(
                            "[EXEC-TRACE {:?}] adapter early-return: uf alias: {reason}",
                            std::thread::current().id()
                        );
                    }
                    return SmtResult::Unknown;
                }
            };
        let alias_script =
            match emit_uf_application_aliases(&uf_application_aliases, Some(executor_deadline)) {
                Ok(script) => script,
                Err(reason) => {
                    tracing::debug!("executor_adapter: {reason}; returning Unknown");
                    if exec_trace_enabled() {
                        safe_eprintln!(
                            "[EXEC-TRACE {:?}] adapter early-return: uf alias: {reason}",
                            std::thread::current().id()
                        );
                    }
                    return SmtResult::Unknown;
                }
            };
        smt.push_str(&alias_script);

        // Assert the formula. Split top-level conjunctions into separate
        // (assert ...) statements so ay-dpll's DT axiom generation sees each
        // conjunct individually. Without this, (assert (and A B C)) hides
        // DT constructor equalities from the reachability filter (#7016).
        let conjuncts = solve_expr.conjuncts();
        if let Some((offending, reason)) = conjuncts
            .iter()
            .find_map(|expr| unsupported_executor_expr_reason(expr).map(|reason| (expr, reason)))
        {
            tracing::debug!(
                "executor_adapter: unsupported SMT-LIB executor term: {reason}; returning Unknown"
            );
            if exec_trace_enabled() {
                safe_eprintln!(
                    "[EXEC-TRACE {:?}] adapter early-return: sort guard: {reason}",
                    std::thread::current().id()
                );
                static SAMPLES: std::sync::atomic::AtomicUsize =
                    std::sync::atomic::AtomicUsize::new(0);
                if SAMPLES.fetch_add(1, std::sync::atomic::Ordering::Relaxed) < 3 {
                    let text = InvariantModel::expr_to_smtlib(offending);
                    safe_eprintln!(
                        "[EXEC-TRACE {:?}] sort-guard sample: {}",
                        std::thread::current().id(),
                        &text[..text.len().min(400)]
                    );
                }
            }
            return SmtResult::Unknown;
        }
        write_executor_asserts(&mut smt, &conjuncts, lane, admitted_tree_nodes);
        smt.push_str("(check-sat)\n");
        smt.push_str("(get-model)\n");
        let build_dt = t_build.elapsed();

        // Timeout-class unknown memo (inc-13): a byte-identical query that
        // already exhausted an equal-or-larger budget in this context
        // short-circuits to Unknown instead of re-burning the executor.
        // See `executor_unknown_memo` for the soundness argument; kill
        // switch AY_EXEC_UNKNOWN_MEMO=0.
        let memo_enabled = super::executor_unknown_memo::executor_unknown_memo_enabled();
        let budget_ms = u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX);
        let query_fingerprint = if memo_enabled {
            let fp = super::executor_unknown_memo::fingerprint_query_text(&smt);
            if super::executor_unknown_memo::should_skip_query(fp, budget_ms) {
                if trace {
                    safe_eprintln!(
                        "[EXEC-TRACE {:?}] memo skip budget={budget_ms}ms smt_bytes={}",
                        std::thread::current().id(),
                        smt.len()
                    );
                }
                return SmtResult::Unknown;
            }
            Some(fp)
        } else {
            None
        };
        let t_solve_start = ay_core::time::Instant::now();

        // Step 4: Parse and execute via ay-dpll.
        let t_parse = ay_core::time::Instant::now();
        let commands = match ay_frontend::parse(&smt) {
            Ok(cmds) => cmds,
            Err(e) => {
                tracing::debug!("executor_adapter: parse error: {e}");
                if exec_trace_enabled() {
                    safe_eprintln!(
                        "[EXEC-TRACE {:?}] adapter early-return: parse error: {e}",
                        std::thread::current().id()
                    );
                }
                return SmtResult::Unknown;
            }
        };
        let parse_dt = t_parse.elapsed();

        // SHARED LANE — role must be Published. This is the executor lane of
        // `SmtContext::check_sat`, and `SmtContext::check_sat` is what the PDR
        // SAFETY VERIFIER runs on (`pdr/verification/model_safety.rs`,
        // `model_inductive.rs`, both reached from `verify_model_impl`). On that
        // path a false UNSAT becomes a false `Safe`. Labelling the lane
        // `InternalLemma` because *some* callers are search guidance would be
        // the caller-blind inference this role parameter exists to abolish, and
        // the "the engine re-derives its claim afterwards" justification is
        // circular here: the re-derivation's own queries come through here too.
        // A caller that is genuinely internal must declare it at ITS call site,
        // after audit. Until then the fail-safe answer is Published.
        let outputs = match execute_commands_via_executor_with_limits(
            &commands,
            ExecutorQueryRole::Published,
            ExecutorResourceLimits {
                deadline: Some(executor_deadline),
                term_memory_limit: self.term_memory_budget,
                cancellation: None,
            },
            new_search_executor,
        ) {
            Ok(out) => out,
            Err(()) => return SmtResult::Unknown,
        };

        // Step 5: Interpret the result.
        let t_model = ay_core::time::Instant::now();
        let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");
        let result = match result_str {
            "unsat" => SmtResult::Unsat,
            "sat" => {
                // Parse model from the second output (get-model response).
                let model_str = outputs.get(1).map(String::as_str).unwrap_or("");
                let mut model = propagated_model.clone();
                let dt_ctor_names: FxHashSet<String> = dt_decls
                    .iter()
                    .flat_map(|(_, ctors)| ctors.iter().map(|c| c.name.clone()))
                    .collect();
                parse_model_into(&mut model, model_str, &dt_ctor_names);
                if !install_uf_application_alias_values(&mut model, &uf_application_aliases) {
                    tracing::debug!(
                        "executor_adapter: scalar-UF application model is incomplete or inconsistent"
                    );
                    return SmtResult::Unknown;
                }
                if let Some((solved, original_vars)) = &solved {
                    if !solved.complete_model(original_vars, &mut model) {
                        return SmtResult::Unknown;
                    }
                }
                let validation_exprs = [original_expr];
                if let Some(model) =
                    accept_reparsed_sat_model(&validation_exprs, model, "executor_adapter")
                {
                    SmtResult::Sat(model)
                } else {
                    SmtResult::Unknown
                }
            }
            "unknown" => SmtResult::Unknown,
            other => {
                tracing::warn!(
                    "executor_adapter: unexpected result string: {other:?}, treating as Unknown"
                );
                SmtResult::Unknown
            }
        };
        let result = if Instant::now() >= executor_deadline || self.exact_term_memory_exceeded() {
            SmtResult::Unknown
        } else {
            result
        };
        // Memo recording (inc-13): only a RAW executor "unknown" that consumed
        // its budget counts as a timeout-class unknown. A SAT downgraded to
        // Unknown by model validation is an answered query and is never
        // memoised; fast structural unknowns are filtered inside the memo.
        if let Some(fp) = query_fingerprint {
            if result_str == "unknown" {
                let elapsed_ms =
                    u64::try_from(t_solve_start.elapsed().as_millis()).unwrap_or(u64::MAX);
                super::executor_unknown_memo::record_unknown_query(fp, budget_ms, elapsed_ms);
            }
        }
        if trace {
            safe_eprintln!(
                "[EXEC-TRACE {:?}] adapter build={:.1}ms parse={:.1}ms model+verify={:.1}ms smt_bytes={} vars={} conjuncts={} raw={} final_unknown={}",
                std::thread::current().id(),
                build_dt.as_secs_f64() * 1e3,
                parse_dt.as_secs_f64() * 1e3,
                t_model.elapsed().as_secs_f64() * 1e3,
                smt.len(),
                vars.len(),
                conjuncts.len(),
                result_str,
                matches!(result, SmtResult::Unknown)
            );
            // Slow-check capture (inc-13 attribution): dump the exact SMT-LIB
            // text of timeout-class checks for offline differential analysis.
            if let Some(dir) = ay_core::misc_cli_flags().chc_checksat_dump.as_deref() {
                let dt = t_build.elapsed();
                if result_str == "unknown"
                    || matches!(result, SmtResult::Unknown)
                    || dt.as_millis() > 500
                {
                    use std::sync::atomic::{AtomicUsize, Ordering};
                    static DUMP_SEQ: AtomicUsize = AtomicUsize::new(0);
                    let n = DUMP_SEQ.fetch_add(1, Ordering::Relaxed);
                    let path = format!("{dir}/check_{n:04}_{}ms_{result_str}.smt2", dt.as_millis());
                    let _ = std::fs::write(path, &smt);
                }
            }
        }
        if Instant::now() >= executor_deadline || self.exact_term_memory_exceeded() {
            SmtResult::Unknown
        } else {
            result
        }
    }
}

/// Dispatch a conjunction of expressions (background + assumptions) to ay-dpll's
/// Executor for full array theory support. Used by `IncrementalQueryContext` when
/// the internal DPLL(T) loop returns Unknown on array-containing formulas.
///
/// Combines all expressions into a single `(and ...)` assertion and runs it
/// through the executor. Returns `IncrementalCheckResult` matching the caller's
/// expected return type.
#[cfg(test)]
pub(crate) fn check_sat_conjunction_via_executor(
    exprs: &[ChcExpr],
    propagated_equalities: &FxHashMap<String, i128>,
    timeout: std::time::Duration,
) -> super::incremental::IncrementalCheckResult {
    check_sat_conjunction_via_executor_with_resource_limits(
        exprs,
        propagated_equalities,
        timeout,
        None,
        None,
    )
}

/// Incremental conjunction adapter under one caller-owned absolute envelope.
/// The relative timeout is intersected with both `caller_deadline` and the
/// ambient CHC solve deadline before admission starts; `term_memory_limit` is
/// installed on the fresh Executor rather than checked only on the caller's
/// unrelated term store.
pub(super) fn check_sat_conjunction_via_executor_with_resource_limits(
    exprs: &[ChcExpr],
    propagated_equalities: &FxHashMap<String, i128>,
    timeout: std::time::Duration,
    caller_deadline: Option<Instant>,
    term_memory_limit: Option<usize>,
) -> super::incremental::IncrementalCheckResult {
    use super::incremental::IncrementalCheckResult;

    // Closed under an effort, as `SmtContext::check_sat_via_executor_with_opts`.
    if crate::run_meter::close_route() {
        return IncrementalCheckResult::Unknown;
    }
    let Some(timeout_deadline) = Instant::now().checked_add(timeout) else {
        return IncrementalCheckResult::Unknown;
    };
    let executor_deadline = [
        caller_deadline,
        crate::smt::current_thread_solve_deadline(),
        super::deadline::current_smt_deadline(),
    ]
    .into_iter()
    .flatten()
    .fold(timeout_deadline, |deadline, outer| deadline.min(outer));
    if Instant::now() >= executor_deadline || ay_core::TermStore::global_memory_exceeded() {
        return IncrementalCheckResult::Unknown;
    }

    // Admit the original roots as one aggregate surface before cloning them
    // into a conjunction.  A per-root gate would reset node/name/sort caps,
    // while constructing the conjunction first would allocate from unbounded
    // caller input before the executor's fail-closed admission point.
    if let Err(reason) = collect_dt_declarations_for_exprs(exprs.iter()) {
        tracing::debug!(
            "executor_adapter (incremental): {reason}; returning Unknown before conjunction construction"
        );
        return IncrementalCheckResult::Unknown;
    }

    // Collect all free variables across all expressions for declarations.
    let combined = ChcExpr::and_all(exprs.iter().cloned());
    if Instant::now() >= executor_deadline || ay_core::TermStore::global_memory_exceeded() {
        return IncrementalCheckResult::Unknown;
    }
    let dt_decls = match collect_dt_declarations_for_expr(&[], &combined) {
        Ok(declarations) => declarations,
        Err(reason) => {
            tracing::debug!(
                "executor_adapter (incremental): {reason}; returning Unknown before recursive variable collection"
            );
            return IncrementalCheckResult::Unknown;
        }
    };
    let vars = combined.vars();
    if vars.is_empty() {
        return IncrementalCheckResult::Unknown;
    }

    // Rung 0: sort-unique names (see `check_sat_via_executor_with_opts`).
    let sort_renaming = super::sort_unique::SortUniqueRenaming::plan(&vars);
    let sort_renamed_exprs: Vec<ChcExpr>;
    let (exprs, combined, vars): (&[ChcExpr], ChcExpr, Vec<ChcVar>) = match &sort_renaming {
        Some(renaming) => {
            sort_renamed_exprs = exprs.iter().map(|e| renaming.apply(e)).collect();
            (
                &sort_renamed_exprs,
                renaming.apply(&combined),
                renaming.renamed_vars(&vars),
            )
        }
        // `dt_decls` borrows the original `combined`; a shallow (Arc) clone
        // keeps it alive on the common no-clash path.
        None => (exprs, combined.clone(), vars),
    };

    let logic = detect_logic(&vars, &combined);

    let mut smt = String::with_capacity(1024);
    smt.push_str(&format!("(set-logic {logic})\n"));
    smt.push_str("(set-option :produce-models true)\n");

    let timeout_ms = timeout.as_millis();
    if timeout_ms > 0 && timeout_ms < u128::from(u64::MAX) {
        smt.push_str(&format!("(set-option :timeout {timeout_ms})\n"));
    }

    // Declare datatypes before any constants that use them.
    match emit_declare_datatypes(&dt_decls) {
        Ok(declarations) => smt.push_str(&declarations),
        Err(reason) => {
            tracing::debug!(
                "executor_adapter (incremental): {reason}; returning Unknown instead of emitting invalid datatype declarations"
            );
            return IncrementalCheckResult::Unknown;
        }
    }

    let uf_decls = match collect_uninterpreted_function_declarations(&combined) {
        Ok(declarations) => declarations,
        Err(reason) => {
            tracing::debug!(
                "executor_adapter (incremental): {reason}; returning Unknown instead of emitting ambiguous declarations"
            );
            return IncrementalCheckResult::Unknown;
        }
    };
    for declaration in &uf_decls {
        smt.push_str(&emit_declare_uninterpreted_function(declaration));
    }

    for var in &vars {
        let sort_str = sort_to_smtlib(&var.sort);
        let name = quote_symbol(&var.name);
        smt.push_str(&format!("(declare-const {name} {sort_str})\n"));
    }

    let mut alias_counter = 0usize;
    let uf_application_aliases =
        match build_uf_application_aliases(std::iter::once(&combined), &mut alias_counter) {
            Ok(aliases) => aliases,
            Err(reason) => {
                tracing::debug!("executor_adapter (incremental): {reason}; returning Unknown");
                return IncrementalCheckResult::Unknown;
            }
        };
    let alias_script =
        match emit_uf_application_aliases(&uf_application_aliases, Some(executor_deadline)) {
            Ok(script) => script,
            Err(reason) => {
                tracing::debug!("executor_adapter (incremental): {reason}; returning Unknown");
                return IncrementalCheckResult::Unknown;
            }
        };
    smt.push_str(&alias_script);

    // Assert each expression separately, splitting top-level conjunctions
    // into individual asserts for DT axiom reachability (#7016).
    for expr in exprs {
        let conjuncts = expr.conjuncts();
        if let Some(reason) = conjuncts
            .iter()
            .find_map(|expr| unsupported_executor_expr_reason(expr))
        {
            tracing::debug!(
                "executor_adapter (incremental): unsupported SMT-LIB executor term: {reason}; returning Unknown"
            );
            return IncrementalCheckResult::Unknown;
        }
        for c in &conjuncts {
            let c_str = InvariantModel::expr_to_smtlib(c);
            smt.push_str(&format!("(assert {c_str})\n"));
        }
    }
    smt.push_str("(check-sat)\n");
    smt.push_str("(get-model)\n");
    if Instant::now() >= executor_deadline || ay_core::TermStore::global_memory_exceeded() {
        return IncrementalCheckResult::Unknown;
    }

    // Timeout-class unknown memo (inc-13) — same contract as the
    // `check_sat_via_executor` wiring; see `executor_unknown_memo`.
    let memo_enabled = super::executor_unknown_memo::executor_unknown_memo_enabled();
    let budget_ms = u64::try_from(timeout.as_millis()).unwrap_or(u64::MAX);
    let query_fingerprint = if memo_enabled {
        let fp = super::executor_unknown_memo::fingerprint_query_text(&smt);
        if super::executor_unknown_memo::should_skip_query(fp, budget_ms) {
            return IncrementalCheckResult::Unknown;
        }
        Some(fp)
    } else {
        None
    };
    let t_solve_start = ay_core::time::Instant::now();

    let commands = match ay_frontend::parse(&smt) {
        Ok(cmds) => cmds,
        Err(e) => {
            tracing::debug!("executor_adapter (incremental): parse error: {e}");
            return IncrementalCheckResult::Unknown;
        }
    };
    if Instant::now() >= executor_deadline || ay_core::TermStore::global_memory_exceeded() {
        return IncrementalCheckResult::Unknown;
    }

    // SHARED LANE — role must be Published, for the same reason as the
    // `check_sat_via_executor_with_opts` dispatch above: this incremental
    // conjunction check is reachable from the PDR verification gate, and no
    // audit has established that every caller is search guidance. Fail safe.
    let outputs = match execute_commands_via_executor_with_limits(
        &commands,
        ExecutorQueryRole::Published,
        ExecutorResourceLimits {
            deadline: Some(executor_deadline),
            term_memory_limit,
            cancellation: None,
        },
        new_search_executor,
    ) {
        Ok(out) => out,
        Err(()) => return IncrementalCheckResult::Unknown,
    };

    if Instant::now() >= executor_deadline || ay_core::TermStore::global_memory_exceeded() {
        return IncrementalCheckResult::Unknown;
    }

    let result_str = outputs.first().map(String::as_str).unwrap_or("unknown");
    if let Some(fp) = query_fingerprint {
        if result_str == "unknown" {
            let elapsed_ms = u64::try_from(t_solve_start.elapsed().as_millis()).unwrap_or(u64::MAX);
            super::executor_unknown_memo::record_unknown_query(fp, budget_ms, elapsed_ms);
        }
    }
    let result = match result_str {
        "unsat" => IncrementalCheckResult::Unsat,
        "sat" => {
            let model_str = outputs.get(1).map(String::as_str).unwrap_or("");
            let mut model = FxHashMap::default();
            // Merge propagated equalities into model.
            for (name, value) in propagated_equalities {
                model.insert(name.clone(), SmtValue::Int(*value));
            }
            let dt_ctor_names: FxHashSet<String> = dt_decls
                .iter()
                .flat_map(|(_, ctors)| ctors.iter().map(|c| c.name.clone()))
                .collect();
            parse_model_into(&mut model, model_str, &dt_ctor_names);
            if !install_uf_application_alias_values(&mut model, &uf_application_aliases) {
                tracing::debug!(
                    "executor_adapter (incremental): scalar-UF application model is incomplete or inconsistent"
                );
                return IncrementalCheckResult::Unknown;
            }
            let validation_exprs: Vec<&ChcExpr> = exprs.iter().collect();
            if let Some(model) = accept_reparsed_sat_model(
                &validation_exprs,
                model,
                "executor_adapter (incremental)",
            ) {
                IncrementalCheckResult::Sat(model)
            } else {
                IncrementalCheckResult::Unknown
            }
        }
        "unknown" => IncrementalCheckResult::Unknown,
        other => {
            tracing::warn!(
                "executor_adapter (incremental): unexpected result string: {other:?}, treating as Unknown"
            );
            IncrementalCheckResult::Unknown
        }
    };
    if Instant::now() >= executor_deadline || ay_core::TermStore::global_memory_exceeded() {
        IncrementalCheckResult::Unknown
    } else {
        result
    }
}

#[cfg(test)]
mod tests;

#[cfg(test)]
mod cancellation_tests;

#[cfg(test)]
mod array_lambda_executor_tests {
    use super::*;
    use crate::{ChcOp, ChcParser};
    use std::sync::Arc;

    fn captured_lambda() -> ChcExpr {
        let index = ChcVar::new("i", ChcSort::Int);
        ChcExpr::array_lambda(
            index.clone(),
            ChcExpr::Op(
                ChcOp::Add,
                vec![
                    Arc::new(ChcExpr::Var(index)),
                    Arc::new(ChcExpr::Var(ChcVar::new("outer value", ChcSort::Int))),
                ],
            ),
        )
        .unwrap()
    }

    #[test]
    fn lambda_bound_uf_is_declared_without_a_global_observation_alias() {
        let index = ChcVar::new("i", ChcSort::Int);
        let lambda = ChcExpr::array_lambda(
            index.clone(),
            ChcExpr::FuncApp(
                "f".into(),
                ChcSort::Int,
                vec![Arc::new(ChcExpr::Var(index))],
            ),
        )
        .unwrap();
        let declarations =
            collect_uninterpreted_function_declarations_for_exprs([&lambda]).unwrap();
        assert_eq!(declarations.len(), 1);
        assert_eq!(declarations[0].name, "f");
        assert_eq!(
            collect_uninterpreted_function_applications_for_exprs([&lambda]).unwrap(),
            [] as [ChcExpr; 0]
        );
    }

    #[test]
    fn lambda_and_outer_shared_uf_keep_distinct_observation_scopes() {
        let lambda = ChcExpr::array_lambda(
            ChcVar::new("i", ChcSort::Int),
            ChcExpr::FuncApp("f".into(), ChcSort::Int, vec![Arc::new(ChcExpr::Int(7))]),
        )
        .unwrap();
        let ChcExpr::ArrayLambda(info) = &lambda else {
            unreachable!()
        };
        // Stack order visits the shared node first under the lambda. Its
        // later outer occurrence must still receive a global observation.
        let applications =
            collect_uninterpreted_function_applications_for_exprs([info.body().as_ref(), &lambda])
                .unwrap();
        assert_eq!(applications.len(), 1);
        assert_eq!(&applications[0], info.body().as_ref());
    }

    #[test]
    fn bounded_lambda_writer_roundtrips_quoted_capture_and_parallel_let() {
        let lambda = captured_lambda();
        let mut script = BoundedUfAliasScript::new(32_768);
        let mut work = 0;
        script.write_expr(&lambda, &mut work, 32_768, None).unwrap();
        assert!(script.text.contains("|outer value|"), "{}", script.text);
        let query = format!(
            "(set-logic HORN) (declare-var |outer value| Int) \
             (declare-rel error ()) \
             (rule (=> (not (= (select {} 4) 11)) error)) (query error)",
            script.text,
        );
        ChcParser::parse(&query).expect("same lexical scopes after bounded serialization");
        assert!(work > 0);
    }

    #[test]
    fn bounded_lambda_writer_respects_output_and_work_limits() {
        let lambda = captured_lambda();
        let mut small = BoundedUfAliasScript::new(8);
        assert_eq!(
            small.write_expr(&lambda, &mut 0, 32_768, None),
            Err(UfApplicationAliasEmissionError::ResourceLimit(
                "emitted bytes"
            ))
        );
        let mut small = BoundedUfAliasScript::new(32_768);
        assert_eq!(
            small.write_expr(&lambda, &mut 0, 1, None),
            Err(UfApplicationAliasEmissionError::ResourceLimit(
                "serializer work"
            ))
        );
    }
}
