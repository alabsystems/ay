// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Owning, fail-closed construction of cooperative floating-point circuits.

pub(crate) mod control;
mod terms;

#[cfg(test)]
mod tests;

use std::fmt;

use ay_core::CnfClause;

use self::control::{BuildControl, Cooperative};
use crate::{FpDecomposed, FpEncodingCache, FpSolver, RmOperand};

/// A cooperative checkpoint in floating-point circuit construction.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FpBuildStage {
    /// Before admitting a solver into an owning construction attempt.
    Setup,
    /// Before recursive term traversal, cache copying or cache admission.
    Term,
    /// At an arithmetic operation boundary.
    Operation,
    /// At a multiplier boundary or before its next shift-and-add row.
    MultiplyRow,
    /// At a divider boundary or before its next restoring-division row.
    DivideRow,
    /// Before the next remainder modular-exponentiation row.
    RemainderExponent,
    /// Before finalization and again after discarding solver-only state.
    Finalize,
}

/// Current retained CNF counts, not an allocator or process-RSS measurement.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FpBuildProgress {
    /// Construction boundary being polled.
    pub stage: FpBuildStage,
    /// Allocated variable frontier (including any imported namespace).
    pub variables: u32,
    /// Number of clauses retained by this construction attempt.
    pub clauses: usize,
}

/// Terminal refusal of an owning floating-point construction attempt.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum FpBuildError {
    /// A stop was observed, or a previous operation unwound before completion.
    Interrupted,
    /// A checkpoint observed variables outside the positive CNF namespace.
    VariableLimit,
}

impl fmt::Display for FpBuildError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Interrupted => f.write_str("floating-point construction interrupted"),
            Self::VariableLimit => f.write_str("floating-point CNF variable limit exceeded"),
        }
    }
}

impl std::error::Error for FpBuildError {}

/// Encoding released only after successful construction and a final stop check.
///
/// This is not a satisfiability verdict or a proof certificate. The consumer
/// must preserve the cache's CNF namespace, link pending conditions, honor
/// encoding gaps, and continue checking its original deadline/stop owner during
/// clause transfer, SAT solving and final result admission.
#[derive(Debug)]
pub struct FpBuiltEncoding {
    /// All retained clauses, transferred without cloning.
    pub clauses: Vec<CnfClause>,
    /// Conditions still requiring links to the caller's Boolean encoding.
    pub pending_condition_links: Vec<(u32, u32)>,
    /// Every persisted variable-bearing cache, transferred without cloning.
    pub cache: FpEncodingCache,
    /// Semantic incompleteness, separate from construction cancellation.
    pub has_encoding_gap: bool,
}

/// An owning attempt that never exports clauses or caches after refusal.
///
/// Recursive term entry points carry control through FP, Boolean and BV inputs,
/// conversions and arithmetic shortcuts. Multiplication, division, square root
/// and remainder also poll inside their arithmetic rows and modular-exponentiation loops.
/// Other arithmetic helpers, individual gate allocations and destruction are
/// not yet cooperatively bounded within each operation checkpoint. A caller
/// that needs a hard memory bound must also enforce a process memory budget.
/// The variable-limit check observes the frontier at these checkpoints; it does
/// not reserve space for an entire circuit chunk. Near namespace exhaustion the
/// existing encoder may panic before its next check. If that unwind is caught,
/// this attempt remains poisoned and cannot publish an encoding.
///
/// Decompositions must be valid, same-format operands produced by the supplied
/// solver (or by this attempt), with its unchanged CNF namespace. This API does
/// not authenticate arbitrary decompositions or imported caches. Preparing the
/// supplied solver is outside this attempt's checkpoints.
pub struct FpConstruction<'terms, 'control> {
    solver: FpSolver<'terms>,
    control: Cooperative<'control>,
    // Remains set if an encoder unwinds after a healthy callback. Only a fully
    // completed operation may clear it; catching a panic cannot permit export.
    operation_pending: bool,
}

impl fmt::Debug for FpConstruction<'_, '_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("FpConstruction")
            .field("variables", &self.solver.next_var.saturating_sub(1))
            .field("clauses", &self.solver.clauses.len())
            .field("refusal", &self.control.refusal())
            .field("operation_pending", &self.operation_pending)
            .finish_non_exhaustive()
    }
}

impl<'terms, 'control> FpConstruction<'terms, 'control> {
    /// Take exclusive ownership and poll the supplied stop callback immediately.
    ///
    /// A callback result of `true` means stop. Once observed, refusal is sticky
    /// even if the caller later resets its cancellation token.
    pub fn new(
        solver: FpSolver<'terms>,
        should_stop: &'control mut dyn FnMut(FpBuildProgress) -> bool,
    ) -> Result<Self, FpBuildError> {
        let mut control = Cooperative::new(should_stop);
        control.checkpoint(solver.construction_progress(FpBuildStage::Setup))?;
        Ok(Self {
            solver,
            control,
            operation_pending: false,
        })
    }

    /// Start a fresh closed-DATA CNF namespace with no external Tseitin names.
    ///
    /// BV leaf/constant/raw-extract guards of width 1..=64 share this solver's
    /// input cache. No supplied solver/cache/frontier can enter here, and the
    /// owning API never exposes a mutable solver or cache-import operation.
    /// Transfer EVERY clause/root and source-input link before using the DATA.
    /// This is not a source, satisfiability or proof credential.
    pub fn new_closed_data(
        terms: &'terms ay_core::TermStore,
        should_stop: &'control mut dyn FnMut(FpBuildProgress) -> bool,
    ) -> Result<Self, FpBuildError> {
        let mut solver = FpSolver::new(terms);
        solver.condition_namespace = crate::closed_data::ConditionNamespace::ClosedData;
        Self::new(solver, should_stop)
    }

    /// Encode IEEE division, refusing the entire attempt on interruption.
    pub fn try_make_div(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
        rm: impl Into<RmOperand>,
    ) -> Result<FpDecomposed, FpBuildError> {
        let rm = rm.into();
        self.encode(|solver, control| solver.make_div_with_control(x, y, rm, control))
    }

    /// Encode IEEE/SMT remainder (not Rust's truncating `%` operation).
    pub fn try_make_rem(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
    ) -> Result<FpDecomposed, FpBuildError> {
        self.encode(|solver, control| solver.make_rem_with_control(x, y, control))
    }

    /// Encode truncating-quotient remainder, distinct from SMT `fp.rem`.
    ///
    /// Finite results have the dividend's sign, including zero, and are exact:
    /// no rounded divide/multiply/subtract sequence is used. NaN is the
    /// existing logical FP NaN; this does not specify Rust's observable NaN
    /// payload/sign bits or certify a consumer's source-to-circuit lowering.
    /// The same operand/namespace contract and sticky owner as division apply.
    pub fn try_make_truncating_rem(
        &mut self,
        x: &FpDecomposed,
        y: &FpDecomposed,
    ) -> Result<FpDecomposed, FpBuildError> {
        self.encode(|solver, control| solver.make_truncating_rem_with_control(x, y, control))
    }

    fn encode<T>(
        &mut self,
        build: impl FnOnce(&mut FpSolver<'terms>, &mut Cooperative<'control>) -> Result<T, FpBuildError>,
    ) -> Result<T, FpBuildError> {
        self.begin_operation()?;
        self.control
            .checkpoint(self.solver.construction_progress(FpBuildStage::Operation))?;
        let result = build(&mut self.solver, &mut self.control)?;
        self.control
            .checkpoint(self.solver.construction_progress(FpBuildStage::Operation))?;
        self.operation_pending = false;
        Ok(result)
    }

    fn begin_operation(&mut self) -> Result<(), FpBuildError> {
        if self.operation_pending {
            return Err(self.control.interrupt());
        }
        if let Some(error) = self.control.refusal() {
            return Err(error);
        }
        self.operation_pending = true;
        Ok(())
    }

    /// Consume the attempt and move its encoding out only if it is complete.
    ///
    /// Finalization polls both before and after dropping solver-only state. No
    /// partial cache or clause accessor is available on an unfinished attempt.
    pub fn finish(self) -> Result<FpBuiltEncoding, FpBuildError> {
        let Self {
            solver,
            mut control,
            operation_pending,
        } = self;
        if operation_pending {
            return Err(control.interrupt());
        }
        let progress = solver.construction_progress(FpBuildStage::Finalize);
        control.checkpoint(progress)?;
        // Both destructurings are exhaustive: adding a solver/cache owner must
        // force an explicit decision about preserving or discarding its state.
        let FpSolver {
            terms: _,
            term_to_fp,
            bv_term_bits,
            clauses,
            next_var,
            check_count: _,
            conflict_count: _,
            propagation_count: _,
            debug: _,
            cached_false,
            cached_true,
            term_to_cnf,
            condition_namespace: _,
            pending_condition_links,
            bool_input_lits,
            has_encoding_gap,
            to_bv_unspec_sites,
            ieee_nan_encodings,
            rm_terms,
        } = solver;
        drop(term_to_cnf);
        let cache = FpEncodingCache {
            term_to_fp,
            bv_term_bits,
            next_var,
            cached_false,
            cached_true,
            bool_input_lits,
            to_bv_unspec_sites,
            ieee_nan_encodings,
            rm_terms,
        };
        control.checkpoint(progress)?;
        Ok(FpBuiltEncoding {
            clauses,
            pending_condition_links,
            cache,
            has_encoding_gap,
        })
    }
}

impl FpSolver<'_> {
    pub(crate) fn construction_progress(&self, stage: FpBuildStage) -> FpBuildProgress {
        FpBuildProgress {
            stage,
            variables: self.next_var.saturating_sub(1),
            clauses: self.clauses.len(),
        }
    }
}
