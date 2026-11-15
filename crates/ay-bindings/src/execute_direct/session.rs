// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0
// Author: Andrew Yates

//! Stepwise in-process session (#execution-session).
//!
//! [`super::execute_incremental`] runs a whole multi-`check-sat` program that
//! was built up front. A verifier that checks every obligation of one function
//! against a shared context wants the same solver driven STEP BY STEP: declare,
//! push a context cell, assert its facts once, then for each row push, assert
//! the row's own conjuncts, check, and pop — deciding what to assert next from
//! what came back, under a per-check deadline.
//!
//! # What a check certifies
//!
//! Each `check_sat` is an ordinary public decision of the underlying solver,
//! so an UNSAT goes through the same mandatory strict certification a one-shot
//! solve does, and its proof premises are drawn from the assertions LIVE at
//! that check: the frontend truncates the assertion stack on `pop`, the
//! query's authored scope is captured from that stack when the check begins,
//! and the strict checker rejects any `assume` outside it. Learned clauses and
//! theory lemmas the solver carries between checks are re-derived or
//! re-validated inside the proof, never admitted as premises.
//!
//! The outcome names the problem it was decided against by
//! [`SessionCheck::live_scope_digest`]: a Merkle digest over the header
//! (logic and options), every live declaration and definition (bodies
//! included) and the live assertions in assertion order (each assertion's
//! node digest, see [`ExecutionSession::assertion_digest`]); `pop` restores
//! the digest the session had at the matching `push`. Two sessions that
//! differ in any of those differ in the digest (`digest.rs`).
//!
//! # Interruption and faults
//!
//! A check that times out or is interrupted answers `unknown` and leaves the
//! stack exactly as it was, so `pop` and further checks are valid; the
//! interrupt flag is cleared when the check returns, so an interrupt cancels
//! at most the check in flight. A solver PANIC poisons the session: its state
//! is suspect, so every later call returns an error rather than a verdict.

use std::sync::atomic::AtomicBool;
use std::sync::Arc;
use std::time::Duration;

use super::context::{catch_execute_stage, ExecutionContext};
use super::digest::ScopeDigests;
use super::incremental::{execute_constraint_safe, run_check_sat, ArtifactTransport};
use super::logic::parse_logic;
use super::translate::translate_expr;
use super::types::{CheckSatOutcome, ExecuteDegradationKind, ExecuteError};
use crate::constraint::Constraint;
use crate::program::AYProgram;
use crate::Expr;

/// One check of an [`ExecutionSession`].
#[derive(Debug, Clone)]
#[non_exhaustive]
pub struct SessionCheck {
    /// The verdict, model, degradation and (for UNSAT) the proof artifact.
    pub outcome: CheckSatOutcome,
    /// Number of assertions live at this check.
    pub live_assertions: usize,
    /// Chain digest of the assertions live at this check.
    pub live_scope_digest: [u8; 32],
}

/// A push/pop solver session driven one command at a time.
pub struct ExecutionSession {
    ctx: ExecutionContext,
    digests: ScopeDigests,
    check_sat_index: usize,
    poisoned: Option<String>,
}

impl std::fmt::Debug for ExecutionSession {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ExecutionSession")
            .field("depth", &self.digests.depth())
            .field("check_sat_index", &self.check_sat_index)
            .field("live_assertions", &self.digests.live())
            .field("poisoned", &self.poisoned)
            .finish_non_exhaustive()
    }
}

impl ExecutionSession {
    /// Open a session from a HEADER program: its logic and options, and any
    /// declarations or definitions it lists. A header that asserts, pushes,
    /// pops or checks is refused — those are session steps.
    ///
    /// # Errors
    ///
    /// An unsupported logic, a header command that is not a declaration, or a
    /// declaration the solver refuses.
    pub fn new(header: &AYProgram) -> Result<Self, ExecuteError> {
        let logic = parse_logic(header)?;
        let digests = ScopeDigests::new(header.get_logic().unwrap_or_default(), header.options());
        let mut ctx = ExecutionContext::new(logic, header)?;
        for (name, value) in header.options() {
            execute_constraint_safe(
                &mut ctx,
                &Constraint::set_option(name.clone(), value.clone()),
            )?;
        }
        let mut session = Self {
            ctx,
            digests,
            check_sat_index: 0,
            poisoned: None,
        };
        for command in header.commands() {
            session.declare(command)?;
        }
        Ok(session)
    }

    /// Execute one declaration, definition or option.
    ///
    /// # Errors
    ///
    /// A command that is not a declaration, definition, option or logic, or
    /// one the solver refuses.
    pub fn declare(&mut self, command: &Constraint) -> Result<(), ExecuteError> {
        self.live()?;
        match command {
            Constraint::SetLogic(_)
            | Constraint::SetOption { .. }
            | Constraint::DeclareConst { .. }
            | Constraint::DeclareFun { .. }
            | Constraint::DefineFun { .. }
            | Constraint::DeclareVar { .. }
            | Constraint::DeclareDatatype(_) => {
                execute_constraint_safe(&mut self.ctx, command)?;
                self.digests.declare(command);
                Ok(())
            }
            other => Err(ExecuteError::ConstraintExecution(format!(
                "execution session: {other:?} is a session step, not a declaration"
            ))),
        }
    }

    /// Open a scope.
    ///
    /// # Errors
    ///
    /// The session is poisoned, or the solver refuses the push.
    pub fn push(&mut self) -> Result<(), ExecuteError> {
        self.live()?;
        execute_constraint_safe(&mut self.ctx, &Constraint::Push)?;
        self.digests.push();
        Ok(())
    }

    /// Close the innermost scope, dropping every assertion made in it.
    ///
    /// # Errors
    ///
    /// No scope is open, the session is poisoned, or the solver refuses.
    pub fn pop(&mut self) -> Result<(), ExecuteError> {
        self.live()?;
        if self.digests.depth() == 0 {
            return Err(ExecuteError::ConstraintExecution(
                "execution session: pop with no open scope".to_string(),
            ));
        }
        execute_constraint_safe(&mut self.ctx, &Constraint::Pop(1))?;
        self.digests.pop();
        Ok(())
    }

    /// Assert `expr` in the innermost scope and return its node digest.
    ///
    /// # Errors
    ///
    /// The session is poisoned, `expr` is not a Boolean the solver accepts,
    /// or translation fails.
    pub fn assert(&mut self, expr: &Expr) -> Result<[u8; 32], ExecuteError> {
        self.live()?;
        let term = self.translate(expr)?;
        let asserted = catch_execute_stage(
            || super::assertion_source::assert_with_source(&mut self.ctx, term, expr),
            |reason| Err(ExecuteError::Internal(format!("assert panic: {reason}"))),
        );
        if let Err(ExecuteError::Internal(reason)) = &asserted {
            self.poisoned = Some(reason.clone());
        }
        asserted?;
        Ok(self.digests.assert(expr))
    }

    /// Decide the live assertion stack, under `timeout` when given.
    ///
    /// # Errors
    ///
    /// The session is poisoned. A solver panic during the check poisons the
    /// session and is reported here as an `unknown` outcome.
    pub fn check_sat(&mut self, timeout: Option<Duration>) -> Result<SessionCheck, ExecuteError> {
        self.live()?;
        let next_index = self.check_sat_index.checked_add(1).ok_or_else(|| {
            ExecuteError::ConstraintExecution(
                "execution session: check-sat index overflow".to_string(),
            )
        })?;
        self.ctx.solver.set_timeout(timeout);
        let outcome = run_check_sat(
            &mut self.ctx,
            self.check_sat_index,
            ArtifactTransport::SessionTranscript,
        );
        self.ctx.solver.set_timeout(None);
        self.ctx.solver.clear_interrupt();
        self.check_sat_index = next_index;
        let outcome = outcome?;
        if outcome
            .degradation
            .as_ref()
            .is_some_and(|degradation| degradation.kind == ExecuteDegradationKind::SolverPanic)
        {
            self.poisoned = outcome.degradation.as_ref().map(|d| d.message.clone());
        }
        Ok(SessionCheck {
            outcome,
            live_assertions: self.digests.live(),
            live_scope_digest: self.digests.scope(),
        })
    }

    /// Merkle digest of `expr` as [`Self::assert`] would chain it. Computing
    /// it leaves the session's tables as they were.
    #[must_use]
    pub fn assertion_digest(&self, expr: &Expr) -> [u8; 32] {
        self.digests.node(expr)
    }

    /// The live-scope digest of this session's live header and declarations
    /// beside a stack of assertions with these node digests, in assertion
    /// order — what [`SessionCheck::live_scope_digest`] reports for that
    /// stack. A caller binds an outcome to the row it meant by recomputing
    /// this from its own record of the row's assertions.
    #[must_use]
    pub fn scope_digest_of(&self, assertions: &[[u8; 32]]) -> [u8; 32] {
        self.digests.live_digest_of(assertions)
    }

    /// Chain digest of the live assertion stack.
    #[must_use]
    pub fn live_scope_digest(&self) -> [u8; 32] {
        self.digests.scope()
    }

    /// Number of live assertions.
    #[must_use]
    pub fn live_assertions(&self) -> usize {
        self.digests.live()
    }

    /// Number of open scopes.
    #[must_use]
    pub fn depth(&self) -> usize {
        self.digests.depth()
    }

    /// Handle that interrupts the check in flight from another thread.
    #[must_use]
    pub fn interrupt_handle(&self) -> Arc<AtomicBool> {
        self.ctx.solver.interrupt_handle()
    }

    /// Why the session refuses further steps, if it does.
    #[must_use]
    pub fn poisoned(&self) -> Option<&str> {
        self.poisoned.as_deref()
    }

    /// Distinct expression nodes whose translation is currently memoized.
    #[must_use]
    pub fn memoized_nodes(&self) -> usize {
        self.ctx.translation_memo.len()
    }

    fn translate(&mut self, expr: &Expr) -> Result<ay_dpll::api::Term, ExecuteError> {
        let translated = catch_execute_stage(
            || translate_expr(&mut self.ctx, expr),
            |reason| {
                Err(ExecuteError::Internal(format!(
                    "translation panic: {reason}"
                )))
            },
        );
        if let Err(ExecuteError::Internal(reason)) = &translated {
            self.poisoned = Some(reason.clone());
        }
        translated
    }

    fn live(&self) -> Result<(), ExecuteError> {
        match &self.poisoned {
            Some(reason) => Err(ExecuteError::Internal(format!(
                "execution session is poisoned by an earlier solver fault: {reason}"
            ))),
            None => Ok(()),
        }
    }
}
