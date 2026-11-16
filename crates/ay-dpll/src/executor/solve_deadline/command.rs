// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Lifetime of the one complete decision deadline, including certification.

use super::{Instant, SolveDeadlineCell};
use ay_core::resource::{CheckStopScope, Exhausted, Guard};
use std::sync::atomic::{AtomicBool, AtomicUsize, Ordering};
use std::sync::{Arc, Mutex, PoisonError};

#[derive(Debug, Clone, Default)]
pub(crate) struct CommandDeadlineState {
    state: Arc<State>,
}

#[derive(Debug, Default)]
struct State {
    depth: AtomicUsize,
    has_owner: AtomicBool,
    owner: Mutex<Option<Guard>>,
}

impl CommandDeadlineState {
    pub(crate) fn active(&self) -> bool {
        self.state.depth.load(Ordering::Acquire) != 0
    }

    /// The original caller's live limits, never a search-local slice created
    /// by this command. This borrows authority and grants no work.
    pub(crate) fn owner_stop(&self) -> Option<Exhausted> {
        if !self.state.has_owner.load(Ordering::Acquire) {
            return None;
        }
        let owner = self
            .state
            .owner
            .lock()
            .unwrap_or_else(PoisonError::into_inner)
            .clone();
        // Resource observers may run while polling. Keep their work outside
        // the command-state lock.
        owner.as_ref().and_then(Guard::poll)
    }

    fn enter(&self, owner: Option<&Guard>) -> Option<CheckStopScope> {
        if self.state.depth.fetch_add(1, Ordering::AcqRel) != 0 {
            return None;
        }
        let owner = owner?.clone();
        *self
            .state
            .owner
            .lock()
            .unwrap_or_else(PoisonError::into_inner) = Some(owner.clone());
        self.state.has_owner.store(true, Ordering::Release);
        // Unlike the command's later search nodes, this is an original
        // caller boundary. Retain it under Certify's CancelOnly edge too.
        let previous = ay_core::resource::current_check_stop();
        Some(ay_core::resource::enter_check_stop(Arc::new(move || {
            owner.poll().is_some()
                || match &previous {
                    Ok(Some(stop)) => stop(),
                    Ok(None) => false,
                    Err(_) => true,
                }
        })))
    }

    fn leave(&self) {
        if self.state.depth.fetch_sub(1, Ordering::AcqRel) == 1 {
            self.state.has_owner.store(false, Ordering::Release);
            self.state
                .owner
                .lock()
                .unwrap_or_else(PoisonError::into_inner)
                .take();
        }
    }
}

/// A relative allowance planned once, before search starts, together with
/// the external owner whose limits it must not renew or escape.
#[derive(Clone, Debug)]
pub(crate) struct DecisionDeadlinePlan {
    pub(crate) deadline: Option<Instant>,
    pub(crate) owner: Option<Guard>,
}

/// Restore both predecessor deadlines on return or unwind. The scope also
/// prevents retries and nested checks from starting a new relative window.
#[must_use = "the command deadline is restored when this scope drops"]
pub(crate) struct CommandDeadlineScope {
    solve: SolveDeadlineCell,
    certification: SolveDeadlineCell,
    previous: (Option<Instant>, Option<Instant>),
    command: CommandDeadlineState,
    was_active: bool,
    _owner_stop: Option<CheckStopScope>,
    _thread: std::marker::PhantomData<std::rc::Rc<()>>,
}

impl CommandDeadlineScope {
    pub(crate) fn snapshot(
        solve: &SolveDeadlineCell,
        certification: &SolveDeadlineCell,
        command: &CommandDeadlineState,
        owner: Option<&Guard>,
    ) -> Self {
        let previous = (solve.get(), certification.get());
        let was_active = command.active();
        let owner_stop = command.enter(owner);
        Self {
            solve: solve.clone(),
            certification: certification.clone(),
            previous,
            command: command.clone(),
            was_active,
            _owner_stop: owner_stop,
            _thread: std::marker::PhantomData,
        }
    }

    pub(crate) fn was_active(&self) -> bool {
        self.was_active
    }

    #[cfg(test)]
    pub(crate) fn previous(&self) -> (Option<Instant>, Option<Instant>) {
        self.previous
    }
}

impl Drop for CommandDeadlineScope {
    fn drop(&mut self) {
        self.solve.set(self.previous.0);
        self.certification.set(self.previous.1);
        self.command.leave();
    }
}

/// Restore a solve-local wall before returning to publication, then close a
/// command this raw call started. An existing outer command stays installed.
#[must_use = "the solve-local wall is restored when this scope drops"]
pub(crate) struct SolveCallDeadlineScope {
    solve: SolveDeadlineCell,
    previous: Option<Instant>,
    _command: Option<CommandDeadlineScope>,
}

impl SolveCallDeadlineScope {
    pub(crate) fn snapshot(
        solve: &SolveDeadlineCell,
        command: Option<CommandDeadlineScope>,
    ) -> Self {
        Self {
            solve: solve.clone(),
            previous: solve.get(),
            _command: command,
        }
    }

    #[cfg(test)]
    pub(crate) fn previous(&self) -> Option<Instant> {
        self._command
            .as_ref()
            .map_or(self.previous, |command| command.previous().0)
    }
}

impl Drop for SolveCallDeadlineScope {
    fn drop(&mut self) {
        self.solve.set(self.previous);
    }
}
