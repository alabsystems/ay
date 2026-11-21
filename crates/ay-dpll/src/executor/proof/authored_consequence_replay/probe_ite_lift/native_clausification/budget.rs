// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! One original leaf-repair allowance, shared across planning and owned copies.

use super::{replay_note, Executor};
use std::{cell::RefCell, rc::Rc};

const MAX_WORK: usize = 1_048_576;
const MAX_STORAGE: usize = 8_388_608;

struct State {
    work: usize,
    storage: usize,
    refused: bool,
    polling: bool,
}

struct Owner {
    state: RefCell<State>,
    stop: Box<dyn Fn() -> bool>,
}

/// Cloning retains the SAME allowance and sticky refusal, with no authority.
#[derive(Clone)]
pub(super) struct RepairBudget(Rc<Owner>);

impl RepairBudget {
    pub(super) fn new(exec: &Executor) -> Self {
        Self(Rc::new(Owner {
            state: RefCell::new(State {
                work: MAX_WORK,
                storage: MAX_STORAGE,
                refused: false,
                polling: false,
            }),
            stop: Box::new(exec.make_proof_assembly_should_stop()),
        }))
    }

    pub(super) fn pay(&self, work: usize, storage: usize) -> bool {
        {
            let mut state = self.0.state.borrow_mut();
            if state.refused || state.polling {
                state.refused = true;
                return false;
            }
            let (Some(next_work), Some(next_storage)) = (
                state.work.checked_sub(work),
                state.storage.checked_sub(storage),
            ) else {
                let remaining_work = state.work;
                let remaining_storage = state.storage;
                state.refused = true;
                drop(state);
                replay_note(|| {
                    format!(
                        "native-repair-budget: exhausted requested_work={work} \
                         remaining_work={remaining_work} requested_storage={storage} \
                         remaining_storage={remaining_storage}"
                    )
                });
                return false;
            };
            state.work = next_work;
            state.storage = next_storage;
            state.polling = true;
        }
        struct OnUnwind<'a>(&'a RepairBudget, bool);
        impl Drop for OnUnwind<'_> {
            fn drop(&mut self) {
                if self.1 {
                    let mut state = self.0 .0.state.borrow_mut();
                    state.refused = true;
                    state.polling = false;
                }
            }
        }
        let mut unwind = OnUnwind(self, true);
        let stopped = (self.0.stop)();
        let mut state = self.0.state.borrow_mut();
        state.polling = false;
        state.refused |= stopped;
        unwind.1 = false;
        let live = !state.refused;
        let remaining_work = state.work;
        let remaining_storage = state.storage;
        drop(state);
        if stopped {
            replay_note(|| {
                format!(
                    "native-repair-budget: stopped remaining_work={remaining_work} \
                     remaining_storage={remaining_storage}"
                )
            });
        }
        live
    }

    pub(super) fn refuse(&self) -> Option<()> {
        let (remaining_work, remaining_storage) = {
            let mut state = self.0.state.borrow_mut();
            state.refused = true;
            (state.work, state.storage)
        };
        replay_note(|| {
            format!(
                "native-repair-budget: explicit refusal remaining_work={remaining_work} \
                 remaining_storage={remaining_storage}"
            )
        });
        None
    }

    pub(super) fn remaining(&self) -> (usize, usize) {
        let state = self.0.state.borrow();
        (state.work, state.storage)
    }

    pub(super) fn reserve<T>(&self, values: &mut Vec<T>, count: usize) -> Option<()> {
        let Some(bytes) = values
            .len()
            .checked_add(count)
            .and_then(|n| n.checked_add(values.len()))
            .and_then(|n| n.checked_mul(std::mem::size_of::<T>()))
            .and_then(|n| n.checked_mul(2))
        else {
            return self.refuse();
        };
        if !self.pay(count, bytes) || values.try_reserve_exact(count).is_err() {
            return self.refuse();
        }
        Some(())
    }

    #[cfg(test)]
    pub(super) fn set_remaining(&self, work: usize, storage: usize) {
        let mut state = self.0.state.borrow_mut();
        state.work = work;
        state.storage = storage;
    }
}
