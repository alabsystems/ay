// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Serialized process-environment mutation for tests — THE blessed choke
//! point for `std::env::set_var` / `std::env::remove_var` across the workspace.
//!
//! `std::env::set_var`/`remove_var` mutate process-global state: unserialized
//! use races parallel test threads and any reader that consults the environment
//! mid-flight. The Trust toolchain's deny-by-default `ENV_MUTATION` lint
//! therefore forbids calling them directly; every mutation must route through
//! this module, which
//! (a) serializes mutation behind one process-wide lock, and
//! (b) restores the previous value on scope exit, even on panic.
//!
//! This module is the ONLY sanctioned home for the raw `set_var`/`remove_var`
//! calls: the item-level `#[allow(unknown_lints, env_mutation)]` attributes
//! below sit exactly on the RAII set/restore boundaries and nowhere else. Every
//! other site in the workspace routes through the helpers here. (`unknown_lints`
//! keeps the stock-rustc build green — the lint name is Trust-only.)
//!
//! Patterns:
//! - whole-test fixed values: [`with_serialized_env_vars`] /
//!   [`with_serialized_env_vars_removed`]
//! - set/remove sequences probing a knob's parser: [`with_env_edits`]
//! - guard style inside an existing serialization scope: [`lock_env`] +
//!   [`ScopedEnvVar::set`] / [`ScopedEnvVar::unset`]

use std::sync::{Mutex, MutexGuard, OnceLock};

/// One process-wide lock for all environment mutation in a test binary.
fn env_mutex() -> &'static Mutex<()> {
    static LOCK: OnceLock<Mutex<()>> = OnceLock::new();
    LOCK.get_or_init(|| Mutex::new(()))
}

/// Acquire the process-wide environment lock explicitly.
///
/// For tests that need guard-style scoping ([`ScopedEnvVar`]) across a whole
/// test body. Hold the returned guard for as long as the mutated environment
/// must stay in place. A poisoned lock (a previous test panicked while holding
/// it) is recovered: the guards below restore state on unwind, so the
/// environment is consistent even after a panic.
pub fn lock_env() -> MutexGuard<'static, ()> {
    env_mutex().lock().unwrap_or_else(|e| e.into_inner())
}

/// RAII guard: sets or removes one env var, restoring the previous state on
/// drop (also on panic).
///
/// Does NOT itself take [`lock_env`] — compose with [`lock_env`] or use the
/// `with_*` helpers below, which do. (Taking the lock per-guard would deadlock
/// the multi-guard helpers.)
pub struct ScopedEnvVar {
    key: String,
    previous: Option<std::ffi::OsString>,
}

impl ScopedEnvVar {
    /// Set `key=value` for the guard's lifetime.
    pub fn set(key: &str, value: &str) -> Self {
        let previous = std::env::var_os(key);
        // Blessed choke point: serialized by lock_env()/with_* callers and
        // restored on drop — the one place raw set_var is allowed.
        // (`env_mutation` is the Trust toolchain's deny-by-default env wall;
        // stock rustc doesn't know it, hence `unknown_lints`.)
        #[allow(unknown_lints, env_mutation)]
        std::env::set_var(key, value);
        Self {
            key: key.to_owned(),
            previous,
        }
    }

    /// Remove `key` for the guard's lifetime.
    pub fn unset(key: &str) -> Self {
        let previous = std::env::var_os(key);
        // Blessed choke point: serialized by lock_env()/with_* callers and
        // restored on drop — the one place raw remove_var is allowed.
        // (`env_mutation`: Trust-only deny-by-default env wall.)
        #[allow(unknown_lints, env_mutation)]
        std::env::remove_var(key);
        Self {
            key: key.to_owned(),
            previous,
        }
    }
}

impl Drop for ScopedEnvVar {
    fn drop(&mut self) {
        // Blessed choke point: restoring the captured pre-test state.
        // (`env_mutation`: Trust-only deny-by-default env wall.)
        #[allow(unknown_lints, env_mutation)]
        match &self.previous {
            Some(value) => std::env::set_var(&self.key, value),
            None => std::env::remove_var(&self.key),
        }
    }
}

/// Run `f` with `vars` set, serialized behind the process-wide env lock;
/// previous values are restored afterwards (also on panic).
pub fn with_serialized_env_vars<T>(vars: &[(&str, &str)], f: impl FnOnce() -> T) -> T {
    let _env_lock = lock_env();
    let _guards: Vec<_> = vars
        .iter()
        .map(|(key, value)| ScopedEnvVar::set(key, value))
        .collect();
    f()
}

/// Run `f` with `vars` removed from the environment, serialized behind the
/// process-wide env lock; previous values are restored afterwards.
pub fn with_serialized_env_vars_removed<T>(vars: &[&str], f: impl FnOnce() -> T) -> T {
    let _env_lock = lock_env();
    let _guards: Vec<_> = vars.iter().map(|key| ScopedEnvVar::unset(key)).collect();
    f()
}

/// Scoped editor for tests that walk a knob through several set/remove states
/// (e.g. probing an env parser's `"0"` / `"1"` / unset behavior).
///
/// Every key touched through the editor is captured once on first touch and
/// restored when the [`with_env_edits`] scope ends (also on panic).
pub struct EnvEditor {
    saved: Vec<(String, Option<std::ffi::OsString>)>,
}

impl EnvEditor {
    fn save_once(&mut self, key: &str) {
        if !self.saved.iter().any(|(k, _)| k == key) {
            self.saved.push((key.to_owned(), std::env::var_os(key)));
        }
    }

    /// Set `key=value` until the end of the [`with_env_edits`] scope or the
    /// next edit of `key`.
    pub fn set(&mut self, key: &str, value: &str) {
        self.save_once(key);
        // Blessed choke point: serialized by with_env_edits, restored on scope
        // exit. (`env_mutation`: Trust-only deny-by-default env wall.)
        #[allow(unknown_lints, env_mutation)]
        std::env::set_var(key, value);
    }

    /// Remove `key` until the end of the [`with_env_edits`] scope or the next
    /// edit of `key`.
    pub fn remove(&mut self, key: &str) {
        self.save_once(key);
        // Blessed choke point: serialized by with_env_edits, restored on scope
        // exit. (`env_mutation`: Trust-only deny-by-default env wall.)
        #[allow(unknown_lints, env_mutation)]
        std::env::remove_var(key);
    }
}

impl Drop for EnvEditor {
    fn drop(&mut self) {
        // Restore in reverse touch order (first-touched wins last).
        // Blessed choke point: restoring the captured pre-test state.
        // (`env_mutation`: Trust-only deny-by-default env wall.)
        #[allow(unknown_lints, env_mutation)]
        for (key, previous) in self.saved.drain(..).rev() {
            match previous {
                Some(value) => std::env::set_var(&key, value),
                None => std::env::remove_var(&key),
            }
        }
    }
}

/// Run `f` with exclusive, restore-on-exit access to the process environment
/// via an [`EnvEditor`].
pub fn with_env_edits<T>(f: impl FnOnce(&mut EnvEditor) -> T) -> T {
    let _env_lock = lock_env();
    let mut editor = EnvEditor { saved: Vec::new() };
    f(&mut editor)
    // editor drops (restores) before _env_lock releases.
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn scoped_set_and_unset_restore_previous_state() {
        let _lock = lock_env();
        let key = "AY_TEST_SUPPORT_ENV_SCOPED";
        assert!(std::env::var(key).is_err());
        {
            let _g = ScopedEnvVar::set(key, "a");
            assert_eq!(std::env::var(key).as_deref(), Ok("a"));
            {
                let _h = ScopedEnvVar::unset(key);
                assert!(std::env::var(key).is_err());
            }
            assert_eq!(std::env::var(key).as_deref(), Ok("a"));
        }
        assert!(std::env::var(key).is_err());
    }

    #[test]
    fn env_edits_restore_all_touched_keys() {
        let key = "AY_TEST_SUPPORT_ENV_EDITS";
        with_env_edits(|env| {
            env.set(key, "0");
            assert_eq!(std::env::var(key).as_deref(), Ok("0"));
            env.set(key, "1");
            assert_eq!(std::env::var(key).as_deref(), Ok("1"));
            env.remove(key);
            assert!(std::env::var(key).is_err());
        });
        assert!(std::env::var(key).is_err());
    }

    #[test]
    fn serialized_vars_visible_inside_scope_only() {
        let key = "AY_TEST_SUPPORT_ENV_SERIALIZED";
        with_serialized_env_vars(&[(key, "42")], || {
            assert_eq!(std::env::var(key).as_deref(), Ok("42"));
        });
        assert!(std::env::var(key).is_err());
        with_serialized_env_vars_removed(&[key], || {
            assert!(std::env::var(key).is_err());
        });
    }
}
