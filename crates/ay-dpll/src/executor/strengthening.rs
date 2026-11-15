// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Satisfiability-preserving strengthenings (Σ), and the per-executor switch
//! that keeps them out of every re-solve used as evidence.
//!
//! A strengthening adds a fact the input does not entail but that keeps at
//! least one model of every satisfiable input — symmetry breaking is the
//! textbook case. Such a fact has no implication proof, so it reaches a
//! refutation as an anonymous `trust` step. On 2026-10-02 that was the whole
//! story of a wrong `unsat`: LNH symmetry breaking excluded every model of a
//! satisfiable QF_UF problem, its fact became the refutation's one hole, and
//! the re-solve that admitted the hole as `discharged-trust` ran the same pass
//! and re-derived the same wrong answer (`~/ay-bench/dtrust/POLICY.md` §0, §9).
//!
//! The evidence-policy decision of that day (P1) is that every re-solve used to
//! check or corroborate a verdict runs with every strengthening OFF. The CLI
//! switches are process-global (`ay_core::theory_disable_flags`), so a derived
//! executor could not be told to run without one; [`StrengtheningPolicy`] is the
//! executor-local half. A strengthening runs only when its global switch is on
//! AND the executor permits it ([`Executor::strengthening_permitted`]).
//!
//! # What is (and is not) on the list
//!
//! Audited on main `a68e18a38f` by reading every pass that pushes into
//! `ctx.assertions` before solving and grepping the solver for symmetry,
//! lex-leader, cardinality and finite-model-finding passes:
//!
//! * **LNH symmetry breaking** (`lnh_symmetry.rs`, both the least-index prefix
//!   and the signature lex-leader schemes): a strengthening. The only one on
//!   the SMT path.
//! * The int finite-domain pigeonhole (`pigeonhole_core/int_domain.rs`) is a
//!   refutation, not an added fact: it returns a core only after re-deriving
//!   every clique edge and domain from the core assertions alone. Its colouring
//!   twin only proposes models, which the model gates check.
//! * The enum finite-domain SAT lane (`enum_sat.rs`) is a definitional one-hot
//!   encoding; every clause it adds holds in the intended extension of every
//!   model. It breaks no symmetry.
//! * The purification passes and enum/RoundingMode domain coverage add
//!   definitions and valid facts. A BUG in one of them can strengthen (the
//!   critic's §9.3 item 5), but that is not something a switch fixes.
//! * `ay-sat`'s symmetry switches apply to DIMACS input only.
//!
//! A new strengthening gets a [`Strengthening`] variant and is gated on
//! [`Executor::strengthening_permitted`]; the derived-executor test then covers
//! it with no further work.

use std::cell::Cell;

use super::Executor;

thread_local! {
    /// How many checking solves (executors with [`StrengtheningPolicy::ForcedOff`])
    /// are on this thread's stack.
    ///
    /// A checking re-solve spawns nested probes of its own — ground probes,
    /// isolated certification probes, sub-queries — each a fresh executor
    /// whose policy defaults to `Permitted`. Without this scope those probes
    /// would run a strengthening inside the very re-solve that must run none,
    /// and a probe's verdict reaches the re-solve's answer. Nested solves run
    /// on the caller's thread (the only solver thread is the BV encoder's,
    /// which runs no strengthening), so the dynamic extent of the checking
    /// solve's `check_sat` is the whole of it.
    static CHECKING_SOLVE_DEPTH: Cell<u32> = const { Cell::new(0) };

    /// Test-only stand-in for the process-global (CLI) switches, so a unit
    /// test can show the per-executor gate holding while a strengthening is
    /// globally ON whatever the CLI default is (LNH was off in every posture
    /// from 2026-10-02 until its domain fix landed), so a test of the gate
    /// never passes vacuously.
    #[cfg(test)]
    static GLOBAL_SWITCH_OVERRIDE: Cell<Option<bool>> = const { Cell::new(None) };
}

/// RAII marker that a checking solve is running on this thread; while one is,
/// no executor on the thread may run a strengthening
/// ([`Executor::enter_checking_solve_scope`]).
#[must_use = "the scope ends when the marker is dropped"]
pub(in crate::executor) struct CheckingSolveScope {
    _private: (),
}

impl Drop for CheckingSolveScope {
    fn drop(&mut self) {
        CHECKING_SOLVE_DEPTH.with(|depth| depth.set(depth.get().saturating_sub(1)));
    }
}

fn inside_checking_solve() -> bool {
    CHECKING_SOLVE_DEPTH.with(Cell::get) > 0
}

/// One satisfiability-preserving strengthening technique.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Strengthening {
    /// LNH symmetry breaking for finite-model QF_UF (`lnh_symmetry.rs`), in
    /// either of its two schemes.
    LnhSymmetry,
}

impl Strengthening {
    /// Every strengthening, in tag order.
    pub const ALL: [Self; 1] = [Self::LnhSymmetry];

    /// Stable census tag, kebab-case.
    #[must_use]
    pub const fn tag(self) -> &'static str {
        match self {
            Self::LnhSymmetry => "lnh-symmetry",
        }
    }

    const fn bit(self) -> u8 {
        match self {
            Self::LnhSymmetry => 1,
        }
    }

    /// The process-global (CLI) half of the gate.
    fn globally_enabled(self) -> bool {
        #[cfg(test)]
        if let Some(enabled) = GLOBAL_SWITCH_OVERRIDE.with(Cell::get) {
            return enabled;
        }
        match self {
            Self::LnhSymmetry => super::lnh_symmetry::lnh_enabled(),
        }
    }
}

/// A set of [`Strengthening`]s.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct StrengtheningSet(u8);

impl StrengtheningSet {
    /// The empty set.
    pub const EMPTY: Self = Self(0);

    /// Whether the set names no strengthening.
    #[must_use]
    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }

    /// Whether `strengthening` is in the set.
    #[must_use]
    pub const fn contains(self, strengthening: Strengthening) -> bool {
        self.0 & strengthening.bit() != 0
    }

    /// The set with `strengthening` added.
    #[must_use]
    pub const fn with(self, strengthening: Strengthening) -> Self {
        Self(self.0 | strengthening.bit())
    }

    /// The members, comma-separated by tag, or `none` — the literal spelling
    /// the certificate line prints, so a reader can see a re-solve that
    /// disabled nothing.
    #[must_use]
    pub fn tags(self) -> String {
        let tags: Vec<&str> = Strengthening::ALL
            .iter()
            .filter(|strengthening| self.contains(**strengthening))
            .map(|strengthening| strengthening.tag())
            .collect();
        if tags.is_empty() {
            "none".to_string()
        } else {
            tags.join(",")
        }
    }
}

/// Whether an executor may run strengthenings at all.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub(crate) enum StrengtheningPolicy {
    /// The CLI switches decide. Every public solve starts here.
    #[default]
    Permitted,
    /// None runs, whatever the CLI says: a re-solve used as evidence.
    ForcedOff,
}

impl Executor {
    /// Whether `strengthening` may run in this executor's solve: its global
    /// switch is on, this executor is not a checking re-solve, and no checking
    /// re-solve is running further up this thread's stack (a nested probe of
    /// one runs without, too).
    pub(in crate::executor) fn strengthening_permitted(
        &self,
        strengthening: Strengthening,
    ) -> bool {
        self.strengthening_policy == StrengtheningPolicy::Permitted
            && !inside_checking_solve()
            && strengthening.globally_enabled()
    }

    /// Whether this solve is, or runs inside, a re-solve used as evidence:
    /// this executor is one, or a checking solve is running further up this
    /// thread's stack. Search state another solve handed over
    /// (`ground_solve_carry`) stays out of such a solve.
    pub(in crate::executor) fn in_evidence_solve(&self) -> bool {
        self.strengthening_policy == StrengtheningPolicy::ForcedOff || inside_checking_solve()
    }

    /// Mark this thread as inside a checking solve for the marker's lifetime,
    /// when this executor is one; `None` (nothing marked) otherwise. Held
    /// across `check_sat` / `check_sat_assuming`, so every executor the solve
    /// creates — however it is built — inherits the forced-off policy.
    pub(in crate::executor) fn enter_checking_solve_scope(&self) -> Option<CheckingSolveScope> {
        (self.strengthening_policy == StrengtheningPolicy::ForcedOff).then(|| {
            CHECKING_SOLVE_DEPTH.with(|depth| depth.set(depth.get().saturating_add(1)));
            CheckingSolveScope { _private: () }
        })
    }

    /// Turn every strengthening off for this executor's solves.
    pub(crate) fn force_strengthenings_off(&mut self) {
        self.strengthening_policy = StrengtheningPolicy::ForcedOff;
    }

    /// Record that `strengthening` added at least one fact to this query.
    pub(in crate::executor) fn record_strengthening_applied(
        &mut self,
        strengthening: Strengthening,
    ) {
        self.strengthenings_applied = self.strengthenings_applied.with(strengthening);
    }

    /// The strengthenings that added a fact during the current public query.
    #[must_use]
    pub fn strengthenings_applied(&self) -> StrengtheningSet {
        self.strengthenings_applied
    }
}

/// Test-only: set (`Some`) or clear (`None`) the stand-in for every
/// strengthening's process-global switch on this thread.
#[cfg(test)]
pub(in crate::executor) fn override_global_switches_for_test(enabled: Option<bool>) {
    GLOBAL_SWITCH_OVERRIDE.with(|cell| cell.set(enabled));
}

#[cfg(test)]
#[path = "strengthening_tests.rs"]
pub(in crate::executor) mod tests;
