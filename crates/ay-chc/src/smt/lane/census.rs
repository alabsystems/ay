// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Rung-4 coverage census (`--chc-session-coverage`; #horn-smt-session §8
//! Rung 4).
//!
//! Every CHC-side SMT entry point opens a [`CensusFrame`]. Only the OUTERMOST
//! frame on a thread is recorded (an `IncrementalQueryContext` query that
//! falls back to a fresh `SmtContext::check_sat` is ONE query of kind
//! `incremental_query`); the router marks the live frame when it hands a query
//! to a session. The key is `(engine, entry, theory, context, outcome)`:
//!
//! * `engine` — the portfolio engine label of the thread
//!   ([`ScopedEngineLabel`], installed by `run_engine_guarded`), else the
//!   thread name;
//! * `theory` — `lra` (every conjunct passes the Rung-1 `Lra` eligibility),
//!   `lia` (every conjunct passes the `Lia` eligibility the session applies:
//!   Int vars, no `mod`/`div`), `liamod` (`Lia`-eligible only once `mod`/`div`
//!   are admitted), `other`;
//! * `context` — `pinned` (a `ScopedVerificationMode` is alive: a verifier,
//!   never routed by design), `search` / `verif` (the caller's `SmtContext`
//!   lane), `nolane` (an executor backend with no `SmtContext`);
//! * `outcome` — `decided` (the session answered Sat/Unsat), `unknown` (the
//!   session answered a budget Unknown), `fallthrough` (the session declined;
//!   the legacy bridge ran), `legacy` (never reached the router).
//!
//! Off by default; the classification scan only runs when the flag is on.

use std::cell::{Cell, RefCell};
use std::collections::BTreeMap;
use std::sync::{Mutex, OnceLock};

use ay_core::time::Instant;

use super::{verification_mode_active, SmtLane};
use crate::smt::session::convert_memo::{eligible, split_conjuncts, Rung};
use crate::smt::session::TheoryKind;
use crate::ChcExpr;

/// The SMT entry point a query came through.
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum SmtEntry {
    /// `SmtContext::check_sat` (and `check_sat_with_timeout`).
    CheckSat,
    /// `SmtContext::check_sat_with_executor_fallback(_timeout)`.
    ExecutorFallback,
    /// `SmtContext::check_sat_with_assumption_conjuncts`.
    AssumptionConjuncts,
    /// `IncrementalQueryContext::check_sat_incremental` / `check_sat_fresh_query`.
    IncrementalQuery,
    /// `PersistentExecutorSmtContext::check_query`.
    PersistentExecutor,
    /// `PdrExecutorBackend::check_sat*`.
    PdrExecutorBackend,
    /// `IncrementalPdrContext::check_sat_at_level_with_activations`.
    IncrementalPdr,
    /// `InterpolatingSmtContext::check_with_query`.
    Interpolating,
}

impl SmtEntry {
    fn name(self) -> &'static str {
        match self {
            Self::CheckSat => "check_sat",
            Self::ExecutorFallback => "executor_fallback",
            Self::AssumptionConjuncts => "assumption_conjuncts",
            Self::IncrementalQuery => "incremental_query",
            Self::PersistentExecutor => "persistent_executor",
            Self::PdrExecutorBackend => "pdr_executor_backend",
            Self::IncrementalPdr => "incremental_pdr",
            Self::Interpolating => "interpolating",
        }
    }
}

/// What the router did with a routed query (the outermost frame keeps the
/// strongest mark: decided > unknown > fallthrough).
#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub(crate) enum RouteMark {
    Legacy = 0,
    Fallthrough = 1,
    Unknown = 2,
    Decided = 3,
}

impl RouteMark {
    fn name(self) -> &'static str {
        match self {
            Self::Legacy => "legacy",
            Self::Fallthrough => "fallthrough",
            Self::Unknown => "unknown",
            Self::Decided => "decided",
        }
    }
}

thread_local! {
    static ROLE: Cell<&'static str> = const { Cell::new("-") };
    static ENGINE_LABEL: Cell<Option<&'static str>> = const { Cell::new(None) };
    static DEPTH: Cell<u32> = const { Cell::new(0) };
    static MARK: Cell<RouteMark> = const { Cell::new(RouteMark::Legacy) };
    static THREAD_NAME: RefCell<Option<String>> = const { RefCell::new(None) };
}

/// `--chc-session-coverage` (read once).
pub(crate) fn coverage_enabled() -> bool {
    ay_core::misc_cli_flags().chc_session_coverage
}

/// RAII: the portfolio engine label of this thread for the census.
#[must_use = "the label applies only while the guard is alive"]
pub(crate) struct ScopedEngineLabel {
    prev: Option<&'static str>,
    /// `false` while the census is off: no thread-local touched (the flag-off
    /// path does no per-call work for the census).
    active: bool,
}

impl ScopedEngineLabel {
    pub(crate) fn set(label: &'static str) -> Self {
        if !coverage_enabled() {
            return Self {
                prev: None,
                active: false,
            };
        }
        let prev = ENGINE_LABEL.with(|c| c.replace(Some(label)));
        Self { prev, active: true }
    }
}

impl Drop for ScopedEngineLabel {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        let prev = self.prev;
        ENGINE_LABEL.with(|c| c.set(prev));
    }
}

/// RAII: the census role of the SMT calls made while alive (`interp` for
/// interpolant computation internals — the Rung-3 consumers, whose legacy
/// cores/Farkas the session does not provide yet). Nests; restores on drop.
#[must_use = "the role applies only while the guard is alive"]
pub(crate) struct ScopedCensusRole {
    prev: &'static str,
    /// See [`ScopedEngineLabel::active`].
    active: bool,
}

impl ScopedCensusRole {
    pub(crate) fn set(role: &'static str) -> Self {
        if !coverage_enabled() {
            return Self {
                prev: "",
                active: false,
            };
        }
        let prev = ROLE.with(|c| c.replace(role));
        Self { prev, active: true }
    }
}

impl Drop for ScopedCensusRole {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        let prev = self.prev;
        ROLE.with(|c| c.set(prev));
    }
}

fn engine_label() -> String {
    if let Some(label) = ENGINE_LABEL.with(Cell::get) {
        return label.to_string();
    }
    THREAD_NAME.with(|n| {
        n.borrow_mut()
            .get_or_insert_with(|| {
                std::thread::current()
                    .name()
                    .map_or_else(|| "unnamed".to_string(), str::to_string)
            })
            .clone()
    })
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord)]
enum Theory {
    Lra,
    Lia,
    LiaMod,
    Other,
}

fn classify_theory(exprs: &[&ChcExpr]) -> Theory {
    let mut theory = Theory::Lra;
    for e in exprs {
        let Ok(conjuncts) = split_conjuncts(e) else {
            continue;
        };
        for c in &conjuncts {
            if theory == Theory::Lra && eligible(c, TheoryKind::Lra, Rung::Rung1).is_ok() {
                continue;
            }
            if theory != Theory::LiaMod && eligible(c, TheoryKind::Lia, Rung::Rung1).is_ok() {
                theory = Theory::Lia;
                continue;
            }
            if eligible(c, TheoryKind::Lia, Rung::Rung2).is_ok() {
                theory = Theory::LiaMod;
                continue;
            }
            return Theory::Other;
        }
    }
    theory
}

type Key = (
    String,
    &'static str,
    SmtEntry,
    Theory,
    &'static str,
    RouteMark,
);

#[derive(Default, Clone, Copy)]
struct Cell2 {
    n: u64,
    us: u64,
}

fn table() -> &'static Mutex<BTreeMap<Key, Cell2>> {
    static TABLE: OnceLock<Mutex<BTreeMap<Key, Cell2>>> = OnceLock::new();
    TABLE.get_or_init(|| Mutex::new(BTreeMap::new()))
}

struct Outer {
    role: &'static str,
    entry: SmtEntry,
    theory: Theory,
    context: &'static str,
    start: Instant,
}

/// One SMT entry-point frame; see the module docs. Inert when the census is
/// off.
#[must_use = "the frame records on drop"]
pub(crate) struct CensusFrame {
    active: bool,
    outer: Option<Outer>,
}

impl CensusFrame {
    /// Open a frame for a query over the conjunction of `exprs`. `lane` is the
    /// caller context's lane (`None` for executor backends).
    pub(crate) fn enter(entry: SmtEntry, lane: Option<SmtLane>, exprs: &[&ChcExpr]) -> Self {
        if !coverage_enabled() {
            return Self {
                active: false,
                outer: None,
            };
        }
        let depth = DEPTH.with(|d| {
            let v = d.get();
            d.set(v + 1);
            v
        });
        if depth > 0 {
            return Self {
                active: true,
                outer: None,
            };
        }
        MARK.with(|m| m.set(RouteMark::Legacy));
        let context = if verification_mode_active() {
            "pinned"
        } else {
            match lane {
                Some(SmtLane::Search) => "search",
                Some(_) => "verif",
                None => "nolane",
            }
        };
        Self {
            active: true,
            outer: Some(Outer {
                role: ROLE.with(Cell::get),
                entry,
                theory: classify_theory(exprs),
                context,
                start: Instant::now(),
            }),
        }
    }

    /// `enter` over one expression.
    pub(crate) fn enter1(entry: SmtEntry, lane: Option<SmtLane>, expr: &ChcExpr) -> Self {
        Self::enter(entry, lane, &[expr])
    }
}

impl Drop for CensusFrame {
    fn drop(&mut self) {
        if !self.active {
            return;
        }
        DEPTH.with(|d| d.set(d.get().saturating_sub(1)));
        let Some(outer) = self.outer.take() else {
            return;
        };
        let mark = MARK.with(|m| m.replace(RouteMark::Legacy));
        let us = u64::try_from(outer.start.elapsed().as_micros()).unwrap_or(u64::MAX);
        let key = (
            engine_label(),
            outer.role,
            outer.entry,
            outer.theory,
            outer.context,
            mark,
        );
        if let Ok(mut t) = table().lock() {
            let cell = t.entry(key).or_default();
            cell.n += 1;
            cell.us = cell.us.saturating_add(us);
        }
    }
}

/// Router hook: the live outermost frame reached the session with `mark`.
pub(crate) fn note_route(mark: RouteMark) {
    if !coverage_enabled() {
        return;
    }
    MARK.with(|m| {
        if mark > m.get() {
            m.set(mark);
        }
    });
}

/// One `[CHC-SESSION-COVERAGE]` line per recorded key (empty when off).
pub(crate) fn coverage_report() -> Vec<String> {
    if !coverage_enabled() {
        return Vec::new();
    }
    let Ok(t) = table().lock() else {
        return Vec::new();
    };
    t.iter()
        .map(|((engine, role, entry, theory, context, mark), c)| {
            let theory = match theory {
                Theory::Lra => "lra",
                Theory::Lia => "lia",
                Theory::LiaMod => "liamod",
                Theory::Other => "other",
            };
            format!(
                "[CHC-SESSION-COVERAGE] engine={engine} role={role} entry={} theory={theory} ctx={context} outcome={} n={} ms={}",
                entry.name(),
                mark.name(),
                c.n,
                c.us / 1000
            )
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ChcSort;
    use crate::ChcVar;

    #[test]
    fn classify_theory_splits_lra_lia_other() {
        let x = ChcExpr::var(ChcVar::new("x", ChcSort::Real));
        let i = ChcExpr::var(ChcVar::new("i", ChcSort::Int));
        let lra = ChcExpr::ge(x.clone(), ChcExpr::Real(1, 1));
        let lia = ChcExpr::ge(i.clone(), ChcExpr::int(1));
        assert_eq!(classify_theory(&[&lra]), Theory::Lra);
        assert_eq!(classify_theory(&[&lra, &lia]), Theory::Lia);
        let nonlinear = ChcExpr::ge(ChcExpr::mul(i.clone(), i), ChcExpr::int(1));
        assert_eq!(classify_theory(&[&lra, &nonlinear]), Theory::Other);
    }
}
