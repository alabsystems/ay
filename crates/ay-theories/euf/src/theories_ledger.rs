// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE ay-theories ENV LEDGER — P6 rollout, first crate group.
//!
//! # Why ay-theories is first, and not ay-dpll
//!
//! ay-dpll has 134 names to ay-theories' 47, and the rollout still starts here.
//! **All four instances of the size-gate antipattern were found in ay-theories**
//! (the development design notes), one of them
//! costing a *correct answer* rather than time. Order by where the defects are, not
//! by where the names are.
//!
//! It also holds a duplication the antipattern doc flags directly:
//! `PHASE_EPOCH_MIN_ATOMS = 8192` is declared TWICE with no shared definition, once
//! here in `lia` and once in `ay-dpll`'s combiner. Both are instrumented separately
//! in `ay_core::forgone` so the census keeps them apart — if the two copies ever
//! diverge, the report says so before a reader has to notice.
//!
//! # What this buys, stated exactly
//!
//! The same three things `ay-milp`'s ledger buys, and no more:
//!
//! * a name added at a fresh `env::var` site fails a test rather than appearing
//!   silently;
//! * the unknown-name audit becomes trustworthy for these crates, because it is
//!   only as good as the ledger is exhaustive;
//! * `read_sites` is DERIVED here from the first commit — `ay-milp` learned that the
//!   hand-typed version was wrong on 23 of 353 entries and was still being quoted as
//!   evidence.
//!
//! It does NOT give these knobs a typed surface, a soundness class, or a per-solve
//! carrier. That is the `ay-param` migration, and it is ordered after this.

/// What a knob is for. Mirrors `ay_milp::Bucket` deliberately: two vocabularies for
/// the same concept is how a kill switch and its typed setter come to disagree.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bucket {
    /// `*_NO_*` / `*_OFF`: the A/B arm for a shipped default. NEVER delete.
    KillSwitch,
    /// Numeric measurement scaffolding: caps, budgets, thresholds, rounds.
    Tuning,
    /// Trace / stats / census output. No behaviour.
    Diagnostic,
    /// Experiment arm selector.
    Arm,
    /// Named in source but never read.
    Dead,
}

/// One environment knob in the ay-theories crate group.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Knob {
    /// The environment variable name.
    pub name: &'static str,
    /// Which theory crate(s) read it. A name read by two theories is a coupling
    /// worth seeing: `PHASE_EPOCH_MIN_ATOMS` is the reason this column exists.
    pub crate_name: &'static str,
    /// What it is for.
    pub bucket: Bucket,
    /// Literal `env::var`/`env::var_os` call sites. DERIVED, never hand-typed —
    /// see the module note.
    pub read_sites: u32,
}

/// Every `AY_*` name the ay-theories crates read.
pub const KNOBS: &[Knob] = &[
    Knob {
        name: "AY_BENCH_LOOP_B_ITERS",
        crate_name: "lia",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_BENCH_LOOP_B_PERF_GATE",
        crate_name: "lia",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_LIA_HOT_LOOP_ITERS",
        crate_name: "lia",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        // Opt-in guard for the NRA measurement-harness tests (the gate
        // forbids disabled tests; AY_LIA_HOT_LOOP_ITERS class).
        name: "AY_NRA_PROFILE",
        crate_name: "nra",
        bucket: Bucket::Diagnostic,
        read_sites: 27,
    },
];
