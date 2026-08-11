// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! THE ENV-VAR LEDGER: every `AY_*` name this crate reads, in one place.
//!
//! # Why an inventory before a deletion
//!
//! There are hundreds of `AY_*` switches in this crate, and the temptation is
//! to delete most of them. That would be a mistake, and the reason is in the
//! project journal: the negative results ("cut solves-per-node is already
//! spent", the byte-identical `AY_MILP_PROP_ARM` probe, the mas74 finite-tree
//! boundary) are only RE-CHECKABLE while their arms still exist. Losing the
//! ability to re-derive a negative result is how a project pays twice for the
//! same work. So the first move is an INVENTORY, not a purge:
//!
//! * it stops the count growing silently (a test asserts every `AY_*` string
//!   literal in `src/` and `examples/` appears in this table);
//! * it makes every knob discoverable (`ay-milp knobs --list`);
//! * and it powers the one CORRECTNESS fix in this whole area — see below.
//!
//! # The correctness fix: a typo must not be silent
//!
//! `AY_MILP_NO_CUTZ=1` is a no-op. A measurement campaign that sets it
//! silently measures the WRONG ARM and records a result that looks like a
//! finding. [`env_audit`] scans the process environment once for `AY_*` names
//! outside this table and reports them, so the CLI can warn loudly. This is a
//! correctness fix for the measurement record, not cosmetics.
//!
//! # Buckets
//!
//! * [`Bucket::Product`] — product surface: a real flag exists (or should).
//! * [`Bucket::KillSwitch`] — `AY_MILP_NO_*`, the emergency-off for a shipped
//!   optimisation and the A/B mechanism the journal rests on. NEVER delete.
//! * [`Bucket::Tuning`] — numeric measurement scaffolding (caps, budgets,
//!   shares, rounds).
//! * [`Bucket::Diagnostic`] — trace/profile/census output switches.
//! * [`Bucket::Arm`] — experiment arm selectors.
//! * [`Bucket::Dead`] — named in prose or a comment but never read. Several of
//!   these mentions are DELIBERATE HISTORICAL RECORD of a measured decision
//!   (`bab.rs`: "SCIP's (5/6)min+(1/6)max score (AY_MILP_PC_SCORE=minmax):
//!   mas76 +54%") and are worth more than the variables were. The sentence
//!   stays; only the variable is gone.

/// What a knob is for.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Bucket {
    /// Product surface: promote to a CLI flag / typed option.
    Product,
    /// `AY_MILP_NO_*` kill switch for a shipped default.
    KillSwitch,
    /// Numeric measurement scaffolding.
    Tuning,
    /// Trace / profile / census output.
    Diagnostic,
    /// Experiment arm selector.
    Arm,
    /// Mentioned in source but never read.
    Dead,
}

impl Bucket {
    /// The bucket's short name.
    #[must_use]
    pub fn name(self) -> &'static str {
        match self {
            Self::Product => "product",
            Self::KillSwitch => "kill-switch",
            Self::Tuning => "tuning",
            Self::Diagnostic => "diagnostic",
            Self::Arm => "arm",
            Self::Dead => "dead",
        }
    }
}

/// One environment knob.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Knob {
    /// The environment variable name.
    pub name: &'static str,
    /// What it is for.
    pub bucket: Bucket,
    /// Literal `env::var`/`env::var_os` call sites naming this knob, in `src/`
    /// and `examples/`.
    ///
    /// # This number is DERIVED, not declared
    ///
    /// It was hand-typed until `tests/env_ledger.rs::read_site_counts_are_derived`
    /// began deriving it, and by then **23 of 353 entries disagreed with the
    /// source**. That mattered because the number is quoted as evidence: a debt
    /// census written off this column reported "404 read sites" for a table whose
    /// column summed to 432 and whose true literal count was 423.
    ///
    /// The drift was not random, which is the interesting part. Twelve of the
    /// twenty-three are exactly the knobs `EngineEconomics` migrated to
    /// [`crate::tune`]: their literal reads were deleted and the ledger still
    /// claimed one apiece. Three more were read by **nothing at all** and are now
    /// [`Bucket::Dead`] — see [`ROUTED`] for the ones that legitimately read zero.
    ///
    /// A zero here means "no literal call site", which is *not* the same as dead:
    /// check [`ROUTED`] before concluding anything.
    pub read_sites: u32,
}

/// Why a live knob has **zero** literal `env::var` sites.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum Route {
    /// Resolved through [`crate::tune`]'s accessors, which hold the only copy of
    /// the name (`tune::Knob::env`). The call site names the typed knob, not the
    /// variable.
    Tune,
    /// Read through a named constant rather than a literal. A grep of the call
    /// sites cannot see these, which is the reason this table is hand-maintained
    /// and the derivation needs an exception list at all.
    Indirect {
        /// The constant that holds the name.
        via: &'static str,
    },
}

/// A live knob with no literal `env::var` site, and why.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Routed {
    /// The environment variable.
    pub env: &'static str,
    /// How it is reached instead.
    pub route: Route,
}

/// Knobs that read zero literal sites and are nevertheless **live**.
///
/// Without this table the derivation in `tests/env_ledger.rs` could not tell a
/// migrated knob from a dead one, and would have to accept any zero — which is
/// exactly the hole that let three genuinely unread names sit in the ledger
/// claiming a read site each.
pub const ROUTED: &[Routed] = &[
    // The five REDUCTION/lane settings, migrated to `EngineEconomics` for the
    // same reason as the twelve below but with higher stakes: three of them gate
    // transformations that change the model a verdict is proved against, and
    // `AY_MILP_NO_COLD_LU` was additionally a process-global `OnceLock` — the
    // first solve in a process latched the lane for every later one. A consumer
    // whose policy forbids exporting `AY_MILP_*` (ny) had no in-policy way to
    // reach any of them. `AY_MILP_NO_CERT_DECOUPLE` is deliberately NOT here: its
    // spelling is not plain presence (`0`/`off` keep the default), so it takes
    // the caller layer first and keeps its own literal env parse.
    Routed {
        env: "AY_MILP_NO_DUALFIX",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_NO_KERNEL_REFORM",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_NO_FEAS_CONFLICT",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_NO_COLD_LU",
        route: Route::Tune,
    },
    // The twelve `EngineEconomics` settings. Their literal reads were removed by
    // the M1 migration (the development design notes); the name now
    // lives once, in `tune::Knob::env`.
    Routed {
        env: "AY_MILP_DIVE_MAX_PINS",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_FLIP_CAP_SECS",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_FLIP_SHARE",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_NO_BLOOM_RELAX",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_NO_CUTS",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_NO_LATTICE",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_NO_SAT_STOP",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_PRESOLVE_SHARE",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_PUMP_RESTARTS",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_SAT_STOP_MULT",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_SAT_STOP_SECS",
        route: Route::Tune,
    },
    Routed {
        env: "AY_MILP_WARM_LU",
        route: Route::Tune,
    },
    // The documented indirect read: the one name a naive grep of the call sites
    // misses, and the original reason this ledger is hand-maintained.
    // Found by `read_site_counts_are_derived` on the very commit that added it:
    // the fatal-audit hatch is read through its own `ALLOW_UNKNOWN_ENV` const, so
    // it is invisible to a literal scan. The mechanism catching its own author is
    // the argument for having it.
    Routed {
        env: "AY_ALLOW_UNKNOWN_ENV",
        route: Route::Indirect {
            via: "knobs::ALLOW_UNKNOWN_ENV",
        },
    },
    Routed {
        env: "AY_MILP_NO_BOXPRUNE",
        route: Route::Indirect {
            via: "lattice::BOX_PRUNE_OFF_ENV",
        },
    },
];

/// A knob whose value `0` is silently discarded.
///
/// # The trap
///
/// The idiom is `env::var(K).ok().and_then(|v| v.parse().ok()).filter(|&n| n > 0)
/// .unwrap_or(DEFAULT)`. Setting `K=0` therefore does **not** mean zero — it
/// parses, fails the filter, and falls through to the compiled default, which is
/// the one value the operator was trying to move away from. `AY_MILP_NG_CAP=0`
/// reads as `NOGOOD_CAP_*`, and nothing says so.
///
/// This is `AY_MILP_NO_CUTZ` with a different mechanism. There the name is wrong
/// and the run measures the default arm; here the name is right, the *value* is
/// discarded, and the run measures the default arm. Both record a finding about a
/// configuration that never existed.
///
/// # Why an inventory rather than a fix
///
/// For several of these, zero genuinely has no meaning — "separate cuts every 0
/// nodes" is not a schedule — and clamping to the default is the right behaviour.
/// For others (`AY_MILP_COLD_LU_ROWS=0`, i.e. "no floor, always take the LU
/// lane"; `AY_MILP_NG_CAP=0`, i.e. "no no-good store") zero is exactly the
/// experiment an operator would try, and it silently does nothing.
///
/// Deciding which is which is a change per call site, each needing its own
/// measurement. What is cheap and immediate is to stop the set growing in
/// silence: `zero_ignored_sites_are_declared` in `tests/env_ledger.rs` fails on a
/// fifteenth undeclared one.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ZeroIgnored {
    /// The environment variable.
    pub env: &'static str,
    /// What an operator would reasonably expect `0` to mean, and does not get.
    pub zero_would_mean: &'static str,
}

/// Knobs where `=0` falls through to the compiled default.
///
/// Sorted, and exhaustive over `src/` — the test derives the set from the source
/// and requires exact agreement, so this cannot drift the way `read_sites` did.
pub const ZERO_IGNORED: &[ZeroIgnored] = &[
    ZeroIgnored {
        env: "AY_MILP_COLD_LU_ROWS",
        zero_would_mean: "no row floor: always take the LU lane",
    },
    ZeroIgnored {
        env: "AY_MILP_LB_CAP",
        zero_would_mean: "no local-branching store",
    },
    ZeroIgnored {
        env: "AY_MILP_LB_LEN",
        zero_would_mean: "admit no local-branching constraint",
    },
    ZeroIgnored {
        env: "AY_MILP_NG_CAP",
        zero_would_mean: "no no-good store",
    },
    ZeroIgnored {
        env: "AY_MILP_NG_LEN",
        zero_would_mean: "admit no no-good",
    },
    ZeroIgnored {
        env: "AY_MILP_NODE_CUT_BATCH",
        zero_would_mean: "add no cuts per node visit",
    },
    ZeroIgnored {
        env: "AY_MILP_NODE_CUT_EVERY",
        zero_would_mean: "(no meaning: a period of zero)",
    },
    ZeroIgnored {
        env: "AY_MILP_NODE_CUT_NNZ",
        zero_would_mean: "admit no node cut by density",
    },
    ZeroIgnored {
        env: "AY_MILP_NODE_GMI_BUDGET",
        zero_would_mean: "no node-GMI budget",
    },
    ZeroIgnored {
        env: "AY_MILP_NODE_GMI_EVERY",
        zero_would_mean: "(no meaning: a period of zero)",
    },
    ZeroIgnored {
        env: "AY_MILP_NODE_GMI_ROUNDS",
        zero_would_mean: "no node-GMI rounds",
    },
    ZeroIgnored {
        env: "AY_MILP_PC_CAP",
        zero_would_mean: "no pseudocost store",
    },
    ZeroIgnored {
        env: "AY_MILP_PC_LEN",
        zero_would_mean: "no pseudocost history",
    },
    ZeroIgnored {
        env: "AY_MILP_RINS_EVERY",
        zero_would_mean: "(no meaning: a period of zero)",
    },
];

/// A `Product`-bucket knob that a CLI flag now supersedes.
///
/// The env name KEEPS WORKING — deleting it in the same change that adds the
/// flag would break every measurement script in the journal, and a paper trail
/// that stops reproducing is a real loss. The CLI warns once per run instead.
#[derive(Debug, Clone, Copy)]
pub struct Deprecation {
    /// The environment variable.
    pub env: &'static str,
    /// The flag that replaces it.
    pub flag: &'static str,
}

/// Env names a CLI flag now supersedes. Aliases, not removals.
pub const DEPRECATED: &[Deprecation] = &[
    Deprecation {
        env: "AY_DUMP_SOL",
        flag: "ay-milp solve --emit-witness <path>",
    },
    Deprecation {
        env: "AY_CHECK_SOL",
        flag: "ay-milp diag cross-check --solution <path>",
    },
    Deprecation {
        env: "AY_ROOT_CLOSURE",
        flag: "ay-milp diag root-closure",
    },
    Deprecation {
        env: "AY_LP_ONLY",
        flag: "ay-milp diag lp-only",
    },
    Deprecation {
        env: "AY_MILP_MARGIN_ROW",
        flag: "ay-milp diag margin-row --row <last|i>",
    },
    Deprecation {
        env: "AY_MILP_SEED_SOL",
        flag: "ay-milp solve --seed-solution <path>",
    },
    Deprecation {
        env: "AY_MILP_TREE_CERT_LEAVES",
        flag: "ay-milp solve --tree-cert-leaves <n>",
    },
    Deprecation {
        env: "AY_MILP_THREADS",
        flag: "ay-milp solve --threads <n>",
    },
    Deprecation {
        env: "AY_MILP_ITER_PROFILE",
        flag: "ay-milp diag profile --iter",
    },
    Deprecation {
        env: "AY_MILP_LP_STATS",
        flag: "ay-milp diag profile --lp-stats",
    },
];

/// What a scan of the process environment found.
#[derive(Debug, Clone, Default)]
pub struct EnvAudit {
    /// `AY_*` names set in the environment and present in [`KNOBS`].
    pub known: Vec<(String, String)>,
    /// `AY_*` names set in the environment that NO read site consumes. A typo
    /// here silently measures the wrong arm — the single highest-value item in
    /// this whole area.
    pub unknown: Vec<String>,
    /// `AY_*` names set that are in the table but marked [`Bucket::Dead`] —
    /// also no-ops, for a different reason.
    pub dead: Vec<String>,
    /// Set names a CLI flag now supersedes, with the flag to use.
    pub deprecated: Vec<(String, &'static str)>,
}

/// Scan the process environment for `AY_*` names and classify them.
///
/// This reads the environment, so it is a CLI-startup operation, not something
/// a library call should do behind a caller's back.
#[must_use]
pub fn env_audit() -> EnvAudit {
    let mut out = EnvAudit::default();
    for (k, v) in std::env::vars() {
        if !k.starts_with("AY_") {
            continue;
        }
        // A SIBLING CRATE'S NAME THAT THIS PROCESS SETS ON ITSELF.
        //
        // `ay_sys::govern` arms the memory governor by re-execing with its
        // `ARMED_ENV` set, so the solve child inherits a name this crate's
        // ledger has never heard of. The audit then classified it `unknown` and
        // refused to run — "set but NO code reads it ... refusing to run under
        // an environment that does not mean what it says". The binary would not
        // run under its own governor. A real product failure: it takes out
        // `ay-milp solve --require full` whenever the governor arms, and it had
        // been sitting behind a red integration test in `tests/cert_io.rs`.
        //
        // Referenced through ay-sys's own constant rather than spelled out, for
        // two reasons. The exclusion cannot drift from its owner if the name
        // changes. And no `AY_*` LITERAL enters this crate's sources — which
        // matters, because `tests/env_ledger.rs` scans the source TEXT,
        // comments included, so writing the name here in prose would itself
        // trip `every_ay_env_name_in_source_is_in_the_ledger`. (It did, on the
        // first attempt.) The ledger stays exactly as strict as it was:
        // `the_ledger_does_not_invent_names` rightly forbids an entry for a name
        // this crate does not read, and this one genuinely belongs to ay-sys.
        if k == ay_sys::govern::ARMED_ENV {
            continue;
        }
        match KNOBS.iter().find(|kn| kn.name == k) {
            None => out.unknown.push(k),
            Some(kn) if kn.bucket == Bucket::Dead => out.dead.push(k),
            Some(_) => {
                if let Some(d) = DEPRECATED.iter().find(|d| d.env == k) {
                    out.deprecated.push((k.clone(), d.flag));
                }
                out.known.push((k, v));
            }
        }
    }
    out.known.sort();
    out.unknown.sort();
    out.dead.sort();
    out.deprecated.sort();
    out
}

/// The escape hatch for [`EnvAudit::is_fatal`]. Set it to run anyway.
pub const ALLOW_UNKNOWN_ENV: &str = "AY_ALLOW_UNKNOWN_ENV";

impl EnvAudit {
    /// Does this environment invalidate the run?
    ///
    /// # Why a warning was not enough
    ///
    /// `AY_MILP_NO_CUTZ=1` is a no-op, so a campaign that sets it measures the
    /// default arm and writes the result down as a finding. That is a correctness
    /// defect in the measurement record, and the response to it was a `WARNING`
    /// line on stderr — inside a harness that produces hundreds of lines per
    /// instance and is read by a script. A warning nobody reads is not a guard.
    ///
    /// Both classes are fatal and for the same reason: the operator asked for a
    /// configuration, and the run is not going to deliver it. An [`unknown`] name
    /// is usually a typo; a [`dead`] one is usually a recipe that outlived its
    /// knob (`AY_MILP_COND_TIGHTEN` is the worked example — documented in
    /// `presolve.rs` as *"kept as the explicit-on A/B arm"*, read by nothing).
    /// Neither run measures what it claims to.
    ///
    /// [`unknown`]: Self::unknown
    /// [`dead`]: Self::dead
    #[must_use]
    pub fn is_fatal(&self) -> bool {
        (!self.unknown.is_empty() || !self.dead.is_empty())
            && std::env::var_os(ALLOW_UNKNOWN_ENV).is_none()
    }
}

/// Every `AY_*` name that appears in this crate's sources.
///
/// Generated from the call sites and kept honest by `tests/env_ledger.rs`.
pub const KNOBS: &[Knob] = &[
    Knob {
        name: "AY_ALLOCSTAT",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    // The escape hatch for the fatal environment audit (`EnvAudit::is_fatal`).
    // Product surface: an operator who really does have an unrelated AY_* set
    // needs a documented way through, and a knob with no way through is a knob
    // people work around by deleting the check.
    Knob {
        name: "AY_ALLOW_UNKNOWN_ENV",
        bucket: Bucket::Product,
        read_sites: 0,
    },
    Knob {
        name: "AY_BASIS_FILE",
        bucket: Bucket::Product,
        read_sites: 3,
    },
    Knob {
        name: "AY_CHECK_SOL",
        bucket: Bucket::Product,
        read_sites: 2,
    },
    Knob {
        name: "AY_DIAG_COST_PERTURB",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_DIAG_PLAIN_COLD",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_DUMP_SOL",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_DUMP_VERTEX",
        bucket: Bucket::Product,
        read_sites: 2,
    },
    Knob {
        name: "AY_LP_ONLY",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ADOPT_FT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // The FT-adoption ROW CEILING. Added because a gate audit found the ceiling had
    // NO override while its cold-root sibling has `AY_MILP_COLD_LU_MAX_ROWS`, so the
    // 106-of-379 instances above it could not be measured even in principle. Default
    // unchanged (`REFACTOR_TALL_ROWS`); this makes the gate reachable, not different.
    Knob {
        name: "AY_MILP_ADOPT_FT_MAX_ROWS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ALLOCSTAT",
        bucket: Bucket::Diagnostic,
        read_sites: 2,
    },
    // AUTO-DETECTED margin reframe (`margin::auto_margin_row`). DEFAULT OFF, and
    // registered as an ARM rather than a kill switch for the same reason
    // `AY_MILP_CUT_FRAC_PENALTY` and `AY_MILP_RINS_DRYCAP` are: it was MEASURED
    // and it LOST, and the value of the name is that the negative stays
    // re-checkable. It makes the whole `margin` module reachable from an ordinary
    // `check()` — `mark_margin_row`'s only non-test callers require the CALLER to
    // name the row, so the reframe was dormant on every model that arrives as a
    // file, which is every ny W1 model. Measured over 46 W1 captures at 30s: the
    // reframed objective is a PRIMAL driver, so it lands both previously-open SAT
    // roots (8/10 -> 10/10) and loses FIVE UNSAT proofs (25/46 -> 22/46 decided,
    // 379 -> 41,867 nodes on the instances both arms decide). the downstream optimization consumer's W1 deliverable
    // is UNSAT. Unset is bit-identical to a build without it.
    Knob {
        name: "AY_MILP_AMO_MULTIWAY",
        bucket: Bucket::Arm,
        read_sites: 2,
    },
    // Milliseconds the ANCHOR (native proof-producing search) is given to beat a
    // DEFERRED lane verdict on the evidence axis before that verdict is
    // published as-is. See `claim::ANCHOR_FIRST_REFUSAL_CAP`.
    //
    // `0` DISABLES deferral entirely, which recovers the pre-portfolio routing
    // behaviour exactly: every lane that clears its own floor closes as before,
    // and a below-floor lane closes too. That degenerate point is what makes the
    // dominance invariant a property of ONE program with a parameter rather than
    // a claim about two programs, and `deferral_disabled_recovers_greedy_close`
    // asserts it.
    Knob {
        name: "AY_MILP_ANCHOR_FIRST_REFUSAL_MS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_AUTO_MARGIN",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BB_CACHE_AGE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BB_K",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BB_PAIR_ITERS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BB_REPROBE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BB_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BINARY_COMPLEMENT_SUB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BUMPDIFF_LANES",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BUMP_BTF",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BUMP_DIAG",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    // Opt-in for the provisional fill-rate trip (`Simplex::maybe_trip_bump_fill`).
    // Default OFF: the predicate is known biased -- see the function.
    Knob {
        name: "AY_MILP_BUMP_FILL_TRIP",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BUMP_LU_MIN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_BUMP_SCC",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CERT_GRACE",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CHAIN_DEVEX",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CHAIN_PREORDER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CHAIN_PROBE",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CHAIN_SHAPE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CHILD_ORDER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CHURN_BAND",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CLEAN_BUDGET",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CLIQUE_PER_ROUND",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CLIQUE_ROUNDS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_COEF_TIGHTEN_DEBUG",
        bucket: Bucket::Diagnostic,
        read_sites: 2,
    },
    // The COLD-ROOT LU BAND (`FloatLp::cold_root_lu`): row window in which the
    // vertex-seeding cold root LP is handed to the Forrest-Tomlin engine instead
    // of the product-form eta file. Floor 3,000 / ceiling 8,192 are a measured
    // crossover, not a guess -- below the floor the FT engine costs 1.4-2.7x
    // wall for nothing and moved air05 off its proven bound; above the ceiling
    // `LuEngine::update`'s O(m) sweeps replace the refactorisation wall rather
    // than removing it. These two knobs move the window for the follow-up
    // experiment; `AY_MILP_NO_COLD_LU` is the A/B lever the band was measured
    // against.
    // And the band's MEASURED companion: promote a solve that is already on the
    // eta file once it has paid for this many rebuilds, whatever its row count.
    // It exists because `m` does not predict FT cost (Spearman -0.045 against
    // ns/update/row over 39 models; spike density scores 0.841 but cannot be
    // observed from the eta lane at all), while the rebuild pressure the band
    // was actually buying down IS countable as it is paid. DEFAULT 0 = OFF.
    // Measurement arm: try the cold dual start on EVERY shape, not just `wide_tall`.
    // The square-ish corpus never ran it, and that is the corpus the headline LP
    // numbers were measured on -- see the call site in `simplex.rs`.
    Knob {
        name: "AY_MILP_COLD_DUAL_ALL",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_COLD_LU_ETA_REBUILDS",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_COLD_LU_MAX_ROWS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_COLD_LU_ROWS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_COND_TIGHTEN",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_COVER_EXT_ROUNDS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_COVER_MINIMAL",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CROSSOVER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CUTS_PER_ROUND",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CUT_EFF_FLOOR",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CUT_FRAC_PENALTY",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CUT_MAX_PARALLEL",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // THE PERTURBATION-MATCHED CUT CONTROL (arm C of the three-arm cut measurement in
    // the development design notes §9(1)). Runs the shipped cut
    // loop unchanged and then REPLACES every row it installed with an information-free
    // row of the same shape: a non-negative combination of the model's own column
    // bounds, tight at the cut-free root vertex. It cuts off no point of the box, hence
    // none of the LP relaxation, hence none of any node's relaxation — so the arm
    // isolates what ROWS cost from what CUTS buy. See `bab::shadow_control_model`.
    Knob {
        name: "AY_MILP_CUT_SHADOW",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CUT_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_CUT_TOPK",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // Warm-starts the root cut loop's re-optimisation from the previous round's optimal
    // basis instead of solving each round cold. Measured motivation (ITER LEDGER, 60
    // instances): the `root-cut` phase is 0.0% dual pivots and ~50/50 primal phase-I /
    // phase-II on EVERY instance -- the exact mixture of the cold root LP, which is what
    // "no warm start" looks like -- and one round costs a median 0.99x a full cold root
    // solve. DEFAULT OFF: the cut loop separates FROM the vertex the round's LP returns,
    // so a different (equally optimal) vertex changes which cuts exist and moves the whole
    // measured root trajectory. See `add_root_cuts`.
    Knob {
        name: "AY_MILP_CUT_WARM",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DEDUP_COLS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // Restores the DENSE `m × m` `Bᵀ` assembly + `ExactLu` in the GMI separator,
    // the path `SparseExactLu` replaced. Both arms solve `Bᵀ u = e_i` EXACTLY, and
    // a non-singular basis has one solution, so the cuts are byte-identical; what
    // differs is ≈36·m² bytes of peak RSS. The row cap's whole re-derivation is an
    // A/B against this switch, so deleting it deletes the evidence.
    Knob {
        name: "AY_MILP_DENSE_GMI_LU",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DEVEX",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DFS",
        bucket: Bucket::Tuning,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_DIAG",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DIVE_COMMIT_STOPPED",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DIVE_MAX_PINS",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_DIVE_PROBE_SECS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DRY_ARM",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DSE_PERSIST",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // Widens DUAL FIXING (`dualfix.rs`) from objective-≡0 models to EVERY model. An ARM and
    // not tuning because what it trades is the ARTIFACT, not the speed: with a real objective
    // the verdict at stake is an OPTIMAL value whose dual-bound certificate the reduction
    // strips and no re-solve buys back. The rule itself is sound with an objective (the sign
    // test is implemented, sense-aware and tested); only the evidence economics differ.
    Knob {
        name: "AY_MILP_DUALFIX_ALL",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DUAL_ANATOMY",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DUAL_BLOOM_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_DUAL_BYPASS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // An EXTERNAL dual bound delivered as a pure CUTOFF (no row, no LP touched).
    // The measurement instrument that separates a better bound's PRUNING POWER from
    // the vertex perturbation its row-shaped delivery causes. See `bab.rs`.
    Knob {
        name: "AY_MILP_DUAL_CUTOFF",
        bucket: Bucket::Arm,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_DUAL_PERTURB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // THREE-VALUED, not a boolean: `0` off, unset = ARMED (a cold solve of an LP
    // whose cold walk has already stalled), `1`/`all` = the blanket 2026-07-20
    // behaviour and the downstream optimization consumer's diff-net lever. See `simplex::eager_perturb_mode`.
    Knob {
        name: "AY_MILP_EAGER_PERTURB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ETA_AGE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ETA_CAP_MULT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ETA_GEN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FC",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FJ_POLISH_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FJ_SKIP_GAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FLIP_CAP_SECS",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_FLIP_NZ",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FLIP_PAIR_K",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FLIP_REACH",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FLIP_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_FLIP_STALL",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FLIP_WANDER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FLOWAGG_CUTS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FT_GROWTH_TOL",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // Pins the Forrest–Tomlin spike build to one arm (`dense` = the exact
    // pre-sparsification path, `sparse` = always take the pattern-driven one),
    // overriding the density gate. Both arms leave BYTE-IDENTICAL engine state
    // (see `LuEngine::update_nz`), so this is a pure A/B on cost — which is
    // how the band measurements were taken, and how they can be re-derived.
    Knob {
        name: "AY_MILP_FT_SPIKE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FULL_PRICING",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_FUSED_RT",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_FUSED_RT_DEFER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_GI_DFS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // Per-cut identity fingerprints for the GMI separator (`sepstat::gmi_cut`).
    // Separate from `AY_MILP_TRACE` on purpose: the general trace's volume is
    // itself a cost, and it perturbs which A/B arm runs out of round budget first
    // — which is the confounder these lines exist to remove.
    Knob {
        name: "AY_MILP_GMI_CUT_TRACE",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_GMI_MAX_ROWS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_GMI_ROUNDS",
        bucket: Bucket::Tuning,
        read_sites: 4,
    },
    Knob {
        name: "AY_MILP_GUB_BRANCH",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_GUB_CLIQUE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_GUB_MEAS_EVERY",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_GUB_SB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_GUB_SB_ITERS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_GUB_SB_K",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_HEUR_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_HYBRID_PB_LP",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_IMPL",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_IMPLIED_BOUND",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_IMPLIED_BOUND_DEBUG",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    // The implied-column-bound rescue inside `safe_bound` (`implied_open_corner`):
    // when the exact reduced-cost sign charges a column's OPEN side, read a corner
    // off the rows' own activity instead of forfeiting the node's whole bound.
    // OPT-IN and DEFAULT OFF: measured across 48 instances it closes ZERO of the 9
    // root declines (the rows' other columns are open too, and anything they DO
    // imply the exact presolve already installed) and costs 2.6x node throughput.
    // Kept, exact-admitted and tested, for the day a source of open columns the
    // presolve cannot see appears.
    Knob {
        name: "AY_MILP_IMPLIED_COL_BOUNDS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_IMPL_ARM",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_IMPL_CUT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_IMPL_TAB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // The per-PHASE iteration ledger. `AY_MILP_ITER_PROFILE` answers "what does one
    // pivot cost"; this one answers "which phase ran the pivots" -- root LP, root cut
    // re-optimisation, node, cold retry, node cut, strong branching, each heuristic,
    // in-solve recovery. Counts only (iterations and solves), so the line reproduces
    // exactly on a contended box.
    Knob {
        name: "AY_MILP_ITER_LEDGER",
        bucket: Bucket::Diagnostic,
        read_sites: 4,
    },
    Knob {
        name: "AY_MILP_ITER_PROFILE",
        bucket: Bucket::Diagnostic,
        read_sites: 3,
    },
    Knob {
        name: "AY_MILP_KEEP_SLACK_CUTS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // Points the kernel-reformulation gate's corpus census at a directory of models, so its
    // real-world firing rate is a measurement rather than an assertion. Test-only: the census
    // self-skips when unset.
    Knob {
        name: "AY_MILP_KERNEL_SCAN_DIR",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LATTICE_BKZ",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LATTICE_THREADS",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LB_ACT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LB_ARM",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LB_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LB_CONFLICT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LB_LEN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LB_STRICT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LIFTED_COVER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LNP",
        bucket: Bucket::Tuning,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_LNP_PROBE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LNP_PROBE_PRESOLVE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LNP_SECS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LP_STATS",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LU",
        bucket: Bucket::Tuning,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_LU_MAX_FILL_NNZ",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LU_REFACTOR",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_LU_VERIFY",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MARGIN_ROW",
        bucket: Bucket::Product,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_MAS74_PLUNGE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MAS74_ROWS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MAX_BASIS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MAX_CUT_DENSITY",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MAX_CUT_NNZ",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MAX_NODES",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MEAS",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_MIK_MIR_EXT_ROUNDS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MIN_VIOLATION",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MIR_EXT_CUTS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MIR_EXT_ROUNDS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MIXING",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MIX_DELTAS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MIX_RMAX",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MODK",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MODK_MAX",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MODK_SEEDS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MODK_TRI",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MS_BRANCH",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MS_DIVE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MS_DIVE_STEPS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MS_DIVE_THR",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MS_DIVE_TRACE",
        bucket: Bucket::Diagnostic,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_MS_WALK_MOVES",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_MS_WALK_SALT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NG_BOX",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NG_BRANCH",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NG_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NG_LEN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NG_ORDER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NG_SUB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NG_UP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUTS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_AGE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_BATCH",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_DEPTH",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_EAGER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_EPS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_EVERY",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_LOCAL",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_NNZ",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_SLOTS",
        bucket: Bucket::Tuning,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_NODE_CUT_STREAK",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_GMI",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_GMI_BUDGET",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_GMI_EVERY",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_GMI_MARGIN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_GMI_ONLY",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_GMI_ROUNDS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_PROP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NODE_RC",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NOKNAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_BLOOM_RELAX",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_NO_BOTTLENECK_EXT",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    // Read INDIRECTLY, through `lattice::BOX_PRUNE_OFF_ENV` rather than a
    // literal `env::var("AY_...")` — the one name in this table a naive grep of
    // the call sites misses, and the reason this ledger is hand-maintained
    // rather than generated at build time.
    // Restores the pre-fix dual-bound REPORT: an open node whose own bound
    // re-derivation declined forfeits the whole tree's global claim, instead of
    // falling back to the nearest ancestor bound that covers its box. Pure
    // reporting — `Node::cover` is never read by the search.
    //
    // IT NOW ISOLATES THE ANCESTOR-COVER CHANGE, AND IT USED NOT TO. `Node::cover`
    // was the root floor's ONLY route to the global claim, so switching the
    // `cover()` read off suppressed the floor with it — measured on 30n20b8 at
    // `AY_MILP_MAX_NODES=0`: default `BOUND 44`, and `AY_MILP_NO_BOUND_COVER=1`
    // and `AY_MILP_NO_ROOT_FLOOR=1` both `UNKNOWN SolverIncomplete`, identically.
    // The floor now also reaches `tree_bound` directly (`root_floor_global`), so
    // the same three arms measure `BOUND 44`, `BOUND 44`, `UNKNOWN` — this knob
    // moves the cover channel alone. `AY_MILP_NO_TREE_FLOOR` is the other half.
    Knob {
        name: "AY_MILP_NO_BOUND_COVER",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_BOXPRUNE",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_NO_BUMP_LU",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    // The A/B arm for DECOUPLING the root reductions from tree-certificate
    // capture. The kernel reformulation and duplicate-column dedup were gated on
    // `opts.tree_cert_leaves == 0`, and that field defaults to 256 — so both were
    // OFF on default options, traded for an artifact `Outcome` can only carry on
    // its `Infeasible` variant. Set this and the two gates collapse back to
    // exactly `tree_cert_leaves == 0`, which also makes the harvest re-solve
    // unreachable (it requires `tree_cert_leaves > 0`), so one name restores the
    // whole prior path. See `bab::cert_decouple_enabled`.
    Knob {
        name: "AY_MILP_NO_CERT_DECOUPLE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_CLIQUE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_COEF_TIGHTEN",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_COLD_DUAL",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    // Restores the historical `plain_cold` eta-file cold root byte-for-byte
    // (see `FloatLp::cold_root_lu`). The whole band's evidence is an A/B against
    // this switch; deleting it deletes the ability to re-derive the result.
    Knob {
        name: "AY_MILP_NO_COLD_LU",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_NO_COND_SCOUT",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_COND_TIGHTEN",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_COUNTSORT",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_COVER_EXT",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_CUTOFF",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_CUTS",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_NO_CUT_FMA",
        bucket: Bucket::KillSwitch,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_NO_DEVEX",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_DIVE_SKIP",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_DUALFIX",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_NO_DUAL_CHURN_BAND",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_DUAL_PERTURB",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_ETA_REUSE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    // Restores the SIZE-gated conflict levers on the objective-≡0 feasibility
    // class: nogood unit propagation and nogood-guided branching go back to
    // `tall_lu() || impl_class`, propagation-conflict learning back to `impl_on`,
    // and VSIDS branching back to default-off. Every model with a real objective
    // reads identically either way — the gate is a property of the objective.
    // See `feas_class` in `bab.rs`.
    Knob {
        name: "AY_MILP_NO_FEAS_CONFLICT",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    // The A/B arm for the FILL-RATE TRIP (`Simplex::maybe_trip_bump_fill`), which
    // arms the Markowitz bump lane on MEASURED fill instead of on the
    // `AY_MILP_BUMP_LU_MIN` column count. Set it and `bump_active` reduces to the
    // historical `peel_nb >= bump_lu_min()` expression byte-for-byte.
    Knob {
        name: "AY_MILP_NO_FILL_TRIP",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_FLIP_LNS",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_FLOAT",
        bucket: Bucket::KillSwitch,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_NO_FLOWCOVER",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_FLOWCOVER_AGG",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_FTRANNZ_FAST",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_FTRAN_FAST",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_FT_FAST",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_FUSED_RT",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_GI_EXT",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_KERNEL_REFORM",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_NO_LATTICE",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_NO_MARGIN_REFRAME",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    // Restores the MIR-class self-gate's historical ALL-INTEGRAL predicate. The gate now
    // excludes only all-BINARY models (`cuts::mir_family_inert`): a general integer column
    // with a non-unit coefficient is precisely what MIR / strengthened-CG rounding is for,
    // and gating it off cost haprp its proof outright (300s BOUND 3666028.211734 at 640,876
    // nodes with no incumbent at all -> OPTIMAL 3673280.681685 in 63.2s at 357,624 nodes;
    // root closure 0% -> 96.2%). Setting it also removes the MIR class's per-round wall
    // budget, which exists only on the models this narrowing admits.
    Knob {
        name: "AY_MILP_NO_MIR_GENINT",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_MIXING",
        bucket: Bucket::KillSwitch,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_NO_MS_WALK",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_NODE_CUTS",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_NODE_LU",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_NOENTER_UNSCALE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_ODD_CYCLE",
        bucket: Bucket::KillSwitch,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_NO_ODD_LIFT",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_ORBITOPE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_PARITY",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_PRESOLVE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_PRESOLVE_SCOUT",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_PROBE_LU_REUSE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    // Restores the pre-fix reduced-cost caps, which would close an OPEN column
    // side at any finite value at all — measured up to 5.8e20 on a model whose
    // largest bound is 673.5, derived from an `rc` of 1.5e-15. Such a cap prunes
    // nothing and disables `safe_bound`'s open-column repair. The A/B arm.
    Knob {
        name: "AY_MILP_NO_RC_CAP_GUARD",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_RINS_RESCUE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    // Restores the historical unfloored root node, whose hole forfeited the whole
    // tree's dual bound on any interrupt at or near the root. Reporting only: the
    // floor is written to `Node::cover`, which the search never reads.
    Knob {
        name: "AY_MILP_NO_ROOT_FLOOR",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_RT_BITS_KEY",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_RT_KIND",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_SAT_STOP",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_NO_SEP_SCREEN",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_SHAPE_CPR",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_SNAP",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_SPLNS",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_STRONGCG",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_STRUCTURE_ROUTE",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_SWEEP_PROVE",
        bucket: Bucket::KillSwitch,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_NO_SYM",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_TALL_LU",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    // Restores the pre-fix behaviour where an interrupted no-incumbent tree
    // DISCARDED the rigorous global dual bound it had already computed and
    // reported `Unknown{Timeout}`. The A/B arm for that fix.
    Knob {
        name: "AY_MILP_NO_TREE_BOUND_OUTCOME",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    // Restores the pre-fix global dual bound: a MIN over the open set and the
    // incumbent, with no floor by the root's own bound. The root floor is a
    // valid bound on the WHOLE tree, so the min could — and on 50v-10 did —
    // report a number 2335 units below one the solver had already proven.
    // Reporting only; `root_floor_global` is never read by the search.
    Knob {
        name: "AY_MILP_NO_TREE_FLOOR",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_TRI_CRASH",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_VUB",
        bucket: Bucket::KillSwitch,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_NO_WIDE_BLOOM",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_NO_ZERO_HALF",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_OBJECTIVE_SINGLETON_SUB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_OC_CUTS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_OC_SOURCES",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ODD_CYCLE",
        bucket: Bucket::Tuning,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_OPEN_BYTES",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ORACLE",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ORBITOPE_BRANCH",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ORBITOPE_BRANCH_DYN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ORBITOPE_DYN",
        bucket: Bucket::Tuning,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_ORBITOPE_ILV",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ORBITOPE_MIN_INT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ORBITOPE_ORDER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PARTIAL_PRICING",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PC_ACT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PC_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PC_EST",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PC_LEN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PC_PROBE_W",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_PC_RAW",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PC_SCORE",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_PC_ZERO_W_NODE",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_PERTURB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PLATEAU_DFS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PLUNGE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PLUNGE_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_POOL_PRICING",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PREFIX_COLS",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PREFIX_WORKERS",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PRESOLVE_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_PRINT_POINT",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PROP_ARM",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PROP_CONFLICT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PROP_FIRST",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PROP_QUEUE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PROP_SWEEPS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PUMP_BARREN_MULT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PUMP_FRAC_STALE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PUMP_RESTARTS",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_PUMP_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_PUMP_WORK_MULT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_RANGE_LOGICAL_CRASH",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_REFACTOR_EVERY",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_RENS_WIDEN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_RIM_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_RINS",
        bucket: Bucket::Tuning,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_RINS_DRYCAP",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_RINS_EVERY",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ROOT_CUTS_PER_ROUND",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ROOT_PROBE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ROOT_PROBE_ALL",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ROOT_PROBE_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ROOT_PROBE_CLIQUE_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ROOT_PROBE_NO_LP_RANK",
        bucket: Bucket::KillSwitch,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_ROOT_PROBE_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_RT_KIND_VERIFY",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_RT_MASKED",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SAT_STOP_MULT",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_SAT_STOP_SECS",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_SB_",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_SB_CANDS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SB_PROBE_ITERS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SB_REL",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SB_SUSTAIN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SB_TIE",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_SB_TOTAL",
        bucket: Bucket::Tuning,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_SCALE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SEED_SOL",
        bucket: Bucket::Product,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_SEPSTAT",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SEP_SCREEN_AUDIT",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SEP_SCREEN_EXPLAIN",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SETPART_BUDGET",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SETPART_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SHAPE_CENSUS",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SINGLETON_DIAG",
        bucket: Bucket::Diagnostic,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_SINGLETON_SUB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SMT",
        bucket: Bucket::Product,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_SMT_MIN_BUDGET",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SOLVE_DBG",
        bucket: Bucket::Diagnostic,
        read_sites: 2,
    },
    Knob {
        name: "AY_MILP_SPLNS_BUDGET",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_EXPOSED",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_NEARGAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_POLISH_BUDGET",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_POLISH_CAP",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_SHARE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_STALL",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_SUBGRAD",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_TARGET",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_TREE_RESERVE",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SPLNS_WANDER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_STAB_ORBIT",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_STEP_TRACE",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SUBMIP_BB",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SUBMIP_NODES",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SWEEP_DIAG",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SWEEP_DRAWS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SWEEP_NODES",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SWEEP_PINGEN",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SWEEP_PROVE_ARM",
        bucket: Bucket::Arm,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SWEEP_PROVE_FRAC",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SWEEP_SECS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SYM",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SYM_BRANCH",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    // How far below the pseudocost pick's score a candidate may score and still
    // be reconsidered for its orbit. DEFAULT 0 (score ties only); `1` restores
    // the 2026-07-22 wide band. See `bab::symmetry_branch_band_setting`.
    Knob {
        name: "AY_MILP_SYM_BRANCH_BAND",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_SYM_DEBUG",
        bucket: Bucket::Diagnostic,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_TABLEAU_MIR",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_TALL_LU_ROWS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_TAU_NZ",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_THREADS",
        bucket: Bucket::Product,
        read_sites: 2,
    },
    // 72 -> 74: the GMI basis factorization's fill line (`cuts.rs`, `m`/basis nnz/
    // factor nnz/fill) and `sepstat::gmi_cut`'s per-cut identity fingerprint, which
    // rides on the general trace as well as its own switch.
    Knob {
        name: "AY_MILP_TRACE",
        bucket: Bucket::Diagnostic,
        read_sites: 74,
    },
    Knob {
        name: "AY_MILP_TREE_CERT_LEAVES",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_TRI_CRASH",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_VERIFY_AFTER",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_VSIDS",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_MILP_WARM_LU",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_ZERO_HALF",
        bucket: Bucket::Tuning,
        read_sites: 1,
    },
    Knob {
        name: "AY_OBBT_COLS",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_OBBT_OUT",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_OBBT_ROUNDS",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_PIN_COL",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_ROOT_CLOSURE",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_ROOT_CLOSURE_PRESOLVE",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    Knob {
        name: "AY_SEPSTAT",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
];

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn table_has_no_duplicates_and_is_sorted() {
        for w in KNOBS.windows(2) {
            assert!(w[0].name < w[1].name, "KNOBS not sorted at {}", w[0].name);
        }
    }

    #[test]
    fn every_deprecation_names_a_known_knob() {
        for d in DEPRECATED {
            assert!(
                KNOBS.iter().any(|k| k.name == d.env),
                "{} is deprecated but not in the ledger",
                d.env
            );
        }
    }

    /// Dead means no reads. The converse is NOT true, and assuming it was is how
    /// three unread names kept a read site each in the table: the twelve knobs
    /// `EngineEconomics` migrated to `tune` also read zero literal sites, so the
    /// old `Dead == (read_sites == 0)` biconditional could not have held once M1
    /// landed. It is now an implication plus [`ROUTED`].
    #[test]
    fn dead_knobs_have_no_read_sites() {
        for k in KNOBS {
            if k.bucket == Bucket::Dead {
                assert_eq!(k.read_sites, 0, "{} is Dead but claims a read site", k.name);
            }
        }
    }

    /// Every zero is accounted for: a knob reads nothing because it is dead, or
    /// because it is reached another way and [`ROUTED`] says how. An unexplained
    /// zero is the `AY_MILP_COND_TIGHTEN` shape — a name documented as *"kept as
    /// the explicit-on A/B arm"* (`presolve.rs`) that no code reads, so a campaign
    /// setting it measures the default arm and records the result as a finding.
    #[test]
    fn every_zero_read_knob_is_dead_or_routed() {
        for k in KNOBS {
            if k.read_sites == 0 && k.bucket != Bucket::Dead {
                assert!(
                    ROUTED.iter().any(|r| r.env == k.name),
                    "{} has no literal read site, is not Dead, and is not in ROUTED — \
                     setting it does nothing and nothing says so",
                    k.name
                );
            }
        }
    }

    /// A routed knob must be live and in the table. A stale `ROUTED` entry would
    /// re-open the hole it exists to close.
    #[test]
    fn routed_names_are_live_ledger_entries() {
        for r in ROUTED {
            let k = KNOBS
                .iter()
                .find(|k| k.name == r.env)
                .unwrap_or_else(|| panic!("{} is ROUTED but not in the ledger", r.env));
            assert_ne!(k.bucket, Bucket::Dead, "{} is both ROUTED and Dead", r.env);
            assert_eq!(
                k.read_sites, 0,
                "{} is ROUTED but has literal read sites; drop the ROUTED entry",
                r.env
            );
        }
    }
}
