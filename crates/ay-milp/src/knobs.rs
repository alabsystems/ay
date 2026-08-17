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

mod types;

pub use types::{Bucket, EnvAudit, Knob, Route, Routed};

/// Knobs that read zero literal sites and are nevertheless **live**.
///
/// Without this table the derivation in `tests/env_ledger.rs` could not tell a
/// migrated knob from a dead one, and would have to accept any zero — which is
/// exactly the hole that let three genuinely unread names sit in the ledger
/// claiming a read site each.
pub const ROUTED: &[Routed] = &[
    // B38: the sixteen tune-routed env spellings (the five reduction/lane
    // settings and the twelve EngineEconomics ones minus plunge) are retired
    // with the env snapshot layer — knobs resolve caller > policy > compiled
    // default only, and the spellings live on as engine_cli flags.
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
    // The three hybrid-branching WEIGHTS. All three are read by one shared
    // closure that takes the name as a `&str` PARAMETER, so the literals exist
    // but no `env::var("...")` site does — a grep of the call sites sees the
    // closure, not the names. The arm itself (the hybrid-term knob) keeps its own
    // literal read and is therefore NOT routed.
    Routed {
        env: "AY_MILP_HYBRID_W",
        route: Route::Indirect {
            via: "bab::hybrid_weights' shared `read` closure",
        },
    },
    Routed {
        env: "AY_MILP_HYBRID_INF",
        route: Route::Indirect {
            via: "bab::hybrid_weights' shared `read` closure",
        },
    },
    Routed {
        env: "AY_MILP_HYBRID_CUT",
        route: Route::Indirect {
            via: "bab::hybrid_weights' shared `read` closure",
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
pub const ZERO_IGNORED: &[ZeroIgnored] = &[];

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
        env: "AY_ROOT_CLOSURE",
        flag: "ay-milp diag root-closure",
    },
    Deprecation {
        env: "AY_LP_ONLY",
        flag: "ay-milp diag lp-only",
    },
    // (B13: the AY_MILP_SEED_SOL entry left WITH its env read — the carriers
    // are `--seed-solution` on the bin and `SolveOpts::seed_solution_file`
    // in the library; a stale export surfaces via EnvAudit's unknown-name
    // warning.)
    Deprecation {
        env: "AY_MILP_THREADS",
        flag: "ay-milp solve --threads <n>",
    },
    // (B12: the AY_MILP_ITER_PROFILE entry is gone WITH its env read — the
    // carrier is `ay-milp solve --iter-profile`, and a stale export now
    // surfaces through `EnvAudit`'s unknown-name warning, which is the
    // stronger signal: a deprecation hint implies the name still does
    // something.)
    // (B40: the LP-stats deprecation entry is gone WITH its env read — the
    // carrier is the --lp-stats engine flag, and a stale export surfaces
    // through EnvAudit's unknown-name warning, the stronger signal.)
];

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
        if k == ay_sys::govern::ARMED_ENV || k == ay_sys::govern::ROOT_PID_ENV {
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

fn allow_unknown_env_is_set() -> bool {
    std::env::var_os(ALLOW_UNKNOWN_ENV).is_some()
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
        name: "AY_LP_ONLY",
        bucket: Bucket::Product,
        read_sites: 1,
    },
    // ALLOCATION CENSUS. Diagnostic-only and inert unless BOTH this is set and
    // the counting allocator is installed (the examples `alloc_census` /
    // `alloc_ub` install it). It exists because per-node allocation churn was
    // proposed as a throughput lever and REFUTED; the census is the instrument
    // that refuted it, kept so the refutation can be re-run rather than retold.
    // The FT-adoption ROW CEILING. Added because a gate audit found the ceiling had
    // NO override while its cold-root sibling has `AY_MILP_COLD_LU_MAX_ROWS`, so the
    // 106-of-379 instances above it could not be measured even in principle. Default
    // unchanged (`REFACTOR_TALL_ROWS`); this makes the gate reachable, not different.
    // AUTO-DETECTED margin reframe (`margin::auto_margin_row`). DEFAULT OFF, and
    // registered as an ARM rather than a kill switch for the same reason
    // `AY_MILP_CUT_FRAC_PENALTY` and the RINS dry-cap (now `--rins-drycap`) are: it was MEASURED
    // and it LOST, and the value of the name is that the negative stays
    // re-checkable. It makes the whole `margin` module reachable from an ordinary
    // `check()` — `mark_margin_row`'s only non-test callers require the CALLER to
    // name the row, so the reframe was dormant on every model that arrives as a
    // file, which is every ny W1 model. Measured over 46 W1 captures at 30s: the
    // reframed objective is a PRIMAL driver, so it lands both previously-open SAT
    // roots (8/10 -> 10/10) and loses FIVE UNSAT proofs (25/46 -> 22/46 decided,
    // 379 -> 41,867 nodes on the instances both arms decide). the downstream optimization consumer's W1 deliverable
    // is UNSAT. Unset is bit-identical to a build without it.
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
    // ATTRIBUTION DUMP. Diagnostic-only: per-phase wall, allocation regions and
    // rounding-kernel call/yield counts, dumped at solve end. This is the
    // instrument behind the attribution findings (the cut families that derive
    // ZERO cuts, and the sub-MIP share of node work) — kept so those numbers can
    // be re-derived rather than cited.
    // Opt-in for the provisional fill-rate trip (`Simplex::maybe_trip_bump_fill`).
    // Default OFF: the predicate is known biased -- see the function.
    // CHAIN AGGREGATION for the c-MIR family: aggregates a capacity row with the
    // variable-upper-bound rows of its chain partners before rounding (the qiu
    // fixed-charge shape, where every negative column has two chain partners).
    // Ships OFF. One live read; the four `ScopedEnvVar` sites in the tests are
    // setters, not reads, and the derivation counts reads.
    // The COLD-ROOT LU BAND (`FloatLp::cold_root_lu`): row window in which the
    // vertex-seeding cold root LP is handed to the Forrest-Tomlin engine instead
    // of the product-form eta file. Floor 3,000 / ceiling 8,192 are a measured
    // crossover, not a guess -- below the floor the FT engine costs 1.4-2.7x
    // wall for nothing and moved air05 off its proven bound; above the ceiling
    // `LuEngine::update`'s O(m) sweeps replace the refactorisation wall rather
    // than removing it. These two knobs move the window for the follow-up
    // experiment; `--no-cold-lu` is the A/B lever the band was measured
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
    // THE PERTURBATION-MATCHED CUT CONTROL (arm C of the three-arm cut measurement in
    // the development design notes §9(1)). Runs the shipped cut
    // loop unchanged and then REPLACES every row it installed with an information-free
    // row of the same shape: a non-negative combination of the model's own column
    // bounds, tight at the cut-free root vertex. It cuts off no point of the box, hence
    // none of the LP relaxation, hence none of any node's relaxation — so the arm
    // isolates what ROWS cost from what CUTS buy. See `bab::shadow_control_model`.
    // Warm-starts the root cut loop's re-optimisation from the previous round's optimal
    // basis instead of solving each round cold. Measured motivation (ITER LEDGER, 60
    // instances): the `root-cut` phase is 0.0% dual pivots and ~50/50 primal phase-I /
    // phase-II on EVERY instance -- the exact mixture of the cold root LP, which is what
    // "no warm start" looks like -- and one round costs a median 0.99x a full cold root
    // solve. DEFAULT OFF: the cut loop separates FROM the vertex the round's LP returns,
    // so a different (equally optimal) vertex changes which cuts exist and moves the whole
    // measured root trajectory. See `add_root_cuts`.
    // Restores the DENSE `m × m` `Bᵀ` assembly + `ExactLu` in the GMI separator,
    // the path `SparseExactLu` replaced. Both arms solve `Bᵀ u = e_i` EXACTLY, and
    // a non-singular basis has one solution, so the cuts are byte-identical; what
    // differs is ≈36·m² bytes of peak RSS. The row cap's whole re-derivation is an
    // A/B against this switch, so deleting it deletes the evidence.
    // The root dive's bounded chronological backtrack. DEFAULT 0 = INERT, and
    // the default IS the measurement: escaping the dive needs a way to
    // reconsider an EARLY pin, not a deeper stack of late ones. Kept
    // env-reachable so that negative stays re-checkable (see
    // `MAX_DIVE_BACKTRACKS` in bab.rs for the per-instance numbers).
    Knob {
        // B18: read deleted (measured slower on the seeds it was tried on;
        // the overflow pathology was pre-cap and produced no wrong answers).
        // The name stays as the record of the reversal — the prose in
        // simplex.rs still carries the numbers.
        name: "AY_MILP_DSE_PERSIST",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    // Widens DUAL FIXING (`dualfix.rs`) from objective-≡0 models to EVERY model. An ARM and
    // not tuning because what it trades is the ARTIFACT, not the speed: with a real objective
    // the verdict at stake is an OPTIMAL value whose dual-bound certificate the reduction
    // strips and no re-solve buys back. The rule itself is sound with an objective (the sign
    // test is implemented, sense-aware and tested); only the evidence economics differ.
    // An EXTERNAL dual bound delivered as a pure CUTOFF (no row, no LP touched).
    // The measurement instrument that separates a better bound's PRUNING POWER from
    // the vertex perturbation its row-shaped delivery causes. See `bab.rs`.
    // THREE-VALUED, not a boolean: `0` off, unset = ARMED (a cold solve of an LP
    // whose cold walk has already stalled), `1`/`all` = the blanket 2026-07-20
    // behaviour and the downstream optimization consumer's diff-net lever. See `simplex::eager_perturb_mode`.
    // Pins the Forrest–Tomlin spike build to one arm (`dense` = the exact
    // pre-sparsification path, `sparse` = always take the pattern-driven one),
    // overriding the density gate. Both arms leave BYTE-IDENTICAL engine state
    // (see `LuEngine::update_nz`), so this is a pure A/B on cost — which is
    // how the band measurements were taken, and how they can be re-derived.
    Knob {
        name: "AY_MILP_FUSED_RT",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    // Per-cut identity fingerprints for the GMI separator (`sepstat::gmi_cut`).
    // Separate from the `--trace` stream on purpose: the general trace's volume is
    // itself a cost, and it perturbs which A/B arm runs out of round budget first
    // — which is the confounder these lines exist to remove.
    // HYBRID BRANCHING SCORE. All four ship OFF: the campaign measured a WASH
    // (-0.4% nodes across the corpus) and the inference term specifically was a
    // REGRESSION. Registered as arm + weights so the wash stays re-checkable —
    // the unset path is instruction-identical (`CountDeps` vs `NoDeps`
    // monomorphise to the same arithmetic).
    Knob {
        name: "AY_MILP_HYBRID_CUT",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_HYBRID_INF",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_HYBRID_W",
        bucket: Bucket::Tuning,
        read_sites: 0,
    },
    // The implied-column-bound rescue inside `safe_bound` (`implied_open_corner`):
    // when the exact reduced-cost sign charges a column's OPEN side, read a corner
    // off the rows' own activity instead of forfeiting the node's whole bound.
    // OPT-IN and DEFAULT OFF: measured across 48 instances it closes ZERO of the 9
    // root declines (the rows' other columns are open too, and anything they DO
    // imply the exact presolve already installed) and costs 2.6x node throughput.
    // Kept, exact-admitted and tested, for the day a source of open columns the
    // presolve cannot see appears.
    // The per-PHASE iteration ledger. `AY_MILP_ITER_PROFILE` answers "what does one
    // pivot cost"; this one answers "which phase ran the pivots" -- root LP, root cut
    // re-optimisation, node, cold retry, node cut, strong branching, each heuristic,
    // in-solve recovery. Counts only (iterations and solves), so the line reproduces
    // exactly on a contended box.
    Knob {
        // B18: read + both disjuncts deleted (measured worse: 15356 vs 15408
        // on qnet1's root — a bigger pool buys fewer rounds and the rounds
        // were what was paying). The name stays as the record.
        name: "AY_MILP_KEEP_SLACK_CUTS",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    // Points the kernel-reformulation gate's corpus census at a directory of models, so its
    // real-world firing rate is a measurement rather than an assertion. Test-only: the census
    // self-skips when unset.
    // Per-row trace of the two knapsack-form complementation policies.
    Knob {
        name: "AY_MILP_MEAS",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    // Admits `separate_mir_agg` into EVERY root round rather than only the
    // stage-two round the plain family's dry-up buys — a gate qnet1 never
    // reaches. SHIPS OFF: qnet1's root bound falls 14,857.59 -> 14,805.06.
    // The knapsack-form complementation search (`BoundPolicy`). SHIPS OFF: it
    // separates nothing on 16 of the 17 corpus instances and displaces one cut
    // on `gen`. The arm is what keeps that negative re-checkable.
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
    // `with_max_nodes(0)`: default `BOUND 44`, and `with_bound_cover(false)`
    // and the no-root-floor knob both `UNKNOWN SolverIncomplete`, identically.
    // The floor now also reaches `tree_bound` directly (`root_floor_global`), so
    // the same three arms measure `BOUND 44`, `BOUND 44`, `UNKNOWN` — this knob
    // moves the cover channel alone. the no-tree-floor knob is the other half.
    Knob {
        name: "AY_MILP_NO_BOXPRUNE",
        bucket: Bucket::KillSwitch,
        read_sites: 0,
    },
    // The A/B arm for DECOUPLING the root reductions from tree-certificate
    // capture. The kernel reformulation and duplicate-column dedup were gated on
    // `opts.tree_cert_leaves == 0`, and that field defaults to 256 — so both were
    // OFF on default options, traded for an artifact `Outcome` can only carry on
    // its `Infeasible` variant. Set this and the two gates collapse back to
    // exactly `tree_cert_leaves == 0`, which also makes the harvest re-solve
    // unreachable (it requires `tree_cert_leaves > 0`), so one name restores the
    // whole prior path. See `bab::cert_decouple_enabled`.
    // Restores the historical `plain_cold` eta-file cold root byte-for-byte
    // (see `FloatLp::cold_root_lu`). The whole band's evidence is an A/B against
    // this switch; deleting it deletes the ability to re-derive the result.
    // Restores the SIZE-gated conflict levers on the objective-≡0 feasibility
    // class: nogood unit propagation and nogood-guided branching go back to
    // `tall_lu() || impl_class`, propagation-conflict learning back to `impl_on`,
    // and VSIDS branching back to default-off. Every model with a real objective
    // reads identically either way — the gate is a property of the objective.
    // See `feas_class` in `bab.rs`.
    // The A/B arm for the FILL-RATE TRIP (`Simplex::maybe_trip_bump_fill`), which
    // arms the Markowitz bump lane on MEASURED fill instead of on the
    // bump-lu-min column count. Set it and `bump_active` reduces to the
    // historical `peel_nb >= bump_lu_min()` expression byte-for-byte.
    // Restores the MIR-class self-gate's historical ALL-INTEGRAL predicate. The gate now
    // excludes only all-BINARY models (`cuts::mir_family_inert`): a general integer column
    // with a non-unit coefficient is precisely what MIR / strengthened-CG rounding is for,
    // and gating it off cost haprp its proof outright (300s BOUND 3666028.211734 at 640,876
    // nodes with no incumbent at all -> OPTIMAL 3673280.681685 in 63.2s at 357,624 nodes;
    // root closure 0% -> 96.2%). Setting it also removes the MIR class's per-round wall
    // budget, which exists only on the models this narrowing admits.
    // Kill switch for the knapsack-form complementation search; paired with
    // Restores the pre-fix reduced-cost caps, which would close an OPEN column
    // side at any finite value at all — measured up to 5.8e20 on a model whose
    // largest bound is 673.5, derived from an `rc` of 1.5e-15. Such a cap prunes
    // nothing and disables `safe_bound`'s open-column repair. The A/B arm.
    // Kill switch for the feasibility pump's per-call iteration CAP. Default off
    // (the cap is on): without it a single pump call can spend the whole
    // heuristic budget on one model.
    // Restores the historical unfloored root node, whose hole forfeited the whole
    // tree's dual bound on any interrupt at or near the root. Reporting only: the
    // floor is written to `Node::cover`, which the search never reads.
    // Restores the COLD re-solve of the root relaxation at the first tree node.
    // Default off: that node's LP IS the root LP, so it is handed the root
    // Candidate itself (as a `prepared` relaxation, box-rechecked at the
    // consumption boundary) instead of paying a second cold solve of it.
    // Restores the pre-fix behaviour where an interrupted no-incumbent tree
    // DISCARDED the rigorous global dual bound it had already computed and
    // reported `Unknown{Timeout}`. The A/B arm for that fix.
    // Restores the pre-fix global dual bound: a MIN over the open set and the
    // incumbent, with no floor by the root's own bound. The root floor is a
    // valid bound on the WHOLE tree, so the min could — and on 50v-10 did —
    // report a number 2335 units below one the solver had already proven.
    // Reporting only; `root_floor_global` is never read by the search.
    Knob {
        name: "AY_MILP_PC_PROBE_W",
        bucket: Bucket::Dead,
        read_sites: 0,
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
    // Multiplier on the feasibility pump's per-call iteration cap. Tuning knob
    // that exists so the cap can be A/B'd rather than argued about.
    // RELAXATION LIFTING. Ships OFF as an arm: lifts a separated row against the
    // relaxed (non-integral) support before it is offered to the pool.
    // How far past [floor, ceil] a fractional GENERAL integer's RENS window
    // reaches. DEFAULT 0 = byte-identical. It exists because the primal
    // opportunity table this front was built on turned out to be MISMEASURED —
    // the premise was FALSE — and the knob is what lets that be re-checked.
    Knob {
        name: "AY_MILP_SB_",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    Knob {
        name: "AY_MILP_SB_TIE",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
    // STRUCTURAL ELIMINATION (fixed columns, redundant rows). SHIPS OFF as an
    // ARM: the pass is correct and finds real structure, but it MEASURED
    // NEGATIVE on the corpus. The arm is what keeps that negative re-checkable
    // rather than merely recorded.
    // How far below the pseudocost pick's score a candidate may score and still
    // be reconsidered for its orbit. DEFAULT 0 (score ties only); `1` restores
    // the 2026-07-22 wide band. See `bab::symmetry_branch_band_setting`.
    Knob {
        name: "AY_MILP_THREADS",
        bucket: Bucket::Product,
        read_sites: 2,
    },
    // 72 -> 74: the GMI basis factorization's fill line (`cuts.rs`, `m`/basis nnz/
    // factor nnz/fill) and `sepstat::gmi_cut`'s per-cut identity fingerprint, which
    // rides on the general trace as well as its own switch.
    Knob {
        name: "AY_ROOT_CLOSURE",
        bucket: Bucket::Product,
        // 3 -> 2 (B71): `alloc_census` now takes `--root-closure` on its own
        // argv; `alloc_ub` and `mps_solve` still honour the deprecated env
        // alias (see DEPRECATED — superseded by `ay-milp diag root-closure`).
        read_sites: 2,
    },
    Knob {
        name: "AY_SEPSTAT",
        bucket: Bucket::Dead,
        read_sites: 0,
    },
];

#[cfg(test)]
mod tests;
