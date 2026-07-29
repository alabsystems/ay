// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Self-tuning: the engine reads the model and picks its own settings.
//!
//! # Why this exists
//!
//! ay-milp grew ~300 tuning decisions read straight from `std::env::var` at
//! scattered call sites. Every one of those is a setting a *user* would
//! otherwise have to discover, and a solver that needs its user to know 300
//! environment variables is not competitive with one that reads the model and
//! decides. This module is where that decision moves into the engine.
//!
//! # The shape of the problem
//!
//! The 2026-07 campaign measured single-component moves toward Gurobi's design
//! and found every one of them a regression *in ay*: a Gurobi-sized root cut
//! pool cost 7 verdicts, root probing 3, devex pricing was 3.4x worse, and
//! structural LP presolve took qnet1 from 4.18s to 15.75s (nodes 372 -> 2209).
//! The conclusion recorded in the development design notes is
//! that ay sits at a *different local optimum* — exact-first, unreduced model,
//! small cut pool — and that moving one component toward Gurobi's design leaves
//! ay's optimum without arriving at Gurobi's.
//!
//! That result is what makes this module the right next move rather than
//! another transplant. Each of those settings *helped* on some instances and
//! hurt on more; a single global default is forced to pick one side of that
//! trade for every model it will ever see. Selection is not a new component to
//! transplant — it is the freedom to stop choosing globally.
//!
//! # Precedent in this crate
//!
//! The approach is already proven here, ad hoc. `bab.rs` decides GMI rounds
//! from `num_cols() + num_rows() <= 64` (`TINY_GMI_COLS_PLUS_ROWS`), and gates
//! extensions behind `wants_gi_extension` / `wants_bottleneck_extension`, each
//! with measurements quoted in its comment. Those work. What they lack is a
//! home: they are invisible to each other, cannot be measured as a policy, and
//! cannot be turned off as a unit. This module is that home.
//!
//! # Safety: this ships as a no-op
//!
//! [`Policy::select`] returns [`Profile::EMPTY`] — no opinion about anything.
//! Every accessor therefore falls through to exactly the environment-variable
//! read and compiled default that the call site used before, so migrating a
//! call site is *behaviour-preserving by construction* and merging this module
//! changes no verdict and no timing. [`tests::empty_policy_is_a_no_op`] pins
//! that. Policy rules land one at a time, each behind its own corpus
//! measurement, and each is revertible on its own.
//!
//! An explicitly set environment variable **outranks** a selected value, and a
//! setting carried on the caller's [`crate::SolveOpts`] outranks both:
//!
//! ```text
//! caller (SolveOpts)  >  explicit valid environment value  >  policy  >  compiled default
//! ```
//!
//! Every existing A/B recipe, kill switch and reproduction script keeps working
//! unchanged, and a measurement can always pin a setting against the policy.
//! The environment-over-policy half of that ordering is not negotiable: without
//! it, the harness that measures the policy could not override the policy it is
//! measuring. The one qualification is that an explicit but *unparseable*
//! numeric value resolves to the compiled default rather than to the policy —
//! see [`num`] for why that exact choice is what makes migration
//! behaviour-preserving for every input string.
//!
//! # The caller layer, and why the environment is a snapshot
//!
//! The top layer arrives with the solve rather than with the process. It exists
//! because ay-milp's primary consumer is an in-process library user (a
//! multi-threaded NN verifier) which was configuring the engine the only way
//! the engine allowed — by mutating its own process environment mid-run, which
//! races with concurrent `getenv`, cannot express two differently-configured
//! concurrent solves, and let a malformed inherited value abort a worker.
//! the development design notes §M1 states the problem;
//! [`crate::EngineEconomics`] is the typed surface and
//! [`activate_caller`] installs it for the duration of one solve.
//!
//! The environment layer is read **once**, into [`EnvSnapshot`], and never
//! again — so no accessor on the solve path touches `std::env`. An exported
//! variable behaves exactly as it always has; mutating one mid-process and
//! expecting a live solve to see it does not, which no shipped lane did.

use crate::model::{ColKind, Model};

/// A tunable the engine may decide for itself.
///
/// Only *performance-relevant* settings belong here. The great majority of the
/// crate's environment variables are diagnostics (`AY_MILP_TRACE`,
/// `AY_MILP_*_DEBUG`) or A/B kill switches that exist so a measurement can
/// disable one mechanism; neither is something the engine should decide, and
/// neither appears in this enum.
///
/// The second block is different in kind: those twelve are the knobs an
/// embedding *consumer* configures per solve. They are here because
/// [`crate::EngineEconomics`] needs a typed carrier for them and this is the
/// crate's one table mapping a setting to its historical environment spelling;
/// giving them a second, parallel table is how a kill switch and its typed
/// setter come to disagree.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub(crate) enum Knob {
    /// Full GMI/MIR separation rounds at the root.
    GmiRounds,
    /// Cuts retained per round at the root (node budget is separate).
    RootCutsPerRound,
    /// Run implication probing at the root.
    RootProbe,
    /// Depth-first node selection.
    Dfs,
    /// Separate cuts at nodes below the root.
    NodeCuts,
    /// Dive toward a leaf after branching, to buy an incumbent.
    Plunge,

    // The twelve `crates/ny-mip/src/ay_lib.rs` pins today, per
    // the development design notes §M1. Negative senses
    // (`No*`) are kept exactly as the environment spells them, because the
    // accessor convention is per *variable*, not per concept: inverting one
    // here to read positively would flip what an operator's existing
    // `AY_MILP_NO_CUTS=1` means. The public builder is positive-sense
    // (`with_cuts(false)`) and does the one inversion, in one place.
    /// Disable the market-split lattice detector (`lattice::try_prove`).
    NoLattice,
    /// Disable the flip-LNS saturation stop.
    NoSatStop,
    /// Saturation-stop dry-spell floor, in seconds.
    SatStopSecs,
    /// Saturation-stop multiplier on the largest observed improvement gap.
    SatStopMult,
    /// Disable the tall-degenerate bloom-cap relaxation.
    NoBloomRelax,
    /// Absolute cap on the flip-LNS window for `tall_lu` models, in seconds.
    FlipCapSecs,
    /// Flip-LNS share of the remaining budget. Setting it at all also opts out
    /// of the absolute cap — see the call site at `bab.rs:19251`.
    FlipShare,
    /// Install an LU engine in the pooled `WarmSolver`.
    WarmLu,
    /// Share of the remaining budget handed to bound-propagation presolve.
    PresolveShare,
    /// Disable root cut separation.
    NoCuts,
    /// Feasibility-pump restart allowance (`0` skips the pump).
    PumpRestarts,
    /// Cap on committed pins in the terminal-salvage dive.
    DiveMaxPins,
}

impl Knob {
    /// The environment variable that overrides this knob.
    ///
    /// One table, so a call site can never disagree with the harness about the
    /// spelling of its own knob.
    pub(crate) const fn env(self) -> &'static str {
        match self {
            Self::GmiRounds => "AY_MILP_GMI_ROUNDS",
            Self::RootCutsPerRound => "AY_MILP_ROOT_CUTS_PER_ROUND",
            Self::RootProbe => "AY_MILP_ROOT_PROBE",
            Self::Dfs => "AY_MILP_DFS",
            Self::NodeCuts => "AY_MILP_NODE_CUTS",
            Self::Plunge => "AY_MILP_PLUNGE",
            Self::NoLattice => "AY_MILP_NO_LATTICE",
            Self::NoSatStop => "AY_MILP_NO_SAT_STOP",
            Self::SatStopSecs => "AY_MILP_SAT_STOP_SECS",
            Self::SatStopMult => "AY_MILP_SAT_STOP_MULT",
            Self::NoBloomRelax => "AY_MILP_NO_BLOOM_RELAX",
            Self::FlipCapSecs => "AY_MILP_FLIP_CAP_SECS",
            Self::FlipShare => "AY_MILP_FLIP_SHARE",
            Self::WarmLu => "AY_MILP_WARM_LU",
            Self::PresolveShare => "AY_MILP_PRESOLVE_SHARE",
            Self::NoCuts => "AY_MILP_NO_CUTS",
            Self::PumpRestarts => "AY_MILP_PUMP_RESTARTS",
            Self::DiveMaxPins => "AY_MILP_DIVE_MAX_PINS",
        }
    }

    const ALL: [Knob; 18] = [
        Self::GmiRounds,
        Self::RootCutsPerRound,
        Self::RootProbe,
        Self::Dfs,
        Self::NodeCuts,
        Self::Plunge,
        Self::NoLattice,
        Self::NoSatStop,
        Self::SatStopSecs,
        Self::SatStopMult,
        Self::NoBloomRelax,
        Self::FlipCapSecs,
        Self::FlipShare,
        Self::WarmLu,
        Self::PresolveShare,
        Self::NoCuts,
        Self::PumpRestarts,
        Self::DiveMaxPins,
    ];

    const fn slot(self) -> usize {
        match self {
            Self::GmiRounds => 0,
            Self::RootCutsPerRound => 1,
            Self::RootProbe => 2,
            Self::Dfs => 3,
            Self::NodeCuts => 4,
            Self::Plunge => 5,
            Self::NoLattice => 6,
            Self::NoSatStop => 7,
            Self::SatStopSecs => 8,
            Self::SatStopMult => 9,
            Self::NoBloomRelax => 10,
            Self::FlipCapSecs => 11,
            Self::FlipShare => 12,
            Self::WarmLu => 13,
            Self::PresolveShare => 14,
            Self::NoCuts => 15,
            Self::PumpRestarts => 16,
            Self::DiveMaxPins => 17,
        }
    }
}

/// A value chosen for a knob, by the policy or by the caller.
///
/// `Count` is not a redundant `Num`: `DiveMaxPins` defaults to `usize::MAX`
/// (`bab.rs:6363`), which does not survive a `usize -> i64 -> usize` round trip
/// and would come back as `i64::MAX`. A settable knob whose own default cannot
/// be spelled in the carrier is a trap, so counts keep their width.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum Setting {
    /// A boolean mechanism the policy turns on or off.
    Flag(bool),
    /// A budget or count.
    #[cfg_attr(not(test), allow(dead_code))]
    Num(i64),
    /// A count that must survive `usize`'s full range.
    Count(usize),
    /// A share, multiplier or seconds value, in `[0, MAX_REAL]`. Every
    /// consumer feeds it to `Duration::from_secs_f64`/`mul_f64`, which *panic*
    /// on a negative, a non-finite, or an over-large input, so a value outside
    /// the domain reads as no opinion rather than as itself.
    Real(f64),
}

impl Setting {
    /// As an `i64` budget, or `None` if this setting is not a number or does
    /// not fit.
    #[cfg_attr(not(test), allow(dead_code))]
    fn as_num(self) -> Option<i64> {
        match self {
            Setting::Num(n) => Some(n),
            Setting::Count(n) => i64::try_from(n).ok(),
            Setting::Flag(_) | Setting::Real(_) => None,
        }
    }

    /// As a `usize` count. A negative takes `None`: every consumer is a count
    /// or a budget, for which a negative is meaningless rather than
    /// meaningfully zero.
    fn as_count(self) -> Option<usize> {
        match self {
            Setting::Count(n) => Some(n),
            Setting::Num(n) => usize::try_from(n).ok(),
            Setting::Flag(_) | Setting::Real(_) => None,
        }
    }

    /// As a finite non-negative real.
    fn as_real(self) -> Option<f64> {
        match self {
            Setting::Real(v) if in_real_domain(v) => Some(v),
            _ => None,
        }
    }
}

/// The settings selected for one model. `None` means *no opinion* — fall
/// through to the call site's compiled default.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Profile {
    entries: [Option<Setting>; Knob::ALL.len()],
}

impl Profile {
    /// No opinion about anything. The identity element, and the shipped policy.
    pub(crate) const EMPTY: Profile = Profile {
        entries: [None; Knob::ALL.len()],
    };

    fn get(&self, k: Knob) -> Option<Setting> {
        self.entries[k.slot()]
    }

    pub(crate) fn with(mut self, k: Knob, v: Setting) -> Self {
        self.entries[k.slot()] = Some(v);
        self
    }

    /// `self`, with every knob `other` has an opinion about taken from `other`.
    ///
    /// Used to inherit an enclosing solve's caller settings into a sub-MIP:
    /// the RENS sub-search builds its options with `..Default::default()`
    /// (`bab.rs:10943`), so without inheritance a consumer's per-solve
    /// configuration would silently stop applying inside every sub-search it
    /// spawns — the one place a "per-`SolveOpts`" promise is easiest to break.
    pub(crate) fn overlay(mut self, other: Profile) -> Self {
        for k in Knob::ALL {
            if let Some(v) = other.get(k) {
                self.entries[k.slot()] = Some(v);
            }
        }
        self
    }

    /// Is this profile silent about every knob?
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn is_empty(&self) -> bool {
        self.entries.iter().all(Option::is_none)
    }
}

impl Default for Profile {
    fn default() -> Self {
        Self::EMPTY
    }
}

// --------------------------------------------------------------------- shape

/// Cheaply computed structural features of a model.
///
/// Every field is filled by a single pass over the columns and one over the
/// rows, both of which are dense `Vec`s — this is measured in microseconds on
/// the corpus and is not on any hot path regardless, being computed once per
/// solve rather than per node.
///
/// Fields exist here only when something plausibly *selects* on them. The
/// existing inline heuristics in `bab.rs` already select on `cols + rows`
/// (`TINY_GMI_COLS_PLUS_ROWS`) and on general-integer counts
/// (`wants_gi_extension`), so those are represented directly.
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) struct Shape {
    pub(crate) rows: usize,
    pub(crate) cols: usize,
    /// Structural nonzeros in the constraint matrix.
    pub(crate) nnz: usize,
    pub(crate) binaries: usize,
    /// Integer columns that are not binary.
    pub(crate) general_ints: usize,
    pub(crate) continuous: usize,
    /// General-integer columns with an infinite bound.
    ///
    /// **Not** a proxy for the `ej` defect class, though it was introduced as
    /// one. Unboundedness was measured on 2026-07-27 NOT to be why ej defeats
    /// ay: oracle-tight bounds taken from the true optimum leave it unproved at
    /// 316,909 nodes, while the LLL kernel reformulation — whose columns are
    /// unbounded on *both* sides — closes it in 5 nodes. The operative property
    /// is that ej's node LP bound moves only with the LOWER bounds, so
    /// single-variable branching needs ~10^8 leaves. See
    /// the development design notes.
    ///
    /// It earns its place for a different and better-evidenced reason: an
    /// unbounded column silently discards every cut whose support touches it
    /// (`cuts.rs:2117-2120` and five sibling sites), which is measured to
    /// affect 71% of the corpus. That makes it a real regime marker for
    /// separation, not for branching.
    pub(crate) unbounded_ints: usize,
    /// Rows with `lb == ub`.
    pub(crate) equalities: usize,
    /// The longest row, which bounds what dense-row separators will cost.
    pub(crate) max_row_len: usize,
    /// Ratio of largest to smallest nonzero `|coefficient|`, saturating at
    /// `f64::INFINITY`. A wide range is the conditioning signal that decides
    /// whether float advice can be trusted before exact certification.
    pub(crate) coeff_range: f64,
}

impl Shape {
    /// Extract features from a model.
    pub(crate) fn of(model: &Model) -> Shape {
        let mut binaries = 0usize;
        let mut general_ints = 0usize;
        let mut continuous = 0usize;
        let mut unbounded_ints = 0usize;
        for c in &model.cols {
            match c.kind {
                ColKind::Binary => binaries += 1,
                ColKind::Integer => {
                    general_ints += 1;
                    if c.lb.is_infinite() || c.ub.is_infinite() {
                        unbounded_ints += 1;
                    }
                }
                ColKind::Continuous => continuous += 1,
            }
        }
        let mut nnz = 0usize;
        let mut equalities = 0usize;
        let mut max_row_len = 0usize;
        let mut lo = f64::INFINITY;
        let mut hi = 0.0f64;
        for r in &model.rows {
            nnz += r.coeffs.len();
            max_row_len = max_row_len.max(r.coeffs.len());
            if r.lb == r.ub {
                equalities += 1;
            }
            for &(_, v) in &r.coeffs {
                let a = v.abs();
                // Explicit zeros are excluded by RowSpec's invariant, but a
                // denormal would still poison the ratio.
                if a > 0.0 {
                    lo = lo.min(a);
                    hi = hi.max(a);
                }
            }
        }
        let coeff_range = if lo.is_finite() && lo > 0.0 && hi > 0.0 {
            hi / lo
        } else {
            1.0
        };
        Shape {
            rows: model.rows.len(),
            cols: model.cols.len(),
            nnz,
            binaries,
            general_ints,
            continuous,
            unbounded_ints,
            equalities,
            max_row_len,
            coeff_range,
        }
    }

    /// Fraction of columns that must take integer values.
    pub(crate) fn integrality_fraction(&self) -> f64 {
        if self.cols == 0 {
            return 0.0;
        }
        (self.binaries + self.general_ints) as f64 / self.cols as f64
    }

    /// Matrix density in `[0, 1]`.
    pub(crate) fn density(&self) -> f64 {
        let cells = self.rows.saturating_mul(self.cols);
        if cells == 0 {
            return 0.0;
        }
        self.nnz as f64 / cells as f64
    }

    /// Every integral column is binary and there are no continuous columns.
    pub(crate) fn is_pure_binary(&self) -> bool {
        self.general_ints == 0 && self.continuous == 0 && self.binaries > 0
    }
}

// -------------------------------------------------------------------- policy

/// The mapping from model shape to settings.
pub(crate) struct Policy;

impl Policy {
    /// Choose settings for a shape.
    ///
    /// **Currently selects nothing**, and that is deliberate rather than
    /// unfinished. Shipping the plumbing separately from the policy makes the
    /// plumbing's no-op property testable on its own
    /// ([`tests::empty_policy_is_a_no_op`]), so that when the first rule lands
    /// any measured change is attributable to that rule and not to the
    /// migration of a hundred call sites.
    ///
    /// A rule is added here only with a corpus measurement showing it wins on
    /// the shapes it fires for and does not lose elsewhere — the standard the
    /// previous campaign's four transplants each failed. `scripts/
    /// milp_portfolio.py` produces that evidence.
    pub(crate) fn select(_shape: &Shape) -> Profile {
        Profile::EMPTY
    }
}

// ------------------------------------------------------------------- runtime

/// One entry of the active stack: the two profile layers of a live solve.
///
/// They are separate because they rank on opposite sides of the environment.
/// `caller` is what an embedding consumer asked for *on this solve's*
/// [`crate::SolveOpts`] and outranks everything, so a stray `AY_MILP_*`
/// inherited from a CI shell cannot reconfigure a scored run; `policy` is what
/// the engine selected for itself from the model's shape and is outranked by
/// the environment, so the harness measuring the policy can still override it.
#[derive(Debug, Clone, Copy)]
struct Frame {
    caller: Profile,
    policy: Profile,
}

thread_local! {
    /// The active profile stack.
    ///
    /// A stack rather than a single slot because sub-MIP lanes (RENS, RINS,
    /// local-branching) re-enter the solver *on the same thread* while an outer
    /// solve is live. A sub-solve gets its own profile for its own sub-model
    /// and must restore the outer one on the way out; a flat slot would leak
    /// whichever finished last into the outer search.
    ///
    /// Thread-*local* is also what makes the caller layer per-session rather
    /// than per-process: two ny worker threads inside two concurrent ay solves
    /// see their own stacks, which is exactly the property
    /// `std::env::set_var` cannot offer (and the reason it is `unsafe` in
    /// edition 2024).
    static ACTIVE: std::cell::RefCell<Vec<Frame>> = const {
        std::cell::RefCell::new(Vec::new())
    };
}

/// Restores the enclosing profile when dropped.
///
/// Held by value at the solve entry point. `#[must_use]` because dropping it
/// immediately would silently un-tune the solve it was created for.
///
/// # Why this is `!Send` and depth-checked
///
/// The guard's `Drop` mutates a *thread-local* stack. Two ways that goes wrong,
/// both of which leave a solve running under a profile that was never selected
/// for it:
///
/// - **Moved across threads.** A guard created on thread A and dropped on
///   thread B would pop *B's* stack, leaving A's profile installed forever and
///   corrupting B's. The `PhantomData<*const ()>` makes the guard `!Send`, so
///   this is a compile error rather than a silent misconfiguration. This
///   matters more, not less, once parallel search returns.
/// - **Dropped out of order.** Popping blindly would let a guard released out
///   of LIFO order remove somebody else's entry. Each guard records the depth
///   it installed at and asserts it is the top on the way out.
///
/// The longer-term design is an explicit `SolveConfig` owned by the session and
/// passed by reference, which needs neither of these defences. This thread-local
/// is the adapter that lets existing call sites — which reach for a global
/// today, because `std::env` is one — migrate without threading a parameter
/// through twenty thousand lines first.
#[must_use = "the profile is active only while this guard is held"]
pub(crate) struct Active {
    depth: usize,
    /// Makes the guard `!Send`: its `Drop` is only correct on the thread that
    /// created it.
    _not_send: std::marker::PhantomData<*const ()>,
}

impl Drop for Active {
    fn drop(&mut self) {
        ACTIVE.with(|a| {
            let mut stack = a.borrow_mut();
            debug_assert_eq!(
                stack.len(),
                self.depth + 1,
                "tune::Active dropped out of LIFO order: installed at depth {} \
                 but the stack is {} deep",
                self.depth,
                stack.len(),
            );
            // In release, only pop what we actually own. Popping a shorter
            // stack would steal an enclosing solve's profile.
            if stack.len() == self.depth + 1 {
                stack.pop();
            }
        });
    }
}

/// Select a profile for `model` and make it active until the guard is dropped.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn activate(model: &Model) -> Active {
    let profile = Policy::select(&Shape::of(model));
    activate_profile(profile)
}

/// Make an explicit *policy* profile active. Exists for tests and for the
/// measurement harness, which needs to install a profile it did not derive.
pub(crate) fn activate_profile(profile: Profile) -> Active {
    push(Frame {
        caller: caller_layer(),
        policy: profile,
    })
}

/// Make a *caller* profile active for the duration of one solve.
///
/// This is the entry point for [`crate::EngineEconomics`]: the settings on the
/// solve's own `SolveOpts`, which outrank both the environment snapshot and the
/// policy.
///
/// Two deliberate choices, both visible in the body:
///
/// - The enclosing solve's caller layer is **inherited** and overlaid, so a
///   sub-MIP that builds its own options from `Default` (`bab.rs:10943`) still
///   runs under the settings the embedding consumer configured.
/// - The policy layer is **not** inherited. A policy is selected for one
///   model's shape; applying it to a sub-model it was never derived for is a
///   silent misconfiguration, and `Profile::EMPTY` is the honest answer until
///   the sub-solve selects its own.
pub(crate) fn activate_caller(profile: Profile) -> Active {
    push(Frame {
        caller: caller_layer().overlay(profile),
        policy: Profile::EMPTY,
    })
}

fn push(frame: Frame) -> Active {
    let depth = ACTIVE.with(|a| {
        let mut stack = a.borrow_mut();
        stack.push(frame);
        stack.len() - 1
    });
    Active {
        depth,
        _not_send: std::marker::PhantomData,
    }
}

fn caller_layer() -> Profile {
    ACTIVE.with(|a| a.borrow().last().map_or(Profile::EMPTY, |f| f.caller))
}

/// The enclosing solve's caller layer, to be carried to a worker thread.
///
/// The stack is thread-local and [`Active`] is deliberately `!Send`, so a
/// thread the search spawns starts with no settings at all. That is safe (it
/// falls back to the environment snapshot and the compiled defaults, exactly as
/// before this layer existed) but it is not what the caller asked for: read the
/// profile on the parent, hand the `Copy` value to the worker, and let the
/// worker call [`activate_caller`] with it on its own stack.
pub(crate) fn caller_profile() -> Profile {
    caller_layer()
}

fn caller(k: Knob) -> Option<Setting> {
    ACTIVE.with(|a| a.borrow().last().and_then(|f| f.caller.get(k)))
}

fn policy(k: Knob) -> Option<Setting> {
    ACTIVE.with(|a| a.borrow().last().and_then(|f| f.policy.get(k)))
}

// ------------------------------------------------------------ env  snapshot

/// The `AY_MILP_*` environment as it stood the first time the engine looked.
///
/// # Why a snapshot and not a read
///
/// ay-milp is consumed in-process by a heavily multi-threaded verifier
/// (the development design notes §M1), and `std::env::set_var`
/// races with a concurrent `getenv` — which is precisely why it is `unsafe` in
/// edition 2024. A solver that reads the environment *during* a solve makes
/// that race the consumer's problem: the downstream optimization consumer's recorded mitigation is to rewrite the
/// same constant values before every window solve, which works only because
/// every value it writes is constant.
///
/// Capturing once and resolving from the capture removes the read from the
/// solve path entirely while preserving the operator workflow verbatim: a
/// variable exported before the process starts is seen exactly as before.
/// What it does *not* preserve is mutating the environment mid-process and
/// expecting a live solve to notice — no shipped lane did that, and the
/// in-crate A/B tests that do are handled by the test seam below.
struct EnvSnapshot {
    values: [Option<std::ffi::OsString>; Knob::ALL.len()],
}

impl EnvSnapshot {
    /// Read every knob's variable once. Values are stored as `OsString`, not
    /// `String`: `on` tests *presence* (`var_os`) while the parsing accessors
    /// use `var`, and only keeping the raw bytes preserves the difference for a
    /// non-UTF-8 value, which `var` reports as absent and `var_os` as present.
    fn capture() -> Self {
        Self {
            values: std::array::from_fn(|i| std::env::var_os(Knob::ALL[i].env())),
        }
    }

    fn get(&self, k: Knob) -> Option<&std::ffi::OsStr> {
        self.values[k.slot()].as_deref()
    }
}

/// The snapshot layer for one knob.
///
/// # The test build reads live, and that is the seam
///
/// Under `cfg(test)` this reads the process environment on every call. The
/// crate's own kill-switch coverage sets variables *at runtime* with
/// `ay_test_support::env::ScopedEnvVar` (`AY_MILP_NO_CUTS` alone at five sites
/// in `bab.rs`), and a frozen snapshot would turn every one of those into a
/// test that silently exercises the opposite configuration from the one it
/// names. The behaviour under test is identical either way — the layer supplies
/// the same bytes, only the moment of the read differs — and the capture itself
/// is covered directly by [`tests::snapshot_captures_the_environment`] rather
/// than by whichever variables happen to be exported.
#[cfg(not(test))]
fn env_layer(k: Knob) -> Option<std::borrow::Cow<'static, std::ffi::OsStr>> {
    static SNAPSHOT: std::sync::OnceLock<EnvSnapshot> = std::sync::OnceLock::new();
    SNAPSHOT
        .get_or_init(EnvSnapshot::capture)
        .get(k)
        .map(std::borrow::Cow::Borrowed)
}

#[cfg(test)]
fn env_layer(k: Knob) -> Option<std::borrow::Cow<'static, std::ffi::OsStr>> {
    std::env::var_os(k.env()).map(std::borrow::Cow::Owned)
}

/// One knob as the shipped `env_layer` and a fresh `EnvSnapshot` see it.
///
/// # Why this is `pub` at all
///
/// `env_layer` forks on `cfg(test)`, and the arm every release resolves from —
/// the frozen `OnceLock` capture — is the one no test in this module can reach:
/// a unit test compiles the live-read arm instead. An integration test links
/// the crate *without* `cfg(test)` and so gets the shipped arm, but cannot see
/// a private module. The result before this existed was that the shipped arm
/// was asserted about by nothing: replacing its `var_os` with `var` would have
/// collapsed the presence-vs-UTF-8 distinction `on` rests on — a non-UTF-8
/// `AY_MILP_NO_CUTS` would have read as *absent*, silently turning a consumer's
/// kill switch off — and passed the entire suite.
///
/// `tests/env_layer_snapshot.rs` is that coverage and this is the narrowest
/// surface that supports it: no `Knob`, no `Profile`, no way to *install*
/// anything, and `#[doc(hidden)]` so it is not a documented API.
#[doc(hidden)]
#[derive(Debug, Clone, PartialEq)]
pub struct EnvLayerProbe {
    /// The variable this knob reads.
    pub name: &'static str,
    /// What the shipped `env_layer` resolved: the frozen snapshot outside
    /// `cfg(test)`, a live read inside it.
    pub layer: Option<std::ffi::OsString>,
    /// A *fresh* `EnvSnapshot::capture` of the same variable, taken now. Equal
    /// to `layer` while the environment has not moved since the capture, and
    /// deliberately not equal after it has — which is how a test tells a frozen
    /// snapshot from a live read.
    pub capture: Option<std::ffi::OsString>,
    /// `on`: presence, via `var_os`. True for a non-UTF-8 value.
    pub on: bool,
    /// `real_opt`: parses, via `var`. `None` for a non-UTF-8 value.
    pub real_opt: Option<f64>,
    /// `count_opt`: parses, via `var`. `None` for a non-UTF-8 value.
    pub count_opt: Option<usize>,
}

/// Probe the environment layer for the knob spelled `env_name`, or `None` if no
/// knob reads that variable.
///
/// **This call may be what first captures the snapshot**, since the capture is
/// lazy. A test that wants a variable in the snapshot must export it before
/// calling this.
#[doc(hidden)]
#[must_use]
pub fn diag_env_layer(env_name: &str) -> Option<EnvLayerProbe> {
    let k = Knob::ALL.into_iter().find(|k| k.env() == env_name)?;
    Some(EnvLayerProbe {
        name: k.env(),
        layer: env_layer(k).map(std::borrow::Cow::into_owned),
        capture: EnvSnapshot::capture().get(k).map(std::ffi::OsStr::to_owned),
        on: on(k),
        real_opt: real_opt(k),
        count_opt: count_opt(k),
    })
}

/// The snapshot layer as `std::env::var(K).ok()` would have reported it.
///
/// By reference, not by value: the shipped path borrows from the snapshot, so
/// the historical `String` allocation per read disappears with it. A non-UTF-8
/// value is `None` here and `Some` to [`on`], matching `var`/`var_os`.
fn with_env_str<R>(k: Knob, f: impl FnOnce(Option<&str>) -> R) -> R {
    match env_layer(k) {
        Some(v) => f(v.to_str()),
        None => f(None),
    }
}

// ----------------------------------------------------------------- accessors
//
// One accessor per environment-variable convention already in the crate. The
// crate spells "on" three different ways at different call sites — presence,
// exactly "1", and anything-but-"0" — and a single normalised accessor would
// silently change behaviour at whichever sites did not match the normal form.
// Preserving all three is what makes migration mechanical; unifying them is a
// separate change that has to be measured, not smuggled in here.
//
// Every accessor resolves the same four layers, in this order:
//
//     caller (SolveOpts)  >  environment snapshot  >  policy  >  compiled default
//
// The caller layer is first because it is the one an embedding consumer can
// reason about: ny pays -150 for a wrong verdict and needs a stray inherited
// `AY_MILP_*` to be unable to change what it configured. The environment stays
// ahead of the *policy* for the reason the module header gives — the harness
// that measures a policy rule has to be able to override the rule it is
// measuring — and while `Policy::select` returns `EMPTY` the two are in any
// case indistinguishable.

/// Environment *presence* means on: `env::var_os(K).is_some()`.
///
/// # Trap, preserved deliberately
///
/// `AY_MILP_DFS=0` reads as **on**, because presence is the whole test. That is
/// surprising, and it is what the call sites have always done
/// (`bab.rs:16538`); changing it here would silently flip behaviour for anyone
/// who has ever written `=0` expecting off. The inconsistency is real and
/// belongs on a list to fix deliberately, with a deprecation cycle — not as an
/// invisible side effect of moving the read into this module.
pub(crate) fn on(k: Knob) -> bool {
    if let Some(Setting::Flag(b)) = caller(k) {
        return b;
    }
    if env_layer(k).is_some() {
        return true;
    }
    matches!(policy(k), Some(Setting::Flag(true)))
}

/// Environment value exactly `"1"` means on; any other explicit value means
/// off: `env::var(K).as_deref() == Ok("1")`.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn on_strict(k: Knob) -> bool {
    if let Some(Setting::Flag(b)) = caller(k) {
        return b;
    }
    with_env_str(k, |v| match v {
        Some(v) => v == "1",
        None => matches!(policy(k), Some(Setting::Flag(true))),
    })
}

/// On unless explicitly `"0"`, and on by default:
/// `env::var(K).map_or(true, |v| v != "0")`.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn on_unless_zero(k: Knob) -> bool {
    if let Some(Setting::Flag(b)) = caller(k) {
        return b;
    }
    with_env_str(k, |v| match v {
        Some(v) => v != "0",
        None => match policy(k) {
            Some(Setting::Flag(b)) => b,
            _ => true,
        },
    })
}

/// A numeric budget. Resolution order:
///
/// ```text
/// explicit valid environment value  >  policy  >  compiled default
/// ```
///
/// # An explicitly set but unparseable value takes the compiled default
///
/// It does **not** fall through to the policy, and the distinction is not
/// pedantic. The call sites spell this as `.ok().and_then(|v| v.parse().ok())
/// .unwrap_or(DEFAULT)` (`bab.rs:17368`, `cuts.rs:1422`), so under the old code
/// `AY_MILP_GMI_ROUNDS=garbage` yields `DEFAULT`. Routing garbage to the policy
/// would make migration behaviour-preserving only while the policy is empty,
/// and would silently change what a malformed environment means on the day the
/// first rule lands. Preserving it here means a migrated call site behaves
/// identically for *every* input string, policy or no policy — which is the
/// property that lets rules be measured one at a time.
///
/// Note this is the one place the module-level "an explicit environment
/// variable always wins" is qualified: an explicit *invalid* value wins over
/// the policy too, but resolves to the compiled default rather than to itself.
///
/// # The raw value is parsed, not trimmed
///
/// Every pre-migration site parsed the string as it arrived — `cuts.rs:1422`
/// and `cuts.rs:1457` spell it `.ok().and_then(|v| v.parse().ok())`,
/// `finite_nonnegative_setting` (`bab.rs:3961`) spells it
/// `raw.and_then(|value| value.parse::<f64>().ok())` — so
/// `AY_MILP_DIVE_MAX_PINS=" 5"` parse-failed and left the dive uncapped at
/// `usize::MAX`. A `.trim()` here would silently reinterpret that exact recipe
/// as a cap of five: a 10^18 change in the knob, and a *different measured arm*
/// from the one the journal recorded against the identical string. Every result
/// in `reports/` is an A/B between two environments, so a migration that
/// re-reads one of those environments differently invalidates the comparison it
/// was supposed to preserve.
///
/// Whitespace tolerance may well be worth having. It is then its own change,
/// applied to the six knobs still read raw here as well, and measured — not a
/// side effect of moving a read into this module. Until then the claim above
/// holds without exception: a migrated call site behaves identically for every
/// input string, whitespace included.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn num(k: Knob, default: i64) -> i64 {
    if let Some(n) = caller(k).and_then(Setting::as_num) {
        return n;
    }
    with_env_str(k, |v| match v {
        Some(v) => v.parse::<i64>().unwrap_or(default),
        None => policy(k).and_then(Setting::as_num).unwrap_or(default),
    })
}

/// [`num`] clamped to `usize`, for budgets and counts.
///
/// A negative resolved value takes `default`: every consumer of this is a count
/// or a budget, for which a negative is meaningless rather than meaningfully
/// zero.
pub(crate) fn count(k: Knob, default: usize) -> usize {
    // Resolved in `usize` throughout rather than by delegating to `num`: a
    // `usize` default above `i64::MAX` cannot survive a `usize -> i64 -> usize`
    // round trip, and would come back clamped to `i64::MAX` instead of itself.
    if let Some(n) = caller(k).and_then(Setting::as_count) {
        return n;
    }
    with_env_str(k, |v| match v {
        Some(v) => v.parse::<usize>().unwrap_or(default),
        None => policy(k).and_then(Setting::as_count).unwrap_or(default),
    })
}

/// A count whose *absence* is meaningful, for the call sites that spell the
/// read `env::var(K).ok().and_then(|v| v.parse().ok())` and then branch on the
/// `Option` (`AY_MILP_PUMP_RESTARTS`, `bab.rs:18873`).
///
/// An unparseable explicit value is `None`, exactly as `.ok().and_then(..)`
/// made it — and, following [`num`], it does not fall through to the policy.
pub(crate) fn count_opt(k: Knob) -> Option<usize> {
    if let Some(n) = caller(k).and_then(Setting::as_count) {
        return Some(n);
    }
    with_env_str(k, |v| match v {
        Some(v) => v.parse::<usize>().ok(),
        None => policy(k).and_then(Setting::as_count),
    })
}

/// A finite, non-negative real: a share, a multiplier, or a seconds value.
///
/// # Why the domain is part of the accessor
///
/// Every consumer of these knobs feeds the value to `Duration::from_secs_f64`
/// or `Duration::mul_f64`, **both of which panic** on a negative or non-finite
/// input. So `AY_MILP_SAT_STOP_MULT=-1` was an abort, in-process, inside a
/// consumer's solve — which is the third of the three consequences ny recorded
/// against the environment surface: *"malformed inherited values must never
/// panic an in-process verifier worker"*. Rejecting the value here is the fix,
/// and it is a behaviour change on exactly one input class: values that used to
/// panic now resolve to the compiled default. `1e26` is the same defect from
/// the other end — a well-formed `f64` that overflows `Duration` — which is
/// why the domain is bounded above as well as below (see [`MAX_REAL`]).
///
/// Rejection rather than clamping, where `finite_nonnegative_setting`
/// (`bab.rs:3515`) clamps with `.max(0.0)`: this module's rule for an explicit
/// but invalid value is already "take the compiled default" (see [`num`]), and
/// a `PRESOLVE_SHARE` of `0` is a materially different instruction from a
/// malformed one — silently reading `-0.5` as "no presolve budget" would be a
/// configuration the operator never asked for.
pub(crate) fn real(k: Knob, default: f64) -> f64 {
    if let Some(v) = caller(k).and_then(Setting::as_real) {
        return v;
    }
    with_env_str(k, |v| match v {
        Some(v) => parse_real(v).unwrap_or(default),
        None => policy(k).and_then(Setting::as_real).unwrap_or(default),
    })
}

/// [`real`] where absence is meaningful.
///
/// `AY_MILP_FLIP_SHARE` is the case: setting it at all *also* opts out of the
/// absolute flip-LNS cap (`bab.rs:19265`), so "set to the same value as the
/// default" and "unset" are different instructions and cannot share a
/// signature.
pub(crate) fn real_opt(k: Knob) -> Option<f64> {
    if let Some(v) = caller(k).and_then(Setting::as_real) {
        return Some(v);
    }
    with_env_str(k, |v| match v {
        Some(v) => parse_real(v),
        None => policy(k).and_then(Setting::as_real),
    })
}

/// The environment half of [`real`]/[`real_opt`]: parse the raw value exactly
/// as `finite_nonnegative_setting` (`bab.rs:3961`) did, then apply the domain.
/// Not trimmed, for the reason [`num`] gives.
fn parse_real(raw: &str) -> Option<f64> {
    raw.parse::<f64>().ok().filter(|v| in_real_domain(*v))
}

/// The admissible domain for every [`Setting::Real`], shared by the accessors
/// and by [`crate::EngineEconomics`]'s builders so one number defines it.
///
/// The upper bound is not decoration. `Duration::from_secs_f64` panics above
/// `u64::MAX` seconds, so `AY_MILP_SAT_STOP_SECS=1e26` — a perfectly
/// well-formed `f64` — aborted the process at `bab.rs:12338`. `1e15` seconds
/// is ~31 million years: past any deadline anyone will ever set, and far
/// enough below the panic threshold that a consumer multiplying it by a
/// duration (`sat_mult`) stays inside the type as well.
pub(crate) const MAX_REAL: f64 = 1e15;

fn in_real_domain(v: f64) -> bool {
    v.is_finite() && (0.0..=MAX_REAL).contains(&v)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::model::Sense;
    use ay_test_support::env::{lock_env, ScopedEnvVar};
    use std::time::Duration;

    /// Environment reads are process-global, so tests that set them cannot run
    /// concurrently with tests that read them.
    ///
    /// This is the CRATE-WIDE lock, not a module-local one, and it has to be:
    /// `Knob::ALL` now covers `AY_MILP_NO_CUTS`, `AY_MILP_WARM_LU` and ten more
    /// variables that `bab.rs`'s and `cuts.rs`'s kill-switch tests set at
    /// runtime under `ay_test_support::env::lock_env`. Two independent mutexes
    /// over one process environment serialize nothing.
    ///
    /// `ScopedEnvVar` rather than raw `set_var`/`remove_var` for the same
    /// reason it exists: it restores the previous value on drop, including on
    /// panic, so a test cannot strip an operator's exported configuration from
    /// the rest of the run.
    fn unset_all_knobs() -> Vec<ScopedEnvVar> {
        Knob::ALL
            .iter()
            .map(|k| ScopedEnvVar::unset(k.env()))
            .collect()
    }

    fn tiny_model() -> Model {
        let mut m = Model::new();
        let x = m.add_binary_col();
        let y = m.add_int_col(0.0, 10.0);
        let z = m.add_col(0.0, f64::INFINITY);
        m.add_row(1.0, 1.0, &[(x, 1.0), (y, 2.0)]);
        m.add_row(f64::NEG_INFINITY, 5.0, &[(y, 1.0), (z, 4.0)]);
        m.set_objective(&[(x, 1.0)], Sense::Minimize);
        m
    }

    #[test]
    fn shape_reads_the_model() {
        let s = Shape::of(&tiny_model());
        assert_eq!(s.rows, 2);
        assert_eq!(s.cols, 3);
        assert_eq!(s.nnz, 4);
        assert_eq!(s.binaries, 1);
        assert_eq!(s.general_ints, 1);
        assert_eq!(s.continuous, 1);
        assert_eq!(s.equalities, 1, "row 0 has lb == ub");
        assert_eq!(s.max_row_len, 2);
        assert_eq!(s.unbounded_ints, 0, "y is bounded [0, 10]");
        assert!((s.coeff_range - 4.0).abs() < 1e-12, "|4| / |1|");
        assert!(!s.is_pure_binary());
    }

    /// The `ej` defect class is visible in the features.
    #[test]
    fn unbounded_integer_columns_are_visible() {
        let mut m = Model::new();
        let a = m.add_int_col(1.0, f64::INFINITY);
        let b = m.add_int_col(0.0, f64::INFINITY);
        m.add_row(0.0, 0.0, &[(a, 31013.0), (b, -41014.0)]);
        let s = Shape::of(&m);
        assert_eq!(s.unbounded_ints, 2);
        assert_eq!(s.general_ints, 2);
    }

    #[test]
    fn empty_shape_does_not_divide_by_zero() {
        let s = Shape::of(&Model::new());
        assert_eq!(s.density(), 0.0);
        assert_eq!(s.integrality_fraction(), 0.0);
        assert!(!s.is_pure_binary());
        assert_eq!(s.coeff_range, 1.0);
    }

    /// THE SAFETY PROPERTY. With the shipped policy, every accessor returns
    /// exactly what the pre-migration call site returned: the environment if
    /// set, the compiled default otherwise. This is what makes migrating a call
    /// site behaviour-preserving, and it must keep holding for as long as
    /// `Policy::select` is empty.
    #[test]
    fn empty_policy_is_a_no_op() {
        let _lock = lock_env();
        let _clean = unset_all_knobs();
        let profile = Policy::select(&Shape::of(&tiny_model()));
        assert!(profile.is_empty(), "shipped policy must select nothing");
        let _g = activate_profile(profile);
        for k in Knob::ALL {
            assert!(!on(k), "{:?}: unset must be off", k);
            assert!(!on_strict(k), "{:?}: unset must be off", k);
            assert!(on_unless_zero(k), "{:?}: unset must be on", k);
            assert_eq!(num(k, 7), 7, "{:?}: unset must be the default", k);
            assert_eq!(count(k, 9), 9, "{:?}: unset must be the default", k);
            assert_eq!(real(k, 0.25), 0.25, "{:?}: unset must be the default", k);
            assert_eq!(count_opt(k), None, "{:?}: unset must be absent", k);
            assert_eq!(real_opt(k), None, "{:?}: unset must be absent", k);
        }
    }

    #[test]
    fn environment_beats_policy() {
        let _lock = lock_env();
        let k = Knob::GmiRounds;
        let _g = activate_profile(
            Profile::EMPTY
                .with(k, Setting::Num(10))
                .with(Knob::Dfs, Setting::Flag(true)),
        );
        {
            let _clean = ScopedEnvVar::unset(k.env());
            assert_eq!(num(k, 2), 10, "policy applies when the env is unset");
        }
        {
            let _set = ScopedEnvVar::set(k.env(), "3");
            assert_eq!(num(k, 2), 3, "an explicit env var outranks the policy");
        }
        let _clean = ScopedEnvVar::unset(k.env());
        assert_eq!(num(k, 2), 10);

        let _no_dfs = ScopedEnvVar::unset(Knob::Dfs.env());
        assert!(on(Knob::Dfs), "policy can turn a flag on");
        let _dfs = ScopedEnvVar::set(Knob::Dfs.env(), "0");
        assert!(
            !on_strict(Knob::Dfs),
            "an explicit 0 outranks a policy true"
        );
    }

    /// An explicitly set but unparseable value resolves to the COMPILED
    /// DEFAULT, not to the policy and not to zero. This is what makes a
    /// migrated call site behave identically for every input string whether or
    /// not a policy rule exists for the knob — see [`num`].
    #[test]
    fn unparseable_env_takes_the_compiled_default_not_the_policy() {
        let _lock = lock_env();
        let k = Knob::RootCutsPerRound;
        let _g = activate_profile(Profile::EMPTY.with(k, Setting::Num(16)));
        {
            let _set = ScopedEnvVar::set(k.env(), "not-a-number");
            assert_eq!(num(k, 4), 4, "garbage must read as the compiled default");
        }
        {
            let _set = ScopedEnvVar::set(k.env(), "");
            assert_eq!(num(k, 4), 4, "empty must read as the compiled default");
        }
        let _clean = ScopedEnvVar::unset(k.env());
        assert_eq!(num(k, 4), 16, "unset still reaches the policy");
    }

    /// A `usize` default above `i64::MAX` must not wrap into a negative and
    /// come back as garbage.
    #[test]
    fn count_saturates_instead_of_wrapping() {
        let _lock = lock_env();
        let k = Knob::RootCutsPerRound;
        let _clean = ScopedEnvVar::unset(k.env());
        assert_eq!(count(k, usize::MAX), usize::MAX);
        let _g = activate_profile(Profile::EMPTY.with(k, Setting::Num(-3)));
        assert_eq!(count(k, 5), 5, "a negative count takes the default");
    }

    /// `DiveMaxPins` defaults to `usize::MAX` and a caller may legitimately set
    /// it there; `Setting::Count` is what lets that round-trip, where the
    /// `i64`-widthed `Num` would return `i64::MAX`.
    #[test]
    fn a_caller_count_round_trips_at_full_usize_width() {
        let _lock = lock_env();
        let k = Knob::DiveMaxPins;
        let _clean = ScopedEnvVar::unset(k.env());
        let _g = activate_caller(Profile::EMPTY.with(k, Setting::Count(usize::MAX)));
        assert_eq!(count(k, 16), usize::MAX);
    }

    /// The guard must not be `Send`: its `Drop` mutates a thread-local, so
    /// moving it across threads would pop the wrong thread's stack and strand
    /// the creating thread's profile.
    ///
    /// This is a genuine COMPILE-TIME assertion, not a runtime one. Two blanket
    /// impls are visible for `Active`; method resolution is ambiguous — and the
    /// crate therefore fails to build — exactly when `Active: Send` makes the
    /// second one apply. Removing the `PhantomData<*const ()>` from `Active`
    /// breaks the build here rather than silently reintroducing the bug.
    #[test]
    fn active_guard_is_not_send() {
        trait AmbiguousIfSend<A> {
            fn assert_not_send() {}
        }
        impl<T: ?Sized> AmbiguousIfSend<()> for T {}
        impl<T: ?Sized + Send> AmbiguousIfSend<u8> for T {}
        // Resolves only while `Active` is `!Send`.
        <Active as AmbiguousIfSend<_>>::assert_not_send();
    }

    /// Sub-MIP lanes re-enter the solver on the same thread; the outer profile
    /// has to survive that.
    #[test]
    fn nested_activation_restores_the_outer_profile() {
        let _lock = lock_env();
        let k = Knob::GmiRounds;
        let _clean = ScopedEnvVar::unset(k.env());
        let _outer = activate_profile(Profile::EMPTY.with(k, Setting::Num(2)));
        assert_eq!(num(k, 0), 2);
        {
            let _inner = activate_profile(Profile::EMPTY.with(k, Setting::Num(40)));
            assert_eq!(num(k, 0), 40, "the sub-solve sees its own profile");
        }
        assert_eq!(num(k, 0), 2, "the outer solve gets its profile back");
    }

    #[test]
    fn no_active_profile_is_the_compiled_default() {
        let _lock = lock_env();
        let _clean = unset_all_knobs();
        assert_eq!(num(Knob::GmiRounds, 2), 2);
        assert!(!on(Knob::RootProbe));
    }

    /// The selection entry point is wired for a policy that does not exist yet;
    /// exercising it keeps the `Shape`-to-`Policy` path compiling and honest.
    #[test]
    fn activating_for_a_model_selects_nothing_today() {
        let _lock = lock_env();
        let _clean = unset_all_knobs();
        let _g = activate(&tiny_model());
        assert!(!on(Knob::NoCuts));
        assert_eq!(real(Knob::PresolveShare, 0.35), 0.35);
    }

    // ------------------------------------------------------- the caller layer

    /// THE PROPERTY ny ASKED FOR. A setting carried on the solve outranks the
    /// process environment, in both directions: it can turn a knob on that the
    /// environment leaves off, and — the case that matters for a fail-closed
    /// consumer — it can turn a knob OFF that a stray inherited `AY_MILP_*`
    /// turns on.
    #[test]
    fn the_caller_layer_outranks_the_environment() {
        let _lock = lock_env();
        let k = Knob::NoCuts;
        let _env = ScopedEnvVar::set(k.env(), "1");
        assert!(on(k), "the environment alone still turns the knob on");

        let g = activate_caller(Profile::EMPTY.with(k, Setting::Flag(false)));
        assert!(!on(k), "the caller's setting outranks the environment");
        drop(g);
        assert!(on(k), "and stops applying when the solve ends");

        let share = Knob::PresolveShare;
        let _bad = ScopedEnvVar::set(share.env(), "0.9");
        let _g = activate_caller(Profile::EMPTY.with(share, Setting::Real(0.02)));
        assert_eq!(real(share, 0.35), 0.02);
    }

    /// Two concurrent solves configured differently must not see each other's
    /// settings. This is the whole point of the exercise: the environment
    /// cannot express it at all, because there is one environment per process.
    #[test]
    fn two_concurrent_solves_do_not_interfere() {
        let _lock = lock_env();
        let _clean = unset_all_knobs();
        let barrier = std::sync::Arc::new(std::sync::Barrier::new(2));

        let ready = std::sync::Arc::clone(&barrier);
        let cuts_off = std::thread::spawn(move || {
            let _g = activate_caller(
                Profile::EMPTY
                    .with(Knob::NoCuts, Setting::Flag(true))
                    .with(Knob::DiveMaxPins, Setting::Count(16)),
            );
            // Both profiles are installed before either is read.
            ready.wait();
            (on(Knob::NoCuts), count(Knob::DiveMaxPins, usize::MAX))
        });

        let ready = std::sync::Arc::clone(&barrier);
        let cuts_on = std::thread::spawn(move || {
            let _g = activate_caller(Profile::EMPTY.with(Knob::NoCuts, Setting::Flag(false)));
            ready.wait();
            (on(Knob::NoCuts), count(Knob::DiveMaxPins, usize::MAX))
        });

        assert_eq!(cuts_off.join().unwrap(), (true, 16));
        assert_eq!(
            cuts_on.join().unwrap(),
            (false, usize::MAX),
            "the second session sees neither of the first's settings"
        );
    }

    /// A sub-MIP inherits the enclosing solve's caller settings — the RENS
    /// sub-search builds its options from `Default`, so without inheritance a
    /// consumer's configuration would evaporate inside it — but can still
    /// override any one of them, and the outer layer is restored on the way
    /// out.
    #[test]
    fn a_sub_solve_inherits_and_may_override_the_caller_layer() {
        let _lock = lock_env();
        let _clean = unset_all_knobs();
        let _outer = activate_caller(
            Profile::EMPTY
                .with(Knob::NoCuts, Setting::Flag(true))
                .with(Knob::DiveMaxPins, Setting::Count(16)),
        );
        {
            let _sub = activate_caller(Profile::EMPTY.with(Knob::DiveMaxPins, Setting::Count(4)));
            assert!(on(Knob::NoCuts), "inherited from the enclosing solve");
            assert_eq!(count(Knob::DiveMaxPins, usize::MAX), 4, "overridden");
        }
        assert_eq!(count(Knob::DiveMaxPins, usize::MAX), 16);
    }

    /// A policy is selected for one model's shape and must not leak into a
    /// sub-model it was never derived for.
    #[test]
    fn a_sub_solve_does_not_inherit_the_policy_layer() {
        let _lock = lock_env();
        let _clean = unset_all_knobs();
        let _outer = activate_profile(Profile::EMPTY.with(Knob::GmiRounds, Setting::Num(9)));
        assert_eq!(num(Knob::GmiRounds, 2), 9);
        let _sub = activate_caller(Profile::EMPTY);
        assert_eq!(
            num(Knob::GmiRounds, 2),
            2,
            "the sub-solve starts unopinionated"
        );
    }

    // ------------------------------------------------------ malformed  input

    const GARBAGE: [&str; 9] = [
        "",
        " ",
        "not-a-number",
        "-0.5",
        "nan",
        "inf",
        "1e400",
        "0x10",
        "1,5",
    ];

    /// The knobs a malformed value may be PUBLISHED to the process environment
    /// for, because every consumer reads them through a parse that rejects it:
    ///
    /// ```text
    /// SatStopSecs    real       bab.rs:13030        garbage -> 15.0
    /// SatStopMult    real       bab.rs:13034        garbage -> 1.5
    /// PresolveShare  real       bab.rs:18193        garbage -> PRESOLVE_SHARE
    /// FlipCapSecs    real       bab.rs:20144        garbage -> the compiled cap
    /// FlipShare      real_opt   bab.rs:20129        garbage -> None == unset
    /// PumpRestarts   count_opt  bab.rs:19747        garbage -> None == unset
    /// DiveMaxPins    count      bab.rs:6849         garbage -> usize::MAX
    /// ```
    ///
    /// So for these seven, "set to garbage" and "unset" are the same
    /// configuration and a concurrent solve cannot tell them apart.
    ///
    /// # Why the other eleven are excluded
    ///
    /// `ScopedEnvVar::set` mutates the PROCESS environment, and the crate-wide
    /// `lock_env` does not make that private: `bab.rs` has 83 `#[test]`
    /// functions and 13 of them take the lock, so ~70 may be running a solve
    /// while this test holds it. Every excluded knob is read as *presence*, and
    /// every garbage string is present — so sweeping them would publish
    /// cuts-off, depth-first, probing-on or node-cuts-on for the microseconds
    /// each value is live, to a solve that never asked for any of it:
    ///
    /// ```text
    /// NoCuts        bab.rs:3990       tune::on           -> root cuts off
    /// NoSatStop     bab.rs:13029      tune::on           -> saturation stop off
    /// NoLattice     lattice.rs:647    tune::on           -> detector off
    /// NoBloomRelax  simplex.rs:1168   tune::on           -> bloom cap restored
    /// WarmLu        simplex.rs:1431   tune::on           -> LU in the warm pool
    /// Dfs           bab.rs:17366      var_os().is_some() -> depth-first
    /// RootProbe     bab.rs:8058       var_os().is_none() -> probing on
    /// NodeCuts      bab.rs:18644      var_os().is_some() -> node separation on
    /// GmiRounds     bab.rs:4174       var_os().is_none() -> shape override off
    /// ```
    ///
    /// (`Plunge` and `RootCutsPerRound` happen to survive garbage too, but they
    /// buy nothing here and would have to be re-justified whenever their call
    /// sites move.)
    ///
    /// Nothing is lost. No accessor branches on knob identity — `real(k, d)` is
    /// the same code for every `k` — so the STRINGS are covered end to end
    /// below, and every KNOB is covered by
    /// `malformed_settings_never_panic_through_the_caller_or_policy`, which
    /// touches no process state at all.
    const ENV_SWEEPABLE: [Knob; 7] = [
        Knob::SatStopSecs,
        Knob::SatStopMult,
        Knob::PresolveShare,
        Knob::FlipCapSecs,
        Knob::FlipShare,
        Knob::PumpRestarts,
        Knob::DiveMaxPins,
    ];

    /// NO INPUT MAY PANIC. A stray `AY_MILP_*` in a CI environment must not be
    /// able to take down an in-process consumer — the third consequence ny
    /// recorded against the environment surface. Note `-1` and `inf`: those are
    /// not hypothetical, they are the values that reached
    /// `Duration::from_secs_f64` and `Duration::mul_f64`, both of which panic.
    ///
    /// This is the END-TO-END arm: the string goes in through the process
    /// environment, exactly as an operator's does, and comes out of the same
    /// `Duration` constructors that used to abort. See [`ENV_SWEEPABLE`] for why
    /// it runs on seven knobs rather than eighteen.
    #[test]
    fn malformed_environment_values_never_panic() {
        let _lock = lock_env();
        for k in ENV_SWEEPABLE {
            for raw in GARBAGE {
                let _set = ScopedEnvVar::set(k.env(), raw);
                assert!(on(k), "{:?}={:?}: presence is presence", k, raw);
                let _ = on_strict(k);
                let _ = on_unless_zero(k);
                assert_eq!(num(k, 7), 7, "{:?}={:?}", k, raw);
                assert_eq!(count(k, 9), 9, "{:?}={:?}", k, raw);
                assert_eq!(real(k, 0.25), 0.25, "{:?}={:?}", k, raw);
                assert_eq!(count_opt(k), None, "{:?}={:?}", k, raw);
                assert_eq!(real_opt(k), None, "{:?}={:?}", k, raw);
                // The consumers, not just the accessors: these are the two
                // calls that used to abort the process.
                let _ = Duration::from_secs_f64(real(k, 15.0));
                let _ = Duration::from_secs(1).mul_f64(real(k, 1.5));
            }
            // `-1` is well-formed as an integer and malformed as a duration:
            // what rejects it is the accessor's DOMAIN, not the string's
            // syntax. It is listed separately because `num` legitimately
            // returns it.
            let _neg = ScopedEnvVar::set(k.env(), "-1");
            assert_eq!(num(k, 7), -1);
            assert_eq!(count(k, 9), 9);
            assert_eq!(real(k, 15.0), 15.0);
            assert_eq!(real_opt(k), None);
            let _ = Duration::from_secs_f64(real(k, 15.0));
            // ...and the mirror image: `1e26` is a fine `f64` and overflows
            // every integer accessor. Neither may panic, and neither may
            // borrow the other's verdict on the string.
            let _big = ScopedEnvVar::set(k.env(), "99999999999999999999999999");
            assert_eq!(num(k, 7), 7);
            assert_eq!(count(k, 9), 9);
            assert_eq!(
                real(k, 15.0),
                15.0,
                "1e26 is a fine f64 and a Duration overflow"
            );
            let _ = Duration::from_secs_f64(real(k, 15.0));
        }
    }

    /// The same property for EVERY knob and for the layers that carry a value
    /// from an embedding consumer rather than from a shell — and it publishes
    /// nothing, because the caller and policy layers are thread-local.
    ///
    /// Not a weaker restatement of the env sweep: the domain is enforced by two
    /// separate pieces of code that must both hold. The environment half filters
    /// in [`parse_real`]; the caller/policy half filters in
    /// [`Setting::as_real`], on a value that never was a string and so cannot be
    /// rejected by parsing. `ny` reaches the second one — an
    /// `EngineEconomics` built by a caller who ignored the builder's `Result`
    /// and a policy rule that computes a share from a shape are both `f64`s
    /// arriving with no syntax to be wrong.
    ///
    /// `1e26` and `MAX_REAL * 2.0` are the [`MAX_REAL`] ceiling from the
    /// `AY_MILP_SAT_STOP_SECS=1e26` abort; `-1.0` is the
    /// `AY_MILP_SAT_STOP_MULT=-1` abort. Both must be refused here as well, or
    /// the two aborts simply move from the environment to the typed API.
    #[test]
    fn malformed_settings_never_panic_through_the_caller_or_policy() {
        let _lock = lock_env();
        let _clean = unset_all_knobs();
        const OUT_OF_DOMAIN: [f64; 7] = [
            -1.0,
            -0.5,
            f64::NAN,
            f64::INFINITY,
            f64::NEG_INFINITY,
            1e26,
            MAX_REAL * 2.0,
        ];
        for k in Knob::ALL {
            for bad in OUT_OF_DOMAIN {
                {
                    let _caller = activate_caller(Profile::EMPTY.with(k, Setting::Real(bad)));
                    assert_eq!(real(k, 15.0), 15.0, "caller {:?}={}", k, bad);
                    assert_eq!(real_opt(k), None, "caller {:?}={}", k, bad);
                    let _ = Duration::from_secs_f64(real(k, 15.0));
                    let _ = Duration::from_secs(1).mul_f64(real(k, 1.5));
                }
                {
                    let _policy = activate_profile(Profile::EMPTY.with(k, Setting::Real(bad)));
                    assert_eq!(real(k, 15.0), 15.0, "policy {:?}={}", k, bad);
                    assert_eq!(real_opt(k), None, "policy {:?}={}", k, bad);
                    let _ = Duration::from_secs_f64(real(k, 15.0));
                    let _ = Duration::from_secs(1).mul_f64(real(k, 1.5));
                }
            }
            // A count is a budget, so a negative one is meaningless rather than
            // meaningfully zero, in this layer as in the environment.
            let _neg = activate_caller(Profile::EMPTY.with(k, Setting::Num(-1)));
            assert_eq!(
                count(k, 9),
                9,
                "{:?}: a negative count takes the default",
                k
            );
            assert_eq!(count_opt(k), None, "{:?}", k);
        }
    }

    /// The string half of the malformed-input property, for every knob, with no
    /// process state touched: [`parse_real`] is what the environment arm of
    /// [`real`]/[`real_opt`] resolves through, so a string it accepts is a
    /// string that reaches `Duration::from_secs_f64`.
    ///
    /// This exists because the end-to-end sweep above is restricted to the seven
    /// knobs it is safe to publish to. It is knob-independent by construction —
    /// which is also the argument that the restriction costs no coverage.
    #[test]
    fn no_malformed_string_survives_the_real_domain() {
        for raw in GARBAGE
            .iter()
            .copied()
            .chain(["-1", "99999999999999999999999999", "1e15.5"])
        {
            assert_eq!(parse_real(raw), None, "{:?} must not reach a Duration", raw);
        }
        // The good cases still get through, and the ceiling is inclusive.
        assert_eq!(parse_real("0"), Some(0.0));
        assert_eq!(parse_real("1.5"), Some(1.5));
        assert_eq!(parse_real("1e15"), Some(MAX_REAL));
        let _ = Duration::from_secs_f64(parse_real("1e15").expect("in domain"));
    }

    /// A LEADING SPACE STILL PARSE-FAILS, exactly as it did before this module
    /// existed. `AY_MILP_DIVE_MAX_PINS=" 5"` left the dive uncapped at the old
    /// call site (`bab.rs:6849` reads `usize::MAX`) and must still leave it
    /// uncapped, or the identical recipe measures a different arm than the
    /// journal recorded for it. See [`num`].
    #[test]
    fn a_padded_value_does_not_parse() {
        let _lock = lock_env();
        let _pins = ScopedEnvVar::set(Knob::DiveMaxPins.env(), " 5");
        assert_eq!(count(Knob::DiveMaxPins, usize::MAX), usize::MAX);
        let _pump = ScopedEnvVar::set(Knob::PumpRestarts.env(), "3 ");
        assert_eq!(count_opt(Knob::PumpRestarts), None);
        let _mult = ScopedEnvVar::set(Knob::SatStopMult.env(), " 2.5");
        assert_eq!(real(Knob::SatStopMult, 1.5), 1.5);
        assert_eq!(num(Knob::SatStopMult, 7), 7);
    }

    /// A well-formed value still reaches the call site unchanged — the
    /// malformed-input hardening above must not have swallowed the good cases.
    #[test]
    fn well_formed_environment_values_still_apply() {
        let _lock = lock_env();
        let _secs = ScopedEnvVar::set(Knob::SatStopSecs.env(), "30");
        let _mult = ScopedEnvVar::set(Knob::SatStopMult.env(), "2.5");
        let _share = ScopedEnvVar::set(Knob::FlipShare.env(), "0.25");
        let _pump = ScopedEnvVar::set(Knob::PumpRestarts.env(), "0");
        assert_eq!(real(Knob::SatStopSecs, 15.0), 30.0);
        assert_eq!(real(Knob::SatStopMult, 1.5), 2.5);
        assert_eq!(real_opt(Knob::FlipShare), Some(0.25));
        assert_eq!(count_opt(Knob::PumpRestarts), Some(0));
    }

    /// The snapshot is what the shipped build resolves from, so its capture is
    /// tested directly rather than through whichever variables the test binary
    /// happens to inherit.
    #[test]
    fn snapshot_captures_the_environment() {
        let _lock = lock_env();
        let k = Knob::PresolveShare;
        {
            let _set = ScopedEnvVar::set(k.env(), "0.02");
            let snap = EnvSnapshot::capture();
            assert_eq!(snap.get(k), Some(std::ffi::OsStr::new("0.02")));
            assert_eq!(
                snap.get(Knob::NoCuts),
                std::env::var_os(Knob::NoCuts.env()).as_deref()
            );
        }
        let _clean = ScopedEnvVar::unset(k.env());
        assert_eq!(
            EnvSnapshot::capture().get(k),
            None,
            "an unset variable is absent from the capture, not empty in it"
        );
    }

    #[test]
    fn knob_env_names_are_distinct() {
        let mut seen = std::collections::HashSet::new();
        for k in Knob::ALL {
            assert!(seen.insert(k.env()), "duplicate env name for {:?}", k);
            assert_eq!(Knob::ALL[k.slot()], k, "slot must round-trip");
        }
    }

    /// THE UNIFICATION PIN. This crate has two knob tables by design and they
    /// must never drift: [`crate::knobs::KNOBS`] is the LEDGER (every `AY_*`
    /// name, bucketed, powering `ay-milp knobs --list` and the typo guard), and
    /// [`Knob`] is the TYPED subset the engine resolves per solve.
    ///
    /// Two tables is the right factoring — one is a catalogue of every name that
    /// exists, the other is the handful with a typed setter — but only while
    /// every entry in the second appears in the first. A tuned knob missing from
    /// the ledger is invisible to `knobs --list` and, worse, would be reported by
    /// the unknown-name guard as a probable TYPO when an operator sets the very
    /// variable the engine reads.
    #[test]
    fn every_tuned_knob_is_in_the_ledger() {
        for k in Knob::ALL {
            assert!(
                crate::knobs::KNOBS.iter().any(|e| e.name == k.env()),
                "tune::Knob::{:?} reads {} but that name is absent from knobs.rs's ledger: \
                 `ay-milp knobs --list` would omit it and the unknown-name guard would call \
                 it a typo",
                k,
                k.env(),
            );
        }
    }
}
