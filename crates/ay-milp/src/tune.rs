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
//! again — so no accessor **in this module** touches `std::env` on the solve path.
//!
//! ⚠ THAT IS A STATEMENT ABOUT THIS MODULE, NOT ABOUT THE CRATE, and it was
//! previously written as though it were the latter. Measured: ay-milp holds **318
//! live `env::var` calls outside this layer**, plus 90 `OnceLock`-cached ones
//! (`bab::prime_env_all` forces the cached subset at solve entry; nothing can force
//! the live ones). Bringing those under this snapshot is the outstanding `Config`
//! migration, not a property the crate has today.
//!
//! An exported
//! variable behaves exactly as it always has; mutating one mid-process and
//! expecting a live solve to see it does not, which no shipped lane did.

use crate::model::{ColKind, Model};

mod knob;
pub(crate) use knob::Knob;

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
    pub(crate) fn overlay(mut self, other: &Profile) -> Self {
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
    #[cfg(test)]
    pub(crate) fn integrality_fraction(&self) -> f64 {
        if self.cols == 0 {
            return 0.0;
        }
        (self.binaries + self.general_ints) as f64 / self.cols as f64
    }

    /// Matrix density in `[0, 1]`.
    #[cfg(test)]
    pub(crate) fn density(&self) -> f64 {
        let cells = self.rows.saturating_mul(self.cols);
        if cells == 0 {
            return 0.0;
        }
        self.nnz as f64 / cells as f64
    }

    /// Every integral column is binary and there are no continuous columns.
    #[cfg(test)]
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
// Profiles are Copy snapshots; taking ownership prevents an active frame from
// observing later caller mutation and is cheaper than heap indirection here.
#[allow(clippy::large_types_passed_by_value)]
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
#[allow(clippy::large_types_passed_by_value)]
pub(crate) fn activate_caller(profile: Profile) -> Active {
    push(Frame {
        caller: caller_layer().overlay(&profile),
        policy: Profile::EMPTY,
    })
}

#[allow(clippy::large_types_passed_by_value)]
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

/// The CALLER layer's opinion about a flag knob, if it has one.
///
/// For a knob whose environment spelling is NOT plain presence (see
/// `bab::cert_decouple_enabled`, where `0`/`off` mean "keep the default"),
/// `on` would silently redefine what an operator's existing export means.
/// This exposes just the caller layer so such a site can take a typed value
/// first and otherwise fall through to its own established env parse.
pub(crate) fn caller_flag(k: Knob) -> Option<bool> {
    match caller_layer().get(k) {
        Some(Setting::Flag(b)) => Some(b),
        _ => None,
    }
}

fn caller(k: Knob) -> Option<Setting> {
    ACTIVE.with(|a| a.borrow().last().and_then(|f| f.caller.get(k)))
}

fn policy(k: Knob) -> Option<Setting> {
    ACTIVE.with(|a| a.borrow().last().and_then(|f| f.policy.get(k)))
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
/// `--dfs` reads as **on**, because presence is the whole test. That is
/// surprising, and it is what the call sites have always done
/// (`bab.rs:16538`); changing it here would silently flip behaviour for anyone
/// who has ever written `=0` expecting off. The inconsistency is real and
/// belongs on a list to fix deliberately, with a deprecation cycle — not as an
/// invisible side effect of moving the read into this module.
pub(crate) fn on(k: Knob) -> bool {
    if let Some(Setting::Flag(b)) = caller(k) {
        return b;
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
    matches!(policy(k), Some(Setting::Flag(true)))
}

/// On unless explicitly `"0"`, and on by default:
/// `env::var(K).map_or(true, |v| v != "0")`.
#[cfg_attr(not(test), allow(dead_code))]
pub(crate) fn on_unless_zero(k: Knob) -> bool {
    if let Some(Setting::Flag(b)) = caller(k) {
        return b;
    }
    match policy(k) {
        Some(Setting::Flag(b)) => b,
        _ => true,
    }
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
/// `--gmi-rounds=garbage` yields `DEFAULT`. Routing garbage to the policy
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
/// `--dive-max-pins` parse-failed and left the dive uncapped at
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
    policy(k).and_then(Setting::as_num).unwrap_or(default)
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
    policy(k).and_then(Setting::as_count).unwrap_or(default)
}

/// A count whose *absence* is meaningful, for the call sites that spell the
/// read `env::var(K).ok().and_then(|v| v.parse().ok())` and then branch on the
/// `Option` (`--pump-restarts`, `bab.rs:18873`).
///
/// An unparseable explicit value is `None`, exactly as `.ok().and_then(..)`
/// made it — and, following [`num`], it does not fall through to the policy.
pub(crate) fn count_opt(k: Knob) -> Option<usize> {
    if let Some(n) = caller(k).and_then(Setting::as_count) {
        return Some(n);
    }
    policy(k).and_then(Setting::as_count)
}

/// A finite, non-negative real: a share, a multiplier, or a seconds value.
///
/// # Why the domain is part of the accessor
///
/// Every consumer of these knobs feeds the value to `Duration::from_secs_f64`
/// or `Duration::mul_f64`, **both of which panic** on a negative or non-finite
/// input. So `--sat-stop-mult=-1` was an abort, in-process, inside a
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
    policy(k).and_then(Setting::as_real).unwrap_or(default)
}

/// [`real`] where absence is meaningful.
///
/// `--flip-share` is the case: setting it at all *also* opts out of the
/// absolute flip-LNS cap (`bab.rs:19265`), so "set to the same value as the
/// default" and "unset" are different instructions and cannot share a
/// signature.
pub(crate) fn real_opt(k: Knob) -> Option<f64> {
    if let Some(v) = caller(k).and_then(Setting::as_real) {
        return Some(v);
    }
    policy(k).and_then(Setting::as_real)
}

/// The environment half of [`real`]/[`real_opt`]: parse the raw value exactly
/// as `finite_nonnegative_setting` (`bab.rs:3961`) did, then apply the domain.
/// Not trimmed, for the reason [`num`] gives.

/// The admissible domain for every [`Setting::Real`], shared by the accessors
/// and by [`crate::EngineEconomics`]'s builders so one number defines it.
///
/// The upper bound is not decoration. `Duration::from_secs_f64` panics above
/// `u64::MAX` seconds, so `--sat-stop-secs=1e26` — a perfectly
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
    use ay_test_support::env::lock_env;
    use std::time::Duration;

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

    /// A `usize` default above `i64::MAX` must not wrap into a negative and
    /// come back as garbage.
    #[test]
    fn count_saturates_instead_of_wrapping() {
        let k = Knob::RootCutsPerRound;
        assert_eq!(count(k, usize::MAX), usize::MAX);
        let _g = activate_profile(Profile::EMPTY.with(k, Setting::Num(-3)));
        assert_eq!(count(k, 5), 5, "a negative count takes the default");
    }

    /// `DiveMaxPins` defaults to `usize::MAX` and a caller may legitimately set
    /// it there; `Setting::Count` is what lets that round-trip, where the
    /// `i64`-widthed `Num` would return `i64::MAX`.
    #[test]
    fn a_caller_count_round_trips_at_full_usize_width() {
        let k = Knob::DiveMaxPins;
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
        let k = Knob::GmiRounds;
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
        assert_eq!(num(Knob::GmiRounds, 2), 2);
        assert!(!on(Knob::RootProbe));
    }

    /// The selection entry point is wired for a policy that does not exist yet;
    /// exercising it keeps the `Shape`-to-`Policy` path compiling and honest.
    #[test]
    fn activating_for_a_model_selects_nothing_today() {
        let _lock = lock_env();
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
    fn the_caller_layer_outranks_the_policy() {
        let k = Knob::NoCuts;
        let p = activate_profile(Profile::EMPTY.with(k, Setting::Flag(true)));
        assert!(on(k), "the policy alone still turns the knob on");

        let g = activate_caller(Profile::EMPTY.with(k, Setting::Flag(false)));
        assert!(!on(k), "the caller's setting outranks the policy");
        drop(g);
        assert!(on(k), "and stops applying when the solve ends");
        drop(p);

        let share = Knob::PresolveShare;
        let _g = activate_caller(Profile::EMPTY.with(share, Setting::Real(0.02)));
        assert_eq!(real(share, 0.3), 0.02, "a typed real wins over the default");
    }

    /// Two concurrent solves configured differently must not see each other's
    /// settings. This is the whole point of the exercise: the environment
    /// cannot express it at all, because there is one environment per process.
    #[test]
    fn two_concurrent_solves_do_not_interfere() {
        let _lock = lock_env();
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
    /// `--sat-stop-secs=1e26` abort; `-1.0` is the
    /// `--sat-stop-mult=-1` abort. Both must be refused here as well, or
    /// the two aborts simply move from the environment to the typed API.
    #[test]
    fn malformed_settings_never_panic_through_the_caller_or_policy() {
        let _lock = lock_env();
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

    #[test]
    fn knob_env_names_are_distinct() {
        let mut seen = std::collections::HashSet::new();
        for k in Knob::ALL {
            if let Some(name) = k.env() {
                assert!(seen.insert(name), "duplicate env name for {:?}", k);
            }
            assert_eq!(Knob::ALL[k.slot()], k, "slot must round-trip");
        }
    }

    /// THE PROPERTY THE REDUCTION KNOBS EXIST FOR: a typed caller value beats an
    /// inherited `AY_MILP_*` export, in BOTH directions.
    ///
    /// Three of these gate transformations that change the model a verdict is
    /// proved against. A consumer whose policy forbids exporting `AY_MILP_*`
    /// (ny) previously had no way to quarantine one; the point of the typed
    /// carrier is that its answer is not merely consulted but authoritative.
    /// Asserting only "caller can turn it on" would pass even if the environment
    /// silently won whenever it disagreed, so both directions are pinned.
    #[test]
    fn a_typed_reduction_setting_is_authoritative() {
        for k in [
            Knob::NoDualfix,
            Knob::NoKernelReform,
            Knob::NoFeasConflict,
            Knob::NoColdLu,
        ] {
            {
                let _caller = activate_caller(Profile::EMPTY.with(k, Setting::Flag(true)));
                assert!(on(k), "{}: a typed `true` engages the switch", k.label());
            }
            {
                let _caller = activate_caller(Profile::EMPTY.with(k, Setting::Flag(false)));
                assert!(!on(k), "{}: a typed `false` disengages it", k.label());
            }
            assert!(
                !on(k),
                "{}: no opinion resolves to the compiled default",
                k.label()
            );
        }
    }

    /// The same property for the knob deliberately NOT routed through `on`.
    ///
    /// `certificate_decoupling`'s historical env spelling was not plain
    /// presence, so its site takes the caller layer and otherwise falls
    /// through to the compiled default (B29: the env parse is retired).
    #[test]
    fn cert_decouple_takes_the_caller_layer() {
        let k = Knob::NoCertDecouple;
        {
            let _caller = activate_caller(Profile::EMPTY.with(k, Setting::Flag(false)));
            assert_eq!(caller_flag(k), Some(false));
        }
        assert_eq!(
            caller_flag(k),
            None,
            "with no caller opinion the site must fall through to its compiled default"
        );
    }
}

/// Force [`EnvSnapshot`]'s one-shot capture to happen NOW.
///
/// The snapshot is `OnceLock`-backed and captured on FIRST USE, which without this
/// is wherever the solve path first resolves a knob through this layer — the second
/// of the two cached holes left by `bab::prime_env_all`. Priming it alongside the
/// rest puts every environment read in the crate's cached set at one point the
/// caller controls.
///
/// # Genuinely a no-op under `cfg(test)`
///
/// [`env_layer`] forks on `cfg(test)` and reads LIVE there, deliberately, so the
/// crate's own `ScopedEnvVar` kill-switch coverage keeps working. An earlier
/// version of this function said it was a no-op in test builds and then called
/// `env_layer` anyway — 18 live `var_os` calls that stored nothing. Harmless, and
/// the doc was still false; a review caught it. The `cfg` split below makes the
/// sentence true rather than merely nearly-true.
/// B38: the env snapshot layer is gone; priming is a no-op kept so the
/// `bab::prime_env_all` choke point keeps one shape while its other cached
/// holes retire.
pub(crate) fn prime_env() {}
