//! SEPARATION-WORK CENSUS — measurement scaffolding for the cut-separation front.
//!
//! Every counter here is load-invariant (counts, not wall) except the two `*_NS` timers, which
//! are reported only as a secondary signal. The census proper is behind `--sepstat`; with
//! the env var unset the only cost is one relaxed load of a `OnceLock<bool>` per bump site, and
//! the bump sites sit outside the exact-rational inner loops that matter.
//!
//! The FORGONE-COST counters below are the exception and are deliberately always on — see their
//! own notes. Scaffolding answers a question you already have; those counters answer one you do
//! not.
//!
//! Motivation: the campaign brief attributed 6.01s of mas74's wall to cut families that derive
//! ZERO cuts, and named `strongcg_round` / `mir_round` as the kernels. "Derives nothing" is not
//! the same claim as "costs nothing to find that out" — a kernel that bails on its first
//! fractionality test is already free. These counters separate the two: they record how far
//! into each rounding pass the derivation got before it gave up.

use std::sync::{
    atomic::{AtomicBool, AtomicU64, Ordering},
    Arc,
};

macro_rules! counters {
    ($($name:ident),* $(,)?) => {
        $(pub static $name: AtomicU64 = AtomicU64::new(0);)*
    };
}

counters! {
    // Row-level: how many (row, orientation) derivations each family entered.
    MIR_ROWS, SCG_ROWS,
    // `mir_build_subs` calls, and the ones that produced no substituted row at all.
    SUBS_BUILT, SUBS_NONE,
    // Exact `terms` vectors built by the family row loop.
    TERMS_BUILT,
    // Rounding kernel passes and their exit points. `late_none` is derived
    // (`passes - early - some`): it is the count that matters, because a pass that reaches the
    // end and is rejected there has paid the whole exact-rational bill.
    MIR_PASS, MIR_EARLY, MIR_SOME,
    SCG_PASS, SCG_EARLY, SCG_SOME,
    // `strongcg_round` bailing in the continuous-projection prologue (before any per-column
    // exact-rational work at all).
    SCG_RANGE_NONE,
    // Cuts the two families actually returned to the caller.
    MIR_CUTS, SCG_CUTS,
    // Delta lists built, and total delta entries across them.
    DELTA_LISTS, DELTA_ENTRIES,
    // Of the derived cuts: how many were violated at all (efficacy > 0), and how many rows
    // ended up returning a cut past the MIN_VIOLATION floor.
    CAND_POS, CAND_NONPOS, ROW_RET,
    // Late `None` exits of the rounding kernels, by reason.
    LATE_EMPTY, LATE_NONFINITE, LATE_ABSURD,
    // Screen accounting (see `ScreenRow`).
    SCREEN_TRIED, SCREEN_SKIP, SCREEN_BUILD_FAIL, SCREEN_ROW_KILL, SCREEN_UNKNOWN,
    // Audit mode (`--sep-screen-audit`): screen claims checked against the exact kernel.
    AUDIT_OK, AUDIT_FAIL,
}

pub static SEP_NS: AtomicU64 = AtomicU64::new(0);

// ------------------------------------------------------- FORGONE COST
//
// Everything above is gated on `--sepstat` and answers "how far did the
// derivation get". The two counters below are ALWAYS ON and answer a different
// question, about the branch a gate did NOT take.
//
// # The defect class
//
// the development design notes names it: a gate is
// added for a real measured reason, its condition proxies the cost it is avoiding,
// and the proxy silently mis-serves a workload nobody measured. Found four times in
// EUF, four more times in this crate, and one of the EUF instances was costing a
// CORRECT ANSWER rather than time.
//
// Fire rate cannot detect it. `1c1ce672c` measured four separator families all at
// fire rate ZERO and reached four DIFFERENT verdicts: clique correctly silent (93
// of 154 instances have no qualifying rows), mixing correctly off, odd-cycle
// WRONGLY gated and worth a verdict, zero-half inverted but net-negative to
// broaden. What separates them is the SIGN OF THE DELTA, which a fire rate does
// not carry.
//
// # What is measured instead
//
// The cost the gate asserts is negligible, accumulated on the branch it forces.
// Here that is a cut this crate built EXACTLY and then threw away: at the
// `coef_to_f64` refusal in `cuts.rs` the exact `cx`/`rhs` pair is fully
// constructed, so its violation at the current point is already paid for and
// recording it is free. A discarded cut that was violated is capability the model
// had and did not get; a discarded cut that was satisfied cost nothing.
//
// Counts only, so the line reproduces on a contended box. `DISCARDED_VIOLATED` is
// the decision statistic; `DISCARDED` alone is the fire rate and is not.
pub static DISCARDED: AtomicU64 = AtomicU64::new(0);
pub static DISCARDED_VIOLATED: AtomicU64 = AtomicU64::new(0);

/// Charge a fully-derived cut that a downstream gate refused.
///
/// `violated` is whether the exact cut cut off the point it was separating — i.e.
/// whether the refusal cost the search anything at all.
#[inline]
pub fn discarded(violated: bool) {
    DISCARDED.fetch_add(1, Ordering::Relaxed);
    if violated {
        DISCARDED_VIOLATED.fetch_add(1, Ordering::Relaxed);
    }
}

// ------------------------------------------------------- GMI CUT IDENTITY
//
// A running digest of every GMI cut this process separated, in the order it
// separated them. Always on, for the same reason the forgone counters are: it
// answers a question you do not know you have until a representation change
// claims to be one.
//
// The claim it exists to police is `SparseExactLu`'s — "same cuts, less memory".
// Root closure, bound and node count are all TOO COARSE to police it: a cut that
// moved by one ulp can leave closure identical to six decimals and still be a
// different cut, and a cut LOST can be invisible behind a bound that another
// family recovers. Two runs that agree here agree on every coefficient bit, every
// right-hand side bit, and the order the rows were produced in.
//
// ORDER-SENSITIVE, hence one-thread-only as evidence: `--threads 1` (the default,
// and the only setting the determinism contract covers) produces the cuts in a
// fixed sequence, and the chain records that. Under worker threads the value is
// still a legitimate function of what was separated, but two runs need not agree
// and a mismatch means nothing.
pub static GMI_CUTS: AtomicU64 = AtomicU64::new(0);
pub static GMI_DIGEST: AtomicU64 = AtomicU64::new(0);

/// Mix one separated GMI cut into the process digest.
///
/// The `f64` BITS go in, not the value: `-0.0` and `0.0` are different stores and
/// a digest that cannot tell them apart cannot police a rounding change either.
///
/// Under `the gmi-cut-trace knob` (or the general `--trace`) each cut also
/// prints its OWN hash. The run digest is a chain, so it answers "did these two
/// runs separate the same cuts" and nothing else — and two arms that stop at
/// different points disagree for a reason that is not a disagreement about any
/// cut. That is not hypothetical: on `bg512142` the dense arm separated 4 cuts to
/// the sparse arm's 8, and the 4 were hash-for-hash the first 4 — it ran out of
/// round budget paying for the `m²` assembly the sparse path does not build. The
/// per-cut line makes the honest comparison possible: PREFIX-compare, and name
/// the first index that actually differs. It gets its own switch rather than
/// riding on `--trace` because the general trace's VOLUME is itself a cost
/// that perturbs which arm runs out of budget first, which is the exact
/// confounder this line exists to remove.
pub fn gmi_cut(lb: f64, coeffs: impl Iterator<Item = (u32, f64)>) {
    const FNV_PRIME: u64 = 0x100_0000_01b3;
    const FNV_OFFSET: u64 = 0xcbf2_9ce4_8422_2325;
    let mut one = FNV_OFFSET;
    let mix = |h: &mut u64, w: u64| {
        for b in w.to_le_bytes() {
            *h ^= b as u64;
            *h = h.wrapping_mul(FNV_PRIME);
        }
    };
    mix(&mut one, lb.to_bits());
    let mut nz = 0usize;
    for (c, v) in coeffs {
        mix(&mut one, c as u64);
        mix(&mut one, v.to_bits());
        nz += 1;
    }
    let mut run = GMI_DIGEST.load(Ordering::Relaxed);
    mix(&mut run, one);
    GMI_DIGEST.store(run, Ordering::Relaxed);
    let i = GMI_CUTS.fetch_add(1, Ordering::Relaxed);
    static TRACE: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    if *TRACE.get_or_init(|| {
        crate::tune::caller_flag(crate::tune::Knob::GmiCutTrace) == Some(true)
            || crate::debug_flags::milp_debug_flags().trace
    }) {
        eprintln!("GMICUT i={i} h={one:016x} nz={nz} lb={lb:.17e}");
    }
}

/// FT-ADOPTION EXCLUSIONS: top-level native MILP solves that actually reached
/// the adoption ceiling, and the LP row count at their first excluded
/// refactorization.
///
/// Separate from the cut pair above because it is a different gate with a different
/// unit. `EXCLUDED` is one per outermost [`crate::BabSession::check`] frame,
/// not one per nested check, simplex refactorization or node LP.
/// `EXCLUDED_ROWS` sums the first excluded LP's row count once for each such
/// solve.
pub static ADOPTION_EXCLUDED: AtomicU64 = AtomicU64::new(0);
pub static ADOPTION_EXCLUDED_ROWS: AtomicU64 = AtomicU64::new(0);

/// One top-level native MILP solve's FT-adoption exclusion latch.
///
/// The outermost `BabSession::check` creates this latch and owns its lifetime.
/// A nested check (notably margin reframe) borrows the inherited latch rather
/// than replacing it. Every derived/cloned float LP shares this `Arc`,
/// including worker clones; rebuilt sub-MIPs copy it onto both their model and
/// solve options. `Simplex::refactorize` may reach the exclusion branch many
/// times, but only the first successful compare-exchange charges the process
/// census.
#[derive(Debug, Clone, Default)]
pub(crate) struct FtAdoptionSolveLatch {
    charged: Arc<AtomicBool>,
}

impl FtAdoptionSolveLatch {
    #[must_use]
    pub(crate) fn new() -> Self {
        Self::default()
    }

    /// Whether two carriers refer to the same top-level solve frame.
    #[must_use]
    pub(crate) fn same_frame(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.charged, &other.charged)
    }

    /// Charge this solve once, carrying the first excluded LP's `rows`.
    ///
    /// Returns `true` only for the refactorization that performed the charge.
    #[inline]
    pub(crate) fn charge(&self, rows: u64) -> bool {
        if self.charged.load(Ordering::Relaxed)
            || self
                .charged
                .compare_exchange(false, true, Ordering::Relaxed, Ordering::Relaxed)
                .is_err()
        {
            return false;
        }
        ADOPTION_EXCLUDED.fetch_add(1, Ordering::Relaxed);
        ADOPTION_EXCLUDED_ROWS.fetch_add(rows, Ordering::Relaxed);
        true
    }
}

/// Serialize tests that assert deltas of the process-global census.
#[cfg(test)]
pub(crate) fn adoption_test_guard() -> std::sync::MutexGuard<'static, ()> {
    static GUARD: std::sync::OnceLock<std::sync::Mutex<()>> = std::sync::OnceLock::new();
    GUARD
        .get_or_init(|| std::sync::Mutex::new(()))
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

/// `(excluded top-level solves, first-excluded LP rows)` since process start.
#[must_use]
pub fn adoption_forgone() -> (u64, u64) {
    (
        ADOPTION_EXCLUDED.load(Ordering::Relaxed),
        ADOPTION_EXCLUDED_ROWS.load(Ordering::Relaxed),
    )
}

#[cfg(test)]
mod adoption_latch_tests {
    use super::*;

    #[test]
    fn concurrent_distinct_rows_have_one_winner_and_charge_its_rows() {
        let _guard = adoption_test_guard();
        let latch = FtAdoptionSolveLatch::new();
        let rows = [11_u64, 23, 47, 89];
        let barrier = Arc::new(std::sync::Barrier::new(rows.len()));
        let before = adoption_forgone();

        let results = std::thread::scope(|scope| {
            let handles: Vec<_> = rows
                .into_iter()
                .map(|row| {
                    let latch = latch.clone();
                    let barrier = Arc::clone(&barrier);
                    scope.spawn(move || {
                        barrier.wait();
                        (row, latch.charge(row))
                    })
                })
                .collect();
            handles
                .into_iter()
                .map(|handle| handle.join().expect("census worker did not panic"))
                .collect::<Vec<_>>()
        });
        let winners: Vec<_> = results
            .iter()
            .filter_map(|&(rows, won)| won.then_some(rows))
            .collect();
        let after = adoption_forgone();

        assert_eq!(winners.len(), 1, "exactly one worker must win the latch");
        assert_eq!(after.0 - before.0, 1);
        assert_eq!(
            after.1 - before.1,
            winners[0],
            "the census must retain the winning first-exclusion row count"
        );
    }
}

/// `(refused, of which were violated)` since process start.
#[must_use]
pub fn forgone() -> (u64, u64) {
    (
        DISCARDED.load(Ordering::Relaxed),
        DISCARDED_VIOLATED.load(Ordering::Relaxed),
    )
}

pub fn on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| crate::tune::caller_flag(crate::tune::Knob::Sepstat) == Some(true))
}

#[inline]
pub fn bump(c: &AtomicU64) {
    if on() {
        c.fetch_add(1, Ordering::Relaxed);
    }
}

#[inline]
pub fn add(c: &AtomicU64, n: u64) {
    if on() {
        c.fetch_add(n, Ordering::Relaxed);
    }
}

fn g(c: &AtomicU64) -> u64 {
    c.load(Ordering::Relaxed)
}

// ------------------------------------------------- GATE CENSUS (18 audited gates)
//
// The mechanism is `ay_core::forgone`, reimplemented here because ay-milp does not
// depend on ay-core (see Cargo.toml). Same contract: charge on the branch the gate
// FORCES, in the units the gate's own doc comment claims are negligible. Hits alone
// are a fire rate and rank nothing (`1c1ce672c`); the COST column is the statistic.
//
// A site that never fires is omitted rather than reported clean — but a zero here is
// still an answer, because several of these gates have no env override at all and a
// zero is the first evidence their excluded population is empty.
pub struct GateSite {
    /// The gate constant and the file it lives in.
    pub gate: &'static str,
    /// What the cost counts.
    pub unit: &'static str,
}

pub const GATE_SITES: &[GateSite] = &[
    GateSite {
        gate: "has_inexact_coeffs fail-close (presolve.rs)",
        unit: "open column bound sides on a model presolve refused wholesale",
    },
    GateSite {
        gate: "ODD_CYCLE_MAX_LEN (cuts.rs)",
        unit: "micro-units of scale-free depth of a valid odd hole refused for length",
    },
    GateSite {
        gate: "NOGOOD_MAX_LEN (bab.rs, pure-binary tier)",
        unit: "fixings PAST the cap in a proven-empty box whose refutation was discarded",
    },
    GateSite {
        gate: "MAX_FLIP_LNS_BINS (bab.rs)",
        unit: "binary switches on a fixed-charge model refused for switch count",
    },
    GateSite {
        gate: "REFACTOR_TALL_ROWS verify/cadence ceiling (simplex.rs)",
        unit: "rows of a tall LU basis rebuilt at d = 0 because the 20-trigger stayed",
    },
    GateSite {
        gate: "cutoff-closure cascade continuous-side gate (bab.rs)",
        unit: "columns pinned by reduced-cost fixing whose row implications never cascaded",
    },
    GateSite {
        gate: "`!gub_on` term in the strong-branch seeding entry (bab.rs)",
        unit: "branch candidates ranked by unseeded pseudocosts at a node GUB declined",
    },
    GateSite {
        gate: "GUB_MIN_ROWS (bab.rs)",
        unit: "dominant set-partition rows below the arming floor",
    },
    GateSite {
        gate: "gub_supports disarmed by sym.is_some() (bab.rs)",
        unit: "branchable set-partition supports a symmetric model was never offered",
    },
    GateSite {
        gate: "MAX_CUT_NNZ_LOCAL, aggregated flow cover (cuts.rs)",
        unit: "exact flow covers refused on nnz that would have BEEN the returned cut",
    },
    GateSite {
        gate: "KERNEL_MAX_ROWS, AHL |E| cap (lattice.rs)",
        unit: "all-integral-support equality rows above the fold ceiling, |C| fitting",
    },
    GateSite {
        gate: "MAX_ROWS, lattice front door (lattice.rs)",
        unit: "model rows above the row ceiling on a column-tight model",
    },
    GateSite {
        gate: "MAX_COLS, lattice front door (lattice.rs)",
        unit: "model columns above the column ceiling on a row-tight model",
    },
    GateSite {
        gate: "impl_class orbitope requirement (bab.rs)",
        unit: "implication-source binaries a mixed lever-default model never mined",
    },
    GateSite {
        gate: "MAX_CLIQUE_ROW_SUPPORT (cuts.rs)",
        unit: "dropped row-side columns that PROVABLY carried a conflict edge",
    },
    GateSite {
        gate: "mode.cheap skips root presolve (bab.rs)",
        unit: "open column bound sides carried into a cheap sub-solve un-re-propagated",
    },
    GateSite {
        gate: "bump_lu_min PFI floor (simplex.rs)",
        unit: "eta entries the product-form bump segment actually produced",
    },
    GateSite {
        gate: "gub_sb_on(lp.wide_tall()) (bab.rs)",
        unit: "columns of a GUB split branched with no probed child bound",
    },
    GateSite {
        gate: "MAX_COLS post-compile slack append (lattice.rs)",
        unit: "lattice columns of a fully compiled market split refused for width",
    },
    // ------------------------------------------------- ROOT-CUT POST-FILTERS (cause 6)
    //
    // the development design notes lists six causes
    // for ay's 7.02%-vs-54.69% root-closure gap and attributes the SIXTH, on 6 of 65
    // zero-cut instances, to "valid cuts generated and then killed entirely by
    // post-filters -- the absolute nnz cap and the efficacy floor". That attribution
    // was made by reading the code, not by counting, and the four sites below are the
    // count. Each is charged on the branch the filter FORCES, with a cost in the unit
    // the filter's own doc comment claims is negligible.
    //
    // The `MIN_VIOLATION` cost is deliberately NOT the refused violation. Raw violation
    // is scale-DEPENDENT (multiply a cut through by ten and its violation multiplies by
    // ten while the inequality says exactly the same thing), and the root pool does not
    // rank on it -- it ranks on scale-free DEPTH and applies its own floor there
    // (`cut_eff_floor`, 1e-3 or 6e-3 by shape). So the decision statistic is not "how
    // many cuts did 1e-4 refuse" but "how many of them would have survived the floor
    // that actually governs the pool", and that is what the cost counts.
    GateSite {
        gate: "MIN_VIOLATION raw-violation floor (cuts.rs)",
        unit: "refused violated cuts that would ALSO have cleared the pool's DEPTH floor",
    },
    GateSite {
        gate: "ZH_MAX_NNZ (cuts.rs)",
        unit: "nonzeros of an exact violated zero-half row refused for width",
    },
    GateSite {
        gate: "MAX_CUT_NNZ_LOCAL, single-row flow cover (cuts.rs)",
        unit: "nonzeros of an exact violated flow cover refused for width",
    },
    GateSite {
        gate: "MAX_CUT_NNZ pool cap (bab.rs)",
        unit: "nonzeros of a cleaned, snapped, violated cut refused at pool admission",
    },
    GateSite {
        gate: "MIR_AGG_MAX_NNZ aggregate-growth stop (cuts.rs)",
        unit: "further aggregation STEPS forgone (this one refuses no built cut)",
    },
];

pub const GATE_PRESOLVE_INEXACT: usize = 0;
pub const GATE_ODD_CYCLE_LEN: usize = 1;
pub const GATE_NOGOOD_MAX_LEN: usize = 2;
pub const GATE_FLIP_LNS_BINS: usize = 3;
pub const GATE_LU_VERIFY_CEILING: usize = 4;
pub const GATE_CUTOFF_CLOSURE: usize = 5;
pub const GATE_SB_SEED_GUB: usize = 6;
pub const GATE_GUB_MIN_ROWS: usize = 7;
pub const GATE_GUB_SYM_DISARM: usize = 8;
pub const GATE_FLOWCOVER_AGG_NNZ: usize = 9;
pub const GATE_KERNEL_MAX_ROWS: usize = 10;
pub const GATE_LATTICE_FRONT_ROWS: usize = 11;
pub const GATE_LATTICE_FRONT_COLS: usize = 12;
pub const GATE_IMPL_ORBITOPE: usize = 13;
pub const GATE_CLIQUE_ROW_SUPPORT: usize = 14;
pub const GATE_CHEAP_PRESOLVE: usize = 15;
pub const GATE_BUMP_LU_FLOOR: usize = 16;
pub const GATE_GUB_SB_UNARMED: usize = 17;
pub const GATE_LATTICE_POST_COLS: usize = 18;
pub const GATE_CUT_MIN_VIOLATION: usize = 19;
pub const GATE_ZH_NNZ: usize = 20;
pub const GATE_FLOWCOVER_NNZ: usize = 21;
pub const GATE_POOL_CUT_NNZ: usize = 22;
pub const GATE_MIR_AGG_NNZ: usize = 23;

const NGATES: usize = 24;

static GATE_COSTS: [AtomicU64; NGATES] = [const { AtomicU64::new(0) }; NGATES];
static GATE_HITS: [AtomicU64; NGATES] = [const { AtomicU64::new(0) }; NGATES];

/// Distinct top-level solves that charged each gate at least once.
///
/// # Why a census number without a population is uninterpretable
///
/// The `REFACTOR_TALL_ROWS` row read `cost=5,161,317 hits=473` over an 18-instance
/// sweep, and was triaged on the strength of "473 hits over 18 instances". It
/// decomposes exactly as `468 × 10,914 + 5 × 10,713`: **468 of the 473 rebuilds
/// were ONE LP.** n was 2, not 18, and nothing in the output said so — the gate was
/// promoted on a phrase the instrument could not have supported.
///
/// `hits` counts events and `cost` sums a magnitude; neither distinguishes "a
/// broad effect" from "one pathological instance". This does, at one bit per gate
/// per solve.
static GATE_SOLVES: [AtomicU64; NGATES] = [const { AtomicU64::new(0) }; NGATES];

thread_local! {
    /// Which gates this top-level solve has already counted. Cleared by
    /// [`begin_solve`]; a sub-MIP inherits the parent's marks, so one model solve
    /// contributes one to each gate it touches however deep the re-entry goes.
    static GATE_SEEN: std::cell::RefCell<[bool; NGATES]> =
        const { std::cell::RefCell::new([false; NGATES]) };
}

/// Start a top-level solve's gate population accounting. Called from
/// `bab::prime_env_all`, which already runs once per top-level solve.
pub(crate) fn begin_solve() {
    GATE_SEEN.with(|s| *s.borrow_mut() = [false; NGATES]);
}

/// Charge `cost` to `site`'s forced branch. Call on the NOT-TAKEN side of the gate.
#[inline]
pub fn gate_charge(site: usize, cost: u64) {
    if let (Some(c), Some(h)) = (GATE_COSTS.get(site), GATE_HITS.get(site)) {
        c.fetch_add(cost, Ordering::Relaxed);
        h.fetch_add(1, Ordering::Relaxed);
        let first = GATE_SEEN.with(|s| {
            let mut s = s.borrow_mut();
            match s.get_mut(site) {
                Some(seen) if !*seen => {
                    *seen = true;
                    true
                }
                _ => false,
            }
        });
        if first {
            if let Some(n) = GATE_SOLVES.get(site) {
                n.fetch_add(1, Ordering::Relaxed);
            }
        }
    }
}

/// `(hits, summed cost)` for `site`.
#[must_use]
pub fn gate_read(site: usize) -> (u64, u64) {
    match (GATE_HITS.get(site), GATE_COSTS.get(site)) {
        (Some(h), Some(c)) => (h.load(Ordering::Relaxed), c.load(Ordering::Relaxed)),
        _ => (0, 0),
    }
}

/// Every gate with a non-zero charge, as `(site, hits, cost)`.
#[must_use]
pub fn gate_report() -> Vec<(&'static GateSite, u64, u64, u64)> {
    GATE_SITES
        .iter()
        .enumerate()
        .filter_map(|(i, s)| {
            let (hits, cost) = gate_read(i);
            let solves = GATE_SOLVES.get(i).map_or(0, |n| n.load(Ordering::Relaxed));
            (hits > 0).then_some((s, hits, cost, solves))
        })
        .collect()
}

#[cfg(test)]
mod gate_census_tests {
    use super::*;

    #[test]
    fn every_gate_has_an_index_and_a_unit() {
        assert_eq!(
            GATE_SITES.len(),
            NGATES,
            "GATE_SITES and the arrays must agree"
        );
        for s in GATE_SITES {
            assert!(!s.gate.is_empty() && !s.unit.is_empty());
        }
    }
}

pub fn dump() {
    // FORGONE COST IS NOT GATED. The counters above answer "how far did the
    // derivation get" and are scaffolding; this one answers "what did a gate throw
    // away", which is the question the size-gate antipattern is invisible to. A
    // number that only appears when someone already suspects a problem cannot
    // report a problem nobody suspects, and every instance of that defect in this
    // repo was found by suspicion rather than by instrumentation.
    let (refused, violated) = forgone();
    if refused > 0 {
        eprintln!(
            // NOT `AY_`-prefixed, deliberately. In this crate an `AY_*` token means a
            // KNOB, and `tests/env_ledger.rs` enforces that by scanning source for the
            // prefix -- it caught this line the moment it was written. There is no
            // switch here (the counters are always on), so a knob-shaped label would
            // be exactly the confusion the ledger exists to prevent. Same defect as
            // AY_ALLOCSTAT / AY_SEPSTAT, which were output labels the ledger carried
            // as live knobs until P0.4 derived the read counts and found them dead.
            "FORGONE cuts              refused={refused} of_which_violated={violated}  \
             (exactly derived, then discarded by the f64 coefficient refusal)"
        );
    }
    // GMI CUT IDENTITY. Printed whenever GMI separated anything, so an A/B that
    // claims "same cuts" has a line to compare instead of an assertion to trust.
    let gmi = GMI_CUTS.load(Ordering::Relaxed);
    if gmi > 0 {
        eprintln!(
            "GMICUTS n={gmi} digest={:016x}  \
             (FNV-1a over every coefficient/rhs bit, in separation order; 1 thread)",
            GMI_DIGEST.load(Ordering::Relaxed)
        );
    }
    let (adopt, adopt_rows) = adoption_forgone();
    if adopt > 0 {
        eprintln!(
            "FORGONE ft-adoption       excluded_solves={adopt} first_excluded_rows={adopt_rows}  \
             (above the adopt-ft-max-rows knob)",
        );
    }
    // THE GATE CENSUS. Also outside the `on()` guard, for the reason above: these
    // rank gates nobody has measured, and a ranking that only appears once somebody
    // suspects a particular gate cannot rank the ones nobody suspects.
    //
    // COST is the statistic, hits is not. `1c1ce672c` measured four separator
    // families at fire rate ZERO and reached four DIFFERENT verdicts, so a count of
    // firings orders nothing; the cost carries the size of what was refused. Sites
    // that never fired are omitted rather than printed as clean -- but note a zero
    // is still an answer here, because most of these gates have no env override at
    // all, and "the excluded population is empty" is the cheapest way for one of
    // them to be settled.
    // SORTED BY COST, and the sort is NOT a ranking -- see the header note. It mixes
    // eta entries, rows, fixings and a bool, and on the one corpus where it was
    // checked, ordering these rows by `hits` gave the IDENTICAL permutation, so the
    // cost column ordered nothing. It is a work QUEUE, and `solves` is printed
    // beside it because a magnitude without a population cannot be read at all:
    // one row here was 468 of its 473 hits from a single LP.
    let mut ranked = gate_report();
    ranked.sort_by_key(|entry| std::cmp::Reverse(entry.2));
    for (site, hits, cost, solves) in ranked {
        eprintln!(
            "FORGONE gate              cost={cost:<12} hits={hits:<8} solves={solves:<5} {}  [{}]",
            site.gate, site.unit
        );
    }
    if !on() {
        return;
    }
    eprintln!(
        "AY_SEPSTAT rows           mir={} strongcg={}",
        g(&MIR_ROWS),
        g(&SCG_ROWS)
    );
    eprintln!("AY_SEPSTAT terms          built={}", g(&TERMS_BUILT));
    eprintln!(
        "AY_SEPSTAT build_subs     built={} none={}",
        g(&SUBS_BUILT),
        g(&SUBS_NONE)
    );
    eprintln!(
        "AY_SEPSTAT deltas         lists={} entries={}",
        g(&DELTA_LISTS),
        g(&DELTA_ENTRIES)
    );
    eprintln!(
        "AY_SEPSTAT mir_round      passes={} early_none={} late_none={} some={}",
        g(&MIR_PASS),
        g(&MIR_EARLY),
        g(&MIR_PASS).saturating_sub(g(&MIR_EARLY) + g(&MIR_SOME)),
        g(&MIR_SOME)
    );
    eprintln!(
        "AY_SEPSTAT strongcg_round passes={} range_none={} early_none={} late_none={} some={}",
        g(&SCG_PASS),
        g(&SCG_RANGE_NONE),
        g(&SCG_EARLY),
        g(&SCG_PASS).saturating_sub(g(&SCG_RANGE_NONE) + g(&SCG_EARLY) + g(&SCG_SOME)),
        g(&SCG_SOME)
    );
    eprintln!(
        "AY_SEPSTAT candidates     violated={} not_violated={} rows_returning_cut={}",
        g(&CAND_POS),
        g(&CAND_NONPOS),
        g(&ROW_RET)
    );
    eprintln!(
        "AY_SEPSTAT late_none      out_empty={} nonfinite={} absurd_numbers={}",
        g(&LATE_EMPTY),
        g(&LATE_NONFINITE),
        g(&LATE_ABSURD)
    );
    eprintln!(
        "AY_SEPSTAT screen         tried={} skipped={} row_kills={} build_fail={} unknown={}",
        g(&SCREEN_TRIED),
        g(&SCREEN_SKIP),
        g(&SCREEN_ROW_KILL),
        g(&SCREEN_BUILD_FAIL),
        g(&SCREEN_UNKNOWN)
    );
    eprintln!(
        "AY_SEPSTAT audit          ok={} FAIL={}",
        g(&AUDIT_OK),
        g(&AUDIT_FAIL)
    );
    eprintln!(
        "AY_SEPSTAT cuts_returned  mir={} strongcg={}",
        g(&MIR_CUTS),
        g(&SCG_CUTS)
    );
    eprintln!(
        "AY_SEPSTAT sep_wall       {:.3}s (secondary, load-affected)",
        g(&SEP_NS) as f64 / 1e9
    );
}

#[cfg(test)]
mod forgone_tests {
    use super::*;

    /// The two counters must be distinguishable, because they answer different
    /// questions: `refused` is a fire rate and reports nothing on its own, while
    /// `refused_violated` is capability the model had and did not get.
    ///
    /// `1c1ce672c` is the measured reason the distinction is load-bearing: four
    /// separator families at fire rate ZERO produced four DIFFERENT verdicts —
    /// two correctly silent, one wrongly gated and worth a verdict, one net-
    /// negative to broaden. A count of refusals cannot separate those.
    #[test]
    fn a_satisfied_discard_and_a_violated_one_are_not_the_same_event() {
        let (r0, v0) = forgone();
        discarded(false);
        let (r1, v1) = forgone();
        assert_eq!(
            (r1 - r0, v1 - v0),
            (1, 0),
            "a satisfied discard cost nothing"
        );
        discarded(true);
        let (r2, v2) = forgone();
        assert_eq!(
            (r2 - r1, v2 - v1),
            (1, 1),
            "a violated discard is the finding, and must be counted apart"
        );
    }

    /// Always-on: the counters do not consult `--sepstat`. A number that
    /// appears only when someone already suspects a problem cannot report one
    /// nobody suspects.
    #[test]
    fn the_counters_are_not_gated() {
        let (before, _) = forgone();
        discarded(false);
        assert!(
            forgone().0 > before,
            "forgone cost must accrue regardless of the census switch"
        );
    }
}

/// Force every lazily-cached environment read in this module to happen NOW.
///
/// # The race this closes
///
/// `tune.rs` states the property the crate is supposed to have: *"The environment
/// layer is read **once**, into `EnvSnapshot`, and never again — so no accessor on
/// the solve path touches `std::env`."* That is true of the `tune` layer and FALSE
/// of the crate: 1 accessors here cache their value in a `OnceLock` and call
/// `env::var` **lazily**, inside `get_or_init`, the first time the solve path
/// happens to reach them — at an arbitrary point, on an arbitrary thread.
///
/// That is the exact hazard `EngineEconomics` was built to remove.
/// the development design notes records the consumer's mitigation:
/// it *"rewrites the same constant values before every window solve"*, so a
/// `set_var` on one thread can land while another thread is mid-solve taking its
/// first `getenv` here. `std::env::set_var` racing a concurrent `getenv` is why it
/// is `unsafe` in edition 2024.
///
/// Priming collapses those windows into ONE, at solve entry, before any worker is
/// spawned. It changes no value: the same `OnceLock`s resolve to the same bytes.
/// It only moves *when* they are read, from "scattered across the solve" to "once,
/// at a point the caller controls".
pub(crate) fn prime_env() {
    let _ = on();
}

#[cfg(test)]
mod prime_tests {
    /// Priming must be IDEMPOTENT and VALUE-PRESERVING. It moves *when* the
    /// environment is read, never *what* is read: the same `OnceLock`s resolve to
    /// the same bytes, so a primed solve and an unprimed one are configured
    /// identically. If this ever fails, priming has become a behaviour change and
    /// the "changes no value" claim in `prime_env_all` is false.
    #[test]
    fn priming_is_idempotent_and_changes_nothing() {
        let before = (
            super::on(),
            crate::simplex::stats::solve_work(),
            super::forgone(),
        );
        for _ in 0..3 {
            super::prime_env();
            crate::simplex::prime_env();
            crate::lu::prime_env();
            crate::cuts::prime_env();
            crate::session::prime_env();
            crate::certify::prime_env();
        }
        let after = (
            super::on(),
            crate::simplex::stats::solve_work(),
            super::forgone(),
        );
        assert_eq!(before, after, "priming must not change any resolved value");
    }
}
