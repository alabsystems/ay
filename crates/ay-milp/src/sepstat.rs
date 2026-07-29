//! SEPARATION-WORK CENSUS — measurement scaffolding for the cut-separation front.
//!
//! Every counter here is load-invariant (counts, not wall) except the two `*_NS` timers, which
//! are reported only as a secondary signal. All of it is behind `AY_MILP_SEPSTAT`; with the env
//! var unset the only cost is one relaxed load of a `OnceLock<bool>` per bump site, and the
//! bump sites sit outside the exact-rational inner loops that matter.
//!
//! Motivation: the campaign brief attributed 6.01s of mas74's wall to cut families that derive
//! ZERO cuts, and named `strongcg_round` / `mir_round` as the kernels. "Derives nothing" is not
//! the same claim as "costs nothing to find that out" — a kernel that bails on its first
//! fractionality test is already free. These counters separate the two: they record how far
//! into each rounding pass the derivation got before it gave up.

use std::sync::atomic::{AtomicU64, Ordering};

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
    // Audit mode (`AY_MILP_SEP_SCREEN_AUDIT`): screen claims checked against the exact kernel.
    AUDIT_OK, AUDIT_FAIL,
}

pub static SEP_NS: AtomicU64 = AtomicU64::new(0);

pub fn on() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("AY_MILP_SEPSTAT").is_some())
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

pub fn dump() {
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
