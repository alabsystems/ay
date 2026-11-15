//! Definition related to variables.

use crate::prelude::{ToPrettyString, VarNameLookup};

/// Type definition for a variable index. The variable index is just `usize`, but the separate name makes it easier to identify what a variable is.
pub type VarIdx = usize;

/// The largest variable index this checker will build its dense per-variable tables for.
///
/// [`Lit::MAX_VAR_IDX`](crate::lit::Lit::MAX_VAR_IDX) is the *representability* bound: above it
/// two distinct variables pack to the same [`Lit`](crate::lit::Lit). This is the *practical* one,
/// and it exists because the checker is densely indexed by variable. The variable-name table, the
/// propagation [`Assignment`](crate::assignment::Assignment) and every watchlist are `Vec`s
/// indexed by [`VarIdx`], so a run costs `Θ(largest variable index used)` and **not**
/// `Θ(size of the input)` — a 25-byte DIMACS file naming variable 4294967300 asks for tables
/// covering four billion variables before a single proof line is read.
///
/// Measured at the bound itself rather than extrapolated to it, because the per-index cost is
/// **not** linear in `N`. Release build, 2026-08-24, on an arm64 Mac (Apple M5 Max, 128 GiB,
/// macOS 26.5.2); each run is `p cnf N 1` with a one-literal body and a proof that checks
/// nothing, so all of the cost is the dense set-up before the first proof line. Minimum wall
/// time and maximum peak memory footprint over three runs, `/usr/bin/time -l`:
///
/// | `N` | wall | peak footprint | bytes/index | ns/index |
/// |---|---|---|---|---|
/// | 10^5 | 0.01 s | 8.6 MB | 68 | 53 |
/// | 10^6 | 0.09 s | 95 MB | 93 | 85 |
/// | 10^7 | 1.5 s | 796 MB | 79 | 154 |
/// | 3·10^7 | 6.4 s | 2.9 GB | 98 | 212 |
/// | 6·10^7 | 14.4 s | 5.9 GB | 98 | 241 |
/// | `1 << 27` | 37 s | 12.1 GB | 90 | 278 |
///
/// So: **≈70–100 bytes per index, and between ≈50 and ≈280 ns per index depending on how many
/// there are.** Memory is roughly proportional (the spread is the allocator's growth doubling);
/// time is not — the per-index cost grows by 5x across this range, because the work is dominated
/// by faulting in and touching pages rather than by anything per-variable, so the time figures in
/// particular are a property of *this* machine's memory subsystem and will differ elsewhere. At
/// the bound that is **≈12 GB and ≈31–38 s** (the span of repeated runs) of set-up — already past
/// most machines, and deliberately so, since a bound that only refuses what no machine could ever
/// attempt would never fire. Peak *resident* set at the bound is lower, ≈10.0–10.2 GB, but that
/// is the OS reclaiming pages under pressure rather than memory the run did not ask for.
///
/// Above the bound nothing can be measured through the checker, since the checker is what refuses
/// it; extrapolating the ≈90 bytes/index measured at the bound, one power of two higher is
/// ≈24 GB and `u32::MAX`, where a 32-bit variable index would put it, is ≈390 GB — at which point
/// the process dies in the allocator or to the OOM killer, neither of which is a verdict. Those
/// two are extrapolations and are not measurements.
///
/// The lower end is set by what must keep working: `1 << 27` is 13x the largest instance in this
/// repository's own performance corpus (10.2M variables — see the `[profile.release]` note in
/// `Cargo.toml`) and far above any published DIMACS instance. A file that needs more is refused
/// with a parse error naming the index, which is strictly better than dying inside the allocator
/// after the run has already claimed to be checking a proof.
///
/// Raising it is one line and costs no soundness: the unconditional
/// [`Lit::MAX_VAR_IDX`](crate::lit::Lit::MAX_VAR_IDX) check sits above it and is the one that
/// must not move.
pub const MAX_DENSE_VAR_IDX: VarIdx = 1 << 27;

// Checked at compile time on every target, including a 32-bit one where `Lit::MAX_VAR_IDX` is
// only `2^30 - 1`: the practical bound must sit strictly below the representability bound. If
// that order ever inverted, the practical check would shadow the unconditional soundness one and
// an index that aliases another variable would be reported as merely too large.
const _: () = assert!(MAX_DENSE_VAR_IDX < crate::lit::Lit::MAX_VAR_IDX);

impl ToPrettyString for VarIdx {
    fn to_pretty_string<V: VarNameLookup>(&self, var_names: &V) -> String {
        var_names.get_name(*self).to_string()
    }
}

/// Generic variable trait to represent a variable with potentially arbitrary names.
///
/// High-level properties of a variable:
/// - is either unassigned (`None`) or assigned (`Some(v)`, where `v` could be something like True, False, integer, float, ...)
///
pub trait VarType: Clone + Default {
    /// The type deteriming the value of the [`VarType`].
    type Value: Negate + Default;
    /// Construct a new variable.
    fn new() -> Self
    where
        Self: Sized;

    /// Set value of the variable.
    fn set_value(&mut self, value: Self::Value);

    /// Get value of the variable.
    fn get_value(&self) -> Self::Value;
}

/// Trait for in situ negation of a [`VarType::Value`].
pub trait Negate {
    /// Get the negation of the value.
    fn negate(self) -> Self;
}
