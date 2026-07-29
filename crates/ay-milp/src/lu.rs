//! Sparse LU factorization of the simplex basis with Forrest–Tomlin-style
//! updates. Replaces the product-form-inverse eta file of the float simplex.
//!
//! # Representation
//!
//! The caller hands us the m basis columns explicitly (logical columns
//! already gathered as `-e_r`, so the `-I` sign convention of the engine
//! being replaced lives entirely in the caller's gather). We maintain
//!
//! ```text
//!     B = P_r^{-1} · L · E_1^{-1} · E_2^{-1} ··· E_k^{-1} · U · P_c
//! ```
//!
//! * `P_r`, `P_c` are row / column permutations kept as index maps between
//!   "original" indices (matrix rows, basis positions) and "stage" indices
//!   (the elimination order of the last `factor`). No data is ever moved to
//!   permute; solves gather on entry and scatter on exit.
//! * `L` is unit lower triangular in stage coordinates, frozen at
//!   factorization time, stored as a column list of below-diagonal
//!   `(row, multiplier)` pairs. Threshold pivoting bounds every multiplier
//!   by `1 / REL_PIVOT_THRESHOLD`, which is what keeps applying `L^{-1}`
//!   backward-stable.
//! * Each `E_j` is a Forrest–Tomlin row eta produced by one basis change:
//!   `E = I - Σ_c mult_c · e_t e_c^T`. Applying `E` costs one sparse dot
//!   product; applying `E^T` one sparse axpy.
//! * `U` is upper triangular with respect to a *mutable* pivot order
//!   (`uorder`): entry `(r, c)` satisfies `upos[r] < upos[c]` (diagonals are
//!   held separately in `udiag`). Updates never renumber stages, they only
//!   reorder `uorder`.
//!
//! # Why U is stored row-major
//!
//! A row-major `U` serves every hot path at once: the ftran back-solve runs
//! as dot products over rows in reverse pivot order, the btran forward-solve
//! runs as axpys over the same rows, and the Forrest–Tomlin elimination of
//! the spiked row walks rows of `U` by construction. The only column-wise
//! question we ever ask is "which rows hold an entry of column `t`?" when an
//! update replaces column `t` — a pattern-only query. So `ucols` stores a
//! lazily-maintained *pattern superset* (row ids, no values): deletions leave
//! stale ids behind and every consumer re-validates against the row lists.
//! That halves the bookkeeping of a full Suhl–Suhl two-sided store without
//! giving up the sparse walks.
//!
//! # Failure discipline
//!
//! Both `factor` and `update` are transactional: they return `Err(Singular)`
//! *before* mutating any engine state, so on failure the previous
//! factorization stays valid and the caller may keep solving with the stale
//! basis (the "stale costs tightness, never soundness" doctrine of the
//! surrounding simplex) or refactorize/repair as it sees fit. Nothing here
//! panics on numerically bad input; `update` treats malformed caller-shaped
//! arguments (wrong lengths, out-of-range leaving positions) as closed
//! singular declines.

use std::cmp::Reverse;
use std::collections::BinaryHeap;
use std::sync::atomic::{AtomicU64, Ordering::Relaxed};

/// Per-solve LU cost census (AY_MILP_TRACE): call counts, summed reach
/// (touched-slot) sizes, and update wall. Diagnostics only — accumulated
/// only when `lu_solve_stats()` is set, so the default hot path is untouched.
/// The reach sums answer "how many of m slots does each solve actually
/// touch?" — the dense-inverse question the fill-reduction lever turns on.
pub(crate) static LU_FTRAN_CALLS: AtomicU64 = AtomicU64::new(0);
pub(crate) static LU_FTRAN_REACH: AtomicU64 = AtomicU64::new(0);
pub(crate) static LU_BTRAN_CALLS: AtomicU64 = AtomicU64::new(0);
pub(crate) static LU_BTRAN_REACH: AtomicU64 = AtomicU64::new(0);
pub(crate) static LU_UPDATE_CALLS: AtomicU64 = AtomicU64::new(0);
pub(crate) static LU_UPDATE_NANOS: AtomicU64 = AtomicU64::new(0);
// Forrest–Tomlin `update()` sub-phase timers (AY_MILP_TRACE; surfaced on the
// UPDPROFILE line): SPIKE = v = U·(P_c·alpha) build, ELIM = the sparse
// left-looking row solve of old row t + new diagonal, COMMIT = U row/column
// splice + cyclic pivot-order shift + eta record. Only accumulated under the
// trace flag (the hot path leaves them untouched), so they cost nothing off.
pub(crate) static FT_SPIKE_NANOS: AtomicU64 = AtomicU64::new(0);
pub(crate) static FT_ELIM_NANOS: AtomicU64 = AtomicU64::new(0);
pub(crate) static FT_COMMIT_NANOS: AtomicU64 = AtomicU64::new(0);

/// Whether to accumulate the per-solve LU cost census (`AY_MILP_TRACE`).
fn lu_solve_stats() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| std::env::var_os("AY_MILP_TRACE").is_some())
}

/// Kill switch for the Forrest–Tomlin update's bounds-check-elided fast loops
/// (`AY_MILP_NO_FT_FAST`). Off (env set) => take the safe checked path, the
/// exact pre-change arithmetic. Both branches run the SAME float ops in the SAME
/// order — the unchecked form only drops bounds checks on indices that are
/// provably `< m` (stage ids, and `stage_pos`/`urows` column ids are all stage
/// ids in `0..m` by construction; `w`/`v` are resized to `m`), so it is
/// byte-identical, not a numeric change. An A/B toggle in one binary.
fn ft_fast_update() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| std::env::var_os("AY_MILP_NO_FT_FAST").is_none())
}

/// Spike-build arm selection for the Forrest–Tomlin `update`
/// (`AY_MILP_FT_SPIKE` = `dense` | `sparse` | anything else / unset = `auto`).
/// `dense` is the exact pre-change path, so this is an A/B toggle in one
/// binary; `sparse` forces the pattern-driven arm regardless of density, which
/// is what lets the dense-reference guard tests cover the new code at m=48..60
/// where `auto` would always pick dense (their alphas are 100% dense).
#[derive(Clone, Copy, PartialEq, Eq)]
enum SpikeArm {
    Auto,
    Dense,
    Sparse,
}

fn spike_arm() -> SpikeArm {
    static B: std::sync::OnceLock<SpikeArm> = std::sync::OnceLock::new();
    *B.get_or_init(|| match std::env::var("AY_MILP_FT_SPIKE").as_deref() {
        Ok("dense") => SpikeArm::Dense,
        Ok("sparse") => SpikeArm::Sparse,
        _ => SpikeArm::Auto,
    })
}

/// How much of `U` the sparse spike build is allowed to touch before the dense
/// build is the better deal, as a divisor of `m`: the sparse arm is taken only
/// when the PREDICTED marked set `|supp(w)| · (1 + unnz/m)` is under `m/2`.
///
/// Break-even is near `|M| ≈ m/2` because the marking pass costs about as much
/// as the compute pass it guards, so below half the rows the sparse arm wins
/// twice and above it loses twice. Measured spike densities on the five
/// profiled models (FTRAN reach / m, and `unnz/m` from LUFACT `avg_nnz`) put
/// the split exactly where the per-update costs already sit:
///
/// ```text
///   model               m         reach     rho    predicted |M|/m   arm
///   uccase12            121,161      554    2.33         1.8%        sparse
///   physiciansched6-2   168,336    7,373    1.23         9.8%        sparse
///   neos-960392           4,744    1,158    3.00        97.7%        dense
///   ex10                 69,608   44,782    3.14       266%          dense
///   ex9                  40,962   32,322    3.69       369%          dense
/// ```
///
/// which is the same 2/2 split the per-update cost shows independently:
/// uccase12 and physiciansched6-2 sit pinned on the 5.2-5.3 ns/row dense-pass
/// floor and do not move with the refactor cadence (they pay ONLY the m-length
/// sweeps), while ex9/ex10 sit 8-10x above it and move 2.6x with the cadence
/// (they pay U fill, which sparsifying cannot touch).
///
/// THE GATE IS LOAD-BEARING, NOT A HEDGE. Forcing each arm on all four
/// (`AY_MILP_FT_SPIKE`, 400 s cap, `AY_MILP_COLD_LU_MAX_ROWS=400000`, 4
/// concurrent; `update=N (Ts, X ns/call)` off the LUSOLVE line):
///
/// ```text
///   model              m         dense ns    sparse ns   sparse arm    upd (D / P)
///   uccase12           121,161     598,160     112,557   5.31x FASTER  111,080 / 120,571
///   physiciansched6-2  168,336     783,870     459,543   1.71x FASTER   96,390 / 106,368
///   ex9                 40,962   1,886,336   3,092,302   1.64x SLOWER   60,313 /  51,393
///   ex10                69,608   3,970,991   6,062,673   1.53x SLOWER   23,889 /  23,306
/// ```
///
/// On uccase12 that takes `update` from 66.44 s to 13.57 s of a ~398 s solve.
/// On ex9/ex10 the forced sparse arm is a 1.5-1.6x LOSS — the marking pass
/// costs a full sweep and then the compute pass runs over nearly every row
/// anyway. Which is exactly the `flip_nz_enabled` precedent restated: air05's
/// ~54%-dense B^-1 made the sparse solve 2.3x SLOWER.
///
/// AND `Auto` DOES PICK RIGHT, unaided, on all four — a fourth run with no
/// `AY_MILP_FT_SPIKE` set lands within 1.7% of the better arm every time:
///
/// ```text
///   model              auto ns/call   best forced   auto/best
///   ex9                   1,882,182     1,886,336     0.998   (took dense)
///   ex10                  3,960,613     3,970,991     0.997   (took dense)
///   uccase12                114,443       112,557     1.017   (took sparse)
///   physiciansched6-2       464,324       459,543     1.010   (took sparse)
/// ```
///
/// On ex9 and ex10 the auto run's root LP bound comes out BYTE-IDENTICAL to
/// the forced-dense run's (62.120038 and 14.782647) — independent corroboration
/// that taking the gate's other branch changes nothing but the clock.
///
/// # Corpus A/B (`AY_MILP_FT_SPIKE=dense` vs default), 65 models, 60 s, 4 up
///
/// ```text
///                                          models  >10% cheaper  >10% dearer
///   cold-root LU band [3,000, 8,192)         44/43       19            0
///   above the ceiling (warm-node LU only)    21/14       13            0
/// ```
///
/// (second column = models that ran any LU update at all). Zero models got
/// dearer anywhere. The best in-band factors are h80x6320d 7.83x,
/// nexp-150-20-8-5 5.17x, n3div36 3.98x, fiball 3.66x, neos-4387871-tavua
/// 3.40x, dws008-01 3.39x; above the ceiling, decomp2 4.79x, CMS750_4 3.61x,
/// traininstance6 2.63x, net12 1.91x. Note that band membership is NOT the
/// population this helps: `tall_lu` puts every WARM node re-solve at m ≥ 1,000
/// on the LU engine, so the sparse arm pays on models far above the cold-root
/// ceiling too.
///
/// Verdicts: 0 gained, 0 lost. Node counts move on 9 of 65, all of them
/// capped-at-60 s runs where the cheaper update simply buys more nodes in the
/// same wall — every one of those keeps its incumbent and its rigorous bound
/// (h80x6320d: 1,069 -> 1,108 nodes, dual bound 5563.133723964278 both;
/// rmatr100-p10: 302 -> 329, incumbent 426 both, bound 396.026 -> 397.288,
/// i.e. TIGHTER). app1-1 is the only band model that terminates before the
/// cap, and it is the clean test of the vertex mechanism: identical node count
/// (176) and identical objective (-3) on both arms. seymour1 flipped
/// BOUND/UNKNOWN once in the sweep and does NOT reproduce — four repeats give
/// BOUND at 6 nodes on both arms, and two same-arm runs disagree with each
/// other, so it is 60 s-cap contention noise, not the change.
const SPIKE_SPARSE_MARGIN: usize = 2;

/// Kill switch for the DENSE `ftran`'s bounds-check-elided sweeps
/// (`AY_MILP_NO_FTRAN_FAST`). Off (env set) => take the safe checked path, the
/// exact pre-change arithmetic. This is the dense triangular solve the dual
/// simplex runs TWICE per pivot on the LU lane — the steepest-edge τ = B⁻¹ρ and
/// the long-step flip aggregate wflip = B⁻¹Σδ — where the RHS closes near-dense
/// and the sparse `ftran_nz` is a loss (see `tau_nz_enabled`/`flip_nz_enabled`).
/// Both branches run the SAME float ops in the SAME order; the unchecked form
/// only drops bounds checks on indices provably `< m` — `row_stage`, `stage_pos`
/// and `uorder` are permutations of `0..m`, `lcols`/`urows`/`etas` entries are
/// stage ids in `0..m` by construction, `udiag` has length `m`, and `x`/`w` are
/// length `m` — so it is byte-identical, not a numeric change. Same discipline
/// (and the same debug_asserts) as `apply_inverse_parts`.
fn ftran_fast() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| std::env::var_os("AY_MILP_NO_FTRAN_FAST").is_none())
}

/// Kill switch for the SPARSE `ftran_nz`'s bounds-check-elided reach + sweep
/// loops (`AY_MILP_NO_FTRANNZ_FAST`). Off (env set) => take the safe checked
/// path, the exact pre-change arithmetic. This is the PRIMARY pivot-column solve
/// α = B⁻¹·a_q the dual simplex runs ONCE PER PIVOT on the LU lane (the biggest
/// FTRAN by nnz — its support is `alpha_nnz`), plus the flip aggregate and the
/// duplicate-column admissibility solve. Both branches run the SAME float ops in
/// the SAME order over the SAME reach set (`count_sort_by` yields a unique order
/// either way); the unchecked form only drops bounds checks on indices provably
/// `< m` — `row_stage`/`stage_pos` are permutations of `0..m`, `lcols`/`urows`/
/// `ucols`/`etas` entries and the reach are all stage ids in `0..m` by
/// construction, `udiag`/`visit`/`w` have length `m`, and `x.len() == m`. So it
/// is byte-identical, not a numeric change. Same discipline (and the same
/// debug_asserts) as `ftran`'s `ftran_fast` path.
fn ftrannz_fast() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| std::env::var_os("AY_MILP_NO_FTRANNZ_FAST").is_none())
}

/// Kill switch for the O(m) counting sort of the sparse-solve reach set
/// (`AY_MILP_NO_COUNTSORT`). Off (env set) => always take the comparison sort,
/// which is the exact pre-change path — so this is an A/B toggle in one binary.
/// The two branches produce the SAME order (the reach holds distinct stage ids
/// and the key is injective into `[0, m)`, so the sorted order is unique), so
/// the numeric solve loops that consume `reach` are byte-identical either way.
fn count_sort_enabled() -> bool {
    static B: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *B.get_or_init(|| std::env::var_os("AY_MILP_NO_COUNTSORT").is_none())
}

/// Sort `reach` — a set of DISTINCT stage ids, each `< m` — ascending (or
/// descending) by `key`, an INJECTIVE map into `[0, m)` (`upos`/`stage` are
/// permutation positions). When the reach is a large fraction of `m`, an O(m)
/// counting sort (scatter into `scratch` at `key(x)`, then sweep the range)
/// beats the O(k·log k) comparison sort; when it is small, the sweep would
/// dominate, so the comparison sort is kept. Because the keys are distinct the
/// resulting order is UNIQUE, so both branches yield the identical sequence —
/// the caller's downstream float loops run in the same order, bit for bit.
///
/// `scratch` is a persistent buffer the caller holds at all-`usize::MAX`
/// between calls; this routine restores that invariant as it drains, so its
/// own reset cost is O(k), not O(m).
#[inline]
fn count_sort_by(
    reach: &mut Vec<usize>,
    scratch: &mut Vec<usize>,
    m: usize,
    descending: bool,
    key: impl Fn(usize) -> usize,
) {
    let k = reach.len();
    // Crossover: the counting sort's O(m) scatter+sweep beats ~k·⌈log2 k⌉
    // comparisons only when the reach is dense. `bits` = ⌊log2 k⌋+1.
    let bits = (u64::BITS - (k as u64).leading_zeros()) as usize;
    if k < 2 || k.saturating_mul(bits) < m || !count_sort_enabled() {
        if descending {
            reach.sort_unstable_by_key(|&x| Reverse(key(x)));
        } else {
            reach.sort_unstable_by_key(|&x| key(x));
        }
    } else {
        if scratch.len() < m {
            scratch.resize(m, usize::MAX);
        }
        for &x in reach.iter() {
            scratch[key(x)] = x;
        }
        reach.clear();
        if descending {
            for slot in (0..m).rev() {
                let v = scratch[slot];
                if v != usize::MAX {
                    reach.push(v);
                    scratch[slot] = usize::MAX;
                }
            }
        } else {
            for slot in 0..m {
                let v = scratch[slot];
                if v != usize::MAX {
                    reach.push(v);
                    scratch[slot] = usize::MAX;
                }
            }
        }
    }
}

/// Absolute pivot floor for factorization. Matches the surrounding simplex's
/// `pivot_tol` (1e-9): a pivot this small is indistinguishable from a basis
/// that is singular at the working precision, and dividing by it would launder
/// noise into the factors.
const ABS_PIVOT_TOL: f64 = 1e-9;

/// Threshold-partial-pivoting relative tolerance `u`: a pivot candidate must
/// satisfy `|a| >= u * max|column|`. This is the classical stability/sparsity
/// trade: it bounds every L multiplier by `1/u = 10`, so element growth per
/// elimination step is bounded, while leaving Markowitz free to choose among
/// admissible entries for sparsity.
const REL_PIVOT_THRESHOLD: f64 = 0.1;

/// How many lowest-count candidate columns the Markowitz search examines per
/// pivot step (Suhl-style bounded search). Full Markowitz would scan the
/// whole active submatrix each step; a small candidate set gets essentially
/// the same fill in practice at near-O(1) selection cost.
const MARKOWITZ_CANDIDATE_COLS: usize = 8;

/// Absolute floor for the new U diagonal created by an update. Same scale
/// rationale as `ABS_PIVOT_TOL`; the caller responds by refactorizing, which
/// is always safe and usually overdue when this trips.
const UPDATE_PIVOT_TOL: f64 = 1e-9;

/// Relative floor for the new U diagonal against the spike's infinity norm.
/// A diagonal tiny *relative to the spike* means the update would introduce
/// element growth of order `vmax/|d|`; 1e-12 only rejects catastrophic cases
/// (growth beyond ~1e12), preferring a refactorization to a poisoned U.
const FT_REL_PIVOT_TOL: f64 = 1e-12;

/// #layer2 growth-guard: the relaxed floor used on ILL-CONDITIONED bases.
/// The historical `FT_REL_PIVOT_TOL` (1e-12) rejects any FT update whose growth
/// exceeds ~1e12 and refactorizes. On a large-span big-M basis that can cause a
/// refactorization storm. Relaxing to the `f64` precision floor for this case
/// avoids that storm and remains sound: a grown U can only make the floating
/// solve less accurate, while every bound this lane produces is independently
/// revalidated (`check_point` or weak duality on exact duals). The worst case is
/// extra work or a declined candidate, never an unsupported verdict.
const FT_REL_PIVOT_TOL_ILL: f64 = 1e-16;

/// Spike-norm above which a basis is treated as ill-conditioned and gets the
/// relaxed growth guard. Well-conditioned bases (O(1)-O(1e3) coefficients) stay
/// on the conservative 1e-12 — BYTE-IDENTICAL to before — so a genuinely
/// near-singular small basis still refactorizes as it always did.
const BIG_SPIKE_NORM: f64 = 1e4;

/// `AY_MILP_FT_GROWTH_TOL` override (measurement lever); `None` = auto.
fn parse_ft_growth_tol_override(value: Option<&str>) -> Option<f64> {
    value
        .and_then(|s| s.parse::<f64>().ok())
        .filter(|v| v.is_finite() && *v > 0.0)
}

fn ft_growth_tol_override() -> Option<f64> {
    static V: std::sync::OnceLock<Option<f64>> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        parse_ft_growth_tol_override(std::env::var("AY_MILP_FT_GROWTH_TOL").ok().as_deref())
    })
}

/// Fill budget for `factor` (`AY_MILP_LU_MAX_FILL_NNZ`). A pure SAFETY CEILING
/// on the produced L+U nonzero count: cross it and `factor` DECLINES
/// (`FactorFail::OutOfBudget`) instead of letting a pathological Markowitz
/// blow-up exhaust the box's memory. This is what lets the solver ATTEMPT a
/// huge NN-verification MILP (cifar100: 106k rows / 44M nnz) and give up
/// gracefully rather than crash. The default is far above any shipping
/// instance's factor fill (measured qiu peak ≪ default), so it is a NO-OP —
/// byte-identical unset.
const LU_MAX_FILL_NNZ_DEFAULT: usize = 200_000_000;

fn parse_lu_max_fill_nnz(value: Option<&str>) -> usize {
    value
        .and_then(|s| s.parse::<usize>().ok())
        .filter(|&v| v > 0)
        .unwrap_or(LU_MAX_FILL_NNZ_DEFAULT)
}

fn lu_max_fill_nnz() -> usize {
    static V: std::sync::OnceLock<usize> = std::sync::OnceLock::new();
    *V.get_or_init(|| {
        parse_lu_max_fill_nnz(std::env::var("AY_MILP_LU_MAX_FILL_NNZ").ok().as_deref())
    })
}

fn automatic_ft_rel_pivot_tol(vmax: f64) -> f64 {
    if vmax > BIG_SPIKE_NORM {
        FT_REL_PIVOT_TOL_ILL
    } else {
        FT_REL_PIVOT_TOL
    }
}

/// The FT-update growth guard floor for a spike whose infinity norm is `vmax`.
/// Auto-relaxes on big-spike (ill-conditioned) bases; the env override wins.
fn ft_rel_pivot_tol(vmax: f64) -> f64 {
    if let Some(v) = ft_growth_tol_override() {
        return v;
    }
    automatic_ft_rel_pivot_tol(vmax)
}

/// One basis column, borrowed from the caller: `(row_index, value)` pairs.
/// Entries need not be sorted; duplicate row indices are summed. Logical
/// columns arrive as a single `(r, -1.0)` entry.
pub(crate) type BasisCol<'a> = &'a [(usize, f64)];

/// Factorization or update failure: the basis (or updated basis) is singular
/// at working precision.
///
/// `position` is a basis position (column slot) implicated in the failure:
/// for `factor`, a column that could not be pivoted (empty column, or the
/// first still-active column when no admissible pivot remains) — the caller
/// can repair the basis by replacing that slot with a logical; for `update`,
/// the `leaving_pos` whose replacement was rejected.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) struct Singular {
    pub(crate) position: usize,
}

/// Why `factor` gave up. Two distinct failures the caller must treat
/// differently:
///
/// * `Singular` — the classic working-precision rank failure. The previous
///   factorization stays valid, and the caller may repair the basis (kick the
///   dependent column) or retry; the eta-file arm knows how.
/// * `OutOfBudget` — the fill DECLINE. The produced L+U nonzero count crossed
///   `lu_max_fill_nnz()`, so the factorization was ABANDONED fail-closed rather
///   than exhaust memory. There is no repair: the caller must give up on this
///   basis (and, upstream, report `Unknown{MemoryLimit}`) — falling through to
///   the eta rebuild would only re-enter the same unbounded blow-up.
///
/// Both leave `self` bit-identical to the previous valid factorization: the
/// commit writes `self` only at the very end, past every failure return.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum FactorFail {
    Singular(Singular),
    OutOfBudget,
}

/// One Forrest–Tomlin row eta: `E = I - Σ (c, mult) · e_row e_c^T`.
/// ftran applies `w[row] -= Σ mult · w[c]`; btran (the transpose, in reverse
/// eta order) applies `w[c] -= mult · w[row]`.
#[derive(Clone)]
struct RowEta {
    row: usize,
    terms: Vec<(usize, f64)>,
}

/// Sparse LU basis engine. See the module docs for the operator layout.
///
/// A freshly constructed engine (`new(m)`) is *exactly* the factorization of
/// `B = -I` (the all-logical crash basis): identity permutations, empty `L`,
/// diagonal `U = -I`, no etas — zero factorization work, correct solves from
/// the first call, as the crash-basis contract requires.
#[derive(Clone)]
pub(crate) struct LuEngine {
    /// Dimension m (number of rows == number of basis positions).
    m: usize,
    /// stage -> original matrix row pivoted at that stage.
    stage_row: Vec<usize>,
    /// original matrix row -> stage.
    row_stage: Vec<usize>,
    /// stage -> basis position eliminated at that stage.
    stage_pos: Vec<usize>,
    /// basis position -> stage.
    pos_stage: Vec<usize>,
    /// L columns by stage: below-diagonal (stage_row, multiplier) pairs.
    lcols: Vec<Vec<(usize, f64)>>,
    /// Off-diagonal entry count of L.
    lnnz: usize,
    /// U diagonal by stage id. Every entry stays above the pivot tolerances
    /// by construction, so dividing by it is always safe.
    udiag: Vec<f64>,
    /// U off-diagonal rows by stage id: (column stage id, value), with
    /// `upos[col] > upos[row]` as invariant.
    urows: Vec<Vec<(usize, f64)>>,
    /// Lazy column pattern of U: for each column stage id, a superset of the
    /// row stage ids holding an entry in that column (stale ids allowed,
    /// re-validated on use). Values live only in `urows`.
    ucols: Vec<Vec<usize>>,
    /// Exact off-diagonal entry count of U (kept in step with `urows`).
    unnz: usize,
    /// Pivot order: position in the triangular order -> stage id.
    uorder: Vec<usize>,
    /// stage id -> position in `uorder`.
    upos: Vec<usize>,
    /// Forrest–Tomlin row etas, in application (append) order.
    etas: Vec<RowEta>,
    /// Total term count across `etas`.
    eta_nnz: usize,
    /// Updates applied since the last successful `factor`.
    n_updates: usize,
    /// Persistent solve scratch (stage-indexed), so ftran/btran allocate
    /// nothing per call — the hot-loop discipline of the engine this
    /// replaces.
    scratch: Vec<f64>,
    /// Row pattern of L (pattern only): for stage i, the stages k < i whose
    /// L column holds an entry in row i. Frozen with L at factor time; the
    /// sparse `btran_nz` reachability walks it backward.
    lrows: Vec<Vec<usize>>,
    /// Reachability stamps for the sparse solves (epoch-tagged so they are
    /// never cleared wholesale).
    visit: Vec<u32>,
    epoch: u32,
    /// Sparse-solve worklists (reused across calls).
    reach: Vec<usize>,
    stack: Vec<usize>,
    /// Counting-sort scratch for the reach set (`count_sort_by`): length `m`,
    /// held at all-`usize::MAX` between calls so each dense-reach sort pays only
    /// its own O(k) reset, not an O(m) wipe.
    sortbuf: Vec<usize>,
    // ---- factor() scratch, persistent so a per-node refactorization costs
    // work proportional to the basis's structural content, not m allocations.
    f_acols: Vec<Vec<(usize, f64)>>,
    f_arows: Vec<Vec<usize>>,
    f_rcount: Vec<usize>,
    f_ccount: Vec<usize>,
    f_rowact: Vec<bool>,
    f_colact: Vec<bool>,
    f_queue: Vec<usize>,
    // ---- update() scratch, persistent so a Forrest–Tomlin update costs no
    // per-call m-length allocation (the hot warm-pivot path). `u_w`/`u_v` are
    // fully overwritten by the DENSE spike build (see `u_w_dirty`); `u_res`
    // self-clears on the heap drain; `u_inq` is reset on pop; `u_heap` is
    // cleared at entry. Reusing them is BIT-IDENTICAL to the previous
    // fresh-Vec form — same values, same order.
    u_w: Vec<f64>,
    u_v: Vec<f64>,
    u_res: Vec<f64>,
    u_inq: Vec<bool>,
    u_heap: BinaryHeap<Reverse<(usize, usize)>>,
    /// Whether `u_w` / `u_v` may hold stale nonzeros. The DENSE spike build
    /// overwrites both in full, so it neither needs nor leaves a clean buffer;
    /// the SPARSE build reads `w` at columns it never wrote and `v` at rows it
    /// never wrote, so it REQUIRES all-zero and restores that on every exit.
    /// Carrying the flag means an arm switch pays one O(m) wipe instead of the
    /// sparse arm paying an O(m) pre-clear per call — which is precisely the
    /// cost it exists to remove. Checked in `assert_well_formed`.
    u_w_dirty: bool,
    u_v_dirty: bool,
    /// Marked-set stamps + worklist for the SPARSE spike build: epoch-tagged
    /// like `visit` so the reset is O(1) off a wrap. Kept SEPARATE from
    /// `visit`/`reach` so `update` never has to reason about aliasing with the
    /// sparse solves (which may be mid-flight in a caller's borrow).
    u_mark: Vec<u32>,
    u_epoch: u32,
    u_pat: Vec<usize>,
    /// Per-engine spike-arm override, outranking `AY_MILP_FT_SPIKE`. Exists so
    /// the guard tests can drive BOTH arms in one process (the env knob is a
    /// process-global `OnceLock`) and, in particular, so the dense-reference
    /// tests can be re-run with the sparse arm FORCED — at m = 48..60 with a
    /// 100%-dense alpha the automatic gate would always pick dense and the new
    /// code would be covered by nothing.
    spike_force: Option<bool>,
}

impl LuEngine {
    /// Engine representing `B = -I` (the crash basis) with no factorization
    /// work; see the struct docs.
    pub(crate) fn new(m: usize) -> Self {
        LuEngine {
            m,
            stage_row: (0..m).collect(),
            row_stage: (0..m).collect(),
            stage_pos: (0..m).collect(),
            pos_stage: (0..m).collect(),
            lcols: vec![Vec::new(); m],
            lnnz: 0,
            udiag: vec![-1.0; m],
            urows: vec![Vec::new(); m],
            ucols: vec![Vec::new(); m],
            unnz: 0,
            uorder: (0..m).collect(),
            upos: (0..m).collect(),
            etas: Vec::new(),
            eta_nnz: 0,
            n_updates: 0,
            scratch: vec![0.0; m],
            lrows: vec![Vec::new(); m],
            visit: vec![0; m],
            epoch: 0,
            reach: Vec::new(),
            stack: Vec::new(),
            sortbuf: vec![usize::MAX; m],
            f_acols: vec![Vec::new(); m],
            f_arows: vec![Vec::new(); m],
            f_rcount: vec![0; m],
            f_ccount: vec![0; m],
            f_rowact: vec![false; m],
            f_colact: vec![false; m],
            f_queue: Vec::new(),
            u_w: vec![0.0; m],
            u_v: vec![0.0; m],
            u_res: vec![0.0; m],
            u_inq: vec![false; m],
            u_heap: BinaryHeap::new(),
            u_w_dirty: false,
            u_v_dirty: false,
            u_mark: vec![0; m],
            u_epoch: 0,
            u_pat: Vec::new(),
            spike_force: None,
        }
    }

    /// Pin the Forrest–Tomlin spike build to one arm (`Some(true)` = sparse,
    /// `Some(false)` = dense, `None` = the density gate). Test/A-B hook only;
    /// the two arms leave byte-identical engine state, so this is never a
    /// numeric choice. See `update_nz`.
    #[cfg(test)]
    fn force_spike_arm(&mut self, sparse: Option<bool>) {
        self.spike_force = sparse;
    }

    /// Reset to the crash-basis operator (`B = -I`): identity permutations,
    /// empty L, diagonal `U = -I`, no updates — the state a fresh engine is
    /// born in, restored in place so every pool keeps its capacity.
    pub(crate) fn reset_to_identity(&mut self) {
        for k in 0..self.m {
            self.stage_row[k] = k;
            self.row_stage[k] = k;
            self.stage_pos[k] = k;
            self.pos_stage[k] = k;
            self.lcols[k].clear();
            self.udiag[k] = -1.0;
            self.urows[k].clear();
            self.ucols[k].clear();
            self.uorder[k] = k;
            self.upos[k] = k;
            self.lrows[k].clear();
        }
        self.lnnz = 0;
        self.unnz = 0;
        self.etas.clear();
        self.eta_nnz = 0;
        self.n_updates = 0;
    }

    /// Total fill of the representation: L off-diagonals, U diagonal +
    /// off-diagonals, and eta terms. The caller's refactor-on-fill policy
    /// compares this against its cap exactly as it compared the eta file's
    /// nonzero count.
    pub(crate) fn nnz(&self) -> usize {
        self.lnnz + self.m + self.unnz + self.eta_nnz
    }

    /// Number of Forrest–Tomlin updates absorbed since the last successful
    /// `factor` (the caller's `since_refactor` staleness trigger).
    pub(crate) fn updates(&self) -> usize {
        self.n_updates
    }

    /// Factor the given basis columns from scratch with Markowitz-ordered,
    /// threshold-partial-pivoted right-looking sparse Gaussian elimination.
    ///
    /// Transactional: all elimination state is local, and `self` is only
    /// overwritten on success — a failed factor leaves the previous
    /// factorization (and its solves) fully intact, which is the failure
    /// mode the surrounding simplex relies on. On success the update list is
    /// cleared and the update counter reset.
    ///
    /// Position binding is PRESERVED: `ftran` scatters by `stage_pos`, so
    /// slot `p` keeps exactly the column the caller put there. The caller
    /// must NOT re-permute `basis` after `factor` — the elimination order is
    /// internal to the engine.
    pub(crate) fn factor(&mut self, cols: &[BasisCol<'_>]) -> Result<(), FactorFail> {
        // The fill ceiling is read ONCE here (process-global OnceLock) and
        // passed down, so the decline path is unit-testable without racing the
        // env cache. Default 200M ⇒ never trips on a shipping instance.
        self.factor_within(cols, lu_max_fill_nnz())
    }

    /// The factorization proper, parameterized on the fill `budget`. `factor`
    /// is the sole production caller (with `lu_max_fill_nnz()`); the tests call
    /// this directly with a low budget to exercise the decline.
    fn factor_within(&mut self, cols: &[BasisCol<'_>], budget: usize) -> Result<(), FactorFail> {
        let m = self.m;
        assert_eq!(cols.len(), m, "factor: expected {m} basis columns");

        // ---- gather the active matrix ---------------------------------
        // Exact column entry lists (only nonzeros, only active rows), exact
        // row/column counts for Markowitz, and a lazy row pattern (column
        // ids, superset) so pivot rows can be enumerated without a scan.
        // All containers are the engine's persistent pools: a simplex
        // refactorizes every ~50 pivots at EVERY node, and the allocation
        // churn of fresh Vec-of-Vecs was the dominant cost in the profile.
        let mut acols = std::mem::take(&mut self.f_acols);
        let mut arows = std::mem::take(&mut self.f_arows);
        let mut rcount = std::mem::take(&mut self.f_rcount);
        let mut ccount = std::mem::take(&mut self.f_ccount);
        let mut row_active = std::mem::take(&mut self.f_rowact);
        let mut col_active = std::mem::take(&mut self.f_colact);
        acols.resize(m, Vec::new());
        arows.resize(m, Vec::new());
        rcount.resize(m, 0);
        ccount.resize(m, 0);
        row_active.resize(m, true);
        col_active.resize(m, true);
        for i in 0..m {
            acols[i].clear();
            arows[i].clear();
            rcount[i] = 0;
            row_active[i] = true;
            col_active[i] = true;
        }
        // A macro instead of a closure: the pools must go back into `self`
        // on EVERY exit path, including the singular ones.
        macro_rules! restore_pools {
            () => {
                self.f_acols = acols;
                self.f_arows = arows;
                self.f_rcount = rcount;
                self.f_ccount = ccount;
                self.f_rowact = row_active;
                self.f_colact = col_active;
            };
        }
        {
            let mut val = vec![0.0f64; m];
            let mut mark = vec![false; m];
            let mut touched: Vec<usize> = Vec::new();
            for (c, col) in cols.iter().enumerate() {
                touched.clear();
                for &(r, v) in col.iter() {
                    assert!(r < m, "factor: row {r} out of range in column {c}");
                    if !mark[r] {
                        mark[r] = true;
                        touched.push(r);
                    }
                    val[r] += v; // duplicate row indices sum
                }
                let mut n_ents = 0usize;
                for &r in &touched {
                    mark[r] = false;
                    let v = val[r];
                    val[r] = 0.0;
                    if v != 0.0 {
                        acols[c].push((r, v));
                        rcount[r] += 1;
                        arows[r].push(c);
                        n_ents += 1;
                    }
                }
                if n_ents == 0 {
                    // Structurally empty column: singular before any work.
                    restore_pools!();
                    return Err(FactorFail::Singular(Singular { position: c }));
                }
                ccount[c] = n_ents;
            }
        }
        // Elimination products, in original indices until stages are known.
        let mut rof: Vec<usize> = Vec::with_capacity(m); // stage -> orig row
        let mut cop: Vec<usize> = Vec::with_capacity(m); // stage -> position
        let mut lraw: Vec<Vec<(usize, f64)>> = Vec::with_capacity(m);
        let mut uraw: Vec<(f64, Vec<(usize, f64)>)> = Vec::with_capacity(m);
        // Dense merge scratch (stamped, so never re-zeroed wholesale):
        // wtag 0 = untouched, 1 = pre-existing entry, 2 = fill-in.
        let mut wval = vec![0.0f64; m];
        let mut wtag = vec![0u8; m];
        // Column-dedup stamps for the pivot-row pattern walk.
        let mut seen = vec![false; m];

        // ---- singleton peel ---------------------------------------------
        // A column with one active entry pivots for free: nothing else holds
        // the column, so there is no elimination, no fill, no L multipliers —
        // only the pivot row's other entries move into U, and each removal
        // can expose the next singleton. On a simplex basis this peels every
        // logical column (and any triangular tail) in one cascade, which is
        // the eta engine's "logicals for free" property — without it, a full
        // Markowitz factorization ran at every node warm-start and was the
        // whole profile.
        let mut queue = std::mem::take(&mut self.f_queue);
        queue.clear();
        for c in 0..m {
            if ccount[c] == 1 {
                queue.push(c);
            }
        }
        // Running total of PRODUCED L+U fill (the memory the factors occupy),
        // the quantity metered against `budget`. The peel makes no L entries
        // and cannot fill (it only moves existing pivot-row entries into U), so
        // its contribution is exactly the summed `urow` lengths — a bounded
        // O(nnz) prelude; the Markowitz phase below is where fill can explode.
        let mut peel_fill = 0usize;
        while let Some(pc) = queue.pop() {
            if !col_active[pc] || ccount[pc] != 1 {
                continue; // count changed since it was queued
            }
            debug_assert_eq!(acols[pc].len(), 1);
            let (pr, piv) = acols[pc][0];
            if piv.abs() <= ABS_PIVOT_TOL {
                // The only entry this column will ever have is numerically
                // zero: the basis is singular at working precision.
                self.f_queue = queue;
                restore_pools!();
                return Err(FactorFail::Singular(Singular { position: pc }));
            }
            row_active[pr] = false;
            col_active[pc] = false;
            acols[pc].clear();
            // Pivot row -> U entries; removals may expose new singletons.
            let mut urow: Vec<(usize, f64)> = Vec::new();
            for pidx in 0..arows[pr].len() {
                let c = arows[pr][pidx];
                if !col_active[c] || seen[c] {
                    continue;
                }
                seen[c] = true;
                if let Some(k) = acols[c].iter().position(|&(r, _)| r == pr) {
                    let (_, uval) = acols[c].swap_remove(k);
                    ccount[c] -= 1;
                    if ccount[c] == 1 {
                        queue.push(c);
                    }
                    urow.push((c, uval));
                }
            }
            for &(c, _) in &urow {
                seen[c] = false;
            }
            arows[pr].clear();
            rof.push(pr);
            cop.push(pc);
            lraw.push(Vec::new());
            peel_fill += urow.len();
            uraw.push((piv, urow));
        }
        self.f_queue = queue;
        let peeled = rof.len();
        // Seed the fill meter with the peel's produced U entries; every
        // Markowitz step below adds its own L+U and re-checks the budget.
        let mut produced = peel_fill;

        /// Best admissible pivot inside one column: `(markowitz, |v|, row, v)`
        /// minimizing the Markowitz count, breaking ties toward the larger
        /// magnitude (numerics) then the smaller row id (determinism).
        fn eval_col(
            ents: &[(usize, f64)],
            rcount: &[usize],
            ccnt: usize,
        ) -> Option<(usize, f64, usize, f64)> {
            let mut cmax = 0.0f64;
            for &(_, v) in ents {
                let a = v.abs();
                if a > cmax {
                    cmax = a;
                }
            }
            if cmax <= ABS_PIVOT_TOL {
                return None;
            }
            let floor = REL_PIVOT_THRESHOLD * cmax;
            let mut best: Option<(usize, f64, usize, f64)> = None;
            for &(r, v) in ents {
                let a = v.abs();
                if a <= ABS_PIVOT_TOL || a < floor {
                    continue;
                }
                let mk = (rcount[r] - 1) * (ccnt - 1);
                let better = match best {
                    None => true,
                    Some((bmk, ba, br, _)) => {
                        mk < bmk || (mk == bmk && (a > ba || (a == ba && r < br)))
                    }
                };
                if better {
                    best = Some((mk, a, r, v));
                }
            }
            best
        }

        // Min-heap of (column count, column) for candidate selection over the
        // columns the peel left behind. Lazy: every count change pushes a
        // fresh entry; stale pops are discarded.
        let mut heap: BinaryHeap<Reverse<(usize, usize)>> = BinaryHeap::new();
        for c in 0..m {
            if col_active[c] {
                heap.push(Reverse((ccount[c], c)));
            }
        }

        for _step in peeled..m {
            // ---- pivot selection ---------------------------------------
            let mut cands: Vec<(usize, usize)> = Vec::with_capacity(MARKOWITZ_CANDIDATE_COLS);
            while cands.len() < MARKOWITZ_CANDIDATE_COLS {
                let Some(Reverse((cnt, c))) = heap.pop() else {
                    break;
                };
                if !col_active[c] || ccount[c] != cnt {
                    continue; // stale entry
                }
                if cands.iter().any(|&(_, cc)| cc == c) {
                    continue; // same live column pushed twice at equal count
                }
                cands.push((cnt, c));
            }
            // (markowitz, col, |v|, row, v); ties: larger |v|, smaller col,
            // smaller row — fully deterministic.
            let mut best: Option<(usize, usize, f64, usize, f64)> = None;
            let consider =
                |mk: usize,
                 c: usize,
                 a: f64,
                 r: usize,
                 v: f64,
                 best: &mut Option<(usize, usize, f64, usize, f64)>| {
                    let better = match *best {
                        None => true,
                        Some((bmk, bc, ba, br, _)) => {
                            mk < bmk
                                || (mk == bmk
                                    && (a > ba || (a == ba && (c < bc || (c == bc && r < br)))))
                        }
                    };
                    if better {
                        *best = Some((mk, c, a, r, v));
                    }
                };
            for &(cnt, c) in &cands {
                if let Some((mk, a, r, v)) = eval_col(&acols[c], &rcount, cnt) {
                    consider(mk, c, a, r, v, &mut best);
                }
            }
            if best.is_none() {
                // Rare fallback: none of the low-count candidates has an
                // admissible entry (all below the threshold). Sweep every
                // active column before declaring the basis singular.
                for c in 0..m {
                    if !col_active[c] {
                        continue;
                    }
                    if let Some((mk, a, r, v)) = eval_col(&acols[c], &rcount, ccount[c]) {
                        consider(mk, c, a, r, v, &mut best);
                    }
                }
            }
            let Some((_, pc, _, pr, piv)) = best else {
                // No admissible pivot anywhere: singular at working
                // precision. Report a concrete unpivotable slot.
                let position = (0..m).find(|&c| col_active[c]).unwrap_or(0);
                restore_pools!();
                return Err(FactorFail::Singular(Singular { position }));
            };
            // Unchosen candidates go back; their heap entries were consumed.
            for &(cnt, c) in &cands {
                if c != pc {
                    heap.push(Reverse((cnt, c)));
                }
            }

            row_active[pr] = false;
            col_active[pc] = false;

            // ---- L multipliers from the pivot column -------------------
            let mut pcol = std::mem::take(&mut acols[pc]);
            let mut lents: Vec<(usize, f64)> = Vec::with_capacity(pcol.len().saturating_sub(1));
            for &(r, v) in &pcol {
                if r == pr {
                    continue;
                }
                rcount[r] -= 1; // column pc leaves the active submatrix
                lents.push((r, v / piv));
            }
            pcol.clear();
            acols[pc] = pcol; // keep the capacity in the pool

            // ---- pivot row: extract U entries from every active column --
            let prpat = std::mem::take(&mut arows[pr]);
            let mut urow: Vec<(usize, f64)> = Vec::new();
            for &c in &prpat {
                if !col_active[c] || seen[c] {
                    continue; // dead column or duplicate pattern id
                }
                seen[c] = true;
                if let Some(k) = acols[c].iter().position(|&(r, _)| r == pr) {
                    let (_, uval) = acols[c].swap_remove(k);
                    ccount[c] -= 1;
                    urow.push((c, uval));
                }
                // else: stale pattern entry (cancelled earlier) — skip.
            }
            for &c in &prpat {
                seen[c] = false;
            }

            // ---- right-looking update: A[i][c] -= L[i] * U[pr][c] -------
            for &(c, uval) in &urow {
                if !lents.is_empty() {
                    let colvec = std::mem::take(&mut acols[c]);
                    let mut tlist: Vec<usize> = Vec::with_capacity(colvec.len() + lents.len());
                    for &(r, v) in &colvec {
                        wval[r] = v;
                        wtag[r] = 1;
                        tlist.push(r);
                    }
                    for &(r, lm) in &lents {
                        if wtag[r] == 0 {
                            wtag[r] = 2;
                            wval[r] = -lm * uval;
                            tlist.push(r);
                        } else {
                            wval[r] -= lm * uval;
                        }
                    }
                    let mut newcol = Vec::with_capacity(tlist.len());
                    for &r in &tlist {
                        let v = wval[r];
                        let tag = wtag[r];
                        wval[r] = 0.0;
                        wtag[r] = 0;
                        if v != 0.0 {
                            if tag == 2 {
                                rcount[r] += 1; // genuine fill-in
                                arows[r].push(c);
                            }
                            newcol.push((r, v));
                        } else if tag == 1 {
                            rcount[r] -= 1; // exact cancellation drops out
                        }
                        // tag == 2 with v == 0.0: fill that cancelled to
                        // exactly zero — never materialized, no counts.
                    }
                    ccount[c] = newcol.len();
                    acols[c] = newcol;
                }
                // Count changed (at least the pivot-row removal): refresh
                // the column's heap entry.
                heap.push(Reverse((ccount[c], c)));
            }

            rof.push(pr);
            cop.push(pc);
            // Meter the PRODUCED L+U fill (cheaper than materializing the active
            // submatrix's fill, and it tracks the same blow-up). Compute before
            // the move; on crossing the budget, DECLINE fail-closed. The commit
            // that writes `self` is past this point, so `restore_pools!` leaves
            // `self` = the previous valid factorization — no rollback needed.
            produced += lents.len() + urow.len();
            lraw.push(lents);
            uraw.push((piv, urow));
            if produced > budget {
                restore_pools!();
                return Err(FactorFail::OutOfBudget);
            }
        }

        restore_pools!();
        // ---- success: renumber into stage coordinates and commit -------
        let mut row_stage = vec![0usize; m];
        let mut pos_stage = vec![0usize; m];
        for (k, &r) in rof.iter().enumerate() {
            row_stage[r] = k;
        }
        for (k, &c) in cop.iter().enumerate() {
            pos_stage[c] = k;
        }
        let mut lcols: Vec<Vec<(usize, f64)>> = Vec::with_capacity(m);
        let mut lnnz = 0usize;
        for ents in lraw {
            let mapped: Vec<(usize, f64)> =
                ents.into_iter().map(|(r, v)| (row_stage[r], v)).collect();
            lnnz += mapped.len();
            lcols.push(mapped);
        }
        let mut udiag = vec![0.0f64; m];
        let mut urows: Vec<Vec<(usize, f64)>> = Vec::with_capacity(m);
        let mut unnz = 0usize;
        for (k, (diag, ents)) in uraw.into_iter().enumerate() {
            udiag[k] = diag;
            let mapped: Vec<(usize, f64)> =
                ents.into_iter().map(|(c, v)| (pos_stage[c], v)).collect();
            unnz += mapped.len();
            urows.push(mapped);
        }
        let mut ucols: Vec<Vec<usize>> = vec![Vec::new(); m];
        for (k, row) in urows.iter().enumerate() {
            for &(j, _) in row {
                ucols[j].push(k);
            }
        }

        self.stage_row = rof;
        self.row_stage = row_stage;
        self.stage_pos = cop;
        self.pos_stage = pos_stage;
        self.lcols = lcols;
        self.lnnz = lnnz;
        self.udiag = udiag;
        self.urows = urows;
        self.ucols = ucols;
        self.unnz = unnz;
        self.uorder = (0..m).collect();
        self.upos = (0..m).collect();
        self.etas.clear();
        self.eta_nnz = 0;
        self.n_updates = 0;
        for pat in &mut self.lrows {
            pat.clear();
        }
        for k in 0..m {
            for idx in 0..self.lcols[k].len() {
                let i = self.lcols[k][idx].0;
                self.lrows[i].push(k);
            }
        }
        #[cfg(any(test, debug_assertions))]
        self.assert_well_formed();
        Ok(())
    }

    /// Debug/test-only validation of the representation invariants that the
    /// checked and unchecked solve paths rely on. Release builds pay nothing;
    /// tests and debug builds get a direct corruption tripwire at factor/update
    /// boundaries.
    #[cfg(any(test, debug_assertions))]
    fn assert_well_formed(&self) {
        let m = self.m;
        assert_eq!(self.stage_row.len(), m, "stage_row length");
        assert_eq!(self.row_stage.len(), m, "row_stage length");
        assert_eq!(self.stage_pos.len(), m, "stage_pos length");
        assert_eq!(self.pos_stage.len(), m, "pos_stage length");
        assert_eq!(self.lcols.len(), m, "lcols length");
        assert_eq!(self.udiag.len(), m, "udiag length");
        assert_eq!(self.urows.len(), m, "urows length");
        assert_eq!(self.ucols.len(), m, "ucols length");
        assert_eq!(self.uorder.len(), m, "uorder length");
        assert_eq!(self.upos.len(), m, "upos length");
        assert_eq!(self.lrows.len(), m, "lrows length");
        assert_eq!(self.scratch.len(), m, "scratch length");
        assert_eq!(self.visit.len(), m, "visit length");

        fn assert_inverse_perm(forward: &[usize], inverse: &[usize], what: &str) {
            let m = forward.len();
            assert_eq!(inverse.len(), m, "{what}: inverse length");
            let mut seen = vec![false; m];
            for (i, &v) in forward.iter().enumerate() {
                assert!(v < m, "{what}: forward[{i}]={v} out of range");
                assert!(!seen[v], "{what}: duplicate forward value {v}");
                seen[v] = true;
                assert_eq!(inverse[v], i, "{what}: inverse mismatch at {v}");
            }
            assert!(
                seen.into_iter().all(|b| b),
                "{what}: forward is not a permutation"
            );
        }

        assert_inverse_perm(&self.stage_row, &self.row_stage, "row permutation");
        assert_inverse_perm(&self.stage_pos, &self.pos_stage, "position permutation");
        assert_inverse_perm(&self.uorder, &self.upos, "U pivot order");

        let mut lnnz = 0usize;
        let mut reconstructed_lrows = vec![Vec::new(); m];
        let mut seen = vec![false; m];
        for (k, col) in self.lcols.iter().enumerate() {
            for &(i, lv) in col {
                assert!(i < m, "L column {k}: row {i} out of range");
                assert!(i > k, "L column {k}: row {i} is not below diagonal");
                assert!(lv.is_finite(), "L column {k}: non-finite multiplier");
                assert!(!seen[i], "L column {k}: duplicate row {i}");
                seen[i] = true;
                reconstructed_lrows[i].push(k);
                lnnz += 1;
            }
            for &(i, _) in col {
                seen[i] = false;
            }
        }
        assert_eq!(self.lnnz, lnnz, "L nonzero counter");
        assert_eq!(self.lrows, reconstructed_lrows, "L row pattern");

        let mut unnz = 0usize;
        for (k, row) in self.urows.iter().enumerate() {
            assert!(
                self.udiag[k].is_finite() && self.udiag[k].abs() > UPDATE_PIVOT_TOL,
                "U diagonal {k} is invalid: {}",
                self.udiag[k]
            );
            for &(c, uv) in row {
                assert!(c < m, "U row {k}: column {c} out of range");
                assert!(
                    self.upos[k] < self.upos[c],
                    "U row {k}: column {c} violates triangular order"
                );
                assert!(uv.is_finite(), "U row {k}: non-finite value");
                assert!(!seen[c], "U row {k}: duplicate column {c}");
                seen[c] = true;
                assert!(
                    self.ucols[c].contains(&k),
                    "U column pattern for {c} misses actual row {k}"
                );
                unnz += 1;
            }
            for &(c, _) in row {
                seen[c] = false;
            }
        }
        assert_eq!(self.unnz, unnz, "U nonzero counter");
        for (c, pat) in self.ucols.iter().enumerate() {
            for &k in pat {
                assert!(k < m, "U column pattern {c}: row {k} out of range");
            }
        }

        let mut eta_nnz = 0usize;
        for (idx, eta) in self.etas.iter().enumerate() {
            assert!(eta.row < m, "eta {idx}: row {} out of range", eta.row);
            for &(c, mu) in &eta.terms {
                assert!(c < m, "eta {idx}: column {c} out of range");
                assert!(mu.is_finite(), "eta {idx}: non-finite multiplier");
                assert!(!seen[c], "eta {idx}: duplicate column {c}");
                seen[c] = true;
                eta_nnz += 1;
            }
            for &(c, _) in &eta.terms {
                seen[c] = false;
            }
        }
        assert_eq!(self.eta_nnz, eta_nnz, "eta nonzero counter");

        assert!(
            self.scratch.iter().all(|&v| v == 0.0),
            "shared solve scratch must be clean between solves"
        );
        assert!(
            self.u_res.iter().all(|&v| v == 0.0),
            "update residual scratch must be clean between updates"
        );
        assert!(
            self.u_inq.iter().all(|&b| !b),
            "update heap-membership scratch must be clean between updates"
        );
        // The sparse spike build reads `w` at columns and `v` at rows it never
        // writes, and relies on those reading exact 0.0. It therefore owes an
        // all-zero buffer on EVERY exit including the declines, and says so by
        // leaving the dirty flag down. This is the tripwire for the one new
        // failure mode the sparse arm introduces (a missed re-clear).
        assert!(
            self.u_w_dirty || self.u_w.iter().all(|&v| v == 0.0),
            "clean-marked spike gather scratch holds a nonzero"
        );
        assert!(
            self.u_v_dirty || self.u_v.iter().all(|&v| v == 0.0),
            "clean-marked spike scratch holds a nonzero"
        );
        assert_eq!(self.u_mark.len(), m, "spike mark length");
        assert!(self.u_heap.is_empty(), "update heap must be clean");
        assert!(self.stack.is_empty(), "DFS stack must be clean");
        assert!(
            self.sortbuf.iter().all(|&v| v == usize::MAX),
            "count-sort scratch must be clean"
        );
    }

    /// Solve `B x = b` in place: on entry `x` is the dense right-hand side
    /// indexed by matrix row, on exit it is the solution indexed by basis
    /// position (so `x[p]` pairs with basis slot `p`, as the simplex expects
    /// of an FTRAN result).
    ///
    /// Uses a dense stage-indexed scratch of length m; the solve already
    /// visits all m rows of U, so the O(m) scratch does not change the
    /// complexity class. L application skips zero positions, which is where
    /// sparsity actually pays (unit RHS, sparse entering columns).
    pub(crate) fn ftran(&mut self, x: &mut [f64]) {
        let m = self.m;
        assert_eq!(x.len(), m, "ftran: rhs length");
        let mut w = std::mem::take(&mut self.scratch);
        w.resize(m, 0.0);
        if !ftran_fast() {
            // Checked reference path (`AY_MILP_NO_FTRAN_FAST`): the exact
            // pre-change arithmetic. The fast path below is byte-identical to it.
            for r in 0..m {
                w[self.row_stage[r]] = x[r];
            }
            // L^{-1}: apply the frozen column etas in stage order.
            for k in 0..m {
                let wk = w[k];
                if wk != 0.0 {
                    for &(i, lv) in &self.lcols[k] {
                        w[i] -= lv * wk;
                    }
                }
            }
            // Forrest–Tomlin row etas, in append order.
            for e in &self.etas {
                let mut s = 0.0;
                for &(c, mu) in &e.terms {
                    s += mu * w[c];
                }
                w[e.row] -= s;
            }
            // U^{-1}: dot-product back-substitution in reverse pivot order; row
            // entries reference stages later in the order, already final.
            for pos in (0..m).rev() {
                let k = self.uorder[pos];
                let mut s = w[k];
                for &(c, v) in &self.urows[k] {
                    s -= v * w[c];
                }
                w[k] = s / self.udiag[k];
            }
            for k in 0..m {
                x[self.stage_pos[k]] = w[k];
                w[k] = 0.0; // the sparse solves share this scratch and rely on zeros
            }
            self.scratch = w;
            return;
        }
        // Bounds-check-elided fast path. SAFETY / byte-identity: every index is
        // provably `< m` — `row_stage`/`stage_pos`/`uorder` are permutations of
        // `0..m`; `lcols`/`urows`/`etas` entries are stage ids in `0..m`; `udiag`
        // has length `m`; `w` is resized to `m` and `x.len() == m` is asserted.
        // Identical float ops in identical order to the checked path above; only
        // the panic branches are dropped. Same discipline as `apply_inverse_parts`.
        unsafe {
            let wp = w.as_mut_ptr();
            for r in 0..m {
                let rs = *self.row_stage.get_unchecked(r);
                debug_assert!(rs < m);
                *wp.add(rs) = *x.get_unchecked(r);
            }
            // L^{-1}: apply the frozen column etas in stage order.
            for k in 0..m {
                let wk = *wp.add(k);
                if wk != 0.0 {
                    for &(i, lv) in self.lcols.get_unchecked(k) {
                        debug_assert!(i < m);
                        *wp.add(i) -= lv * wk;
                    }
                }
            }
            // Forrest–Tomlin row etas, in append order.
            for e in &self.etas {
                let mut s = 0.0;
                for &(c, mu) in &e.terms {
                    debug_assert!(c < m);
                    s += mu * *wp.add(c);
                }
                debug_assert!(e.row < m);
                *wp.add(e.row) -= s;
            }
            // U^{-1}: dot-product back-substitution in reverse pivot order; row
            // entries reference stages later in the order, already final.
            for pos in (0..m).rev() {
                let k = *self.uorder.get_unchecked(pos);
                debug_assert!(k < m);
                let mut s = *wp.add(k);
                for &(c, v) in self.urows.get_unchecked(k) {
                    debug_assert!(c < m);
                    s -= v * *wp.add(c);
                }
                *wp.add(k) = s / *self.udiag.get_unchecked(k);
            }
            for k in 0..m {
                let sp = *self.stage_pos.get_unchecked(k);
                debug_assert!(sp < m);
                *x.get_unchecked_mut(sp) = *wp.add(k);
                *wp.add(k) = 0.0; // the sparse solves share this scratch and rely on zeros
            }
        }
        self.scratch = w;
    }

    /// Solve `B^T y = c` in place: on entry `y` is the dense cost vector
    /// indexed by basis position, on exit the solution indexed by matrix row
    /// (the simplex's BTRAN convention for both dense pricing vectors and
    /// unit vectors).
    ///
    /// The transpose chain runs in the opposite order of `ftran`:
    /// `U^{-T}` (axpy form — a unit vector touches only the fill it creates,
    /// keeping the dual simplex's per-row BTRAN cheap), then the eta
    /// transposes in reverse, then `L^{-T}` as dot products.
    // Dense reference solve, exercised only by the unit tests below; the
    // production simplex goes through `btran_nz`.
    #[cfg_attr(not(test), allow(dead_code))]
    pub(crate) fn btran(&mut self, y: &mut [f64]) {
        let m = self.m;
        assert_eq!(y.len(), m, "btran: rhs length");
        let mut w = std::mem::take(&mut self.scratch);
        w.resize(m, 0.0);
        for k in 0..m {
            w[k] = y[self.stage_pos[k]];
        }
        // U^{-T}: forward substitution over rows of U in pivot order.
        for pos in 0..m {
            let k = self.uorder[pos];
            let zk = w[k] / self.udiag[k];
            w[k] = zk;
            if zk != 0.0 {
                for &(c, v) in &self.urows[k] {
                    w[c] -= v * zk;
                }
            }
        }
        // Eta transposes, reverse append order.
        for e in self.etas.iter().rev() {
            let wt = w[e.row];
            if wt != 0.0 {
                for &(c, mu) in &e.terms {
                    w[c] -= mu * wt;
                }
            }
        }
        // L^{-T}: dot products in reverse stage order (column k of L is row
        // k of L^T; its entries reference later stages, already final).
        for k in (0..m).rev() {
            let mut s = w[k];
            for &(i, lv) in &self.lcols[k] {
                s -= lv * w[i];
            }
            w[k] = s;
        }
        for r in 0..m {
            y[r] = w[self.row_stage[r]];
        }
        w.fill(0.0); // the sparse solves share this scratch and rely on zeros
        self.scratch = w;
    }

    /// Advance the reachability epoch, resetting the stamp array on wrap.
    fn bump_epoch(&mut self) -> u32 {
        self.epoch = self.epoch.wrapping_add(1);
        if self.epoch == 0 {
            self.visit.fill(0);
            self.epoch = 1;
        }
        self.epoch
    }

    /// Sparse FTRAN (Gilbert–Peierls): solve `B x = b` where `b`'s nonzero
    /// support is `nz` (matrix-row indices). On exit `x` holds the solution
    /// (basis-position indexed), `nz` its support, and every entry of `x`
    /// outside `nz` is zero — the shared-scratch discipline of the caller.
    ///
    /// Work is O(reachable pattern), not O(m): the L pass touches only the
    /// stages reachable from the support through L's column pattern, the U
    /// pass only the closure through `ucols` (a lazy SUPERSET pattern —
    /// legal here, because a stale id merely computes a zero it then never
    /// scatters). This is what makes a unit-vector solve on a sparse basis
    /// cost tens of operations instead of a dense O(m) sweep — the entire
    /// point of replacing the eta file at scale.
    pub(crate) fn ftran_nz(&mut self, x: &mut [f64], nz: &mut Vec<usize>) {
        let ep = self.bump_epoch();
        let mut w = std::mem::take(&mut self.scratch);
        let mut reach = std::mem::take(&mut self.reach);
        let mut stack = std::mem::take(&mut self.stack);
        let mut sortbuf = std::mem::take(&mut self.sortbuf);
        reach.clear();

        if !ftrannz_fast() {
            // Checked reference path (`AY_MILP_NO_FTRANNZ_FAST`): the exact
            // pre-change arithmetic. The fast path below is byte-identical to it.
            // Gather to stage space + symbolic DFS through L's column pattern.
            for idx in 0..nz.len() {
                let r = nz[idx];
                let k0 = self.row_stage[r];
                w[k0] += x[r];
                x[r] = 0.0;
                if self.visit[k0] != ep {
                    self.visit[k0] = ep;
                    stack.push(k0);
                    while let Some(k) = stack.pop() {
                        reach.push(k);
                        for &(i, _) in &self.lcols[k] {
                            if self.visit[i] != ep {
                                self.visit[i] = ep;
                                stack.push(i);
                            }
                        }
                    }
                }
            }
            // L forward, in stage order over the reach set only.
            count_sort_by(&mut reach, &mut sortbuf, self.m, false, |x| x);
            for &k in reach.iter() {
                let wk = w[k];
                if wk != 0.0 {
                    for &(i, lv) in &self.lcols[k] {
                        w[i] -= lv * wk;
                    }
                }
            }
            // Forrest–Tomlin row etas, append order. A row an eta writes joins
            // the touched set.
            for e in &self.etas {
                let mut s = 0.0;
                for &(c, mu) in &e.terms {
                    s += mu * w[c];
                }
                if s != 0.0 {
                    if self.visit[e.row] != ep {
                        self.visit[e.row] = ep;
                        reach.push(e.row);
                    }
                    w[e.row] -= s;
                }
            }
            // U backward: close the reach over `ucols` (column-pattern superset),
            // then back-substitute in descending pivot order. Every stage a
            // nonzero can flow into is in the closure; stages only reachable via
            // stale pattern ids just compute a value from their true row.
            let mut i0 = 0;
            while i0 < reach.len() {
                let c = reach[i0];
                i0 += 1;
                for idx in 0..self.ucols[c].len() {
                    let k = self.ucols[c][idx];
                    if self.visit[k] != ep {
                        self.visit[k] = ep;
                        reach.push(k);
                    }
                }
            }
            count_sort_by(&mut reach, &mut sortbuf, self.m, true, |x| self.upos[x]);
            for &k in reach.iter() {
                let mut s = w[k];
                for &(c, v) in &self.urows[k] {
                    s -= v * w[c];
                }
                w[k] = s / self.udiag[k];
            }
            // Scatter to positions; clear every touched stage.
            nz.clear();
            for &k in reach.iter() {
                let v = w[k];
                w[k] = 0.0;
                if v != 0.0 {
                    x[self.stage_pos[k]] = v;
                    nz.push(self.stage_pos[k]);
                }
            }
        } else {
            // Bounds-check-elided fast path. SAFETY / byte-identity: every index
            // is provably `< m` — `nz`/`row_stage` map matrix rows in `0..m`;
            // `reach`, `lcols`/`urows`/`ucols`/`etas` entries and every DFS id are
            // stage ids in `0..m` by construction; `stage_pos` maps stages to
            // positions in `0..m`; `udiag`/`visit`/`w` have length `m` and
            // `x.len() == m`. Identical float ops in identical order to the checked
            // path (the reach set and its `count_sort_by` order are the same);
            // only the panic branches are dropped. Same discipline (and the same
            // debug_asserts) as `ftran`'s `ftran_fast` path.
            unsafe {
                let wp = w.as_mut_ptr();
                // Gather to stage space + symbolic DFS through L's column pattern.
                for idx in 0..nz.len() {
                    let r = *nz.get_unchecked(idx);
                    debug_assert!(r < self.m);
                    let k0 = *self.row_stage.get_unchecked(r);
                    debug_assert!(k0 < self.m);
                    *wp.add(k0) += *x.get_unchecked(r);
                    *x.get_unchecked_mut(r) = 0.0;
                    if *self.visit.get_unchecked(k0) != ep {
                        *self.visit.get_unchecked_mut(k0) = ep;
                        stack.push(k0);
                        while let Some(k) = stack.pop() {
                            reach.push(k);
                            for &(i, _) in self.lcols.get_unchecked(k) {
                                debug_assert!(i < self.m);
                                if *self.visit.get_unchecked(i) != ep {
                                    *self.visit.get_unchecked_mut(i) = ep;
                                    stack.push(i);
                                }
                            }
                        }
                    }
                }
                // L forward, in stage order over the reach set only.
                count_sort_by(&mut reach, &mut sortbuf, self.m, false, |x| x);
                for &k in reach.iter() {
                    let wk = *wp.add(k);
                    if wk != 0.0 {
                        for &(i, lv) in self.lcols.get_unchecked(k) {
                            debug_assert!(i < self.m);
                            *wp.add(i) -= lv * wk;
                        }
                    }
                }
                // Forrest–Tomlin row etas, append order. A row an eta writes joins
                // the touched set.
                for e in &self.etas {
                    let mut s = 0.0;
                    for &(c, mu) in &e.terms {
                        debug_assert!(c < self.m);
                        s += mu * *wp.add(c);
                    }
                    if s != 0.0 {
                        debug_assert!(e.row < self.m);
                        if *self.visit.get_unchecked(e.row) != ep {
                            *self.visit.get_unchecked_mut(e.row) = ep;
                            reach.push(e.row);
                        }
                        *wp.add(e.row) -= s;
                    }
                }
                // U backward: close the reach over `ucols`, then back-substitute
                // in descending pivot order (see the reference path for why the
                // superset closure is safe).
                let mut i0 = 0;
                while i0 < reach.len() {
                    let c = *reach.get_unchecked(i0);
                    i0 += 1;
                    let clen = self.ucols.get_unchecked(c).len();
                    for idx in 0..clen {
                        let k = *self.ucols.get_unchecked(c).get_unchecked(idx);
                        debug_assert!(k < self.m);
                        if *self.visit.get_unchecked(k) != ep {
                            *self.visit.get_unchecked_mut(k) = ep;
                            reach.push(k);
                        }
                    }
                }
                count_sort_by(&mut reach, &mut sortbuf, self.m, true, |x| self.upos[x]);
                for &k in reach.iter() {
                    let mut s = *wp.add(k);
                    for &(c, v) in self.urows.get_unchecked(k) {
                        debug_assert!(c < self.m);
                        s -= v * *wp.add(c);
                    }
                    *wp.add(k) = s / *self.udiag.get_unchecked(k);
                }
                // Scatter to positions; clear every touched stage.
                nz.clear();
                for &k in reach.iter() {
                    let v = *wp.add(k);
                    *wp.add(k) = 0.0;
                    if v != 0.0 {
                        let sp = *self.stage_pos.get_unchecked(k);
                        debug_assert!(sp < self.m);
                        *x.get_unchecked_mut(sp) = v;
                        nz.push(sp);
                    }
                }
            }
        }
        if lu_solve_stats() {
            LU_FTRAN_CALLS.fetch_add(1, Relaxed);
            LU_FTRAN_REACH.fetch_add(reach.len() as u64, Relaxed);
        }
        self.scratch = w;
        self.reach = reach;
        self.stack = stack;
        self.sortbuf = sortbuf;
    }

    /// Sparse BTRAN: solve `B^T y = c` where `c`'s support is `nz`
    /// (basis-position indices). On exit `y` is the solution (matrix-row
    /// indexed), `nz` its support, entries outside it zero. The chain is the
    /// transpose of `ftran_nz`, phase by phase; L's backward reach walks the
    /// `lrows` row pattern frozen at factor time.
    pub(crate) fn btran_nz(&mut self, y: &mut [f64], nz: &mut Vec<usize>) {
        let ep = self.bump_epoch();
        let mut w = std::mem::take(&mut self.scratch);
        let mut reach = std::mem::take(&mut self.reach);
        let mut sortbuf = std::mem::take(&mut self.sortbuf);
        reach.clear();

        for idx in 0..nz.len() {
            let p = nz[idx];
            let k = self.pos_stage[p];
            w[k] += y[p];
            y[p] = 0.0;
            if self.visit[k] != ep {
                self.visit[k] = ep;
                reach.push(k);
            }
        }
        // U^T forward: closure over the (exact) row patterns, ascending
        // pivot order.
        let mut i0 = 0;
        while i0 < reach.len() {
            let k = reach[i0];
            i0 += 1;
            for idx in 0..self.urows[k].len() {
                let c = self.urows[k][idx].0;
                if self.visit[c] != ep {
                    self.visit[c] = ep;
                    reach.push(c);
                }
            }
        }
        count_sort_by(&mut reach, &mut sortbuf, self.m, false, |x| self.upos[x]);
        for &k in reach.iter() {
            let zk = w[k] / self.udiag[k];
            w[k] = zk;
            if zk != 0.0 {
                for &(c, v) in &self.urows[k] {
                    w[c] -= v * zk;
                }
            }
        }
        // Eta transposes, reverse append order.
        for e in self.etas.iter().rev() {
            let wt = w[e.row];
            if wt != 0.0 {
                for &(c, mu) in &e.terms {
                    if self.visit[c] != ep {
                        self.visit[c] = ep;
                        reach.push(c);
                    }
                    w[c] -= mu * wt;
                }
            }
        }
        // L^T backward: closure through `lrows` (who reads me?), descending
        // stage order.
        let mut i1 = 0;
        while i1 < reach.len() {
            let i = reach[i1];
            i1 += 1;
            for idx in 0..self.lrows[i].len() {
                let k = self.lrows[i][idx];
                if self.visit[k] != ep {
                    self.visit[k] = ep;
                    reach.push(k);
                }
            }
        }
        count_sort_by(&mut reach, &mut sortbuf, self.m, true, |x| x);
        for &k in reach.iter() {
            let mut s = w[k];
            for &(i, lv) in &self.lcols[k] {
                s -= lv * w[i];
            }
            w[k] = s;
        }
        nz.clear();
        for &k in reach.iter() {
            let v = w[k];
            w[k] = 0.0;
            if v != 0.0 {
                y[self.stage_row[k]] = v;
                nz.push(self.stage_row[k]);
            }
        }
        if lu_solve_stats() {
            LU_BTRAN_CALLS.fetch_add(1, Relaxed);
            LU_BTRAN_REACH.fetch_add(reach.len() as u64, Relaxed);
        }
        self.scratch = w;
        self.reach = reach;
        self.sortbuf = sortbuf;
    }

    /// Forrest–Tomlin update: basis position `leaving_pos` is replaced by
    /// `entering` (sparse, matrix-row indexed). `ftran_result` must be the
    /// FTRAN of `entering` through *this* factorization — the simplex always
    /// has it in hand from the ratio test, and we use it twice: for the O(1)
    /// early singularity check below, and implicitly as the guarantee that
    /// the spike we compute is consistent with what the caller just used.
    ///
    /// Scheme: let `t` be the stage bound to `leaving_pos`. The spike
    /// `v = E_k···E_1 L^{-1} P_r a` replaces column `t` of U; stage `t` moves
    /// to the end of the pivot order (the "permute the spiked column to the
    /// end" step, done on `uorder`, no data motion); the now-left-of-diagonal
    /// row `t` is eliminated against the later rows of U, and the multipliers
    /// become a new row eta while row `t` collapses to its new diagonal
    /// `d = v[t] - Σ mult_c v[c]`.
    ///
    /// Rejection: by the Forrest–Tomlin pivot identity the new diagonal
    /// equals `udiag[t] · alpha[leaving_pos]`, so a vanishing or non-finite
    /// prediction rejects before any work; the exactly-assembled `d` is
    /// checked again (absolute, and relative to the spike's magnitude)
    /// before anything is mutated. On `Err` the engine is untouched and the
    /// caller refactorizes.
    // No production caller: every simplex call site holds its FTRAN's support
    // and goes straight to `update_nz`. Kept because it is the entry point the
    // dense-reference guard tests drive, and because a caller without a
    // pattern must have a correct way in rather than an incentive to fake one.
    #[allow(dead_code)]
    pub(crate) fn update(
        &mut self,
        leaving_pos: usize,
        ftran_result: &[f64],
    ) -> Result<(), Singular> {
        // Pattern-free entry point: recover the support with the very O(m)
        // scan the sparse build exists to avoid. Every production call site
        // already holds its FTRAN's support and calls `update_nz` directly;
        // this form is for callers that do not — chiefly the dense-reference
        // guard tests, which drive `update` with a dense `ftran` result and
        // must keep compiling and passing verbatim.
        let nz: Vec<usize> = ftran_result
            .iter()
            .enumerate()
            .filter_map(|(i, &val)| (val != 0.0).then_some(i))
            .collect();
        self.update_nz(leaving_pos, ftran_result, &nz)
    }

    /// `update` with the caller's FTRAN support supplied.
    ///
    /// `nz` must be a SUPERSET of `supp(ftran_result)`: every index `i` with
    /// `ftran_result[i] != 0.0` must appear in `nz` (extra indices, and
    /// duplicates, are harmless — they only widen the marked set). That is
    /// exactly the contract `ftran_nz` already meets, and every production
    /// call site passes the `nz` vector it just used to fill (and is about to
    /// use to re-zero) its alpha buffer, so the pattern costs nothing to
    /// obtain. Violating it silently corrupts the factorization, so it is
    /// checked directly under `debug_assertions`.
    ///
    /// # Why the pattern buys anything
    ///
    /// The spike is `v = U · (P_c alpha)`. Building it densely costs a fixed
    /// number of full `0..m` sweeps regardless of how few nonzeros `alpha`
    /// has — a gather, the compute pass, two non-finite scans, the `vmax`
    /// scan and the spike-insert scan. Measured, that floor is 5.2-5.9 ns per
    /// row and it is INVARIANT over a 35x range of m (4,744 -> 168,336), which
    /// is the signature of nothing but the sweeps. On uccase12 the engine was
    /// paying seven 121,161-length passes to process 554 nonzeros.
    ///
    /// With the pattern the marked set is a ONE-STEP closure, no transitive
    /// walk: `v[k] != 0` needs either `w[k] != 0` or some `(c, ·)` in
    /// `urows[k]` with `w[c] != 0`, and the second case implies `k ∈ ucols[c]`
    /// because `assert_well_formed` enforces `ucols` to be a superset of the
    /// true column pattern. So
    /// `M = supp(w) ∪ ⋃_{c ∈ supp(w)} ucols[c] ⊇ supp(v)`, and for every
    /// `k ∉ M` the dense build would have computed exactly `0.0`.
    ///
    /// # Why it is bit-identical
    ///
    /// `M` is sorted ascending before it is used, so the compute loop, the
    /// `vmax` fold and the spike-insert loop all run in the DENSE arm's own
    /// order restricted to `M`; each `v[k]` runs the same inner loop over
    /// `urows[k]` in the same stored order and depends on no other `v`. The
    /// skipped entries are exactly `0.0`, which is the additive identity for
    /// `d`, cannot raise `vmax`, and inserts no spike entry. So the two arms
    /// leave BYTE-IDENTICAL engine state — asserted directly by
    /// `sparse_and_dense_spike_arms_agree_bit_for_bit`, which is why the arm
    /// choice can be a pure performance decision.
    ///
    /// # What the sparse arm does NOT remove
    ///
    /// Two `m`-length terms survive it, and they are what is left on the table:
    ///
    /// * the CYCLIC PIVOT-ORDER SHIFT in the commit (`for pos in p0..m-1`),
    ///   pure bookkeeping that computes nothing and could be O(1) with a
    ///   monotone `upos` counter plus a tombstoned `uorder` tail; and
    /// * `pat.sort_unstable()`, which is the price of BIT-IDENTITY rather than
    ///   mere equivalence (nothing downstream needs the order — every `v[k]` is
    ///   independent — but sorting is what makes the two arms diffable).
    ///
    /// They show up as a floor the sparse arm cannot get under. uccase12 lands
    /// at 0.93 ns/row against the dense arm's 4.94 (|M| ≈ 3.9 % of m), but
    /// physiciansched6-2 only reaches 2.76 against 4.66 (|M| ≈ 10.9 % of m) —
    /// far worse than its `|M|/m` would predict, and the `k·log k` of an 18,300
    /// element sort at m = 168,336 is the right size to be most of the gap.
    pub(crate) fn update_nz(
        &mut self,
        leaving_pos: usize,
        ftran_result: &[f64],
        nz: &[usize],
    ) -> Result<(), Singular> {
        let m = self.m;
        let _t0 = if lu_solve_stats() {
            Some(std::time::Instant::now())
        } else {
            None
        };
        // Records the update wall on every exit path (diagnostics only).
        macro_rules! upd_stat {
            () => {
                if let Some(t0) = _t0 {
                    LU_UPDATE_CALLS.fetch_add(1, Relaxed);
                    LU_UPDATE_NANOS.fetch_add(t0.elapsed().as_nanos() as u64, Relaxed);
                }
            };
        }

        if leaving_pos >= m || ftran_result.len() != m {
            upd_stat!();
            return Err(Singular {
                position: leaving_pos,
            });
        }
        let t = self.pos_stage[leaving_pos];

        // Early O(1) rejection via the FT pivot identity.
        let d_pred = self.udiag[t] * ftran_result[leaving_pos];
        if !d_pred.is_finite() || d_pred.abs() <= UPDATE_PIVOT_TOL {
            upd_stat!();
            return Err(Singular {
                position: leaving_pos,
            });
        }
        // The caller's pattern is load-bearing for the sparse arm: an index
        // missing from `nz` becomes a silently dropped spike entry, i.e. a
        // wrong inverse that still passes every numeric tolerance. Check it
        // outright where checking is free.
        debug_assert!(
            {
                let mut seen = vec![false; m];
                for &i in nz {
                    if i < m {
                        seen[i] = true;
                    }
                }
                ftran_result
                    .iter()
                    .enumerate()
                    .all(|(i, &val)| val == 0.0 || seen[i])
            },
            "update_nz: nz is not a superset of supp(ftran_result)"
        );

        // Arm choice. `Auto` compares the PREDICTED marked set against `m/2`:
        // `|M| ≲ |nz| · (1 + unnz/m)`, so the test `|nz|·(m+unnz)·2 < m·m` is
        // that comparison cleared of the division. See `SPIKE_SPARSE_MARGIN`
        // for the measured densities this is calibrated against. All terms are
        // saturating: at m = 168,336, `m·m` is 2.8e10 and the left side 5.5e9,
        // both far inside usize, but a malformed `nz` must not wrap.
        let sparse_spike = match self.spike_force.map_or_else(spike_arm, |s| {
            if s {
                SpikeArm::Sparse
            } else {
                SpikeArm::Dense
            }
        }) {
            SpikeArm::Dense => false,
            SpikeArm::Sparse => true,
            SpikeArm::Auto => {
                nz.len()
                    .saturating_mul(m.saturating_add(self.unnz))
                    .saturating_mul(SPIKE_SPARSE_MARGIN)
                    < m.saturating_mul(m)
            }
        };

        if sparse_spike {
            // Equivalent to the dense scan below: every index outside `nz`
            // holds exactly 0.0 (the contract just asserted), and 0.0 is
            // finite. An out-of-range pattern index is a closed decline, the
            // same fail-shut treatment malformed lengths get above.
            if nz.iter().any(|&i| i >= m || !ftran_result[i].is_finite()) {
                upd_stat!();
                return Err(Singular {
                    position: leaving_pos,
                });
            }
        } else if ftran_result.iter().any(|v| !v.is_finite()) {
            upd_stat!();
            return Err(Singular {
                position: leaving_pos,
            });
        }

        // ---- spike from the caller's FTRAN: v = U · (P_c alpha) ---------
        // The caller holds alpha = B^{-1}a for the entering column, and the
        // spike is exactly U applied to it in stage coordinates — one
        // O(m + unnz) row-major pass, instead of re-solving the column
        // through L and the whole eta chain (which doubled the dominant
        // per-pivot cost late in a refactor cycle).
        // Persistent scratch (see the struct fields): the DENSE arm overwrites
        // `w`/`v` in full, so it needs no pre-clear; the SPARSE arm needs them
        // all-zero on entry (it reads slots it never writes) and restores that
        // on every exit, which `u_w_dirty`/`u_v_dirty` track across arm
        // switches. `res` is left clean by the heap drain; `inq` is reset on
        // pop; `heap` is cleared here.
        let mut w = std::mem::take(&mut self.u_w);
        let mut v = std::mem::take(&mut self.u_v);
        let mut res = std::mem::take(&mut self.u_res);
        let mut inq = std::mem::take(&mut self.u_inq);
        let mut q = std::mem::take(&mut self.u_heap);
        w.resize(m, 0.0);
        v.resize(m, 0.0);
        res.resize(m, 0.0);
        inq.resize(m, false);
        q.clear();
        // Epoch for the sparse arm's marked set; bumped before `u_mark` is
        // moved out so the wrap reset can still see the field.
        self.u_epoch = self.u_epoch.wrapping_add(1);
        if self.u_epoch == 0 {
            self.u_mark.fill(0);
            self.u_epoch = 1;
        }
        let ep = self.u_epoch;
        let mut mark = std::mem::take(&mut self.u_mark);
        let mut pat = std::mem::take(&mut self.u_pat);
        mark.resize(m, 0);
        pat.clear();
        macro_rules! reject_update {
            () => {{
                // The sparse arm owns the all-zero invariant on `w`/`v`, and
                // owes it on the DECLINE paths too — a stale spike entry left
                // behind here would be read as real by the next call. The
                // transactional tests (`nonfinite_update_input_is_transactional`,
                // `late_reject_is_transactional`, `singular_rejected_engine_untouched`)
                // plus the `assert_well_formed` cleanliness checks are the guard.
                if sparse_spike {
                    for &k in pat.iter() {
                        w[k] = 0.0;
                        v[k] = 0.0;
                    }
                }
                res.fill(0.0);
                inq.fill(false);
                q.clear();
                self.u_w = w;
                self.u_v = v;
                self.u_res = res;
                self.u_inq = inq;
                self.u_heap = q;
                self.u_mark = mark;
                self.u_pat = pat;
                upd_stat!();
                return Err(Singular {
                    position: leaving_pos,
                });
            }};
        }
        // The dense arm overwrites every slot of `w` and `v` before reading
        // any of them — on its reject paths too — so it neither needs nor
        // leaves a clean buffer, and says so for the next sparse call.
        if !sparse_spike {
            self.u_w_dirty = true;
            self.u_v_dirty = true;
        }
        let mut _tph = _t0.map(|_| std::time::Instant::now());
        if sparse_spike {
            if self.u_w_dirty {
                w.fill(0.0);
                self.u_w_dirty = false;
            }
            if self.u_v_dirty {
                v.fill(0.0);
                self.u_v_dirty = false;
            }
            // 1. Scatter w = P_c alpha in stage coordinates and seed the mark
            //    set with supp(w). `t` is seeded unconditionally: the FT pivot
            //    identity above already proved `ftran_result[leaving_pos] != 0`,
            //    so `t` IS in the true support, and seeding it directly means
            //    the diagonal never depends on the caller's pattern being tight.
            let kt = self.pos_stage[leaving_pos];
            mark[kt] = ep;
            pat.push(kt);
            w[kt] = ftran_result[leaving_pos];
            for &p in nz {
                let k = self.pos_stage[p];
                if mark[k] != ep {
                    mark[k] = ep;
                    pat.push(k);
                }
                w[k] = ftran_result[p];
            }
            // 2. One-step closure over the U column patterns. `ucols` is a
            //    lazily-maintained SUPERSET (stale ids allowed), which only
            //    ever makes M bigger — never smaller — so the cover holds.
            let seeds = pat.len();
            for i in 0..seeds {
                let c = pat[i];
                for idx in 0..self.ucols[c].len() {
                    let k = self.ucols[c][idx];
                    if mark[k] != ep {
                        mark[k] = ep;
                        pat.push(k);
                    }
                }
            }
            // 3. Ascending stage order == the dense arm's order restricted to
            //    M, which is what makes the two arms byte-identical rather
            //    than merely equivalent.
            pat.sort_unstable();
            let mut finite = true;
            for &k in pat.iter() {
                let mut s = self.udiag[k] * w[k];
                for &(c, uv) in &self.urows[k] {
                    s += uv * w[c];
                }
                v[k] = s;
                finite &= s.is_finite();
            }
            // `w` is not read past the spike build; return it to the pool
            // clean so the next sparse call needs no wipe.
            for &k in pat.iter() {
                w[k] = 0.0;
            }
            if !finite {
                reject_update!();
            }
        } else if ft_fast_update() {
            // SAFETY: `stage_pos` is a permutation of `0..m`, so `stage_pos[k] < m`
            // and `ftran_result.len() == m` (asserted at entry); `w`/`v` were just
            // resized to `m`; `udiag` has length `m`; `urows[k]`'s column ids are
            // stage ids in `0..m` by the U-triangularity invariant. Every index is
            // thus in range. The arithmetic is unchanged (same muls/adds, same
            // order, no reassociation) — only the proven bounds checks are dropped.
            let stage_pos = &self.stage_pos;
            let udiag = &self.udiag;
            let urows = &self.urows;
            unsafe {
                for k in 0..m {
                    *w.get_unchecked_mut(k) =
                        *ftran_result.get_unchecked(*stage_pos.get_unchecked(k));
                }
                for k in 0..m {
                    let mut s = *udiag.get_unchecked(k) * *w.get_unchecked(k);
                    for &(c, uv) in urows.get_unchecked(k) {
                        s += uv * *w.get_unchecked(c);
                    }
                    *v.get_unchecked_mut(k) = s;
                }
            }
        } else {
            for k in 0..m {
                w[k] = ftran_result[self.stage_pos[k]];
            }
            for k in 0..m {
                let mut s = self.udiag[k] * w[k];
                for &(c, uv) in &self.urows[k] {
                    s += uv * w[c];
                }
                v[k] = s;
            }
        }
        // The sparse arm folded this into its own compute loop (entries
        // outside M are exactly 0.0, hence finite).
        if !sparse_spike && v.iter().any(|vk| !vk.is_finite()) {
            reject_update!();
        }

        if let Some(t) = _tph.as_mut() {
            FT_SPIKE_NANOS.fetch_add(t.elapsed().as_nanos() as u64, Relaxed);
            *t = std::time::Instant::now();
        }
        // ---- eliminate old row t against the later rows of U -----------
        // Sparse left-looking row solve: process touched columns in
        // ascending pivot order; each multiplier scatters that row's fill
        // further right, so every column is finalized when popped.
        let mut terms: Vec<(usize, f64)> = Vec::new();
        for &(c, uv) in &self.urows[t] {
            res[c] = uv;
            inq[c] = true;
            q.push(Reverse((self.upos[c], c)));
        }
        while let Some(Reverse((_, c))) = q.pop() {
            let val = res[c];
            res[c] = 0.0;
            inq[c] = false; // reset for the next update's reuse of `inq`
            if val == 0.0 {
                continue; // cancelled exactly — no eta term, no fill
            }
            let mu = val / self.udiag[c];
            if !mu.is_finite() {
                terms.push((c, mu));
                continue;
            }
            terms.push((c, mu));
            for &(c2, v2) in &self.urows[c] {
                if !inq[c2] {
                    inq[c2] = true;
                    q.push(Reverse((self.upos[c2], c2)));
                }
                res[c2] -= mu * v2;
            }
        }
        // `res` is provably ALL ZERO here — every slot written was `inq`-marked
        // and pushed, and every pop zeroes its slot before continuing — so the
        // full-length `res.iter().any(!is_finite)` this used to run alongside
        // could never fire on its own: a non-finite `res[c]` is read out as
        // `val` at its pop and turns into a non-finite `mu = val/udiag[c]`
        // (NaN/x, inf/x and inf/inf are all non-finite), which the `terms`
        // check below catches. `val == 0.0` is the only `continue` and 0.0 is
        // finite. So the scan was a pure m-length pass with no reachable
        // effect; it is kept as a debug tripwire on the argument itself.
        debug_assert!(
            res.iter().all(|v| *v == 0.0),
            "update: residual scratch must self-drain to exact zero"
        );
        if terms.iter().any(|&(_, mu)| !mu.is_finite()) {
            reject_update!();
        }
        // `res` (self-cleared on drain), `inq` (reset on pop) and the drained
        // `q` return to the pool clean; `w` is no longer read (the sparse arm
        // already re-zeroed it), and neither is `mark`. `v` is still needed
        // through the commit, so it and `pat` go back at each exit below.
        self.u_w = w;
        self.u_res = res;
        self.u_inq = inq;
        self.u_heap = q;
        self.u_mark = mark;

        // New diagonal, assembled the same way ftran will see it. `v[c]` for
        // an eliminated column outside M reads the exact 0.0 the dense arm
        // would have computed, so `d` is identical either way.
        let mut d = v[t];
        for &(c, mu) in &terms {
            d -= mu * v[c];
        }
        // Same for `vmax`: unmarked entries are exactly 0.0 and 0.0 can never
        // raise a running max that starts at 0.0.
        let mut vmax = 0.0f64;
        if sparse_spike {
            for &k in pat.iter() {
                let a = v[k].abs();
                if a > vmax {
                    vmax = a;
                }
            }
        } else {
            for &vk in v.iter() {
                let a = vk.abs();
                if a > vmax {
                    vmax = a;
                }
            }
        }
        if !d.is_finite() || d.abs() <= UPDATE_PIVOT_TOL || d.abs() < ft_rel_pivot_tol(vmax) * vmax
        {
            if sparse_spike {
                for &k in pat.iter() {
                    v[k] = 0.0;
                }
            }
            self.u_v = v;
            self.u_pat = pat;
            upd_stat!();
            return Err(Singular {
                position: leaving_pos,
            });
        }

        if let Some(t) = _tph.as_mut() {
            FT_ELIM_NANOS.fetch_add(t.elapsed().as_nanos() as u64, Relaxed);
            *t = std::time::Instant::now();
        }
        // ---- commit (no fallible step below this line) ------------------
        // 1. Row t's content now lives in the eta; drop it from U. Its
        //    columns' patterns keep stale ids (lazy, re-validated on use).
        self.unnz -= self.urows[t].len();
        self.urows[t].clear();
        // 2. Delete the replaced column t from the rows that hold it.
        let oldpat = std::mem::take(&mut self.ucols[t]);
        for i in oldpat {
            if let Some(k) = self.urows[i].iter().position(|&(c, _)| c == t) {
                self.urows[i].swap_remove(k);
                self.unnz -= 1;
            }
        }
        // 3. Insert the spike as the new column t. With t moved to the end
        //    of the pivot order, every off-diagonal spike entry sits above
        //    the diagonal, preserving U's triangularity invariant.
        let mut newpat = Vec::new();
        let ft_fast = ft_fast_update();
        if sparse_spike {
            // `pat` is sorted ascending, so this is the dense scan restricted
            // to M — same stages, same order, and every skipped stage holds
            // the exact 0.0 the dense scan would have skipped anyway. `newpat`
            // therefore comes out identical, element for element.
            for &k in pat.iter() {
                let vk = v[k];
                if vk != 0.0 && k != t {
                    self.urows[k].push((t, vk));
                    newpat.push(k);
                    self.unnz += 1;
                }
                v[k] = 0.0; // restore the sparse arm's all-zero invariant
            }
        } else if ft_fast {
            // SAFETY: `v.len() == m` and `urows.len() == m`, so `k < m` throughout.
            for (k, &vk) in v.iter().enumerate() {
                if vk != 0.0 && k != t {
                    unsafe { self.urows.get_unchecked_mut(k) }.push((t, vk));
                    newpat.push(k);
                    self.unnz += 1;
                }
            }
        } else {
            for (k, &vk) in v.iter().enumerate() {
                if vk != 0.0 && k != t {
                    self.urows[k].push((t, vk));
                    newpat.push(k);
                    self.unnz += 1;
                }
            }
        }
        self.u_v = v; // last read of the spike; return it to the pool
        self.u_pat = pat;
        self.ucols[t] = newpat;
        self.udiag[t] = d;
        // 4. Cyclic shift: stage t goes to the last pivot position.
        let p0 = self.upos[t];
        if ft_fast {
            // SAFETY: `pos` and `pos+1` are `< m` (range ends at `m-1`); `uorder`
            // and `upos` have length `m`; `s = uorder[pos+1]` is a stage id `< m`.
            // `uorder`/`upos` are disjoint fields, so the two mut borrows are sound.
            let uorder = &mut self.uorder;
            let upos = &mut self.upos;
            unsafe {
                for pos in p0..m - 1 {
                    let s = *uorder.get_unchecked(pos + 1);
                    *uorder.get_unchecked_mut(pos) = s;
                    *upos.get_unchecked_mut(s) = pos;
                }
            }
        } else {
            for pos in p0..m - 1 {
                let s = self.uorder[pos + 1];
                self.uorder[pos] = s;
                self.upos[s] = pos;
            }
        }
        self.uorder[m - 1] = t;
        self.upos[t] = m - 1;
        // 5. Record the row eta (indices are stage ids, immune to later
        //    reorderings; values are frozen linear-map coefficients).
        if !terms.is_empty() {
            self.eta_nnz += terms.len();
            self.etas.push(RowEta { row: t, terms });
        }
        self.n_updates += 1;
        if let Some(t) = _tph.as_ref() {
            FT_COMMIT_NANOS.fetch_add(t.elapsed().as_nanos() as u64, Relaxed);
        }
        upd_stat!();
        #[cfg(any(test, debug_assertions))]
        self.assert_well_formed();
        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ft_growth_guard_auto_threshold_and_override_parsing() {
        assert_eq!(automatic_ft_rel_pivot_tol(BIG_SPIKE_NORM), FT_REL_PIVOT_TOL);
        assert_eq!(
            automatic_ft_rel_pivot_tol(BIG_SPIKE_NORM + 1.0),
            FT_REL_PIVOT_TOL_ILL
        );
        assert_eq!(parse_ft_growth_tol_override(None), None);
        assert_eq!(parse_ft_growth_tol_override(Some("1e-14")), Some(1e-14));
        for invalid in ["0", "-1", "NaN", "inf", "invalid"] {
            assert_eq!(parse_ft_growth_tol_override(Some(invalid)), None);
        }
    }

    /// xorshift64* — deterministic, dependency-free test randomness.
    struct Rng(u64);

    impl Rng {
        fn new(seed: u64) -> Rng {
            Rng(seed.max(1))
        }
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x >> 12;
            x ^= x << 25;
            x ^= x >> 27;
            self.0 = x;
            x.wrapping_mul(0x2545_F491_4F6C_DD1D)
        }
        /// Uniform-ish in [-1, 1).
        fn f(&mut self) -> f64 {
            (self.next() >> 11) as f64 / (1u64 << 52) as f64 - 1.0
        }
        fn below(&mut self, n: usize) -> usize {
            (self.next() % n as u64) as usize
        }
    }

    fn refs(cols: &[Vec<(usize, f64)>]) -> Vec<BasisCol<'_>> {
        cols.iter().map(|c| c.as_slice()).collect()
    }

    /// Dense LU with partial pivoting — the reference the engine is checked
    /// against. `prow[k]` = original row placed at elimination position k.
    struct Dense {
        m: usize,
        a: Vec<f64>, // row-major, L below diagonal (unit), U on/above
        prow: Vec<usize>,
    }

    impl Dense {
        fn factor(m: usize, cols: &[Vec<(usize, f64)>]) -> Option<Dense> {
            let mut a = vec![0.0f64; m * m];
            for (c, col) in cols.iter().enumerate() {
                for &(r, v) in col {
                    a[r * m + c] += v;
                }
            }
            let mut prow: Vec<usize> = (0..m).collect();
            for k in 0..m {
                let mut ip = k;
                for i in k + 1..m {
                    if a[i * m + k].abs() > a[ip * m + k].abs() {
                        ip = i;
                    }
                }
                if a[ip * m + k].abs() < 1e-12 {
                    return None;
                }
                if ip != k {
                    for j in 0..m {
                        a.swap(k * m + j, ip * m + j);
                    }
                    prow.swap(k, ip);
                }
                let piv = a[k * m + k];
                for i in k + 1..m {
                    let lm = a[i * m + k] / piv;
                    a[i * m + k] = lm;
                    if lm != 0.0 {
                        for j in k + 1..m {
                            a[i * m + j] -= lm * a[k * m + j];
                        }
                    }
                }
            }
            Some(Dense { m, a, prow })
        }

        /// Solve A x = b; result indexed like A's columns.
        fn solve(&self, b: &[f64]) -> Vec<f64> {
            let m = self.m;
            let mut w: Vec<f64> = (0..m).map(|k| b[self.prow[k]]).collect();
            for k in 0..m {
                for i in k + 1..m {
                    w[i] -= self.a[i * m + k] * w[k];
                }
            }
            for k in (0..m).rev() {
                let mut s = w[k];
                for j in k + 1..m {
                    s -= self.a[k * m + j] * w[j];
                }
                w[k] = s / self.a[k * m + k];
            }
            w
        }

        /// Solve A^T y = c; input indexed like A's columns.
        fn solve_t(&self, c: &[f64]) -> Vec<f64> {
            let m = self.m;
            let mut z = vec![0.0f64; m];
            for k in 0..m {
                let mut s = c[k];
                for i in 0..k {
                    s -= self.a[i * m + k] * z[i];
                }
                z[k] = s / self.a[k * m + k];
            }
            for k in (0..m).rev() {
                let mut s = z[k];
                for i in k + 1..m {
                    s -= self.a[i * m + k] * z[i];
                }
                z[k] = s;
            }
            let mut y = vec![0.0f64; m];
            for k in 0..m {
                y[self.prow[k]] = z[k];
            }
            y
        }
    }

    fn max_diff(a: &[f64], b: &[f64]) -> f64 {
        a.iter()
            .zip(b)
            .map(|(x, y)| (x - y).abs())
            .fold(0.0, f64::max)
    }

    fn scale_of(v: &[f64]) -> f64 {
        1.0 + v.iter().fold(0.0f64, |s, x| s.max(x.abs()))
    }

    /// Threshold pivoting promises |multiplier| <= 1/u; verify on the real L.
    fn assert_multipliers_bounded(eng: &LuEngine) {
        let bound = 1.0 / REL_PIVOT_THRESHOLD + 1e-9;
        for col in &eng.lcols {
            for &(_, lv) in col {
                assert!(
                    lv.abs() <= bound,
                    "L multiplier {lv} exceeds threshold bound {bound}"
                );
            }
        }
    }

    #[test]
    fn fresh_engine_is_minus_identity() {
        let mut eng = LuEngine::new(5);
        let mut x = vec![1.0, 2.0, 3.0, 4.0, 5.0];
        eng.ftran(&mut x);
        assert_eq!(x, vec![-1.0, -2.0, -3.0, -4.0, -5.0]);
        let mut y = vec![2.0, -1.0, 0.5, 0.0, 3.0];
        eng.btran(&mut y);
        assert_eq!(y, vec![-2.0, 1.0, -0.5, 0.0, -3.0]);
        assert_eq!(eng.nnz(), 5);
        assert_eq!(eng.updates(), 0);
    }

    /// (a) Dense random systems, ftran/btran against the dense reference.
    #[test]
    fn dense_random_factor_matches_reference() {
        for &(m, seed) in &[(50usize, 11u64), (200usize, 12u64)] {
            let mut rng = Rng::new(seed);
            let cols: Vec<Vec<(usize, f64)>> = (0..m)
                .map(|_| (0..m).map(|r| (r, rng.f())).collect())
                .collect();
            let dense = Dense::factor(m, &cols).expect("reference factor");
            let mut eng = LuEngine::new(m);
            eng.factor(&refs(&cols)).expect("engine factor");
            assert_multipliers_bounded(&eng);
            assert_eq!(eng.updates(), 0);
            for _ in 0..3 {
                let b: Vec<f64> = (0..m).map(|_| rng.f()).collect();
                let mut x = b.clone();
                eng.ftran(&mut x);
                let xref = dense.solve(&b);
                let tol = 1e-8 * scale_of(&xref);
                assert!(max_diff(&x, &xref) <= tol, "ftran m={m}");
                let c: Vec<f64> = (0..m).map(|_| rng.f()).collect();
                let mut y = c.clone();
                eng.btran(&mut y);
                let yref = dense.solve_t(&c);
                let tol = 1e-8 * scale_of(&yref);
                assert!(max_diff(&y, &yref) <= tol, "btran m={m}");
            }
        }
    }

    /// A sparse, certainly-nonsingular random basis: a signed scaled
    /// permutation plus a few small off-diagonal entries per column.
    fn random_sparse_basis(m: usize, rng: &mut Rng) -> Vec<Vec<(usize, f64)>> {
        let mut perm: Vec<usize> = (0..m).collect();
        for i in (1..m).rev() {
            let j = rng.below(i + 1);
            perm.swap(i, j);
        }
        (0..m)
            .map(|c| {
                let sign = if rng.next() & 1 == 0 { 1.0 } else { -1.0 };
                let mut col = vec![(perm[c], sign * (0.5 + rng.f().abs() * 1.5))];
                for _ in 0..3 {
                    let r = rng.below(m);
                    if col.iter().all(|&(rr, _)| rr != r) {
                        col.push((r, 0.4 * rng.f()));
                    }
                }
                col
            })
            .collect()
    }

    fn random_sparse_col(m: usize, rng: &mut Rng) -> Vec<(usize, f64)> {
        let sign = if rng.next() & 1 == 0 { 1.0 } else { -1.0 };
        let mut col = vec![(rng.below(m), sign * (0.5 + rng.f().abs() * 1.5))];
        for _ in 0..3 {
            let r = rng.below(m);
            if col.iter().all(|&(rr, _)| rr != r) {
                col.push((r, 0.5 * rng.f()));
            }
        }
        col
    }

    /// Every piece of engine state a solve can observe, in a form two engines
    /// can be compared on EXACTLY (bit patterns, not tolerances). Used to hold
    /// the two spike arms to byte-identity rather than to agreement.
    #[derive(PartialEq, Eq, Debug)]
    struct StateSnapshot {
        stage_row: Vec<usize>,
        row_stage: Vec<usize>,
        stage_pos: Vec<usize>,
        pos_stage: Vec<usize>,
        lcols: Vec<Vec<(usize, u64)>>,
        lnnz: usize,
        udiag: Vec<u64>,
        urows: Vec<Vec<(usize, u64)>>,
        ucols: Vec<Vec<usize>>,
        unnz: usize,
        uorder: Vec<usize>,
        upos: Vec<usize>,
        etas: Vec<(usize, Vec<(usize, u64)>)>,
        eta_nnz: usize,
        n_updates: usize,
    }

    fn state_snapshot(eng: &LuEngine) -> StateSnapshot {
        // `to_bits` so that "equal" means the identical float, and so a NaN
        // that should not be there compares unequal to a good value rather
        // than to nothing.
        let bits = |rows: &Vec<Vec<(usize, f64)>>| -> Vec<Vec<(usize, u64)>> {
            rows.iter()
                .map(|r| r.iter().map(|&(c, x)| (c, x.to_bits())).collect())
                .collect()
        };
        StateSnapshot {
            stage_row: eng.stage_row.clone(),
            row_stage: eng.row_stage.clone(),
            stage_pos: eng.stage_pos.clone(),
            pos_stage: eng.pos_stage.clone(),
            lcols: bits(&eng.lcols),
            lnnz: eng.lnnz,
            udiag: eng.udiag.iter().map(|x| x.to_bits()).collect(),
            urows: bits(&eng.urows),
            ucols: eng.ucols.clone(),
            unnz: eng.unnz,
            uorder: eng.uorder.clone(),
            upos: eng.upos.clone(),
            etas: eng
                .etas
                .iter()
                .map(|e| {
                    (
                        e.row,
                        e.terms.iter().map(|&(c, x)| (c, x.to_bits())).collect(),
                    )
                })
                .collect(),
            eta_nnz: eng.eta_nnz,
            n_updates: eng.n_updates,
        }
    }

    /// The sparse spike build is only allowed to be a PERFORMANCE decision, so
    /// prove it is one: drive the identical update sequence through two
    /// engines, one pinned to each arm, and require byte-identical internal
    /// state after every accepted update — same U rows in the same order, same
    /// `ucols`, same pivot order, same eta terms, same float bit patterns.
    ///
    /// That is a strictly stronger statement than "the solves agree to
    /// tolerance", and it is what lets the density gate be tuned freely: a
    /// mis-set gate can then only cost time, never an answer.
    ///
    /// SCOPE, stated because it is easy to over-read: `random_sparse_basis`
    /// has a DENSE inverse, so the alphas here are ~100% dense and the marked
    /// set is all of `0..m`. That makes this the worst-case-density end of the
    /// sparse arm — it covers the scatter, the re-clears, the reject paths and
    /// the arithmetic, but NOT the closure's ability to find fill-in, because
    /// with every row already seeded the closure has nothing left to find.
    /// (Confirmed by sabotage: dropping an entry from the `ucols` closure
    /// leaves this test GREEN.) The skipping regime is
    /// `long_sparse_spike_chain_matches_fresh_factor`'s job.
    #[test]
    fn sparse_and_dense_spike_arms_agree_bit_for_bit() {
        let m = 240usize;
        let mut rng = Rng::new(0xb17_1de7);
        let cols = random_sparse_basis(m, &mut rng);

        let mut dense_eng = LuEngine::new(m);
        dense_eng.force_spike_arm(Some(false));
        dense_eng.factor(&refs(&cols)).expect("dense-arm factor");
        let mut sparse_eng = LuEngine::new(m);
        sparse_eng.force_spike_arm(Some(true));
        sparse_eng.factor(&refs(&cols)).expect("sparse-arm factor");
        assert_eq!(
            state_snapshot(&dense_eng),
            state_snapshot(&sparse_eng),
            "the two engines did not even start equal"
        );

        let mut accepted = 0usize;
        let mut attempts = 0usize;
        let mut rejects = 0usize;
        while accepted < 150 && attempts < 4000 {
            attempts += 1;
            let p = rng.below(m);
            let cand = random_sparse_col(m, &mut rng);
            let mut alpha = vec![0.0f64; m];
            for &(r, x) in &cand {
                alpha[r] += x;
            }
            // FTRAN through the dense-arm engine, then hand the SAME vector to
            // both — the input must be identical for the outputs to be
            // comparable at all.
            dense_eng.ftran(&mut alpha);
            let nz: Vec<usize> = (0..m).filter(|&i| alpha[i] != 0.0).collect();
            let d_res = dense_eng.update_nz(p, &alpha, &nz);
            let s_res = sparse_eng.update_nz(p, &alpha, &nz);
            assert_eq!(d_res, s_res, "arms disagreed on accept/reject at {p}");
            assert_eq!(
                state_snapshot(&dense_eng),
                state_snapshot(&sparse_eng),
                "arms diverged after {accepted} accepted updates (attempt {attempts})"
            );
            if d_res.is_err() {
                rejects += 1;
                continue;
            }
            accepted += 1;

            // Solves too, exactly — the snapshot covers the representation,
            // this covers the code paths that read it.
            let b: Vec<f64> = (0..m).map(|_| rng.f()).collect();
            let mut xd = b.clone();
            dense_eng.ftran(&mut xd);
            let mut xs = b.clone();
            sparse_eng.ftran(&mut xs);
            assert_eq!(xd, xs, "ftran differs after {accepted} updates");
            let mut yd = b.clone();
            dense_eng.btran(&mut yd);
            let mut ys = b;
            sparse_eng.btran(&mut ys);
            assert_eq!(yd, ys, "btran differs after {accepted} updates");
        }
        assert_eq!(accepted, 150, "not enough accepted updates to be a test");
        // The reject paths must have been exercised too — they are where the
        // sparse arm's new re-clear obligation lives.
        assert!(
            rejects > 0,
            "no update was ever rejected: reject paths untested"
        );
    }

    /// A basis whose INVERSE is genuinely sparse, which `random_sparse_basis`
    /// is not: a sparse random matrix has a dense inverse, so `B^-1 a` there
    /// covers 93-98% of `m` (measured) and the sparse spike would mark
    /// essentially all of `U` — a test that never exercises any skipping.
    ///
    /// Block-diagonal-with-coupling reproduces the regime the sparse arm is
    /// FOR: uccase12's FTRAN reach is 0.46% of m and physiciansched6-2's is
    /// 4.4%. Each column's pivot entry stays inside its own block (the pivot
    /// rows of a block are a permutation of that block's rows, so the basis is
    /// nonsingular by construction) and a quarter of the columns reach one row
    /// into an earlier block, which is what produces real cross-block fill for
    /// the `ucols` closure to have to find.
    fn block_sparse_basis(m: usize, blk: usize, rng: &mut Rng) -> Vec<Vec<(usize, f64)>> {
        let nblocks = m / blk;
        let mut cols: Vec<Vec<(usize, f64)>> = vec![Vec::new(); m];
        for g in 0..nblocks {
            let base = g * blk;
            let mut perm: Vec<usize> = (0..blk).collect();
            for i in (1..blk).rev() {
                let j = rng.below(i + 1);
                perm.swap(i, j);
            }
            for j in 0..blk {
                let c = base + j;
                let sign = if rng.next() & 1 == 0 { 1.0 } else { -1.0 };
                let mut col = vec![(base + perm[j], sign * (1.0 + rng.f().abs()))];
                for _ in 0..2 {
                    let r = base + rng.below(blk);
                    if col.iter().all(|&(rr, _)| rr != r) {
                        col.push((r, 0.3 * rng.f()));
                    }
                }
                if g > 0 && rng.below(4) == 0 {
                    let r = rng.below(base);
                    if col.iter().all(|&(rr, _)| rr != r) {
                        col.push((r, 0.2 * rng.f()));
                    }
                }
                cols[c] = col;
            }
        }
        cols
    }

    /// A replacement column for slot `p`, keeping `p`'s block structure (so
    /// the basis stays nonsingular often enough for a long chain to run).
    fn block_sparse_col(blk: usize, p: usize, rng: &mut Rng) -> Vec<(usize, f64)> {
        let base = (p / blk) * blk;
        let sign = if rng.next() & 1 == 0 { 1.0 } else { -1.0 };
        let mut col = vec![(base + rng.below(blk), sign * (1.0 + rng.f().abs()))];
        for _ in 0..2 {
            let r = base + rng.below(blk);
            if col.iter().all(|&(rr, _)| rr != r) {
                col.push((r, 0.3 * rng.f()));
            }
        }
        if base > 0 && rng.below(4) == 0 {
            let r = rng.below(base);
            if col.iter().all(|&(rr, _)| rr != r) {
                col.push((r, 0.2 * rng.f()));
            }
        }
        col
    }

    /// A pattern bug in the sparse spike — a missed fill-in, a stale `ucols`
    /// id, a mark that never got set — does not show up as noise. It shows up
    /// as a single dropped `U` entry: invisible for a few updates, then
    /// compounding. The existing 30-update / m=60 chain is too small to reach
    /// that, and (see `block_sparse_basis`) its alphas are ~100% dense, so it
    /// cannot exercise skipping at all.
    ///
    /// So: a LONG chain (200 accepted updates) on an m = 960 basis whose
    /// inverse is genuinely sparse, driven through BOTH arms in lockstep off
    /// the same FTRAN, with
    ///
    /// * byte-identical internal state required at EVERY step — zero
    ///   tolerance, and immune to the accumulated Forrest–Tomlin drift that
    ///   any absolute comparison at update 130+ has to make room for; and
    /// * ftran / ftran_nz / btran re-checked at every step against a FRESH
    ///   factorization of the current basis.
    ///
    /// The test also asserts the sparse arm is actually SKIPPING (its marked
    /// set stays under a fifth of m), because a sparse test that silently
    /// marks every row proves nothing.
    ///
    /// Non-vacuity verified by sabotage: dropping one entry from the `ucols`
    /// closure makes this fail; reverting makes it green again.
    #[test]
    fn long_sparse_spike_chain_matches_fresh_factor() {
        let m = 960usize;
        let blk = 8usize;
        let mut rng = Rng::new(0x5da2_5e11);
        let mut cols = block_sparse_basis(m, blk, &mut rng);

        let mut eng = LuEngine::new(m);
        eng.force_spike_arm(Some(true));
        eng.factor(&refs(&cols)).expect("initial factor");
        let mut dense_eng = LuEngine::new(m);
        dense_eng.force_spike_arm(Some(false));
        dense_eng
            .factor(&refs(&cols))
            .expect("initial dense-arm factor");

        let mut accepted = 0usize;
        let mut attempts = 0usize;
        let mut checked = 0usize;
        let mut sum_pat = 0usize;
        let mut sum_nz = 0usize;
        while accepted < 200 && attempts < 8000 {
            attempts += 1;
            let p = rng.below(m);
            let cand = block_sparse_col(blk, p, &mut rng);
            let mut alpha = vec![0.0f64; m];
            for &(r, x) in &cand {
                alpha[r] += x;
            }
            eng.ftran(&mut alpha);
            let nz: Vec<usize> = (0..m).filter(|&i| alpha[i] != 0.0).collect();
            let res = eng.update_nz(p, &alpha, &nz);
            assert_eq!(
                res,
                dense_eng.update_nz(p, &alpha, &nz),
                "arms disagreed on accept/reject at attempt {attempts}"
            );
            assert_eq!(
                state_snapshot(&eng),
                state_snapshot(&dense_eng),
                "arms diverged after {accepted} accepted updates"
            );
            if res.is_err() {
                continue;
            }
            cols[p] = cand;
            accepted += 1;
            sum_nz += nz.len();
            sum_pat += eng.u_pat.len();
            eng.assert_well_formed();

            // Every step, not every tenth: a dropped entry has to be caught
            // while its effect is still one entry wide.
            let mut fresh = LuEngine::new(m);
            fresh.factor(&refs(&cols)).expect("fresh factor");
            for _ in 0..2 {
                let b: Vec<f64> = (0..m).map(|_| 0.25 + rng.f()).collect();
                let mut got = b.clone();
                eng.ftran(&mut got);
                let mut want = b.clone();
                fresh.ftran(&mut want);
                let tol = 1e-6 * scale_of(&want);
                assert!(
                    max_diff(&got, &want) <= tol,
                    "update {accepted}: sparse-spike ftran drift {:.3e} > {tol:.3e}",
                    max_diff(&got, &want)
                );

                // The sparse solve as well: it consumes `ucols`, which the
                // spike build rewrites wholesale through `newpat`, so a
                // pattern that is right for the dense walk but wrong for the
                // reach shows here and nowhere else.
                let mut rhs = vec![0.0f64; m];
                let mut rnz = Vec::new();
                for _ in 0..6 {
                    let r = rng.below(m);
                    if rhs[r] == 0.0 {
                        rhs[r] = 0.5 + rng.f();
                        rnz.push(r);
                    }
                }
                let mut got_sparse = rhs.clone();
                eng.ftran_nz(&mut got_sparse, &mut rnz);
                let mut want_sparse = rhs.clone();
                fresh.ftran(&mut want_sparse);
                let tol = 1e-6 * scale_of(&want_sparse);
                assert!(
                    max_diff(&got_sparse, &want_sparse) <= tol,
                    "update {accepted}: sparse-spike ftran_nz drift"
                );

                let mut got_t = b.clone();
                eng.btran(&mut got_t);
                let mut want_t = b;
                fresh.btran(&mut want_t);
                let tol = 1e-6 * scale_of(&want_t);
                assert!(
                    max_diff(&got_t, &want_t) <= tol,
                    "update {accepted}: sparse-spike btran drift {:.3e} > {tol:.3e}",
                    max_diff(&got_t, &want_t)
                );
                checked += 1;
            }
        }
        assert_eq!(accepted, 200, "not enough accepted updates to be a test");
        assert_eq!(checked, 400);
        // Non-vacuity of the SPARSITY, not just of the checks: if the marked
        // set were most of `m` the sparse arm would be doing the dense arm's
        // work and this test would prove nothing about skipping. Measured on
        // this basis: mean |supp(alpha)| = 63 of 960 (6.6%, i.e. between
        // physiciansched6-2's 4.4% and neos-960392's 16%) and a mean marked
        // set well under a quarter of m, so the arm really is skipping most
        // rows on most calls.
        let mean_nz = sum_nz / accepted;
        let mean_pat = sum_pat / accepted;
        assert!(
            mean_nz * 8 < m && mean_pat * 4 < m,
            "the sparse arm was not actually skipping: mean |supp(alpha)| = \
             {mean_nz}, mean |M| = {mean_pat}, m = {m}"
        );
    }

    /// `update_nz`'s assembled diagonal `d` and its spike norm `vmax`,
    /// recomputed OUTSIDE the engine so a test can say WHICH rejection branch
    /// an attempt lands on.
    ///
    /// This exists because the two declines are indistinguishable from the
    /// caller's side — both are `Err(Singular { position })` — and that is
    /// precisely how one of them ended up with no coverage. Measured on the
    /// two random-chain tests as they stood: 150 sparse entries / 12 rejects
    /// and 200 entries / 38 rejects, and EVERY ONE of those 50 rejects was the
    /// O(1) pivot-identity prediction at the top of `update_nz`, which returns
    /// before `w`/`v`/`pat` are touched and so has nothing to put back. Zero
    /// reached the growth guard, which is the branch that does.
    ///
    /// The recomputation is the DENSE arm's own build followed by the same
    /// elimination: the engine walks touched columns out of a min-heap on
    /// `upos`, and a straight sweep over `uorder` visits the same columns in
    /// the same order (a column the engine never pushes holds `res == 0.0`,
    /// which both forms skip), so `d` comes out with the same operations in
    /// the same sequence. Classification, not a tolerance, is all it is used
    /// for — the constructions it serves sit a factor of 2-4 clear of every
    /// threshold, far outside the rounding it could plausibly differ by.
    fn reference_spike_diag(eng: &LuEngine, leaving_pos: usize, alpha: &[f64]) -> (f64, f64) {
        let m = eng.m;
        let t = eng.pos_stage[leaving_pos];
        let mut w = vec![0.0f64; m];
        for (k, wk) in w.iter_mut().enumerate() {
            *wk = alpha[eng.stage_pos[k]];
        }
        let mut v = vec![0.0f64; m];
        let mut vmax = 0.0f64;
        for k in 0..m {
            let mut s = eng.udiag[k] * w[k];
            for &(c, uv) in &eng.urows[k] {
                s += uv * w[c];
            }
            v[k] = s;
            if s.abs() > vmax {
                vmax = s.abs();
            }
        }
        let mut res = vec![0.0f64; m];
        for &(c, uv) in &eng.urows[t] {
            res[c] = uv;
        }
        let mut d = v[t];
        for &c in &eng.uorder {
            let val = res[c];
            res[c] = 0.0;
            if val == 0.0 {
                continue;
            }
            let mu = val / eng.udiag[c];
            d -= mu * v[c];
            for &(c2, v2) in &eng.urows[c] {
                res[c2] -= mu * v2;
            }
        }
        (d, vmax)
    }

    /// An `alpha` that PASSES the early pivot-identity prediction and then
    /// FAILS the growth guard — the input shape the sparse arm's late re-clear
    /// exists for and that no random chain ever produced.
    ///
    /// The two checks look at different things, which is the whole opening.
    /// The early one is `|udiag[t] · alpha[leaving_pos]| > UPDATE_PIVOT_TOL`,
    /// an ABSOLUTE floor on the new diagonal. The late one adds
    /// `|d| >= FT_REL_PIVOT_TOL · vmax`, a floor RELATIVE to the spike it came
    /// out of. So the target is a diagonal that is comfortably nonzero on its
    /// own but negligible against a large spike: here `d = 2e-9` (2x clear of
    /// the absolute floor) against `vmax = 8e3` (whose relative floor is
    /// 8e-9, 4x above `d`). `vmax` stays under `BIG_SPIKE_NORM` on purpose —
    /// cross it and the guard relaxes to the `f64` floor and stops rejecting.
    ///
    /// The bulk of `alpha` is a random sparse direction rescaled to hit that
    /// `vmax`; the pivot entry is then set from the Forrest-Tomlin identity
    /// `d = udiag[t] · alpha[leaving_pos]`, which is what makes `d` settable
    /// independently of the spike's size. Nothing about this is a fake input:
    /// `alpha` is `B^-1 a` for the entering column `a = B · alpha`, i.e. a
    /// column that is a large combination of the OTHER basis columns plus a
    /// vanishing amount of the one it would replace — a genuinely
    /// near-singular basis change, which is exactly what the growth guard is
    /// there to decline.
    ///
    /// `bulk` is how many entries that direction gets, which is also what
    /// decides the arm the `Auto` gate routes the call to — the density knob
    /// `one_engine_alternating_spike_arms_matches_pinned_arms` turns.
    fn late_rejecting_alpha(
        eng: &LuEngine,
        leaving_pos: usize,
        bulk: usize,
        rng: &mut Rng,
    ) -> Vec<f64> {
        let m = eng.m;
        let t = eng.pos_stage[leaving_pos];
        let mut alpha = vec![0.0f64; m];
        for _ in 0..bulk {
            let r = rng.below(m);
            if r != leaving_pos {
                alpha[r] = 0.5 + rng.f();
            }
        }
        let (_, vmax0) = reference_spike_diag(eng, leaving_pos, &alpha);
        if vmax0 > 0.0 {
            let scale = 8e3 / vmax0;
            for x in alpha.iter_mut() {
                *x *= scale;
            }
        }
        alpha[leaving_pos] = 2e-9 / eng.udiag[t];
        alpha
    }

    /// The sparse arm's LATE reject must put back the scratch it dirtied.
    ///
    /// `update_nz` declines in two places. The early one is an O(1) check that
    /// returns before `w`/`v`/`pat` exist, so it owes nothing. The late one —
    /// the growth guard on the assembled diagonal — runs after the sparse arm
    /// has scattered a spike into `v` at every marked stage, and the sparse
    /// arm's whole contract is that `v` is all-zero on entry (it reads rows it
    /// never writes). So that branch carries a `for &k in pat { v[k] = 0.0 }`,
    /// and until this test nothing could fail if it were deleted.
    ///
    /// That is not a guess. Counting rejects by branch across the two random
    /// chains (`sparse_and_dense_spike_arms_agree_bit_for_bit`,
    /// `long_sparse_spike_chain_matches_fresh_factor`) gives 50 rejects, ALL
    /// of them early, 0 late — over 54,000+ sparse calls the re-clear can be
    /// deleted and the suite stays green. Once the branch is actually reached,
    /// the same deletion changes 23 accept/reject decisions.
    ///
    /// Random inputs do not find it because the two checks agree except in a
    /// narrow window; `late_rejecting_alpha` constructs that window directly.
    /// The count of late rejects is asserted nonzero so this cannot quietly
    /// decay back into another early-reject test if the checks move.
    ///
    /// Two independent tripwires fire on a leak:
    ///
    /// * `assert_well_formed` right after the decline — `u_v_dirty` is down on
    ///   a sparse-pinned engine, so "clean-marked spike scratch holds a
    ///   nonzero" trips immediately; and
    /// * the byte-identical comparison against the dense-arm engine on the
    ///   FOLLOWING accepted update, which is where a stale `v[c]` is actually
    ///   read: `d` subtracts `mu · v[c]` over the eliminated columns, and those
    ///   are not confined to the marked set — outside it the code is entitled
    ///   to read the exact `0.0` the dense arm would have computed.
    ///
    /// Measured on this seed: 47 attempts, 47 of them landing in the window,
    /// 40 accepted updates interleaved. Deleting the re-clear fails this test
    /// on the first attempt (`clean-marked spike scratch holds a nonzero`)
    /// while every other test in the crate stays green.
    #[test]
    fn sparse_arm_late_reject_re_clears_its_spike_scratch() {
        let m = 240usize;
        let blk = 8usize;
        let mut rng = Rng::new(0x1a7e_5eed);
        let mut cols = block_sparse_basis(m, blk, &mut rng);

        let mut sparse_eng = LuEngine::new(m);
        sparse_eng.force_spike_arm(Some(true));
        sparse_eng.factor(&refs(&cols)).expect("sparse-arm factor");
        let mut dense_eng = LuEngine::new(m);
        dense_eng.force_spike_arm(Some(false));
        dense_eng.factor(&refs(&cols)).expect("dense-arm factor");
        assert_eq!(
            state_snapshot(&sparse_eng),
            state_snapshot(&dense_eng),
            "the two engines did not even start equal"
        );

        let mut late = 0usize;
        let mut accepted = 0usize;
        let mut attempts = 0usize;
        while accepted < 40 && attempts < 2000 {
            attempts += 1;
            let p = rng.below(m);

            // ---- the constructed late reject -----------------------------
            let alpha = late_rejecting_alpha(&sparse_eng, p, 20, &mut rng);
            let nz: Vec<usize> = (0..m).filter(|&i| alpha[i] != 0.0).collect();
            let t = sparse_eng.pos_stage[p];
            let d_pred = sparse_eng.udiag[t] * alpha[p];
            let (d_ref, vmax_ref) = reference_spike_diag(&sparse_eng, p, &alpha);
            let early_passes = d_pred.is_finite() && d_pred.abs() > UPDATE_PIVOT_TOL;
            let guard_fires = !d_ref.is_finite()
                || d_ref.abs() <= UPDATE_PIVOT_TOL
                || d_ref.abs() < ft_rel_pivot_tol(vmax_ref) * vmax_ref;
            if early_passes && guard_fires {
                // Everything the engine may not have changed, captured before.
                let before = state_snapshot(&sparse_eng);
                let probe: Vec<f64> = (0..m).map(|_| 0.25 + rng.f()).collect();
                let mut ftran_before = probe.clone();
                sparse_eng.ftran(&mut ftran_before);
                let mut btran_before = probe.clone();
                sparse_eng.btran(&mut btran_before);

                assert_eq!(
                    sparse_eng.update_nz(p, &alpha, &nz),
                    Err(Singular { position: p }),
                    "constructed late-reject alpha was ACCEPTED at attempt \
                     {attempts}: d = {d_ref:.6e}, vmax = {vmax_ref:.6e}"
                );
                late += 1;

                // Tripwire 1: the invariant itself, checked where it is owed.
                sparse_eng.assert_well_formed();
                assert_eq!(
                    state_snapshot(&sparse_eng),
                    before,
                    "late-rejected update changed engine state (attempt {attempts})"
                );
                let mut ftran_after = probe.clone();
                sparse_eng.ftran(&mut ftran_after);
                assert_eq!(ftran_before, ftran_after, "ftran moved under a decline");
                let mut btran_after = probe;
                sparse_eng.btran(&mut btran_after);
                assert_eq!(btran_before, btran_after, "btran moved under a decline");

                // The dense arm must decline the same input identically — the
                // arm choice stays a pure performance decision on the reject
                // paths too, not only on the accepted ones.
                assert_eq!(
                    dense_eng.update_nz(p, &alpha, &nz),
                    Err(Singular { position: p }),
                    "arms disagreed on the late reject at attempt {attempts}"
                );
                dense_eng.assert_well_formed();
                assert_eq!(
                    state_snapshot(&sparse_eng),
                    state_snapshot(&dense_eng),
                    "arms diverged over a late reject at attempt {attempts}"
                );
            }

            // ---- a genuine update, which is what READS a leaked spike -----
            let cand = block_sparse_col(blk, p, &mut rng);
            let mut real_alpha = vec![0.0f64; m];
            for &(r, x) in &cand {
                real_alpha[r] += x;
            }
            sparse_eng.ftran(&mut real_alpha);
            let real_nz: Vec<usize> = (0..m).filter(|&i| real_alpha[i] != 0.0).collect();
            let res = sparse_eng.update_nz(p, &real_alpha, &real_nz);
            assert_eq!(
                res,
                dense_eng.update_nz(p, &real_alpha, &real_nz),
                "arms disagreed on accept/reject after a late reject (attempt {attempts})"
            );
            // Tripwire 2: a stale `v[c]` poisons `d` here, in the eliminated
            // columns outside this call's own marked set.
            assert_eq!(
                state_snapshot(&sparse_eng),
                state_snapshot(&dense_eng),
                "arms diverged on the update following a late reject (attempt {attempts})"
            );
            if res.is_err() {
                continue;
            }
            cols[p] = cand;
            accepted += 1;

            let mut fresh = LuEngine::new(m);
            fresh.factor(&refs(&cols)).expect("fresh factor");
            let b: Vec<f64> = (0..m).map(|_| 0.25 + rng.f()).collect();
            let mut got = b.clone();
            sparse_eng.ftran(&mut got);
            let mut want = b;
            fresh.ftran(&mut want);
            let tol = 1e-6 * scale_of(&want);
            assert!(
                max_diff(&got, &want) <= tol,
                "update {accepted}: ftran drift {:.3e} > {tol:.3e} after a late reject",
                max_diff(&got, &want)
            );
        }
        assert_eq!(accepted, 40, "not enough accepted updates to be a test");
        // Non-vacuity: without this the test degrades silently into yet
        // another early-reject test the moment either check moves. Measured on
        // this seed: all 47 attempts land in the window, so the margin here is
        // enormous and the assert only fires if the construction stops
        // reaching the branch at all.
        assert!(
            late > 0,
            "the sparse arm's LATE reject was never reached: {late} of {attempts} \
             attempts, so the re-clear it owes is still untested"
        );
    }

    /// One engine, BOTH spike arms — the switch protocol `u_w_dirty` /
    /// `u_v_dirty` exist for, and which nothing in the crate exercised.
    ///
    /// The two arms leave the scratch in incompatible states by design: the
    /// dense build overwrites `u_w`/`u_v` in full and so is entitled to leave
    /// them full of the last spike, while the sparse build writes only at
    /// `k in pat` and READS the rest, so it requires all-zero. A single engine
    /// crossing between them therefore owes one O(m) wipe at the crossing, and
    /// the dirty flags are how the crossing is detected. In production this is
    /// not an edge case: the `Auto` gate re-decides on every call from
    /// `nz.len()` and `unnz`, so a real engine crosses constantly.
    ///
    /// Instrumenting the crate's own lu suite with a per-engine arm-switch
    /// counter gave 381 sparse-arm calls, 485 dense-arm calls and 0 switches:
    /// every engine in every test is either pinned by `force_spike_arm` or
    /// lands on one side of the gate for its whole life. Sabotaging the wipe
    /// corrupts the factorization outright and nothing in the repo noticed.
    ///
    /// So: one engine that crosses, twice over.
    ///
    /// PHASE 1 goes through the REAL gate, with the call stream alternating
    /// between block-local candidate columns — whose FTRAN reach is small
    /// enough that `nz.len()·(m+unnz)·2 < m·m` routes many of them sparse, and
    /// which get denser as the eta file grows, so the gate genuinely changes
    /// its mind about them — and 200-entry probes from `late_rejecting_alpha`,
    /// which are over the threshold and route dense. The probes are
    /// DECLINED by construction, and that is the point: an accepted dense
    /// column would make `B^-1` dense, every later alpha dense with it, and
    /// the gate would have only one answer left for the rest of the run. A
    /// declined call still commits to an arm, still dirties the dense arm's
    /// scratch, and so still poses the switch. PHASE 2 flips `force_spike_arm`
    /// by hand on ACCEPTED updates, so the crossing is covered across commits
    /// as well, and stays covered if the gate's calibration ever moves.
    ///
    /// Two pinned reference engines are fed the identical inputs and must stay
    /// byte-identical throughout, which is what turns "the wipe was skipped"
    /// into a failure rather than into drift someone tolerates.
    ///
    /// The arm actually taken is READ OFF the engine rather than re-derived
    /// from the gate formula under test: `u_pat` is the sparse build's marked
    /// set, which it always seeds with the pivot stage, and which the dense
    /// build clears and never pushes to. Non-empty means sparse. Sampling is
    /// skipped when the early pivot-identity check declined, because that path
    /// returns before `pat` is touched and leaves the previous call's value.
    ///
    /// Measured on this seed: 196 calls, 58 taken on the sparse arm, 126 on
    /// the dense arm, 107 crossings between them — against the 0 crossings the
    /// rest of the crate manages. Skipping the wipe (flags left up, so
    /// `assert_well_formed` cannot see it) diverges `unnz`/`urows` from the
    /// pinned engines on the second call: the sparse build reads the dense
    /// build's leftover gather at columns it never wrote and invents U
    /// entries. Skipping it while still lowering the flags trips
    /// `assert_well_formed` instead. Every other test in the crate stays green
    /// either way.
    #[test]
    fn one_engine_alternating_spike_arms_matches_pinned_arms() {
        let m = 240usize;
        let blk = 8usize;
        let mut rng = Rng::new(0x5117_c40e);
        let mut cols = block_sparse_basis(m, blk, &mut rng);

        // No `force_spike_arm`: this one goes through the production gate.
        let mut mixed = LuEngine::new(m);
        mixed.factor(&refs(&cols)).expect("mixed-arm factor");
        let mut sparse_ref = LuEngine::new(m);
        sparse_ref.force_spike_arm(Some(true));
        sparse_ref.factor(&refs(&cols)).expect("sparse-arm factor");
        let mut dense_ref = LuEngine::new(m);
        dense_ref.force_spike_arm(Some(false));
        dense_ref.factor(&refs(&cols)).expect("dense-arm factor");

        let mut switches = 0usize;
        let mut sparse_calls = 0usize;
        let mut dense_calls = 0usize;
        let mut prev_arm: Option<bool> = None;
        let mut accepted = 0usize;
        let mut attempts = 0usize;
        while accepted < 120 && attempts < 4000 {
            attempts += 1;
            let phase2 = accepted >= 60;
            // Phase 2 pins the arm and flips it by hand; phase 1 leaves
            // `spike_force` at its production `None` and lets the gate decide.
            let probe = !phase2 && attempts % 2 == 1;
            if phase2 {
                mixed.force_spike_arm(Some(attempts % 2 == 0));
            }
            let p = rng.below(m);
            let cand = block_sparse_col(blk, p, &mut rng);
            let alpha = if probe {
                late_rejecting_alpha(&mixed, p, 200, &mut rng)
            } else {
                let mut a = vec![0.0f64; m];
                for &(r, x) in &cand {
                    a[r] += x;
                }
                mixed.ftran(&mut a);
                a
            };
            let nz: Vec<usize> = (0..m).filter(|&i| alpha[i] != 0.0).collect();

            let t = mixed.pos_stage[p];
            let d_pred = mixed.udiag[t] * alpha[p];
            let reaches_arm = d_pred.is_finite() && d_pred.abs() > UPDATE_PIVOT_TOL;

            let res = mixed.update_nz(p, &alpha, &nz);
            if reaches_arm {
                let arm = !mixed.u_pat.is_empty();
                if arm {
                    sparse_calls += 1;
                } else {
                    dense_calls += 1;
                }
                if prev_arm.is_some_and(|q| q != arm) {
                    switches += 1;
                }
                prev_arm = Some(arm);
            }
            assert_eq!(
                res,
                sparse_ref.update_nz(p, &alpha, &nz),
                "mixed engine disagreed with the sparse-pinned one at attempt {attempts}"
            );
            assert_eq!(
                res,
                dense_ref.update_nz(p, &alpha, &nz),
                "mixed engine disagreed with the dense-pinned one at attempt {attempts}"
            );
            mixed.assert_well_formed();
            let snap = state_snapshot(&mixed);
            assert_eq!(
                snap,
                state_snapshot(&sparse_ref),
                "arm-switching engine diverged from the sparse-pinned one at \
                 attempt {attempts} (phase2 = {phase2}, probe = {probe})"
            );
            assert_eq!(
                snap,
                state_snapshot(&dense_ref),
                "arm-switching engine diverged from the dense-pinned one at \
                 attempt {attempts} (phase2 = {phase2}, probe = {probe})"
            );
            if probe {
                // A probe that was ACCEPTED would silently desync `cols` from
                // the engines and quietly densify the basis, which is the one
                // way this test could stop posing the switch at all.
                assert!(
                    res.is_err(),
                    "the dense arm-routing probe was accepted at attempt {attempts}"
                );
            }
            if res.is_err() {
                continue;
            }
            cols[p] = cand;
            accepted += 1;

            // Solves, and against a fresh factorization: byte-identical state
            // is the sharp check, but a switch that corrupts the shared
            // scratch has to show up in the answers too.
            let b: Vec<f64> = (0..m).map(|_| 0.25 + rng.f()).collect();
            let mut xm = b.clone();
            mixed.ftran(&mut xm);
            let mut xs = b.clone();
            sparse_ref.ftran(&mut xs);
            assert_eq!(xm, xs, "ftran differs after {accepted} updates");
            let mut ym = b.clone();
            mixed.btran(&mut ym);
            let mut ys = b.clone();
            dense_ref.btran(&mut ys);
            assert_eq!(ym, ys, "btran differs after {accepted} updates");
            if accepted % 10 == 0 {
                let mut fresh = LuEngine::new(m);
                fresh.factor(&refs(&cols)).expect("fresh factor");
                let mut want = b;
                fresh.ftran(&mut want);
                let tol = 1e-6 * scale_of(&want);
                assert!(
                    max_diff(&xm, &want) <= tol,
                    "update {accepted}: arm-switching ftran drift {:.3e} > {tol:.3e}",
                    max_diff(&xm, &want)
                );
            }
        }
        assert_eq!(accepted, 120, "not enough accepted updates to be a test");
        // Non-vacuity of the SWITCHING, not just of the checks: a test where
        // one engine happens to stay on one arm proves exactly what the
        // 0-switch measurement above proves, which is nothing.
        assert!(
            sparse_calls > 0 && dense_calls > 0 && switches > 0,
            "the engine never changed arms: {sparse_calls} sparse / \
             {dense_calls} dense calls, {switches} switches — the wipe the \
             dirty flags guard is still untested"
        );
    }

    /// (b) A chain of 30 accepted updates, each checked against a fresh
    /// factorization of the replaced basis and the dense reference.
    #[test]
    fn thirty_updates_match_fresh_factor() {
        let m = 60usize;
        let mut rng = Rng::new(77);
        let mut cols = random_sparse_basis(m, &mut rng);
        assert!(Dense::factor(m, &cols).is_some(), "test basis singular");
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&cols)).expect("initial factor");

        let mut accepted = 0usize;
        while accepted < 30 {
            let p = rng.below(m);
            let cand = random_sparse_col(m, &mut rng);
            // FTRAN of the candidate through the *current* factorization —
            // exactly what the simplex has in hand at pivot time.
            let mut alpha = vec![0.0f64; m];
            for &(r, v) in &cand {
                alpha[r] += v;
            }
            eng.ftran(&mut alpha);
            if eng.update(p, &alpha).is_err() {
                continue; // singular replacement — try another
            }
            cols[p] = cand;
            accepted += 1;
            assert_eq!(eng.updates(), accepted);

            let dense = Dense::factor(m, &cols).expect("updated basis singular");
            let mut fresh = LuEngine::new(m);
            fresh.factor(&refs(&cols)).expect("fresh factor");
            for _ in 0..2 {
                let b: Vec<f64> = (0..m).map(|_| rng.f()).collect();
                let mut x = b.clone();
                eng.ftran(&mut x);
                let mut xf = b.clone();
                fresh.ftran(&mut xf);
                let xref = dense.solve(&b);
                let tol = 1e-6 * scale_of(&xref);
                assert!(
                    max_diff(&x, &xf) <= tol,
                    "update {accepted}: ftran vs fresh"
                );
                assert!(
                    max_diff(&x, &xref) <= tol,
                    "update {accepted}: ftran vs dense"
                );
                let c: Vec<f64> = (0..m).map(|_| rng.f()).collect();
                let mut y = c.clone();
                eng.btran(&mut y);
                let yref = dense.solve_t(&c);
                let tol = 1e-6 * scale_of(&yref);
                assert!(
                    max_diff(&y, &yref) <= tol,
                    "update {accepted}: btran vs dense"
                );
            }
        }
    }

    /// `thirty_updates_match_fresh_factor` with the SPARSE arm pinned.
    ///
    /// The original is left exactly as it was — but at m = 60 with a 100%
    /// dense alpha the density gate always picks the dense arm, so as written
    /// it covers none of the new code. Pinning the arm puts the independent
    /// dense reference (`Dense::factor`/`solve`/`solve_t`) behind the sparse
    /// build too. This is an ADDITION to the guard, never a relaxation: the
    /// tolerances, the reference and the checks are the originals verbatim.
    #[test]
    fn thirty_updates_match_fresh_factor_with_sparse_spike_forced() {
        let m = 60usize;
        let mut rng = Rng::new(77);
        let mut cols = random_sparse_basis(m, &mut rng);
        assert!(Dense::factor(m, &cols).is_some(), "test basis singular");
        let mut eng = LuEngine::new(m);
        eng.force_spike_arm(Some(true));
        eng.factor(&refs(&cols)).expect("initial factor");

        let mut accepted = 0usize;
        while accepted < 30 {
            let p = rng.below(m);
            let cand = random_sparse_col(m, &mut rng);
            let mut alpha = vec![0.0f64; m];
            for &(r, v) in &cand {
                alpha[r] += v;
            }
            eng.ftran(&mut alpha);
            if eng.update(p, &alpha).is_err() {
                continue;
            }
            cols[p] = cand;
            accepted += 1;
            assert_eq!(eng.updates(), accepted);

            let dense = Dense::factor(m, &cols).expect("updated basis singular");
            let mut fresh = LuEngine::new(m);
            fresh.factor(&refs(&cols)).expect("fresh factor");
            for _ in 0..2 {
                let b: Vec<f64> = (0..m).map(|_| rng.f()).collect();
                let mut x = b.clone();
                eng.ftran(&mut x);
                let mut xf = b.clone();
                fresh.ftran(&mut xf);
                let xref = dense.solve(&b);
                let tol = 1e-6 * scale_of(&xref);
                assert!(
                    max_diff(&x, &xf) <= tol,
                    "update {accepted}: sparse-spike ftran vs fresh"
                );
                assert!(
                    max_diff(&x, &xref) <= tol,
                    "update {accepted}: sparse-spike ftran vs dense"
                );
                let c: Vec<f64> = (0..m).map(|_| rng.f()).collect();
                let mut y = c.clone();
                eng.btran(&mut y);
                let yref = dense.solve_t(&c);
                let tol = 1e-6 * scale_of(&yref);
                assert!(
                    max_diff(&y, &yref) <= tol,
                    "update {accepted}: sparse-spike btran vs dense"
                );
            }
        }
    }

    /// (c) Singular bases are rejected without touching the previous
    /// factorization; singular updates are rejected likewise.
    #[test]
    fn singular_rejected_engine_untouched() {
        let m = 10usize;
        let ident: Vec<Vec<(usize, f64)>> = (0..m).map(|r| vec![(r, 1.0)]).collect();
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&ident)).expect("identity factors");
        let probe: Vec<f64> = (0..m).map(|r| r as f64 - 4.0).collect();
        let mut before = probe.clone();
        eng.ftran(&mut before);

        // Structurally empty column: reported by slot, engine untouched.
        let mut bad = ident.clone();
        bad[3] = Vec::new();
        assert_eq!(
            eng.factor(&refs(&bad)),
            Err(FactorFail::Singular(Singular { position: 3 }))
        );

        // Duplicated column (rank deficiency found during elimination).
        let mut dup = ident.clone();
        dup[3] = vec![(5, 1.0)];
        let err = match eng.factor(&refs(&dup)).unwrap_err() {
            FactorFail::Singular(s) => s,
            FactorFail::OutOfBudget => panic!("duplicated column is singular, not over budget"),
        };
        // Columns 3 and 5 are both e_5; whichever pivots first empties the
        // other. Anything else means the failure was misattributed.
        assert!(
            err.position == 3 || err.position == 5,
            "position {}",
            err.position
        );

        // Both failures left the previous factorization bit-identical.
        let mut after = probe.clone();
        eng.ftran(&mut after);
        assert_eq!(before, after);

        // Singular update: replacing slot 3 with a copy of basis column 5
        // makes alpha[3] == 0, tripping the early FT pivot check.
        let mut alpha = vec![0.0f64; m];
        alpha[5] = 1.0;
        eng.ftran(&mut alpha);
        assert_eq!(eng.update(3, &alpha), Err(Singular { position: 3 }));
        assert_eq!(eng.updates(), 0);
        let mut after = probe.clone();
        eng.ftran(&mut after);
        assert_eq!(before, after);
    }

    /// (c') Fill DECLINE is fail-closed AND transactional. A dense basis whose
    /// L+U fill overruns a tiny budget must return `FactorFail::OutOfBudget`
    /// (never OOM, never a wrong `Singular`), and — like every other failure —
    /// leave the previous valid factorization bit-identical: a subsequent
    /// `ftran` matches the pre-decline solve exactly.
    #[test]
    fn over_budget_decline_leaves_factorization_intact() {
        let m = 60usize;
        let mut rng = Rng::new(2024);
        // A valid basis the engine factors under any real budget.
        let base = random_sparse_basis(m, &mut rng);
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&base)).expect("base basis factors");
        let probe: Vec<f64> = (0..m).map(|_| rng.f()).collect();
        let mut before = probe.clone();
        eng.ftran(&mut before);

        // A DENSE, diagonally-strong (so certainly non-singular) basis whose
        // Markowitz fill is Θ(m²) ≫ the budget: the meter trips on the first
        // step, before any singularity question could arise.
        let dense: Vec<Vec<(usize, f64)>> = (0..m)
            .map(|c| {
                (0..m)
                    .map(|r| (r, if r == c { 8.0 + rng.f() } else { rng.f() }))
                    .collect()
            })
            .collect();
        assert_eq!(
            eng.factor_within(&refs(&dense), 100),
            Err(FactorFail::OutOfBudget)
        );

        // The decline was transactional: `self` still represents `base`.
        let mut after = probe.clone();
        eng.ftran(&mut after);
        assert_eq!(before, after);

        // Sanity: the SAME dense basis factors fine under a generous budget,
        // proving the decline was the budget and not the basis.
        eng.factor_within(&refs(&dense), 10_000_000)
            .expect("dense basis factors under a generous budget");
    }

    /// The fill-budget env parse: valid positives win, everything else falls
    /// back to the 200M default (mirrors `parse_ft_growth_tol_override`).
    #[test]
    fn lu_max_fill_nnz_parse() {
        assert_eq!(parse_lu_max_fill_nnz(None), LU_MAX_FILL_NNZ_DEFAULT);
        assert_eq!(parse_lu_max_fill_nnz(Some("500")), 500);
        for invalid in ["0", "-1", "1.5", "NaN", "invalid", ""] {
            assert_eq!(
                parse_lu_max_fill_nnz(Some(invalid)),
                LU_MAX_FILL_NNZ_DEFAULT
            );
        }
    }

    /// (d) Near-singular and threshold pathology. A 1e-12 singleton pivot is
    /// below the absolute floor (singular at working precision). And a tiny
    /// entry with the *best* Markowitz count must be refused by the u = 0.1
    /// relative threshold — taking it would inject multipliers of order 1e7
    /// and wreck the factors; the multiplier bound proves it was refused.
    #[test]
    fn near_singular_and_threshold_pathology() {
        // (i) below the absolute pivot floor.
        let m = 4usize;
        let mut cols: Vec<Vec<(usize, f64)>> = (0..m).map(|r| vec![(r, 1.0)]).collect();
        cols[2] = vec![(2, 1e-12)];
        let mut eng = LuEngine::new(m);
        assert!(eng.factor(&refs(&cols)).is_err());

        // (ii) threshold steering. Column 0 holds a tiny entry at row 0
        // whose Markowitz count beats every alternative; row 0 and row 1
        // both carry healthy entries elsewhere so the basis is benign.
        let m = 6usize;
        let mut rng = Rng::new(5);
        let mut cols: Vec<Vec<(usize, f64)>> = Vec::new();
        // col 0: tiny (row 0) + unit (row 1)
        cols.push(vec![(0, 1e-7), (1, 1.0)]);
        // col 1: dense-ish, covers row 0 with a healthy entry
        cols.push(vec![(0, 1.0), (2, 0.8), (3, -0.6), (4, 0.3)]);
        // col 2: covers row 1 again plus others (inflates row 1's count)
        cols.push(vec![(1, 0.9), (2, -0.4), (5, 0.7)]);
        for c in 3..m {
            let col: Vec<(usize, f64)> = (0..m)
                .map(|r| (r, rng.f()))
                .filter(|&(r, _)| r != 0 || c == 4) // keep row 0 sparse
                .collect();
            cols.push(col);
        }
        let dense = Dense::factor(m, &cols).expect("reference factor");
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&cols)).expect("engine factor");
        // The tiny (0,0) entry must not have been pivoted: every multiplier
        // obeys the 1/u bound, impossible had 1e-7 divided a unit entry.
        assert_multipliers_bounded(&eng);
        let mut rng = Rng::new(6);
        for _ in 0..3 {
            let b: Vec<f64> = (0..m).map(|_| rng.f()).collect();
            let mut x = b.clone();
            eng.ftran(&mut x);
            let xref = dense.solve(&b);
            assert!(max_diff(&x, &xref) <= 1e-8 * scale_of(&xref));
        }
    }
    /// (e) `factor` on an engine that has absorbed updates must RESET the
    /// update state — the reviewer's highest-value missing case: deleting the
    /// eta/uorder reset at the end of `factor` passed every other test while
    /// guaranteeing silently wrong solves after the first routine refactor in
    /// production.
    #[test]
    fn refactor_after_updates_resets_cleanly() {
        let m = 40usize;
        let mut rng = Rng::new(1234);
        let mut cols = random_sparse_basis(m, &mut rng);
        assert!(Dense::factor(m, &cols).is_some(), "test basis singular");
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&cols)).expect("initial factor");

        let mut accepted = 0usize;
        while accepted < 10 {
            let p = rng.below(m);
            let cand = random_sparse_col(m, &mut rng);
            let mut alpha = vec![0.0f64; m];
            for &(r, v) in &cand {
                alpha[r] += v;
            }
            eng.ftran(&mut alpha);
            if eng.update(p, &alpha).is_err() {
                continue;
            }
            cols[p] = cand;
            accepted += 1;
        }
        assert_eq!(eng.updates(), 10);

        // Re-factor the SAME engine on the mutated basis.
        eng.factor(&refs(&cols)).expect("refactor after updates");
        assert_eq!(eng.updates(), 0, "update counter must reset");

        let mut fresh = LuEngine::new(m);
        fresh.factor(&refs(&cols)).expect("fresh factor");
        assert_eq!(
            eng.nnz(),
            fresh.nnz(),
            "a dirty engine's refactor must shed every update (etas, fill)"
        );
        let dense = Dense::factor(m, &cols).expect("reference");
        for _ in 0..3 {
            let b: Vec<f64> = (0..m).map(|_| rng.f()).collect();
            let mut x = b.clone();
            eng.ftran(&mut x);
            let xref = dense.solve(&b);
            assert!(max_diff(&x, &xref) <= 1e-6 * scale_of(&xref));
            let c: Vec<f64> = (0..m).map(|_| rng.f()).collect();
            let mut y = c.clone();
            eng.btran(&mut y);
            let yref = dense.solve_t(&c);
            assert!(max_diff(&y, &yref) <= 1e-6 * scale_of(&yref));
        }
    }

    /// (f) The LATE rejection path of `update` (assembled diagonal fails the
    /// relative-growth floor after passing the early prediction) must leave
    /// the engine bit-identical — the transactionality the early-path tests
    /// never exercise. Diagonal basis, spike with a 1e4-scale entry and a
    /// 2e-9 diagonal: passes `> UPDATE_PIVOT_TOL`, fails
    /// `>= FT_REL_PIVOT_TOL * vmax`.
    #[test]
    fn late_reject_is_transactional() {
        let m = 6usize;
        let ident: Vec<Vec<(usize, f64)>> = (0..m).map(|r| vec![(r, 1.0)]).collect();
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&ident)).expect("identity factors");
        let probe: Vec<f64> = (0..m).map(|r| 1.5 * r as f64 - 2.0).collect();
        let mut ftran_before = probe.clone();
        eng.ftran(&mut ftran_before);
        let mut btran_before = probe.clone();
        eng.btran(&mut btran_before);
        let (nnz0, upd0) = (eng.nnz(), eng.updates());

        // alpha = B^{-1} a for a = 2e-9 e_2 + 1e4 e_4 (B = I here).
        let mut alpha = vec![0.0f64; m];
        alpha[2] = 2e-9;
        alpha[4] = 1e4;
        assert_eq!(eng.update(2, &alpha), Err(Singular { position: 2 }));

        assert_eq!(eng.nnz(), nnz0);
        assert_eq!(eng.updates(), upd0);
        let mut ftran_after = probe.clone();
        eng.ftran(&mut ftran_after);
        assert_eq!(
            ftran_before, ftran_after,
            "ftran changed by rejected update"
        );
        let mut btran_after = probe.clone();
        eng.btran(&mut btran_after);
        assert_eq!(
            btran_before, btran_after,
            "btran changed by rejected update"
        );
    }

    #[test]
    fn nonfinite_update_input_is_transactional() {
        let m = 6usize;
        let ident: Vec<Vec<(usize, f64)>> = (0..m).map(|r| vec![(r, 1.0)]).collect();
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&ident)).expect("identity factors");
        let probe: Vec<f64> = (0..m).map(|r| 0.25 + r as f64).collect();
        let mut ftran_before = probe.clone();
        eng.ftran(&mut ftran_before);
        let mut btran_before = probe.clone();
        eng.btran(&mut btran_before);
        let (nnz0, upd0) = (eng.nnz(), eng.updates());

        let mut alpha = vec![0.0f64; m];
        alpha[0] = 1.0;
        alpha[3] = f64::NAN;
        assert_eq!(eng.update(0, &alpha), Err(Singular { position: 0 }));

        assert_eq!(eng.nnz(), nnz0);
        assert_eq!(eng.updates(), upd0);
        eng.assert_well_formed();
        let mut ftran_after = probe.clone();
        eng.ftran(&mut ftran_after);
        assert_eq!(
            ftran_before, ftran_after,
            "ftran changed by rejected non-finite update"
        );
        let mut btran_after = probe.clone();
        eng.btran(&mut btran_after);
        assert_eq!(
            btran_before, btran_after,
            "btran changed by rejected non-finite update"
        );
    }

    #[test]
    fn malformed_update_arguments_fail_closed_without_panicking() {
        let m = 5usize;
        let ident: Vec<Vec<(usize, f64)>> = (0..m).map(|r| vec![(r, 1.0)]).collect();
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&ident)).expect("identity factors");
        let probe: Vec<f64> = (0..m).map(|r| 0.75 + r as f64).collect();
        let mut before = probe.clone();
        eng.ftran(&mut before);
        let (nnz0, upd0) = (eng.nnz(), eng.updates());

        assert_eq!(
            eng.update(m, &[0.0; 5]),
            Err(Singular { position: m }),
            "out-of-range leaving position must be a closed failure"
        );
        assert_eq!(
            eng.update(0, &[1.0, 0.0]),
            Err(Singular { position: 0 }),
            "wrong-length FTRAN result must be a closed failure"
        );

        assert_eq!(eng.nnz(), nnz0);
        assert_eq!(eng.updates(), upd0);
        eng.assert_well_formed();
        let mut after = probe;
        eng.ftran(&mut after);
        assert_eq!(before, after, "malformed update arguments changed FTRAN");
    }

    /// (g) The sparse solves must agree with the dense ones bit-for-bit on
    /// the support and leave the scratch clean outside it — through factor
    /// AND through absorbed updates (etas change both reachability closures).
    #[test]
    fn sparse_solves_match_dense() {
        let m = 80usize;
        let mut rng = Rng::new(4242);
        let mut cols = random_sparse_basis(m, &mut rng);
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&cols)).expect("factor");

        let check = |eng: &mut LuEngine, label: &str, rng: &mut Rng| {
            for trial in 0..20 {
                // Sparse RHS with 1-4 nonzeros (unit vectors included).
                let mut x_dense = vec![0.0f64; m];
                let mut x_sparse = vec![0.0f64; m];
                let mut nz = Vec::new();
                let kn = 1 + rng.below(4);
                for _ in 0..kn {
                    let r = rng.below(m);
                    if x_dense[r] == 0.0 {
                        let v = rng.f() + 0.1;
                        x_dense[r] = v;
                        x_sparse[r] = v;
                        nz.push(r);
                    }
                }
                eng.ftran(&mut x_dense);
                eng.ftran_nz(&mut x_sparse, &mut nz);
                for r in 0..m {
                    assert!(
                        (x_dense[r] - x_sparse[r]).abs() <= 1e-12 * (1.0 + x_dense[r].abs()),
                        "{label} ftran trial {trial} row {r}: {} vs {}",
                        x_dense[r],
                        x_sparse[r]
                    );
                }
                let mut in_nz = vec![false; m];
                for &r in &nz {
                    in_nz[r] = true;
                }
                for r in 0..m {
                    if !in_nz[r] {
                        assert_eq!(x_sparse[r], 0.0, "{label}: stale nonzero outside nz");
                    }
                }

                // btran on a unit vector (the dual's rho pattern).
                let p = rng.below(m);
                let mut y_dense = vec![0.0f64; m];
                y_dense[p] = 1.0;
                let mut y_sparse = y_dense.clone();
                let mut ynz = vec![p];
                eng.btran(&mut y_dense);
                eng.btran_nz(&mut y_sparse, &mut ynz);
                for r in 0..m {
                    assert!(
                        (y_dense[r] - y_sparse[r]).abs() <= 1e-12 * (1.0 + y_dense[r].abs()),
                        "{label} btran trial {trial} row {r}"
                    );
                }
            }
        };
        check(&mut eng, "post-factor", &mut rng);

        let mut accepted = 0usize;
        while accepted < 15 {
            let pos = rng.below(m);
            let cand = random_sparse_col(m, &mut rng);
            let mut alpha = vec![0.0f64; m];
            for &(r, v) in &cand {
                alpha[r] += v;
            }
            eng.ftran(&mut alpha);
            if eng.update(pos, &alpha).is_err() {
                continue;
            }
            cols[pos] = cand;
            accepted += 1;
        }
        check(&mut eng, "post-updates", &mut rng);
    }

    /// A longer update chain aimed at the operational failure modes that are
    /// easy to miss with one-shot factors: lazy `ucols` staleness, eta-order
    /// mistakes, and scratch left dirty by sparse FTRAN/BTRAN. The dense
    /// reference is rebuilt from the current basis after every checkpoint, so
    /// this validates the accumulated update product, not just local pivots.
    #[test]
    fn long_update_chain_keeps_sparse_dense_and_reject_paths_consistent() {
        let m = 48usize;
        let mut rng = Rng::new(0x5eed_cafe);
        let mut cols = random_sparse_basis(m, &mut rng);
        let mut eng = LuEngine::new(m);
        eng.factor(&refs(&cols)).expect("initial factor");

        let check_all =
            |eng: &mut LuEngine, cols: &[Vec<(usize, f64)>], rng: &mut Rng, label: &str| {
                eng.assert_well_formed();
                let dense = Dense::factor(m, cols).expect("reference factor");
                for trial in 0..6 {
                    let mut rhs = vec![0.0f64; m];
                    let mut rhs_sparse = vec![0.0f64; m];
                    let mut nz = Vec::new();
                    for _ in 0..(1 + rng.below(5)) {
                        let r = rng.below(m);
                        if rhs[r] == 0.0 {
                            let v = 0.25 + rng.f();
                            rhs[r] = v;
                            rhs_sparse[r] = v;
                            nz.push(r);
                        }
                    }

                    let mut got = rhs.clone();
                    eng.ftran(&mut got);
                    let mut got_sparse = rhs_sparse;
                    eng.ftran_nz(&mut got_sparse, &mut nz);
                    let want = dense.solve(&rhs);
                    let tol = 1e-7 * scale_of(&want);
                    assert!(
                        max_diff(&got, &want) <= tol,
                        "{label} trial {trial}: dense ftran drift"
                    );
                    assert!(
                        max_diff(&got_sparse, &want) <= tol,
                        "{label} trial {trial}: sparse ftran drift"
                    );

                    let mut cost = vec![0.0f64; m];
                    let mut cnz = Vec::new();
                    for _ in 0..(1 + rng.below(4)) {
                        let p = rng.below(m);
                        if cost[p] == 0.0 {
                            cost[p] = 0.25 + rng.f();
                            cnz.push(p);
                        }
                    }
                    let mut got_t = cost.clone();
                    eng.btran(&mut got_t);
                    let mut got_t_sparse = cost.clone();
                    eng.btran_nz(&mut got_t_sparse, &mut cnz);
                    let want_t = dense.solve_t(&cost);
                    let tol = 1e-7 * scale_of(&want_t);
                    assert!(
                        max_diff(&got_t, &want_t) <= tol,
                        "{label} trial {trial}: dense btran drift"
                    );
                    assert!(
                        max_diff(&got_t_sparse, &want_t) <= tol,
                        "{label} trial {trial}: sparse btran drift"
                    );

                    eng.assert_well_formed();
                }
            };

        check_all(&mut eng, &cols, &mut rng, "initial");
        let mut accepted = 0usize;
        while accepted < 80 {
            let pos = rng.below(m);
            let cand = random_sparse_col(m, &mut rng);
            let mut trial_cols = cols.clone();
            trial_cols[pos] = cand.clone();
            if Dense::factor(m, &trial_cols).is_none() {
                continue;
            }

            let mut alpha = vec![0.0f64; m];
            for &(r, v) in &cand {
                alpha[r] += v;
            }
            eng.ftran(&mut alpha);
            if eng.update(pos, &alpha).is_err() {
                continue;
            }
            cols = trial_cols;
            accepted += 1;
            if accepted % 10 == 0 {
                check_all(
                    &mut eng,
                    &cols,
                    &mut rng,
                    &format!("after {accepted} updates"),
                );
            }
        }

        // After a long eta chain, a rejected singular replacement must remain
        // fully transactional. `alpha = e_q` is the FTRAN result for reusing
        // current basis column q; replacing p != q with it is rank-deficient
        // and must not perturb any solve state.
        let p = 0usize;
        let q = 1usize;
        let probe: Vec<f64> = (0..m).map(|i| 0.5 + i as f64 / 7.0).collect();
        let mut ftran_before = probe.clone();
        eng.ftran(&mut ftran_before);
        let mut btran_before = probe.clone();
        eng.btran(&mut btran_before);
        let mut alpha = vec![0.0f64; m];
        alpha[q] = 1.0;
        assert_eq!(eng.update(p, &alpha), Err(Singular { position: p }));
        eng.assert_well_formed();
        let mut ftran_after = probe.clone();
        eng.ftran(&mut ftran_after);
        let mut btran_after = probe;
        eng.btran(&mut btran_after);
        assert_eq!(ftran_before, ftran_after, "rejected update changed FTRAN");
        assert_eq!(btran_before, btran_after, "rejected update changed BTRAN");
    }
}
