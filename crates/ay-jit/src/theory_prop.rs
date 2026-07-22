// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JIT-compiled theory bound propagation for LIA/LRA.
//!
//! Replaces the interpreted per-variable atom scanning loop in
//! `LraSolver::propagate_var_atoms()` and
//! `compute_direct_bound_propagations_for_var()` with a pre-compiled
//! fast path using native i64/i128 arithmetic.
//!
//! ## Motivation
//!
//! The LRA/LIA bound propagation hot loop checks whether a variable's
//! current bounds imply the truth value of registered atoms. Each atom
//! has a `bound_value: BigRational` and the comparison
//! `current_bound <op> atom_bound` involves heap-allocated BigRational
//! arithmetic. In practice, >95% of LIA bounds are small integers that
//! fit in i64. Pre-extracting these values and using i128 cross-multiply
//! comparisons eliminates allocation and reduces per-atom cost from
//! ~50ns (BigRational) to ~2ns (i128 multiply + compare).
//!
//! ## Architecture
//!
//! This module lives in `ay-jit` which does NOT depend on `ay-theories`.
//! The caller (in ay-theories/lra) converts `AtomRef` and `Bound` into
//! the JIT's input types (`BoundAtom`, `SmallBound`).
//!
//! The current implementation is an "interpreted JIT" — a pre-compiled
//! data structure with a tight Rust loop. Future work can lower this to
//! native aarch64/x86_64 using the existing assembler infrastructure.
//!
//! ## Algorithm
//!
//! For a variable with atoms `{(k_i, is_upper_i, strict_i)}` and
//! current bounds `lb = p_l/q_l` (strict_l), `ub = p_u/q_u` (strict_u):
//!
//! For each atom with bound value `k = n/d`:
//!
//! **Upper atom** (`x <= k` or `x < k`):
//! - Implied TRUE if `ub <= k` (with strictness adjustments)
//! - Implied FALSE if `lb > k` (with strictness adjustments)
//!
//! **Lower atom** (`x >= k` or `x > k`):
//! - Implied TRUE if `lb >= k` (with strictness adjustments)
//! - Implied FALSE if `ub < k` (with strictness adjustments)
//!
//! For small-int atoms: `p/q <=> n/d` reduces to `p*d <=> n*q` using
//! i128 multiplication (2 MUL + 1 CMP, no allocation).

/// A pre-compiled bound atom extracted from an `AtomRef`.
///
/// Stores the bound value as i64 numerator/denominator when possible,
/// enabling i128 cross-multiply comparison instead of BigRational.
#[derive(Debug, Clone)]
pub struct BoundAtom {
    /// Index of this atom in the caller's atom array for this variable.
    /// Used to identify which atom was implied when returning results.
    pub atom_index: u32,
    /// Numerator of the bound value (valid when `is_small` is true).
    pub bound_numer: i64,
    /// Denominator of the bound value (valid when `is_small` is true, always > 0).
    pub bound_denom: i64,
    /// true for upper bound atoms (`x <= k` or `x < k`).
    pub is_upper: bool,
    /// true for strict comparisons (`<` or `>`).
    pub strict: bool,
    /// Whether the bound value fits in i64/i64 (Small path).
    /// When false, the atom is skipped by the fast path and must
    /// be handled by the fallback BigRational comparison.
    pub is_small: bool,
}

/// A variable bound value represented as i64 numerator/denominator.
///
/// The caller extracts this from `Rational::Small(n, d)`.
#[derive(Debug, Clone, Copy)]
pub struct SmallBound {
    /// Numerator (can be negative).
    pub numer: i64,
    /// Denominator (always > 0 after normalization).
    pub denom: i64,
    /// Whether this is a strict bound.
    pub strict: bool,
}

/// Result of checking a single atom: implied true, implied false, or unknown.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AtomImplication {
    /// The atom is implied to be true by the current bounds.
    ImpliedTrue,
    /// The atom is implied to be false by the current bounds.
    ImpliedFalse,
    /// Cannot determine implication from the current bounds (or atom is non-small).
    Unknown,
}

/// Result entry from propagation: which atom is implied and its truth value.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct PropagationResult {
    /// Index of the atom in the caller's atom array.
    pub atom_index: u32,
    /// Whether the atom is implied true (true) or false (false).
    pub implied_value: bool,
}

/// Pre-compiled per-variable bound propagation function.
///
/// After initial atom registration, the caller compiles a `VarPropagator`
/// for each variable that has bound atoms. During propagation, calling
/// `check_bounds()` with the current lb/ub values returns a list of
/// implied atoms without any BigRational allocation.
#[derive(Debug, Clone)]
pub struct VarPropagator {
    /// Pre-compiled atoms sorted by bound value for cache-friendly scanning.
    /// Upper atoms first (sorted by bound value ascending), then lower atoms
    /// (sorted by bound value descending). This ordering enables early-exit:
    /// once an upper atom is NOT implied by the current ub, all subsequent
    /// upper atoms with larger bounds are also not implied.
    pub(crate) upper_atoms: Vec<BoundAtom>,
    pub(crate) lower_atoms: Vec<BoundAtom>,
    /// Number of atoms that have small-int bound values.
    pub(crate) small_atom_count: u32,
    /// Total number of atoms.
    pub(crate) total_atom_count: u32,
}

impl VarPropagator {
    /// Create a new VarPropagator from a list of bound atoms for a variable.
    ///
    /// Atoms are sorted for cache-friendly scanning:
    /// - Upper atoms ascending by bound value (early-exit when ub < atom bound)
    /// - Lower atoms descending by bound value (early-exit when lb > atom bound)
    pub fn new(_var_id: u32, atoms: Vec<BoundAtom>) -> Self {
        let total_atom_count = atoms.len() as u32;
        let small_atom_count = atoms.iter().filter(|a| a.is_small).count() as u32;

        let mut upper_atoms: Vec<BoundAtom> =
            atoms.iter().filter(|a| a.is_upper).cloned().collect();
        let mut lower_atoms: Vec<BoundAtom> = atoms.into_iter().filter(|a| !a.is_upper).collect();

        // Sort upper atoms ascending by bound value (for early-exit).
        // Cross-multiply for comparison: n1/d1 < n2/d2 iff n1*d2 < n2*d1
        // (both denoms positive).
        upper_atoms.sort_by(|a, b| {
            if a.is_small && b.is_small {
                let lhs = i128::from(a.bound_numer) * i128::from(b.bound_denom);
                let rhs = i128::from(b.bound_numer) * i128::from(a.bound_denom);
                lhs.cmp(&rhs).then_with(|| a.strict.cmp(&b.strict))
            } else {
                // Non-small atoms sort to the end.
                a.is_small.cmp(&b.is_small).reverse()
            }
        });

        // Sort lower atoms descending by bound value (for early-exit).
        lower_atoms.sort_by(|a, b| {
            if a.is_small && b.is_small {
                let lhs = i128::from(b.bound_numer) * i128::from(a.bound_denom);
                let rhs = i128::from(a.bound_numer) * i128::from(b.bound_denom);
                lhs.cmp(&rhs).then_with(|| a.strict.cmp(&b.strict))
            } else {
                a.is_small.cmp(&b.is_small).reverse()
            }
        });

        Self {
            upper_atoms,
            lower_atoms,
            small_atom_count,
            total_atom_count,
        }
    }

    /// Check which atoms are implied by the current variable bounds.
    ///
    /// Returns a list of (atom_index, implied_value) pairs. Only returns
    /// results for small-int atoms; non-small atoms return Unknown and must
    /// be handled by the caller's fallback path.
    ///
    /// # Arguments
    ///
    /// * `lb` - Current lower bound, if any. `None` means unbounded below.
    /// * `ub` - Current upper bound, if any. `None` means unbounded above.
    /// * `results` - Output buffer, cleared and filled with propagation results.
    pub fn check_bounds(
        &self,
        lb: Option<SmallBound>,
        ub: Option<SmallBound>,
        results: &mut Vec<PropagationResult>,
    ) {
        results.clear();

        // Check upper atoms (x <= k or x < k).
        // Implied TRUE when: ub satisfies the atom.
        // Implied FALSE when: lb contradicts the atom.
        if let Some(ub) = ub {
            for atom in &self.upper_atoms {
                if !atom.is_small {
                    continue;
                }
                let imp = check_upper_atom_true(&ub, atom);
                if imp == AtomImplication::ImpliedTrue {
                    results.push(PropagationResult {
                        atom_index: atom.atom_index,
                        implied_value: true,
                    });
                }
            }
        }

        if let Some(lb) = lb {
            for atom in &self.upper_atoms {
                if !atom.is_small {
                    continue;
                }
                let imp = check_upper_atom_false(&lb, atom);
                if imp == AtomImplication::ImpliedFalse {
                    results.push(PropagationResult {
                        atom_index: atom.atom_index,
                        implied_value: false,
                    });
                }
            }
        }

        // Check lower atoms (x >= k or x > k).
        // Implied TRUE when: lb satisfies the atom.
        // Implied FALSE when: ub contradicts the atom.
        if let Some(lb) = lb {
            for atom in &self.lower_atoms {
                if !atom.is_small {
                    continue;
                }
                let imp = check_lower_atom_true(&lb, atom);
                if imp == AtomImplication::ImpliedTrue {
                    results.push(PropagationResult {
                        atom_index: atom.atom_index,
                        implied_value: true,
                    });
                }
            }
        }

        if let Some(ub) = ub {
            for atom in &self.lower_atoms {
                if !atom.is_small {
                    continue;
                }
                let imp = check_lower_atom_false(&ub, atom);
                if imp == AtomImplication::ImpliedFalse {
                    results.push(PropagationResult {
                        atom_index: atom.atom_index,
                        implied_value: false,
                    });
                }
            }
        }
    }

    /// Number of atoms for this variable.
    pub fn total_atom_count(&self) -> u32 {
        self.total_atom_count
    }

    /// Number of atoms with small-int bound values.
    pub fn small_atom_count(&self) -> u32 {
        self.small_atom_count
    }
}

/// Check if an upper atom (x <= k or x < k) is implied TRUE by the current
/// upper bound.
///
/// The atom is implied true when:
/// - Non-strict atom (x <= k): ub.value <= k
///   - If ub is strict: ub.value < k, OR ub.value == k (since x < ub.value implies x <= k when ub.value == k? No...)
///     Actually: if ub is strict, the bound is x < ub_val. For atom x <= k:
///     x < ub_val && ub_val <= k implies x < k implies x <= k. So: ub_val <= k suffices.
///     But if ub_val == k and ub is strict: x < k implies x <= k... wait, the atom is x <= k.
///     If x < k (from strict ub at k), then x <= k is true. So ub_val <= k works.
///   - If ub is non-strict: ub.value <= k (same)
/// - Strict atom (x < k): ub.value < k, OR (ub.value == k AND ub is strict)
///
/// Matches the logic in `propagate_var_atoms()`:
/// ```text
/// if atom.strict {
///     ub.value < atom.bound_value || (ub.value == atom.bound_value && ub.strict)
/// } else {
///     ub.value <= atom.bound_value
/// }
/// ```
#[inline(always)]
fn check_upper_atom_true(ub: &SmallBound, atom: &BoundAtom) -> AtomImplication {
    // Compare ub.value vs atom.bound_value using cross-multiply.
    // ub = p/q, atom = n/d. Compare: p*d vs n*q.
    let lhs = i128::from(ub.numer) * i128::from(atom.bound_denom);
    let rhs = i128::from(atom.bound_numer) * i128::from(ub.denom);

    if atom.strict {
        // Atom: x < k. Implied true when ub < k OR (ub == k AND ub.strict).
        if lhs < rhs || (lhs == rhs && ub.strict) {
            AtomImplication::ImpliedTrue
        } else {
            AtomImplication::Unknown
        }
    } else {
        // Atom: x <= k. Implied true when ub <= k.
        if lhs <= rhs {
            AtomImplication::ImpliedTrue
        } else {
            AtomImplication::Unknown
        }
    }
}

/// Check if an upper atom (x <= k or x < k) is implied FALSE by the current
/// lower bound.
///
/// The atom is implied false when:
/// - Non-strict atom (x <= k): lb > k, OR (lb == k AND lb.strict)
/// - Strict atom (x < k): lb >= k (regardless of lb strictness)
///
/// Matches the logic in `propagate_var_atoms()`:
/// ```text
/// if atom.strict {
///     lb.value >= atom.bound_value
/// } else {
///     lb.value > atom.bound_value || (lb.value == atom.bound_value && lb.strict)
/// }
/// ```
#[inline(always)]
fn check_upper_atom_false(lb: &SmallBound, atom: &BoundAtom) -> AtomImplication {
    let lhs = i128::from(lb.numer) * i128::from(atom.bound_denom);
    let rhs = i128::from(atom.bound_numer) * i128::from(lb.denom);

    if atom.strict {
        // Atom: x < k. Implied false when lb >= k.
        if lhs >= rhs {
            AtomImplication::ImpliedFalse
        } else {
            AtomImplication::Unknown
        }
    } else {
        // Atom: x <= k. Implied false when lb > k, or (lb == k and lb.strict).
        if lhs > rhs || (lhs == rhs && lb.strict) {
            AtomImplication::ImpliedFalse
        } else {
            AtomImplication::Unknown
        }
    }
}

/// Check if a lower atom (x >= k or x > k) is implied TRUE by the current
/// lower bound.
///
/// The atom is implied true when:
/// - Non-strict atom (x >= k): lb >= k
/// - Strict atom (x > k): lb > k, OR (lb == k AND lb.strict)
///
/// Matches the logic in `propagate_var_atoms()`:
/// ```text
/// if atom.strict {
///     lb.value > atom.bound_value || (lb.value == atom.bound_value && lb.strict)
/// } else {
///     lb.value >= atom.bound_value
/// }
/// ```
#[inline(always)]
fn check_lower_atom_true(lb: &SmallBound, atom: &BoundAtom) -> AtomImplication {
    let lhs = i128::from(lb.numer) * i128::from(atom.bound_denom);
    let rhs = i128::from(atom.bound_numer) * i128::from(lb.denom);

    if atom.strict {
        // Atom: x > k. Implied true when lb > k, or (lb == k and lb.strict).
        if lhs > rhs || (lhs == rhs && lb.strict) {
            AtomImplication::ImpliedTrue
        } else {
            AtomImplication::Unknown
        }
    } else {
        // Atom: x >= k. Implied true when lb >= k.
        if lhs >= rhs {
            AtomImplication::ImpliedTrue
        } else {
            AtomImplication::Unknown
        }
    }
}

/// Check if a lower atom (x >= k or x > k) is implied FALSE by the current
/// upper bound.
///
/// The atom is implied false when:
/// - Non-strict atom (x >= k): ub < k, OR (ub == k AND ub.strict)
/// - Strict atom (x > k): ub <= k (regardless of ub strictness)
///
/// Matches the logic in `propagate_var_atoms()`:
/// ```text
/// if atom.strict {
///     ub.value <= atom.bound_value
/// } else {
///     ub.value < atom.bound_value || (ub.value == atom.bound_value && ub.strict)
/// }
/// ```
#[inline(always)]
fn check_lower_atom_false(ub: &SmallBound, atom: &BoundAtom) -> AtomImplication {
    let lhs = i128::from(ub.numer) * i128::from(atom.bound_denom);
    let rhs = i128::from(atom.bound_numer) * i128::from(ub.denom);

    if atom.strict {
        // Atom: x > k. Implied false when ub <= k.
        if lhs <= rhs {
            AtomImplication::ImpliedFalse
        } else {
            AtomImplication::Unknown
        }
    } else {
        // Atom: x >= k. Implied false when ub < k, or (ub == k and ub.strict).
        if lhs < rhs || (lhs == rhs && ub.strict) {
            AtomImplication::ImpliedFalse
        } else {
            AtomImplication::Unknown
        }
    }
}

/// Atom-index fingerprint: `(atom entry count, hash)` over every
/// `(var, bound_numer, bound_denom, is_upper, strict, is_small)` tuple in the
/// caller's atom index (lia-hot-loop-plan.md §3.8). Compiled propagator
/// tables are valid for exactly one fingerprint: positions, bound values,
/// directions, and strictness must all match. Term identity is deliberately
/// excluded — the JIT only reports atom *positions*; callers resolve
/// positions against their live atom index.
pub type TheoryPropFingerprint = (u64, u64);

/// Number of `propagate_var` runs before native machine code is emitted
/// (Fix A1, lia-hot-loop-plan.md §1).
///
/// Why defer at all: native emission costs an mmap + memmove + icache flush.
/// The interpreted `VarPropagator` path is already allocation-free i128
/// arithmetic (~2-5ns/atom), so native code only pays off on sustained
/// workloads. Solver instances that perform only a handful of propagations
/// (one-shot lazy DPLL(T) iterations, trivially-SAT checks) should never pay
/// native compile costs.
///
/// Why 8: the cost being amortized is per-instance, not per-call. Any solver
/// that survives into real BCP work crosses 8 propagation runs within its
/// first check() — so hot instances upgrade almost immediately and >99% of
/// their propagations run native — while genuinely cold instances (<8 runs)
/// stay entirely on the interpreted path with zero executable-memory cost.
/// Larger thresholds delay the upgrade without reducing the (already single,
/// batched) mmap; smaller thresholds compile native for throwaway solvers.
pub const NATIVE_COMPILE_THRESHOLD: u64 = 8;

/// Top-level JIT compilation manager for theory bound propagation.
///
/// Holds per-variable propagators and compilation statistics.
/// Created once after atom registration, then used during every
/// propagation call.
///
/// Cloneable so theory solvers can persist compiled propagators across
/// solver instances via structural snapshots (Fix A1): the interpreted
/// tables are deep-copied and the native code region is shared via `Arc`.
#[derive(Clone)]
pub struct TheoryPropJit {
    /// Per-variable propagators. Indexed by internal variable ID.
    /// `None` for variables without bound atoms.
    propagators: Vec<Option<VarPropagator>>,
    /// Native machine code propagators (aarch64/x86_64). Indexed by internal variable ID.
    /// `None` for variables without native compilation support.
    native_propagators: Vec<Option<crate::theory_prop_native::NativeVarPropagator>>,
    /// Number of variables with native machine code propagators.
    native_compiled_vars: u32,
    /// Total number of atoms compiled.
    total_atoms: u32,
    /// Number of atoms with small-int bound values.
    small_atoms: u32,
    /// Number of variables with at least one atom.
    compiled_vars: u32,
    /// Hotness counter: number of `propagate_var` calls on this instance
    /// (persists across recompiles and snapshot transfer).
    propagation_runs: u64,
    /// Native code is emitted once `propagation_runs` exceeds this threshold.
    native_compile_threshold: u64,
    /// Whether native compilation has been attempted for the current tables.
    native_attempted: bool,
    /// Fingerprint of the atom index the current tables were compiled from,
    /// when provided by the caller. Used by theory solvers to skip
    /// recompilation when the atom index is structurally identical.
    fingerprint: Option<TheoryPropFingerprint>,
}

impl TheoryPropJit {
    /// Create a new empty JIT manager.
    pub fn new() -> Self {
        Self {
            propagators: Vec::new(),
            native_propagators: Vec::new(),
            native_compiled_vars: 0,
            total_atoms: 0,
            small_atoms: 0,
            compiled_vars: 0,
            propagation_runs: 0,
            native_compile_threshold: NATIVE_COMPILE_THRESHOLD,
            native_attempted: false,
            fingerprint: None,
        }
    }

    /// Compile propagators for all variables with bound atoms.
    ///
    /// Native machine code emission is deferred behind the hotness
    /// threshold: cold instances get interpreted tables only; instances
    /// that are already hot (mid-solve recompiles after new atom
    /// registration) re-emit native code immediately.
    ///
    /// # Arguments
    ///
    /// * `var_atoms` - Iterator of (var_id, atoms) pairs. Each atom is a
    ///   `BoundAtom` pre-extracted from the theory solver's `AtomRef`.
    pub fn compile<I>(&mut self, var_atoms: I)
    where
        I: IntoIterator<Item = (u32, Vec<BoundAtom>)>,
    {
        self.compile_fingerprinted(var_atoms, None);
    }

    /// Like [`compile`](Self::compile), but records the caller's atom-index
    /// fingerprint so subsequent identical compiles can be skipped via
    /// [`fingerprint`](Self::fingerprint) (Fix A1 snapshot persistence).
    pub fn compile_fingerprinted<I>(
        &mut self,
        var_atoms: I,
        fingerprint: Option<TheoryPropFingerprint>,
    ) where
        I: IntoIterator<Item = (u32, Vec<BoundAtom>)>,
    {
        let mut total_atoms = 0u32;
        let mut small_atoms = 0u32;
        let mut compiled_vars = 0u32;
        let mut max_var = 0u32;

        // Collect all entries to determine max var ID.
        let entries: Vec<(u32, Vec<BoundAtom>)> = var_atoms.into_iter().collect();
        for (var_id, _) in &entries {
            if *var_id >= max_var {
                max_var = *var_id + 1;
            }
        }

        self.propagators.clear();
        self.propagators.resize_with(max_var as usize, || None);

        for (var_id, atoms) in entries {
            if atoms.is_empty() {
                continue;
            }
            let propagator = VarPropagator::new(var_id, atoms);
            total_atoms += propagator.total_atom_count;
            small_atoms += propagator.small_atom_count;
            compiled_vars += 1;
            if (var_id as usize) < self.propagators.len() {
                self.propagators[var_id as usize] = Some(propagator);
            }
        }

        self.total_atoms = total_atoms;
        self.small_atoms = small_atoms;
        self.compiled_vars = compiled_vars;
        self.fingerprint = fingerprint;

        // The old native code (if any) is stale for the new tables.
        self.native_propagators.clear();
        self.native_compiled_vars = 0;
        self.native_attempted = false;

        // Emit native machine code immediately only when this instance is
        // already hot; cold instances defer to the interpreted path until
        // the hotness threshold is crossed in propagate_var().
        if self.propagation_runs >= self.native_compile_threshold {
            self.compile_native_now();
        }
    }

    /// Emit native machine code for the current interpreted tables.
    ///
    /// All eligible variables are batched into a single executable mapping
    /// (one mmap + one icache flush), not one mapping per variable.
    fn compile_native_now(&mut self) {
        self.native_attempted = true;
        let (native, native_count) = crate::theory_prop_native::compile_native_propagators(self);
        self.native_propagators = native;
        self.native_compiled_vars = native_count;
    }

    /// Override the native-emission hotness threshold.
    ///
    /// `0` restores eager native compilation (used by tests that exercise
    /// the native path directly).
    pub fn set_native_compile_threshold(&mut self, threshold: u64) {
        self.native_compile_threshold = threshold;
        if threshold == 0 && !self.native_attempted && !self.propagators.is_empty() {
            self.compile_native_now();
        }
    }

    /// Fingerprint of the atom index the current tables were compiled from.
    pub fn fingerprint(&self) -> Option<TheoryPropFingerprint> {
        self.fingerprint
    }

    /// Number of `propagate_var` calls observed by this instance.
    pub fn propagation_runs(&self) -> u64 {
        self.propagation_runs
    }

    /// Check which atoms are implied for a given variable's current bounds.
    ///
    /// Returns the number of implied atoms written to `results`.
    /// Only handles small-int atoms; non-small atoms are skipped.
    ///
    /// Takes `&mut self` to maintain the hotness counter: once the
    /// interpreted path has run more than `native_compile_threshold` times,
    /// native machine code is emitted for all variables in one batch.
    ///
    /// # Arguments
    ///
    /// * `var_id` - The internal variable ID.
    /// * `lb` - Current lower bound, if any and small.
    /// * `ub` - Current upper bound, if any and small.
    /// * `results` - Output buffer for propagation results.
    pub fn propagate_var(
        &mut self,
        var_id: u32,
        lb: Option<SmallBound>,
        ub: Option<SmallBound>,
        results: &mut Vec<PropagationResult>,
    ) {
        results.clear();
        self.propagation_runs += 1;
        if !self.native_attempted
            && self.propagation_runs > self.native_compile_threshold
            && !self.propagators.is_empty()
        {
            self.compile_native_now();
        }
        let vi = var_id as usize;
        if vi >= self.propagators.len() {
            return;
        }
        // Try native machine code path first (aarch64/x86_64).
        if vi < self.native_propagators.len() {
            if let Some(ref native) = self.native_propagators[vi] {
                native.check_bounds(lb, ub, results);
                return;
            }
        }
        // Fall back to interpreted i128 cross-multiply path.
        if let Some(ref prop) = self.propagators[vi] {
            prop.check_bounds(lb, ub, results);
        }
    }

    /// Whether a variable has a compiled propagator.
    #[inline]
    pub fn has_propagator(&self, var_id: u32) -> bool {
        let vi = var_id as usize;
        vi < self.propagators.len() && self.propagators[vi].is_some()
    }

    /// Whether the variable's compiled propagator covers every registered atom.
    ///
    /// Variables with any non-small atom bound still benefit from the fast path
    /// for their small atoms, but callers must run their interpreted fallback
    /// afterward so large `BigRational` atom bounds are not stranded.
    #[inline]
    pub fn variable_is_fully_small(&self, var_id: u32) -> bool {
        let vi = var_id as usize;
        vi < self.propagators.len()
            && self.propagators[vi]
                .as_ref()
                .is_some_and(|prop| prop.small_atom_count() == prop.total_atom_count())
    }

    /// Total atoms compiled across all variables.
    pub fn total_atoms(&self) -> u32 {
        self.total_atoms
    }

    /// Number of atoms with small-int bound values (fast-path eligible).
    pub fn small_atoms(&self) -> u32 {
        self.small_atoms
    }

    /// Number of variables with at least one compiled atom.
    pub fn compiled_vars(&self) -> u32 {
        self.compiled_vars
    }

    /// Access the per-variable propagator list (crate-internal).
    ///
    /// Used by `theory_prop_native` to compile native machine code versions
    /// of the interpreted propagators.
    pub(crate) fn propagators(&self) -> &[Option<VarPropagator>] {
        &self.propagators
    }

    /// Number of variables with native machine code propagators.
    pub fn native_compiled_vars(&self) -> u32 {
        self.native_compiled_vars
    }

    /// Fraction of atoms eligible for the fast path.
    pub fn small_fraction(&self) -> f64 {
        if self.total_atoms == 0 {
            0.0
        } else {
            f64::from(self.small_atoms) / f64::from(self.total_atoms)
        }
    }
}

impl Default for TheoryPropJit {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn make_atom(index: u32, numer: i64, denom: i64, is_upper: bool, strict: bool) -> BoundAtom {
        BoundAtom {
            atom_index: index,
            bound_numer: numer,
            bound_denom: denom,
            is_upper,
            strict,
            is_small: true,
        }
    }

    fn make_big_atom(index: u32, is_upper: bool, strict: bool) -> BoundAtom {
        BoundAtom {
            atom_index: index,
            bound_numer: 0,
            bound_denom: 1,
            is_upper,
            strict,
            is_small: false,
        }
    }

    fn make_bound(numer: i64, denom: i64, strict: bool) -> SmallBound {
        SmallBound {
            numer,
            denom,
            strict,
        }
    }

    // --- Upper atom TRUE tests ---

    #[test]
    fn test_upper_nonstrict_atom_implied_true_by_ub_less() {
        // Atom: x <= 5. ub = 3. 3 <= 5 => implied true.
        let atom = make_atom(0, 5, 1, true, false);
        let ub = make_bound(3, 1, false);
        assert_eq!(
            check_upper_atom_true(&ub, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_upper_nonstrict_atom_implied_true_by_ub_equal() {
        // Atom: x <= 5. ub = 5. 5 <= 5 => implied true.
        let atom = make_atom(0, 5, 1, true, false);
        let ub = make_bound(5, 1, false);
        assert_eq!(
            check_upper_atom_true(&ub, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_upper_nonstrict_atom_not_implied_by_ub_greater() {
        // Atom: x <= 5. ub = 7. 7 > 5 => unknown.
        let atom = make_atom(0, 5, 1, true, false);
        let ub = make_bound(7, 1, false);
        assert_eq!(check_upper_atom_true(&ub, &atom), AtomImplication::Unknown);
    }

    #[test]
    fn test_upper_strict_atom_implied_true_by_ub_less() {
        // Atom: x < 5. ub = 3. 3 < 5 => implied true.
        let atom = make_atom(0, 5, 1, true, true);
        let ub = make_bound(3, 1, false);
        assert_eq!(
            check_upper_atom_true(&ub, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_upper_strict_atom_implied_true_by_strict_ub_equal() {
        // Atom: x < 5. ub = 5 (strict). ub == k and ub.strict => implied true.
        let atom = make_atom(0, 5, 1, true, true);
        let ub = make_bound(5, 1, true);
        assert_eq!(
            check_upper_atom_true(&ub, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_upper_strict_atom_not_implied_by_nonstrict_ub_equal() {
        // Atom: x < 5. ub = 5 (non-strict). x <= 5 does NOT imply x < 5.
        let atom = make_atom(0, 5, 1, true, true);
        let ub = make_bound(5, 1, false);
        assert_eq!(check_upper_atom_true(&ub, &atom), AtomImplication::Unknown);
    }

    // --- Upper atom FALSE tests ---

    #[test]
    fn test_upper_nonstrict_atom_implied_false_by_lb_greater() {
        // Atom: x <= 5. lb = 7. 7 > 5 => atom is false.
        let atom = make_atom(0, 5, 1, true, false);
        let lb = make_bound(7, 1, false);
        assert_eq!(
            check_upper_atom_false(&lb, &atom),
            AtomImplication::ImpliedFalse
        );
    }

    #[test]
    fn test_upper_nonstrict_atom_implied_false_by_strict_lb_equal() {
        // Atom: x <= 5. lb = 5 (strict). x > 5 contradicts x <= 5.
        let atom = make_atom(0, 5, 1, true, false);
        let lb = make_bound(5, 1, true);
        assert_eq!(
            check_upper_atom_false(&lb, &atom),
            AtomImplication::ImpliedFalse
        );
    }

    #[test]
    fn test_upper_nonstrict_atom_not_implied_false_by_lb_equal() {
        // Atom: x <= 5. lb = 5 (non-strict). x >= 5 is compatible with x <= 5.
        let atom = make_atom(0, 5, 1, true, false);
        let lb = make_bound(5, 1, false);
        assert_eq!(check_upper_atom_false(&lb, &atom), AtomImplication::Unknown);
    }

    #[test]
    fn test_upper_strict_atom_implied_false_by_lb_equal() {
        // Atom: x < 5. lb = 5. x >= 5 contradicts x < 5.
        let atom = make_atom(0, 5, 1, true, true);
        let lb = make_bound(5, 1, false);
        assert_eq!(
            check_upper_atom_false(&lb, &atom),
            AtomImplication::ImpliedFalse
        );
    }

    #[test]
    fn test_upper_strict_atom_implied_false_by_lb_greater() {
        // Atom: x < 5. lb = 7. 7 >= 5 => atom is false.
        let atom = make_atom(0, 5, 1, true, true);
        let lb = make_bound(7, 1, false);
        assert_eq!(
            check_upper_atom_false(&lb, &atom),
            AtomImplication::ImpliedFalse
        );
    }

    // --- Lower atom TRUE tests ---

    #[test]
    fn test_lower_nonstrict_atom_implied_true_by_lb_greater() {
        // Atom: x >= 5. lb = 7. 7 >= 5 => implied true.
        let atom = make_atom(0, 5, 1, false, false);
        let lb = make_bound(7, 1, false);
        assert_eq!(
            check_lower_atom_true(&lb, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_lower_nonstrict_atom_implied_true_by_lb_equal() {
        // Atom: x >= 5. lb = 5. 5 >= 5 => implied true.
        let atom = make_atom(0, 5, 1, false, false);
        let lb = make_bound(5, 1, false);
        assert_eq!(
            check_lower_atom_true(&lb, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_lower_strict_atom_implied_true_by_lb_greater() {
        // Atom: x > 5. lb = 7. 7 > 5 => implied true.
        let atom = make_atom(0, 5, 1, false, true);
        let lb = make_bound(7, 1, false);
        assert_eq!(
            check_lower_atom_true(&lb, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_lower_strict_atom_implied_true_by_strict_lb_equal() {
        // Atom: x > 5. lb = 5 (strict). lb == k and lb.strict => implied true.
        let atom = make_atom(0, 5, 1, false, true);
        let lb = make_bound(5, 1, true);
        assert_eq!(
            check_lower_atom_true(&lb, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_lower_strict_atom_not_implied_by_nonstrict_lb_equal() {
        // Atom: x > 5. lb = 5 (non-strict). x >= 5 does NOT imply x > 5.
        let atom = make_atom(0, 5, 1, false, true);
        let lb = make_bound(5, 1, false);
        assert_eq!(check_lower_atom_true(&lb, &atom), AtomImplication::Unknown);
    }

    // --- Lower atom FALSE tests ---

    #[test]
    fn test_lower_nonstrict_atom_implied_false_by_ub_less() {
        // Atom: x >= 5. ub = 3. 3 < 5 => atom is false.
        let atom = make_atom(0, 5, 1, false, false);
        let ub = make_bound(3, 1, false);
        assert_eq!(
            check_lower_atom_false(&ub, &atom),
            AtomImplication::ImpliedFalse
        );
    }

    #[test]
    fn test_lower_nonstrict_atom_implied_false_by_strict_ub_equal() {
        // Atom: x >= 5. ub = 5 (strict). x < 5 contradicts x >= 5.
        let atom = make_atom(0, 5, 1, false, false);
        let ub = make_bound(5, 1, true);
        assert_eq!(
            check_lower_atom_false(&ub, &atom),
            AtomImplication::ImpliedFalse
        );
    }

    #[test]
    fn test_lower_nonstrict_atom_not_implied_false_by_ub_equal() {
        // Atom: x >= 5. ub = 5 (non-strict). x <= 5 is compatible with x >= 5.
        let atom = make_atom(0, 5, 1, false, false);
        let ub = make_bound(5, 1, false);
        assert_eq!(check_lower_atom_false(&ub, &atom), AtomImplication::Unknown);
    }

    #[test]
    fn test_lower_strict_atom_implied_false_by_ub_equal() {
        // Atom: x > 5. ub = 5. x <= 5 contradicts x > 5.
        let atom = make_atom(0, 5, 1, false, true);
        let ub = make_bound(5, 1, false);
        assert_eq!(
            check_lower_atom_false(&ub, &atom),
            AtomImplication::ImpliedFalse
        );
    }

    // --- Rational (non-integer) bound tests ---

    #[test]
    fn test_rational_bounds_cross_multiply() {
        // Atom: x <= 3/2. ub = 1/1 (=1). 1*2 = 2 <= 3*1 = 3 => implied true.
        let atom = make_atom(0, 3, 2, true, false);
        let ub = make_bound(1, 1, false);
        assert_eq!(
            check_upper_atom_true(&ub, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_rational_bounds_not_implied() {
        // Atom: x <= 1/3. ub = 1/2. 1*3 = 3 > 1*2 = 2 => unknown.
        let atom = make_atom(0, 1, 3, true, false);
        let ub = make_bound(1, 2, false);
        assert_eq!(check_upper_atom_true(&ub, &atom), AtomImplication::Unknown);
    }

    // --- VarPropagator integration tests ---

    #[test]
    fn test_var_propagator_basic() {
        let atoms = vec![
            make_atom(0, 10, 1, true, false), // x <= 10
            make_atom(1, 5, 1, true, false),  // x <= 5
            make_atom(2, 3, 1, false, false), // x >= 3
            make_atom(3, 7, 1, false, false), // x >= 7
        ];
        let prop = VarPropagator::new(0, atoms);
        assert_eq!(prop.total_atom_count(), 4);
        assert_eq!(prop.small_atom_count(), 4);

        let mut results = Vec::new();

        // lb=4, ub=8: x<=10 true, x<=5 unknown, x>=3 true, x>=7 unknown
        prop.check_bounds(
            Some(make_bound(4, 1, false)),
            Some(make_bound(8, 1, false)),
            &mut results,
        );
        // Expect: atom 0 (x<=10) true, atom 2 (x>=3) true
        let true_atoms: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(
            true_atoms.contains(&(0, true)),
            "x<=10 should be implied true"
        );
        assert!(
            true_atoms.contains(&(2, true)),
            "x>=3 should be implied true"
        );
        assert!(
            !true_atoms.iter().any(|&(i, _)| i == 1),
            "x<=5 should not be implied"
        );
        assert!(
            !true_atoms.iter().any(|&(i, _)| i == 3),
            "x>=7 should not be implied"
        );
    }

    #[test]
    fn test_var_propagator_implied_false() {
        let atoms = vec![
            make_atom(0, 5, 1, true, false),  // x <= 5
            make_atom(1, 3, 1, false, false), // x >= 3
        ];
        let prop = VarPropagator::new(0, atoms);
        let mut results = Vec::new();

        // lb=7: x <= 5 is false (lb=7 > 5), x >= 3 is true (lb=7 >= 3)
        prop.check_bounds(Some(make_bound(7, 1, false)), None, &mut results);
        let res: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(res.contains(&(0, false)), "x<=5 should be implied false");
        assert!(res.contains(&(1, true)), "x>=3 should be implied true");
    }

    #[test]
    fn test_var_propagator_skips_big_atoms() {
        let atoms = vec![
            make_atom(0, 5, 1, true, false),  // x <= 5 (small)
            make_big_atom(1, true, false),    // x <= BIG (non-small)
            make_atom(2, 3, 1, false, false), // x >= 3 (small)
        ];
        let prop = VarPropagator::new(0, atoms);
        assert_eq!(prop.total_atom_count(), 3);
        assert_eq!(prop.small_atom_count(), 2);

        let mut results = Vec::new();
        prop.check_bounds(
            Some(make_bound(4, 1, false)),
            Some(make_bound(4, 1, false)),
            &mut results,
        );
        // atom 1 (big) should not appear in results
        assert!(!results.iter().any(|r| r.atom_index == 1));
    }

    // --- TheoryPropJit integration tests ---

    #[test]
    fn test_jit_compile_and_propagate() {
        let mut jit = TheoryPropJit::new();

        let var0_atoms = vec![
            make_atom(0, 10, 1, true, false), // var0: x <= 10
            make_atom(1, 5, 1, false, false), // var0: x >= 5
        ];
        let var2_atoms = vec![
            make_atom(0, 3, 1, true, true), // var2: x < 3
        ];

        jit.compile(vec![(0, var0_atoms), (2, var2_atoms)]);

        assert_eq!(jit.total_atoms(), 3);
        assert_eq!(jit.small_atoms(), 3);
        assert_eq!(jit.compiled_vars(), 2);
        assert!((jit.small_fraction() - 1.0).abs() < f64::EPSILON);
        assert!(jit.has_propagator(0));
        assert!(!jit.has_propagator(1));
        assert!(jit.has_propagator(2));

        let mut results = Vec::new();

        // var0: lb=6, ub=8
        jit.propagate_var(
            0,
            Some(make_bound(6, 1, false)),
            Some(make_bound(8, 1, false)),
            &mut results,
        );
        let res: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(res.contains(&(0, true)), "x<=10 implied true by ub=8");
        assert!(res.contains(&(1, true)), "x>=5 implied true by lb=6");

        // var2: ub=2 (non-strict)
        jit.propagate_var(2, None, Some(make_bound(2, 1, false)), &mut results);
        let res: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(res.contains(&(0, true)), "x<3 implied true by ub=2");
    }

    #[test]
    fn test_jit_no_propagator_for_missing_var() {
        let mut jit = TheoryPropJit::new();
        let mut results = Vec::new();
        jit.propagate_var(999, Some(make_bound(5, 1, false)), None, &mut results);
        assert!(results.is_empty());
    }

    // --- Hotness-deferred native compilation (Fix A1) ---

    #[test]
    fn test_native_compilation_deferred_until_hot() {
        let mut jit = TheoryPropJit::new();
        let atoms = vec![
            make_atom(0, 10, 1, true, false), // x <= 10
            make_atom(1, 5, 1, false, false), // x >= 5
        ];
        jit.compile(vec![(0, atoms)]);

        // Cold instance: interpreted tables only, no native code emitted.
        assert_eq!(jit.compiled_vars(), 1);
        assert_eq!(
            jit.native_compiled_vars(),
            0,
            "native code must be deferred behind the hotness threshold"
        );

        // Drive propagation runs up to the threshold: still interpreted.
        let mut results = Vec::new();
        for _ in 0..NATIVE_COMPILE_THRESHOLD {
            jit.propagate_var(
                0,
                Some(make_bound(6, 1, false)),
                Some(make_bound(8, 1, false)),
                &mut results,
            );
            let res: Vec<(u32, bool)> = results
                .iter()
                .map(|r| (r.atom_index, r.implied_value))
                .collect();
            assert!(res.contains(&(0, true)) && res.contains(&(1, true)));
        }
        assert_eq!(
            jit.native_compiled_vars(),
            0,
            "first {NATIVE_COMPILE_THRESHOLD} runs stay interpreted"
        );

        // The next run crosses the threshold and upgrades to native
        // (on supported platforms); results must be unchanged. Native emit
        // needs executable memory, which exists only on Linux/macOS —
        // elsewhere the instance stays (correctly) interpreted.
        jit.propagate_var(
            0,
            Some(make_bound(6, 1, false)),
            Some(make_bound(8, 1, false)),
            &mut results,
        );
        #[cfg(all(
            any(target_arch = "aarch64", target_arch = "x86_64"),
            any(target_os = "linux", target_os = "macos")
        ))]
        assert_eq!(
            jit.native_compiled_vars(),
            1,
            "hot instance must upgrade to native machine code"
        );
        let res: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(res.contains(&(0, true)) && res.contains(&(1, true)));
    }

    #[test]
    fn test_recompile_of_hot_instance_emits_native_immediately() {
        let mut jit = TheoryPropJit::new();
        jit.compile(vec![(0, vec![make_atom(0, 10, 1, true, false)])]);
        let mut results = Vec::new();
        for _ in 0..=NATIVE_COMPILE_THRESHOLD {
            jit.propagate_var(0, None, Some(make_bound(8, 1, false)), &mut results);
        }
        // Mid-solve recompile (new atom registered): the instance is hot,
        // so native code is re-emitted for the new tables immediately.
        jit.compile(vec![(
            0,
            vec![
                make_atom(0, 10, 1, true, false),
                make_atom(1, 3, 1, false, false),
            ],
        )]);
        #[cfg(all(
            any(target_arch = "aarch64", target_arch = "x86_64"),
            any(target_os = "linux", target_os = "macos")
        ))]
        assert_eq!(jit.native_compiled_vars(), 1);
        assert_eq!(jit.total_atoms(), 2);
    }

    #[test]
    fn test_clone_preserves_tables_and_fingerprint() {
        let mut jit = TheoryPropJit::new();
        jit.set_native_compile_threshold(0);
        jit.compile_fingerprinted(
            vec![(0, vec![make_atom(0, 10, 1, true, false)])],
            Some((1, 0xDEAD_BEEF)),
        );
        let mut cloned = jit.clone();
        assert_eq!(cloned.fingerprint(), Some((1, 0xDEAD_BEEF)));
        assert_eq!(cloned.total_atoms(), 1);
        #[cfg(all(
            any(target_arch = "aarch64", target_arch = "x86_64"),
            any(target_os = "linux", target_os = "macos")
        ))]
        assert_eq!(cloned.native_compiled_vars(), 1);

        // The clone (sharing the native code region via Arc) must produce
        // identical propagation results.
        let mut results = Vec::new();
        cloned.propagate_var(0, None, Some(make_bound(8, 1, false)), &mut results);
        let res: Vec<(u32, bool)> = results
            .iter()
            .map(|r| (r.atom_index, r.implied_value))
            .collect();
        assert!(res.contains(&(0, true)), "x<=10 implied true by ub=8");
    }

    // --- Edge cases ---

    #[test]
    fn test_negative_bounds() {
        // Atom: x <= -3. ub = -5. -5 <= -3 => implied true.
        let atom = make_atom(0, -3, 1, true, false);
        let ub = make_bound(-5, 1, false);
        assert_eq!(
            check_upper_atom_true(&ub, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_zero_bound() {
        // Atom: x >= 0. lb = 0. 0 >= 0 => implied true.
        let atom = make_atom(0, 0, 1, false, false);
        let lb = make_bound(0, 1, false);
        assert_eq!(
            check_lower_atom_true(&lb, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_strict_at_zero() {
        // Atom: x > 0. lb = 0 (non-strict). Cannot conclude x > 0.
        let atom = make_atom(0, 0, 1, false, true);
        let lb = make_bound(0, 1, false);
        assert_eq!(check_lower_atom_true(&lb, &atom), AtomImplication::Unknown);

        // Atom: x > 0. lb = 0 (strict). x > 0 => implied true.
        let lb_strict = make_bound(0, 1, true);
        assert_eq!(
            check_lower_atom_true(&lb_strict, &atom),
            AtomImplication::ImpliedTrue
        );
    }

    #[test]
    fn test_large_i64_values() {
        // Test with values near i64 limits. The cross-multiply uses i128
        // so overflow is not possible.
        let atom = make_atom(0, i64::MAX / 2, 1, true, false);
        let ub = make_bound(i64::MAX / 2 - 1, 1, false);
        assert_eq!(
            check_upper_atom_true(&ub, &atom),
            AtomImplication::ImpliedTrue
        );
    }
}
