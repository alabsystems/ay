// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! JIT compilation and fast-path dispatch for LRA bound propagation (#8174).
//!
//! Compiles per-variable atom bound checks using i64/i128 cross-multiply
//! arithmetic instead of BigRational. >95% of LIA/LRA bounds are small
//! integers that fit in i64, reducing per-atom comparison cost from ~50ns
//! (BigRational heap alloc) to ~2ns (i128 multiply + compare).
//!
//! ## Lifecycle
//!
//! - `compile_theory_propagation_jit()`: Called after `sort_atom_index()` to
//!   pre-compile per-variable propagators from the atom index.
//! - `try_jit_propagate_var_atoms()`: Called from `propagate_var_atoms()` to
//!   attempt the fast path. Returns `true` if all atoms were handled; `false`
//!   signals the caller to fall back to the interpreted BigRational path.

use super::*;

/// FNV-1a mixing step for the atom-index fingerprint.
#[inline]
fn fnv_mix(h: &mut u64, v: u64) {
    *h ^= v;
    *h = h.wrapping_mul(0x0000_0100_0000_01B3);
}

impl LraSolver {
    /// Atom-index fingerprint for JIT propagator validity (Fix A1,
    /// lia-hot-loop-plan.md §3.8): `(entry count, hash)` over every
    /// `(var, bound_numer, bound_denom, is_upper, strict, is_small)` tuple,
    /// positional within each variable (atom positions are semantic: the JIT
    /// reports positions into `atom_index[var]`), order-independent across
    /// variables (`HashMap` iteration order).
    ///
    /// Term identity is deliberately excluded: compiled tables encode only
    /// (position, bound value, direction, strictness, smallness), and
    /// `try_jit_propagate_var_atoms` resolves positions against the *live*
    /// `atom_index` — so two atom indices with identical tuples yield
    /// identical propagator behavior regardless of `TermId`s.
    pub(crate) fn atom_index_jit_fingerprint(&self) -> ay_jit::TheoryPropFingerprint {
        let mut count: u64 = 0;
        let mut combined: u64 = 0;
        for (&var, atoms) in &self.atom_index {
            // FNV-1a offset basis.
            let mut h: u64 = 0xCBF2_9CE4_8422_2325;
            fnv_mix(&mut h, u64::from(var));
            for atom_ref in atoms {
                let (is_small, numer, denom) = rational_to_i64(&atom_ref.bound_value);
                fnv_mix(&mut h, u64::from(is_small));
                fnv_mix(&mut h, numer as u64);
                fnv_mix(&mut h, denom as u64);
                fnv_mix(&mut h, u64::from(atom_ref.is_upper));
                fnv_mix(&mut h, u64::from(atom_ref.strict));
                count += 1;
            }
            combined = combined.wrapping_add(h);
        }
        (count, combined)
    }

    /// Compile JIT propagators from the current `atom_index`.
    ///
    /// Iterates all `(var, Vec<AtomRef>)` entries, converts each `AtomRef`'s
    /// `Rational` bound value to `i64` numerator/denominator when possible,
    /// and feeds the result into `TheoryPropJit::compile_fingerprinted()`.
    ///
    /// Should be called once after atom registration is complete (e.g., after
    /// `sort_atom_index()`).
    ///
    /// Fix A1: when the JIT was persisted across solver instances (structural
    /// snapshot) or this is a same-instance recompile with an unchanged atom
    /// index, the atom-index fingerprint matches and the rebuild is skipped
    /// entirely — no table rebuild, no native re-emission.
    pub(crate) fn compile_theory_propagation_jit(&mut self) {
        let fingerprint = self.atom_index_jit_fingerprint();
        // JIT persistence (Fix A1) is always on: the former
        // `AY_LRA_JIT_PERSIST` kill-switch is removed (on was the default).
        if self.theory_prop_jit.fingerprint() == Some(fingerprint) {
            self.theory_prop_jit_compiled = true;
            return;
        }
        let var_atoms_iter = self.atom_index.iter().map(|(&var, atoms)| {
            let bound_atoms: Vec<ay_jit::BoundAtom> = atoms
                .iter()
                .enumerate()
                .map(|(idx, atom_ref)| {
                    let (is_small, numer, denom) = rational_to_i64(&atom_ref.bound_value);
                    ay_jit::BoundAtom {
                        atom_index: idx as u32,
                        bound_numer: numer,
                        bound_denom: denom,
                        is_upper: atom_ref.is_upper,
                        strict: atom_ref.strict,
                        is_small,
                    }
                })
                .collect();
            (var, bound_atoms)
        });
        // Collect to Vec since compile() takes IntoIterator and we can't
        // hold an immutable borrow on self.atom_index while mutating self.
        let entries: Vec<(u32, Vec<ay_jit::BoundAtom>)> = var_atoms_iter.collect();
        self.theory_prop_jit
            .compile_fingerprinted(entries, Some(fingerprint));
        self.theory_prop_jit_compiled = true;
    }

    /// Convenience wrapper that compiles the JIT and sets the compiled flag.
    /// Used from tests and from the lazy compilation path in `propagate_var_atoms`.
    #[allow(dead_code)]
    pub(crate) fn compile_theory_prop_jit(&mut self) {
        self.compile_theory_propagation_jit();
    }

    /// Convert a `Bound` to a `SmallBound` if the bound value is `Rational::Small`.
    /// Returns `None` for `Rational::Big` values.
    #[allow(dead_code)]
    pub(crate) fn bound_to_small_bound(bound: &Bound) -> Option<ay_jit::SmallBound> {
        match &bound.value {
            Rational::Small(n, d) => Some(ay_jit::SmallBound {
                numer: *n,
                denom: *d,
                strict: bound.strict,
            }),
            Rational::Big(_) => None,
        }
    }

    /// Attempt JIT fast-path propagation for a single variable's atoms.
    ///
    /// Returns `true` if all atoms for this variable were handled by the JIT
    /// (all atoms are small-int). Returns `false` if the variable has no JIT
    /// propagator, or if any atom has a non-small bound value — the caller
    /// must fall back to the interpreted `propagate_var_atoms()` path.
    ///
    /// Semantics match `propagate_var_atoms()` exactly: checks `asserted` and
    /// `propagated_atoms`, eagerly collects bound reasons, and queues
    /// `PendingPropagation::eager()` entries.
    pub(crate) fn try_jit_propagate_var_atoms(&mut self, var: u32) -> bool {
        // Check if a JIT propagator exists for this variable.
        if !self.theory_prop_jit.has_propagator(var) {
            return false;
        }
        let fully_handled = self.theory_prop_jit.variable_is_fully_small(var);

        let vi = var as usize;
        let Some(info) = self.vars.get(vi) else {
            return false;
        };

        // Extract lb/ub as SmallBound. If either bound exists but is not
        // Small, we cannot use the JIT path — fall back entirely.
        let lb_small = match info.lower.as_ref() {
            Some(b) => match &b.value {
                Rational::Small(n, d) => Some(ay_jit::SmallBound {
                    numer: *n,
                    denom: *d,
                    strict: b.strict,
                }),
                Rational::Big(_) => return false,
            },
            None => None,
        };

        let ub_small = match info.upper.as_ref() {
            Some(b) => match &b.value {
                Rational::Small(n, d) => Some(ay_jit::SmallBound {
                    numer: *n,
                    denom: *d,
                    strict: b.strict,
                }),
                Rational::Big(_) => return false,
            },
            None => None,
        };

        // Run the JIT propagator.
        self.theory_prop_jit
            .propagate_var(var, lb_small, ub_small, &mut self.theory_prop_results);

        if self.theory_prop_results.is_empty() {
            return fully_handled;
        }

        // #8467: Use deferred reasons (same as propagate_var_atoms).
        // Instead of eagerly collecting Vec<TheoryLit> reasons here, use
        // DeferredReason::DirectBound. Reasons are materialized later in
        // propagate_impl() only for propagations that survive the stale-reason
        // filter. This eliminates O(reason_len) allocation per JIT propagation.
        let has_ub = self.vars.get(vi).is_some_and(|info| info.upper.is_some());
        let has_lb = self.vars.get(vi).is_some_and(|info| info.lower.is_some());

        // Swap atoms out of atom_index instead of cloning Vec<AtomRef>.
        // The caller may still need the interpreted fallback when the JIT only
        // handles small-bound atoms, so restore before returning.
        let atoms = match self.atom_index.get_mut(&var).map(std::mem::take) {
            Some(atoms) => atoms,
            None => return true,
        };

        // Process each JIT result.
        for result in &self.theory_prop_results {
            let atom_idx = result.atom_index as usize;
            if atom_idx >= atoms.len() {
                continue;
            }
            let atom = &atoms[atom_idx];

            // Skip already-asserted atoms.
            if self.asserted.contains_key(&atom.term) {
                continue;
            }

            // Skip already-propagated atoms.
            if self
                .propagated_atoms
                .contains(&(atom.term, result.implied_value))
            {
                continue;
            }

            // Select the appropriate deferred reason based on the implication direction.
            // For implied TRUE:
            //   - Upper atom (x <= k): reason is ub (need_upper=true)
            //   - Lower atom (x >= k): reason is lb (need_upper=false)
            // For implied FALSE:
            //   - Upper atom (x <= k): reason is lb (need_upper=false)
            //   - Lower atom (x >= k): reason is ub (need_upper=true)
            let (need_upper, has_bound) = if result.implied_value {
                if atom.is_upper {
                    (true, has_ub)
                } else {
                    (false, has_lb)
                }
            } else {
                if atom.is_upper {
                    (false, has_lb)
                } else {
                    (true, has_ub)
                }
            };

            if has_bound {
                self.propagated_atoms
                    .insert((atom.term, result.implied_value));
                self.pending_propagations.push(PendingPropagation::deferred(
                    TheoryLit::new(atom.term, result.implied_value),
                    DeferredReason::DirectBound { var, need_upper },
                ));
                self.stats.jit_propagation_count += 1;
            }
        }

        if let Some(slot) = self.atom_index.get_mut(&var) {
            *slot = atoms;
        } else if !atoms.is_empty() {
            self.atom_index.insert(var, atoms);
        }

        fully_handled
    }
}

/// Convert a `Rational` to `(is_small, numerator, denominator)`.
///
/// Returns `(true, n, d)` directly for `Rational::Small`.
/// Returns `(true, n, d)` for `Rational::Big` if both numer/denom fit in i64.
/// Returns `(false, 0, 1)` otherwise (placeholder values, atom skipped by JIT).
fn rational_to_i64(r: &Rational) -> (bool, i64, i64) {
    match r {
        Rational::Small(n, d) => (true, *n, *d),
        Rational::Big(br) => {
            // `numer()`/`denom()` return `&BigInt`; both expose a fallible
            // i64 conversion.
            let (n_opt, d_opt) = (
                num_traits::ToPrimitive::to_i64(br.numer()),
                num_traits::ToPrimitive::to_i64(br.denom()),
            );
            match (n_opt, d_opt) {
                (Some(n), Some(d)) if d > 0 => (true, n, d),
                (Some(n), Some(d)) if d < 0 => (true, -n, -d),
                _ => (false, 0, 1),
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rational_to_i64_small_integer() {
        let r = Rational::from(42);
        let (is_small, n, d) = rational_to_i64(&r);
        assert!(is_small);
        assert_eq!(n, 42);
        assert_eq!(d, 1);
    }

    #[test]
    fn test_rational_to_i64_fraction() {
        let r = Rational::Small(3, 7);
        let (is_small, n, d) = rational_to_i64(&r);
        assert!(is_small);
        assert_eq!(n, 3);
        assert_eq!(d, 7);
    }

    #[test]
    fn test_rational_to_i64_negative() {
        let r = Rational::Small(-5, 3);
        let (is_small, n, d) = rational_to_i64(&r);
        assert!(is_small);
        assert_eq!(n, -5);
        assert_eq!(d, 3);
    }

    #[test]
    fn test_rational_to_i64_large_value() {
        // Value that exceeds i64 range, forcing the Big variant via the public
        // overflow path (the pure-Rust `BigRational` backing).
        let r = Rational::from(i64::MAX) * Rational::from(2i64);
        assert!(!r.is_small());
        let (is_small, _, _) = rational_to_i64(&r);
        assert!(!is_small);
    }

    #[test]
    fn test_rational_to_i64_zero() {
        let r = Rational::from(0);
        let (is_small, n, d) = rational_to_i64(&r);
        assert!(is_small);
        assert_eq!(n, 0);
        assert_eq!(d, 1);
    }
}
