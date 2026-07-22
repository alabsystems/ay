// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Root EDAC/VAC-lite lower-bound probe over a reconstructed WCSP view of a
//! WBO instance (campaign soft-1).
//!
//! # Premise (measured)
//! The PB24 WBO `wcsp` families encode weighted CSPs verbatim
//! (`proofs/evidence/pbcomp/wbo-structure-census-2026-07-11/README.md`):
//! 100.0% of their soft mass is forbidden-tuple softs over explicit one-hot
//! domains, 99.9% of it binary. The shapes are exact:
//!
//! * hard domain rows:  `+1 x1 +1 x2 ... +1 xk = 1`   (one-hot value groups)
//! * binary tuple soft: `[w] -1 xa -1 xb >= -1`        (pay `w` iff `xa AND xb`,
//!   `xa`/`xb` in DIFFERENT domains)
//! * unary soft:        `[w] -1 xa >= 0`               (pay `w` iff `xa`)
//!
//! # What this module does
//! 1. [`reconstruct_wcsp_view`] rebuilds the WCSP: disjoint one-hot domains
//!    from the `= 1` unit rows, per-(domain,value) unary cost vectors, and
//!    per-domain-pair binary cost matrices, with `c0 = 0`. It DECLINES
//!    (returns `None`) on ANY soft that does not match the unary/binary tuple
//!    shape over the detected domains — it never guesses.
//! 2. [`run_wcsp_transfer`] runs bounded rounds of the standard
//!    soft-arc-consistency cost projections (binary→unary, unary→c0) with
//!    checked integer arithmetic, recording EVERY projection in an audit
//!    trail.
//! 3. [`check_wcsp_transfer_trail`] independently replays the trail against a
//!    FRESH reconstruction (the `refutation_check` house pattern: the verdict
//!    input is re-derived, not trusted from the engine) and verifies every
//!    projection plus the final `c0`.
//! 4. [`wcsp_root_edac_probe`] composes 1–3 and returns `Some` ONLY when the
//!    independent trail check passed, so a caller holding a probe result may
//!    rely on its `c0` by construction.
//!
//! # Soundness argument for `c0`
//! Both projection kinds are classical equivalence-preserving transfers of
//! the WCSP cost function (Cooper & Schiex, "Arc consistency for soft
//! constraints", AIJ 2004):
//!
//! * **binary→unary** for pair `(D1, D2)`, value `a` of `D1`:
//!   `delta = min_b C(a, b)`. Every complete assignment with `D1 = a` selects
//!   exactly one `b` (the `= 1` rows are hard), so it pays at least `delta`
//!   inside the matrix; moving `delta` from row `a` to `unary[D1][a]` changes
//!   no assignment's total cost. Symmetrically for values of `D2`.
//! * **unary→c0** for domain `D`: `delta = min_v U[v]`. Every complete
//!   assignment selects exactly one value of `D`, so it pays at least `delta`
//!   in `U`; moving `delta` from all of `U` to `c0` changes no total cost.
//!
//! All stored costs remain `>= 0` (checked at every step), so after any
//! prefix of the trail the residual problem cost is `>= 0` and therefore
//! EVERY assignment that satisfies the hard one-hot rows pays a total soft
//! cost `>= c0`. Assignments violating a hard row are not WBO models at all.
//! Official WBO semantics admit only models whose falsified-soft cost is
//! STRICTLY LESS than the `soft:` top cost, hence `c0 >= top` proves the
//! instance UNSATISFIABLE. Extra hard constraints beyond the domain rows only
//! shrink the model set further, so ignoring them keeps `c0` a valid lower
//! bound (over a superset of the models).
//!
//! A verdict may rely on `c0` ONLY after [`check_wcsp_transfer_trail`]
//! passed; [`wcsp_root_edac_probe`] enforces this by construction.

use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::atomic::{AtomicBool, Ordering};
use std::time::{Duration, Instant};

use crate::types::{PbRel, WboInstance};

/// Opt-in gate for the root EDAC/VAC-lite probe: `AY_PB_WCSP_EDAC` ∈
/// {`1`, `true`, `yes`, `on`}. Default OFF (same pattern as `AY_PB_BNB`).
#[must_use]
pub fn wcsp_edac_enabled() -> bool {
    std::env::var_os("AY_PB_WCSP_EDAC").is_some_and(|v| {
        matches!(
            v.to_str().map(str::trim),
            Some("1") | Some("true") | Some("yes") | Some("on")
        )
    })
}

/// Transfer time budget in milliseconds: `AY_PB_WCSP_EDAC_MS`, default 2000.
/// Unparseable values fall back to the default (fail-closed toward LESS
/// probe work, never more).
fn wcsp_edac_budget_ms() -> u64 {
    const DEFAULT_MS: u64 = 2000;
    std::env::var("AY_PB_WCSP_EDAC_MS")
        .ok()
        .and_then(|v| v.trim().parse::<u64>().ok())
        .unwrap_or(DEFAULT_MS)
}

/// A CHECKED root probe result: `c0` is a floor on the falsified-soft cost of
/// every assignment satisfying the instance's hard one-hot rows, and the
/// audit trail deriving it has passed the independent
/// [`check_wcsp_transfer_trail`] replay (enforced by construction — this type
/// is only ever built by [`wcsp_root_edac_probe`] after the check).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct WcspEdacProbe {
    /// Trail-checked lower bound on the total soft cost of every assignment
    /// satisfying the hard domain rows (and a fortiori every WBO model).
    pub c0: i128,
    /// Number of audited projections that derived `c0`.
    pub trail_len: usize,
    /// Whether the projection fixpoint was reached (vs. a budget stop; `c0`
    /// is sound either way).
    pub fixpoint: bool,
    /// Number of reconstructed one-hot domains.
    pub num_domains: usize,
}

/// Runs the full root probe: reconstruct → transfer (budgeted by
/// `AY_PB_WCSP_EDAC_MS`, default 2000 ms, `term_flag` polled) → INDEPENDENT
/// trail replay. Returns `Some` only if reconstruction succeeded AND the
/// checker certified the trail; on `None` the caller learns nothing (decline
/// / stop / arithmetic failure / failed check are indistinguishable, by
/// design — never guess).
#[must_use]
pub fn wcsp_root_edac_probe(
    wbo: &WboInstance,
    term_flag: Option<&AtomicBool>,
) -> Option<WcspEdacProbe> {
    let mut view = reconstruct_wcsp_view(wbo)?;
    let num_domains = view.domains.len();
    let deadline = Instant::now().checked_add(Duration::from_millis(wcsp_edac_budget_ms()));
    let outcome = run_wcsp_transfer(&mut view, deadline, term_flag)?;
    if !check_wcsp_transfer_trail(wbo, &outcome.trail, outcome.c0) {
        return None;
    }
    Some(WcspEdacProbe {
        c0: outcome.c0,
        trail_len: outcome.trail.len(),
        fixpoint: outcome.fixpoint,
        num_domains,
    })
}

/// Reconstructed WCSP view of a WBO instance (see the module docs).
///
/// Invariant established by [`reconstruct_wcsp_view`] and preserved by
/// [`run_wcsp_transfer`]: every stored cost (`unary`, `binary`, `c0`) is
/// `>= 0`.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WcspView {
    /// `domains[d]` = the variables of one-hot group `d`, in row order.
    pub(crate) domains: Vec<Vec<u32>>,
    /// `unary[d][v]` = accumulated unary cost of assigning value `v` (i.e.
    /// setting variable `domains[d][v]` true) in domain `d`. Always `>= 0`.
    pub(crate) unary: Vec<Vec<i128>>,
    /// Binary cost matrices keyed by `(d1, d2)` with `d1 < d2`;
    /// `matrix[a][b]` is the cost of `domains[d1][a] AND domains[d2][b]`.
    /// Deterministically ordered (BTreeMap) so the transfer trail is
    /// reproducible. Always `>= 0`.
    pub(crate) binary: BTreeMap<(usize, usize), Vec<Vec<i128>>>,
    /// Cost floor already proven (starts at 0; raised by unary→c0 transfers).
    pub(crate) c0: i128,
}

/// Reconstructs the WCSP view from a parsed WBO instance, or declines.
///
/// DECLINE (`None`) — never guess — on any of:
/// * a soft constraint not matching the exact unary (`[w] -1 xa >= 0`) or
///   binary (`[w] -1 xa -1 xb >= -1`) forbidden-tuple shape (this covers
///   arity > 2, non-unit/positive coefficients, negated literals, non-linear
///   terms, wrong relation or RHS, and duplicated variables);
/// * a negative soft cost;
/// * a soft variable outside every detected domain;
/// * a binary soft whose two variables share a domain;
/// * overlapping domains (a variable in two `= 1` unit rows);
/// * cost accumulation overflow (checked arithmetic).
///
/// Hard rows that are not one-hot domain rows are IGNORED: they only shrink
/// the model set, so the derived floor stays sound (module docs).
pub(crate) fn reconstruct_wcsp_view(wbo: &WboInstance) -> Option<WcspView> {
    // --- Pass 1: domains from the `= 1` unit rows. ---
    let mut domains: Vec<Vec<u32>> = Vec::new();
    let mut var_pos: HashMap<u32, (usize, usize)> = HashMap::new();
    for hard in &wbo.hard_constraints {
        if hard.rel != PbRel::Eq || hard.rhs != 1 || hard.terms.is_empty() {
            continue;
        }
        let mut row: Vec<u32> = Vec::with_capacity(hard.terms.len());
        let mut is_domain_row = true;
        for term in &hard.terms {
            let [lit] = term.lits.as_slice() else {
                is_domain_row = false;
                break;
            };
            if term.coeff != 1 || lit.negated {
                is_domain_row = false;
                break;
            }
            row.push(lit.var);
        }
        if !is_domain_row {
            continue;
        }
        // Duplicate variable inside the row: not a one-hot group; skip the
        // row (its vars, if soft-referenced and in no other domain, decline
        // below).
        let mut seen: HashSet<u32> = HashSet::with_capacity(row.len());
        if !row.iter().all(|v| seen.insert(*v)) {
            continue;
        }
        let d = domains.len();
        for (v, var) in row.iter().enumerate() {
            // Overlapping domains: DECLINE the whole reconstruction.
            if var_pos.insert(*var, (d, v)).is_some() {
                return None;
            }
        }
        domains.push(row);
    }

    // --- Pass 2: softs into unary vectors / binary matrices. ---
    let mut unary: Vec<Vec<i128>> = domains.iter().map(|d| vec![0_i128; d.len()]).collect();
    let mut binary: BTreeMap<(usize, usize), Vec<Vec<i128>>> = BTreeMap::new();
    for (cost, soft) in &wbo.soft_constraints {
        if *cost < 0 || soft.rel != PbRel::Ge {
            return None;
        }
        let mut positions: Vec<(usize, usize)> = Vec::with_capacity(soft.terms.len());
        for term in &soft.terms {
            let [lit] = term.lits.as_slice() else {
                return None;
            };
            if term.coeff != -1 || lit.negated {
                return None;
            }
            // Soft variable outside every domain: DECLINE.
            positions.push(*var_pos.get(&lit.var)?);
        }
        match positions.as_slice() {
            // Unary `[w] -1 xa >= 0`: pay `w` iff `xa`.
            [(d, v)] => {
                if soft.rhs != 0 {
                    return None;
                }
                let slot = &mut unary[*d][*v];
                *slot = slot.checked_add(*cost)?;
            }
            // Binary `[w] -1 xa -1 xb >= -1`: pay `w` iff `xa AND xb`,
            // in different domains.
            [(d1, v1), (d2, v2)] => {
                if soft.rhs != -1 || d1 == d2 {
                    return None;
                }
                let ((dl, vl), (dh, vh)) = if d1 < d2 {
                    ((*d1, *v1), (*d2, *v2))
                } else {
                    ((*d2, *v2), (*d1, *v1))
                };
                let matrix = binary
                    .entry((dl, dh))
                    .or_insert_with(|| vec![vec![0_i128; domains[dh].len()]; domains[dl].len()]);
                let slot = &mut matrix[vl][vh];
                *slot = slot.checked_add(*cost)?;
            }
            // Arity 0 or > 2 (0.1% of the corpus soft mass): fail-closed.
            _ => return None,
        }
    }

    Some(WcspView {
        domains,
        unary,
        binary,
        c0: 0,
    })
}

/// One equivalence-preserving cost projection, as recorded in the audit
/// trail. `delta` is always the FULL minimum at application time (the engine
/// only records strictly positive deltas; the checker verifies
/// `delta == min` at replay time, which subsumes non-negativity).
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum WcspProjection {
    /// Moved `delta` from row/column `value` of the binary matrix of the
    /// domain pair `(d_low, d_high)` (`d_low < d_high`) into the unary vector
    /// of `d_low` (`to_low == true`, `value` indexes `d_low`'s values /
    /// matrix rows) or of `d_high` (`to_low == false`, `value` indexes
    /// `d_high`'s values / matrix columns).
    BinaryToUnary {
        d_low: usize,
        d_high: usize,
        to_low: bool,
        value: usize,
        delta: i128,
    },
    /// Moved `delta` from EVERY unary cost of `domain` into `c0`.
    UnaryToC0 { domain: usize, delta: i128 },
}

/// Result of [`run_wcsp_transfer`]: the proven floor, the full audit trail
/// that derives it, and whether the projection fixpoint was reached (vs. an
/// early stop on the time budget / term flag — the trail prefix, and hence
/// `c0`, stays sound either way).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) struct WcspTransferOutcome {
    pub(crate) c0: i128,
    pub(crate) trail: Vec<WcspProjection>,
    pub(crate) fixpoint: bool,
}

/// Runs bounded rounds of soft-arc-consistency cost projections on `view`
/// until fixpoint, deadline, or term-flag stop (polled between passes).
///
/// Round structure: every binary matrix projects its row minima into the low
/// domain's unary vector and its column minima into the high domain's, then
/// every domain projects its unary minimum into `c0`. Projections only move
/// cost downward (binary→unary→c0, no extensions), so a full no-op round is
/// a true fixpoint — reached after at most two rounds with this ordering.
///
/// All arithmetic is checked; `None` means an arithmetic invariant failed
/// (fail-closed — the caller must not use any bound). Every applied
/// projection is appended to the returned audit trail in order.
pub(crate) fn run_wcsp_transfer(
    view: &mut WcspView,
    deadline: Option<Instant>,
    term_flag: Option<&AtomicBool>,
) -> Option<WcspTransferOutcome> {
    let should_stop = || {
        term_flag.is_some_and(|flag| flag.load(Ordering::Relaxed))
            || deadline.is_some_and(|d| Instant::now() >= d)
    };
    let mut trail: Vec<WcspProjection> = Vec::new();
    let mut fixpoint = false;
    let mut stopped = false;
    while !stopped {
        let mut changed = false;
        // --- binary -> unary, one pass per matrix. ---
        for (&(d_low, d_high), matrix) in &mut view.binary {
            if should_stop() {
                stopped = true;
                break;
            }
            let n_low = matrix.len();
            let n_high = view.domains[d_high].len();
            // Row minima into the low domain's unary vector.
            for a in 0..n_low {
                let delta = matrix[a].iter().copied().min()?;
                if delta < 0 {
                    return None; // negative cost: invariant broken, fail closed
                }
                if delta == 0 {
                    continue;
                }
                for cell in &mut matrix[a] {
                    *cell = cell.checked_sub(delta)?;
                    if *cell < 0 {
                        return None;
                    }
                }
                let slot = &mut view.unary[d_low][a];
                *slot = slot.checked_add(delta)?;
                trail.push(WcspProjection::BinaryToUnary {
                    d_low,
                    d_high,
                    to_low: true,
                    value: a,
                    delta,
                });
                changed = true;
            }
            // Column minima into the high domain's unary vector.
            for b in 0..n_high {
                let delta = (0..n_low).map(|a| matrix[a][b]).min()?;
                if delta < 0 {
                    return None; // negative cost: invariant broken, fail closed
                }
                if delta == 0 {
                    continue;
                }
                for row in matrix.iter_mut() {
                    row[b] = row[b].checked_sub(delta)?;
                    if row[b] < 0 {
                        return None;
                    }
                }
                let slot = &mut view.unary[d_high][b];
                *slot = slot.checked_add(delta)?;
                trail.push(WcspProjection::BinaryToUnary {
                    d_low,
                    d_high,
                    to_low: false,
                    value: b,
                    delta,
                });
                changed = true;
            }
        }
        if stopped {
            break;
        }
        // --- unary -> c0, one pass per domain. ---
        for domain in 0..view.unary.len() {
            if should_stop() {
                stopped = true;
                break;
            }
            let delta = match view.unary[domain].iter().copied().min() {
                Some(delta) => delta,
                None => continue, // empty domain cannot occur (rows non-empty)
            };
            if delta < 0 {
                return None; // negative cost: invariant broken, fail closed
            }
            if delta == 0 {
                continue;
            }
            for slot in &mut view.unary[domain] {
                *slot = slot.checked_sub(delta)?;
                if *slot < 0 {
                    return None;
                }
            }
            view.c0 = view.c0.checked_add(delta)?;
            trail.push(WcspProjection::UnaryToC0 { domain, delta });
            changed = true;
        }
        if stopped {
            break;
        }
        if !changed {
            fixpoint = true;
            break;
        }
    }
    Some(WcspTransferOutcome {
        c0: view.c0,
        trail,
        fixpoint,
    })
}

/// Independently replays a transfer trail against a FRESH reconstruction and
/// verifies the claimed floor (the `refutation_check` house pattern: nothing
/// the engine computed is trusted — the checker re-derives the WCSP view from
/// the instance and re-computes every minimum itself).
///
/// Verified per step, fail-closed on any violation:
/// * all indices in range for the fresh reconstruction (the trail is
///   untrusted input);
/// * `delta >= 0` and `delta` EQUALS the minimum of the projected row /
///   column / unary vector at replay time (equality subsumes the
///   "non-negativity preserved" requirement: subtracting the exact minimum
///   leaves the vector `>= 0`, which is additionally re-checked);
/// * all arithmetic checked;
/// * the final accumulated `c0` equals `claimed_c0`.
///
/// A verdict may rely on a probe's `c0` ONLY if this function returns `true`.
pub(crate) fn check_wcsp_transfer_trail(
    wbo: &WboInstance,
    trail: &[WcspProjection],
    claimed_c0: i128,
) -> bool {
    let Some(mut view) = reconstruct_wcsp_view(wbo) else {
        return false;
    };
    for step in trail {
        match *step {
            WcspProjection::BinaryToUnary {
                d_low,
                d_high,
                to_low,
                value,
                delta,
            } => {
                if d_low >= d_high || d_high >= view.domains.len() || delta < 0 {
                    return false;
                }
                let Some(matrix) = view.binary.get_mut(&(d_low, d_high)) else {
                    return false;
                };
                if to_low {
                    // Row projection into unary[d_low][value].
                    let Some(row) = matrix.get_mut(value) else {
                        return false;
                    };
                    let Some(min) = row.iter().copied().min() else {
                        return false;
                    };
                    if delta != min {
                        return false;
                    }
                    for cell in row.iter_mut() {
                        let Some(next) = cell.checked_sub(delta) else {
                            return false;
                        };
                        if next < 0 {
                            return false;
                        }
                        *cell = next;
                    }
                    let Some(slot) = view.unary.get_mut(d_low).and_then(|u| u.get_mut(value))
                    else {
                        return false;
                    };
                    let Some(next) = slot.checked_add(delta) else {
                        return false;
                    };
                    *slot = next;
                } else {
                    // Column projection into unary[d_high][value].
                    let mut min: Option<i128> = None;
                    for row in matrix.iter() {
                        let Some(&cell) = row.get(value) else {
                            return false;
                        };
                        min = Some(min.map_or(cell, |m| m.min(cell)));
                    }
                    let Some(min) = min else {
                        return false;
                    };
                    if delta != min {
                        return false;
                    }
                    for row in matrix.iter_mut() {
                        let Some(next) = row[value].checked_sub(delta) else {
                            return false;
                        };
                        if next < 0 {
                            return false;
                        }
                        row[value] = next;
                    }
                    let Some(slot) = view.unary.get_mut(d_high).and_then(|u| u.get_mut(value))
                    else {
                        return false;
                    };
                    let Some(next) = slot.checked_add(delta) else {
                        return false;
                    };
                    *slot = next;
                }
            }
            WcspProjection::UnaryToC0 { domain, delta } => {
                if delta < 0 {
                    return false;
                }
                let Some(vector) = view.unary.get_mut(domain) else {
                    return false;
                };
                let Some(min) = vector.iter().copied().min() else {
                    return false;
                };
                if delta != min {
                    return false;
                }
                for slot in vector.iter_mut() {
                    let Some(next) = slot.checked_sub(delta) else {
                        return false;
                    };
                    if next < 0 {
                        return false;
                    }
                    *slot = next;
                }
                let Some(next) = view.c0.checked_add(delta) else {
                    return false;
                };
                view.c0 = next;
            }
        }
    }
    view.c0 == claimed_c0
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::parser::parse_wbo;
    use crate::types::{PbConstraint, PbLit, PbTerm};

    fn wbo(text: &str) -> WboInstance {
        parse_wbo(text).expect("test WBO must parse")
    }

    // ------------------------------------------------------------------
    // Reconstructor: handwritten accept cases
    // ------------------------------------------------------------------

    #[test]
    fn reconstructs_two_domains_with_unary_and_binary_softs() {
        let instance = wbo(concat!(
            "soft: 10 ;\n",
            "+1 x1 +1 x2 +1 x3 = 1 ;\n",
            "+1 x4 +1 x5 = 1 ;\n",
            "[3] -1 x2 >= 0 ;\n",
            "[4] -1 x1 -1 x4 >= -1 ;\n",
            "[2] -1 x3 -1 x5 >= -1 ;\n",
            "[1] -1 x5 -1 x3 >= -1 ;\n", // reversed order, same cell as above
        ));
        let view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        assert_eq!(view.domains, vec![vec![1, 2, 3], vec![4, 5]]);
        assert_eq!(view.unary, vec![vec![0, 3, 0], vec![0, 0]]);
        assert_eq!(view.binary.len(), 1);
        let m = &view.binary[&(0, 1)];
        // C(x1, x4) = 4; C(x3, x5) accumulates 2 + 1 = 3.
        assert_eq!(m, &vec![vec![4, 0], vec![0, 0], vec![0, 3]]);
        assert_eq!(view.c0, 0);
    }

    #[test]
    fn accumulates_repeated_unary_softs_and_singleton_domains() {
        let instance = wbo(concat!(
            "soft: 9 ;\n",
            "+1 x1 = 1 ;\n",
            "[2] -1 x1 >= 0 ;\n",
            "[5] -1 x1 >= 0 ;\n",
        ));
        let view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        assert_eq!(view.domains, vec![vec![1]]);
        assert_eq!(view.unary, vec![vec![7]]);
        assert!(view.binary.is_empty());
    }

    #[test]
    fn ignores_non_domain_hard_rows_when_softs_stay_inside_domains() {
        // The extra `>=` hard row and the weighted `= 1` row are not domain
        // rows; they are ignored (sound: they only shrink the model set).
        let instance = wbo(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "+1 x3 +1 x4 = 1 ;\n",
            "+1 x1 +1 x3 >= 1 ;\n",
            "+2 x5 +1 x6 = 1 ;\n",
            "[1] -1 x1 -1 x3 >= -1 ;\n",
        ));
        let view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        assert_eq!(view.domains, vec![vec![1, 2], vec![3, 4]]);
        assert_eq!(view.binary[&(0, 1)], vec![vec![1, 0], vec![0, 0]]);
    }

    #[test]
    fn zero_cost_soft_is_accepted_and_adds_nothing() {
        let instance = wbo(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[0] -1 x1 >= 0 ;\n",
        ));
        let view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        assert_eq!(view.unary, vec![vec![0, 0]]);
    }

    // ------------------------------------------------------------------
    // Reconstructor: real corpus instances (PB24 WBO/PARTIAL-LIN/wcsp)
    // ------------------------------------------------------------------

    fn load_fixture(name: &str) -> WboInstance {
        let path = format!("{}/tests/instances/{name}", env!("CARGO_MANIFEST_DIR"));
        let text =
            std::fs::read_to_string(&path).unwrap_or_else(|e| panic!("failed to read {path}: {e}"));
        parse_wbo(&text).unwrap_or_else(|e| panic!("failed to parse {path}: {e}"))
    }

    #[test]
    fn reconstructs_real_warehouse0_instance() {
        // normalized-warehouse0_wcsp.wbo: 15 one-hot domains (10 client
        // domains of 5 values over x1..x50, 5 warehouse domains of 2 values
        // over x51..x60), 55 unary + 50 binary softs.
        let instance = load_fixture("wcsp_warehouse0.wbo");
        let view = reconstruct_wcsp_view(&instance).expect("warehouse0 must reconstruct");
        assert_eq!(view.domains.len(), 15);
        assert_eq!(
            view.domains.iter().map(Vec::len).sum::<usize>(),
            60,
            "every variable lives in exactly one domain"
        );
        // `[30] -1 x52 >= 0`: x52 is value 1 of domain 10 ({x51, x52}).
        assert_eq!(view.domains[10], vec![51, 52]);
        assert_eq!(view.unary[10][1], 30);
        // `[954] -1 x1 -1 x51 >= -1`: cell (0,0) of pair (domain 0, domain 10).
        assert_eq!(view.binary[&(0, 10)][0][0], 954);
        // Non-negativity invariant over the whole reconstruction.
        assert!(view.unary.iter().flatten().all(|&c| c >= 0));
        assert!(view.binary.values().flatten().flatten().all(|&c| c >= 0));
        assert_eq!(view.c0, 0);
    }

    #[test]
    fn declines_real_4queens_instance_with_quaternary_softs() {
        // normalized-4queens_wcsp.wbo carries arity-4 forbidden-tuple softs
        // (the rare >2-arity tail of the census): fail-closed DECLINE.
        let instance = load_fixture("wcsp_4queens.wbo");
        assert_eq!(reconstruct_wcsp_view(&instance), None);
    }

    // ------------------------------------------------------------------
    // Reconstructor: decline (fail-closed) cases
    // ------------------------------------------------------------------

    fn declines(text: &str) {
        let instance = wbo(text);
        assert_eq!(
            reconstruct_wcsp_view(&instance),
            None,
            "must DECLINE: {text}"
        );
    }

    #[test]
    fn declines_arity_three_soft() {
        declines(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "+1 x3 +1 x4 = 1 ;\n",
            "+1 x5 +1 x6 = 1 ;\n",
            "[1] -1 x1 -1 x3 -1 x5 >= -2 ;\n",
        ));
    }

    #[test]
    fn declines_soft_variable_outside_all_domains() {
        declines(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[1] -1 x1 -1 x9 >= -1 ;\n",
        ));
    }

    #[test]
    fn declines_binary_soft_inside_one_domain() {
        declines(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 +1 x3 = 1 ;\n",
            "[1] -1 x1 -1 x2 >= -1 ;\n",
        ));
    }

    #[test]
    fn declines_overlapping_domains() {
        declines(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "+1 x2 +1 x3 = 1 ;\n",
            "[1] -1 x1 >= 0 ;\n",
        ));
    }

    #[test]
    fn declines_wrong_unary_rhs() {
        // `-1 x1 >= -1` is trivially satisfied — NOT the unary tuple shape.
        declines(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[1] -1 x1 >= -1 ;\n",
        ));
    }

    #[test]
    fn declines_wrong_binary_rhs() {
        // `>= 0` over two vars means "pay iff xa OR xb" — different semantics.
        declines(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "+1 x3 +1 x4 = 1 ;\n",
            "[1] -1 x1 -1 x3 >= 0 ;\n",
        ));
    }

    #[test]
    fn declines_positive_coefficient_soft() {
        declines(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[1] +1 x1 >= 1 ;\n",
        ));
    }

    #[test]
    fn declines_negated_literal_soft() {
        declines(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[1] -1 ~x1 >= 0 ;\n",
        ));
    }

    #[test]
    fn declines_duplicated_variable_in_binary_soft() {
        declines(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[1] -1 x1 -1 x1 >= -1 ;\n",
        ));
    }

    #[test]
    fn declines_empty_soft() {
        let mut instance = wbo(concat!("soft: 9 ;\n", "+1 x1 +1 x2 = 1 ;\n"));
        instance.soft_constraints.push((
            1,
            PbConstraint {
                terms: vec![],
                rel: PbRel::Ge,
                rhs: 0,
            },
        ));
        assert_eq!(reconstruct_wcsp_view(&instance), None);
    }

    #[test]
    fn declines_negative_soft_cost() {
        let mut instance = wbo(concat!("soft: 9 ;\n", "+1 x1 +1 x2 = 1 ;\n"));
        instance.soft_constraints.push((
            -1,
            PbConstraint {
                terms: vec![PbTerm {
                    coeff: -1,
                    lits: vec![PbLit {
                        var: 1,
                        negated: false,
                    }],
                }],
                rel: PbRel::Ge,
                rhs: 0,
            },
        ));
        assert_eq!(reconstruct_wcsp_view(&instance), None);
    }

    #[test]
    fn declines_nonlinear_soft_term() {
        let mut instance = wbo(concat!("soft: 9 ;\n", "+1 x1 +1 x2 = 1 ;\n"));
        instance.soft_constraints.push((
            1,
            PbConstraint {
                terms: vec![PbTerm {
                    coeff: -1,
                    lits: vec![
                        PbLit {
                            var: 1,
                            negated: false,
                        },
                        PbLit {
                            var: 2,
                            negated: false,
                        },
                    ],
                }],
                rel: PbRel::Ge,
                rhs: 0,
            },
        ));
        assert_eq!(reconstruct_wcsp_view(&instance), None);
    }

    // ------------------------------------------------------------------
    // Transfer engine: projections, trail, fixpoint, budget stops
    // ------------------------------------------------------------------

    #[test]
    fn transfer_moves_uniform_binary_mass_to_c0() {
        // Every (a, b) combination costs 5 => every assignment pays >= 5.
        let instance = wbo(concat!(
            "soft: 5 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "+1 x3 +1 x4 = 1 ;\n",
            "[5] -1 x1 -1 x3 >= -1 ;\n",
            "[5] -1 x1 -1 x4 >= -1 ;\n",
            "[5] -1 x2 -1 x3 >= -1 ;\n",
            "[5] -1 x2 -1 x4 >= -1 ;\n",
        ));
        let mut view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        let outcome = run_wcsp_transfer(&mut view, None, None).expect("transfer must run");
        assert_eq!(outcome.c0, 5);
        assert!(outcome.fixpoint);
        // Two row projections (delta 5 each into domain 0) + one unary->c0.
        assert_eq!(
            outcome.trail,
            vec![
                WcspProjection::BinaryToUnary {
                    d_low: 0,
                    d_high: 1,
                    to_low: true,
                    value: 0,
                    delta: 5
                },
                WcspProjection::BinaryToUnary {
                    d_low: 0,
                    d_high: 1,
                    to_low: true,
                    value: 1,
                    delta: 5
                },
                WcspProjection::UnaryToC0 {
                    domain: 0,
                    delta: 5
                },
            ]
        );
        // Residual costs are fully drained and non-negative.
        assert!(view.unary.iter().flatten().all(|&c| c == 0));
        assert!(view.binary.values().flatten().flatten().all(|&c| c == 0));
    }

    #[test]
    fn transfer_projects_unary_minimum_only() {
        let instance = wbo(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[3] -1 x1 >= 0 ;\n",
            "[5] -1 x2 >= 0 ;\n",
        ));
        let mut view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        let outcome = run_wcsp_transfer(&mut view, None, None).expect("transfer must run");
        assert_eq!(outcome.c0, 3);
        assert!(outcome.fixpoint);
        assert_eq!(view.unary, vec![vec![0, 2]]);
        assert_eq!(
            outcome.trail,
            vec![WcspProjection::UnaryToC0 {
                domain: 0,
                delta: 3
            }]
        );
    }

    #[test]
    fn transfer_row_and_column_projections_compose() {
        // Matrix [[2,3],[4,7]]: row mins 2/4 -> unary0 [2,4]; residual
        // [[0,1],[0,3]]; column mins 0/1 -> unary1 [0,1]; unary0 min 2 -> c0.
        // True per-assignment minimum is C(0,0) = 2, matched exactly here.
        let instance = wbo(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "+1 x3 +1 x4 = 1 ;\n",
            "[2] -1 x1 -1 x3 >= -1 ;\n",
            "[3] -1 x1 -1 x4 >= -1 ;\n",
            "[4] -1 x2 -1 x3 >= -1 ;\n",
            "[7] -1 x2 -1 x4 >= -1 ;\n",
        ));
        let mut view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        let outcome = run_wcsp_transfer(&mut view, None, None).expect("transfer must run");
        assert_eq!(outcome.c0, 2);
        assert!(outcome.fixpoint);
        assert_eq!(view.unary, vec![vec![0, 2], vec![0, 1]]);
        assert_eq!(view.binary[&(0, 1)], vec![vec![0, 0], vec![0, 2]]);
    }

    #[test]
    fn transfer_reaches_fixpoint_on_real_warehouse0_floor_229() {
        // MEASURED BASELINE, cross-checked by hand against the raw softs:
        // every client domain carries a unary cost on each of its 5 values,
        // so the per-domain unary minima drain to c0: 11 + 27 + 70 + 2 + 4 +
        // 22 + 1 + 10 + 35 + 47 = 229. The binary matrices contribute 0
        // (every row has a zero-cost option), and the warehouse domains'
        // unary minima are 0 (closing is free). Projection-only soft AC
        // therefore proves c0 = 229 < top = 954: no UNSAT verdict here, but a
        // nonzero typed floor. Recorded exactly so any strengthening
        // (extensions/VAC) or regression shows up as a deliberate change.
        let instance = load_fixture("wcsp_warehouse0.wbo");
        let mut view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        let outcome = run_wcsp_transfer(&mut view, None, None).expect("transfer must run");
        assert!(outcome.fixpoint);
        assert_eq!(outcome.c0, 229);
        // Exactly the 10 client-domain unary->c0 drains, no binary motion.
        assert_eq!(outcome.trail.len(), 10);
        assert!(outcome
            .trail
            .iter()
            .all(|p| matches!(p, WcspProjection::UnaryToC0 { .. })));
    }

    #[test]
    fn transfer_stops_immediately_on_expired_deadline() {
        let instance = wbo(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[3] -1 x1 >= 0 ;\n",
            "[5] -1 x2 >= 0 ;\n",
        ));
        let mut view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        let expired = Instant::now()
            .checked_sub(Duration::from_millis(1))
            .expect("the monotonic clock has advanced by at least one millisecond");
        let outcome = run_wcsp_transfer(&mut view, Some(expired), None).expect("transfer must run");
        // No work done: c0 = 0 (still a sound floor), empty trail, no fixpoint claim.
        assert_eq!(outcome.c0, 0);
        assert!(outcome.trail.is_empty());
        assert!(!outcome.fixpoint);
    }

    #[test]
    fn transfer_stops_immediately_on_term_flag() {
        let instance = wbo(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[3] -1 x1 >= 0 ;\n",
        ));
        let mut view = reconstruct_wcsp_view(&instance).expect("must reconstruct");
        let flag = AtomicBool::new(true);
        let outcome = run_wcsp_transfer(&mut view, None, Some(&flag)).expect("transfer must run");
        assert_eq!(outcome.c0, 0);
        assert!(outcome.trail.is_empty());
        assert!(!outcome.fixpoint);
    }

    #[test]
    fn transfer_fails_closed_on_c0_overflow() {
        // Hand-built view violating no invariant except that draining the
        // unary minimum into c0 would overflow i128.
        let mut view = WcspView {
            domains: vec![vec![1, 2]],
            unary: vec![vec![i128::MAX, i128::MAX]],
            binary: BTreeMap::new(),
            c0: 1,
        };
        assert_eq!(run_wcsp_transfer(&mut view, None, None), None);
    }

    #[test]
    fn transfer_fails_closed_on_negative_cost_invariant_breach() {
        // A negative cost can only mean reconstruction/engine corruption;
        // the engine must refuse to derive anything from it.
        let mut view = WcspView {
            domains: vec![vec![1, 2]],
            unary: vec![vec![-1, 5]],
            binary: BTreeMap::new(),
            c0: 0,
        };
        assert_eq!(run_wcsp_transfer(&mut view, None, None), None);
    }

    // ------------------------------------------------------------------
    // Trail checker: accept and reject cases
    // ------------------------------------------------------------------

    fn uniform_binary_instance() -> WboInstance {
        wbo(concat!(
            "soft: 5 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "+1 x3 +1 x4 = 1 ;\n",
            "[5] -1 x1 -1 x3 >= -1 ;\n",
            "[5] -1 x1 -1 x4 >= -1 ;\n",
            "[5] -1 x2 -1 x3 >= -1 ;\n",
            "[5] -1 x2 -1 x4 >= -1 ;\n",
        ))
    }

    fn engine_outcome(instance: &WboInstance) -> WcspTransferOutcome {
        let mut view = reconstruct_wcsp_view(instance).expect("must reconstruct");
        run_wcsp_transfer(&mut view, None, None).expect("transfer must run")
    }

    #[test]
    fn checker_accepts_engine_trails() {
        for instance in [
            uniform_binary_instance(),
            load_fixture("wcsp_warehouse0.wbo"),
        ] {
            let outcome = engine_outcome(&instance);
            assert!(check_wcsp_transfer_trail(
                &instance,
                &outcome.trail,
                outcome.c0
            ));
        }
    }

    #[test]
    fn checker_rejects_overclaimed_c0() {
        let instance = uniform_binary_instance();
        let outcome = engine_outcome(&instance);
        assert!(!check_wcsp_transfer_trail(
            &instance,
            &outcome.trail,
            outcome.c0 + 1
        ));
        assert!(!check_wcsp_transfer_trail(
            &instance,
            &outcome.trail,
            outcome.c0 - 1
        ));
    }

    #[test]
    fn checker_rejects_tampered_delta() {
        let instance = uniform_binary_instance();
        let outcome = engine_outcome(&instance);
        let mut tampered = outcome.trail.clone();
        let WcspProjection::BinaryToUnary { delta, .. } = &mut tampered[0] else {
            panic!("first trail step must be a binary projection");
        };
        *delta += 1;
        assert!(!check_wcsp_transfer_trail(&instance, &tampered, outcome.c0));
    }

    #[test]
    fn checker_rejects_reordered_trail() {
        // Draining unary->c0 BEFORE the binary projections claims delta 5
        // where the true minimum is still 0.
        let instance = uniform_binary_instance();
        let outcome = engine_outcome(&instance);
        let mut reordered = outcome.trail.clone();
        reordered.rotate_right(1);
        assert!(!check_wcsp_transfer_trail(
            &instance, &reordered, outcome.c0
        ));
    }

    #[test]
    fn checker_rejects_out_of_range_indices_and_missing_pairs() {
        let instance = uniform_binary_instance();
        assert!(!check_wcsp_transfer_trail(
            &instance,
            &[WcspProjection::UnaryToC0 {
                domain: 7,
                delta: 0
            }],
            0
        ));
        assert!(!check_wcsp_transfer_trail(
            &instance,
            &[WcspProjection::BinaryToUnary {
                d_low: 0,
                d_high: 5,
                to_low: true,
                value: 0,
                delta: 0
            }],
            0
        ));
        // Pair (0, 1) exists but value index 9 does not.
        assert!(!check_wcsp_transfer_trail(
            &instance,
            &[WcspProjection::BinaryToUnary {
                d_low: 0,
                d_high: 1,
                to_low: true,
                value: 9,
                delta: 0
            }],
            0
        ));
    }

    #[test]
    fn checker_rejects_when_reconstruction_declines() {
        // 4queens declines reconstruction => NO trail (even an empty one
        // claiming c0 = 0) is certifiable against it.
        let instance = load_fixture("wcsp_4queens.wbo");
        assert!(!check_wcsp_transfer_trail(&instance, &[], 0));
    }

    #[test]
    fn checker_accepts_empty_trail_with_zero_claim_only() {
        let instance = uniform_binary_instance();
        assert!(check_wcsp_transfer_trail(&instance, &[], 0));
        assert!(!check_wcsp_transfer_trail(&instance, &[], 1));
    }

    // ------------------------------------------------------------------
    // Differential: probe floor vs exhaustive brute-force minimum
    // ------------------------------------------------------------------

    /// Deterministic xorshift64 (seeded per case; no external RNG deps).
    struct XorShift64(u64);

    impl XorShift64 {
        fn new(seed: u64) -> Self {
            // Avoid the all-zero fixed point; splmix-style scramble.
            Self(seed.wrapping_mul(0x9E37_79B9_7F4A_7C15) | 1)
        }

        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }

        fn below(&mut self, n: u64) -> u64 {
            self.next() % n
        }
    }

    /// Builds a random tiny WCSP-shaped WBO instance (<= 3 domains x <= 3
    /// values) in WBO surface syntax, exercising the real parser path.
    fn random_tiny_wcsp(rng: &mut XorShift64) -> WboInstance {
        let num_domains = 1 + rng.below(3) as usize;
        let sizes: Vec<usize> = (0..num_domains)
            .map(|_| 1 + rng.below(3) as usize)
            .collect();
        let mut first_var: Vec<u32> = Vec::with_capacity(num_domains);
        let mut next_var = 1_u32;
        let mut text = String::from("soft: 1000000 ;\n");
        for &size in &sizes {
            first_var.push(next_var);
            let row: Vec<String> = (0..size)
                .map(|v| format!("+1 x{}", next_var + v as u32))
                .collect();
            text.push_str(&format!("{} = 1 ;\n", row.join(" ")));
            next_var += size as u32;
        }
        for (d, &size) in sizes.iter().enumerate() {
            for v in 0..size {
                if rng.below(2) == 0 {
                    let weight = rng.below(7);
                    text.push_str(&format!(
                        "[{weight}] -1 x{} >= 0 ;\n",
                        first_var[d] + v as u32
                    ));
                }
            }
        }
        for d1 in 0..num_domains {
            for d2 in (d1 + 1)..num_domains {
                if rng.below(2) == 1 {
                    continue; // no cost function between this pair
                }
                for a in 0..sizes[d1] {
                    for b in 0..sizes[d2] {
                        if rng.below(2) == 0 {
                            continue;
                        }
                        let weight = rng.below(7);
                        let (xa, xb) = (first_var[d1] + a as u32, first_var[d2] + b as u32);
                        text.push_str(&format!("[{weight}] -1 x{xa} -1 x{xb} >= -1 ;\n"));
                        if rng.below(8) == 0 {
                            // Occasional duplicate soft on the same cell
                            // (accumulation path).
                            text.push_str(&format!(
                                "[{}] -1 x{xb} -1 x{xa} >= -1 ;\n",
                                rng.below(3)
                            ));
                        }
                    }
                }
            }
        }
        wbo(&text)
    }

    /// Exhaustive minimum total soft cost over all assignments satisfying the
    /// one-hot rows, evaluated against the ORIGINAL soft constraints via the
    /// crate's constraint evaluator (an oracle independent of the WCSP view).
    fn brute_force_min_cost(instance: &WboInstance, sizes: &[usize]) -> i128 {
        let num_vars = instance.num_vars as usize;
        let mut choice = vec![0_usize; sizes.len()];
        let mut best = i128::MAX;
        loop {
            let mut assignment = vec![false; num_vars];
            let mut var = 0_usize;
            for (d, &size) in sizes.iter().enumerate() {
                assignment[var + choice[d]] = true;
                var += size;
            }
            let mut cost = 0_i128;
            for (weight, soft) in &instance.soft_constraints {
                if !crate::solver::eval_constraint(soft, &assignment) {
                    cost += *weight;
                }
            }
            best = best.min(cost);
            // Next tuple (odometer).
            let mut d = 0;
            loop {
                if d == sizes.len() {
                    return best;
                }
                choice[d] += 1;
                if choice[d] < sizes[d] {
                    break;
                }
                choice[d] = 0;
                d += 1;
            }
        }
    }

    #[test]
    fn differential_probe_floor_never_exceeds_brute_force_minimum_5000_cases() {
        let mut nonzero_floors = 0_u32;
        let mut exact_floors = 0_u32;
        for seed in 0..5000_u64 {
            let mut rng = XorShift64::new(seed);
            let instance = random_tiny_wcsp(&mut rng);
            let sizes: Vec<usize> = {
                let view = reconstruct_wcsp_view(&instance)
                    .unwrap_or_else(|| panic!("seed {seed}: generated instance must reconstruct"));
                view.domains.iter().map(Vec::len).collect()
            };
            let mut view = reconstruct_wcsp_view(&instance).expect("second reconstruction");
            let outcome = run_wcsp_transfer(&mut view, None, None)
                .unwrap_or_else(|| panic!("seed {seed}: transfer must run"));
            assert!(
                outcome.fixpoint,
                "seed {seed}: unbudgeted transfer must reach fixpoint"
            );
            assert!(
                check_wcsp_transfer_trail(&instance, &outcome.trail, outcome.c0),
                "seed {seed}: independent trail check must pass"
            );
            assert!(outcome.c0 >= 0, "seed {seed}: floor must be non-negative");
            let brute = brute_force_min_cost(&instance, &sizes);
            assert!(
                brute >= outcome.c0,
                "seed {seed}: UNSOUND floor — brute-force minimum {brute} < probe c0 {}",
                outcome.c0
            );
            if outcome.c0 > 0 {
                nonzero_floors += 1;
            }
            if outcome.c0 == brute {
                exact_floors += 1;
            }
        }
        // Anti-vacuity: the generator must exercise nontrivial floors, and
        // projection-only soft AC is exact on a healthy share of tiny cases.
        assert!(
            nonzero_floors >= 500,
            "generator degenerated: only {nonzero_floors}/5000 cases had a nonzero floor"
        );
        assert!(
            exact_floors >= 500,
            "generator degenerated: only {exact_floors}/5000 floors were tight"
        );
    }

    #[test]
    fn declines_unary_cost_overflow() {
        let mut instance = wbo(concat!(
            "soft: 9 ;\n",
            "+1 x1 +1 x2 = 1 ;\n",
            "[1] -1 x1 >= 0 ;\n",
        ));
        instance
            .soft_constraints
            .push((i128::MAX, instance.soft_constraints[0].1.clone()));
        assert_eq!(reconstruct_wcsp_view(&instance), None);
    }
}
