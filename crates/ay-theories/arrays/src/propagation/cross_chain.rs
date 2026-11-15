// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Cross-chain resolution through asserted array equalities.
//!
//! The emitter relates reads at each selected index through both actual store
//! resolutions. A chain's terminal cannot be approximated independently of the
//! index or substituted for the exact alias proof used by the emitter.
//!
//! Compute productive indices once per distinct array, using the same resolver
//! and alias predicate as emission. Value resolutions can participate directly;
//! Base resolutions need an actual read of a provably equal array at that index;
//! Unresolved resolutions emit nothing. A pair can emit only in the intersection
//! of its sides' productive indices. The original emitter still checks every
//! selected pair in its original order and carries all original proof reasons.
//! Its standing debug oracle compares the complete ordered output against the
//! unfiltered loop.

use super::*;

#[path = "cross_chain_index_bits.rs"]
mod index_bits;
use index_bits::IndexBits;

#[cfg(test)]
#[path = "cross_chain_tests.rs"]
mod tests;

/// Inputs frozen for the complete propagation window.
pub(super) struct CrossChainInput<'a> {
    pub(super) select_indices: &'a [TermId],
    pub(super) index_to_selects: &'a HashMap<TermId, Vec<(TermId, TermId)>>,
    pub(super) eq_pairs: &'a [(TermId, TermId)],
}

/// Array pairs in input order -> productive index intersection.
pub(super) struct CrossChainCandidates {
    per_pair: Vec<Option<IndexBits>>,
}

impl ArraySolver<'_> {
    /// Exact necessary conditions for the emitter's four productive arms.
    /// Per-array resolutions and per-(base,index) read existence are shared
    /// across all partners inside this immutable equality/assignment window.
    pub(super) fn cross_chain_candidates(
        &self,
        input: &CrossChainInput<'_>,
    ) -> Option<CrossChainCandidates> {
        let mut per_array: HashMap<TermId, Rc<IndexBits>> = HashMap::default();
        let mut base_reads: HashMap<(TermId, TermId), bool> = HashMap::default();
        let mut productive_of = |array: TermId| -> Option<Rc<IndexBits>> {
            if let Some(hit) = per_array.get(&array) {
                return Some(Rc::clone(hit));
            }
            let mut bits = IndexBits::empty(input.select_indices.len());
            for (pos, &index) in input.select_indices.iter().enumerate() {
                if pos.is_multiple_of(32) && self.interrupted_or_deadline() {
                    return None;
                }
                let (resolution, _) =
                    self.resolve_select_base_for_propagation_with_reasons(array, index);
                let productive = match resolution {
                    SelectResolution::Value(_) => true,
                    SelectResolution::Base(base) => {
                        if let Some(&found) = base_reads.get(&(base, index)) {
                            found
                        } else {
                            let mut found = false;
                            if let Some(selects) = input.index_to_selects.get(&index) {
                                for (position, &(_, selected)) in selects.iter().enumerate() {
                                    if position.is_multiple_of(32) && self.interrupted_or_deadline()
                                    {
                                        return None;
                                    }
                                    if selected == base
                                        || self.explain_equal_if_provable(selected, base).is_some()
                                    {
                                        found = true;
                                        break;
                                    }
                                }
                            }
                            // An interrupted proof lookup must not cache a
                            // partial negative result for a large index cohort.
                            if self.interrupted_or_deadline() {
                                return None;
                            }
                            base_reads.insert((base, index), found);
                            found
                        }
                    }
                    SelectResolution::Unresolved => false,
                };
                if productive {
                    bits.set(pos);
                }
            }
            let bits = Rc::new(bits);
            per_array.insert(array, Rc::clone(&bits));
            Some(bits)
        };

        let mut per_pair = Vec::new();
        let _ = per_pair.try_reserve_exact(input.eq_pairs.len());
        for &(lhs, rhs) in input.eq_pairs {
            if self.interrupted_or_deadline() {
                return None;
            }
            let left = productive_of(lhs)?;
            let right = productive_of(rhs)?;
            let bits = left.and(&right);
            per_pair.push(if bits.any() { Some(bits) } else { None });
        }
        if self.interrupted_or_deadline() {
            return None;
        }
        Some(CrossChainCandidates { per_pair })
    }

    /// The cross-chain loop body, unchanged from the pre-filter code except
    /// that `candidates` (when given) skips `(pair, idx)` combinations that
    /// cannot emit. Returns `true` when the interrupt flag stopped the loop.
    pub(super) fn cross_chain_emit(
        &self,
        input: &CrossChainInput<'_>,
        candidates: Option<&CrossChainCandidates>,
        seen_equalities: &mut HashSet<(TermId, TermId)>,
        result: &mut EqualityPropagationResult,
    ) -> bool {
        let proven_equal_reasons =
            |lhs: TermId, rhs: TermId| self.explain_equal_if_provable(lhs, rhs);
        macro_rules! push_equality {
            ($lhs:expr, $rhs:expr, $reason:expr $(,)?) => {
                if !self.equality_already_known_or_assigned_true($lhs, $rhs) {
                    let _ = Self::push_discovered_equality(
                        seen_equalities,
                        result,
                        $lhs,
                        $rhs,
                        $reason,
                    );
                } else {
                    prop_eq_stats::add(&prop_eq_stats::suppressed_known, 1);
                }
            };
        }
        for (pair_pos, &(lhs, rhs)) in input.eq_pairs.iter().enumerate() {
            // #8615: Check interrupt in cross-chain resolution O(n^2) loop.
            if self.is_interrupted() {
                return true;
            }
            let pair_bits = match candidates {
                Some(c) => match &c.per_pair[pair_pos] {
                    Some(bits) => Some(bits),
                    None => continue,
                },
                None => None,
            };
            let Some(array_eq_reasons) = proven_equal_reasons(lhs, rhs) else {
                continue;
            };
            for (idx_pos, &idx) in input.select_indices.iter().enumerate() {
                if let Some(bits) = pair_bits {
                    if !bits.get(idx_pos) {
                        continue;
                    }
                }
                prop_eq_stats::add(&prop_eq_stats::cross_chain_visits, 1);
                let (lhs_res, lhs_res_reasons) =
                    self.resolve_select_base_for_propagation_with_reasons(lhs, idx);
                let (rhs_res, rhs_res_reasons) =
                    self.resolve_select_base_for_propagation_with_reasons(rhs, idx);

                let selects_at_idx = input
                    .index_to_selects
                    .get(&idx)
                    .cloned()
                    .unwrap_or_default();

                match (lhs_res, rhs_res) {
                    (SelectResolution::Base(base_l), SelectResolution::Base(base_r)) => {
                        if base_l == base_r {
                            continue;
                        }
                        let lhs_sels: Vec<(TermId, Vec<TheoryLit>)> = selects_at_idx
                            .iter()
                            .filter_map(|&(sel, arr)| {
                                if arr == base_l {
                                    Some((sel, Vec::new()))
                                } else {
                                    proven_equal_reasons(arr, base_l).map(|reasons| (sel, reasons))
                                }
                            })
                            .collect();
                        let rhs_sels: Vec<(TermId, Vec<TheoryLit>)> = selects_at_idx
                            .iter()
                            .filter_map(|&(sel, arr)| {
                                if arr == base_r {
                                    Some((sel, Vec::new()))
                                } else {
                                    proven_equal_reasons(arr, base_r).map(|reasons| (sel, reasons))
                                }
                            })
                            .collect();
                        for (sel_l, sel_l_reasons) in &lhs_sels {
                            for (sel_r, sel_r_reasons) in &rhs_sels {
                                if Self::equality_already_discovered(
                                    seen_equalities,
                                    *sel_l,
                                    *sel_r,
                                ) {
                                    continue;
                                }
                                let mut reasons = array_eq_reasons.clone();
                                reasons.extend(lhs_res_reasons.clone());
                                reasons.extend(rhs_res_reasons.clone());
                                reasons.extend(sel_l_reasons.clone());
                                reasons.extend(sel_r_reasons.clone());
                                push_equality!(*sel_l, *sel_r, reasons);
                            }
                        }
                    }
                    (SelectResolution::Value(val_l), SelectResolution::Base(base_r)) => {
                        for &(sel, arr) in &selects_at_idx {
                            if Self::equality_already_discovered(seen_equalities, sel, val_l) {
                                continue;
                            }
                            let Some(mut reasons) = (if arr == base_r {
                                Some(Vec::new())
                            } else {
                                proven_equal_reasons(arr, base_r)
                            }) else {
                                continue;
                            };
                            reasons.extend(array_eq_reasons.clone());
                            reasons.extend(lhs_res_reasons.clone());
                            reasons.extend(rhs_res_reasons.clone());
                            push_equality!(sel, val_l, reasons);
                        }
                    }
                    (SelectResolution::Base(base_l), SelectResolution::Value(val_r)) => {
                        for &(sel, arr) in &selects_at_idx {
                            if Self::equality_already_discovered(seen_equalities, sel, val_r) {
                                continue;
                            }
                            let Some(mut reasons) = (if arr == base_l {
                                Some(Vec::new())
                            } else {
                                proven_equal_reasons(arr, base_l)
                            }) else {
                                continue;
                            };
                            reasons.extend(array_eq_reasons.clone());
                            reasons.extend(lhs_res_reasons.clone());
                            reasons.extend(rhs_res_reasons.clone());
                            push_equality!(sel, val_r, reasons);
                        }
                    }
                    (SelectResolution::Value(val_l), SelectResolution::Value(val_r)) => {
                        if Self::equality_already_discovered(seen_equalities, val_l, val_r) {
                            continue;
                        }
                        let mut reasons = array_eq_reasons.clone();
                        reasons.extend(lhs_res_reasons.clone());
                        reasons.extend(rhs_res_reasons.clone());
                        push_equality!(val_l, val_r, reasons);
                    }
                    _ => {}
                }
            }
        }
        false
    }

    /// Standing debug oracle: the filtered emission must equal the
    /// unfiltered one — same pairs, same reasons, same order — starting from
    /// the same `seen_equalities` / `result` state. Runs the unfiltered loop
    /// on scratch copies.
    #[cfg(debug_assertions)]
    pub(super) fn debug_cross_chain_matches_unfiltered(
        &self,
        input: &CrossChainInput<'_>,
        seen_before: &HashSet<(TermId, TermId)>,
        result_before_len: usize,
        result_after: &EqualityPropagationResult,
    ) -> bool {
        if self.is_interrupted() {
            // An interrupted filtered run may have stopped early; the
            // comparison is only meaningful for complete runs.
            return true;
        }
        // `result_before_len` is the result length the caller read before the
        // filtered run, which only appends; a prefix that is not there means
        // the oracle's own precondition failed, which is a divergence.
        let Some(prefix) = result_after.equalities.get(..result_before_len) else {
            return false;
        };
        let mut seen = seen_before.clone();
        let mut reference = EqualityPropagationResult::default();
        reference.equalities.extend(prefix.iter().cloned());
        let interrupted = self.cross_chain_emit(input, None, &mut seen, &mut reference);
        if interrupted {
            return true;
        }
        let Some(filtered) = result_after.equalities.get(result_before_len..) else {
            return false;
        };
        let Some(unfiltered) = reference.equalities.get(result_before_len..) else {
            return false;
        };
        let same = filtered.len() == unfiltered.len()
            && filtered
                .iter()
                .zip(unfiltered)
                .all(|(a, b)| a.lhs == b.lhs && a.rhs == b.rhs && a.reason == b.reason);
        if !same {
            tracing::error!(
                target: "ay::arrays",
                filtered = filtered.len(),
                unfiltered = unfiltered.len(),
                "arrays cross-chain candidate filter diverged from the unfiltered loop"
            );
        }
        same
    }
}
