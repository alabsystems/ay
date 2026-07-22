// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! XOR gate detection for BVE and congruence.
//!
//! XOR gate y = x1 ⊕ x2 ⊕ ... ⊕ xk (up to arity 5) is encoded as 2^k
//! clauses with all even-parity sign patterns.

use super::{bit_parity, sorted_lit_pair, Gate, GateExtractor, GateType};
use crate::clause_arena::ClauseArena;
use crate::literal::{Literal, Variable};

/// Maximum XOR arity for gate detection. CaDiCaL default: `elimxorlim=5`.
/// A k-arity XOR requires finding `2^k` clauses, so cost is exponential in arity.
const XOR_ARITY_LIMIT: usize = 5;

/// Rounds of k-core candidate-count refinement in the clause-driven XOR pass.
/// Kissat `congruencexorcounts` default (options.h:32).
const XOR_COUNT_ROUNDS: usize = 2;

/// Outcome counters for the clause-driven XOR pass (congruence extraction).
#[derive(Debug, Default, Clone, Copy)]
pub(crate) struct XorPassStats {
    /// Complete XOR clause groups found (one group = 2^arity clauses).
    pub groups: usize,
    /// Gates emitted (up to arity+1 per group — one per group literal as LHS).
    pub lhs_gates: usize,
    /// True when the effort or wall-clock budget stopped the pass early.
    pub truncated: bool,
}

impl GateExtractor {
    /// Clause-driven XOR group extraction for congruence closure.
    ///
    /// Port of Kissat's XOR machinery (congruence.c:2679-3242), replacing the
    /// per-pivot XOR search on the congruence path. Differences from the
    /// per-pivot path that make this both cheaper and higher-recall:
    ///
    /// 1. **Candidate harvest + k-core counting** (Kissat
    ///    `init_xor_gate_extraction`): every irredundant clause of size
    ///    3..=`XOR_ARITY_LIMIT`+1 is a candidate; `largecount[lit]` counts
    ///    candidate occurrences; `XOR_COUNT_ROUNDS` rounds drop candidates
    ///    whose literals cannot possibly belong to a complete group
    ///    (`largecount < 2^(arity-1)`), rebuilding counts over survivors.
    /// 2. **Canonical base selection** (congruence.c:2857-2876): a group is
    ///    attempted from exactly one member — the clause with at most one
    ///    negated literal where that literal has the largest index — so no
    ///    group is searched twice and no marks churn is wasted.
    /// 3. **Least-count sibling lookup** (congruence.c:2744-2820): each of
    ///    the 2^arity - 1 sibling sign patterns is looked up by scanning the
    ///    occurrence list of the pattern's least-frequent literal, not the
    ///    pivot's full occurrence list.
    /// 4. **Per-LHS emission** (congruence.c:2929-2947): a matched group over
    ///    k+1 variables emits one gate per (non-frozen) group variable as
    ///    output. This is what lets the closure merge across groups: gates
    ///    `b = a XOR c` and `e = a XOR c` collide on signature (inputs) and
    ///    merge b with e — structurally impossible for one-gate-per-pivot
    ///    extraction. XNOR is folded into `negated_output` exactly as in the
    ///    per-pivot path: a group with parity target 1 (all-positive base)
    ///    yields `negated_output = true` outputs.
    ///
    /// Soundness: a gate is emitted only when ALL 2^arity defining clauses
    /// are present in the arena, so the gate constraint is entailed by the
    /// formula; downstream, congruence equivalence edges remain RUP-gated in
    /// proof mode and unit applications remain live-BCP-probed (#7137).
    ///
    /// Effort/wall budgets are shared with the caller: `effort_spent` is
    /// advanced by clauses scanned; the pass stops (setting
    /// `stats.truncated`) when either budget is exhausted, leaving the
    /// remaining budget to the per-pivot AND/ITE loop.
    #[allow(clippy::too_many_arguments)]
    pub(crate) fn extract_xor_groups_clause_driven(
        &mut self,
        clauses: &ClauseArena,
        num_vars: usize,
        frozen: &[bool],
        effort_spent: &mut u64,
        effort_budget: u64,
        extract_start: ay_core::time::Instant,
        time_budget_ms: u128,
        gates: &mut Vec<Gate>,
    ) -> XorPassStats {
        let mut stats = XorPassStats::default();
        let num_lits = num_vars * 2;

        // Step 1: harvest candidates + per-literal candidate counts.
        let mut largecount: Vec<u32> = vec![0; num_lits];
        let mut candidates: Vec<usize> = Vec::new();
        'harvest: for idx in clauses.indices() {
            if clauses.is_empty_clause(idx) || clauses.is_learned(idx) {
                continue;
            }
            let lits = clauses.literals(idx);
            let size = lits.len();
            if !(3..=XOR_ARITY_LIMIT + 1).contains(&size) {
                continue;
            }
            *effort_spent += 1;
            // Defensive: XOR groups need distinct variables inside num_vars.
            for (i, a) in lits.iter().enumerate() {
                if a.variable().0 as usize >= num_vars {
                    continue 'harvest;
                }
                for b in lits.iter().skip(i + 1) {
                    if a.variable() == b.variable() {
                        continue 'harvest;
                    }
                }
            }
            for &lit in lits {
                largecount[lit.index()] += 1;
            }
            candidates.push(idx);
        }

        // Step 2: k-core refinement — a literal occurring fewer than
        // 2^(arity-1) times among candidates cannot be in a complete group.
        for _round in 0..XOR_COUNT_ROUNDS {
            let mut survivors: Vec<usize> = Vec::with_capacity(candidates.len());
            let mut removed_any = false;
            for &idx in &candidates {
                let lits = clauses.literals(idx);
                let needed = 1u32 << (lits.len() - 2);
                if lits.iter().all(|l| largecount[l.index()] >= needed) {
                    survivors.push(idx);
                } else {
                    removed_any = true;
                }
            }
            if !removed_any {
                break;
            }
            for c in largecount.iter_mut() {
                *c = 0;
            }
            for &idx in &survivors {
                for &lit in clauses.literals(idx) {
                    largecount[lit.index()] += 1;
                }
            }
            candidates = survivors;
        }

        // Step 3: candidate-only occurrence lists (far smaller than full occs).
        let mut cand_occs: Vec<Vec<usize>> = vec![Vec::new(); num_lits];
        for &idx in &candidates {
            for &lit in clauses.literals(idx) {
                cand_occs[lit.index()].push(idx);
            }
        }

        // Step 4: canonical-base iteration + sibling matching + emission.
        let mut sibling: Vec<Literal> = Vec::new();
        let mut group_clauses: Vec<usize> = Vec::new();
        for (ci, &base_idx) in candidates.iter().enumerate() {
            if *effort_spent >= effort_budget {
                stats.truncated = true;
                break;
            }
            if ci & 0xFF == 0 && extract_start.elapsed().as_millis() >= time_budget_ms {
                stats.truncated = true;
                break;
            }
            let base = clauses.literals(base_idx);
            let size = base.len();
            let arity = size - 1;

            // Canonical base: at most one negated literal, and if present it
            // must have the largest literal index in the clause.
            let mut negated_count = 0usize;
            let mut negated_lit: Option<Literal> = None;
            let mut max_index = 0usize;
            for &l in base {
                max_index = max_index.max(l.variable().0 as usize);
                if !l.is_positive() {
                    negated_count += 1;
                    negated_lit = Some(l);
                }
            }
            if negated_count > 1 {
                continue;
            }
            if let Some(nl) = negated_lit {
                if (nl.variable().0 as usize) != max_index {
                    continue;
                }
            }

            // Cheap reject: both polarities of every literal must occur at
            // least 2^(arity-1) times among surviving candidates.
            let needed = 1u32 << (arity - 1);
            if base
                .iter()
                .any(|l| largecount[l.index()] < needed || largecount[l.negated().index()] < needed)
            {
                continue;
            }

            // Enumerate the 2^(size-1) - 1 sibling sign patterns with the
            // same negation parity as the base.
            let base_mask: u32 = base
                .iter()
                .enumerate()
                .map(|(i, l)| if l.is_positive() { 0 } else { 1u32 << i })
                .sum();
            let parity = base_mask.count_ones() & 1;
            group_clauses.clear();
            group_clauses.push(base_idx);
            let mut complete = true;
            for mask in 0..(1u32 << size) {
                if mask == base_mask || (mask.count_ones() & 1) != parity {
                    continue;
                }
                sibling.clear();
                for (i, l) in base.iter().enumerate() {
                    let pos = Literal::positive(l.variable());
                    sibling.push(if mask & (1 << i) != 0 {
                        pos.negated()
                    } else {
                        pos
                    });
                }
                match self.find_xor_side_clause(
                    &sibling,
                    clauses,
                    &cand_occs,
                    &largecount,
                    effort_spent,
                ) {
                    Some(cidx) => group_clauses.push(cidx),
                    None => {
                        complete = false;
                        break;
                    }
                }
            }
            if !complete {
                continue;
            }
            debug_assert_eq!(group_clauses.len(), 1usize << arity);
            stats.groups += 1;

            // Negation parity p of every group clause satisfies
            // p ≡ 1 - t (mod 2) where t is the XOR constraint target
            // (⊕ vars = t). All-positive base (p=0) ⇒ t=1 ⇒ each output is
            // the XNOR of the remaining variables (negated_output = true),
            // matching the per-pivot convention (neg_inputs even ⇒ XNOR).
            let negated_output = parity == 0;
            for (i, l) in base.iter().enumerate() {
                let out_var = l.variable();
                let ovi = out_var.0 as usize;
                if ovi < frozen.len() && frozen[ovi] {
                    continue;
                }
                let inputs: Vec<Literal> = base
                    .iter()
                    .enumerate()
                    .filter(|(j, _)| *j != i)
                    .map(|(_, x)| Literal::positive(x.variable()))
                    .collect();
                gates.push(Gate {
                    output: out_var,
                    gate_type: GateType::Xor,
                    inputs,
                    defining_clauses: group_clauses.clone(),
                    negated_output,
                });
                stats.lhs_gates += 1;
                self.stats.xor_gates += 1;
            }
        }

        stats
    }

    /// Find a candidate clause exactly matching `target` by scanning the
    /// occurrence list of the least-frequent target literal
    /// (Kissat `find_large_xor_side_clause`, congruence.c:2744-2820).
    fn find_xor_side_clause(
        &self,
        target: &[Literal],
        clauses: &ClauseArena,
        cand_occs: &[Vec<usize>],
        largecount: &[u32],
        effort_spent: &mut u64,
    ) -> Option<usize> {
        let min_lit = target
            .iter()
            .min_by_key(|l| largecount[l.index()])
            .expect("XOR sibling pattern must be non-empty");
        for &ci in &cand_occs[min_lit.index()] {
            *effort_spent += 1;
            if ci >= clauses.len() || clauses.is_empty_clause(ci) {
                continue;
            }
            let c = clauses.literals(ci);
            if c.len() != target.len() {
                continue;
            }
            if target.iter().all(|w| c.contains(w)) {
                return Some(ci);
            }
        }
        None
    }

    pub(super) fn find_xor_gate_db(
        &self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
    ) -> Option<Gate> {
        let pivot_pos = Literal::positive(pivot);
        let pivot_neg = Literal::negative(pivot);

        for &clause_idx in pos_occs {
            if clause_idx >= clauses.len() || clauses.is_empty_clause(clause_idx) {
                continue;
            }
            let clause = clauses.literals(clause_idx);
            let Some((a, b)) = Self::get_ternary_others(clause, pivot_pos) else {
                continue;
            };

            let needed_pos = sorted_lit_pair(a.negated(), b.negated());
            let needed_neg1 = sorted_lit_pair(a.negated(), b);
            let needed_neg2 = sorted_lit_pair(a, b.negated());

            let mut pos_idx2 = None;
            for &ci in pos_occs {
                if ci == clause_idx || ci >= clauses.len() || clauses.is_empty_clause(ci) {
                    continue;
                }
                let c = clauses.literals(ci);
                if let Some((x, y)) = Self::get_ternary_others(c, pivot_pos) {
                    if sorted_lit_pair(x, y) == needed_pos {
                        pos_idx2 = Some(ci);
                        break;
                    }
                }
            }

            if pos_idx2.is_none() {
                continue;
            }

            let mut neg_idx1 = None;
            let mut neg_idx2 = None;
            for &ci in neg_occs {
                if ci >= clauses.len() || clauses.is_empty_clause(ci) {
                    continue;
                }
                let c = clauses.literals(ci);
                if let Some((x, y)) = Self::get_ternary_others(c, pivot_neg) {
                    let candidate = sorted_lit_pair(x, y);
                    if candidate == needed_neg1 {
                        neg_idx1 = Some(ci);
                    } else if candidate == needed_neg2 {
                        neg_idx2 = Some(ci);
                    }
                }
            }

            if let (Some(neg1), Some(neg2)) = (neg_idx1, neg_idx2) {
                if let Some(pos2) = pos_idx2 {
                    debug_assert!(
                        {
                            let mut ids = [clause_idx, pos2, neg1, neg2];
                            ids.sort_unstable();
                            ids.windows(2).all(|w| w[0] != w[1])
                        },
                        "BUG: XOR arity-2 witness clauses must be distinct"
                    );
                    debug_assert_ne!(
                        a.variable(),
                        b.variable(),
                        "BUG: XOR-2 inputs share variable"
                    );
                    // CaDiCaL-style RHS normalization: all XOR inputs stored
                    // as positive literals. Parity of negated input literals
                    // in the seed clause determines XOR vs XNOR.
                    // CaDiCaL: `if (!negated) lhs = -lhs` — even parity of
                    // negated inputs means XNOR (#6997, #7137).
                    let neg_inputs = u32::from(!a.is_positive()) + u32::from(!b.is_positive());
                    return Some(Gate {
                        output: pivot,
                        gate_type: GateType::Xor,
                        inputs: vec![
                            Literal::positive(a.variable()),
                            Literal::positive(b.variable()),
                        ],
                        defining_clauses: vec![clause_idx, pos2, neg1, neg2],
                        negated_output: neg_inputs % 2 == 0,
                    });
                }
            }
        }

        // Arity-2 fast path didn't find a gate. Try higher arities (3..=XOR_ARITY_LIMIT)
        // using CaDiCaL's generalized even-parity sign enumeration.
        self.find_xor_gate_higher_arity(pivot, clauses, pos_occs, neg_occs)
    }

    /// Higher-arity XOR gate detection (arity 3..=XOR_ARITY_LIMIT).
    ///
    /// Uses CaDiCaL's even-parity sign enumeration algorithm from `gates.cpp:632-711`.
    /// Only called as fallback when the arity-2 fast path doesn't find a gate.
    fn find_xor_gate_higher_arity(
        &self,
        pivot: Variable,
        clauses: &ClauseArena,
        pos_occs: &[usize],
        neg_occs: &[usize],
    ) -> Option<Gate> {
        let pivot_pos = Literal::positive(pivot);

        for &clause_idx in pos_occs {
            if clause_idx >= clauses.len() || clauses.is_empty_clause(clause_idx) {
                continue;
            }
            let clause = clauses.literals(clause_idx);
            let size = clause.len();
            // Arity 2 (size 3) is handled by the fast path above. Start at arity 3.
            if size < 4 {
                continue;
            }
            let arity = size - 1;
            if arity > XOR_ARITY_LIMIT {
                continue;
            }

            // Build working literal buffer: lits[0] = pivot_pos, rest from clause.
            let mut lits: Vec<Literal> = Vec::with_capacity(size);
            lits.push(pivot_pos);
            for &lit in clause {
                if lit.variable() != pivot {
                    lits.push(lit);
                }
            }
            if lits.len() != size {
                continue;
            }

            // Enumerate the remaining 2^arity - 1 even-parity sign patterns.
            // CaDiCaL reference: gates.cpp:663-680.
            let needed_total = (1u32 << arity) - 1;
            let mut remaining = needed_total;
            let mut signs: u32 = 0;
            let mut gate_clauses: Vec<usize> = Vec::with_capacity(1 << arity);
            let mut found_all = true;

            while remaining > 0 {
                let prev = signs;
                signs += 1;
                // Skip odd-parity patterns.
                while bit_parity(signs) {
                    signs += 1;
                }

                // Flip literals whose sign bit changed.
                for (j, lit) in lits.iter_mut().enumerate() {
                    let bit = 1u32 << j;
                    if (prev & bit) != (signs & bit) {
                        *lit = lit.negated();
                    }
                }

                // Search the appropriate occurrence list based on pivot polarity.
                let search_occs = if lits[0] == pivot_pos {
                    pos_occs
                } else {
                    neg_occs
                };

                if let Some(idx) = self.find_clause_by_lits(&lits, clauses, search_occs) {
                    gate_clauses.push(idx);
                } else {
                    found_all = false;
                    break;
                }

                remaining -= 1;
            }

            if !found_all {
                continue;
            }

            // Add seed clause.
            gate_clauses.push(clause_idx);
            debug_assert_eq!(gate_clauses.len(), 1 << arity);

            let raw_inputs: Vec<Literal> = clause
                .iter()
                .filter(|lit| lit.variable() != pivot)
                .copied()
                .collect();
            debug_assert!(
                !raw_inputs.is_empty(),
                "BUG: XOR gate extraction must produce at least one input literal"
            );
            debug_assert_eq!(
                raw_inputs.len(),
                arity,
                "BUG: XOR gate extraction arity must match input literal count"
            );
            debug_assert!(
                raw_inputs.len() >= 3 && raw_inputs.len() <= XOR_ARITY_LIMIT,
                "BUG: higher-arity XOR inputs.len()={}, expected 3..={XOR_ARITY_LIMIT}",
                raw_inputs.len()
            );

            // CaDiCaL-style RHS normalization: store all inputs as positive.
            // Even negated count = XNOR (#6997, #7137).
            let neg_inputs: u32 = raw_inputs.iter().map(|l| u32::from(!l.is_positive())).sum();
            let inputs: Vec<Literal> = raw_inputs
                .iter()
                .map(|l| Literal::positive(l.variable()))
                .collect();
            return Some(Gate {
                output: pivot,
                gate_type: GateType::Xor,
                inputs,
                defining_clauses: gate_clauses,
                negated_output: neg_inputs.is_multiple_of(2),
            });
        }

        None
    }

    /// Find a clause in `occs` that matches the given literal set exactly.
    /// CaDiCaL reference: `gates.cpp:617-629`.
    fn find_clause_by_lits(
        &self,
        lits: &[Literal],
        clauses: &ClauseArena,
        occs: &[usize],
    ) -> Option<usize> {
        let target_size = lits.len();
        'next_clause: for &ci in occs {
            if ci >= clauses.len() || clauses.is_empty_clause(ci) {
                continue;
            }
            let c = clauses.literals(ci);
            if c.len() != target_size {
                continue;
            }
            for &want in lits {
                if !c.contains(&want) {
                    continue 'next_clause;
                }
            }
            return Some(ci);
        }
        None
    }
}
