// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! BreakID-style symmetry detector: iterative refinement + orbit extraction.
//!
//! Orchestrates the full symmetry-breaking pipeline:
//! 1. Iterative color refinement on the clause-variable incidence graph.
//! 2. Swap verification within refined color classes.
//! 3. Orbit extraction from verified swaps via union-find.
//! 4. Lex-leader SBP clause generation per orbit.
//!
//! This replaces the coarse single-pass color grouping in the original
//! `detect_binary_swaps` with multi-round Weisfeiler-Leman refinement,
//! producing tighter candidate groups and fewer false-positive swap checks.
//!
//! Reference: Devriendt, Bogaerts, Bruynooghe, Denecker. "Improved Static
//! Symmetry Breaking for SAT." (BreakID, SAT 2016).

use std::collections::BTreeMap;

use crate::{Literal, Variable};

use super::orbits;
use super::refinement;
use super::{build_formula_counts, canonical_clause_key, BinarySwap};

/// BreakID-style symmetry detector.
///
/// Orchestrates the full pipeline:
/// 1. Iterative color refinement on the clause-variable incidence graph.
/// 2. Swap verification within refined color classes.
/// 3. Orbit extraction from verified swaps via union-find.
/// 4. Lex-leader SBP clause generation.
pub(crate) struct SymmetryDetector {
    /// Maximum number of swap pairs to verify.
    max_pairs: usize,
    /// Maximum size of a single color class to consider.
    max_group_size: usize,
}

/// Statistics produced by the detector pipeline.
#[derive(Debug, Clone, Default)]
pub(crate) struct DetectorStats {
    /// Number of iterative refinement rounds.
    pub(crate) refinement_rounds: u64,
    /// Number of candidate pairs considered.
    pub(crate) candidate_pairs: u64,
    /// Number of verified swap pairs.
    pub(crate) pairs_detected: u64,
    /// Number of orbits (connected components of swap graph) detected.
    pub(crate) orbits_detected: u64,
    /// Refined colour classes with at least two variables — the raw supply of
    /// symmetry the refinement found, before any budget is applied.
    pub(crate) groups_nontrivial: u64,
    /// Non-trivial classes dropped because they exceed `max_group_size`. A
    /// non-zero count here means detection found symmetry and then threw it
    /// away, which reads identically to "no symmetry" in every other counter.
    pub(crate) groups_over_budget: u64,
    /// Size of the largest non-trivial class.
    pub(crate) largest_group: u64,
}

impl SymmetryDetector {
    /// Create a new detector with the given budget limits.
    pub(crate) fn new(max_pairs: usize, max_group_size: usize) -> Self {
        Self {
            max_pairs,
            max_group_size,
        }
    }

    /// Run the full detection pipeline and return symmetry-breaking clauses.
    ///
    /// Returns `(breaking_clauses, stats)` where each breaking clause
    /// is a `Vec<Literal>`. The caller is responsible for adding these to the
    /// solver's clause database.
    #[cfg(test)]
    pub(crate) fn detect_and_encode(
        &self,
        clauses: &[Vec<Literal>],
    ) -> (Vec<Vec<Literal>>, DetectorStats) {
        self.detect_and_encode_interruptible(clauses, || false)
            .expect("a never-stop symmetry detector cannot be interrupted")
    }

    /// Run the full detection pipeline with cooperative cancellation.
    ///
    /// `should_stop` is polled at phase boundaries and while verifying a
    /// candidate swap against the formula. `None` means detection was
    /// interrupted; no partially derived symmetry-breaking clauses are
    /// returned or installed.
    pub(crate) fn detect_and_encode_interruptible<F>(
        &self,
        clauses: &[Vec<Literal>],
        should_stop: F,
    ) -> Option<(Vec<Vec<Literal>>, DetectorStats)>
    where
        F: Fn() -> bool,
    {
        let mut stats = DetectorStats::default();

        if should_stop() {
            return None;
        }

        // Phase 1: Iterative color refinement.
        let refined = refinement::iterative_color_refinement(clauses);
        stats.refinement_rounds = refined.rounds as u64;

        if should_stop() {
            return None;
        }

        // Phase 2: Within each refined color class, verify swaps.
        let formula_counts = build_formula_counts(clauses);
        let groups = refined.candidate_groups();
        let mut verified_swaps: Vec<BinarySwap> = Vec::new();

        if should_stop() {
            return None;
        }

        for variables in groups.into_values() {
            if variables.len() >= 2 {
                stats.groups_nontrivial += 1;
                stats.largest_group = stats.largest_group.max(variables.len() as u64);
            }
            if variables.len() < 2 || variables.len() > self.max_group_size {
                if variables.len() > self.max_group_size {
                    stats.groups_over_budget += 1;
                }
                continue;
            }
            for i in 0..variables.len() {
                for j in (i + 1)..variables.len() {
                    if verified_swaps.len() >= self.max_pairs {
                        break;
                    }
                    stats.candidate_pairs += 1;
                    let pair = BinarySwap::ordered(variables[i], variables[j]);
                    match swap_preserves_formula_interruptible(&formula_counts, pair, &should_stop)
                    {
                        Some(true) => {
                            stats.pairs_detected += 1;
                            verified_swaps.push(pair);
                        }
                        Some(false) => {}
                        None => return None,
                    }
                }
                if verified_swaps.len() >= self.max_pairs {
                    break;
                }
            }
        }

        if verified_swaps.is_empty() {
            return Some((Vec::new(), stats));
        }

        if should_stop() {
            return None;
        }

        // Phase 3: Extract orbits from verified swaps using union-find.
        let orbit_list = orbits::extract_orbits(&verified_swaps);
        stats.orbits_detected = orbit_list.len() as u64;

        // Phase 4: Generate lex-leader SBP clauses for each orbit.
        let mut all_clauses = Vec::new();
        for orbit in &orbit_list {
            let sbp_clauses = orbits::encode_orbit_lex_leader_sbp(orbit);
            all_clauses.extend(sbp_clauses);
        }

        Some((all_clauses, stats))
    }

    /// Composite-symmetry pipeline (#17): color refinement → gate-verified
    /// composite-involution finding → GROUP-level row-interchangeability
    /// symmetry breaking (BreakID chained lex-leader), with disjoint-support
    /// per-involution SBP as a fallback for the involutions no row-set covers.
    ///
    /// Every returned clause is sound by construction (see the component docs +
    /// soundness proofs):
    ///   * row-set chains keep at least the lex-max (sorted) representative of
    ///     every orbit under the row-permutation group (which the gate-verified
    ///     swaps generate as `S_k`);
    ///   * leftover per-involution binary clauses keep the 2-orbit lex-leader.
    /// All emitted constraints have pairwise-disjoint ORIGINAL-variable support
    /// (disjoint groups compose soundly); the aux variables are fresh.
    ///
    /// `fresh_base` is the first unused variable id; aux equal-prefix variables
    /// are allocated sequentially from there. Returns `(clauses, aux_allocated)`;
    /// the caller MUST `ensure_num_vars(fresh_base + aux_allocated)` before adding
    /// the clauses (they reference variables `>= fresh_base`).
    pub(crate) fn detect_and_encode_composite(
        &self,
        clauses: &[Vec<Literal>],
        fresh_base: u32,
    ) -> (Vec<Vec<Literal>>, u32) {
        let generators = self.find_composite_generators(clauses);

        // Emit a per-generator lex-leader constraint for each gate-verified
        // automorphism, all in the SAME global (ascending variable-id) order.
        //
        // SOUNDNESS (multi-generator lex-leader theorem): let `G` be the group
        // generated by the discovered automorphisms and fix the global variable
        // order. For any model `α`, let `α*` be the lexicographic maximum of the
        // orbit `Gα` (under that order). `α*` is a model (the automorphic image of
        // a model), and for EVERY automorphism `h ∈ G`, `h·α* ∈ Gα` so
        // `h·α* ⪯_lex α*`, i.e. `α*` satisfies `x ⪰_lex h·x`. Hence the
        // conjunction of the per-generator constraints is satisfiability-
        // preserving — adding all of them together is sound, with NO disjoint-
        // support requirement (unlike the per-involution binary SBP). Each `h` is
        // gate-verified, so every emitted constraint is for a genuine
        // automorphism. The equal-prefix aux variables are fresh. ∎
        let mut out: Vec<Vec<Literal>> = Vec::new();
        let mut next = fresh_base;
        for g in &generators {
            let (cls, aux) = encode_perm_lex_leader(g, next);
            next = next.saturating_add(aux);
            out.extend(cls);
        }

        (out, next - fresh_base)
    }

    /// Public accessor for the gate-checkable automorphism generators, used by
    /// the HHW DRAT symmetry-breaking route (`AY_SAT_SYMMETRY_HHW`) which builds
    /// a per-generator Heule-Hunt-Wetzler image-and-chain proof fragment rather
    /// than a lex-leader/PR/SR encoding. Returns the SAME generator set the
    /// composite/DPR/SR routes consume.
    pub(crate) fn find_generators(
        &self,
        clauses: &[Vec<Literal>],
    ) -> Vec<BTreeMap<Variable, Variable>> {
        self.find_composite_generators(clauses)
    }

    /// Shared generator-finding core for the composite-symmetry path: IR
    /// automorphism finder (primary) with the backtracking closure finder as a
    /// fallback. Both `detect_and_encode_composite` (plain clauses) and
    /// `detect_and_encode_composite_with_witness` (PR-tagged clauses) consume the
    /// SAME generators, so the live no-proof path and the DPR proof path emit lex
    /// leaders for an identical generator set.
    fn find_composite_generators(
        &self,
        clauses: &[Vec<Literal>],
    ) -> Vec<BTreeMap<Variable, Variable>> {
        let formula_counts = build_formula_counts(clauses);

        // PRIMARY: individualization-refinement automorphism finder (saucy/nauty
        // core, adapted to CNF). Discovers the composite (vertex/color/block)
        // symmetries the consecutive/half-split and backtracking enumerators miss
        // on clique/coloring/PHP instances. Bounded by an IR-tree node budget so
        // preprocessing stays well under a second or two.
        // Budget defaults are tuned so clique preprocessing stays well under a
        // couple of seconds; overridable via env for experiments.
        let ir_node_budget: u64 = std::env::var("AY_SAT_IR_NODE_BUDGET")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(8_000);
        let ir_max_gens: usize = std::env::var("AY_SAT_IR_MAX_GENERATORS")
            .ok()
            .and_then(|s| s.parse().ok())
            .unwrap_or(96);
        let mut generators =
            super::ir::find_automorphisms(clauses, &formula_counts, ir_node_budget, ir_max_gens);

        // FALLBACK: if IR finds nothing, try the backtracking closure finder.
        if generators.is_empty() {
            let refined = refinement::iterative_color_refinement(clauses);
            let groups: Vec<Vec<Variable>> = refined.candidate_groups().into_values().collect();
            const COMPOSITE_NODE_BUDGET: u64 = 20_000;
            generators = find_composite_symmetries_backtracking(
                clauses,
                &formula_counts,
                &groups,
                self.max_pairs,
                COMPOSITE_NODE_BUDGET,
            );
        }
        generators
    }

    /// PR-emitting variant of [`Self::detect_and_encode_composite`]: emits the
    /// SAME per-generator lex-leader clauses for the SAME generators, but tags each
    /// one as [`LexClause::Pr`] (the aux-free `j=0` binary, with its σ-image
    /// witness) or [`LexClause::Aux`] (the `j>0` tower clauses + Tseitin defs that
    /// are NOT single-σ-PR — see [`encode_perm_lex_leader_with_witness`]).
    ///
    /// On the DPR proof route the caller emits ONLY the [`LexClause::Pr`] binaries
    /// (as DPR `a`-lines with the σ witness) and DROPS the [`LexClause::Aux`]
    /// clauses entirely; binary-only per-generator symmetry breaking is still
    /// satisfiability-preserving (each `(x_{w_0} ∨ ¬x_{σ⁻¹(w_0)})` is the
    /// 2-orbit lex-leader of a verified automorphism). Returns
    /// `(tagged_clauses, aux_allocated)`; the caller must `ensure_num_vars` for the
    /// aux it actually keeps (none, when it drops the Aux clauses).
    pub(crate) fn detect_and_encode_composite_with_witness(
        &self,
        clauses: &[Vec<Literal>],
        fresh_base: u32,
    ) -> (Vec<LexClause>, u32) {
        let generators = self.find_composite_generators(clauses);
        let mut out: Vec<LexClause> = Vec::new();
        let mut next = fresh_base;
        for g in &generators {
            let (tagged, aux) = encode_perm_lex_leader_with_witness(g, next);
            next = next.saturating_add(aux);
            out.extend(tagged);
        }
        (out, next - fresh_base)
    }

    /// SR-emitting variant of [`Self::detect_and_encode_composite_with_witness`]:
    /// emits the SAME per-generator lex-leader clauses for the SAME generators, but
    /// tags EVERY clause (the full lex tower, not just the aux-free `j=0` binary) as
    /// [`LexClause::Sr`] with the full automorphism substitution σ as witness
    /// (#8011 SR route).
    ///
    /// The generators are emitted in BreakID-style **tower order** (sorted by the
    /// minimum variable in each generator's support) so that each generator's lex
    /// tower is added on top of a formula that already contains the lower
    /// generators' SBP. Because the SR witness σ is a substitution, the SR
    /// redundancy check applies σ to the CURRENT formula — including the
    /// already-added SBP of the lower generators — and σ (a verified automorphism)
    /// maps that augmented formula onto itself, so the towers compose. Returns
    /// `(tagged_clauses, aux_allocated)`; the caller MUST `ensure_num_vars` for the
    /// allocated aux because the SR route KEEPS the whole tower.
    pub(crate) fn detect_and_encode_composite_sr(
        &self,
        clauses: &[Vec<Literal>],
        fresh_base: u32,
    ) -> (Vec<LexClause>, u32) {
        let mut generators = self.find_composite_generators(clauses);
        // Tower order: emit generators whose support starts lower first, so each
        // SR step resolves against the already-added lower-generator SBP.
        generators.sort_by_key(|g| g.keys().next().map(|v| v.0).unwrap_or(u32::MAX));
        let mut out: Vec<LexClause> = Vec::new();
        let mut next = fresh_base;
        for g in &generators {
            let (tagged, aux) = encode_perm_lex_leader_sr(g, next);
            next = next.saturating_add(aux);
            out.extend(tagged);
        }
        (out, next - fresh_base)
    }
}

/// A column-aligned set of mutually interchangeable rows (a BreakID row-symmetry
/// block). `rows[r]` is row `r`'s variables in column order; `rows[r][c]` and
/// `rows[r'][c]` are the SAME column `c` (interchanging rows `r,r'` maps them to
/// each other). All rows have the same length `n` (= number of columns) and the
/// variables across all rows are pairwise distinct.
#[derive(Debug, Clone, PartialEq, Eq)]
#[allow(dead_code)] // validated alternative infra (group-level row lex-leader); the
                    // active composite path uses per-generator lex-leader (see detect_and_encode_composite).
pub(crate) struct RowSet {
    pub(crate) rows: Vec<Vec<Variable>>,
}

/// True iff `anchor` is exactly one block of the involution `perm` and the OTHER
/// block is `perm(anchor)` — i.e. `perm`'s support is `anchor ∪ perm(anchor)`,
/// every transposition crosses from `anchor` to its complement, and `perm(a) ∉
/// anchor` for every `a ∈ anchor`. Under this condition `perm` is a CLEAN row
/// swap "anchor ↔ perm(anchor)" that fixes every other variable, and the column
/// of pair `{a, perm(a)}` is identified by the anchor element `a`.
#[allow(dead_code)] // validated alternative infra (group-level row lex-leader); the
                    // active composite path uses per-generator lex-leader (see detect_and_encode_composite).
fn is_clean_swap_with_anchor(
    perm: &BTreeMap<Variable, Variable>,
    anchor: &std::collections::BTreeSet<Variable>,
) -> bool {
    // The anchor must lie entirely in the support and map out of itself.
    for a in anchor {
        match perm.get(a) {
            Some(img) if !anchor.contains(img) => {}
            _ => return false,
        }
    }
    // Every non-anchor support variable must map INTO the anchor, so the support
    // is exactly anchor ∪ perm(anchor) (a clean two-block swap, nothing else).
    for v in perm.keys() {
        if !anchor.contains(v) && !anchor.contains(perm.get(v).expect("involution")) {
            return false;
        }
    }
    true
}

/// Build a row-set anchored on `anchor` (one block) by collecting every
/// not-yet-consumed involution that is a clean row swap "anchor ↔ image": each
/// such swap contributes one new row `image`, column-aligned to the anchor (row's
/// column `a` is the variable `perm(a)`). Rows are required to be pairwise
/// disjoint (independent variable sets). Returns the row-set (>= 2 rows incl. the
/// anchor) and the indices of the involutions it used, or `None` if fewer than
/// the requested rows can be formed.
#[allow(dead_code)] // validated alternative infra (group-level row lex-leader); the
                    // active composite path uses per-generator lex-leader (see detect_and_encode_composite).
fn build_rowset_from_anchor(
    anchor: &std::collections::BTreeSet<Variable>,
    perms: &[BTreeMap<Variable, Variable>],
    consumed: &[bool],
) -> Option<(RowSet, Vec<usize>)> {
    // Columns are the anchor variables in their natural (sorted) order.
    let cols: Vec<Variable> = anchor.iter().copied().collect();
    let mut rows: Vec<Vec<Variable>> = vec![cols.clone()]; // anchor row (identity)
    let mut row_vars: std::collections::BTreeSet<Variable> = anchor.clone();
    let mut used: Vec<usize> = Vec::new();

    for (idx, perm) in perms.iter().enumerate() {
        if consumed[idx] || !is_clean_swap_with_anchor(perm, anchor) {
            continue;
        }
        // Image row, aligned to the anchor's column order.
        let img: Vec<Variable> = cols.iter().map(|a| *perm.get(a).expect("clean")).collect();
        // Require disjointness from all rows already collected (independent rows).
        if img.iter().any(|v| row_vars.contains(v)) {
            continue;
        }
        for v in &img {
            row_vars.insert(*v);
        }
        rows.push(img);
        used.push(idx);
    }

    if rows.len() < 2 {
        return None;
    }
    // Deterministic chain order: sort rows by their column-0 variable. (Any fixed
    // order is sound — the group S_k can realise the lex-sorted representative.)
    rows.sort_by_key(|r| r[0].0);
    Some((RowSet { rows }, used))
}

/// Detect GROUP-level row interchangeability from gate-verified involutions.
///
/// Each involution is a product of disjoint transpositions = a candidate "row
/// swap" between two equal-size variable blocks. Two row swaps that share a
/// common block (their support intersection) chain into a larger interchangeable
/// row-set: we use the shared block as the ANCHOR, and every clean swap
/// "anchor ↔ image" adds the row `image`, column-aligned to the anchor. The
/// star of swaps `(anchor, R_i)` generates the full symmetric group `S_k` on the
/// rows, so a chained lex-leader over the rows is a sound group-symmetry break.
///
/// Returns row-sets with `>= 3` rows (where group breaking beats per-involution
/// SBP), greedily and with pairwise-disjoint involution usage; the caller
/// additionally enforces pairwise-disjoint variable support across all emitted
/// constraints. **Soundness does not depend on how the anchor was chosen**: each
/// retained row is built from a gate-verified clean swap, the rows are pairwise
/// disjoint, and the column alignment is fixed by the anchor — see the
/// soundness note on [`encode_rowset_lex_leader`].
#[allow(dead_code)] // validated alternative infra (group-level row lex-leader); the
                    // active composite path uses per-generator lex-leader (see detect_and_encode_composite).
fn detect_row_interchangeability(perms: &[BTreeMap<Variable, Variable>]) -> Vec<RowSet> {
    let supports: Vec<std::collections::BTreeSet<Variable>> =
        perms.iter().map(|p| p.keys().copied().collect()).collect();

    let mut consumed = vec![false; perms.len()];
    let mut result: Vec<RowSet> = Vec::new();

    loop {
        // Pick the largest row-set buildable from a fresh anchor this round.
        let mut best: Option<(RowSet, Vec<usize>, usize)> = None;
        for i in 0..perms.len() {
            if consumed[i] {
                continue;
            }
            for j in 0..perms.len() {
                if i == j || consumed[j] {
                    continue;
                }
                let anchor: std::collections::BTreeSet<Variable> =
                    supports[i].intersection(&supports[j]).copied().collect();
                if anchor.is_empty() {
                    continue;
                }
                if let Some((rs, used)) = build_rowset_from_anchor(&anchor, perms, &consumed) {
                    // >= 3 rows => >= 2 swaps share the anchor: genuine group.
                    if rs.rows.len() >= 3 {
                        let score = rs.rows.len() * rs.rows[0].len();
                        if best.as_ref().is_none_or(|(_, _, s)| score > *s) {
                            best = Some((rs, used, score));
                        }
                    }
                }
            }
        }
        match best {
            Some((rs, used, _)) => {
                for u in used {
                    consumed[u] = true;
                }
                result.push(rs);
            }
            None => break,
        }
    }
    result
}

/// Emit the Tseitin definition of the equal-prefix aux variable
/// `e_next ↔ e_prev ∧ (x = y)` (`e_prev = None` means the empty prefix, i.e.
/// `e_prev ≡ true`, so `e_next ↔ (x = y)`). A correct *iff* is what makes the
/// chain both sound (the leader's forced aux values satisfy every clause) and
/// effective (the constraint actually bites when the prefix is equal).
fn emit_eq_prefix_def(
    clauses: &mut Vec<Vec<Literal>>,
    e_next: Variable,
    e_prev: Option<Variable>,
    x: Variable,
    y: Variable,
) {
    let en = Literal::negative(e_next);
    let ep = Literal::positive(e_next);
    let xp = Literal::positive(x);
    let xn = Literal::negative(x);
    let yp = Literal::positive(y);
    let yn = Literal::negative(y);
    // e_next -> (x = y): (¬e_next ∨ ¬x ∨ y) ∧ (¬e_next ∨ x ∨ ¬y)
    clauses.push(vec![en, xn, yp]);
    clauses.push(vec![en, xp, yn]);
    match e_prev {
        None => {
            // (x = y) -> e_next: (e_next ∨ ¬x ∨ ¬y) ∧ (e_next ∨ x ∨ y)
            clauses.push(vec![ep, xn, yn]);
            clauses.push(vec![ep, xp, yp]);
        }
        Some(p) => {
            let pp = Literal::positive(p);
            let pn = Literal::negative(p);
            // e_next -> e_prev: (¬e_next ∨ e_prev)
            clauses.push(vec![en, pp]);
            // e_prev ∧ (x = y) -> e_next:
            //   (¬e_prev ∨ ¬x ∨ ¬y ∨ e_next) ∧ (¬e_prev ∨ x ∨ y ∨ e_next)
            clauses.push(vec![pn, xn, yn, ep]);
            clauses.push(vec![pn, xp, yp, ep]);
        }
    }
}

/// Encode a SOUND BreakID chained lex-leader for an interchangeable row-set:
/// `R_0 >=_lex R_1 >=_lex … >=_lex R_{k-1}` (column-major, column 0 most
/// significant). Allocates fresh equal-prefix aux variables sequentially from
/// `fresh_base`; returns `(clauses, aux_allocated)`.
///
/// For one consecutive pair `X >=_lex Y` over columns `0..n` the constraint is
/// `∀j: (x_0=y_0 ∧ … ∧ x_{j-1}=y_{j-1}) → x_j >= y_j`, which is *exactly*
/// `X >=_lex Y`. We realise it with equal-prefix aux `e_j ↔ (cols 0..j-1 equal)`
/// (`e_0 ≡ true`) and the per-column clause `(¬e_j ∨ x_j ∨ ¬y_j)` (for `j=0`,
/// `e_0 ≡ true` collapses it to the binary `(x_0 ∨ ¬y_0)`).
///
/// SOUNDNESS (satisfiability-preserving): the gate-verified swaps `(R_0, R_i)`
/// are formula automorphisms swapping the value-vectors of rows `0` and `i`
/// column-for-column and fixing all other rows; these star transpositions
/// generate `S_k` on the row value-vectors. For any model `α`, applying the group
/// element that sorts the rows into lex-decreasing order yields a model `α'`
/// (composition of automorphisms) that satisfies every `R_t >=_lex R_{t+1}`; set
/// each `e_j` to its forced (iff-defined) value and every clause holds. Hence the
/// formula is SAT iff the formula ∧ chain ∧ aux-defs is SAT. ∎
#[allow(dead_code)] // validated alternative infra (group-level row lex-leader); the
                    // active composite path uses per-generator lex-leader (see detect_and_encode_composite).
fn encode_rowset_lex_leader(rowset: &RowSet, fresh_base: u32) -> (Vec<Vec<Literal>>, u32) {
    let mut clauses: Vec<Vec<Literal>> = Vec::new();
    let mut next = fresh_base;
    let k = rowset.rows.len();
    if k < 2 {
        return (clauses, 0);
    }
    let n = rowset.rows[0].len();
    for t in 0..k - 1 {
        let x = &rowset.rows[t]; // the lex-greater row
        let y = &rowset.rows[t + 1]; // the lex-lesser row
        let mut e_prev: Option<Variable> = None; // e_0 ≡ true (empty prefix)
        for j in 0..n {
            let xj = x[j];
            let yj = y[j];
            // Constraint: prefix-equal -> x_j >= y_j  ==  (¬e_j ∨ x_j ∨ ¬y_j).
            match e_prev {
                None => clauses.push(vec![Literal::positive(xj), Literal::negative(yj)]),
                Some(e) => clauses.push(vec![
                    Literal::negative(e),
                    Literal::positive(xj),
                    Literal::negative(yj),
                ]),
            }
            // Define e_{j+1} for the next column (last column needs no successor).
            if j + 1 < n {
                let e_next = Variable(next);
                next = next.saturating_add(1);
                emit_eq_prefix_def(&mut clauses, e_next, e_prev, xj, yj);
                e_prev = Some(e_next);
            }
        }
    }
    (clauses, next - fresh_base)
}

/// Encode a SOUND lex-leader symmetry-breaking predicate for a SINGLE verified
/// automorphism `perm`: `x ⪰_lex perm·x` over the GLOBAL ascending variable-id
/// order, where `(perm·x)_v = x_{perm⁻¹(v)}`. Allocates fresh equal-prefix aux
/// variables sequentially from `fresh_base`; returns `(clauses, aux_allocated)`.
///
/// Only the moved variables (`perm`'s support, in ascending id order) contribute:
/// outside the support `perm` fixes the variable, so those positions are always
/// equal in the global lex comparison and never decide it. For the support
/// `w_0 < w_1 < … < w_{s-1}` the predicate is, for each `j`,
/// `(w_0..w_{j-1} all equal to their images) → x_{w_j} ≥ x_{perm⁻¹(w_j)}`,
/// realised with equal-prefix aux `e_j ↔ (cols 0..j-1 equal)` and the per-column
/// clause `(¬e_j ∨ x_{w_j} ∨ ¬x_{perm⁻¹(w_j)})` (`e_0 ≡ true` collapses `j=0` to
/// the binary `(x_{w_0} ∨ ¬x_{perm⁻¹(w_0)})`).
///
/// SOUNDNESS for a SET of generators emitted together (the caller's use): see the
/// multi-generator lex-leader theorem in [`SymmetryDetector::detect_and_encode_composite`].
/// `perm` MUST have passed [`permutation_preserves_formula`] first.
fn encode_perm_lex_leader(
    perm: &BTreeMap<Variable, Variable>,
    fresh_base: u32,
) -> (Vec<Vec<Literal>>, u32) {
    let mut clauses: Vec<Vec<Literal>> = Vec::new();
    let mut next = fresh_base;
    // Support in ascending id order (BTreeMap keys are sorted).
    let support: Vec<Variable> = perm.keys().copied().collect();
    if support.is_empty() {
        return (clauses, 0);
    }
    // Inverse map: perm restricted to its support is a bijection support→support.
    let mut inv: BTreeMap<Variable, Variable> = BTreeMap::new();
    for (k, v) in perm {
        inv.insert(*v, *k);
    }
    // Defensive: only encode if perm is a bijection of its own support (IR
    // generators are projected from a node bijection and always satisfy this;
    // a malformed fallback-finder generator might not). Emitting no constraint
    // is always sound, so skip rather than risk a panic on a non-closed support.
    if inv.len() != perm.len() || !perm.keys().all(|k| inv.contains_key(k)) {
        return (clauses, 0);
    }
    let n = support.len();
    let mut e_prev: Option<Variable> = None; // e_0 ≡ true (empty prefix)
    for (j, &xj) in support.iter().enumerate() {
        // y_j = (perm·x)_{w_j} = x_{perm⁻¹(w_j)}.
        let yj = *inv
            .get(&xj)
            .expect("support is closed under perm (a permutation of itself)");
        // Constraint: prefix-equal -> x_j >= y_j == (¬e_j ∨ x_j ∨ ¬y_j).
        match e_prev {
            None => clauses.push(vec![Literal::positive(xj), Literal::negative(yj)]),
            Some(e) => clauses.push(vec![
                Literal::negative(e),
                Literal::positive(xj),
                Literal::negative(yj),
            ]),
        }
        if j + 1 < n {
            let e_next = Variable(next);
            next = next.saturating_add(1);
            emit_eq_prefix_def(&mut clauses, e_next, e_prev, xj, yj);
            e_prev = Some(e_next);
        }
    }
    (clauses, next - fresh_base)
}

/// A single emitted lex-leader clause tagged with how it can be certified in a
/// PR/DPR proof (the witness-threading half of the #8011 work).
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum LexClause {
    /// An aux-free lex clause (every literal lies in `σ`'s support) certifiable as
    /// PR with the σ-image witness `w = σ(¬C)`. `witness` is the partial-assignment
    /// witness as literals; it always contains `clause[0]` (the chosen pivot), so a
    /// DPR `a`-line `clause… witness… 0` is well-formed.
    Pr {
        clause: Vec<Literal>,
        witness: Vec<Literal>,
    },
    /// A clause carrying a fresh equal-prefix aux variable `e_j` (the lex clause for
    /// position `j > 0`, or an `e_j ↔ prefix-equal` Tseitin definition). `σ` does
    /// not constrain `e_j`, so the σ-image construction does NOT certify it; it must
    /// be emitted on the RAT/blocked route. This is exactly the part of the
    /// multi-position lex tower that does not compose under single-σ PR (#8011).
    Aux { clause: Vec<Literal> },
    /// An SR (substitution-redundant) tower clause certifiable under the full
    /// automorphism substitution σ (#8011 SR route). `witness` is the DSR
    /// witness-token stream that follows `clause` on the `a`-line: it begins by
    /// repeating the pivot `clause[0]` (the 2nd pivot occurrence opens the PR part
    /// `pivot↦⊤`, the 3rd opens the substitution part), then carries σ as
    /// literal↦literal pairs. Unlike [`LexClause::Pr`] this certifies the WHOLE lex
    /// tower (including the `j>0` clauses and Tseitin defs) under the same σ:
    /// because σ is a verified automorphism it remaps the formula — including any
    /// previously added SBP — onto itself, so the tower composes (Codel-Avigad-Heule
    /// FMCAD 2024). Verified externally by `dsr-trim → drat/lsr → cake_lpr`.
    Sr {
        clause: Vec<Literal>,
        witness: Vec<Literal>,
    },
}

/// Build the DSR witness-token stream for SR clause `clause` under the
/// automorphism substitution `perm` (var↦var). The returned vector is the witness
/// portion of the `a`-line (it is written after `clause`, before the terminating
/// `0`): `[pivot, pivot, k₁ v₁, k₂ v₂, …]` where `pivot = clause[0]`.
///
/// Layout (see `dsr-trim`'s `parse_sr_clause_and_witness`): the SECOND occurrence
/// of the pivot opens the witness PR part (forcing `pivot↦⊤`, which satisfies the
/// added clause); the THIRD occurrence is the separator opening the substitution
/// part, which lists σ as positive-literal `from to` pairs. The pivot's own
/// variable is omitted from the pairs (it is already pinned to ⊤ in the PR part,
/// and "only the pivot may map to itself"); identity mappings (`k == v`) are
/// skipped as well.
fn sr_witness_tokens(clause: &[Literal], perm: &BTreeMap<Variable, Variable>) -> Vec<Literal> {
    let pivot = clause[0];
    let pivot_var = pivot.variable();
    let mut witness = vec![pivot, pivot];
    for (k, v) in perm {
        if *k == *v || *k == pivot_var {
            continue;
        }
        witness.push(Literal::positive(*k));
        witness.push(Literal::positive(*v));
    }
    witness
}

/// SR variant of [`encode_perm_lex_leader_with_witness`]: emits the SAME full lex
/// tower (the `j=0` binary, every `j>0` lex clause, and all Tseitin equal-prefix
/// definitions — identical literals and aux allocation) but tags EVERY clause as
/// [`LexClause::Sr`] with the full automorphism substitution σ as its DSR witness.
///
/// This is the #8011 SR fix: where the DPR route kept only the aux-free `j=0`
/// binary (single-σ PR) and DROPPED the rest, the SR witness is a SUBSTITUTION, so
/// σ certifies the whole tower at once — applying σ to the current formula
/// (including previously added SBP) maps it onto itself, so the per-generator
/// towers compose. Returns `(tagged_clauses, aux_allocated)` with the same
/// `aux_allocated` count as [`encode_perm_lex_leader`].
fn encode_perm_lex_leader_sr(
    perm: &BTreeMap<Variable, Variable>,
    fresh_base: u32,
) -> (Vec<LexClause>, u32) {
    let (plain, aux) = encode_perm_lex_leader(perm, fresh_base);
    let out = plain
        .into_iter()
        .map(|clause| {
            let witness = sr_witness_tokens(&clause, perm);
            LexClause::Sr { clause, witness }
        })
        .collect();
    (out, aux)
}

/// AUX-FREE SR refutation for the pigeonhole family — a faithful port of the
/// reference generator `third_party/dsr-trim/php/php-sr.c` (Heule/Codel), driven
/// off the detected pigeonhole matrix instead of a hard-coded hole count.
///
/// WHY THIS EXISTS (the #8011 SR blocker). The lex-leader SR route
/// ([`encode_perm_lex_leader_sr`]) emits, per generator, a lex tower that carries
/// fresh equal-prefix aux variables `e_j`. The `e_j` Tseitin definition clauses
/// are NOT redundant under a σ-only substitution witness (σ never touches `e_j`),
/// so `dsr-trim` rejects them ("No UP contradiction for RAT clause"). The fix is
/// to abandon lex-leaders and instead emit a COMPLETE refutation over the
/// ORIGINAL variables only — exactly what php-sr.c does.
///
/// THE CONSTRUCTION (per hole `h`, in tower order `h = 0 … H-2`):
///   * For `p = P-1` down to `h+1`, the SR unit `(¬x_{p,h})` ("pigeon p is not in
///     hole h"), witnessed by the pigeon-swap automorphism `σ = (pigeon p-1 ↔
///     pigeon p)` restricted to holes `j > h` (the literal↦literal substitution
///     part), PLUS the partial assignment `{x_{p,h}=0, x_{p-1,h}=1}` (the PR part:
///     put pigeon p-1 in hole h instead). Holes `j < h` need no swap because the
///     previous tower steps already excluded both pigeons from them; hole `h`
///     itself is handled by the PR part. This is precisely why the tower ORDER
///     matters and why it is aux-free.
///   * The RAT unit `(x_{h,h})` (pigeon h occupies hole h) — RAT on `x_{h,h}`: the
///     only clauses with `¬x_{h,h}` are the hole-`h` AMO binaries, whose resolvents
///     `(¬x_{p,h})` are the units just derived.
///   * The RAT units `(¬x_{h,j})` for `j > h` — RAT on `¬x_{h,j}`: the only clause
///     with `x_{h,j}` is pigeon h's ALO, whose resolvent contains the unit
///     `x_{h,h}`.
///
/// The accumulated units make the last two pigeons collide in the last hole, so
/// the empty clause follows by plain unit propagation (the SOLVER derives and
/// emits it — it is not part of the returned steps).
///
/// Returns `None` when `clauses` is not a pure pigeonhole matrix. SOUNDNESS: when
/// `Some`, every emitted clause is SR/RAT-redundant by construction; a mis-detected
/// matrix can only yield a proof `dsr-trim` REJECTS, never a false VERIFIED.
///
/// Each returned [`LexClause::Sr`] carries the full DSR witness token stream
/// (already beginning with the repeated pivot `clause[0]`), so the caller writes it
/// verbatim after the clause on the `a`-line. The "RAT" units use the minimal
/// pivot-only PR witness `[pivot]` (i.e. the on-wire form `lit lit 0`), which
/// `dsr-trim` accepts identically to a bare `lit 0` RAT line.
pub(crate) fn detect_php_aux_free_sr(clauses: &[Vec<Literal>]) -> Option<Vec<LexClause>> {
    if let Some(matrix) = detect_php_matrix(clauses) {
        return Some(build_php_aux_free_sr(&matrix));
    }
    // `detect_php_matrix` demands the WHOLE formula be one pigeonhole matrix, so
    // a formula that is several variable-disjoint pigeonholes is rejected even
    // though each part is recognisable. Every `chnl` instance is exactly two
    // disjoint PHPs: `chnl-040x041` is 80 AMO cliques of size 41 and 82
    // all-positive width-40 clauses, i.e. (P=41,H=40) twice. Pooled it looks
    // like P=82 against H=40 and fails the shape test.
    //
    // Soundness: a pigeon swap confined to one component is the identity on
    // every other variable, so it is still an automorphism of the FULL formula
    // and its units stay redundant there. And refuting any one component
    // refutes the conjunction. Confirmed externally: the 1638 SR units derived
    // from a single component of `chnl-040x041` verify against the full
    // two-component CNF (`s VERIFIED UNSAT`).
    // Cheap pre-filter before the split. `detect_php_matrix` accepts only
    // all-positive ALO clauses and binary all-negative AMO clauses; a formula
    // containing anything else cannot have a pigeonhole component that the
    // split would find, because a component inherits its clauses whole.
    //
    // This scan is O(clauses) with no allocation, and it matters: without it
    // the split below clones every clause of every formula whose PHP detection
    // failed — i.e. almost all of them — which took the ay-sat suite from 132 s
    // to 697 s when this route went default-on.
    if !clauses.iter().all(|c| {
        (c.len() >= 2 && c.iter().all(|l| l.is_positive()))
            || (c.len() == 2 && c.iter().all(|l| !l.is_positive()))
    }) {
        return None;
    }
    let parts = split_variable_disjoint(clauses)?;
    let mut out = Vec::new();
    for part in &parts {
        if let Some(matrix) = detect_php_matrix(part) {
            out.extend(build_php_aux_free_sr(&matrix));
        }
    }
    (!out.is_empty()).then_some(out)
}

/// Partition `clauses` into variable-disjoint groups, or `None` if there is only
/// one (in which case the caller has already tried it whole).
///
/// Union-find over variables, then bucket the clauses by their root. Returns
/// `None` for the degenerate cases so callers can stay on the fast path.
fn split_variable_disjoint(clauses: &[Vec<Literal>]) -> Option<Vec<Vec<Vec<Literal>>>> {
    let max_var = clauses
        .iter()
        .flat_map(|c| c.iter())
        .map(|l| l.variable().index())
        .max()?;
    let mut parent: Vec<u32> = (0..=max_var as u32).collect();
    fn find(parent: &mut [u32], mut x: u32) -> u32 {
        while parent[x as usize] != x {
            parent[x as usize] = parent[parent[x as usize] as usize]; // path halving
            x = parent[x as usize];
        }
        x
    }
    for clause in clauses {
        let mut it = clause.iter().map(|l| l.variable().index() as u32);
        let Some(first) = it.next() else { continue };
        let mut ra = find(&mut parent, first);
        for v in it {
            let rb = find(&mut parent, v);
            if ra != rb {
                parent[rb as usize] = ra;
                ra = find(&mut parent, ra);
            }
        }
    }
    let mut bucket_of: BTreeMap<u32, usize> = BTreeMap::new();
    let mut parts: Vec<Vec<Vec<Literal>>> = Vec::new();
    for clause in clauses {
        let Some(first) = clause.first() else {
            continue;
        };
        let root = find(&mut parent, first.variable().index() as u32);
        let idx = *bucket_of.entry(root).or_insert_with(|| {
            parts.push(Vec::new());
            parts.len() - 1
        });
        parts[idx].push(clause.clone());
    }
    (parts.len() >= 2).then_some(parts)
}

/// Recognise a pure pigeonhole matrix in `clauses` and return it as
/// `M[row][col]` (`row` = pigeon, `col` = hole), with `P = M.len() = H + 1` rows
/// and `H = M[0].len()` columns.
///
/// The recognised structure (PHP / row-interchangeable ALO+AMO matrix):
///   * Every clause is EITHER an all-positive "at-least-one" (ALO) row clause of
///     width `H`, OR an all-negative binary "at-most-one" (AMO) clause.
///   * There are `P = H + 1` ALO clauses over pairwise-disjoint variable sets
///     (`P·H` distinct variables total).
///   * The AMO graph splits into exactly `H` complete `P`-cliques ("holes"), each
///     with one variable per pigeon, and the AMO edge count is exactly
///     `H · C(P,2)` (no missing or extra binaries).
///
/// These checks guarantee that each pigeon-swap `σ = (pigeon a ↔ pigeon b)` (swap
/// `M[a][c] ↔ M[b][c]` for all columns `c`) is a genuine formula automorphism,
/// which is what makes the emitted SR units redundant.
fn detect_php_matrix(clauses: &[Vec<Literal>]) -> Option<Vec<Vec<Variable>>> {
    use std::collections::BTreeSet;

    let mut alo: Vec<Vec<Variable>> = Vec::new();
    let mut amo_edges: Vec<(Variable, Variable)> = Vec::new();
    for c in clauses {
        if c.len() >= 2 && c.iter().all(|l| l.is_positive()) {
            alo.push(c.iter().map(|l| l.variable()).collect());
        } else if c.len() == 2 && c.iter().all(|l| !l.is_positive()) {
            amo_edges.push((c[0].variable(), c[1].variable()));
        } else {
            return None; // not a pure pigeonhole matrix
        }
    }

    let p = alo.len();
    let h = alo.first()?.len();
    if p < 3 || h < 2 || p < h + 1 {
        // Pigeonhole needs MORE pigeons than holes; P = H + 1 is merely the
        // tight case. P > H + 1 is a strictly easier instance and the aux-free
        // SR construction covers it unchanged, because it iterates all P rows.
        //
        // An earlier attempt at this relaxation was refuted, but what it
        // actually did was TRUNCATE the matrix to h + 1 rows — that discards
        // pigeons and breaks the diagonal RAT units. Keeping every row instead
        // produces a certificate dsr-trim accepts: php_11_8 (P=11, H=8) checks
        // as `s VERIFIED UNSAT`.
        return None;
    }
    if alo.iter().any(|row| row.len() != h) {
        return None; // ragged rows: not a matrix
    }

    // Pigeon (row) index of each variable; rows must be disjoint with no dups.
    let mut pigeon_of: BTreeMap<Variable, usize> = BTreeMap::new();
    for (i, row) in alo.iter().enumerate() {
        let mut seen: BTreeSet<Variable> = BTreeSet::new();
        for &v in row {
            if !seen.insert(v) || pigeon_of.insert(v, i).is_some() {
                return None; // duplicate variable in / across ALO rows
            }
        }
    }
    if pigeon_of.len() != p * h {
        return None;
    }

    // AMO adjacency; every binary must cross two different pigeons.
    let mut adj: BTreeMap<Variable, BTreeSet<Variable>> = BTreeMap::new();
    for &(a, b) in &amo_edges {
        let (pa, pb) = (pigeon_of.get(&a)?, pigeon_of.get(&b)?);
        if a == b || pa == pb {
            return None;
        }
        adj.entry(a).or_default().insert(b);
        adj.entry(b).or_default().insert(a);
    }
    if amo_edges.len() != h * (p * (p - 1) / 2) {
        return None; // wrong AMO count (missing/extra binaries)
    }

    // Holes = connected components of the AMO graph (BFS).
    let mut hole_of: BTreeMap<Variable, usize> = BTreeMap::new();
    let mut holes: Vec<Vec<Variable>> = Vec::new();
    for &start in pigeon_of.keys() {
        if hole_of.contains_key(&start) {
            continue;
        }
        let hole_id = holes.len();
        let mut members: Vec<Variable> = Vec::new();
        let mut stack = vec![start];
        hole_of.insert(start, hole_id);
        while let Some(u) = stack.pop() {
            members.push(u);
            if let Some(ns) = adj.get(&u) {
                for &w in ns {
                    if let std::collections::btree_map::Entry::Vacant(e) = hole_of.entry(w) {
                        e.insert(hole_id);
                        stack.push(w);
                    }
                }
            }
        }
        holes.push(members);
    }
    if holes.len() != h {
        return None;
    }
    // Each hole: exactly P vars, one per pigeon, forming a complete clique.
    for hole in &holes {
        if hole.len() != p {
            return None;
        }
        let mut pigeons: BTreeSet<usize> = BTreeSet::new();
        for &v in hole {
            if !pigeons.insert(*pigeon_of.get(&v)?) {
                return None; // two hole vars from the same pigeon
            }
            let ns = adj.get(&v)?;
            if hole.iter().any(|&w| w != v && !ns.contains(&w)) {
                return None; // hole is not a complete clique
            }
        }
    }

    // Deterministic labelling: rows by their min variable, holes by their min
    // variable. The exact labels are irrelevant to soundness (all pigeons are
    // interchangeable and all holes are interchangeable); a fixed order just makes
    // the emitted proof reproducible.
    let mut row_order: Vec<usize> = (0..p).collect();
    row_order.sort_by_key(|&i| alo[i].iter().map(|v| v.0).min().unwrap_or(u32::MAX));
    let mut hole_rank: BTreeMap<usize, usize> = BTreeMap::new();
    let mut by_min: Vec<(usize, u32)> = holes
        .iter()
        .enumerate()
        .map(|(k, hv)| (k, hv.iter().map(|v| v.0).min().unwrap_or(u32::MAX)))
        .collect();
    by_min.sort_by_key(|&(_, m)| m);
    for (rank, &(k, _)) in by_min.iter().enumerate() {
        hole_rank.insert(k, rank);
    }

    // M[row][col] = the variable of pigeon `row_order[row]` lying in hole `col`.
    let mut matrix: Vec<Vec<Option<Variable>>> = vec![vec![None; h]; p];
    for (row, &i) in row_order.iter().enumerate() {
        for &v in &alo[i] {
            let col = *hole_rank.get(hole_of.get(&v)?)?;
            if matrix[row][col].is_some() {
                return None; // two of this pigeon's vars in the same hole
            }
            matrix[row][col] = Some(v);
        }
    }
    matrix
        .into_iter()
        .map(|row| row.into_iter().collect::<Option<Vec<Variable>>>())
        .collect::<Option<Vec<Vec<Variable>>>>()
}

/// Build the aux-free SR refutation steps from a recognised pigeonhole matrix
/// `M[row][col]` (`P = M.len()` pigeons, `H = M[0].len()` holes, `P = H + 1`).
/// Mirrors the loop structure and witness layout of php-sr.c verbatim. The empty
/// clause is intentionally NOT emitted here — it follows by root unit propagation
/// once the caller has added these units, and the solver emits it.
fn build_php_aux_free_sr(matrix: &[Vec<Variable>]) -> Vec<LexClause> {
    let p = matrix.len(); // P = H + 1 pigeons (rows 0..=H)
    let h = matrix.first().map_or(0, Vec::len); // H holes (cols 0..H-1)
    let mut out: Vec<LexClause> = Vec::new();
    if p < 3 || h < 2 || p < h + 1 {
        return out; // see detect_php_matrix: P >= H + 1, untruncated
    }

    for hole in 0..h - 1 {
        // SR units (¬x_{p,h}) for p = P-1 down to hole+1, each witnessed by the
        // pigeon-swap (pigeon p-1 ↔ pigeon p) over holes j > hole.
        for pig in ((hole + 1)..=(p - 1)).rev() {
            let v1 = matrix[pig][hole];
            let v2 = matrix[pig - 1][hole];
            let clause = vec![Literal::negative(v1)];
            // Witness token stream: [pivot, PR-assignment…, pivot(separator),
            // substitution pairs…]. The PR part puts pigeon p-1 into hole h; the
            // substitution swaps pigeons p-1 and p in every later hole.
            let mut witness = vec![
                Literal::negative(v1), // 2nd pivot occurrence: opens the PR part
                Literal::positive(v2), // PR assignment x_{p-1,h} = 1
                Literal::negative(v1), // 3rd pivot occurrence: separator
            ];
            for (&v3, &v4) in matrix[pig - 1][(hole + 1)..h]
                .iter()
                .zip(&matrix[pig][(hole + 1)..h])
            {
                // σ(v3) = v4, σ(v4) = v3 (swap the two pigeons in hole j).
                witness.push(Literal::positive(v3));
                witness.push(Literal::positive(v4));
                witness.push(Literal::positive(v4));
                witness.push(Literal::positive(v3));
            }
            out.push(LexClause::Sr { clause, witness });
        }

        // RAT unit (x_{h,h}): pigeon `hole` occupies hole `hole`.
        let diag = matrix[hole][hole];
        out.push(LexClause::Sr {
            clause: vec![Literal::positive(diag)],
            witness: vec![Literal::positive(diag)],
        });

        // RAT units (¬x_{h,j}) for j > hole: pigeon `hole` is in no later hole.
        for &v in &matrix[hole][(hole + 1)..h] {
            out.push(LexClause::Sr {
                clause: vec![Literal::negative(v)],
                witness: vec![Literal::negative(v)],
            });
        }
    }
    out
}

/// Witness-threading variant of [`encode_perm_lex_leader`]: emits the SAME clauses
/// (identical literals and aux allocation) but tags each one with its PR
/// certifiability and, for the aux-free clauses, the σ-image PR witness.
///
/// For lex clause `C` with negation `α = ¬C`, the PR witness is `w = σ(α)`: apply
/// `σ` literal-wise to the negated original-variable literals of `C`. Concretely
/// the position-`j` clause `(… ∨ x_{w_j} ∨ ¬x_{σ⁻¹(w_j)})` yields
/// `w = {¬x_{σ(w_j)},  x_{w_j}}`, which satisfies `C` via `x_{w_j}` and witnesses
/// the RUP entailments because `σ` is a verified automorphism (see
/// [`permutation_preserves_formula`] and the PR contract in
/// `ay_proof_common::contracts`). Only `j = 0` (the binary `(x_{w_0} ∨ ¬x_{σ⁻¹(w_0)})`)
/// is aux-free and PR-certifiable; every later position carries `e_j` and is
/// returned as [`LexClause::Aux`].
///
/// `perm` MUST have passed [`permutation_preserves_formula`]. Returns
/// `(tagged_clauses, aux_allocated)` with the same `aux_allocated` count as
/// [`encode_perm_lex_leader`].
fn encode_perm_lex_leader_with_witness(
    perm: &BTreeMap<Variable, Variable>,
    fresh_base: u32,
) -> (Vec<LexClause>, u32) {
    let mut out: Vec<LexClause> = Vec::new();
    let mut next = fresh_base;
    let support: Vec<Variable> = perm.keys().copied().collect();
    if support.is_empty() {
        return (out, 0);
    }
    let mut inv: BTreeMap<Variable, Variable> = BTreeMap::new();
    for (k, v) in perm {
        inv.insert(*v, *k);
    }
    if inv.len() != perm.len() || !perm.keys().all(|k| inv.contains_key(k)) {
        return (out, 0);
    }
    let n = support.len();
    let mut e_prev: Option<Variable> = None;
    for (j, &xj) in support.iter().enumerate() {
        let yj = *inv
            .get(&xj)
            .expect("support is closed under perm (a permutation of itself)");
        match e_prev {
            None => {
                // j == 0: aux-free binary clause (x_{w_0} ∨ ¬x_{σ⁻¹(w_0)}).
                let clause = vec![Literal::positive(xj), Literal::negative(yj)];
                // σ-image witness w = σ(¬C). ¬C = {¬x_{w_0}, x_{σ⁻¹(w_0)}}.
                //   σ(¬x_{w_0})       = ¬x_{σ(w_0)}
                //   σ(x_{σ⁻¹(w_0)})   =  x_{w_0}        (pivot — satisfies C)
                let s_xj = *perm.get(&xj).expect("xj in support");
                let witness = vec![Literal::positive(xj), Literal::negative(s_xj)];
                debug_assert!(
                    witness.contains(&clause[0]),
                    "PR witness must contain the clause pivot (DPR a-line well-formedness)"
                );
                out.push(LexClause::Pr { clause, witness });
            }
            Some(e) => {
                // j > 0: carries the fresh aux e_j → not σ-certifiable (#8011).
                out.push(LexClause::Aux {
                    clause: vec![
                        Literal::negative(e),
                        Literal::positive(xj),
                        Literal::negative(yj),
                    ],
                });
            }
        }
        if j + 1 < n {
            let e_next = Variable(next);
            next = next.saturating_add(1);
            // The e_{j+1} ↔ prefix-equal Tseitin definition clauses are fresh-aux
            // definitions, emitted on the RAT/blocked route.
            let mut def: Vec<Vec<Literal>> = Vec::new();
            emit_eq_prefix_def(&mut def, e_next, e_prev, xj, yj);
            for clause in def {
                out.push(LexClause::Aux { clause });
            }
            e_prev = Some(e_next);
        }
    }
    (out, next - fresh_base)
}

/// Check whether swapping `pair.lhs <-> pair.rhs` in every clause preserves
/// the formula as a multiset of canonical clause keys.
fn swap_preserves_formula_interruptible(
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    pair: BinarySwap,
    should_stop: &impl Fn() -> bool,
) -> Option<bool> {
    // FmlaEquivChain spends minutes here in debug builds: each candidate pair
    // scans the full clause multiset and performs a BTreeMap lookup per clause.
    // Poll often enough to bound cancellation latency without putting an atomic
    // load / clock read on every lookup.
    const INTERRUPT_POLL_INTERVAL: usize = 64;

    for (clause_index, (clause, count)) in formula_counts.iter().enumerate() {
        if clause_index.is_multiple_of(INTERRUPT_POLL_INTERVAL) && should_stop() {
            return None;
        }
        if formula_counts.get(&swap_clause_key(clause, pair)) != Some(count) {
            return Some(false);
        }
    }
    Some(true)
}

/// Apply a variable swap to a canonical clause key and re-sort.
fn swap_clause_key(clause: &[u32], pair: BinarySwap) -> Vec<u32> {
    let mut swapped = Vec::with_capacity(clause.len());
    for &raw in clause {
        let lit = Literal(raw);
        let mapped_var = if lit.variable() == pair.lhs {
            pair.rhs
        } else if lit.variable() == pair.rhs {
            pair.lhs
        } else {
            lit.variable()
        };
        let mapped_lit = if lit.is_positive() {
            Literal::positive(mapped_var)
        } else {
            Literal::negative(mapped_var)
        };
        swapped.push(mapped_lit.raw());
    }
    swapped.sort_unstable();
    swapped
}

/// SOUND verification gate for composite-permutation symmetry detection (#17).
///
/// Generalizes the single-transposition check in
/// [`swap_preserves_formula_interruptible`] to an
/// arbitrary variable permutation `perm` (each variable maps to its image;
/// variables absent from `perm` are fixed). Returns true iff applying `perm` to
/// every clause leaves the formula invariant as a multiset of canonical clause
/// keys — i.e. `perm` is a genuine formula automorphism.
///
/// This is the soundness foundation of the composite-symmetry work: a candidate
/// permutation (from a future automorphism finder) MUST pass this gate before
/// any symmetry-breaking clause may be derived from it, so an unsound candidate
/// can never produce an unsound SBP. The single-transposition symmetries the
/// current detector misses on clique/coloring/PHP instances are *composite*
/// permutations this gate accepts.
pub(crate) fn permutation_preserves_formula(
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    perm: &BTreeMap<Variable, Variable>,
) -> bool {
    formula_counts.iter().all(|(clause, count)| {
        formula_counts
            .get(&permute_clause_key(clause, perm))
            .is_some_and(|permuted_count| permuted_count == count)
    })
}

/// Apply a variable permutation to a canonical clause key and re-sort.
#[allow(dead_code)] // #17 building block (see permutation_preserves_formula).
fn permute_clause_key(clause: &[u32], perm: &BTreeMap<Variable, Variable>) -> Vec<u32> {
    let mut permuted = Vec::with_capacity(clause.len());
    for &raw in clause {
        let lit = Literal(raw);
        let mapped_var = perm.get(&lit.variable()).copied().unwrap_or(lit.variable());
        let mapped_lit = if lit.is_positive() {
            Literal::positive(mapped_var)
        } else {
            Literal::negative(mapped_var)
        };
        permuted.push(mapped_lit.raw());
    }
    permuted.sort_unstable();
    permuted
}

/// Find composite-permutation symmetries (#17, piece 2): enumerate candidate
/// involutions from refined color classes and keep only those that pass the
/// [`permutation_preserves_formula`] gate. **Sound by construction** — a
/// candidate that is not a real formula automorphism is discarded, so a weak or
/// buggy enumerator can only find *fewer* symmetries, never an unsound one.
///
/// This is a first, bounded enumerator: within each refined class it tries the
/// consecutive pairing `(g0 g1)(g2 g3)…` (captures value/color swaps when the
/// class groups a vertex's color variables) and the half-split pairing
/// `(g0 g_{m})(g1 g_{m+1})…` (captures block/vertex swaps). A complete
/// automorphism search (saucy/bliss, or backtracking individualization-
/// refinement) is the eventual upgrade. It does NOT emit SBP — the
/// per-permutation lex-leader encoder is the separate soundness-critical piece.
#[allow(dead_code)] // #17 piece 2; wired once the SBP encoder (piece 3) lands.
fn find_composite_symmetries(
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    refined_groups: &[Vec<Variable>],
    max_candidates: usize,
) -> Vec<BTreeMap<Variable, Variable>> {
    let mut candidates: Vec<Vec<(Variable, Variable)>> = Vec::new();
    for group in refined_groups {
        if group.len() < 2 {
            continue;
        }
        // Consecutive pairing within the class.
        candidates.push(
            group
                .chunks(2)
                .filter(|c| c.len() == 2)
                .map(|c| (c[0], c[1]))
                .collect(),
        );
        // Half-split pairing (only well-defined for even classes).
        if group.len() % 2 == 0 {
            let m = group.len() / 2;
            candidates.push((0..m).map(|i| (group[i], group[m + i])).collect());
        }
    }

    let mut found = Vec::new();
    for pairs in candidates.into_iter().take(max_candidates) {
        let mut perm = BTreeMap::new();
        for (a, b) in pairs {
            perm.insert(a, b);
            perm.insert(b, a);
        }
        // The gate is the soundness guarantee: only genuine automorphisms survive.
        if perm.len() >= 2 && permutation_preserves_formula(formula_counts, &perm) {
            found.push(perm);
        }
    }
    found
}

/// Encode a SOUND symmetry-breaking clause for a single verified involution
/// automorphism `perm` (#17, piece 3).
///
/// For an involution π (a product of disjoint transpositions) with smallest
/// moved variable `v` and `w = π(v)` (necessarily `w > v`), the binary clause
/// `(x_v ∨ ¬x_w)` is **satisfiability-preserving**:
///
/// > If a model `a` violates it (`a[v]=0, a[w]=1`), then `b = π·a` is also a
/// > model (π is a formula automorphism) with `b[v]=a[π(v)]=a[w]=1` and
/// > `b[w]=a[π(w)]=a[v]=0` (involution: `π(w)=v`), so `b` satisfies the clause.
/// > Hence `F` is SAT iff `F ∧ (x_v ∨ ¬x_w)` is SAT. ∎
///
/// This is aux-free and carries no over-constraint risk for a single π. (Adding
/// clauses for MULTIPLE permutations is only sound when their supports are
/// disjoint — left to the caller / a later refinement; the full per-permutation
/// lex-leader chain, which breaks more symmetry, is the eventual upgrade.)
/// `perm` MUST have passed [`permutation_preserves_formula`] first.
#[allow(dead_code)] // #17 piece 3; wired into preprocess (default-off) + fuzzed next.
fn encode_involution_sbp(perm: &BTreeMap<Variable, Variable>) -> Option<Vec<Literal>> {
    // Smallest moved variable; perm only contains moved variables.
    let v = *perm.keys().next()?;
    let w = *perm.get(&v)?;
    // For the minimum key v, its image w is also a key (involution) and w != v,
    // so w > v. Guard anyway: only emit the canonical v < w orientation.
    if w <= v {
        return None;
    }
    Some(vec![Literal::positive(v), Literal::negative(w)])
}

/// Select a maximal subset of verified involutions with PAIRWISE DISJOINT
/// variable support, so their single-clause SBPs (from [`encode_involution_sbp`])
/// compose soundly (#17).
///
/// Soundness of composition: for disjoint-support involution automorphisms,
/// fixing clause `c_i` by applying `π_i` never disturbs any `c_j` (j≠i), because
/// `c_j`'s variables lie in `π_j`'s support, disjoint from `π_i`'s. So greedily
/// applying each `π_i` to a model yields a model satisfying every `c_i` — hence
/// `F` is SAT iff `F ∧ ⋀ c_i` is SAT. Mixing with the single-swap orbit SBP is
/// NOT done (their supports may overlap); the composite path stands alone.
#[allow(dead_code)] // #17 integration helper; wired with the preprocess hook.
fn select_disjoint_support_involutions(
    perms: Vec<BTreeMap<Variable, Variable>>,
) -> Vec<BTreeMap<Variable, Variable>> {
    let mut used: std::collections::BTreeSet<Variable> = std::collections::BTreeSet::new();
    let mut selected = Vec::new();
    for perm in perms {
        if perm.keys().all(|v| !used.contains(v)) {
            used.extend(perm.keys().copied());
            selected.push(perm);
        }
    }
    selected
}

/// Enumerate sign-preserving bijections from `free` literals to `remaining`
/// literals (each free literal maps to a remaining literal of the SAME sign).
/// Returns the variable-pair assignments. Clauses are short, so this is cheap.
fn sign_preserving_matchings(
    free: &[Literal],
    remaining: &[Literal],
) -> Vec<Vec<(Variable, Variable)>> {
    fn rec(
        k: usize,
        free: &[Literal],
        remaining: &[Literal],
        used: &mut [bool],
        current: &mut Vec<(Variable, Variable)>,
        out: &mut Vec<Vec<(Variable, Variable)>>,
    ) {
        if k == free.len() {
            out.push(current.clone());
            return;
        }
        let fl = free[k];
        for (idx, rl) in remaining.iter().enumerate() {
            if used[idx] || fl.is_positive() != rl.is_positive() {
                continue;
            }
            used[idx] = true;
            current.push((fl.variable(), rl.variable()));
            rec(k + 1, free, remaining, used, current, out);
            current.pop();
            used[idx] = false;
        }
    }
    if free.len() != remaining.len() {
        return Vec::new();
    }
    let mut out = Vec::new();
    let mut used = vec![false; remaining.len()];
    let mut current = Vec::new();
    rec(0, free, remaining, &mut used, &mut current, &mut out);
    out
}

/// Backtracking closure: extend the partial involution `perm` to a full formula
/// automorphism by repeatedly repairing a "broken" clause (whose image under
/// `perm` is not a formula clause), branching over the consistent extensions.
/// Returns true if a closed (consistent) extension is reached. The caller
/// gate-verifies the result, so search bugs can only cause a MISS, never an
/// unsound permutation. Bounded by `budget` nodes.
#[allow(clippy::too_many_arguments)]
fn close_involution(
    perm: &mut BTreeMap<Variable, Variable>,
    clauses: &[Vec<Literal>],
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    occ: &BTreeMap<Variable, Vec<usize>>,
    by_len: &BTreeMap<usize, Vec<Vec<u32>>>,
    nodes: &mut u64,
    budget: u64,
) -> bool {
    *nodes += 1;
    if *nodes > budget {
        return false;
    }
    // Find a broken clause among those touching a mapped variable.
    let mut broken: Option<usize> = None;
    'find: for v in perm.keys() {
        if let Some(cis) = occ.get(v) {
            for &ci in cis {
                let raws: Vec<u32> = clauses[ci].iter().map(|l| l.raw()).collect();
                let img = permute_clause_key(&raws, perm);
                if !formula_counts.contains_key(&img) {
                    broken = Some(ci);
                    break 'find;
                }
            }
        }
    }
    let Some(ci) = broken else {
        return true; // no broken clause touching the support: consistent
    };
    let c = &clauses[ci];

    // Split into the already-determined image literals and the free literals.
    let mut img_fixed: Vec<u32> = Vec::new();
    let mut free: Vec<Literal> = Vec::new();
    for l in c {
        if let Some(&iv) = perm.get(&l.variable()) {
            let il = if l.is_positive() {
                Literal::positive(iv)
            } else {
                Literal::negative(iv)
            };
            img_fixed.push(il.raw());
        } else {
            free.push(*l);
        }
    }
    img_fixed.sort_unstable();

    // Candidate formula clauses of the same length that contain img_fixed; the
    // remaining literals are matched (sign-preserving) to the free literals.
    let empty = Vec::new();
    for cand in by_len.get(&c.len()).unwrap_or(&empty) {
        // multiset: cand must contain all of img_fixed; remaining = cand \ img_fixed.
        let mut remaining_raw = cand.clone();
        let mut ok = true;
        for &r in &img_fixed {
            if let Some(pos) = remaining_raw.iter().position(|&x| x == r) {
                remaining_raw.swap_remove(pos);
            } else {
                ok = false;
                break;
            }
        }
        if !ok || remaining_raw.len() != free.len() {
            continue;
        }
        let remaining: Vec<Literal> = remaining_raw.iter().map(|&r| Literal(r)).collect();

        for assignment in sign_preserving_matchings(&free, &remaining) {
            // Apply the forced swaps if consistent with the current partial perm.
            let mut added: Vec<(Variable, Variable)> = Vec::new();
            let mut consistent = true;
            for (u, up) in &assignment {
                if u == up {
                    continue; // fixed point
                }
                match (perm.get(u), perm.get(up)) {
                    (None, None) => added.push((*u, *up)),
                    (Some(&x), _) if x == *up => {}
                    (_, Some(&y)) if y == *u => {}
                    _ => {
                        consistent = false;
                        break;
                    }
                }
            }
            if !consistent {
                continue;
            }
            for (u, up) in &added {
                perm.insert(*u, *up);
                perm.insert(*up, *u);
            }
            if close_involution(perm, clauses, formula_counts, occ, by_len, nodes, budget) {
                return true;
            }
            for (u, up) in &added {
                perm.remove(u);
                perm.remove(up);
            }
        }
    }
    false
}

/// Find composite-permutation symmetries via BACKTRACKING automorphism search
/// (#17): seed an involution from a refined-class pair and extend it to a full
/// formula automorphism by closure with backtracking over ambiguous clause
/// matches. Each result is gate-verified, so it is sound by construction. This
/// replaces the naive consecutive/half-split enumerator, which could not find
/// symmetries on arbitrary variable layouts (e.g. sanitized cliques).
#[allow(dead_code)] // wired via detect_and_encode_composite.
fn find_composite_symmetries_backtracking(
    clauses: &[Vec<Literal>],
    formula_counts: &BTreeMap<Vec<u32>, u32>,
    refined_groups: &[Vec<Variable>],
    max_seeds: usize,
    node_budget: u64,
) -> Vec<BTreeMap<Variable, Variable>> {
    let mut occ: BTreeMap<Variable, Vec<usize>> = BTreeMap::new();
    for (ci, c) in clauses.iter().enumerate() {
        for l in c {
            occ.entry(l.variable()).or_default().push(ci);
        }
    }
    let mut by_len: BTreeMap<usize, Vec<Vec<u32>>> = BTreeMap::new();
    for key in formula_counts.keys() {
        by_len.entry(key.len()).or_default().push(key.clone());
    }

    let mut found: Vec<BTreeMap<Variable, Variable>> = Vec::new();

    // ORBIT-AWARE SEEDING. On vertex+color-transitive formulas (clique/coloring),
    // refinement collapses all variables into one huge class, so blind O(n^2)
    // pair seeding wastes the node budget on arbitrary far-apart pairs. Instead
    // prioritize pairs that CO-OCCUR in a clause and share a refined group: those
    // are the structural automorphism candidates (e.g. the color variables of one
    // vertex sharing an at-most-one clause are exactly a color-swap transposition).
    // Shortest clauses first. Falls back to remaining same-group pairs so that
    // symmetries whose moved variables never co-occur are still reachable. Every
    // candidate is still gate-verified below, so this only changes WHICH seeds are
    // tried, never soundness.
    let mut group_of: BTreeMap<Variable, usize> = BTreeMap::new();
    for (gi, group) in refined_groups.iter().enumerate() {
        for &v in group {
            group_of.insert(v, gi);
        }
    }
    let pair_cap = max_seeds.saturating_mul(8).max(64);
    let mut seen_pairs: std::collections::BTreeSet<(Variable, Variable)> = Default::default();
    let mut ordered_pairs: Vec<(Variable, Variable)> = Vec::new();
    let mut clause_order: Vec<usize> = (0..clauses.len()).collect();
    clause_order.sort_by_key(|&ci| clauses[ci].len());
    'cooccur: for &ci in &clause_order {
        let c = &clauses[ci];
        for a_idx in 0..c.len() {
            for b_idx in (a_idx + 1)..c.len() {
                let (mut a, mut b) = (c[a_idx].variable(), c[b_idx].variable());
                if a == b {
                    continue;
                }
                if a > b {
                    std::mem::swap(&mut a, &mut b);
                }
                match (group_of.get(&a), group_of.get(&b)) {
                    (Some(ga), Some(gb)) if ga == gb => {}
                    _ => continue,
                }
                if seen_pairs.insert((a, b)) {
                    ordered_pairs.push((a, b));
                    if ordered_pairs.len() >= pair_cap {
                        break 'cooccur;
                    }
                }
            }
        }
    }
    // Fallback: remaining same-group pairs, up to the cap.
    'fallback: for group in refined_groups {
        for i in 0..group.len() {
            for j in (i + 1)..group.len() {
                if ordered_pairs.len() >= pair_cap {
                    break 'fallback;
                }
                let (a, b) = (group[i], group[j]);
                let pair = if a <= b { (a, b) } else { (b, a) };
                if seen_pairs.insert(pair) {
                    ordered_pairs.push(pair);
                }
            }
        }
    }

    for (a, b) in ordered_pairs.into_iter().take(max_seeds) {
        let mut perm = BTreeMap::new();
        perm.insert(a, b);
        perm.insert(b, a);
        let mut nodes = 0u64;
        if close_involution(
            &mut perm,
            clauses,
            formula_counts,
            &occ,
            &by_len,
            &mut nodes,
            node_budget,
        ) && perm.len() >= 2
            && permutation_preserves_formula(formula_counts, &perm)
            && !found.contains(&perm)
        {
            found.push(perm);
        }
    }
    found
}

/// Deduplicate SBP clauses against existing formula clauses.
pub(crate) fn deduplicate_sbp_clauses(
    sbp_clauses: Vec<Vec<Literal>>,
    existing: &BTreeMap<Vec<u32>, u32>,
) -> Vec<Vec<Literal>> {
    sbp_clauses
        .into_iter()
        .filter(|clause| {
            let key = canonical_clause_key(clause);
            !existing.contains_key(&key)
        })
        .collect()
}

#[cfg(test)]
#[path = "detector_interrupt_tests.rs"]
mod interrupt_tests;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{Literal, Variable};

    /// The witness-threading encoder must emit byte-for-byte the SAME clauses as
    /// the base encoder (same literals, same aux allocation), and the σ-image PR
    /// witness on the aux-free `j=0` clause must satisfy that clause and contain
    /// only support variables.
    #[test]
    fn test_encode_perm_lex_leader_witness_matches_base_and_witness_is_sound() {
        // A clean 3-cycle automorphism σ = (0 1 2) on variables {0,1,2}.
        let mut perm: BTreeMap<Variable, Variable> = BTreeMap::new();
        perm.insert(Variable(0), Variable(1));
        perm.insert(Variable(1), Variable(2));
        perm.insert(Variable(2), Variable(0));
        let fresh_base = 10u32;

        let (base_clauses, base_aux) = encode_perm_lex_leader(&perm, fresh_base);
        let (tagged, tagged_aux) = encode_perm_lex_leader_with_witness(&perm, fresh_base);

        assert_eq!(
            base_aux, tagged_aux,
            "aux allocation must match base encoder"
        );
        let tagged_clauses: Vec<Vec<Literal>> = tagged
            .iter()
            .map(|t| match t {
                LexClause::Pr { clause, .. } => clause.clone(),
                LexClause::Aux { clause } => clause.clone(),
                LexClause::Sr { clause, .. } => clause.clone(),
            })
            .collect();
        assert_eq!(
            base_clauses, tagged_clauses,
            "witness encoder must emit identical clauses to the base encoder"
        );

        // Exactly the j=0 clause is PR-certifiable; the rest carry aux.
        let pr: Vec<&LexClause> = tagged
            .iter()
            .filter(|t| matches!(t, LexClause::Pr { .. }))
            .collect();
        assert_eq!(
            pr.len(),
            1,
            "only the aux-free j=0 lex clause is PR-certifiable"
        );

        if let LexClause::Pr { clause, witness } = pr[0] {
            // j=0: support sorted ascending → w_0 = var 0, σ⁻¹(0)=2 → C=(x0 ∨ ¬x2).
            assert_eq!(
                clause,
                &vec![
                    Literal::positive(Variable(0)),
                    Literal::negative(Variable(2))
                ]
            );
            // w = σ(¬C) = {x0, ¬x_{σ(0)}} = {x0, ¬x1}.
            assert_eq!(
                witness,
                &vec![
                    Literal::positive(Variable(0)),
                    Literal::negative(Variable(1))
                ]
            );
            // Witness satisfies the clause via the shared pivot x0.
            assert!(clause.iter().any(|c| witness.contains(c)));
        } else {
            unreachable!();
        }
    }

    /// The #17 verification gate must accept a COMPOSITE permutation symmetry
    /// (the kind clique/coloring/PHP instances have) and REJECT the single swaps
    /// the current detector is limited to — which is exactly why the current
    /// detector finds no symmetry on those instances.
    #[test]
    fn test_permutation_preserves_formula_accepts_composite_rejects_single() {
        // 2-vertex edge, 2 colors. Vars 0,1 = vertex0's two color vars;
        // 2,3 = vertex1's. Clauses: each vertex gets a color (at-least-one), at
        // most one color, and the edge forbids the two endpoints sharing a color.
        let lit = |i: u32, pos: bool| {
            if pos {
                Literal::positive(Variable(i))
            } else {
                Literal::negative(Variable(i))
            }
        };
        let clauses: Vec<Vec<Literal>> = vec![
            vec![lit(0, true), lit(1, true)],   // vertex0 gets a color
            vec![lit(2, true), lit(3, true)],   // vertex1 gets a color
            vec![lit(0, false), lit(1, false)], // vertex0: at most one color
            vec![lit(2, false), lit(3, false)], // vertex1: at most one color
            vec![lit(0, false), lit(2, false)], // edge: not both color0
            vec![lit(1, false), lit(3, false)], // edge: not both color1
        ];
        let counts = build_formula_counts(&clauses);

        // COMPOSITE color swap (color0<->color1 across BOTH vertices): 0<->1, 2<->3.
        // This is a genuine formula automorphism.
        let mut color_swap = BTreeMap::new();
        for (a, b) in [(0u32, 1u32), (1, 0), (2, 3), (3, 2)] {
            color_swap.insert(Variable(a), Variable(b));
        }
        assert!(
            permutation_preserves_formula(&counts, &color_swap),
            "composite color-swap must be accepted as a formula automorphism"
        );

        // A SINGLE swap of just vertex0's colors (0<->1) is NOT a symmetry: the
        // edge clause (¬0 ∨ ¬2) maps to (¬1 ∨ ¬2), which is not in the formula.
        // This is precisely the symmetry the current single-swap detector cannot
        // find — confirming the gate's value for #17.
        let mut single = BTreeMap::new();
        single.insert(Variable(0), Variable(1));
        single.insert(Variable(1), Variable(0));
        assert!(
            !permutation_preserves_formula(&counts, &single),
            "a single swap must be rejected — clique/coloring symmetry is composite"
        );
    }

    /// Build the 2-vertex/2-color clique-coloring formula (shared by the
    /// composite-symmetry tests). Vars 0,1 = vertex0's color vars; 2,3 = vertex1's.
    fn clique_coloring_2v2c() -> Vec<Vec<Literal>> {
        let lit = |i: u32, pos: bool| {
            if pos {
                Literal::positive(Variable(i))
            } else {
                Literal::negative(Variable(i))
            }
        };
        vec![
            vec![lit(0, true), lit(1, true)],
            vec![lit(2, true), lit(3, true)],
            vec![lit(0, false), lit(1, false)],
            vec![lit(2, false), lit(3, false)],
            vec![lit(0, false), lit(2, false)],
            vec![lit(1, false), lit(3, false)],
        ]
    }

    /// The #17 finder must DISCOVER composite symmetries (gate-verified) that the
    /// single-swap detector misses. On this clique-coloring formula the color
    /// swap (0<->1, 2<->3) is a genuine automorphism the finder should return.
    #[test]
    fn test_find_composite_symmetries_discovers_color_swap() {
        let counts = build_formula_counts(&clique_coloring_2v2c());
        // For this symmetric formula all four color variables share one refined
        // class; pass it directly to exercise the enumerator + gate.
        let refined = vec![vec![Variable(0), Variable(1), Variable(2), Variable(3)]];
        let syms = find_composite_symmetries(&counts, &refined, 16);
        assert!(
            !syms.is_empty(),
            "finder must discover at least one gate-verified composite symmetry"
        );
        let color_swap: BTreeMap<Variable, Variable> = [(0, 1), (1, 0), (2, 3), (3, 2)]
            .into_iter()
            .map(|(a, b)| (Variable(a), Variable(b)))
            .collect();
        assert!(
            syms.contains(&color_swap),
            "the composite color swap (0<->1,2<->3) must be among the discovered symmetries"
        );
    }

    /// The #17 SBP encoder must be SOUND (keep a real model of the formula) and
    /// EFFECTIVE (remove the symmetric duplicate) — validated on actual models.
    #[test]
    fn test_encode_involution_sbp_sound_and_breaks_symmetry() {
        let clauses = clique_coloring_2v2c();
        let color_swap: BTreeMap<Variable, Variable> = [(0, 1), (1, 0), (2, 3), (3, 2)]
            .into_iter()
            .map(|(a, b)| (Variable(a), Variable(b)))
            .collect();
        let sbp = encode_involution_sbp(&color_swap).expect("involution has a moved pair");
        assert_eq!(
            sbp,
            vec![
                Literal::positive(Variable(0)),
                Literal::negative(Variable(1))
            ],
            "SBP is the smallest-moved-pair binary clause (x0 ∨ ¬x1)"
        );

        // m1: vertex0=color0, vertex1=color1.  m2: its color-swap image.
        let model = |pairs: [(u32, bool); 4]| -> BTreeMap<Variable, bool> {
            pairs.into_iter().map(|(v, b)| (Variable(v), b)).collect()
        };
        let m1 = model([(0, true), (1, false), (2, false), (3, true)]);
        let m2 = model([(0, false), (1, true), (2, true), (3, false)]);
        let sat = |m: &BTreeMap<Variable, bool>, clause: &[Literal]| {
            clause.iter().any(|l| {
                let val = m[&l.variable()];
                if l.is_positive() {
                    val
                } else {
                    !val
                }
            })
        };

        // Both are genuine symmetric models of the formula.
        for m in [&m1, &m2] {
            assert!(
                clauses.iter().all(|c| sat(m, c)),
                "both color-swapped assignments must satisfy the formula"
            );
        }
        // SOUND: the SBP keeps a real model.
        assert!(
            sat(&m1, &sbp),
            "SBP must keep a real model of the formula (sound)"
        );
        // EFFECTIVE: the SBP removes the symmetric duplicate.
        assert!(
            !sat(&m2, &sbp),
            "SBP must break the symmetric duplicate assignment"
        );
    }

    /// Disjoint-support selection keeps non-overlapping involutions (sound to
    /// compose) and drops overlapping ones.
    #[test]
    fn test_select_disjoint_support_involutions() {
        let inv = |pairs: &[(u32, u32)]| -> BTreeMap<Variable, Variable> {
            let mut m = BTreeMap::new();
            for &(a, b) in pairs {
                m.insert(Variable(a), Variable(b));
                m.insert(Variable(b), Variable(a));
            }
            m
        };
        // p1 support {0,1,2,3}; p2 support {4,5} (disjoint); p3 support {2,6}
        // (overlaps p1 on var 2).
        let p1 = inv(&[(0, 1), (2, 3)]);
        let p2 = inv(&[(4, 5)]);
        let p3 = inv(&[(2, 6)]);
        let selected = select_disjoint_support_involutions(vec![p1.clone(), p2.clone(), p3]);
        assert_eq!(selected.len(), 2, "p3 overlaps p1, must be dropped");
        assert!(selected.contains(&p1));
        assert!(selected.contains(&p2));
        // The two kept SBPs are on disjoint variables -> sound to add together.
        let supports: Vec<_> = selected
            .iter()
            .map(|p| p.keys().copied().collect::<std::collections::BTreeSet<_>>())
            .collect();
        assert!(
            supports[0].is_disjoint(&supports[1]),
            "selected involutions must have disjoint support"
        );
    }

    /// The backtracking finder must discover the composite color-swap by closure
    /// (seed 0<->1 forces 2<->3 via the edge clause) — and every result is a
    /// gate-verified automorphism (sound).
    #[test]
    fn test_backtracking_finder_discovers_color_swap() {
        let clauses = clique_coloring_2v2c();
        let counts = build_formula_counts(&clauses);
        let groups = vec![vec![Variable(0), Variable(1), Variable(2), Variable(3)]];
        let syms = find_composite_symmetries_backtracking(&clauses, &counts, &groups, 16, 10_000);
        assert!(
            !syms.is_empty(),
            "backtracking finder must discover a composite symmetry by closure"
        );
        for p in &syms {
            assert!(
                permutation_preserves_formula(&counts, p),
                "every discovered permutation must be a genuine automorphism (sound)"
            );
        }
        let color_swap: BTreeMap<Variable, Variable> = [(0, 1), (1, 0), (2, 3), (3, 2)]
            .into_iter()
            .map(|(a, b)| (Variable(a), Variable(b)))
            .collect();
        assert!(
            syms.contains(&color_swap),
            "the color swap must be reachable by closure from seed 0<->1"
        );
    }

    /// Build a 3-color / 2-vertex clique-coloring formula (an EDGE, so a single
    /// vertex's colors are NOT interchangeable, but the three COLORS are — an
    /// `S_3` row symmetry). Vars: vertex0 colors = 0,1,2; vertex1 colors = 3,4,5.
    /// Color `c` = row {x_{v0,c}, x_{v1,c}}.
    fn clique_coloring_2v3c() -> Vec<Vec<Literal>> {
        let lit = |i: u32, pos: bool| {
            if pos {
                Literal::positive(Variable(i))
            } else {
                Literal::negative(Variable(i))
            }
        };
        vec![
            // at-least-one color per vertex
            vec![lit(0, true), lit(1, true), lit(2, true)],
            vec![lit(3, true), lit(4, true), lit(5, true)],
            // at-most-one color, vertex0
            vec![lit(0, false), lit(1, false)],
            vec![lit(0, false), lit(2, false)],
            vec![lit(1, false), lit(2, false)],
            // at-most-one color, vertex1
            vec![lit(3, false), lit(4, false)],
            vec![lit(3, false), lit(5, false)],
            vec![lit(4, false), lit(5, false)],
            // edge: endpoints must differ in every color
            vec![lit(0, false), lit(3, false)],
            vec![lit(1, false), lit(4, false)],
            vec![lit(2, false), lit(5, false)],
        ]
    }

    /// The three color-swap involutions of [`clique_coloring_2v3c`].
    fn color_swaps_2v3c() -> Vec<BTreeMap<Variable, Variable>> {
        let inv = |a: u32, b: u32, c: u32, d: u32| -> BTreeMap<Variable, Variable> {
            let mut m = BTreeMap::new();
            m.insert(Variable(a), Variable(b));
            m.insert(Variable(b), Variable(a));
            m.insert(Variable(c), Variable(d));
            m.insert(Variable(d), Variable(c));
            m
        };
        vec![
            inv(0, 1, 3, 4), // color0 <-> color1
            inv(0, 2, 3, 5), // color0 <-> color2
            inv(1, 2, 4, 5), // color1 <-> color2
        ]
    }

    /// (a) Row detection must recover the three COLOR rows {0,3},{1,4},{2,5}
    /// (column-aligned by vertex) from the color-swap involutions.
    #[test]
    fn test_detect_row_interchangeability_finds_color_rows() {
        let perms = color_swaps_2v3c();
        let row_sets = detect_row_interchangeability(&perms);
        assert_eq!(row_sets.len(), 1, "exactly one interchangeable row-set");
        let rs = &row_sets[0];
        assert_eq!(rs.rows.len(), 3, "three interchangeable color rows");
        // Each row has one variable per column (2 vertices).
        for r in &rs.rows {
            assert_eq!(r.len(), 2);
        }
        // Rows are the color classes, sorted by their column-0 (vertex0) variable.
        assert_eq!(
            rs.rows,
            vec![
                vec![Variable(0), Variable(3)],
                vec![Variable(1), Variable(4)],
                vec![Variable(2), Variable(5)],
            ],
            "rows are the three color classes, column-aligned by vertex"
        );
    }

    /// The backtracking finder + row detection on the actual formula must find
    /// the color rows end-to-end (not just from hand-built involutions).
    #[test]
    fn test_row_detection_end_to_end_on_formula() {
        let clauses = clique_coloring_2v3c();
        let counts = build_formula_counts(&clauses);
        let refined: Vec<Vec<Variable>> = vec![(0u32..6).map(Variable).collect()];
        let perms = find_composite_symmetries_backtracking(&clauses, &counts, &refined, 64, 50_000);
        let row_sets = detect_row_interchangeability(&perms);
        assert!(
            row_sets.iter().any(|rs| rs.rows.len() >= 3),
            "finder + detection must discover a >=3-row interchangeable set"
        );
    }

    /// (b) SOUNDNESS + EFFECTIVENESS of the chained lex-leader: it must KEEP the
    /// lex-max (sorted) representative of an orbit and REMOVE a symmetric
    /// duplicate, with all aux variables consistently satisfiable.
    #[test]
    fn test_rowset_lex_leader_sound_and_breaks_symmetry() {
        // Rows aligned by vertex (column0 = vertex0, column1 = vertex1):
        //   R0 = {0,3}, R1 = {1,4}, R2 = {2,5}.
        let rowset = RowSet {
            rows: vec![
                vec![Variable(0), Variable(3)],
                vec![Variable(1), Variable(4)],
                vec![Variable(2), Variable(5)],
            ],
        };
        let fresh_base = 6u32;
        let (sbp, aux) = encode_rowset_lex_leader(&rowset, fresh_base);
        assert!(!sbp.is_empty(), "must emit lex-leader clauses");
        // (k-1) pairs * (n-1) aux each = 2 * 1 = 2 aux equal-prefix vars.
        assert_eq!(aux, 2, "two consecutive pairs, one column-gap each");

        let formula = clique_coloring_2v3c();

        // A satisfying assignment of the formula: vertex0=color0, vertex1=color1.
        //   x0=1,x1=0,x2=0 (v0), x3=0,x4=1,x5=0 (v1).
        // Row value vectors (col0=v0,col1=v1): R0=(1,0), R1=(0,1), R2=(0,0).
        // Sorted lex-decreasing: R0=(1,0) >= R1=(0,1) >= R2=(0,0). This IS the
        // leader, so it must survive the chain.
        let leader = [true, false, false, false, true, false];
        // A symmetric duplicate (swap color0<->color1): vertex0=color1,vertex1=color0
        //   x0=0,x1=1,x2=0, x3=1,x4=0,x5=0 -> rows R0=(0,1),R1=(1,0),R2=(0,0):
        // R0 < R1 lexicographically, so the chain R0>=R1 must REJECT it.
        let dup = [false, true, false, true, false, false];

        let sat_under = |base: &[bool], aux_vals: &[bool], clause: &[Literal]| -> bool {
            clause.iter().any(|l| {
                let v = l.variable().0 as usize;
                let val = if v < base.len() {
                    base[v]
                } else {
                    aux_vals[v - fresh_base as usize]
                };
                if l.is_positive() {
                    val
                } else {
                    !val
                }
            })
        };

        // Both base assignments satisfy the original formula (genuine models).
        for m in [&leader, &dup] {
            assert!(
                formula.iter().all(|c| sat_under(m, &[], c)),
                "both color-permuted assignments must satisfy the formula"
            );
        }

        // SOUNDNESS: the leader is preserved — there EXISTS an aux assignment
        // making every SBP clause true. Use the forced (iff) aux values.
        //   pair (R0,R1): e between col0,col1 = (x0 == x1) = (1==0) = false.
        //   pair (R1,R2): e = (x1 == x2) = (0==0) = true.
        let leader_aux = [false, true]; // [e(R0,R1), e(R1,R2)]
        assert!(
            sbp.iter().all(|c| sat_under(&leader, &leader_aux, c)),
            "SBP must keep the lex-max representative (sound)"
        );

        // EFFECTIVENESS: the duplicate is removed under EVERY aux assignment
        // (no extension satisfies the chain), so it cannot survive.
        for a0 in [false, true] {
            for a1 in [false, true] {
                let dup_aux = [a0, a1];
                assert!(
                    !sbp.iter().all(|c| sat_under(&dup, &dup_aux, c)),
                    "SBP must reject the symmetric duplicate for every aux assignment"
                );
            }
        }
    }

    /// The chained lex-leader clauses must reference only the row variables and
    /// the freshly allocated aux variables (no stray ids), and aux ids must be
    /// contiguous from `fresh_base`.
    #[test]
    fn test_rowset_lex_leader_aux_var_range() {
        let rowset = RowSet {
            rows: vec![
                vec![Variable(0), Variable(3)],
                vec![Variable(1), Variable(4)],
                vec![Variable(2), Variable(5)],
            ],
        };
        let fresh_base = 6u32;
        let (sbp, aux) = encode_rowset_lex_leader(&rowset, fresh_base);
        for clause in &sbp {
            for l in clause {
                let v = l.variable().0;
                assert!(
                    v < 6 || (fresh_base..fresh_base + aux).contains(&v),
                    "clause var {v} must be a row var or a fresh aux in range"
                );
            }
        }
    }

    #[test]
    fn test_detector_symmetric_pigeonhole_fragment() {
        // Minimal pigeonhole-like symmetric formula:
        // x0 and x1 are interchangeable, x2 and x3 are interchangeable.
        let x0 = Variable(0);
        let x1 = Variable(1);
        let x2 = Variable(2);
        let x3 = Variable(3);
        let z = Variable(4);

        let clauses = vec![
            // x0 <-> x1 symmetry group
            vec![Literal::positive(x0), Literal::positive(z)],
            vec![Literal::positive(x1), Literal::positive(z)],
            vec![Literal::negative(x0), Literal::negative(z)],
            vec![Literal::negative(x1), Literal::negative(z)],
            // x2 <-> x3 symmetry group (separate from x0,x1)
            vec![Literal::positive(x2), Literal::negative(z)],
            vec![Literal::positive(x3), Literal::negative(z)],
            vec![Literal::negative(x2), Literal::positive(z)],
            vec![Literal::negative(x3), Literal::positive(z)],
        ];

        let detector = SymmetryDetector::new(128, 64);
        let (sbp_clauses, stats) = detector.detect_and_encode(&clauses);

        // Should detect symmetries and emit SBP clauses.
        assert!(
            stats.refinement_rounds > 0,
            "should have performed refinement"
        );
        // At minimum, x0<->x1 and x2<->x3 should be detected.
        assert!(
            stats.pairs_detected >= 2,
            "expected at least 2 swap pairs, got {}",
            stats.pairs_detected
        );
        assert!(
            !sbp_clauses.is_empty(),
            "expected SBP clauses to be generated"
        );

        // All generated clauses should be binary (lex-leader encoding).
        for clause in &sbp_clauses {
            assert_eq!(clause.len(), 2, "lex-leader SBP clauses should be binary");
        }
    }

    #[test]
    fn test_detector_no_symmetry() {
        // Asymmetric formula: x0 and x1 have different occurrence patterns.
        let x0 = Variable(0);
        let x1 = Variable(1);
        let clauses = vec![
            vec![Literal::positive(x0)],
            vec![Literal::positive(x0), Literal::positive(x1)],
        ];

        let detector = SymmetryDetector::new(128, 64);
        let (sbp_clauses, stats) = detector.detect_and_encode(&clauses);

        assert!(
            sbp_clauses.is_empty(),
            "asymmetric formula should produce no SBP"
        );
        assert_eq!(stats.pairs_detected, 0);
    }

    #[test]
    fn test_detector_orbit_merging() {
        // Formula where x0, x1, x2 are all interchangeable: full S3 orbit.
        let x0 = Variable(0);
        let x1 = Variable(1);
        let x2 = Variable(2);
        let z = Variable(3);

        let clauses = vec![
            vec![Literal::positive(x0), Literal::positive(z)],
            vec![Literal::positive(x1), Literal::positive(z)],
            vec![Literal::positive(x2), Literal::positive(z)],
            vec![Literal::negative(x0), Literal::negative(z)],
            vec![Literal::negative(x1), Literal::negative(z)],
            vec![Literal::negative(x2), Literal::negative(z)],
        ];

        let detector = SymmetryDetector::new(128, 64);
        let (sbp_clauses, stats) = detector.detect_and_encode(&clauses);

        // All three swaps (0,1), (0,2), (1,2) should be detected.
        assert_eq!(stats.pairs_detected, 3, "S3 has 3 transpositions");
        // Single orbit of size 3 -> 2 lex-leader clauses.
        assert_eq!(stats.orbits_detected, 1, "should detect 1 orbit");
        assert_eq!(sbp_clauses.len(), 2, "orbit of size 3 needs 2 SBP clauses");
    }

    /// A complete, bounded replacement for the former file-emitting DRAT probe.
    ///
    /// The single positive clause has the verified swap `(x0 x1)` as an
    /// automorphism. Its full lex-leader tower includes both a genuine
    /// symmetry-breaking clause and fresh equal-prefix definitions. Feed every
    /// generated addition directly through the native checker and require at
    /// least one RAT check. `NoEmptyClause` is the expected conclusion because
    /// this is an addition-fragment check, not a refutation.
    #[test]
    fn test_sbp_tower_additions_are_drat_rat() {
        use ay_drat_check::checker::DratChecker;
        use ay_drat_check::{ConcludeFailure, ConcludeResult};

        let clauses = vec![vec![
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
        ]];
        let existing = build_formula_counts(&clauses);
        let mut swap = BTreeMap::new();
        swap.insert(Variable(0), Variable(1));
        swap.insert(Variable(1), Variable(0));
        assert!(
            permutation_preserves_formula(&existing, &swap),
            "the hand-built swap must pass the same automorphism gate as IR"
        );

        let fresh_base = 2;
        let (sbp, aux) = encode_perm_lex_leader(&swap, fresh_base);
        let unique = deduplicate_sbp_clauses(sbp, &existing);
        assert!(!unique.is_empty(), "the swap must emit an SBP tower");
        assert!(aux > 0, "the full tower must exercise fresh aux clauses");

        let to_checker_clause = |clause: &[Literal]| {
            clause
                .iter()
                .map(|lit| ay_drat_check::literal::Literal::from_index(lit.index()))
                .collect::<Vec<_>>()
        };
        let mut checker = DratChecker::new((fresh_base + aux) as usize, true);
        for clause in &clauses {
            checker.add_original(&to_checker_clause(clause));
        }
        for clause in &unique {
            checker
                .add_derived(&to_checker_clause(clause))
                .unwrap_or_else(|error| panic!("SBP addition {clause:?} is not DRAT: {error}"));
        }

        assert_eq!(checker.stats().failures, 0);
        assert!(
            checker.stats().rat_checks > 0,
            "the bounded probe must exercise the RAT path, not only RUP"
        );
        assert_eq!(
            checker.conclude_unsat(),
            ConcludeResult::Failed(ConcludeFailure::NoEmptyClause)
        );
    }

    /// Build a pure pigeonhole CNF `PHP(P=H+1, H)` over 0-indexed variables
    /// `var(pigeon, hole) = pigeon * H + hole`: an all-positive ALO clause per
    /// pigeon and an all-negative AMO binary per (hole, pigeon-pair).
    fn php_clauses(holes: usize) -> Vec<Vec<Literal>> {
        let pigeons = holes + 1;
        let v = |p: usize, h: usize| Variable((p * holes + h) as u32);
        let mut clauses = Vec::new();
        for p in 0..pigeons {
            clauses.push((0..holes).map(|h| Literal::positive(v(p, h))).collect());
        }
        for h in 0..holes {
            for p1 in 0..pigeons {
                for p2 in (p1 + 1)..pigeons {
                    clauses.push(vec![
                        Literal::negative(v(p1, h)),
                        Literal::negative(v(p2, h)),
                    ]);
                }
            }
        }
        clauses
    }

    /// The aux-free SR refutation port (php-sr.c) must: emit the exact tower of SR
    /// steps over ORIGINAL variables only (no aux), with each step's DSR witness
    /// beginning by repeating the clause pivot; and reproduce php-sr.c's first
    /// line verbatim for the smallest non-trivial PHP instance.
    #[test]
    fn test_php_aux_free_sr_matches_reference_structure() {
        // PHP(3,2): pigeons {0,1,2}, holes {0,1}; vars V0..V5 (0-indexed).
        // M[0]=[V0,V1], M[1]=[V2,V3], M[2]=[V4,V5] after min-var ordering.
        let clauses = php_clauses(2);
        let steps = detect_php_aux_free_sr(&clauses).expect("PHP(3,2) must be recognised");

        // hole 0: SR units for pigeon 2 then 1, then diagonal V0, then ¬V1.
        assert_eq!(steps.len(), 4, "two SR units + diagonal + one off-diagonal");
        for lc in &steps {
            let LexClause::Sr { clause, witness } = lc else {
                panic!("aux-free route emits only LexClause::Sr");
            };
            assert!(!clause.is_empty());
            assert_eq!(
                witness.first(),
                clause.first(),
                "DSR witness must begin by repeating the clause pivot"
            );
            // Aux-free: no variable beyond the original support (V0..V5).
            for l in clause.iter().chain(witness.iter()) {
                assert!(l.variable().0 < 6, "no aux variables may appear");
            }
        }

        // First step = (¬V4), witnessed by swap(pigeon1↔pigeon2): PR part puts
        // pigeon 1 into hole 0 (V2), substitution swaps them in hole 1 (V3↔V5).
        let LexClause::Sr { clause, witness } = &steps[0] else {
            unreachable!()
        };
        assert_eq!(clause, &vec![Literal::negative(Variable(4))]);
        assert_eq!(
            witness,
            &vec![
                Literal::negative(Variable(4)), // pivot (opens PR part)
                Literal::positive(Variable(2)), // PR: x_{pig1,hole0} = 1
                Literal::negative(Variable(4)), // pivot (separator)
                Literal::positive(Variable(3)), // σ(V3) = V5
                Literal::positive(Variable(5)),
                Literal::positive(Variable(5)), // σ(V5) = V3
                Literal::positive(Variable(3)),
            ]
        );

        // Diagonal and off-diagonal are pivot-only PR units.
        let LexClause::Sr { clause, witness } = &steps[2] else {
            unreachable!()
        };
        assert_eq!(clause, &vec![Literal::positive(Variable(0))]);
        assert_eq!(witness, &vec![Literal::positive(Variable(0))]);
    }

    /// Non-pigeonhole formulas must be rejected (return `None`) so the route is a
    /// sound no-op: a wrong P:H ratio, a stray clause, and a too-small instance.
    #[test]
    fn test_php_aux_free_sr_rejects_non_php() {
        // Right shape but wrong ratio: 2 ALO of width 2 ⇒ P=2 ≠ H+1=3.
        let two_rows = vec![
            vec![
                Literal::positive(Variable(0)),
                Literal::positive(Variable(1)),
            ],
            vec![
                Literal::positive(Variable(2)),
                Literal::positive(Variable(3)),
            ],
            vec![
                Literal::negative(Variable(0)),
                Literal::negative(Variable(2)),
            ],
            vec![
                Literal::negative(Variable(1)),
                Literal::negative(Variable(3)),
            ],
        ];
        assert!(detect_php_aux_free_sr(&two_rows).is_none());

        // A valid PHP(3,2) plus one stray ternary clause ⇒ not a pure matrix.
        let mut polluted = php_clauses(2);
        polluted.push(vec![
            Literal::positive(Variable(0)),
            Literal::negative(Variable(3)),
            Literal::positive(Variable(5)),
        ]);
        assert!(detect_php_aux_free_sr(&polluted).is_none());

        // Missing one AMO binary ⇒ a hole is not a complete clique.
        let mut incomplete = php_clauses(2);
        incomplete.pop();
        assert!(detect_php_aux_free_sr(&incomplete).is_none());
    }

    // ===== #8011 / T2c: native-checker boundary of GENERIC lex-leader SR =====
    //
    // FINDING (this harness reproduces it natively). AY's generic per-generator
    // lex-leader SR emits, after the aux-free `j=0` binary `(x_{w0} ∨ ¬x_{σ⁻¹w0})`,
    // a tower carrying equal-prefix aux `e_j`. The whole tower is tagged SR with
    // the automorphism σ as the substitution witness. The native `SrChecker`
    // REJECTS it at the FIRST aux clause — but NOT because of the `e_j`: the σ-SR
    // redundancy check scans every formula clause σ reduces, and the previously
    // added `j=0` binary maps under σ to its REVERSE `(x_{σw0} ∨ ¬x_{w0})`, which
    // is absent and not entailed under the candidate's assumption. So the binary,
    // once in F, is not σ-invariant and poisons every later σ-SR step. Extending
    // the witness with the induced `e_j` action cannot fix this (the rejected
    // reduct is of the e_j-FREE binary). Verified on PHP, K-coloring and clique.
    fn to_dc(l: Literal) -> ay_drat_check::literal::Literal {
        ay_drat_check::literal::Literal::from_dimacs(l.to_dimacs())
    }

    fn cyc(pairs: &[(u32, u32)]) -> BTreeMap<Variable, Variable> {
        pairs
            .iter()
            .map(|&(a, b)| (Variable(a), Variable(b)))
            .collect()
    }

    /// Run the generic lex-leader SR tower for `perm` on `f` through the native
    /// `SrChecker`; return the first failing step's error string (or `None` if it
    /// verifies modulo the missing empty clause).
    fn first_sr_rejection(
        f: &[Vec<Literal>],
        perm: &BTreeMap<Variable, Variable>,
    ) -> Option<String> {
        use ay_drat_check::drat_parser::ProofStep;
        let max_orig = f
            .iter()
            .flat_map(|c| c.iter())
            .map(|l| l.variable().0)
            .max()
            .unwrap_or(0);
        let fresh_base = max_orig + 1;
        let (tower, aux) = encode_perm_lex_leader_sr(perm, fresh_base);
        let num_vars = (fresh_base + aux) as usize + 1;
        let dc_f: Vec<Vec<ay_drat_check::literal::Literal>> = f
            .iter()
            .map(|c| c.iter().map(|&l| to_dc(l)).collect())
            .collect();
        let steps: Vec<ProofStep> = tower
            .iter()
            .map(|lc| {
                let LexClause::Sr { clause, witness } = lc else {
                    unreachable!()
                };
                ProofStep::AddPr {
                    clause: clause.iter().map(|&l| to_dc(l)).collect(),
                    witness: witness.iter().map(|&l| to_dc(l)).collect(),
                }
            })
            .collect();
        let mut chk = ay_drat_check::SrChecker::new(num_vars, true);
        match chk.verify(&dc_f, &steps) {
            Ok(()) => None,
            Err(e) => {
                let s = e.to_string();
                // A missing-empty-clause conclusion means every SR step was accepted.
                if s.contains("NoEmptyClause") || s.to_lowercase().contains("empty") {
                    None
                } else {
                    Some(s)
                }
            }
        }
    }

    /// The generic lex-leader SR tower is NOT natively verifiable: it is rejected
    /// at the first equal-prefix aux clause, for both an involution and a 3-cycle
    /// generator (over a loose, non-RUP formula so the substitution witness is
    /// actually exercised). Documents the #8011 boundary as a native regression.
    #[test]
    fn generic_lex_leader_sr_tower_rejected_by_native_checker() {
        // Involution σ = (0 1)(2 3) over a loosely-constrained invariant formula.
        let f_inv = vec![
            vec![
                Literal::positive(Variable(0)),
                Literal::positive(Variable(1)),
                Literal::positive(Variable(2)),
                Literal::positive(Variable(3)),
            ],
            vec![
                Literal::negative(Variable(0)),
                Literal::negative(Variable(1)),
                Literal::negative(Variable(2)),
                Literal::negative(Variable(3)),
            ],
        ];
        let rej_inv = first_sr_rejection(&f_inv, &cyc(&[(0, 1), (1, 0), (2, 3), (3, 2)]))
            .expect("generic lex-leader SR tower must be rejected (involution)");
        assert!(
            rej_inv.contains("PR/SR") && rej_inv.contains("not implied"),
            "{rej_inv}"
        );

        // 3-cycle σ = (0 1 2) over F = {(0 1 2)}.
        let f_3 = vec![vec![
            Literal::positive(Variable(0)),
            Literal::positive(Variable(1)),
            Literal::positive(Variable(2)),
        ]];
        let rej_3 = first_sr_rejection(&f_3, &cyc(&[(0, 1), (1, 2), (2, 0)]))
            .expect("generic lex-leader SR tower must be rejected (3-cycle)");
        assert!(
            rej_3.contains("PR/SR") && rej_3.contains("not implied"),
            "{rej_3}"
        );
    }

    /// SOUNDNESS GATE: the native SR checker fails CLOSED — a non-satisfiability-
    /// preserving addition is rejected under any witness (never a false VERIFIED).
    /// F = {(x0)} forces x0; adding (¬x0) would make F UNSAT.
    #[test]
    fn native_sr_checker_fails_closed_on_non_redundant() {
        use ay_drat_check::drat_parser::ProofStep;
        let f = [vec![Literal::positive(Variable(0))]];
        let dc_f: Vec<_> = f
            .iter()
            .map(|c| c.iter().map(|&l| to_dc(l)).collect())
            .collect();
        let clause = [Literal::negative(Variable(0))];
        let witness = [
            Literal::negative(Variable(0)),
            Literal::negative(Variable(0)),
        ];
        let step = ProofStep::AddPr {
            clause: clause.iter().map(|&l| to_dc(l)).collect(),
            witness: witness.iter().map(|&l| to_dc(l)).collect(),
        };
        let mut chk = ay_drat_check::SrChecker::new(2, true);
        let s = chk
            .verify(&dc_f, &[step])
            .expect_err("non-redundant (¬x0) must NOT verify")
            .to_string();
        assert!(s.contains("PR/SR") || s.contains("empty clause"), "{s}");
    }
}
