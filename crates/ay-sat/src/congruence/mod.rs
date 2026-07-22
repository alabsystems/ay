// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Congruence closure for preprocessing
//!
//! Detects equivalent gate outputs by canonicalizing inputs through union-find
//! and eagerly rewriting affected gates after each merge (CaDiCaL style).
//! This closes equivalence under gate congruence and can derive UNSAT when a literal is forced equivalent to its negation (`x ≡ ¬x`).
//! Reference: CaDiCaL congruence.cpp (Biere, Faller, Fazekas, Pollitt 2024).

mod binary_analysis;
mod forward_subsumption;
mod gate_rewriting;
mod union_find;

#[cfg(test)]
mod delay_tests;
#[cfg(test)]
mod tests;

use crate::clause_arena::ClauseArena;
use crate::gates::{Gate, GateExtractor, GateType};
use crate::lit_marks::LitMarks;
use crate::literal::{Literal, Variable};
use union_find::UnionFind;

/// Cached check for the congruence debug channel.
/// Env-gated merge/unit provenance dump for soundness triage (AY_AB_SUBST_DUMP_MERGES=1).
pub(crate) fn dump_merges_enabled() -> bool {
    use std::sync::OnceLock;
    static ON: OnceLock<bool> = OnceLock::new();
    *ON.get_or_init(|| std::env::var_os("AY_AB_SUBST_DUMP_MERGES").is_some())
}

/// Structured justification for a merge edge, recorded at merge time and
/// consumed by the solver-side proof emitter (#15 T3). `Plain` edges rely on
/// the solver's direct RUP probe; `XorMatch` edges carry the shared canonical
/// XOR inputs so the emitter can build the Kissat-style matching ladder
/// (congruence.c add_xor_matching_proof_chain) that makes the equivalence
/// binaries RUP-checkable in proof mode.
#[derive(Debug, Clone, PartialEq, Eq, Default)]
pub(crate) enum EdgeProvenance {
    #[default]
    Plain,
    /// Two XOR gates with identical canonical inputs collided in the gate
    /// table; `rhs` holds the shared canonical input literal indices at
    /// collision time.
    XorMatch { rhs: Vec<usize> },
    /// Two ITE gates with identical canonical (cond, then, else) collided in
    /// the gate table; `cond` is the shared canonical condition literal
    /// index. The matching chain is the two-rung-per-direction ladder over
    /// ±cond (Kissat congruence.c:1224-1266).
    IteMatch { cond: usize },
}

fn debug_congruence_enabled() -> bool {
    ay_core::debug_channel_active(ay_core::DebugChannel::SatCongruence)
}

/// Statistics for congruence closure
#[derive(Debug, Clone, Default)]
#[non_exhaustive]
pub struct CongruenceStats {
    /// Number of gates analyzed
    pub gates_analyzed: u64,
    /// Number of equivalences found via congruence
    pub equivalences_found: u64,
    /// Number of literals rewritten
    pub literals_rewritten: u64,
    /// Number of clauses modified
    pub clauses_modified: u64,
    /// Number of rounds of congruence closure
    pub rounds: u64,
    /// ITE gates morphed to AND (CaDiCaL rewrite_ite_gate)
    pub ite_to_and: u64,
    /// ITE gates morphed to XOR (CaDiCaL rewrite_ite_gate)
    pub ite_to_xor: u64,
    /// Clauses removed by congruence-driven forward subsumption.
    pub congruence_subsumed: u64,
    /// Units rejected by RUP gate (congruence claim unsound)
    pub non_rup_contradiction_units: u64,
    /// Non-RUP units skipped
    pub non_rup_units: u64,
    /// Non-RUP equivalences skipped
    pub non_rup_equivalences: u64,
    /// XOR full-collapse units accepted without RUP because their polarity is
    /// the machine-checked-exact parity proven in the development proof harness
    /// (only counted under the default-off `AY_AB_CONGRUENCE_PARITY_TRUST` knob).
    pub parity_certified_units_applied: u64,
    /// XOR matching ladders successfully emitted for equivalence edges in
    /// DRAT proof mode (#15 T3).
    pub xor_ladders_emitted: u64,
    /// XOR-match edges skipped in DRAT proof mode because the ladder (or the
    /// post-ladder binary probe) failed — fail-closed coverage loss.
    pub xor_ladder_failures: u64,
    /// Complementary contradiction edges (x ≡ ¬x) skipped at emission.
    /// `merge_or_contradict` records the contradicting merge pair as an edge
    /// so the a ≡ … ≡ ¬a cycle is closed for the UNSAT witness unit's RUP
    /// probe, but the pair's "equivalence binaries" degenerate to the
    /// duplicate-literal units [¬x,¬x]/[x,x] and are never insertable
    /// (duplicate-watch ICE). The contradiction's proof obligation is
    /// discharged by the witness-unit path instead (wf_ff5991a1).
    pub complementary_edges_skipped: u64,
}

/// CaDiCaL-style delay state for retrying fruitless gate extraction later.
#[derive(Debug, Clone, Copy, Default)]
struct GateExtractionDelay {
    count: u32,
    current: u32,
}

impl GateExtractionDelay {
    fn delay(&mut self) -> bool {
        if self.count == 0 {
            false
        } else {
            self.count -= 1;
            true
        }
    }

    fn bump(&mut self) {
        self.current = self.current.saturating_add(1);
        self.count = self.current;
    }

    fn reduce(&mut self) {
        if self.current == 0 {
            return;
        }
        self.current /= 2;
        self.count = self.current;
    }

    fn reset(&mut self) {
        *self = Self::default();
    }
}

/// Congruence closure engine
pub(crate) struct CongruenceClosure {
    num_vars: usize,
    stats: CongruenceStats,
    /// Delay-based retry for gate extraction after fruitless runs.
    /// Unlike the old permanent cache, this eventually rechecks gate
    /// structure even when `num_vars` stays flat but clauses change.
    gate_extraction_delay: GateExtractionDelay,
    /// Cached positive occurrence lists: `var_idx → [clause_indices]`.
    /// Reused across `run()` calls to avoid O(num_vars) allocation per call.
    cached_pos_occs: Vec<Vec<usize>>,
    /// Cached negative occurrence lists: `var_idx → [clause_indices]`.
    cached_neg_occs: Vec<Vec<usize>>,
    /// Cached per-literal ternary-clause occurrence counts: `lit_index → count`.
    /// Mirrors Kissat's `largecount` (congruence.c init_ite_gate_extraction):
    /// the number of (unsatisfied, length-3) clauses each literal occurs in.
    /// Used by the ITE `twice` both-polarity pre-filter to keep candidate
    /// generation cheap on large formulas.
    cached_ternary_count: Vec<u32>,
    /// Cached binary adjacency: `lit_index → [other_lit_indices]`.
    cached_binary_adj: Vec<Vec<usize>>,
    /// Reused matchable-variable marks for equivalence-aware forward subsumption.
    forward_subsumption_matchable: Vec<bool>,
    /// Reused representative-literal marks for equivalence-aware forward subsumption.
    forward_subsumption_marked: Vec<bool>,
}

impl CongruenceClosure {
    /// Create a new congruence closure engine for n variables
    pub(crate) fn new(num_vars: usize) -> Self {
        Self {
            num_vars,
            stats: CongruenceStats::default(),
            gate_extraction_delay: GateExtractionDelay::default(),
            cached_pos_occs: Vec::new(),
            cached_neg_occs: Vec::new(),
            cached_ternary_count: Vec::new(),
            cached_binary_adj: Vec::new(),
            forward_subsumption_matchable: vec![false; num_vars],
            forward_subsumption_marked: vec![false; num_vars * 2],
        }
    }

    /// Ensure internal buffers can handle `num_vars` variables.
    pub(crate) fn ensure_num_vars(&mut self, num_vars: usize) {
        if num_vars > self.num_vars {
            self.num_vars = num_vars;
            self.forward_subsumption_matchable.resize(num_vars, false);
            self.forward_subsumption_marked.resize(num_vars * 2, false);
            // New variables (from BVE/factoring extension) could change gate
            // structure. Reset the delay so the next run re-checks immediately.
            self.gate_extraction_delay.reset();
        }
    }

    /// Get statistics
    pub(crate) fn stats(&self) -> &CongruenceStats {
        &self.stats
    }

    /// Get mutable statistics
    pub(crate) fn stats_mut(&mut self) -> &mut CongruenceStats {
        &mut self.stats
    }

    /// Restore stats after compaction (compact preserves stats across rebuild).
    pub(crate) fn restore_stats(&mut self, stats: CongruenceStats) {
        self.stats = stats;
    }

    fn record_gate_extraction_outcome(&mut self, found_equivalences: bool) {
        if found_equivalences {
            self.gate_extraction_delay.reduce();
        } else {
            self.gate_extraction_delay.bump();
        }
    }

    /// Run congruence closure on the clause database.
    ///
    /// Performs hyper-ternary resolution to enrich binary clauses, then
    /// extracts gates and runs eager congruence closure.
    ///
    /// If `vals` is provided, level-0 assignments are used to simplify gates
    /// before computing congruence. This finds more equivalences by reducing
    /// gate arities (matching CaDiCaL's `propagate_units_and_equivalences`).
    /// `vals` is indexed by literal index: `1` = true, `-1` = false, `0` = unassigned.
    ///
    /// Returns the literal mapping (canonical representative for each literal)
    /// and whether any equivalences were found.
    pub(crate) fn run(
        &mut self,
        clauses: &mut ClauseArena,
        vals: Option<&[i8]>,
        frozen: &[bool],
    ) -> CongruenceResult {
        // CaDiCaL congruence.cpp: num_vars must match internal state
        debug_assert!(
            frozen.len() <= self.num_vars,
            "BUG: congruence frozen.len()={} > num_vars={}",
            frozen.len(),
            self.num_vars,
        );
        self.stats.rounds += 1;

        // Step 0: Hyper-ternary resolution (CaDiCaL extract_binaries).
        // Skip for large formulas: the O(clauses) scan to build binary_map
        // dominates (1.9s on 4.7M-clause shuffling-2). CaDiCaL runs ternary
        // resolution in probing, not congruence. HTR is still useful on
        // small/medium formulas where binary enrichment helps gate extraction.
        let new_binaries = if clauses.num_clauses() > 1_000_000 {
            Vec::new()
        } else {
            self.hyper_ternary_resolution(clauses)
        };

        // Step 0b: Build binary adjacency into cached storage (shared by find_units + find_equivalences).
        // Reuses Vec storage across calls — only the first call allocates.
        self.build_binary_adjacency_cached(clauses);

        if debug_congruence_enabled() {
            let num_binary = clauses
                .indices()
                .filter(|&idx| {
                    !clauses.is_empty_clause(idx)
                        && !clauses.is_learned(idx)
                        && clauses.literals(idx).len() == 2
                })
                .count();
            let num_ternary = clauses
                .indices()
                .filter(|&idx| {
                    !clauses.is_empty_clause(idx)
                        && !clauses.is_learned(idx)
                        && clauses.literals(idx).len() == 3
                })
                .count();
            let num_vals_nonzero = vals
                .map(|v| v.iter().filter(|&&x| x != 0).count())
                .unwrap_or(0);
            let total_clauses = clauses.num_clauses();
            eprintln!(
                "[congruence] clause DB: {total_clauses} total, {num_binary} binary, \
                 {num_ternary} ternary, vals_nonzero={num_vals_nonzero}"
            );
        }

        // Step 0c: Binary complementary pair unit discovery (CaDiCaL find_units).
        // Must run after HTR so newly derived binaries are visible.
        let binary_units = self.find_units_cached();

        // Step 1: Initialize union-find early so find_equivalences can seed it.
        let num_lits = self.num_vars * 2;
        let mut uf = UnionFind::new(num_lits);
        let mut equivalence_edges = Vec::new();
        let mut edge_provenance: Vec<EdgeProvenance> = Vec::new();

        // Step 1b: Binary implication equivalence discovery (CaDiCaL find_equivalences).
        // Seeds the UF with equivalences from binary clauses before gate analysis,
        // so congruence closure sees them and can cascade further.
        let binary_equiv_found = match self.find_equivalences_cached(
            &mut uf,
            &mut equivalence_edges,
            &mut edge_provenance,
        ) {
            Ok(found) => found,
            Err(unit) => {
                // Keep the accumulated edges: the solver inserts their
                // binaries into the DB before probing the contradiction
                // witness, and discarding them both starves that probe
                // and throws away the round's real equivalences.
                return CongruenceResult {
                    found_equivalences: false,
                    is_unsat: true,
                    units: vec![unit],
                    equivalence_edges,
                    edge_provenance,
                    new_binary_clauses: new_binaries,
                    parity_certified_units: Vec::new(),
                };
            }
        };

        // Step 2: Extract gates from the formula (frozen variables excluded).
        // Fruitless gate rounds back off temporarily, but unlike the old
        // permanent skip cache they eventually retry even if `num_vars` is
        // unchanged and clause structure changed underneath.
        let delay_gate_extraction = self.gate_extraction_delay.delay();
        let gates = if delay_gate_extraction {
            Vec::new()
        } else {
            let mut extractor = GateExtractor::new(self.num_vars);
            self.extract_all_gates(&mut extractor, clauses, frozen)
        };

        if gates.is_empty() {
            if delay_gate_extraction {
                if binary_equiv_found {
                    self.gate_extraction_delay.reduce();
                }
            } else {
                self.record_gate_extraction_outcome(binary_equiv_found);
            }
            return CongruenceResult {
                found_equivalences: binary_equiv_found,
                is_unsat: false,
                units: binary_units,
                equivalence_edges,
                edge_provenance,
                new_binary_clauses: new_binaries,
                parity_certified_units: Vec::new(),
            };
        }

        self.stats.gates_analyzed += gates.len() as u64;

        if debug_congruence_enabled() {
            // Count gate types
            let and_count = gates
                .iter()
                .filter(|g| g.gate_type == GateType::And)
                .count();
            let xor_count = gates
                .iter()
                .filter(|g| g.gate_type == GateType::Xor)
                .count();
            let equiv_count = gates
                .iter()
                .filter(|g| g.gate_type == GateType::Equiv)
                .count();
            let ite_count = gates
                .iter()
                .filter(|g| g.gate_type == GateType::Ite)
                .count();
            let total = gates.len();
            let nv = self.num_vars;
            eprintln!(
                "[congruence] gates: {total} total ({and_count} AND, {xor_count} XOR, {equiv_count} Equiv, {ite_count} ITE), num_vars: {nv}"
            );
        }

        // Step 3: Build congruence closure with eager rewriting.
        // UF is pre-seeded with binary equivalences from step 1b.
        // Returns contradiction unit witness on x ≡ ¬x, or
        // (found_any, discovered_units) on success.
        let mut xor_certified_units: Vec<Literal> = Vec::new();
        let (gate_equiv_found, discovered_units) = match self.compute_congruence_closure(
            &gates,
            &mut uf,
            vals,
            &mut equivalence_edges,
            &mut edge_provenance,
            &mut xor_certified_units,
        ) {
            Ok(result) => result,
            Err(unit) => {
                // Keep the accumulated edges (see the step-1b Err arm):
                // the final contradicting edge recorded by
                // merge_or_contradict closes the a ≡ … ≡ ¬a cycle in the
                // DB so the witness unit's RUP probe can succeed.
                return CongruenceResult {
                    found_equivalences: false,
                    is_unsat: true,
                    units: vec![unit],
                    equivalence_edges,
                    edge_provenance,
                    new_binary_clauses: new_binaries,
                    parity_certified_units: xor_certified_units,
                };
            }
        };

        let found_equivalences = binary_equiv_found || gate_equiv_found;

        // Merge units from binary complementary pairs with gate-derived units.
        let mut all_units = binary_units;
        all_units.extend(discovered_units);

        self.record_gate_extraction_outcome(found_equivalences);

        if !found_equivalences {
            if debug_congruence_enabled() {
                let n = gates.len();
                eprintln!("[congruence] no equivalences found from {n} gates");
            }
            return CongruenceResult {
                found_equivalences: false,
                is_unsat: false,
                units: all_units,
                equivalence_edges: Vec::new(),
                edge_provenance: Vec::new(),
                new_binary_clauses: new_binaries,
                parity_certified_units: xor_certified_units,
            };
        }

        if debug_congruence_enabled() {
            // Build a temporary lit_map for debug logging only.
            let lit_map = self.build_lit_map(&mut uf);
            let equiv_count = (0..self.num_vars)
                .filter(|&v| {
                    let pos = Literal::positive(Variable(v as u32));
                    lit_map[pos.index()] != pos
                })
                .count();
            eprintln!("[congruence] found {equiv_count} variable equivalences");
        }

        // NOTE: Forward subsumption (CaDiCaL congruence.cpp:4955-5073) runs
        // in the solver wrapper (congruence_body) AFTER proof emission, because
        // proof RUP checks need gate-defining clauses alive during
        // decide/propagate verification.

        // Clause-level substitution (rewriting, deletion) is deferred to
        // decompose(), which runs after congruence in the inprocessing pipeline.
        // decompose's SCC will discover these equivalences through the binary
        // clauses added above and rewrite ALL clauses uniformly (#5237).

        CongruenceResult {
            found_equivalences: true,
            is_unsat: false,
            units: all_units,
            equivalence_edges,
            edge_provenance,
            new_binary_clauses: new_binaries,
            parity_certified_units: xor_certified_units,
        }
    }

    /// Extract all gates from the formula for congruence closure.
    ///
    /// Reuses cached occurrence lists across calls to avoid O(num_vars) fresh
    /// Vec allocations per call. On shuffling-2 (138K vars), this saves 276K
    /// allocations per round. CaDiCaL maintains persistent `noccs`/`occs`
    /// arrays (congruence.hpp init_closure).
    fn extract_all_gates(
        &mut self,
        extractor: &mut GateExtractor,
        clauses: &ClauseArena,
        frozen: &[bool],
    ) -> Vec<Gate> {
        let mut gates = Vec::new();

        // Reuse cached occurrence lists: grow if needed, clear existing entries.
        // Only the initial call pays the allocation cost; subsequent calls
        // reuse the Vec storage (capacity preserved across clears).
        self.cached_pos_occs.resize_with(self.num_vars, Vec::new);
        self.cached_neg_occs.resize_with(self.num_vars, Vec::new);
        for v in self.cached_pos_occs.iter_mut().take(self.num_vars) {
            v.clear();
        }
        for v in self.cached_neg_occs.iter_mut().take(self.num_vars) {
            v.clear();
        }

        // Per-literal ternary-clause occurrence counts (Kissat `largecount`).
        // Indexed by literal index (var*2 + sign), so width is 2 * num_vars.
        let num_lits = self.num_vars * 2;
        self.cached_ternary_count.clear();
        self.cached_ternary_count.resize(num_lits, 0);

        for idx in clauses.indices() {
            if clauses.is_empty_clause(idx) {
                continue;
            }
            let lits = clauses.literals(idx);
            let is_ternary = lits.len() == 3;
            for &lit in lits {
                let var_idx = lit.variable().0 as usize;
                if var_idx < self.num_vars {
                    if lit.is_positive() {
                        self.cached_pos_occs[var_idx].push(idx);
                    } else {
                        self.cached_neg_occs[var_idx].push(idx);
                    }
                    if is_ternary {
                        let li = lit.index();
                        if li < num_lits {
                            self.cached_ternary_count[li] += 1;
                        }
                    }
                }
            }
        }

        // Effort-bounded gate extraction (#6926): CaDiCaL bounds congruence
        // by using tick-based effort limits. For AY, we track total clause
        // accesses across all variables and bail when the budget is exceeded.
        // Budget: 20 * num_clauses — allows scanning the clause DB ~20 times
        // in aggregate.
        let total_clauses = clauses.num_clauses().max(1);
        let effort_budget: u64 = 20 * total_clauses as u64;
        let mut effort_spent: u64 = 0;

        // Wall-clock guard (#8078): abort gate extraction on large formulas
        // to prevent congruence from dominating preprocessing time.
        let extract_start = ay_core::time::Instant::now();
        const GATE_EXTRACT_TIME_BUDGET_MS: u128 = 2000;

        // ITE gate extraction was O(pos_ternary² × neg) per variable, which
        // blew up on dense-ternary formulas (e.g. shuffling-2: 729K ternary).
        // The old mitigation was a hard `num_vars <= 50_000` cutoff that
        // disabled ITE on large formulas — but that left big instances such as
        // 70da0b78 (68K vars) with 0 ITE gates while Kissat found ~19.8K.
        //
        // We now port Kissat's `twice` both-polarity ternary pre-filter
        // (congruence.c init_ite_gate_extraction): a variable is only an ITE
        // output candidate when both polarities occur in ≥2 ternary clauses,
        // and a base clause is only explored when ≥2 of its literals occur in
        // BOTH polarities among ternary clauses. That `cached_ternary_count`
        // (largecount) filter slashes the candidate set cheaply, so the hard
        // variable-count cutoff is no longer needed. The wall-clock guard
        // (GATE_EXTRACT_TIME_BUDGET_MS) and effort budget still bound the pass.
        let include_ite = true;

        // Shared LitMarks: single allocation reused across all variables.
        // Eliminates N per-variable allocations (138K on shuffling-2).
        // CaDiCaL uses a single shared mark array (internal.hpp:481-495).
        let mut shared_marks = LitMarks::new(self.num_vars);

        // Clause-driven XOR group pass (Kissat congruence.c:2679-3242 port).
        // Owns XOR extraction for congruence: one complete group over k+1
        // variables emits up to k+1 gates (one per literal as LHS), which is
        // what enables cross-group signature merges (b=a⊕c vs e=a⊕c ⇒ b≡e)
        // that the one-gate-per-pivot search structurally missed — measured
        // 8112 vs Kissat 23040 XOR gates on 70da0b78 (#15). The per-pivot
        // loop below runs with include_xor=false; BVE keeps its own per-pivot
        // XOR path. Shares the effort/wall budgets with the per-pivot loop.
        let xor_pass = extractor.extract_xor_groups_clause_driven(
            clauses,
            self.num_vars,
            frozen,
            &mut effort_spent,
            effort_budget,
            extract_start,
            GATE_EXTRACT_TIME_BUDGET_MS,
            &mut gates,
        );

        // Try to find a gate for each variable (skip frozen variables).
        // CaDiCaL has no early-exit threshold — it scans all variables,
        // bounded only by a tick-based effort limit. AY uses effort_budget
        // (20 * num_clauses) for the same purpose. The previous 25%
        // early-exit was removed because it prevented gate extraction on
        // formulas where gates are in higher-indexed variables (e.g.,
        // FmlaEquivChain: first 13K vars have no gates, gates start at
        // ~15K). This caused preprocessing congruence to find 0 gates
        // while CaDiCaL found 11K+ (#7423).
        for var_idx in 0..self.num_vars {
            if effort_spent >= effort_budget {
                break;
            }
            // Wall-clock check every 1024 variables to limit overhead.
            if var_idx & 0x3FF == 0
                && var_idx > 0
                && extract_start.elapsed().as_millis() >= GATE_EXTRACT_TIME_BUDGET_MS
            {
                break;
            }
            if var_idx < frozen.len() && frozen[var_idx] {
                continue;
            }
            if self.cached_pos_occs[var_idx].is_empty() || self.cached_neg_occs[var_idx].is_empty()
            {
                continue;
            }

            // Charge effort: gate extraction examines all occurrences of
            // the pivot variable in both polarities.
            let var_effort =
                self.cached_pos_occs[var_idx].len() + self.cached_neg_occs[var_idx].len();
            effort_spent += var_effort as u64;

            let gate = if include_ite {
                extractor.find_gate_for_congruence_with_marks(
                    Variable(var_idx as u32),
                    clauses,
                    &self.cached_pos_occs[var_idx],
                    &self.cached_neg_occs[var_idx],
                    false, // XOR handled by the clause-driven group pass above
                    &self.cached_ternary_count,
                    &mut shared_marks,
                )
            } else {
                extractor.find_gate_for_congruence_no_ite_with_marks(
                    Variable(var_idx as u32),
                    clauses,
                    &self.cached_pos_occs[var_idx],
                    &self.cached_neg_occs[var_idx],
                    false, // XOR handled by the clause-driven group pass above
                    &mut shared_marks,
                )
            };
            if let Some(gate) = gate {
                gates.push(gate);
            }
        }

        if std::env::var_os("AY_AB_SUBST_DUMP_GATES").is_some() {
            for g in &gates {
                eprintln!(
                    "DUMP_GATE: type={:?} out={} neg_out={} inputs={:?} def_clauses={}",
                    g.gate_type,
                    g.output.0,
                    g.negated_output,
                    g.inputs.iter().map(|l| l.index()).collect::<Vec<_>>(),
                    g.defining_clauses.len(),
                );
            }
        }
        if std::env::var_os("AY_AB_SUBST_STATS").is_some() {
            let ite = gates
                .iter()
                .filter(|g| g.gate_type == GateType::Ite)
                .count();
            let xor = gates
                .iter()
                .filter(|g| g.gate_type == GateType::Xor)
                .count();
            eprintln!(
                "AB_GATES: total={} ite={} xor={} xor_groups={} xor_truncated={} extract_ms={} num_vars={}",
                gates.len(),
                ite,
                xor,
                xor_pass.groups,
                xor_pass.truncated,
                extract_start.elapsed().as_millis(),
                self.num_vars,
            );
        }

        gates
    }
}

/// Result of running congruence closure
#[derive(Debug)]
pub(crate) struct CongruenceResult {
    /// Whether any equivalences were found
    pub found_equivalences: bool,
    /// Whether a contradiction was detected (literal ≡ its complement).
    pub is_unsat: bool,
    /// Unit clause(s) implied by the contradiction witness.
    pub units: Vec<Literal>,
    /// Direct equivalence merges discovered during congruence closure.
    ///
    /// These edges preserve the merge chain. Proof emitters should prefer
    /// them over endpoint-only pairs to avoid non-local clauses.
    pub equivalence_edges: Vec<(Literal, Literal)>,
    /// Per-edge structured justification, parallel to `equivalence_edges`
    /// (#15 T3). XorMatch edges enable the solver-side XOR matching ladder.
    pub edge_provenance: Vec<EdgeProvenance>,
    /// New binary clauses added by hyper-ternary resolution (clause_idx, lit0, lit1).
    /// Callers must set up watches for these.
    pub new_binary_clauses: Vec<(usize, Literal, Literal)>,
    /// Subset of `units` that were emitted by a full XOR-gate collapse (arity-0)
    /// whose polarity is the machine-checked-exact parity proven in
    /// the development proof harness (`xor_collapse_parity_verified`,
    /// order-independent and single-flip-sensitive). These units are sound by
    /// construction — correct extraction, valid UF/level-0 substitutions, and
    /// now machine-checked parity — so the `#7137` RUP guard may accept them
    /// even when AY's post-hoc RUP cannot reconstruct the (ambiguous) XOR chain.
    /// Consumed only behind the default-off `AY_AB_CONGRUENCE_PARITY_TRUST` knob.
    pub parity_certified_units: Vec<Literal>,
}
