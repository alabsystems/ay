// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager BV bit-blasting adapter for check_sat queries.
//!
//! Bit-blasts BV predicates into SAT clauses and connects them to the
//! Tseitin encoding produced by the CNF stage. Uses persistent BV
//! caching to avoid redundant work across queries with identical
//! BV structure.

use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::TermId;

use super::super::context::SmtContext;
use super::support::add_offset_bv_clause;
use super::CnfState;
use crate::expr::ExprFeatures;

#[cfg(test)]
use super::{record_bv_bitblast_for_tests, record_bv_new_clauses_for_tests};

#[cfg(test)]
mod encoding_stop_tests;
#[cfg(test)]
mod full_adder_cache_tests;
#[cfg(test)]
mod transient_cache_tests;

/// Existing per-term width envelope, independent of persistent cache retention.
const DEFAULT_BITBLAST_MAX_WIDTH: u32 = 16_384;

/// Shared by the expression-level gate and the interned-term backstop.
pub(super) fn bitblast_max_width() -> u32 {
    // B25: env override retired; the named constant is the value.
    DEFAULT_BITBLAST_MAX_WIDTH
}

/// Base for the historical total-bit query envelope. This is not a cache cap
/// or a deterministic-effort allowance; those are different resource policies.
const DEFAULT_BITBLAST_MAX_TOTAL_BITS: u64 = 400_000;

/// Expression walks deduplicate by Arc identity, not interned term identity.
/// Both existing gates use this relaxed envelope to accommodate that overcount.
const PREGATE_OVERCOUNT_FACTOR: u64 = 20;

/// Budget for the expression-level and interned-term total-bit gates.
pub(super) fn bitblast_pregate_max_total_bits() -> u64 {
    bitblast_max_total_bits().saturating_mul(PREGATE_OVERCOUNT_FACTOR)
}

/// Base total-bit budget shared by the two existing static query gates.
pub(super) fn bitblast_max_total_bits() -> u64 {
    // B25: env override retired; the named constant is the value.
    DEFAULT_BITBLAST_MAX_TOTAL_BITS
}

/// The two-operand BV predicate symbols `BvSolver::bitblast_predicate` handles.
/// These are exactly the terms `attach_bv_bitblasting` bit-blasts, so the width
/// scan only needs to descend from their operands.
fn is_bv_predicate_symbol(name: &str) -> bool {
    matches!(
        name,
        "=" | "bvult" | "bvule" | "bvugt" | "bvuge" | "bvslt" | "bvsle" | "bvsgt" | "bvsge"
    )
}

fn checked_bv_layout(existing: u32, extra: u32) -> Option<(i32, u32)> {
    let combined = existing.checked_add(extra)?;
    i32::try_from(combined).ok()?;
    Some((i32::try_from(existing).ok()?, combined))
}

impl SmtContext {
    /// Attach BV bit-blasting to the CNF state if the query has BV operations.
    ///
    /// Modifies `state` in place: grows the SAT solver, adds BV clauses,
    /// and wires Tseitin variables to their BV predicate equivalents.
    ///
    /// Returns `true` when bit-blasting was attached (or the query had no BV
    /// operations) and the caller may proceed with the theory loop. Returns
    /// `false` when a BV term exceeds the bit-blast width budget and the query
    /// was ABSTAINED — the caller MUST return `Unknown` (see soundness note).
    #[must_use]
    pub(super) fn attach_bv_bitblasting(
        &mut self,
        features: &ExprFeatures,
        state: &mut CnfState,
    ) -> bool {
        if !features.has_bv {
            return true;
        }
        use ay_bv::BvSolver;
        #[cfg(test)]
        record_bv_bitblast_for_tests();

        let mut bv_solver = BvSolver::new(&self.terms);
        if let Some(flag) = crate::smt::deadline::lane_interrupt_flag() {
            bv_solver.set_interrupt(flag);
        }
        if !bv_solver.inherit_current_encoding_guard() {
            return false;
        }
        let encoding = bv_solver.encoding_guard();
        if !encoding.open() {
            return false;
        }

        // Existing width/total query envelopes remain separate from retention.
        // Refusal must return false: a caller cannot solve an incomplete BV
        // encoding. Removing these static envelopes needs query-owned effort
        // accounting; a bounded persistent cache does not provide that policy.
        let (max_bv_width, total_bv_bits) = self.bitblast_bv_width_and_total(state);
        let width_budget = bitblast_max_width();
        if max_bv_width > width_budget {
            tracing::warn!(
                width = max_bv_width,
                budget = width_budget,
                "bitblast width budget exceeded; abstaining (Unknown)"
            );
            if self.verbose || crate::debug_chc_smt_enabled() {
                safe_eprintln!(
                    "[CHC-SMT] bitblast refused: BV width {max_bv_width} exceeds budget {width_budget}; returning Unknown (fail-closed)"
                );
            }
            return false;
        }
        // This historical envelope uses the high pre-gate threshold because
        // bit counts are not precise estimates of the resulting circuit size.
        let total_budget = bitblast_pregate_max_total_bits();
        if total_bv_bits > total_budget {
            tracing::warn!(
                total_bits = total_bv_bits,
                budget = total_budget,
                "bitblast cumulative total-bits budget exceeded; abstaining (Unknown)"
            );
            if self.verbose || crate::debug_chc_smt_enabled() {
                safe_eprintln!(
                    "[CHC-SMT] bitblast refused: cumulative BV bits {total_bv_bits} exceed total budget {total_budget}; returning Unknown (fail-closed)"
                );
            }
            return false;
        }

        if !encoding.open() {
            return false;
        }
        let mut persistent_bv_cache = std::mem::take(&mut self.persistent_bv_cache);
        let current_terms: Vec<TermId> = state.var_to_term.values().copied().collect();
        let (current_signature, reuse_cached_bv, mut bv_key_memo) =
            self.open_bv_cache(&mut persistent_bv_cache, &mut bv_solver, &current_terms);
        let mut bv_connections: Vec<(u32, i32)> = Vec::new();

        // The retention cap is not an active-query limit. A larger complete
        // circuit remains usable by this query; capture below simply declines
        // to retain it. Only the original encoding owner may stop the blast.
        for (&tseitin_var, &term) in &state.var_to_term {
            if let Some(bv_lit) = bv_solver.bitblast_predicate(term) {
                bv_connections.push((tseitin_var, bv_lit));
            }
            if !encoding.open() {
                drop(bv_solver);
                self.persistent_bv_cache = persistent_bv_cache;
                return false;
            }
        }

        if !encoding.open() {
            drop(bv_solver);
            self.persistent_bv_cache = persistent_bv_cache;
            return false;
        }
        let new_pre_connection_clauses = bv_solver.take_clauses();
        #[cfg(test)]
        record_bv_new_clauses_for_tests(new_pre_connection_clauses.len());

        if !bv_connections.is_empty() {
            let bv_total_vars = bv_solver.num_vars();
            // Both the offset and every shifted literal must fit DIMACS.
            // Never report successful attachment after skipping the circuit.
            let Some((offset, combined_vars)) = checked_bv_layout(state.num_vars, bv_total_vars)
            else {
                drop(bv_solver);
                self.persistent_bv_cache = persistent_bv_cache;
                return false;
            };

            // Grow SAT solver to accommodate BV variables.
            state.sat.ensure_num_vars(combined_vars as usize);

            // Replay the persistent BV circuit before wiring query-local
            // Tseitin roots. This keeps the fresh SAT solver aligned with
            // any cached BV literals restored into `bv_solver`.
            if reuse_cached_bv {
                for clause in &persistent_bv_cache.clauses {
                    add_offset_bv_clause(&mut state.sat, clause, offset);
                }
            }
            for clause in &new_pre_connection_clauses {
                add_offset_bv_clause(&mut state.sat, clause, offset);
            }

            // Connect Tseitin variables to BV predicate variables.
            // For each BV predicate, tseitin_var ↔ bv_lit (offset).
            for (tseitin_var, bv_lit) in &bv_connections {
                let bv_lit_offset = if *bv_lit > 0 {
                    *bv_lit + offset
                } else {
                    *bv_lit - offset
                };
                let tseitin_lit = *tseitin_var as i32;
                // tseitin_var → bv_lit
                state.sat.add_clause(vec![
                    ay_sat::Literal::from_dimacs(-tseitin_lit),
                    ay_sat::Literal::from_dimacs(bv_lit_offset),
                ]);
                // bv_lit → tseitin_var
                state.sat.add_clause(vec![
                    ay_sat::Literal::from_dimacs(tseitin_lit),
                    ay_sat::Literal::from_dimacs(-bv_lit_offset),
                ]);
            }

            // Clauses may have been generated during connection phase.
            let new_post_connection_clauses = bv_solver.take_clauses();
            #[cfg(test)]
            record_bv_new_clauses_for_tests(new_post_connection_clauses.len());
            for clause in &new_post_connection_clauses {
                add_offset_bv_clause(&mut state.sat, clause, offset);
            }

            // The captured clause list must be the FULL circuit for the
            // captured memo state, not just this query's delta. On the reuse
            // path `bv_solver` starts from restored memos (bitblast_predicate
            // mints nothing for already-blasted terms), so `take_clauses()`
            // returns only the delta — capturing the delta alone poisons the
            // cache: the SECOND reuse of a signature replays a "circuit" that
            // is just the previous delta, the actual bit-blast clauses are
            // gone, every BV bit is unconstrained, and each SAT model then
            // fails strict re-verification ("SAT model from DPLL(T) loop
            // violates original expression") demoting the whole native BV
            // lane to Unknown — the model-checker-consumer looping_id L0 WARN-flood /
            // PDR-collapse bug. Accumulate: restored clauses + new deltas.
            let mut circuit_clauses = if reuse_cached_bv {
                std::mem::take(&mut persistent_bv_cache.clauses)
            } else {
                Vec::new()
            };
            circuit_clauses.extend(new_pre_connection_clauses);
            circuit_clauses.extend(new_post_connection_clauses);
            if !encoding.open() {
                drop(bv_solver);
                self.persistent_bv_cache = Default::default();
                return false;
            }
            self.capture_cached_bv_state(
                &mut persistent_bv_cache,
                &bv_solver,
                current_signature,
                &mut bv_key_memo,
                circuit_clauses,
            );

            state.bv_var_offset = offset;
            state.bv_term_to_bits = bv_solver
                .term_to_bits()
                .iter()
                .map(|(&k, v)| (k, v.clone()))
                .collect();
            state.num_vars = combined_vars;

            if crate::debug_chc_smt_enabled() {
                safe_eprintln!(
                    "[CHC-SMT] BV bit-blasting: {} connections, {} BV vars, {} total vars, {} cached clauses",
                    bv_connections.len(),
                    bv_total_vars,
                    state.num_vars,
                    persistent_bv_cache.clauses.len(),
                );
            }
        } else {
            // Same full-circuit invariant as above: keep restored clauses on
            // the reuse path so captured memos never outlive their defining
            // clauses.
            let mut circuit_clauses = if reuse_cached_bv {
                std::mem::take(&mut persistent_bv_cache.clauses)
            } else {
                Vec::new()
            };
            circuit_clauses.extend(new_pre_connection_clauses);
            if !encoding.open() {
                drop(bv_solver);
                self.persistent_bv_cache = Default::default();
                return false;
            }
            self.capture_cached_bv_state(
                &mut persistent_bv_cache,
                &bv_solver,
                current_signature,
                &mut bv_key_memo,
                circuit_clauses,
            );
        }
        drop(bv_solver);
        if !encoding.open() {
            self.persistent_bv_cache = Default::default();
            return false;
        }
        self.persistent_bv_cache = persistent_bv_cache;
        true
    }

    /// Transitive sub-term closure of the given atom terms — the atoms plus
    /// every term reachable through their argument DAG. This is the term set
    /// `restore_cached_bv_state` must see so that cached bit vectors of
    /// VARIABLES and intermediate BV terms are restored alongside the atoms'
    /// memoized predicate vars (see the reuse-path comment at the call site).
    pub(in crate::smt) fn bv_subterm_closure(&self, roots: &[TermId]) -> Vec<TermId> {
        use ay_core::TermData;

        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut order: Vec<TermId> = Vec::new();
        let mut stack: Vec<TermId> = roots.to_vec();
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            order.push(t);
            match self.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Ite(c, then_t, else_t) => {
                    stack.push(*c);
                    stack.push(*then_t);
                    stack.push(*else_t);
                }
                TermData::Not(inner) => stack.push(*inner),
                _ => {}
            }
        }
        order
    }

    /// Two bit-blast cost bounds over the terms `attach_bv_bitblasting` would
    /// bit-blast — the transitive closure of BV sub-terms reachable from the
    /// operands of every BV predicate (`=`, `bvult`, …) attached to a Tseitin
    /// variable, which is exactly the set `BvSolver::get_bits` descends into:
    ///
    /// * `.0` — the WIDEST single BV sub-term (bounds the widest single blast).
    /// * `.1` — the SUM of the widths of every DISTINCT BV sub-term (the
    ///   `visited` set guarantees each interned term is counted once). This is
    ///   the accurate CUMULATIVE bit total: bit-blasting mints ≈ one fresh SAT
    ///   variable per bit, so this bounds the number of variables (and hence
    ///   `PersistentBvCache` entries) the whole blast mints. It is the quantity
    ///   the per-term width alone cannot see — MANY moderate terms accumulate.
    ///
    /// Both are 0 when the query bit-blasts nothing.
    fn bitblast_bv_width_and_total(&self, state: &CnfState) -> (u32, u64) {
        use ay_core::{Sort, TermData};

        let mut max_width = 0u32;
        let mut total_bits = 0u64;
        let mut visited: FxHashSet<TermId> = FxHashSet::default();
        let mut stack: Vec<TermId> = Vec::new();

        // Seed the walk with the operands of every two-operand BV predicate.
        for &term in state.var_to_term.values() {
            if let TermData::App(sym, args) = self.terms.get(term) {
                if args.len() == 2 && is_bv_predicate_symbol(sym.name()) {
                    stack.extend(args.iter().copied());
                }
            }
        }

        // DFS the (interned, acyclic) sub-term DAG; the visited set bounds work
        // to O(reachable terms) AND guarantees each distinct BV term contributes
        // its width to the sum exactly once.
        while let Some(t) = stack.pop() {
            if !visited.insert(t) {
                continue;
            }
            if let Sort::BitVec(bv) = self.terms.sort(t) {
                max_width = max_width.max(bv.width);
                total_bits = total_bits.saturating_add(u64::from(bv.width));
            }
            match self.terms.get(t) {
                TermData::App(_, args) => stack.extend(args.iter().copied()),
                TermData::Ite(c, then_t, else_t) => {
                    stack.push(*c);
                    stack.push(*then_t);
                    stack.push(*else_t);
                }
                TermData::Not(inner) => stack.push(*inner),
                _ => {}
            }
        }

        (max_width, total_bits)
    }
}
