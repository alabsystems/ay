// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Eager BV bit-blasting adapter for check_sat queries.
//!
//! Bit-blasts BV predicates into SAT clauses and connects them to the
//! Tseitin encoding produced by the CNF stage. Uses persistent BV
//! caching to avoid redundant work across queries with identical
//! BV structure.

use ay_core::kani_compat::DetHashMap as FxHashMap;
use ay_core::kani_compat::DetHashSet as FxHashSet;
use ay_core::TermId;

use super::super::context::SmtContext;
use super::support::add_offset_bv_clause;
use super::CnfState;
use crate::expr::ExprFeatures;

#[cfg(test)]
use super::{record_bv_bitblast_for_tests, record_bv_new_clauses_for_tests};

/// Default per-term BV bit-width above which `attach_bv_bitblasting` refuses to
/// bit-blast (fail-closed). Overridable via `AY_BITBLAST_MAX_WIDTH`.
///
/// 16_384 is 64× the widest BV width that occurs in ANY real obligation in this
/// codebase (the widest observed is 256), so a genuine small-BV query is never
/// refused — yet it is far below the hundreds-of-thousands-of-bits blow-up that
/// an arbitrary-precision obligation (e.g. `rational::Rat::inv`) forces.
const DEFAULT_BITBLAST_MAX_WIDTH: u32 = 16_384;

/// The effective per-term BV bit-width bit-blast budget (cached after first
/// read). `AY_BITBLAST_MAX_WIDTH=<n>` overrides the default; a zero/garbage
/// value falls back to the default (never disables the guard). Shared by the
/// ChcExpr-level gate in `check_sat`/`check_sat_with_executor_fallback` and the
/// term-level backstop guard in `attach_bv_bitblasting`.
pub(super) fn bitblast_max_width() -> u32 {
    static WIDTH: std::sync::OnceLock<u32> = std::sync::OnceLock::new();
    *WIDTH.get_or_init(|| {
        std::env::var("AY_BITBLAST_MAX_WIDTH")
            .ok()
            .and_then(|v| v.parse::<u32>().ok())
            .filter(|&w| w > 0)
            .unwrap_or(DEFAULT_BITBLAST_MAX_WIDTH)
    })
}

/// Default CUMULATIVE bit-blast budget: the maximum SUM of BV bit-widths across
/// ALL terms of a single query that will be bit-blasted before the query is
/// refused (fail-closed). Overridable via `AY_BITBLAST_MAX_TOTAL_BITS`.
///
/// This is the guard for the REAL grind. The per-term `DEFAULT_BITBLAST_MAX_WIDTH`
/// guard never fires on the observed obligations (crown_deep::f64_to_rat,
/// crown::Relu, preact_bounds, certz::qpair_json/lincon_json): NO single BV term
/// is wide (each is ≤ 256 bits). Instead MANY moderate-width terms ACCUMULATE —
/// their bit-blasts sum PAST the `MAX_PERSISTENT_CACHE_ENTRIES` (500_000) cap
/// (observed 916k / 1_069k / 1_379k entries), so the cache clears at the cap and
/// refills, thrashing with zero progress until a ~52-minute watchdog SIGKILL.
///
/// 400_000 sits comfortably BELOW the 500_000 cache cap so the thrash never
/// STARTS, yet far above any real small-BV obligation (widest real term 256
/// bits, modest term counts → cumulative bit totals orders of magnitude under
/// this), so no genuine query is refused — WHEN MEASURED ACCURATELY. This
/// value calibrates the `attach_bv_bitblasting` backstop, whose
/// `bitblast_bv_width_and_total` sums over the interned term DAG actually
/// being blasted (bits ≈ minted cache entries there).
const DEFAULT_BITBLAST_MAX_TOTAL_BITS: u64 = 400_000;

/// Pre-gate multiplier (model-checker-consumer #43 bisect, 2026-07-12): the EARLY gate in
/// `bitblast_budget_exceeded` measures via `total_bv_bits`, a `ChcExpr` walk
/// that dedups by `Arc` pointer identity only. CHC BMC unrolling freshly
/// instantiates clause bodies per depth, so logically-shared subterms are
/// counted once PER INSTANTIATION — safe acyclic contract CHCs that blast and
/// solve in 2-6s (accurate totals far under the base budget) counted ~1.03M
/// "bits" and were refused, flipping Safe -> Unknown across the
/// function-contract corpus. The pre-gate therefore allows OVERCOUNT_FACTOR x
/// the base budget: legitimate BMC-unrolled lanes (~1M overcounted) pass with
/// ~8x headroom, the observed thrash class (916k-2.56M interned entries of
/// up-to-256-bit terms → tens-to-hundreds of millions under the same walk)
/// is still refused early, and anything in between is decided by the ACCURATE
/// backstop before any cache entry is minted.
const PREGATE_OVERCOUNT_FACTOR: u64 = 20;

/// Budget for the early, overcounting `ChcExpr`-walk gate. Scales with the
/// base budget so `AY_BITBLAST_MAX_TOTAL_BITS` and the test override move
/// both gates proportionally.
pub(super) fn bitblast_pregate_max_total_bits() -> u64 {
    bitblast_max_total_bits().saturating_mul(PREGATE_OVERCOUNT_FACTOR)
}

/// DYNAMIC bit-blast abort (model-checker-consumer #46): the ground-truth thrash condition.
///
/// The static bit-count gates above PREDICT blast cost from term shapes, but
/// the prediction is structurally imprecise in both directions: BMC-unrolled
/// CHCs count ~1M "bits" (per-depth re-instantiation defeats pointer AND
/// content dedup) yet mint well under the cache cap and solve in seconds,
/// while a flat accumulation of genuinely-distinct variables counts the same
/// ~1M bits and mints 2.5M entries (5x). Only the blast itself knows. So the
/// blast loop polls `BvSolver::minted_entries_estimate()` — the live count of
/// exactly the collections `PersistentBvCache::total_entries()` would capture
/// — and ABORTS the query (fail-closed Unknown, same contract as the static
/// refusals) the moment a single query's blast reaches the cap that would
/// otherwise trigger capture-time clear-and-rebuild on every subsequent
/// query (the observed ny-cert ~52-minute SIGKILL grind).
///
/// Trade-off, documented deliberately: a hypothetical one-shot query minting
/// slightly over the cap that would have completed (slowly, with one
/// capture-time clear) now returns Unknown fast. That regime is exactly the
/// pathological one the cap exists to flag, and every observed legitimate
/// lane mints far below it; `AY_BITBLAST_DYNAMIC_ABORT=0` disables the guard
/// for diagnosis.
fn bitblast_dynamic_abort_enabled() -> bool {
    #[cfg(test)]
    {
        match TEST_DYNAMIC_ABORT_OVERRIDE.load(std::sync::atomic::Ordering::Relaxed) {
            1 => return true,
            2 => return false,
            _ => {}
        }
    }
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AY_BITBLAST_DYNAMIC_ABORT").as_deref() != Ok("0"))
}

/// Test-only override for the dynamic abort: `0` = env/default path,
/// `1` = force-on, `2` = force-off (lets one serial test exercise both the
/// legacy thrash reproduction and the aborted behaviour despite the
/// process-wide `OnceLock`).
#[cfg(test)]
static TEST_DYNAMIC_ABORT_OVERRIDE: std::sync::atomic::AtomicU8 =
    std::sync::atomic::AtomicU8::new(0);

#[cfg(test)]
pub(in crate::smt) fn set_bitblast_dynamic_abort_override_for_tests(v: u8) {
    TEST_DYNAMIC_ABORT_OVERRIDE.store(v, std::sync::atomic::Ordering::Relaxed);
}

/// Test-only override for the cumulative budget. The `OnceLock` in
/// `bitblast_max_total_bits` caches the env/default value process-wide on first
/// read, so a test cannot toggle the budget via the environment (a second test
/// would see the first test's cached value). This atomic lets a single test
/// measure BOTH the un-gated thrash (set a huge value to disable the gate) and
/// the gated bounded behaviour (clear back to 0 → normal env/default path).
/// `0` = no override (use the normal path). Zero overhead in non-test builds.
#[cfg(test)]
static TEST_TOTAL_BITS_OVERRIDE: std::sync::atomic::AtomicU64 =
    std::sync::atomic::AtomicU64::new(0);

#[cfg(test)]
pub(in crate::smt) fn set_bitblast_max_total_bits_override_for_tests(v: u64) {
    TEST_TOTAL_BITS_OVERRIDE.store(v, std::sync::atomic::Ordering::Relaxed);
}

#[cfg(test)]
pub(in crate::smt) fn clear_bitblast_max_total_bits_override_for_tests() {
    TEST_TOTAL_BITS_OVERRIDE.store(0, std::sync::atomic::Ordering::Relaxed);
}

/// The effective CUMULATIVE bit-blast budget (cached after first read).
/// `AY_BITBLAST_MAX_TOTAL_BITS=<n>` overrides the default; a zero/garbage value
/// falls back to the default (never disables the guard). Shared by the
/// ChcExpr-level gate in `check_sat`/`check_sat_with_executor_fallback` and the
/// term-level backstop in `attach_bv_bitblasting`.
pub(super) fn bitblast_max_total_bits() -> u64 {
    #[cfg(test)]
    {
        let ov = TEST_TOTAL_BITS_OVERRIDE.load(std::sync::atomic::Ordering::Relaxed);
        if ov != 0 {
            return ov;
        }
    }
    static BITS: std::sync::OnceLock<u64> = std::sync::OnceLock::new();
    *BITS.get_or_init(|| {
        std::env::var("AY_BITBLAST_MAX_TOTAL_BITS")
            .ok()
            .and_then(|v| v.parse::<u64>().ok())
            .filter(|&b| b > 0)
            .unwrap_or(DEFAULT_BITBLAST_MAX_TOTAL_BITS)
    })
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

        // Bit-blast cost guard (fail-closed), a term-level backstop for the same
        // gate `check_sat`/`check_sat_with_executor_fallback` apply on the raw
        // ChcExpr. Two ways bit-blasting explodes the PersistentBvCache past its
        // cap — after which the cache clears and refills on every subsequent
        // query and the whole verification wave grinds with zero progress until a
        // watchdog SIGKILL:
        //
        //  1. One arbitrary-precision term (e.g. `rational::Rat::inv`) forces a
        //     BV hundreds of thousands of bits wide — caught by the WIDTH bound.
        //  2. MANY moderate-width terms (each ≤ 256 bits) whose bit-blasts SUM
        //     past the cap — the observed real mechanism, invisible to the width
        //     bound because no single term is wide — caught by the TOTAL bound.
        // Bit-blasting mints ≈ one fresh SAT variable and several clauses per
        // bit, so either bound overflowing means the cache would overflow.
        //
        // SOUNDNESS (the whole argument): refusing to bit-blast makes this
        // method ABSTAIN and the caller (`check_sat_internal`) return Unknown.
        // Abstaining is ALWAYS sound — an un-blasted SAT instance is missing its
        // BV constraints, so we never run the theory loop on it and therefore
        // never report Sat (a false refutation) nor Unsat (a false proof).
        // Completeness is lost ONLY on obligations that genuinely need a huge
        // blast, and those produce no verdict at all today (they grind to a
        // SIGKILL that kills the entire wave), so Unknown is strictly better.
        // The thresholds are far above any real small-BV obligation, so no
        // genuine query is refused.
        let (max_bv_width, total_bv_bits) = self.bitblast_bv_width_and_total(state);
        let width_budget = bitblast_max_width();
        if max_bv_width > width_budget {
            tracing::warn!(
                width = max_bv_width,
                budget = width_budget,
                "bitblast width budget exceeded; abstaining (Unknown) to avoid PersistentBvCache thrash"
            );
            if self.verbose || crate::debug_chc_smt_enabled() {
                safe_eprintln!(
                    "[CHC-SMT] bitblast refused: BV width {max_bv_width} exceeds budget {width_budget}; returning Unknown (fail-closed)"
                );
            }
            return false;
        }
        // Relaxed to the HIGH pre-gate threshold (model-checker-consumer #46): with the
        // dynamic mid-blast abort below enforcing the true entry cap, this
        // static count is only a fast-path early-out for astronomically-large
        // queries — predicting cost from bit counts alone misjudges legitimate
        // BMC-unrolled CHC lanes by up to 5x in either direction.
        let total_budget = bitblast_pregate_max_total_bits();
        if total_bv_bits > total_budget {
            tracing::warn!(
                total_bits = total_bv_bits,
                budget = total_budget,
                "bitblast cumulative total-bits budget exceeded; abstaining (Unknown) to avoid PersistentBvCache thrash"
            );
            if self.verbose || crate::debug_chc_smt_enabled() {
                safe_eprintln!(
                    "[CHC-SMT] bitblast refused: cumulative BV bits {total_bv_bits} exceed total budget {total_budget}; returning Unknown (fail-closed)"
                );
            }
            return false;
        }

        use ay_bv::BvSolver;
        #[cfg(test)]
        record_bv_bitblast_for_tests();

        let mut persistent_bv_cache = std::mem::take(&mut self.persistent_bv_cache);
        let mut bv_solver = BvSolver::new(&self.terms);
        let current_terms: Vec<TermId> = state.var_to_term.values().copied().collect();
        let mut bv_key_memo = FxHashMap::default();
        let current_signature =
            self.bv_cache_signature(current_terms.iter().copied(), &mut bv_key_memo);
        let reuse_cached_bv = persistent_bv_cache.signature == current_signature;
        if reuse_cached_bv {
            // Restore over the TRANSITIVE BV SUB-TERM CLOSURE of the atoms,
            // not the atom terms alone. `cache.term_to_bits` holds the bit
            // vectors of every blasted sub-term (variables, adders, ...), but
            // the atoms themselves are Bool — restoring only atoms brings
            // back their memoized predicate vars while leaving every
            // variable's bits unknown to `bv_solver`. Any NEW atom over a
            // previously-blasted variable then mints a SECOND, disconnected
            // set of bit variables for the same term: the replayed circuit
            // constrains the old bits, the new atom constrains the new bits,
            // nothing links them, and model extraction (which reads
            // `term_to_bits`) reports values that violate the memoized atoms.
            // That is the "SAT model from DPLL(T) loop violates original
            // expression" WARN-flood that collapsed the native BV lane to
            // Unknown on model-checker-consumer PDR workloads (looping_id L0 failure):
            // every PDR frame query shares the atom signature but adds fresh
            // cube atoms over the same state variables.
            let restore_terms = self.bv_subterm_closure(&current_terms);
            bv_key_memo =
                self.restore_cached_bv_state(&persistent_bv_cache, &mut bv_solver, restore_terms);
        }
        let mut bv_connections: Vec<(u32, i32)> = Vec::new();

        // Check each Tseitin variable's term for BV predicates, polling the
        // DYNAMIC abort guard after each blast step (see
        // `bitblast_dynamic_abort_enabled`). Mechanically-correct condition:
        // `minted_entries_estimate()` counts the live sizes of exactly the
        // collections `capture_cached_bv_state` copies into the persistent
        // cache and `PersistentBvCache::total_entries()` sums for the
        // capture-time cap-clear — so crossing the cap HERE is the same event
        // that would trigger clear-and-rebuild-per-query afterwards. On reuse,
        // restored entries count too: a signature-matched restore means the
        // same query shape, so restored+new is what a fresh blast of this
        // query would mint. SOUNDNESS/CLEANLINESS: nothing has touched
        // `state` yet (SAT clauses are wired only after this loop), so
        // aborting here leaves the caller's solver exactly as the static
        // refusals above do — we restore the untouched persistent cache and
        // return false, and the caller reports Unknown. Capture-time
        // `enforce_capacity` stays as the between-queries eviction backstop.
        let dynamic_cap = crate::smt::context::MAX_PERSISTENT_CACHE_ENTRIES;
        let dynamic_abort = bitblast_dynamic_abort_enabled();
        for (&tseitin_var, &term) in &state.var_to_term {
            if let Some(bv_lit) = bv_solver.bitblast_predicate(term) {
                bv_connections.push((tseitin_var, bv_lit));
            }
            if dynamic_abort && bv_solver.minted_entries_estimate() > dynamic_cap {
                let minted = bv_solver.minted_entries_estimate();
                tracing::warn!(
                    minted,
                    cap = dynamic_cap,
                    "bitblast aborted mid-blast: minted entries reached the cache cap; abstaining (Unknown)"
                );
                if self.verbose || crate::debug_chc_smt_enabled() {
                    safe_eprintln!(
                        "[CHC-SMT] bitblast aborted: minted entries {minted} reached cache cap {dynamic_cap}; returning Unknown (fail-closed)"
                    );
                }
                self.persistent_bv_cache = persistent_bv_cache;
                return false;
            }
        }

        let new_pre_connection_clauses = bv_solver.take_clauses();
        #[cfg(test)]
        record_bv_new_clauses_for_tests(new_pre_connection_clauses.len());

        // #6090: checked conversion — num_vars exceeding i32::MAX cannot
        // be represented in DIMACS literal encoding. Skip BV if overflow.
        if !bv_connections.is_empty() && i32::try_from(state.num_vars).is_ok() {
            let offset = state.num_vars as i32; // safe: checked above
            let bv_total_vars = bv_solver.num_vars();

            // Grow SAT solver to accommodate BV variables.
            state
                .sat
                .ensure_num_vars((state.num_vars + bv_total_vars) as usize);

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
            state.num_vars += bv_total_vars;

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
            self.capture_cached_bv_state(
                &mut persistent_bv_cache,
                &bv_solver,
                current_signature,
                &mut bv_key_memo,
                circuit_clauses,
            );
        }
        self.persistent_bv_cache = persistent_bv_cache;
        true
    }

    /// Transitive sub-term closure of the given atom terms — the atoms plus
    /// every term reachable through their argument DAG. This is the term set
    /// `restore_cached_bv_state` must see so that cached bit vectors of
    /// VARIABLES and intermediate BV terms are restored alongside the atoms'
    /// memoized predicate vars (see the reuse-path comment at the call site).
    pub(super) fn bv_subterm_closure(&self, roots: &[TermId]) -> Vec<TermId> {
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
