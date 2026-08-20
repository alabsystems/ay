// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Nelson-Oppen equality detection for LIA.
//!
//! Detects algebraic equalities between integer variables from tight bounds
//! and linear equations. Used for Nelson-Oppen theory combination.

use super::*;

/// Production policy for the `detect_algebraic_equalities` memo.
///
/// B24 retired the semantic A/B kill switch after establishing that disabling
/// the memo changes only performance, so production always uses the cache.
fn algebraic_detect_cache_enabled() -> bool {
    true
}

/// Production policy for the #probe-rref-memo conflict predictor.
///
/// B24 retired its semantic A/B kill switch after verification, so eligible
/// conflict probes always use the incremental predictor.
fn algebraic_probe_incremental_enabled() -> bool {
    true
}

/// #probe-rref-memo observability: process-global self-time + call/fallback
/// counters for `detect_algebraic_equalities`, printed to stderr on process
/// exit when `AY_ALGEBRAIC_STATS` is set. Zero overhead when unset (one cached
/// env read on the first call). The incremental (rank-1) probe path records an
/// ATTEMPT on every reuse of prior elimination state and a FALLBACK whenever
/// the release consistency check diverges (or the incremental precondition does
/// not hold) and it re-runs the full recompute — so `fallbacks / attempts` is
/// the fail-safe fire rate that decides whether the incremental path is winning
/// or just paying overhead.
pub(crate) struct AlgebraicStats {
    pub(crate) enabled: bool,
    pub(crate) calls: std::sync::atomic::AtomicU64,
    pub(crate) nanos: std::sync::atomic::AtomicU64,
    pub(crate) scan_nanos: std::sync::atomic::AtomicU64,
    pub(crate) collect_nanos: std::sync::atomic::AtomicU64,
    pub(crate) loop_nanos: std::sync::atomic::AtomicU64,
    pub(crate) incr_attempts: std::sync::atomic::AtomicU64,
    pub(crate) incr_hits: std::sync::atomic::AtomicU64,
    pub(crate) incr_fallbacks: std::sync::atomic::AtomicU64,
    pub(crate) miss_calls: std::sync::atomic::AtomicU64,
    pub(crate) eq_sum: std::sync::atomic::AtomicU64,
    pub(crate) round_sum: std::sync::atomic::AtomicU64,
    pub(crate) eq_max: std::sync::atomic::AtomicU64,
}

pub(crate) fn algebraic_stats() -> &'static AlgebraicStats {
    use std::sync::atomic::AtomicU64;
    static STATS: std::sync::OnceLock<AlgebraicStats> = std::sync::OnceLock::new();
    STATS.get_or_init(|| AlgebraicStats {
        enabled: ay_core::misc_cli_flags().algebraic_stats,
        calls: AtomicU64::new(0),
        nanos: AtomicU64::new(0),
        scan_nanos: AtomicU64::new(0),
        collect_nanos: AtomicU64::new(0),
        loop_nanos: AtomicU64::new(0),
        incr_attempts: AtomicU64::new(0),
        incr_hits: AtomicU64::new(0),
        incr_fallbacks: AtomicU64::new(0),
        miss_calls: AtomicU64::new(0),
        eq_sum: AtomicU64::new(0),
        round_sum: AtomicU64::new(0),
        eq_max: AtomicU64::new(0),
    })
}

fn algebraic_stats_dump() {
    use std::sync::atomic::Ordering::Relaxed;
    let s = algebraic_stats();
    if !s.enabled {
        return;
    }
    safe_eprintln!(
        "[ALGEBRAIC-STATS] calls={} self_ms={:.2} scan_ms={:.2} collect_ms={:.2} loop_ms={:.2} \
         incr_attempts={} incr_hits={} incr_fallbacks={}",
        s.calls.load(Relaxed),
        s.nanos.load(Relaxed) as f64 / 1.0e6,
        s.scan_nanos.load(Relaxed) as f64 / 1.0e6,
        s.collect_nanos.load(Relaxed) as f64 / 1.0e6,
        s.loop_nanos.load(Relaxed) as f64 / 1.0e6,
        s.incr_attempts.load(Relaxed),
        s.incr_hits.load(Relaxed),
        s.incr_fallbacks.load(Relaxed),
    );
    let misses = s.miss_calls.load(Relaxed).max(1);
    safe_eprintln!(
        "[ALGEBRAIC-STATS]   miss_calls={} avg_equations={:.2} avg_rounds={:.2} eq_max={}",
        s.miss_calls.load(Relaxed),
        s.eq_sum.load(Relaxed) as f64 / misses as f64,
        s.round_sum.load(Relaxed) as f64 / misses as f64,
        s.eq_max.load(Relaxed),
    );
}

impl LiaSolver<'_> {
    /// Current input stamp for the `detect_algebraic_equalities` memo.
    ///
    /// See [`AlgebraicDetectStamp`] for why these four revisions plus the
    /// propagated-pairs length cover every input the detection reads.
    fn algebraic_detect_stamp(&self) -> AlgebraicDetectStamp {
        AlgebraicDetectStamp {
            view_epoch: self.assertion_view_cache.epoch(),
            shared_eq_revision: self.shared_eq_revision,
            bound_revision: self.lra.bound_revision(),
            var_index_epoch: self.var_index_epoch,
            propagated_pairs_len: self.propagated_equality_pairs.len(),
        }
    }

    /// Detect algebraic equalities from asserted and shared equalities.
    ///
    /// Returns a list of `(term, value, reasons)` for variables whose values
    /// were uniquely determined by the system of shared equalities (Gaussian
    /// elimination). These are NOT stored in LRA's bounds, so the caller
    /// must feed them into `propagate_tight_bound_equalities` alongside
    /// LRA-derived tight bounds.
    pub(super) fn detect_algebraic_equalities(
        &mut self,
        debug: bool,
    ) -> Vec<(TermId, BigRational, Vec<TheoryLit>)> {
        let stats = algebraic_stats();
        if !stats.enabled {
            return self.detect_algebraic_equalities_inner(debug);
        }
        use std::sync::atomic::Ordering::Relaxed;
        let t0 = ay_core::time::Instant::now();
        let r = self.detect_algebraic_equalities_inner(debug);
        stats
            .nanos
            .fetch_add(t0.elapsed().as_nanos() as u64, Relaxed);
        let n = stats.calls.fetch_add(1, Relaxed) + 1;
        if n.is_multiple_of(20000) {
            algebraic_stats_dump();
        }
        r
    }

    fn detect_algebraic_equalities_inner(
        &mut self,
        debug: bool,
    ) -> Vec<(TermId, BigRational, Vec<TheoryLit>)> {
        self.detect_algebraic_calls += 1;
        // #probe-rref-memo: a conflict PROBE re-runs this from scratch on every
        // one-at-a-time shared-equality add. Route those calls through the
        // incremental reason-free conflict predictor, which reuses the prior
        // elimination state across the append-only adds and only pays the full
        // reason-carrying recompute when it predicts a conflict (the rare case).
        // Sound by construction: see `detect_algebraic_probe`.
        if self.conflict_probe
            && !self.shared_equalities.is_empty()
            && !self.skip_shared_algebraic
            && algebraic_probe_incremental_enabled()
        {
            return self.detect_algebraic_probe(debug);
        }
        self.detect_algebraic_full(debug)
    }

    fn detect_algebraic_full(&mut self, debug: bool) -> Vec<(TermId, BigRational, Vec<TheoryLit>)> {
        // Memo: the detection is a deterministic pure function of the stamped
        // inputs (see AlgebraicDetectStamp), and on a stamp hit its appends to
        // pending_equalities/propagated_equality_pairs are provably empty
        // (every Case-2 pair was already recorded when the cached run exited),
        // so returning the cached conflict-free result is behaviour-identical.
        // Conflict runs are never cached (see the exit sites below).
        let stamp = self.algebraic_detect_stamp();
        if algebraic_detect_cache_enabled() {
            if let Some((cached_stamp, cached)) = &self.detect_algebraic_cache {
                if *cached_stamp == stamp {
                    self.detect_algebraic_cache_hits += 1;
                    return cached.clone();
                }
            }
        }
        // #probe-rref-memo: sub-phase profiling (zero cost unless enabled).
        let prof = algebraic_stats().enabled;
        let t_scan = if prof {
            Some(ay_core::time::Instant::now())
        } else {
            None
        };

        // Collect tight-bound values from LRA for potential substitution
        let mut tight_bound_values: HashMap<TermId, BigRational> = HashMap::default();
        let mut initial_tight: HashSet<TermId> = HashSet::default();
        // #probe-rref-memo companion: borrow the bounds instead of cloning
        // them — a `Bound` clone copies its reason/scale vectors, and this
        // scan runs over EVERY integer var on EVERY probe-loop check (the
        // `detect_algebraic_equalities` memo misses on each probe step
        // because the step itself bumps `shared_eq_revision`).
        for &var_term in &self.integer_vars {
            if let Some((Some(lower), Some(upper))) = self.lra.get_bounds_ref(var_term) {
                if lower.value == upper.value && !lower.strict && !upper.strict {
                    tight_bound_values.insert(var_term, lower.value.to_big());
                    initial_tight.insert(var_term);
                }
            }
        }
        if let (true, Some(t)) = (prof, t_scan) {
            algebraic_stats().scan_nanos.fetch_add(
                t.elapsed().as_nanos() as u64,
                std::sync::atomic::Ordering::Relaxed,
            );
        }
        let t_collect = if prof {
            Some(ay_core::time::Instant::now())
        } else {
            None
        };

        // Track derived tight bounds with their reasons (#3581)
        let mut derived_tight_bounds: Vec<(TermId, BigRational, Vec<TheoryLit>)> = Vec::new();
        // #8742: Reasons for derived tight bounds, keyed by var.
        // When a tight bound is added in a prior round by Case 1, a later
        // substitution must pull the *derivation* reasons (not just the LRA
        // bound's own reasons, which may be empty if the bound was never
        // asserted to LRA). Without this, Case 0 can reduce an equation to
        // `0 = c` with a reason set that omits the tight-bound derivations,
        // yielding a false-UNSAT conflict on SAT-decided atoms.
        let mut derived_tight_reasons: HashMap<TermId, Vec<TheoryLit>> = HashMap::default();

        // Collect all equations: both from asserted literals and shared equalities (#3581).
        //
        // Each equation is (var_coeffs, constant, initial_reasons) where:
        //   Σ(coeff_i * var_i) = constant
        // Shared equalities come from EUF via assert_shared_equality and represent
        // constraints like f(0) = x or f(1) = f(0) - x. Without including these,
        // variables introduced only via shared equalities are invisible to the
        // algebraic detection, breaking theory combination for chains like:
        //   f(0) = x, f(1) = f(0) - x → f(1) = 0
        let mut equations: Vec<(HashMap<TermId, BigInt>, BigInt, Vec<TheoryLit>)> = Vec::new();

        // Equations from assertion view (positive equalities from assert_literal)
        for &literal in &self.assertion_view().positive_equalities {
            if let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) {
                if name != "=" || args.len() != 2 {
                    continue;
                }
                // #7451: Skip non-arithmetic equalities. In QF_SLIA, LIA receives
                // String-sorted equalities like `substr(x,0,1) = sk_res` because
                // they contain `str.substr` (a string-int bridge op). The Gaussian
                // elimination treats opaque non-Int terms as variables with
                // coefficient 1, producing spurious cross-sort equalities
                // (e.g., x:String = 0:Int) that cause false UNSAT via EUF.
                let lhs_sort = self.terms.sort(args[0]);
                let rhs_sort = self.terms.sort(args[1]);
                if !matches!(lhs_sort, Sort::Int | Sort::Real)
                    || !matches!(rhs_sort, Sort::Int | Sort::Real)
                {
                    continue;
                }
                let (var_coeffs, constant) = self.parse_linear_expr_with_vars(args[0], args[1]);
                let initial_reason = TheoryLit::new(literal, true);
                equations.push((var_coeffs, constant, vec![initial_reason]));
            }
        }

        // Equations from shared equalities (from assert_shared_equality, #3581)
        for &(lhs, rhs, ref reasons) in &self.shared_equalities {
            // #7451: Sort-guard shared equalities too. EUF→LIA propagation is
            // already filtered in StringsLiaSolver::check(), but apply the same
            // guard here defensively.
            let lhs_sort = self.terms.sort(lhs);
            let rhs_sort = self.terms.sort(rhs);
            if !matches!(lhs_sort, Sort::Int | Sort::Real)
                || !matches!(rhs_sort, Sort::Int | Sort::Real)
            {
                continue;
            }
            let (var_coeffs, constant) = self.parse_linear_expr_with_vars(lhs, rhs);
            equations.push((var_coeffs, constant, reasons.clone()));
        }

        if equations.is_empty() {
            // Conflict-free exit: cache the (empty) result. The stamp taken
            // at entry is still current — nothing above mutates stamped state.
            if algebraic_detect_cache_enabled() {
                self.detect_algebraic_cache = Some((stamp, Vec::new()));
            }
            return vec![];
        }

        if prof {
            use std::sync::atomic::Ordering::Relaxed;
            let s = algebraic_stats();
            s.miss_calls.fetch_add(1, Relaxed);
            s.eq_sum.fetch_add(equations.len() as u64, Relaxed);
            s.eq_max.fetch_max(equations.len() as u64, Relaxed);
        }

        // Iterative Gaussian-style elimination (#3581):
        //
        // Process all equations, substituting known tight-bound values and
        // deriving new ones. When a shared equality like f(0) = x reduces to
        // "f(0) - x = 0", we first learn that f(0) and x are equal. If another
        // shared equality then reduces a single variable (e.g., f(1) = 0 after
        // substituting f(0) = x into f(1) = f(0) - x), we add a tight bound.
        // Repeat until no new equalities or bounds are found.
        //
        // We also maintain a map of variable-to-variable equalities so we can
        // substitute equal variables (not just tight-bound constants).
        if let (true, Some(t)) = (prof, t_collect) {
            algebraic_stats().collect_nanos.fetch_add(
                t.elapsed().as_nanos() as u64,
                std::sync::atomic::Ordering::Relaxed,
            );
        }
        let t_loop = if prof {
            Some(ay_core::time::Instant::now())
        } else {
            None
        };

        let mut var_equalities: HashMap<TermId, TermId> = HashMap::default();
        // Reasons for variable-to-variable equalities (for proof tracking).
        let mut var_eq_reasons: HashMap<(TermId, TermId), Vec<TheoryLit>> = HashMap::default();

        let mut new_equalities: Vec<DiscoveredEquality> = Vec::new();
        let mut new_pairs: HashSet<(TermId, TermId)> = HashSet::default();

        // Fixed-point loop: keep processing until no new substitutions
        let mut changed = true;
        let max_rounds = 10; // Prevent infinite loops
        let mut round = 0;
        while changed && round < max_rounds {
            changed = false;
            round += 1;

            for (eq_idx, (ref var_coeffs, ref constant, ref initial_reasons)) in
                equations.iter().enumerate()
            {
                let mut coeffs = var_coeffs.clone();
                let mut adj_constant = BigRational::from(constant.clone());
                let mut reasons: Vec<TheoryLit> = initial_reasons.clone();
                let mut reason_seen: HashSet<TheoryLit> = reasons.iter().copied().collect();

                // Substitute known tight-bound values.
                //
                // PERF (verification-consumer ghost-collection timeouts): only this
                // equation's own variables can be substituted, so scan the
                // (small) coefficient map instead of collecting and sorting
                // the full tight-bound map for every equation in every round.
                // The substitution set and order (ascending TermId) are
                // identical to the previous full-map scan: this loop only
                // ever REMOVES variables from `coeffs` and never mutates
                // `tight_bound_values`, so the substituted variables are
                // exactly `coeffs ∩ tight_bound_values` either way.
                let mut relevant_bound_vars: Vec<TermId> = coeffs
                    .keys()
                    .filter(|v| tight_bound_values.contains_key(*v))
                    .copied()
                    .collect();
                relevant_bound_vars.sort_unstable_by_key(|tid| tid.0);
                for var in &relevant_bound_vars {
                    let val = &tight_bound_values[var];
                    if let Some(coeff) = coeffs.remove(var) {
                        let coeff_rat = BigRational::from(coeff);
                        adj_constant -= &coeff_rat * val;

                        if debug {
                            safe_eprintln!(
                                "[LIA N-O Algebraic]   Substituted {} = {} (tight bound)",
                                var.0,
                                val,
                            );
                        }

                        // Add tight bound reasons (borrowed — read-only use)
                        if let Some((Some(lower), Some(upper))) = self.lra.get_bounds_ref(*var) {
                            if lower.value == upper.value && !lower.strict && !upper.strict {
                                for (reason, val) in
                                    lower.reasons.iter().zip(lower.reason_values.iter())
                                {
                                    let lit = TheoryLit::new(*reason, *val);
                                    if reason_seen.insert(lit) {
                                        reasons.push(lit);
                                    }
                                }
                                for (reason, val) in
                                    upper.reasons.iter().zip(upper.reason_values.iter())
                                {
                                    let lit = TheoryLit::new(*reason, *val);
                                    if reason_seen.insert(lit) {
                                        reasons.push(lit);
                                    }
                                }
                            }
                        }

                        // #8742: Also pull derivation reasons for tight bounds
                        // that were derived in Case 1 during the current
                        // Gaussian pass (or a prior round). These bounds are
                        // NOT asserted into LRA — `self.lra.get_bounds` returns
                        // None or an empty-reason bound for them. Without this
                        // fallback, Case 0 can emit a conflict clause missing
                        // the provenance of substituted bounds, producing a
                        // false UNSAT on SAT-decided atoms (e.g., QF_AUFLIA
                        // bridge/quantifier tests: quantifier_consumer_ext_eq_7956,
                        // bridge_value_reason_mismatch_6930).
                        if let Some(derived_reasons) = derived_tight_reasons.get(var) {
                            for r in derived_reasons {
                                if reason_seen.insert(*r) {
                                    reasons.push(*r);
                                }
                            }
                        }
                    }
                }

                // Substitute known variable equalities (#3581):
                // If we know var_a = var_b, replace var_a with var_b in the equation.
                //
                // PERF (verification-consumer ghost-collection timeouts): as with tight
                // bounds above, scan only this equation's variables instead of
                // collecting and sorting the full `var_equalities` map per
                // equation. The previous code visited every map entry once, in
                // ascending `from_var` order, substituting when `coeffs`
                // contained `from_var` AT VISIT TIME. Substituting from→to can
                // INSERT `to` into `coeffs`; under the old ascending scan such
                // a `to` was substituted in the same pass iff `to > from`
                // (its entry had not been passed yet). The ascending worklist
                // below replicates that exactly: pops are monotonically
                // increasing, and a newly-introduced `to` is enqueued only
                // when it has its own mapping — `to <= from` entries stay
                // un-substituted this pass, identically to the old scan (the
                // outer fixed-point round picks them up when anything
                // changed). A worklist var whose coefficient was cancelled to
                // zero before its pop is skipped by the `coeffs.remove`
                // guard, again identically.
                let mut pending: std::collections::BTreeSet<TermId> = coeffs
                    .keys()
                    .filter(|v| var_equalities.contains_key(*v))
                    .copied()
                    .collect();
                while let Some(from_var) = pending.pop_first() {
                    let to_var = var_equalities[&from_var];
                    if let Some(coeff) = coeffs.remove(&from_var) {
                        *coeffs.entry(to_var).or_insert_with(|| BigInt::from(0)) += &coeff;
                        if coeffs.get(&to_var) == Some(&BigInt::from(0)) {
                            coeffs.remove(&to_var);
                        } else if to_var > from_var && var_equalities.contains_key(&to_var) {
                            pending.insert(to_var);
                        }
                        // Add reasons for this variable equality
                        let canon_pair = if from_var.0 < to_var.0 {
                            (from_var, to_var)
                        } else {
                            (to_var, from_var)
                        };
                        if let Some(eq_reasons) = var_eq_reasons.get(&canon_pair) {
                            for r in eq_reasons {
                                if reason_seen.insert(*r) {
                                    reasons.push(*r);
                                }
                            }
                        }
                    }
                }

                // Remove zero coefficients
                coeffs.retain(|_, c| !c.is_zero());

                // Convert adjusted constant to BigInt
                let final_constant = if adj_constant.denom().is_one() {
                    adj_constant.numer().clone()
                } else {
                    continue;
                };

                if debug {
                    safe_eprintln!(
                        "[LIA N-O Algebraic] Eq {}: {} vars, constant={} (round {})",
                        eq_idx,
                        coeffs.len(),
                        final_constant,
                        round,
                    );
                }

                // Case 0 (#8783): Zero variables with a non-zero constant is an
                // immediate contradiction. After Gaussian substitution through
                // `var_equalities` and `tight_bound_values`, an equation of the
                // form `0 = c` (c != 0) means the accumulated set of shared
                // equalities is inconsistent. Without this guard, QF_UFLIA
                // formulas like `(f x) = x /\ (f x) = x+1` silently drop the
                // contradiction: Eq0 (x = f(x)) propagates the var-equality,
                // and Eq1 (f(x) = x+1) then reduces to `0 = 1` via substitution
                // — which Cases 1/2 both ignore. Report the conflict using the
                // accumulated reasons (which include the initial reasons of the
                // current equation PLUS the reasons attached to every
                // var-equality / tight-bound that was substituted in).
                if coeffs.is_empty() && !final_constant.is_zero() {
                    if debug {
                        safe_eprintln!(
                            "[LIA N-O Algebraic] Eq {}: reduced to 0 = {} — UNSAT ({} reasons)",
                            eq_idx,
                            final_constant,
                            reasons.len(),
                        );
                        for (i, r) in reasons.iter().enumerate() {
                            safe_eprintln!(
                                "[LIA N-O Algebraic]   reason[{}]: term={:?} value={} -> {:?}",
                                i,
                                r.term,
                                r.value,
                                self.terms.get(r.term),
                            );
                        }
                    }
                    // #shared-eq-core: a conflict PROBE deliberately asserts the
                    // shared equalities with EMPTY reasons — it only consumes the
                    // sat/unsat verdict, never the explanation — so the
                    // non-empty-reasons invariant is a real-solver invariant only.
                    debug_assert!(
                        self.conflict_probe || !reasons.is_empty(),
                        "BUG: LIA detect_algebraic_equalities: Case 0 conflict with empty reasons \
                         (eq_idx={eq_idx}, final_constant={final_constant})",
                    );
                    // Guard against empty reasons defensively: if we ever hit
                    // this in release, prefer returning no-propagation over a
                    // useless empty conflict clause.
                    if !reasons.is_empty() {
                        self.pending_shared_eq_conflict = Some(reasons);
                        // Clear any partial propagation state from this pass —
                        // the caller will report the conflict on the next
                        // `propagate_equalities()` call.
                        self.pending_equalities.clear();
                        return Vec::new();
                    }
                }

                // Case 1: Single variable with a fixed value → tight bound (#3581)
                // coeff * var = constant → var = constant / coeff
                if coeffs.len() == 1 {
                    let (&var, coeff) = coeffs.iter().next().unwrap();
                    if !coeff.is_zero() {
                        let value = BigRational::from(final_constant.clone())
                            / BigRational::from(coeff.clone());
                        if value.is_integer() && !tight_bound_values.contains_key(&var) {
                            if debug {
                                safe_eprintln!(
                                    "[LIA N-O Algebraic]   Derived tight bound: {} = {} ({} reasons)",
                                    var.0,
                                    value,
                                    reasons.len(),
                                );
                            }
                            tight_bound_values.insert(var, value.clone());
                            // #8742: Remember the derivation reasons so later
                            // substitutions can attach them to the eq being
                            // rewritten. Without this, Case 0 emits UNSAT
                            // clauses that omit the tight-bound provenance.
                            if !initial_tight.contains(&var) {
                                derived_tight_reasons.insert(var, reasons.clone());
                                derived_tight_bounds.push((var, value, reasons.clone()));
                            }
                            changed = true;
                        }
                    }
                }

                // Case 2: Two variables with opposite unit coefficients → equality
                if coeffs.len() == 2 && final_constant.is_zero() {
                    let mut entries: Vec<_> = coeffs.iter().collect();
                    entries.sort_by_key(|(&var, _)| var);
                    let (var_a, coeff_a) = entries[0];
                    let (var_b, coeff_b) = entries[1];

                    if coeff_a == &-coeff_b.clone() && (coeff_a.abs() == BigInt::one()) {
                        let (lhs_var, rhs_var) = if coeff_a.is_positive() {
                            (*var_a, *var_b)
                        } else {
                            (*var_b, *var_a)
                        };

                        let pair = if lhs_var.0 < rhs_var.0 {
                            (lhs_var, rhs_var)
                        } else {
                            (rhs_var, lhs_var)
                        };

                        if !self.propagated_equality_pairs.contains(&pair) && new_pairs.insert(pair)
                        {
                            if debug {
                                safe_eprintln!(
                                    "[LIA N-O Algebraic] Propagating: {} = {} (reasons: {})",
                                    lhs_var.0,
                                    rhs_var.0,
                                    reasons.len()
                                );
                            }

                            new_equalities.push(DiscoveredEquality::new(
                                lhs_var,
                                rhs_var,
                                reasons.clone(),
                            ));
                        }

                        // Record variable equality for substitution in other equations
                        if !var_equalities.contains_key(&lhs_var) {
                            var_equalities.insert(lhs_var, rhs_var);
                            var_eq_reasons.insert(pair, reasons.clone());
                            changed = true;
                        }
                    }
                }
            }
        }

        if let (true, Some(t)) = (prof, t_loop) {
            let s = algebraic_stats();
            s.loop_nanos.fetch_add(
                t.elapsed().as_nanos() as u64,
                std::sync::atomic::Ordering::Relaxed,
            );
            s.round_sum
                .fetch_add(round as u64, std::sync::atomic::Ordering::Relaxed);
        }

        for equality in new_equalities {
            let pair = if equality.lhs.0 < equality.rhs.0 {
                (equality.lhs, equality.rhs)
            } else {
                (equality.rhs, equality.lhs)
            };
            self.propagated_equality_pairs.insert(pair);
            self.pending_equalities.push(equality);
        }

        // Conflict-free exit: cache the result. Recompute the stamp — the
        // loop above grows `propagated_equality_pairs`, and the memo must
        // match the POST-run pair set (a hit means the Case-2 gate would
        // suppress every emission, making the skipped side effects empty).
        // The Case 0 conflict return above is deliberately NOT cached.
        if algebraic_detect_cache_enabled() {
            self.detect_algebraic_cache =
                Some((self.algebraic_detect_stamp(), derived_tight_bounds.clone()));
        }

        derived_tight_bounds
    }

    /// #probe-rref-memo: incremental, reason-free conflict predictor for a
    /// conflict PROBE's `detect_algebraic` calls. SOUND BY CONSTRUCTION.
    ///
    /// A probe consumes ONLY the Case-0 conflict verdict of `detect_algebraic`
    /// (`pending_shared_eq_conflict`); its return value, `pending_equalities`
    /// and `propagated_equality_pairs` are all write-only for a probe (never
    /// read to affect the returned `TheoryResult`). So this path only needs to
    /// reproduce the conflict VERDICT.
    ///
    /// It maintains [`ProbeAlgIncr`] — a reason-free integer-linear consistency
    /// state (union-find over equal vars + determined integer values + the
    /// still-live reduced equations) — extended across the probe's append-only
    /// shared-equality adds. The predictor uses the SAME derivation rules as
    /// `detect_algebraic_full` (integer tight-bound and unit variable-equality
    /// closure), so it flags a conflict on exactly the systems full would — up
    /// to derivation ORDER, which cannot change WHETHER a system reduces to
    /// `0 = c`.
    ///
    /// Both verdict directions are safe regardless of any predictor bug:
    ///   * predictor says CONFLICT → defer to `detect_algebraic_full`, which is
    ///     authoritative and builds the real reason-carrying pending conflict.
    ///     An over-prediction only wastes that recompute (this IS the fallback).
    ///   * predictor says NO CONFLICT → return the empty result with no pending
    ///     conflict. An under-prediction (missing a conflict full would find)
    ///     only costs the probe a minimisation step; the caller keeps the sound
    ///     full-closure over-approximation. Never a wrong answer.
    ///     In debug builds the no-conflict branch re-runs full and asserts it
    ///     also finds no conflict, so any divergence is caught in CI.
    fn detect_algebraic_probe(
        &mut self,
        debug: bool,
    ) -> Vec<(TermId, BigRational, Vec<TheoryLit>)> {
        use std::sync::atomic::Ordering::Relaxed;
        let stats = algebraic_stats();
        if stats.enabled {
            stats.incr_attempts.fetch_add(1, Relaxed);
        }

        let predicts_conflict = self.probe_incr_predict_conflict();

        if predicts_conflict {
            // Risky direction: the authoritative full recompute confirms and
            // builds the real (reason-carrying) pending conflict. THE FALLBACK.
            if stats.enabled {
                stats.incr_fallbacks.fetch_add(1, Relaxed);
            }
            return self.detect_algebraic_full(debug);
        }

        // Safe direction: no conflict predicted. Shadow-verify against full in
        // debug builds (the mandated debug-assert-vs-full-recompute).
        #[cfg(debug_assertions)]
        {
            let saved = self.pending_shared_eq_conflict.take();
            let _ = self.detect_algebraic_full(debug);
            let full_found = self.pending_shared_eq_conflict.take();
            debug_assert!(
                full_found.is_none(),
                "#probe-rref-memo divergence: incremental predicted NO conflict \
                 but detect_algebraic_full found one (shared_eqs={}, view_epoch={})",
                self.shared_equalities.len(),
                self.assertion_view_cache.epoch(),
            );
            self.pending_shared_eq_conflict = saved;
        }

        if stats.enabled {
            stats.incr_hits.fetch_add(1, Relaxed);
        }
        Vec::new()
    }

    /// Reason-free conflict prediction over the probe's current equation system,
    /// reusing [`ProbeAlgIncr`] across the append-only shared-equality adds.
    /// Returns true iff the integer-linear closure reduces some equation to
    /// `0 = c` (c != 0). See [`Self::detect_algebraic_probe`] for the safety
    /// argument — both answers are safe, so the reuse-validity heuristics below
    /// only affect performance, never soundness.
    fn probe_incr_predict_conflict(&mut self) -> bool {
        // Fresh integer tight-bound scan (same rule as detect_algebraic_full).
        let mut initial_tbv: HashMap<TermId, BigRational> = HashMap::default();
        for &var_term in &self.integer_vars {
            if let Some((Some(lower), Some(upper))) = self.lra.get_bounds_ref(var_term) {
                if lower.value == upper.value && !lower.strict && !upper.strict {
                    initial_tbv.insert(var_term, lower.value.to_big());
                }
            }
        }
        let view_epoch = self.assertion_view_cache.epoch();
        let shared_len = self.shared_equalities.len();

        // Reuse the cached state iff the FIXED inputs are unchanged and shared
        // equalities only grew: same assertion-view (view_epoch), the shared
        // trail is an append-extension, and every previously-seen initial tight
        // bound still holds at the same value (bounds are grow-only within a
        // probe's scope, so new pins are allowed and folded incrementally).
        let reuse = matches!(
            &self.probe_alg_incr,
            Some(st)
                if st.view_epoch == view_epoch
                    && shared_len >= st.shared_processed
                    && st.initial_tbv.iter().all(|(k, v)| initial_tbv.get(k) == Some(v))
        );

        if !reuse {
            let all_eqs = self.probe_collect_all_equations();
            let mut st = ProbeAlgIncr::new(view_epoch, initial_tbv, shared_len);
            st.seed_and_close(all_eqs);
            let conflict = st.conflict;
            self.probe_alg_incr = Some(st);
            return conflict;
        }

        // Incremental extension. Take the state out to decouple its &mut borrow
        // from the &self collection helpers below.
        let mut st = self.probe_alg_incr.take().expect("reuse implies Some");

        // (a) Fold any NEW initial tight-bound pins (grow-only).
        let new_pins: Vec<(TermId, BigRational)> = initial_tbv
            .iter()
            .filter(|(k, _)| !st.initial_tbv.contains_key(*k))
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        st.initial_tbv = initial_tbv;
        for (var, value) in new_pins {
            st.assign_value(var, value);
        }

        // (b) Parse and fold the newly-appended shared equalities.
        let new_eqs = self.probe_collect_shared_equations(st.shared_processed, shared_len);
        st.shared_processed = shared_len;
        for (coeffs, constant) in new_eqs {
            st.push_equation(coeffs, constant);
        }

        // (c) Re-close: a new pin or equation may cascade into live equations.
        st.close();

        let conflict = st.conflict;
        self.probe_alg_incr = Some(st);
        conflict
    }

    /// Reason-free collection of ALL detection equations (assertion-view
    /// positive equalities + shared equalities), mirroring the sort guards and
    /// parse of `detect_algebraic_full` but dropping every reason.
    fn probe_collect_all_equations(&self) -> Vec<(HashMap<TermId, BigInt>, BigInt)> {
        let mut eqs = Vec::new();
        for &literal in &self.assertion_view().positive_equalities {
            if let TermData::App(Symbol::Named(name), args) = self.terms.get(literal) {
                if name != "=" || args.len() != 2 {
                    continue;
                }
                let lhs_sort = self.terms.sort(args[0]);
                let rhs_sort = self.terms.sort(args[1]);
                if !matches!(lhs_sort, Sort::Int | Sort::Real)
                    || !matches!(rhs_sort, Sort::Int | Sort::Real)
                {
                    continue;
                }
                eqs.push(self.parse_linear_expr_with_vars(args[0], args[1]));
            }
        }
        for (coeffs, constant) in
            self.probe_collect_shared_equations(0, self.shared_equalities.len())
        {
            eqs.push((coeffs, constant));
        }
        eqs
    }

    /// Reason-free parse of the shared equalities in `[start, end)`, applying
    /// the same Int/Real sort guard as `detect_algebraic_full`.
    fn probe_collect_shared_equations(
        &self,
        start: usize,
        end: usize,
    ) -> Vec<(HashMap<TermId, BigInt>, BigInt)> {
        let mut eqs = Vec::new();
        for i in start..end {
            let (lhs, rhs, _) = &self.shared_equalities[i];
            let (lhs, rhs) = (*lhs, *rhs);
            let lhs_sort = self.terms.sort(lhs);
            let rhs_sort = self.terms.sort(rhs);
            if !matches!(lhs_sort, Sort::Int | Sort::Real)
                || !matches!(rhs_sort, Sort::Int | Sort::Real)
            {
                continue;
            }
            eqs.push(self.parse_linear_expr_with_vars(lhs, rhs));
        }
        eqs
    }
}

/// #probe-rref-memo: reason-free incremental integer-linear consistency state
/// for a conflict PROBE. Detects whether the accumulated equation system
/// reduces to `0 = c` (c != 0) under the SAME closure rules as
/// `detect_algebraic_full` (integer tight-bound derivations + unit
/// variable-equality merges), but carries NO reasons and produces NO output
/// equalities — a probe never consumes those.
///
/// Maintained across the probe's append-only shared-equality adds so each add
/// folds only the new equation(s) instead of re-eliminating the whole system.
pub(crate) struct ProbeAlgIncr {
    /// Assertion-view epoch the folded equations were built from.
    view_epoch: u64,
    /// Count of `shared_equalities` already folded in.
    shared_processed: usize,
    /// Snapshot of the LRA integer tight-bound scan used as the seed. Reused
    /// only while its entries still hold (grow-only) at the same value.
    initial_tbv: HashMap<TermId, BigRational>,
    /// Union-find parent map over variables (absence ⇒ the var is its own root).
    parent: HashMap<TermId, TermId>,
    /// Determined integer value per representative.
    val: HashMap<TermId, BigRational>,
    /// Folded equations (original coefficients over variables), with a `dead`
    /// flag set once an equation has been consumed into `val`/`parent` or is
    /// trivially satisfied — dead equations never yield further facts.
    eqs: Vec<ProbeEq>,
    /// Sticky: set once any equation reduces to `0 = c` (c != 0).
    conflict: bool,
}

struct ProbeEq {
    coeffs: HashMap<TermId, BigInt>,
    constant: BigInt,
    dead: bool,
}

/// Outcome of reducing one equation against the current closure.
enum ProbeReduce {
    /// `0 = c`, c != 0 — inconsistent.
    Conflict,
    /// Consumed: a new tight bound `rep = value` (Case 1).
    Value(TermId, BigRational),
    /// Consumed: a new variable equality `a = b` (Case 2, unit opposite).
    Merge(TermId, TermId),
    /// Trivially satisfied (`0 = 0`) — dead, no new fact.
    Trivial,
    /// Still live (≥2 reps, or a single non-integer-valued var).
    Live,
}

impl ProbeAlgIncr {
    /// Same round cap as `detect_algebraic_full`, so the closure's completeness
    /// matches full's exactly on any system that converges within the cap.
    const MAX_ROUNDS: u32 = 10;

    fn new(
        view_epoch: u64,
        initial_tbv: HashMap<TermId, BigRational>,
        shared_processed: usize,
    ) -> Self {
        ProbeAlgIncr {
            view_epoch,
            shared_processed,
            initial_tbv,
            parent: HashMap::default(),
            val: HashMap::default(),
            eqs: Vec::new(),
            conflict: false,
        }
    }

    /// Seed determined values from the initial tight-bound snapshot, fold every
    /// equation, and run the closure to a fixed point.
    fn seed_and_close(&mut self, eqs: Vec<(HashMap<TermId, BigInt>, BigInt)>) {
        // initial_tbv vars are each their own representative at seed time.
        let seed: Vec<(TermId, BigRational)> = self
            .initial_tbv
            .iter()
            .map(|(k, v)| (*k, v.clone()))
            .collect();
        for (var, value) in seed {
            self.assign_value(var, value);
        }
        for (coeffs, constant) in eqs {
            self.push_equation(coeffs, constant);
        }
        self.close();
    }

    /// Follow the union-find chain to the representative (no path compression;
    /// variable-equality chains are short).
    fn find(&self, mut v: TermId) -> TermId {
        while let Some(&p) = self.parent.get(&v) {
            v = p;
        }
        v
    }

    /// Assign `var`'s representative a determined value, flagging a conflict if
    /// it already has a different one.
    fn assign_value(&mut self, var: TermId, value: BigRational) {
        let rep = self.find(var);
        match self.val.get(&rep) {
            Some(existing) if *existing != value => self.conflict = true,
            Some(_) => {}
            None => {
                self.val.insert(rep, value);
            }
        }
    }

    /// Merge two variables' classes, propagating a determined value if one side
    /// has it (and flagging a conflict on inconsistent values).
    fn union(&mut self, a: TermId, b: TermId) {
        let ra = self.find(a);
        let rb = self.find(b);
        if ra == rb {
            return;
        }
        // Deterministic root: smaller TermId wins (matches nothing in full, but
        // conflict detection is representative-choice-invariant).
        let (keep, gone) = if ra.0 < rb.0 { (ra, rb) } else { (rb, ra) };
        self.parent.insert(gone, keep);
        if let Some(v_gone) = self.val.remove(&gone) {
            match self.val.get(&keep) {
                Some(v_keep) if *v_keep != v_gone => self.conflict = true,
                Some(_) => {}
                None => {
                    self.val.insert(keep, v_gone);
                }
            }
        }
    }

    /// Append an equation (live).
    fn push_equation(&mut self, coeffs: HashMap<TermId, BigInt>, constant: BigInt) {
        self.eqs.push(ProbeEq {
            coeffs,
            constant,
            dead: false,
        });
    }

    /// Reduce equation `i` against the current closure and classify it, using
    /// the SAME rules as `detect_algebraic_full` (Cases 0/1/2), minus reasons.
    fn reduce(&self, i: usize) -> ProbeReduce {
        let eq = &self.eqs[i];
        let mut rc: HashMap<TermId, BigInt> = HashMap::default();
        let mut rk = BigRational::from(eq.constant.clone());
        for (var, c) in &eq.coeffs {
            let rep = self.find(*var);
            if let Some(vv) = self.val.get(&rep) {
                // Substitute the determined value into the constant.
                rk -= BigRational::from(c.clone()) * vv;
            } else {
                *rc.entry(rep).or_insert_with(BigInt::zero) += c;
            }
        }
        rc.retain(|_, c| !c.is_zero());

        // A non-integer residual constant means full would `continue` (skip)
        // this equation this round — keep it live for a later substitution.
        if !rk.denom().is_one() {
            return ProbeReduce::Live;
        }
        let final_constant = rk.numer().clone();

        if rc.is_empty() {
            return if final_constant.is_zero() {
                ProbeReduce::Trivial
            } else {
                ProbeReduce::Conflict
            };
        }

        if rc.len() == 1 {
            let (&rep, coeff) = rc.iter().next().unwrap();
            if !coeff.is_zero() {
                let value =
                    BigRational::from(final_constant.clone()) / BigRational::from(coeff.clone());
                if value.is_integer() {
                    // The rep cannot already be valued (a valued rep would have
                    // been substituted out above), so this is always a new fact.
                    return ProbeReduce::Value(rep, value);
                }
            }
            return ProbeReduce::Live;
        }

        if rc.len() == 2 && final_constant.is_zero() {
            let mut entries: Vec<_> = rc.iter().collect();
            entries.sort_by_key(|(&var, _)| var);
            let (var_a, coeff_a) = entries[0];
            let (var_b, coeff_b) = entries[1];
            if coeff_a == &-coeff_b.clone() && coeff_a.abs() == BigInt::one() {
                return ProbeReduce::Merge(*var_a, *var_b);
            }
        }

        ProbeReduce::Live
    }

    /// Run the round-based closure to a fixed point (or the round cap), marking
    /// consumed equations dead and setting `conflict` on `0 = c`.
    fn close(&mut self) {
        if self.conflict {
            return;
        }
        let mut changed = true;
        let mut round = 0u32;
        while changed && round < Self::MAX_ROUNDS {
            changed = false;
            round += 1;
            for i in 0..self.eqs.len() {
                if self.eqs[i].dead {
                    continue;
                }
                match self.reduce(i) {
                    ProbeReduce::Conflict => {
                        self.conflict = true;
                        return;
                    }
                    ProbeReduce::Value(rep, value) => {
                        self.eqs[i].dead = true;
                        self.assign_value(rep, value);
                        if self.conflict {
                            return;
                        }
                        changed = true;
                    }
                    ProbeReduce::Merge(a, b) => {
                        self.eqs[i].dead = true;
                        self.union(a, b);
                        if self.conflict {
                            return;
                        }
                        changed = true;
                    }
                    ProbeReduce::Trivial => {
                        self.eqs[i].dead = true;
                    }
                    ProbeReduce::Live => {}
                }
            }
        }
    }
}
