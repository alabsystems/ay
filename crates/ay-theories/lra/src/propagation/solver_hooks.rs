// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

/// #inc-guard-memo kill switch: `AY_LRA_NO_GUARD_MEMO=1` restores the
/// unconditional O(num_vars) guard rescan on every SAT return (for
/// bisection/soundness debugging). Read once per process.
fn guard_memo_disabled() -> bool {
    static DISABLED: OnceLock<bool> = OnceLock::new();
    *DISABLED.get_or_init(|| {
        std::env::var("AY_LRA_NO_GUARD_MEMO").is_ok_and(|v| v != "0" && !v.is_empty())
    })
}

#[derive(Debug)]
pub(crate) struct AssignmentBoundViolation {
    pub(crate) var_index: usize,
    pub(crate) bound_kind: &'static str,
    pub(crate) value: InfRational,
    pub(crate) bound: InfRational,
    pub(crate) strict: bool,
}

impl LraSolver {
    /// Debug-only assertion that all variable values satisfy their current bounds.
    ///
    /// This is the core of verification gap #1: verify_model() for the LRA solver.
    /// Called before every Sat return path in check() to catch false-SAT bugs
    /// at their origin, before the result propagates to the DPLL loop.
    ///
    /// Uses InfRational comparison which encodes strict bounds as epsilon offsets:
    ///   non-strict lb: value >= (lb, 0)
    ///   strict lb:     value >= (lb, +1)  i.e. value > lb
    ///   non-strict ub: value <= (ub, 0)
    ///   strict ub:     value <= (ub, -1)  i.e. value < ub
    #[cfg(debug_assertions)]
    pub(crate) fn debug_assert_bounds_satisfied(&self) {
        use num_traits::One;
        for (vi, info) in self.vars.iter().enumerate() {
            if let Some(ref lb) = info.lower {
                let lb_inf = if lb.strict {
                    InfRational::new(lb.value_big(), BigRational::one())
                } else {
                    InfRational::from_rational(lb.value_big())
                };
                debug_assert!(
                    info.value >= lb_inf,
                    "LRA check() false-SAT: var {} value {:?} violates lower bound {} (strict={})",
                    vi,
                    info.value,
                    lb.value,
                    lb.strict
                );
            }
            if let Some(ref ub) = info.upper {
                let ub_inf = if ub.strict {
                    InfRational::new(ub.value_big(), -BigRational::one())
                } else {
                    InfRational::from_rational(ub.value_big())
                };
                debug_assert!(
                    info.value <= ub_inf,
                    "LRA check() false-SAT: var {} value {:?} violates upper bound {} (strict={})",
                    vi,
                    info.value,
                    ub.value,
                    ub.strict
                );
            }
        }
    }

    /// Return the first variable whose current value violates its lower or upper
    /// bound, if any. This is release-available so SAT paths can fail closed
    /// before an invalid LRA model reaches DPLL(T) model validation.
    ///
    /// Uses the same InfRational comparison semantics as the debug assertion:
    ///   non-strict lb: value >= (lb, 0)
    ///   strict lb:     value >= (lb, +1)  i.e. value > lb
    ///   non-strict ub: value <= (ub, 0)
    ///   strict ub:     value <= (ub, -1)  i.e. value < ub
    pub(crate) fn first_current_assignment_bound_violation(
        &self,
    ) -> Option<AssignmentBoundViolation> {
        use crate::rational::Rational;
        use crate::types::BoundType;
        for (var_index, info) in self.vars.iter().enumerate() {
            if let Some(ref lb) = info.lower {
                // Violated when value < lb (strict lb encodes +1ε). This is the
                // hot per-variable / per-check guard (#chc25-pure-rust-lra): use
                // the allocation-free `lt_bound` comparison instead of building
                // an `InfRational` via `value_big()`, which materialized a
                // `BigRational` from a `Small` value on every iteration.
                if info.value.lt_bound(&lb.value, lb.strict, BoundType::Lower) {
                    // Cold path (violation found): build the InfRational bound
                    // for the report — no `to_big`, stays in the `Rational` domain.
                    let bound = if lb.strict {
                        InfRational::new_rat(lb.value.clone(), Rational::Small(1, 1))
                    } else {
                        InfRational::from_rat(lb.value.clone())
                    };
                    return Some(AssignmentBoundViolation {
                        var_index,
                        bound_kind: "lower",
                        value: info.value.clone(),
                        bound,
                        strict: lb.strict,
                    });
                }
            }
            if let Some(ref ub) = info.upper {
                // Violated when value > ub (strict ub encodes -1ε).
                if info.value.gt_bound(&ub.value, ub.strict, BoundType::Upper) {
                    let bound = if ub.strict {
                        InfRational::new_rat(ub.value.clone(), Rational::Small(-1, 1))
                    } else {
                        InfRational::from_rat(ub.value.clone())
                    };
                    return Some(AssignmentBoundViolation {
                        var_index,
                        bound_kind: "upper",
                        value: info.value.clone(),
                        bound,
                        strict: ub.strict,
                    });
                }
            }
        }
        None
    }

    /// Fail closed if a SAT path is about to return with a stale LRA
    /// assignment. The next check must force simplex even when freshness flags
    /// were accidentally clear; otherwise the solver can loop on Unknown while
    /// repeatedly skipping simplex.
    /// `allow_memo`: propagation-time call sites pass `true` — their SAT
    /// results are intermediate (re-verified by the unconditional final-check
    /// guard before any verdict is emitted), so a scan-verified memo may skip
    /// the rescan. Final-verdict sites (`check_impl/*`) pass `false`: per
    /// #8810, final SAT returns must never trust freshness state — they always
    /// run the full scan.
    pub(crate) fn guard_sat_current_assignment_bounds(
        &mut self,
        result: &mut TheoryResult,
        phase: &'static str,
        allow_memo: bool,
    ) {
        if !matches!(result, TheoryResult::Sat) {
            return;
        }

        // #inc-guard-memo: skip the O(num_vars) rescan when a prior FULL SCAN
        // verified the current (values, bounds) pair violation-free and no
        // mutation site has run since (see `guard_clean_valid` in lib.rs for
        // the invalidation-site enumeration and soundness argument). The memo
        // is set only by a clean full scan — never by simplex feasibility
        // claims (a budget-capped propagate simplex can report Sat while a var
        // is out of bounds). Measured 3.3e9 redundant var-scans on a depth-14
        // hybrid_networks BMC trace.
        // Kill switch: AY_LRA_NO_GUARD_MEMO=1 restores the unconditional scan.
        if allow_memo && self.guard_clean_valid && !guard_memo_disabled() {
            // Memo hits must agree with the full scan; a mismatch means a
            // missed invalidation site (a soundness bug in the memo, caught
            // here in debug builds before it can mask a real violation).
            debug_assert!(
                self.first_current_assignment_bound_violation().is_none(),
                "guard memo claims clean but a bound violation exists — \
                 missed guard_clean_valid invalidation site"
            );
            if self.post_simplex_bounds_added {
                self.post_simplex_bounds_added = false;
            }
            return;
        }

        if let Some(violation) = self.first_current_assignment_bound_violation() {
            tracing::warn!(
                phase,
                var_index = violation.var_index,
                bound_kind = violation.bound_kind,
                value = ?violation.value,
                bound = ?violation.bound,
                strict = violation.strict,
                "LRA SAT demoted to Unknown: current assignment violates an active bound"
            );
            self.dirty = true;
            self.bounds_tightened_since_simplex = true;
            self.last_simplex_feasible = false;
            self.discard_lra_basis_region_candidate();
            // #warm-simplex: a violation slipped past the incremental
            // candidate tracking — fail safe by forcing the next simplex
            // through the full heap rebuild + full non-basic scan (which
            // re-arms the warm invariants). Without this, a warm-tracking gap
            // could livelock: targeted Sat -> guard demotes -> targeted Sat.
            if self.warm.enabled {
                self.heap_stale = true;
                self.warm_invalidate();
            }
            *result = TheoryResult::Unknown;
        } else {
            // #inc-guard-memo: full scan verified clean — memoize until the
            // next value/bound mutation. A full verification also restores
            // the tracked-only chain (#inc-guard-chain).
            self.guard_clean_valid = true;
            self.guard_tracked_only = true;
            if self.post_simplex_bounds_added {
                // The cached assignment satisfies every post-simplex bound, so
                // the one-shot SAT gate is settled for this invocation.
                self.post_simplex_bounds_added = false;
            }
        }
    }

    /// No-op: LRA has no integer learned cuts to replay.
    /// Required by `solve_incremental_split_loop_pipeline!` macro (line 164).
    pub fn replay_learned_cuts(&mut self) {
        // LRA does not accumulate learned cuts (that's LIA's branch-and-bound).
    }

    /// Identity: return self as the LRA solver.
    /// Required by `pipeline_map_incremental_split_conflict_clause!` macro
    /// which calls `$theory.lra_solver().collect_all_bound_conflicts(true)`.
    pub fn lra_solver(&self) -> &Self {
        self
    }

    /// Refresh simplex feasibility for propagate-time row analysis (#6987).
    ///
    /// Z3's `propagate_core()` runs `make_feasible()` before deriving LP-backed
    /// implications (reference/z3/src/smt/theory_lra.cpp:2254). AY's `propagate()`
    /// was running `compute_implied_bounds()` against a stale basis when BCP
    /// tightened bounds between check() calls.
    ///
    /// Returns `true` when the simplex state is feasible (safe to run row analysis).
    /// Returns `false` when infeasible (caller should skip row analysis and interval
    /// propagation — `check()` will report the actual conflict).
    pub(crate) fn refresh_simplex_for_propagate(&mut self) -> bool {
        if !self.bounds_tightened_since_simplex && self.last_simplex_feasible {
            return true;
        }
        // Bounds were tightened since last simplex — refresh feasibility.
        // Use propagation-time budget (#8003): tighter cap avoids unbounded
        // simplex during propagation. Budget exhaustion → Sat → skip row analysis.
        self.bounds_tightened_since_simplex = false;
        // #8187: refresh_simplex_for_propagate runs outside check_impl /
        // check_during_propagate_impl, so the check-entry clear does NOT fire
        // here. Reset the soundness gate flag to match the other simplex
        // completion sites — any cascade after this point should re-arm it.
        self.post_simplex_bounds_added = false;
        self.vars_tightened_since_simplex.clear();
        let result = self.dual_simplex_propagate();
        self.last_simplex_feasible = matches!(result, TheoryResult::Sat);
        if self.last_simplex_feasible {
            self.save_feasible_snapshot();
            // #warm-simplex: anchor the last-feasible value delta here.
            self.warm_reanchor_delta();
        } else if matches!(
            result,
            TheoryResult::Unsat(_) | TheoryResult::UnsatWithFarkas(_)
        ) {
            // #warm-simplex conflict recovery (see check_impl). check() will
            // re-derive and report the conflict from the (unchanged) bounds.
            self.warm_restore_last_feasible();
        }
        // Do not package conflicts here — check() owns conflict reporting.
        self.last_simplex_feasible
    }
}
