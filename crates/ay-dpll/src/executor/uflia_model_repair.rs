// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! #uflia-model-repair: §3.2 TARGETED model-repair lever for the UFLIA
//! model-rejection tail (the development design notes
//! lever.md §3.2).
//!
//! FAILURE CLASS. On the QF_UFLIA Hash tail, the search FINDS a sat candidate
//! (hash_sat_07_09 resume @~10s, 07_20 eager1 @~8s, 03_20's fused arm in
//! ≤0.5s of arm time) and dies at *validation*: cross-theory model extraction
//! merges UF/arith points the theories never equated, so a gate (strict
//! oracle / independent gate / `uf_table_conflict` discard) refutes the
//! candidate and fail-closes Sat -> Unknown. The shipped BLIND reactive
//! re-solve (#uflia-cong-repair-arm, `check_sat_guarded`) then re-runs the
//! whole arm pipeline from scratch: its eager first attempt re-wanders
//! (observed 130k decisions on 07_20; 1.6s of a 1.8s remnant window on
//! 03_20+fused) and, being blind, it deterministically re-finds the SAME
//! rejected assignment (07_09 at T:60: "same rejection").
//!
//! THE LEVER (env-gated, `AY_UFLIA_MODEL_REPAIR=1`, default off =
//! byte-identical): use the rejection EVIDENCE the gates already computed —
//! which assertions the candidate falsifies and the concrete colliding value
//! assignment — to make the ONE extra re-solve targeted instead of blind:
//!
//! 1. EVIDENCE PRESERVATION. `check_sat_guarded` snapshots the candidate
//!    model immediately before `emit_sat_verdict` (every rejecting gate
//!    erases `last_model`), and the `uf_table_conflict` discard
//!    (model/completion.rs) preserves the conflicted table names instead of
//!    erasing them (the relevancy design §7 gap).
//! 2. FALSIFIED-ASSERTION EXTRACTION. Re-evaluate the assertion window under
//!    the preserved candidate; the assertions that ground-evaluate `false`
//!    are the ones the gate refuted (same evaluator family as the strict
//!    gate).
//! 3. COLLIDING-ASSIGNMENT BLOCK. The falsified assertions' Int-variable
//!    leaves + the candidate's values for them are the colliding point
//!    (e.g. 07_09's `x1=0,x2=6,..,x7=7`, under which the ite-lifted hash
//!    chain equality is arithmetically unsatisfiable no matter how the UF
//!    tables are repaired). Install ONE blocking constraint
//!    `(not (and (= x1 0) ... (= x7 7)))` for the repair re-solve, so the
//!    search is forced OFF the colliding point instead of re-finding it.
//! 4. TARGETED RE-SOLVE. Re-solve ONCE with (a) the trap blocks installed,
//!    (b) the accept-point congruence-repair scan + finite-domain rescue
//!    armed (`arm_uflia_congruence_repair`, the machinery that already
//!    converts the sibling greens 05_14/06_12/07_11), and (c) the arm
//!    routing ADAPTED to the evidence class (see [`RepairRoute`]).
//!
//! SOUNDNESS IS STRUCTURAL, not analytic:
//! * SAT side — every repaired candidate re-enters `emit_sat_verdict`, the
//!   single SAT chokepoint, and passes the FULL unchanged gate battery
//!   (strict + independent + authoritative-failclosed + postcondition)
//!   against the ORIGINAL assertion window (the block is popped before
//!   emission). A bad repair degrades to `unknown`, never wrong-sat.
//! * UNSAT side — the blocking constraint is a heuristic search cut, NOT an
//!   entailed lemma, so an `unsat` produced while it was installed is
//!   TAINTED and is unconditionally suppressed to `unknown` (never emitted,
//!   no proof built). When no block was installed the re-solve solved the
//!   identical formula and its verdict flows through unchanged, exactly like
//!   the blind re-solve.
//! * The verdict path of every rejecting gate is untouched: this module only
//!   READS the evidence they already produce.

use ay_core::term::TermData;
use ay_core::{Sort, TermId};
use num_bigint::BigInt;

use super::model::EvalValue;
use super::Executor;
use crate::executor_types::{Result, SolveResult, UnknownReason};

/// Env gate for the §3.2 targeted model-repair lever. Default off; every
/// capture/repair site is behind this, so unset means byte-identical
/// behavior (the snapshot clone included).
pub(crate) fn uflia_model_repair_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| std::env::var("AY_UFLIA_MODEL_REPAIR").ok().as_deref() == Some("1"))
}

/// Routing shape for the repair re-solve.
///
/// DEFAULT (`AY_UFLIA_MODEL_REPAIR_ROUTE` unset): ADAPTIVE on the evidence
/// class, per-cell measurements on the classified tail (T:20, 3-5 runs):
///
/// * assertion-falsifying rejection (strict oracle / independent gate — the
///   evidence names concrete falsified assertions, so the trap blocks are
///   sharp) → `Eager`: force the EAGER arm as one full-window run (no
///   wander-abort reroute, no detour, no resume). The blocked eager run
///   steers straight off the trap to a fresh candidate (07_09: sat at 5.2s /
///   586 decisions where the hybrid re-solve burned the window in detour
///   spin + resume wander; 03_20+fused: sat at ~0.1s).
/// * table-conflict-only rejection (`uf_table_conflict` — no assertion
///   ground-falsifies, the block is the weaker whole-window fallback) →
///   `Hybrid`: the normal hybrid pipeline. Its converter on this class is
///   the fresh-restart RESUME over the harvested learned clauses (07_20:
///   sat at 10.8s where a single continuous eager run re-wanders 72k-123k
///   decisions).
///
/// Env overrides for A/B: `eager` / `hybrid` / `detour` (`detour` skips the
/// eager first attempt and enters the relevancy-hard lazy detour directly —
/// measured worst on this tail: the detour theory-spins without reaching an
/// N-O accept point).
enum RepairRoute {
    Eager,
    Hybrid,
    Detour,
}

fn uflia_model_repair_route(assertion_derived_evidence: bool) -> RepairRoute {
    match std::env::var("AY_UFLIA_MODEL_REPAIR_ROUTE").ok().as_deref() {
        Some("eager") => RepairRoute::Eager,
        Some("hybrid") => RepairRoute::Hybrid,
        Some("detour") => RepairRoute::Detour,
        _ if assertion_derived_evidence => RepairRoute::Eager,
        _ => RepairRoute::Hybrid,
    }
}

/// Cap on preserved rejected candidates per check-sat: each distinct
/// rejected candidate names one trap block. A solve rejects at most a
/// handful (in-attempt + gate); the cap fences pathological loops.
const MAX_REPAIR_CANDIDATES: usize = 4;

/// Push a rejected candidate model into the evidence buffer (capped,
/// oldest-first retention). Free function so capture sites that only hold
/// `&mut Vec<Model>` alongside other executor borrows can call it.
pub(crate) fn push_repair_candidate(
    buf: &mut Vec<super::model::Model>,
    model: super::model::Model,
) {
    if buf.len() < MAX_REPAIR_CANDIDATES {
        buf.push(model);
    }
}

/// Assertion-window cap for the falsified-assertion sweep: evaluation is
/// memoized and the target family carries a few hundred assertions, but an
/// adversarial window must not turn the repair into its own spin.
const MAX_REPAIR_SWEEP_ASSERTIONS: usize = 4_096;
/// Cap on blocked Int leaves: one SAT-visible atom each. The Hash family
/// carries 7; the cap fences degenerate formulas. Blocking a PARTIAL
/// assignment blocks a superset region — a completeness heuristic only,
/// never a soundness concern (see module docs).
const MAX_REPAIR_BLOCK_LEAVES: usize = 16;
/// Minimum leaves for a block to be installed: a 1-leaf block excludes every
/// model sharing a single coordinate — too coarse to be a "colliding point".
const MIN_REPAIR_BLOCK_LEAVES: usize = 2;
/// Traversal fence for the leaf walk.
const MAX_REPAIR_WALK_NODES: usize = 100_000;

impl Executor {
    /// The §3.2 TARGETED repair re-solve. Runs at most once per public
    /// check-sat (caller holds the `uflia_model_repair_done` latch), only on
    /// the UFLIA model-rejection path (`uflia_congruence_gate_rejected`),
    /// only under `AY_UFLIA_MODEL_REPAIR=1`, and only with deadline left.
    ///
    /// Returns the (possibly repaired) verdict; `unchanged` when no evidence
    /// was preserved. The blind re-solve (#uflia-cong-repair-arm) stays
    /// downstream of this and untouched: if the targeted re-solve does not
    /// mint a `Sat`, the caller's existing retry logic still applies.
    pub(super) fn uflia_targeted_model_repair_resolve(
        &mut self,
        unchanged: SolveResult,
    ) -> Result<SolveResult> {
        let debug = std::env::var_os("AY_DEBUG_READ_PIN").is_some();
        let candidates = std::mem::take(&mut self.uflia_repair_candidates);
        if debug {
            eprintln!("[model-repair] entry: candidates={}", candidates.len());
        }
        if candidates.is_empty() {
            return Ok(unchanged);
        }
        let conflict_tables = std::mem::take(&mut self.uflia_repair_conflict_tables);

        // (2) Falsified-assertion extraction, per rejected candidate:
        // ground re-evaluation of the window (the same concrete refutation
        // the strict/independent gates keyed on), plus the gate-named
        // assertion when it re-confirms `false` under that candidate (the
        // field is not reset per check-sat, so an unconfirmed stale pointer
        // must never steer the repair; read-only use of the gate's evidence
        // either way).
        let mut falsified: Vec<TermId> = Vec::new();
        for candidate in &candidates {
            if self.ctx.assertions.len() <= MAX_REPAIR_SWEEP_ASSERTIONS {
                for &assertion in &self.ctx.assertions.clone() {
                    if !falsified.contains(&assertion)
                        && matches!(
                            self.evaluate_term(candidate, assertion),
                            EvalValue::Bool(false)
                        )
                    {
                        falsified.push(assertion);
                    }
                }
            }
            if let Some(named) = self.last_rejected_array_assertion {
                if !falsified.contains(&named)
                    && matches!(self.evaluate_term(candidate, named), EvalValue::Bool(false))
                {
                    falsified.push(named);
                }
            }
        }
        let total_falsified = falsified.len();

        // (3) Trap blocks, by evidence regime (each regime is measured on
        // the classified tail — see the route docs above):
        // * ASSERTION-DERIVED (any candidate ground-falsifies an assertion):
        //   the colliding point is nameable — the falsified assertions' Int
        //   scalar leaves. Block EVERY rejected candidate's assignment over
        //   that shared leaf set: the whole family sits in the
        //   doomed-assignment regime, and leaving one rejected assignment
        //   unblocked measurably sends the repair run back into it (07_09:
        //   blocking both traps converts at ~5s; blocking only one wanders
        //   to the deadline).
        // * TABLE-CONFLICT (`uf_table_conflict`, nothing falsifies at
        //   assertion level): the inconsistency is intra-table — name the
        //   discarded assignment via the whole window's Int leaves (07_20:
        //   this fallback block is what converts where the blockless blind
        //   re-solve wanders 130k decisions).
        // * NEITHER (gate refutation the executor evaluator cannot
        //   re-derive): the trap is NOT nameable — a guess block measurably
        //   kills the class the armed accept-point machinery repairs IN
        //   PLACE (06_12: the blind re-solve converts by re-finding the
        //   SAME assignment and repairing it at accept). No blocks; the
        //   repair re-solve degenerates to the armed hybrid — the blind's
        //   own converging shape.
        let trap_leaves = if total_falsified > 0 {
            self.collect_int_scalar_leaves(&falsified)
        } else if !conflict_tables.is_empty() {
            self.collect_int_scalar_leaves(&self.ctx.assertions.clone())
        } else {
            Vec::new()
        };
        let mut blocks: Vec<Vec<(TermId, BigInt)>> = Vec::new();
        if !trap_leaves.is_empty() {
            for candidate in &candidates {
                let mut block_conjuncts: Vec<(TermId, BigInt)> = Vec::new();
                for &leaf in &trap_leaves {
                    if block_conjuncts.len() >= MAX_REPAIR_BLOCK_LEAVES {
                        break;
                    }
                    if let EvalValue::Rational(r) = self.evaluate_term(candidate, leaf) {
                        if r.is_integer() {
                            block_conjuncts.push((leaf, r.numer().clone()));
                        }
                    }
                }
                if block_conjuncts.len() >= MIN_REPAIR_BLOCK_LEAVES
                    && !blocks.contains(&block_conjuncts)
                {
                    blocks.push(block_conjuncts);
                }
            }
        }
        drop(candidates);

        // Install the trap blocks (heuristic search cuts; never validated
        // against, never allowed to license an unsat — see module docs).
        let assertions_before = self.ctx.assertions.len();
        let blocks_installed = blocks.len();
        for block_conjuncts in &blocks {
            let eqs: Vec<TermId> = block_conjuncts
                .iter()
                .map(|(leaf, value)| {
                    let c = self.ctx.terms.mk_int(value.clone());
                    self.ctx.terms.mk_eq(*leaf, c)
                })
                .collect();
            let conj = self.ctx.terms.mk_and(eqs);
            let block = self.ctx.terms.mk_not(conj);
            self.ctx.assertions.push(block);
        }

        // (4) Targeted re-solve: armed + routed, one shot.
        if debug {
            eprintln!(
                "[model-repair] blocks={} falsified={} route={}",
                blocks.len(),
                total_falsified,
                match uflia_model_repair_route(total_falsified > 0) {
                    RepairRoute::Eager => "eager",
                    RepairRoute::Hybrid => "hybrid",
                    RepairRoute::Detour => "detour",
                }
            );
        }
        self.arm_uflia_congruence_repair = true;
        match uflia_model_repair_route(total_falsified > 0) {
            RepairRoute::Eager => self.uflia_repair_eager_direct = true,
            RepairRoute::Detour => self.uflia_repair_detour_direct = true,
            RepairRoute::Hybrid => {}
        }
        self.last_unknown_reason = None;
        self.last_result = None;
        self.last_model = None;
        let retry = self.check_sat_internal();
        // Unconditional teardown BEFORE any early return: the routing/arming
        // flags must never outlive the repair re-solve, and the blocks must
        // never survive into the persistent assertion stack.
        self.arm_uflia_congruence_repair = false;
        self.uflia_repair_detour_direct = false;
        self.uflia_repair_eager_direct = false;
        self.ctx.assertions.truncate(assertions_before);
        let retry = retry?;
        let block_installed = blocks_installed > 0;

        self.last_statistics.set_int("model_repair.attempted", 1);
        self.last_statistics
            .set_int("model_repair.blocks", blocks_installed as u64);
        self.last_statistics
            .set_int("model_repair.falsified_assertions", total_falsified as u64);
        if !conflict_tables.is_empty() {
            self.last_statistics
                .set_string("model_repair.conflict_tables", conflict_tables.join(","));
        }

        if retry.is_unsat() {
            if block_installed {
                // TAINTED: derived under a non-entailed cut. Suppress to the
                // fail-closed Unknown the gate already produced; the caller's
                // blind re-solve (no cut) can still legitimately re-derive an
                // unsat afterwards.
                self.last_statistics
                    .set_int("model_repair.suppressed_unsat", 1);
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                self.last_result = Some(SolveResult::Unknown);
                self.last_model = None;
                self.last_proof = None;
                return Ok(SolveResult::Unknown);
            }
            // No cut installed: identical formula, mirror the blind path.
            if self.produce_proofs_enabled() && self.last_proof.is_none() {
                self.build_unsat_proof();
            }
        }
        // SAT/UNKNOWN (and untainted UNSAT) re-enter the single chokepoint:
        // full unchanged gate battery over the ORIGINAL window (block already
        // popped above).
        self.emit_sat_verdict(retry, &[])
    }

    /// Collect the Int-sorted scalar leaves (declared variables and nullary
    /// applications) reachable from `roots`, deduplicated, in deterministic
    /// TermId order. Bounded traversal.
    fn collect_int_scalar_leaves(&self, roots: &[TermId]) -> Vec<TermId> {
        let mut out: Vec<TermId> = Vec::new();
        let mut seen: std::collections::BTreeSet<TermId> = std::collections::BTreeSet::new();
        let mut stack: Vec<TermId> = roots.to_vec();
        let mut visited = 0usize;
        while let Some(term) = stack.pop() {
            if visited >= MAX_REPAIR_WALK_NODES || !seen.insert(term) {
                continue;
            }
            visited += 1;
            let is_leaf = match self.ctx.terms.get(term) {
                TermData::Var(_, _) => true,
                TermData::App(_, args) if args.is_empty() => true,
                _ => false,
            };
            if is_leaf {
                if matches!(self.ctx.terms.sort(term), Sort::Int) {
                    out.push(term);
                }
                continue;
            }
            stack.extend(self.ctx.terms.children(term));
        }
        out.sort_by_key(|t| t.0);
        out.dedup();
        out
    }
}
