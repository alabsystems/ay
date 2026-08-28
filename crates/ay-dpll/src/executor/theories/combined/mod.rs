// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Combined theory solving: UF+LRA, UF+NRA, AUFLIA, AUFLRA, BV+LIA.
//!
//! LIRA and AUFLIRA (mixed Int + Real) methods are in `lira`.

// #8529: Use deterministic hash maps/sets in all builds.
use ay_core::kani_compat::{DetHashMap as HashMap, DetHashSet as HashSet};
mod arrays_to_lia;
mod lira;

use crate::combined_solvers::combiner::{
    CrossTheoryEqualityReplay, EufArrayNotifyReplayState, TheoryCombiner,
};
use crate::combined_solvers::{UfNiaSolver, UfNraSolver};
use crate::executor::model::{EvalValue, Model};
use crate::executor::theories::solve_harness::{ProofProblemAssertionProvenance, TheoryModels};
use crate::executor_types::{Result, SolveResult, UnknownReason};
use crate::incremental_state::IncrementalTheoryState;
use ay_arrays::{ArrayPropagatedEqualityReplay, ExactSelectModelEqKey};
use ay_core::{Constant, Sort, Symbol, TermData, TermId, TermStore};
use ay_lia::LiaModel;
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};

/// M-A2 lazy-persistent-combiner shadow refutation class. A disagreement in
/// this partition is the wrong-verdict hazard; all other result variants keep
/// the authoritative fresh path undecided or refining.
#[cfg(debug_assertions)]
fn a2_shadow_refutes(result: &ay_core::TheoryResult) -> bool {
    matches!(
        result,
        ay_core::TheoryResult::Unsat(_) | ay_core::TheoryResult::UnsatWithFarkas(_)
    )
}

#[cfg(debug_assertions)]
fn a2_shadow_verdict_tag(result: &ay_core::TheoryResult) -> &'static str {
    match result {
        ay_core::TheoryResult::Sat => "Sat",
        ay_core::TheoryResult::Unsat(_) => "Unsat",
        ay_core::TheoryResult::UnsatWithFarkas(_) => "UnsatWithFarkas",
        ay_core::TheoryResult::Unknown => "Unknown",
        ay_core::TheoryResult::NeedSplit(_) => "NeedSplit",
        ay_core::TheoryResult::NeedDisequalitySplit(_) => "NeedDisequalitySplit",
        ay_core::TheoryResult::NeedExpressionSplit(_) => "NeedExpressionSplit",
        ay_core::TheoryResult::NeedExpressionSplits(_) => "NeedExpressionSplits",
        ay_core::TheoryResult::NeedStringLemma(_) => "NeedStringLemma",
        ay_core::TheoryResult::NeedLemmas(_) => "NeedLemmas",
        ay_core::TheoryResult::NeedModelEquality(_) => "NeedModelEquality",
        ay_core::TheoryResult::NeedModelEqualities(_) => "NeedModelEqualities",
        _ => "Other",
    }
}

#[cfg(debug_assertions)]
fn a2_shadow_clause_set(
    result: &ay_core::TheoryResult,
) -> Option<std::collections::BTreeSet<Vec<(u32, bool)>>> {
    let normalize = |lits: &[ay_core::TheoryLit]| -> Vec<(u32, bool)> {
        let mut normalized: Vec<(u32, bool)> =
            lits.iter().map(|lit| (lit.term.0, lit.value)).collect();
        normalized.sort_unstable();
        normalized.dedup();
        normalized
    };
    match result {
        ay_core::TheoryResult::Unsat(conflict) => {
            Some(std::iter::once(normalize(conflict)).collect())
        }
        ay_core::TheoryResult::NeedLemmas(lemmas) => Some(
            lemmas
                .iter()
                .map(|lemma| normalize(&lemma.clause))
                .collect(),
        ),
        _ => None,
    }
}

/// Drive one observational round on the create-once, warm-reset AUFLIA
/// combiner. The shadow owns a cloned term store and cannot mutate or replace
/// the authoritative fresh result.
///
/// REPLAY FIDELITY: the shadow must receive the same per-round input stream
/// as the authoritative fresh combiner or the differential reports phantom
/// divergences that implicate the warm-reset machinery falsely. Replayed
/// today: base-atom registration, applied theory lemmas, and the synced
/// literals WITH just-in-time registration of dynamic split atoms (mirroring
/// the fresh path's sync loop). KNOWN residual under-replay (none of which
/// has produced a divergence in the A2 suite): the structural snapshot
/// import (atom-cache only), the learned-cut / HNF / Diophantine import, and
/// `assert_top_level_arith_diseq_facts`. If a refutation-class divergence
/// appears, FIRST check whether the fresh path refuted through one of those
/// residual inputs before suspecting a warm-reset state drop.
#[cfg(debug_assertions)]
#[allow(clippy::too_many_arguments)]
fn a2_shadow_run_round<'store>(
    arena: &'store ay_lra::ShadowTermStoreArena,
    current_terms: &TermStore,
    combiner: &mut Option<TheoryCombiner<'store>>,
    interrupt: &Option<std::sync::Arc<std::sync::atomic::AtomicBool>>,
    deadline: Option<ay_core::time::Instant>,
    rescue_counter: &crate::executor::theories::split_incremental::SharedRescuePairCounter,
    fresh_result: &ay_core::TheoryResult,
    lits: &[(TermId, bool)],
    atoms: &HashSet<TermId>,
    lemmas: &[ay_core::TheoryLemma],
    engaged: &mut u64,
    skipped: &mut u64,
    warm_resets: &mut u64,
    verdict_disagree: &mut u64,
    verdict_kind_differ: &mut u64,
    reasonset_disagree: &mut u64,
    first_divergence: &mut Option<String>,
) {
    let current_len = current_terms.len();
    let in_current = |term: TermId| (term.0 as usize) < current_len;
    let replayable = lits.iter().all(|(term, _)| in_current(*term))
        && atoms.iter().all(|term| in_current(*term))
        && lemmas
            .iter()
            .all(|lemma| lemma.clause.iter().all(|lit| in_current(lit.term)));
    if !replayable {
        *skipped += 1;
        return;
    }

    let shadow_terms: &'store TermStore = arena.alloc(current_terms.clone());
    let snapshot_len = shadow_terms.len();
    match combiner {
        None => {
            let mut created = TheoryCombiner::auf_lia(shadow_terms);
            created.set_interrupt(interrupt.clone());
            created.set_deadline(deadline);
            created.set_rescue_pair_counter(Some(rescue_counter.clone()));
            *combiner = Some(created);
        }
        Some(existing) => {
            existing.rebind_terms(shadow_terms);
            ay_core::TheorySolver::soft_reset_warm(existing);
            *warm_resets += 1;
        }
    }
    let shadow = combiner
        .as_mut()
        .expect("shadow combiner was created or retained above");
    for &atom in atoms {
        ay_core::TheorySolver::register_atom(shadow, atom);
    }
    for lemma in lemmas {
        ay_core::TheorySolver::note_applied_theory_lemma(shadow, &lemma.clause);
    }
    for &(term, value) in lits {
        // Mirror the fresh path's per-round sync exactly: DYNAMIC split atoms
        // (minted by earlier refinement rounds, absent from the base
        // registration set) are registered immediately before their literal is
        // asserted — `assert_literal` on an unregistered atom is inert for the
        // arithmetic sub-solvers (the atom was never parsed into constraints).
        // Skipping this dropped every dynamic bound/equality atom from the
        // shadow's LIA view and produced FALSE refutation-class divergences
        // (fresh=UnsatWithFarkas over a dynamic-atom conflict vs
        // shadow=NeedModelEquality on the constraint-starved replay).
        if !atoms.contains(&term) {
            ay_core::TheorySolver::register_atom(shadow, term);
        }
        ay_core::TheorySolver::assert_literal(shadow, term, value);
    }
    let shadow_result = ay_core::TheorySolver::check(shadow);
    *engaged += 1;

    let fresh_tag = a2_shadow_verdict_tag(fresh_result);
    let shadow_tag = a2_shadow_verdict_tag(&shadow_result);
    if a2_shadow_refutes(fresh_result) != a2_shadow_refutes(&shadow_result) {
        *verdict_disagree += 1;
        if first_divergence.is_none() {
            *first_divergence = Some(format!(
                "REFUTATION-CLASS: fresh={fresh_tag} shadow={shadow_tag} (engaged round {})",
                *engaged
            ));
        }
        return;
    }
    if fresh_tag != shadow_tag {
        *verdict_kind_differ += 1;
        return;
    }
    if let (Some(fresh_set), Some(shadow_set)) = (
        a2_shadow_clause_set(fresh_result),
        a2_shadow_clause_set(&shadow_result),
    ) {
        let fresh_all_in = fresh_set.iter().all(|clause| {
            clause
                .iter()
                .all(|(term, _)| (*term as usize) < snapshot_len)
        });
        if fresh_all_in && fresh_set != shadow_set {
            *reasonset_disagree += 1;
            if first_divergence.is_none() {
                *first_divergence = Some(format!(
                    "reason-set ({fresh_tag}): fresh_clauses={} shadow_clauses={} (engaged round {})",
                    fresh_set.len(),
                    shadow_set.len(),
                    *engaged
                ));
            }
        }
    }
}

/// Collect arithmetic disequality variables from every root active in the
/// current solve.  Assumption-based AUFLIA keeps assumptions outside
/// `ctx.assertions`; collecting only that base window lets substitution
/// recovery overwrite an assumption-constrained tableau value.
fn collect_active_arith_diseq_vars(
    terms: &TermStore,
    roots: impl IntoIterator<Item = TermId>,
) -> HashSet<TermId> {
    let roots: Vec<TermId> = roots.into_iter().collect();
    crate::pipeline_fns::collect_top_level_arith_diseq_vars(terms, &roots)
}

/// Check if an assertion term recursively contains select/store operations
/// or array-sorted subterms. Unlike `involves_array` (which returns true for
/// all equalities), this only returns true when actual array content is present.
fn assertion_contains_array_ops(terms: &TermStore, term: TermId) -> bool {
    fn check(terms: &TermStore, term: TermId, visited: &mut HashSet<TermId>) -> bool {
        if !visited.insert(term) {
            return false;
        }
        if matches!(terms.sort(term), Sort::Array(_)) {
            return true;
        }
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                if matches!(name.as_str(), "select" | "store") {
                    return true;
                }
                args.iter().any(|&a| check(terms, a, visited))
            }
            TermData::Not(inner) => check(terms, *inner, visited),
            TermData::Ite(c, t, e) => {
                check(terms, *c, visited) || check(terms, *t, visited) || check(terms, *e, visited)
            }
            TermData::App(_, args) => args.iter().any(|&a| check(terms, a, visited)),
            _ => false,
        }
    }
    let mut visited = HashSet::default();
    check(terms, term, &mut visited)
}

fn is_quantifier_consumer_completion_marker_name(name: &str) -> bool {
    name.starts_with("__quantifier_consumer")
        || name.starts_with("__seq_")
        || name.starts_with("seq_")
        || name.starts_with("logic_")
        || name.starts_with("method_")
        || name == "buckets"
}

fn assertion_window_has_syntactic_contradiction(terms: &TermStore, assertions: &[TermId]) -> bool {
    let false_term = terms.false_term();
    let mut positives = HashSet::default();
    let mut negatives = HashSet::default();

    for &assertion in assertions {
        if assertion == false_term {
            return true;
        }
        if let TermData::Not(inner) = terms.get(assertion) {
            if positives.contains(inner) {
                return true;
            }
            negatives.insert(*inner);
        } else {
            if negatives.contains(&assertion) {
                return true;
            }
            positives.insert(assertion);
        }
    }

    false
}

fn assertion_window_has_top_level_not(terms: &TermStore, assertions: &[TermId]) -> bool {
    assertions
        .iter()
        .copied()
        .any(|assertion| matches!(terms.get(assertion), TermData::Not(_)))
}

fn uflia_lia_model_value_terms(terms: &TermStore, assertions: &[TermId]) -> HashSet<TermId> {
    fn is_arith_op(name: &str) -> bool {
        matches!(name, "+" | "-" | "*" | "div" | "mod" | "abs")
    }

    fn is_arith_predicate(name: &str) -> bool {
        matches!(name, "<" | "<=" | ">" | ">=")
    }

    fn contains_arith_op(terms: &TermStore, term: TermId, visited: &mut HashSet<TermId>) -> bool {
        if !visited.insert(term) {
            return false;
        }
        match terms.get(term) {
            TermData::App(sym, args) => {
                is_arith_op(sym.name())
                    || args
                        .iter()
                        .any(|&arg| contains_arith_op(terms, arg, visited))
            }
            TermData::Not(inner) => contains_arith_op(terms, *inner, visited),
            TermData::Ite(cond, then_term, else_term) => {
                contains_arith_op(terms, *cond, visited)
                    || contains_arith_op(terms, *then_term, visited)
                    || contains_arith_op(terms, *else_term, visited)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, value)| contains_arith_op(terms, *value, visited))
                    || contains_arith_op(terms, *body, visited)
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                contains_arith_op(terms, *body, visited)
                    || triggers
                        .iter()
                        .flatten()
                        .any(|&trigger| contains_arith_op(terms, trigger, visited))
            }
            TermData::Const(_) | TermData::Var(_, _) => false,
            _ => false,
        }
    }

    fn term_contains_arith_op(terms: &TermStore, term: TermId) -> bool {
        let mut visited = HashSet::default();
        contains_arith_op(terms, term, &mut visited)
    }

    fn collect_arith_expr(
        terms: &TermStore,
        term: TermId,
        out: &mut HashSet<TermId>,
        visited: &mut HashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        if matches!(terms.sort(term), Sort::Int) {
            out.insert(term);
        }
        match terms.get(term) {
            TermData::App(sym, args) if is_arith_predicate(sym.name()) => {
                for &arg in args {
                    collect_arith_expr(terms, arg, out, visited);
                }
            }
            TermData::App(sym, args) if is_arith_op(sym.name()) => {
                for &arg in args {
                    collect_arith_expr(terms, arg, out, visited);
                }
            }
            TermData::App(_, args) => {
                for &arg in args {
                    if term_contains_arith_op(terms, arg) {
                        collect_arith_expr(terms, arg, out, visited);
                    }
                }
            }
            TermData::Ite(cond, then_term, else_term) => {
                collect_formula(terms, *cond, out, visited);
                collect_arith_expr(terms, *then_term, out, visited);
                collect_arith_expr(terms, *else_term, out, visited);
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    if term_contains_arith_op(terms, *value) {
                        collect_arith_expr(terms, *value, out, visited);
                    }
                }
                collect_arith_expr(terms, *body, out, visited);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                collect_formula(terms, *body, out, visited);
                for &trigger in triggers.iter().flatten() {
                    if term_contains_arith_op(terms, trigger) {
                        collect_arith_expr(terms, trigger, out, visited);
                    }
                }
            }
            TermData::Not(_) | TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }

    fn collect_formula(
        terms: &TermStore,
        term: TermId,
        out: &mut HashSet<TermId>,
        visited: &mut HashSet<TermId>,
    ) {
        if !visited.insert(term) {
            return;
        }
        match terms.get(term) {
            TermData::App(sym, args) if is_arith_predicate(sym.name()) => {
                for &arg in args {
                    collect_arith_expr(terms, arg, out, visited);
                }
            }
            TermData::App(sym, args)
                if matches!(sym.name(), "=" | "distinct")
                    && args
                        .iter()
                        .all(|&arg| matches!(terms.sort(arg), Sort::Bool)) =>
            {
                for &arg in args {
                    collect_formula(terms, arg, out, visited);
                }
            }
            TermData::App(sym, args)
                if matches!(sym.name(), "=" | "distinct")
                    && args.iter().any(|&arg| term_contains_arith_op(terms, arg)) =>
            {
                for &arg in args {
                    collect_arith_expr(terms, arg, out, visited);
                }
            }
            TermData::App(sym, args)
                if matches!(sym.name(), "=" | "distinct")
                    && args.iter().all(|&arg| matches!(terms.sort(arg), Sort::Int)) =>
            {
                // #uflia-uf-eq-lia-keep (no_diseq_propagation_8455): a pure UF
                // Int (dis)equality — `(= (f a) (f b))`, no arithmetic operator
                // anywhere (the arm above did not match) — is forwarded to LIA
                // as a shared (dis)equality at assert time, so LIA's values for
                // the application sides are CONSTRAINED committed values, not
                // registration shadows. Dropping them left only EUF's
                // fabricated per-class integers: preprocessing (`a := 1`)
                // orphans the ORIGINAL `(f a)`/`(f b)` into fresh singleton
                // classes with DISTINCT fabricated values, and the committed
                // congruent row the table lookup needs (`f(1) -> 0`) resolved
                // to nothing (its result also stayed speculative) — the
                // independent gate then refuted the asserted equality and
                // degraded a genuine `sat` to `unknown`. Keeping the opaque
                // application sides lets the authoritative LIA merge commit
                // their values (and un-mark them speculative), so
                // the orphaned originals resolve through the committed row by
                // congruence. Model-content-only: the fail-closed validation
                // gates still re-check every assertion, so a kept value can
                // never admit a wrong `sat`.
                for &arg in args {
                    if matches!(terms.get(arg), TermData::App(_, _)) {
                        out.insert(arg);
                    }
                }
            }
            TermData::App(sym, args)
                if matches!(sym.name(), "and" | "or" | "=>" | "xor" | "not") =>
            {
                for &arg in args {
                    collect_formula(terms, arg, out, visited);
                }
            }
            TermData::App(_, args) => {
                for &arg in args {
                    if term_contains_arith_op(terms, arg) {
                        collect_arith_expr(terms, arg, out, visited);
                    }
                }
            }
            TermData::Not(inner) => collect_formula(terms, *inner, out, visited),
            TermData::Ite(cond, then_term, else_term) => {
                collect_formula(terms, *cond, out, visited);
                collect_formula(terms, *then_term, out, visited);
                collect_formula(terms, *else_term, out, visited);
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    collect_formula(terms, *value, out, visited);
                }
                collect_formula(terms, *body, out, visited);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                collect_formula(terms, *body, out, visited);
                for &trigger in triggers.iter().flatten() {
                    if term_contains_arith_op(terms, trigger) {
                        collect_arith_expr(terms, trigger, out, visited);
                    }
                }
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }

    let mut out = HashSet::default();
    let mut visited = HashSet::default();
    for &assertion in assertions {
        collect_formula(terms, assertion, &mut out, &mut visited);
    }
    out
}

/// #relevancy-lazy-routing: which split-loop arm(s) the QF_UFLIA lane runs.
///
/// See the development design notes. The design
/// prototype's conflict collapse on the branch-space-bound Hash family was
/// measured on the LAZY regime (plain per-round SAT solves, no live theory
/// extension) with the CNF-frontier relevancy brancher. The eager arm's
/// theory-aware branching prevents that regime, so the lane is routed:
///
/// - `Eager`: the pre-routing behaviour (eager arm only).
/// - `Lazy`: lazy arm only, relevancy HARD (the isolated prototype regime;
///   experimental — regresses eager-easy instances, never the default).
/// - `Hybrid`: eager arm first with the wander-abort trip-wire armed; when the
///   eager attempt WANDERS (it would otherwise burn the whole budget), run a
///   BOUNDED lazy DETOUR (relevancy HARD, capped at
///   `uflia_detour_conflict_budget()` conflicts and 40% of the remaining
///   wall budget); if the detour comes back undecided, RESUME the eager arm
///   (trip-wire disarmed) for the remainder of the budget. `unknown` is only
///   possible when BOTH arms fail — a trip-wire misfire on a
///   trajectory-sensitive eager green (wisas `xs_13_13`: eager wanders early
///   but converges by ~9.5s) costs only the bounded detour, never the
///   verdict. Baseline-easy instances finish inside the first eager attempt
///   untouched.
///
/// Soundness: each arm is a complete, independently gate-validated solve path
/// (the lazy arm is AUFLIA/AUFLRA's production path); switching between them
/// only changes the search trajectory, and an aborted/exhausted attempt
/// yields only `unknown` — every definitive verdict still comes from one
/// arm's full pipeline with its model-validation / verify-before-accept
/// gates intact. The detour caps are the solver's deterministic
/// conflict/decision budgets (machine-independent primary bound); the wall
/// fraction and per-round detour-deadline polls bound the experimental work.
// Every arm extracts models through `extract_uflia_theory_models`, keeping
// anchor recovery, substitution replay, composite recomputation, and
// uninterpreted-equality reunification in one shared path.
#[derive(Clone, Copy, PartialEq, Eq)]
enum UfliaSplitArm {
    Eager,
    Lazy,
    Hybrid,
}

/// Env-selected UFLIA split arm (`AY_UFLIA_ARM=eager|lazy|hybrid`).
/// Process-cached.
///
/// Default: `Hybrid`, a bounded lazy detour followed by a fresh eager resume
/// when the detour remains undecided. The detour is capped by conflicts,
/// decisions, and a fraction of the remaining wall-clock budget.
///
/// `AY_UFLIA_ARM=eager` restores the pre-routing pipeline byte-identically;
/// `lazy` is the isolated prototype regime (experimental — regresses
/// eager-easy instances).
///
/// Some dense lazy rounds can still spend too long in `LiaSolver::check` or
/// `augment_farkas_with_shared_reasons`; the detour budget limits their impact
/// on the hybrid route.
fn uflia_split_arm() -> UfliaSplitArm {
    // B23: the arm env spelling is retired; Hybrid is the shipped measured
    // default (the pure lazy arm regresses).
    UfliaSplitArm::Hybrid
}

/// Env-gated phase-timeline diagnostic for the UFLIA hybrid
/// (`AY_UFLIA_PHASE=1`): stderr-only prints at the eager-attempt / detour /
/// resume phase edges (wall elapsed, verdict, persistent-solver
/// conflict/decision counters). Measurement-only; never affects routing.
/// Process-cached.
fn uflia_phase_debug() -> bool {
    // B23: the phase-timeline diagnostic env is retired; flip for a
    // measurement run.
    false
}

/// Bounded lazy-DETOUR conflict budget for the hybrid arm
/// (#relevancy-lazy-routing). Calibrated to the campaign's 9 hybrid
/// conversions: the largest converts at ~2.2k lazy-arm conflicts (wisas
/// `xs_10_20`; Hash `03_11` at ~0.8k), so 10k covers them with >4x margin
/// while keeping a DIVERGING lazy re-run's detour to a bounded, small
/// fraction of the solve budget. Override: `AY_UFLIA_DETOUR_CONFLICTS`
/// (measurement/tuning only). Process-cached.
fn uflia_detour_conflict_budget() -> u64 {
    10_000
}

/// #detour-snapshot-extend: wall quantum for the SPECULATIVE detour
/// extension (`0` disables the extension entirely).
///
/// The bug class this closes (deadline-adaptive mis-allocation): the hybrid
/// detour's wall window is 40% of the REMAINING budget, so it scales with
/// the total deadline `T` — a detour whose work fits in W seconds converges
/// under a long `T` but is wall-killed mid-grind at a small `T` even when
/// `W < T` (measured on the prior campaign: wisas `xs_26_26`/`xs_32_32`/
/// `xs_33_43` and EufLa `hard14`/`hard16` all decided at T:60 but were
/// killed at T:20 with the deterministic conflict cap untouched,
/// conflicts <= 6, and the reclaimed time handed to an eager resume that
/// had already proven it wanders on exactly those files).
///
/// Why a naive extension cannot ship (measured, prior campaign): the detour
/// and the eager resume are a PIPELINE — the resume HARVESTS state the
/// detour leaves behind (term-store atoms, probe-trajectory state), and two
/// protected greens (Hash `hash_sat_03_09`, Wisa `xs-15-18-4-1-3-5`) are
/// decided by a conflict-trivial harvest resume (03_09: eager1 wanders 1272
/// conflicts, the baseline resume decides sat at THREE). Any in-flight
/// extension of the grind mutates the harvest and re-routes the resume
/// (03_09's 3-conflict resume became a 335-conflict wander), and no online
/// signal separates the converging grinds from the diverging-cheap-harvest
/// class.
///
/// The SNAPSHOT/EXACT-REPLAY primitive resolves this deterministically
/// instead of heuristically. The baseline detour runs UNTOUCHED to its soft
/// 40% window (byte-identical trajectory through the wall-kill, including a
/// straddling round's mid-round combiner cut). Only THEN, on an undecided
/// wall-killed theory-dominated detour with wall slack beyond the resume
/// reserve, the executor SNAPSHOTS every piece of mutable state the resume
/// can read (`ctx.terms`, the ay-lia thread-local probe state, the
/// `last_*` result/model/statistics fields, the conflict-verification
/// memo) and runs a bounded CONTINUATION detour on the same persistent
/// solver (warm VSIDS/phases/learned clauses). If the continuation DECIDES,
/// the verdict flows through the unchanged validation gates — pure win. If
/// it does NOT decide, the snapshot is RESTORED, so the subsequent eager
/// resume observes EXACTLY the state it would have seen without the
/// speculation: the baseline resume trajectory is reproduced BY
/// CONSTRUCTION, and the only cost is the bounded wall time of the failed
/// attempt (which the resume reserve keeps out of the resume's slice).
///
/// Soundness: pure scheduling. Deadlines only bound how long each phase may
/// iterate; every verdict still comes from a full gate-validated round
/// (model-validation gate for sat, verify-before-accept for unsat), so
/// verdicts can flip only between `unknown` and a decided verdict — never
/// sat<->unsat. The persistent solver's extra learned clauses are valid
/// implications of the same formula and die with the isolated incremental
/// state at `solve_uf_lia` exit.
///
/// The value is a CAP on the continuation's wall budget; the binding bound
/// in practice is `remaining - reserve` (the wall-budget principle: with
/// exact replay guaranteed, the speculation may use ALL slack beyond the
/// resume reserve — the measured budget arithmetic demands it, e.g. wisas
/// `xs_26_26` needs ~14.4s of total detour grind in an ~18s post-trip
/// budget: 7.2s soft window + ~7.3s extension + 3.5s reserve). The default
/// cap (20s) exists so a very long deadline cannot hand a diverging
/// theory-dominated grind an unbounded speculation. Override:
/// `AY_UFLIA_DETOUR_EXTEND_MS` (`0` disables the extension and restores
/// the fixed 40% window byte-identically). Process-cached.
fn uflia_detour_extend_quantum() -> Option<std::time::Duration> {
    Some(std::time::Duration::from_secs(20))
}

/// #detour-snapshot-extend: HARVEST-RESUME reserve — the extension's budget
/// is `min(quantum, remaining - reserve)`, never the raw wall. The reserve
/// guarantees a failed extension leaves the eager resume at least `reserve`
/// of wall (an extension only runs when the remaining budget after it still
/// covers the reserve, so a failed speculation delays the resume by at most
/// `quantum` while leaving it `reserve`). Files whose slack cannot cover the
/// reserve simply never extend (structurally-over-budget files like EufLa
/// `hard16` at T:20 stay red rather than gambling a green).
///
/// Value (2.0s): the reserve is a pure wall-budget trade between the
/// extension window and the post-extension resume window. The extension's
/// snapshot/exact-replay contract (see `uflia_detour_extend_quantum`) means
/// a *failed* extension restores the resume's INPUT state byte-for-byte
/// regardless of how long the extension ran, so the reserve's ONLY job is to
/// preserve enough wall for a resume that decides a green. A full-corpus
/// winning-phase audit of the QF_UFLIA sample (wisas/Wisa/Hash, T:20) found
/// ZERO greens decided by a *post-extension* resume: the eager-resume greens
/// the earlier 3.5s value protected (`hash_sat_03_09`, `xs-15-18-4-1-3-5`)
/// now converge via eager1 / the extension itself on this line, not a
/// reserve-gated resume. The 3.5s reserve was therefore withholding wall
/// from the extension for no measured green — and starving the
/// extension-convergence DEADLINE files that decide right at the wall
/// (`xs_26_26` converges in the extension at 0 conflicts / ~155 decisions
/// but is wall-killed ~0.2s short at T:20 under 3.5s; `xs_33_43`,
/// `xs-20-18-3-4-5-4` also extension-decided). Cutting to 2.0s hands those
/// ~1.5s back to the extension (converts `xs_26_26` at T:20, 3x) while still
/// leaving a 2.0s floor for any latent resume-decided green. Override:
/// `AY_UFLIA_DETOUR_RESUME_RESERVE_MS` (measurement/tuning only, e.g. 3500
/// restores the pre-change window). Process-cached.
fn uflia_detour_resume_reserve() -> std::time::Duration {
    std::time::Duration::from_secs(2)
}

/// #detour-snapshot-extend: minimum extension worth paying the continuation
/// restart cost for (the continuation re-clausifies onto the persistent
/// solver before its first round; a sub-half-second window cannot recover
/// that overhead). Below this the speculation is skipped entirely.
const UFLIA_DETOUR_EXTEND_MIN: std::time::Duration = std::time::Duration::from_millis(500);

/// Inc5 #fused-detour: FUSED detour arm (`--uflia-fused-detour=1`, default
/// OFF — flags-off byte-identical). Process-cached env read.
///
/// the development design notes §2 Inc5 +
/// the development design notes When enabled, the
/// hybrid's post-detour slot replaces the ISOLATED eager resume with the
/// z3-regime experiment: the eager split-loop macro (live TheoryExtension —
/// LIA bound props consumed at BCP) instantiated on the SHARED
/// `persistent_sat` — RETAINING eager1's and the detour's learned clauses —
/// with relevancy-HARD ON via the flag-respecting
/// `split_eager_relevancy_hard` seam and the wander-abort trip-wire
/// disarmed for the fused arm only. EUF lazy explanations stay OFF (the
/// arithmetic-combo carve-out in the combiner is untouched: the fused arm
/// creates `TheoryCombiner::uf_lia` exactly like eager1), and the
/// `lia_bcp_dirty`-class change-gating in the extension propagate path is
/// untouched.
///
/// Shared-solver ext→ext safety (brief open question 1, CLEARED): the
/// same-solver ext→ext restart-across-arena-rebuild gate tests
/// (ay-sat solver/tests/ext_restart_arena_rebuild.rs) approve this
/// embodiment — the NO_REASON normalization in `preprocess_reset` covers the
/// stale-arena-reason hazard in every arm-transition direction this slot
/// exercises (eager1 ext → detour plain → fused ext).
fn uflia_fused_detour_enabled() -> bool {
    static ON: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *ON.get_or_init(|| ay_core::misc_cli_flags().uflia_fused_detour)
}

/// UFLIA model extraction shared by ALL split-loop invocations of the hybrid
/// (#relevancy-lazy-routing): the eager attempt, the bounded lazy detour, the
/// speculative detour extension, and the eager resume must apply the
/// IDENTICAL model recovery. This is the hardened descendant's
/// model-fixup/reunification sequence verbatim (the rewiring condition for
/// the hybrid router): exact-anchor recovery BEFORE substitution replay,
/// opaque-app backfill, diseq-protected substituted-value recovery,
/// composite-int recompute, then uninterpreted-equality unification. All
/// repairs are model-repair-only; the fail-closed validation gate re-checks
/// every assertion afterwards.
fn extract_uflia_theory_models(
    terms: &TermStore,
    live_assertions: &[TermId],
    original_assertions: &[TermId],
    var_subst: &crate::preprocess::VariableSubstitution,
    theory: &mut TheoryCombiner<'_>,
) -> TheoryModels {
    let mut model_roots: Vec<TermId> = live_assertions
        .iter()
        .copied()
        .chain(original_assertions.iter().copied())
        .collect();
    model_roots.sort_by_key(|term| term.index());
    model_roots.dedup();
    let lia_model_value_terms = uflia_lia_model_value_terms(terms, &model_roots);
    let fixup_protected = collect_active_arith_diseq_vars(terms, model_roots.iter().copied());
    theory.scope_euf_model_to_roots(&model_roots);
    let (mut euf, lia) = theory.extract_euf_lia_models_with_lia_value_filter_and_fixup(
        &model_roots,
        |term| lia_model_value_terms.contains(&term),
        |terms, euf_model, lia| {
            let Some(model) = lia.as_mut() else { return };
            // Recover exact anchors before replaying eliminated
            // substitutions. Replaying first can commit a dependent from a
            // stale opaque UF value and leave it stale after the exact
            // anchor is restored.
            super::lia::recover_lia_equalities_from_assertions(terms, original_assertions, model);
            // An Int-sorted UF application asserted equal to a LIA-valued
            // variable otherwise keeps its speculative/default value.
            super::lia::backfill_opaque_app_values_from_equalities(terms, &model_roots, model);
            super::lia::recover_substituted_lia_values_protecting(
                terms,
                var_subst,
                model,
                &fixup_protected,
            );
            // Preprocessing can replace original arithmetic UF arguments
            // (`a + 1`) with constants. Recompute every arithmetic composite
            // over the final recovered leaves before the shared merge
            // synchronizes both EUF numeric and formatted views.
            let composite_candidates: Vec<TermId> = euf_model.term_values.keys().copied().collect();
            super::lia::recompute_composite_int_values(terms, &composite_candidates, model);
        },
    );
    theory.clear_euf_model_scope();
    // #uflia-uninterp-eq-recover: the EUF model can give two terms different
    // sort elements despite a top-level `(= x y)` asserting them equal (the
    // verification-consumer mut-ref carrier `a == mk_mut_ref(a_current, a_final, a_id)`
    // over LIA-constrained args: `a=@S!0` but `mk(..)=@S!1`), so the model's
    // own validation gate refutes the equality and a genuine `sat` degrades
    // to `unknown`. Unify the element values for top-level asserted-equal
    // uninterpreted pairs. SOUND/fail-closed: only repairs the materialized
    // model; validation re-checks every assertion, so it can never admit a
    // false `sat`. Fixes verification-consumer bug/682 + final_borrows.
    super::lia::recover_uninterpreted_equalities_from_assertions(terms, &model_roots, &mut euf);
    TheoryModels {
        euf: Some(euf),
        lia,
        ..TheoryModels::default()
    }
}

use super::super::Executor;
use super::{MAX_SPLITS_LIA, MAX_SPLITS_LRA};

fn empty_hash_set<T>() -> HashSet<T>
where
    T: Eq + std::hash::Hash,
{
    HashSet::default()
}

fn bv_const_value(terms: &TermStore, term: TermId) -> Option<BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::BitVec { value, .. }) => Some(value.clone()),
        _ => None,
    }
}

fn bv_width(terms: &TermStore, term: TermId) -> Option<u32> {
    match terms.sort(term) {
        Sort::BitVec(sort) => Some(sort.width),
        _ => None,
    }
}

/// Whether any root term contains a `bvsub` application (anywhere in its DAG).
///
/// The conservative BV<->LIA bridge translates `bv2nat`/`bvult`/`bvule`/signed
/// compares to Int, but it does NOT relate `bvsub(a, b)` to an Int term. Once a
/// `bv2nat` linkage is asserted the bridge therefore stalls and returns Unknown
/// on goals that contain `bvsub` — even ones whose (in)validity is decidable in
/// the pure-BV fragment (e.g. `bvult(bvsub(k,1), k)` given `bvugt(k,4)`). This
/// gate scopes the sound `solve_bv` relaxation fallback to exactly those
/// queries (#9065 gap 2). Bound by a `visited` set so shared subterms in a DAG
/// are not revisited.
fn roots_contain_bvsub(terms: &TermStore, roots: &[TermId]) -> bool {
    fn visit(terms: &TermStore, term: TermId, visited: &mut HashSet<TermId>) -> bool {
        if !visited.insert(term) {
            return false;
        }
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) => {
                if name == "bvsub" {
                    return true;
                }
                args.iter().any(|&a| visit(terms, a, visited))
            }
            TermData::App(_, args) => args.iter().any(|&a| visit(terms, a, visited)),
            TermData::Not(inner) => visit(terms, *inner, visited),
            TermData::Ite(c, t, e) => {
                visit(terms, *c, visited) || visit(terms, *t, visited) || visit(terms, *e, visited)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, bound)| visit(terms, *bound, visited))
                    || visit(terms, *body, visited)
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                visit(terms, *body, visited)
            }
            _ => false,
        }
    }
    let mut visited = HashSet::default();
    roots.iter().any(|&root| visit(terms, root, &mut visited))
}

/// Collect binary `bvadd`/`bvsub` terms reachable from `roots`, returning
/// `(term, is_sub, lhs, rhs, width)` for each. Visited-bounded DAG walk mirroring
/// [`collect_int2bv_terms`]. Feeds the sound modular bridge
/// (`collect_bv2nat_add_sub_modular_assertions`).
fn collect_bv_add_sub_terms(
    terms: &TermStore,
    roots: &[TermId],
) -> Vec<(TermId, bool, TermId, TermId, u32)> {
    fn visit(
        terms: &TermStore,
        term: TermId,
        seen: &mut HashSet<TermId>,
        out: &mut Vec<(TermId, bool, TermId, TermId, u32)>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let TermData::App(Symbol::Named(name), args) = terms.get(term) {
            if (name == "bvadd" || name == "bvsub") && args.len() == 2 {
                if let Some(width) = bv_width(terms, term) {
                    out.push((term, name == "bvsub", args[0], args[1], width));
                }
            }
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                for &arg in args {
                    visit(terms, arg, seen, out);
                }
            }
            TermData::Not(inner) => visit(terms, *inner, seen, out),
            TermData::Ite(c, t, e) => {
                visit(terms, *c, seen, out);
                visit(terms, *t, seen, out);
                visit(terms, *e, seen, out);
            }
            TermData::Let(bindings, body) => {
                for (_, bound) in bindings {
                    visit(terms, *bound, seen, out);
                }
                visit(terms, *body, seen, out);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                visit(terms, *body, seen, out);
                for trigger in triggers {
                    for &t in trigger {
                        visit(terms, t, seen, out);
                    }
                }
            }
            _ => {}
        }
    }
    let mut seen = HashSet::default();
    let mut out = Vec::new();
    for &root in roots {
        visit(terms, root, &mut seen, &mut out);
    }
    out
}

/// Collect BitVec-sorted leaf VARIABLES reachable from `roots`, returning
/// `(term, width)` for each. Feeds the materialized SAT promotion
/// (`bridge_sat_materialize_and_validate`): these are exactly the terms whose
/// concrete value must be supplied so `validate_model` can recompute every BV op
/// from real bits. Constants and compound BV terms are excluded (constants are
/// already concrete; compounds evaluate bottom-up from their leaves).
fn collect_bv_leaf_vars(terms: &TermStore, roots: &[TermId]) -> Vec<(TermId, u32)> {
    fn visit(
        terms: &TermStore,
        term: TermId,
        seen: &mut HashSet<TermId>,
        out: &mut Vec<(TermId, u32)>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if matches!(terms.get(term), TermData::Var(..)) {
            if let Some(width) = bv_width(terms, term) {
                out.push((term, width));
            }
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                for &arg in args {
                    visit(terms, arg, seen, out);
                }
            }
            TermData::Not(inner) => visit(terms, *inner, seen, out),
            TermData::Ite(c, t, e) => {
                visit(terms, *c, seen, out);
                visit(terms, *t, seen, out);
                visit(terms, *e, seen, out);
            }
            TermData::Let(bindings, body) => {
                for (_, bound) in bindings {
                    visit(terms, *bound, seen, out);
                }
                visit(terms, *body, seen, out);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                visit(terms, *body, seen, out);
                for trigger in triggers {
                    for &t in trigger {
                        visit(terms, t, seen, out);
                    }
                }
            }
            _ => {}
        }
    }
    let mut seen = HashSet::default();
    let mut out = Vec::new();
    for &root in roots {
        visit(terms, root, &mut seen, &mut out);
    }
    out
}

/// Structural realizability guard for the BV<->LIA bridge SAT promotion
/// (#9065 / B2).
///
/// Returns `true` iff EVERY BitVec value in `roots` enters the formula SOLELY
/// through a `bv2nat`/`int2bv` bridge, and NO other BitVec operation
/// (`bvadd`/`bvsub`/`bvmul`/`bvand`/`bvor`/`bvxor`/`bvnot`/`bvshl`/`bvlshr`,
/// `concat`, `extract`, `bvult`/`bvule`/`bvslt`/…, a BitVec `=`/`distinct`,
/// a BitVec `ite`, a BitVec array index, …) appears anywhere. Concretely:
///
///   * `bv2nat(x)` — the single BitVec argument is consumed by the bridge.
///     A bare BitVec variable/constant `x` here is exactly the allowed
///     occurrence; a compound argument is recursed into (so `int2bv(int)` is
///     permitted, every other BitVec op inside is rejected).
///   * `int2bv(int_expr)` — a BitVec-producing bridge whose value is fully
///     determined by its Int source; recurse into the Int argument.
///   * Any other node: a BitVec-sorted *result* is a non-bridge BitVec op
///     (=> reject); a BitVec-sorted *operand* feeds a BitVec value into a
///     non-bridge op (=> reject). Otherwise recurse into operands.
///
/// Under this shape the opaque LIA value `v` of each `bv2nat(x)`, which the
/// bridge range-checks into `[0, 2^w)` via `push_bv2nat_range`, is realizable
/// by the witness `x = int2bv_w(v)` — there is NO competing BitVec constraint
/// on `x`, so distinct `bv2nat` values can be witnessed independently. A
/// validated AUFLIA model is therefore a TRUE model and SAT promotion is sound.
///
/// CONSERVATIVE BY CONSTRUCTION: any unhandled node kind (`let`, quantifiers),
/// any BitVec-sorted operand under a non-bridge node, and any BitVec-producing
/// op other than `int2bv`/`bv2nat` all return `false` — keeping the bridge at
/// `Unknown`, which is always sound. A too-loose guard would be a false SAT, so
/// when in doubt this predicate rejects.
///
/// The `visited` set memoizes only NON-leaf nodes, whose verdict is
/// context-independent here. BitVec leaves are never memoized as standalone
/// nodes: their admissibility is decided AT THE PARENT (allowed only directly
/// under `bv2nat`), so every occurrence of a BitVec variable is re-checked.
fn all_bitvec_vars_are_bridge_only(terms: &TermStore, roots: &[TermId]) -> bool {
    fn is_bv(terms: &TermStore, t: TermId) -> bool {
        terms.sort(t).is_bitvec()
    }
    fn walk(terms: &TermStore, term: TermId, visited: &mut HashSet<TermId>) -> bool {
        if !visited.insert(term) {
            return true;
        }
        match terms.get(term) {
            // bv2nat(arg): the single BitVec arg is consumed by the bridge.
            TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1 => {
                let arg = args[0];
                match terms.get(arg) {
                    // Bare BitVec variable / constant directly bridged: the one
                    // allowed BitVec-leaf occurrence. (bv2nat of a constant is
                    // folded away at construction, so Const is effectively dead
                    // here, but accepting it is harmless — a literal is concrete
                    // and trivially realizable.)
                    TermData::Var(_, _) | TermData::Const(_) => true,
                    // Compound argument (e.g. int2bv(int_expr)): validate it.
                    // Any non-bridge BitVec op inside is rejected by recursion.
                    _ => walk(terms, arg, visited),
                }
            }
            // int2bv(int_expr): a BitVec-producing bridge from an Int source.
            // Permitted; recurse into the Int argument.
            TermData::App(Symbol::Indexed(name, _), args)
                if name == "int2bv" && args.len() == 1 =>
            {
                walk(terms, args[0], visited)
            }
            // Any other application. A BitVec-sorted result is a non-bridge BV op
            // (bvadd/concat/extract/…) => reject. A BitVec-sorted operand feeds a
            // BitVec value into a non-bridge op (=, distinct, select index, …) =>
            // reject. Otherwise recurse into the operands.
            TermData::App(_, args) => {
                if is_bv(terms, term) {
                    return false;
                }
                args.iter()
                    .all(|&a| !is_bv(terms, a) && walk(terms, a, visited))
            }
            TermData::Not(inner) => {
                let inner = *inner;
                !is_bv(terms, inner) && walk(terms, inner, visited)
            }
            TermData::Ite(c, t, e) => {
                // A BitVec-sorted ite is itself a non-bridge BitVec op.
                if is_bv(terms, term) {
                    return false;
                }
                let (c, t, e) = (*c, *t, *e);
                [c, t, e]
                    .into_iter()
                    .all(|a| !is_bv(terms, a) && walk(terms, a, visited))
            }
            // A leaf reached directly (e.g. a root) is OK only if it is non-BitVec.
            TermData::Var(_, _) | TermData::Const(_) => !is_bv(terms, term),
            // `let`/quantifiers are outside the QF bridge fragment handled here:
            // reject conservatively (sound — keeps the bridge at Unknown).
            TermData::Let(_, _) | TermData::Forall(..) | TermData::Exists(..) => false,
            _ => false,
        }
    }
    let mut visited = HashSet::default();
    roots.iter().all(|&root| walk(terms, root, &mut visited))
}

/// If a BitVec leaf var `v` is DIRECTLY pinned to a BitVec constant by a
/// top-level asserted equality `(= v c)` / `(= c v)` in `roots`, return the
/// unsigned (`bv2nat`) value of `c` (#snd-bv-1).
///
/// Used only to materialize a concrete SAT witness for a pinned leaf when the
/// AUFLIA model keys the leaf's `bv2nat` value under a substituted term (the
/// solver eliminated `v` via its pin, so `bv2nat(v)`'s value is stored under
/// `bv2nat(c)` and the direct `bv2nat(v)` lookup misses). `validate_model`
/// remains the sole soundness arbiter of the materialized model, so returning a
/// value here can only enable a genuine SAT that then validates — a wrong guess
/// simply fails validation and the bridge stays Unknown (never a false SAT).
fn bv_leaf_pinned_nat(terms: &TermStore, roots: &[TermId], v: TermId) -> Option<BigInt> {
    for &root in roots {
        let TermData::App(Symbol::Named(name), args) = terms.get(root) else {
            continue;
        };
        if name != "=" || args.len() != 2 {
            continue;
        }
        let (a, b) = (args[0], args[1]);
        let other = if a == v {
            b
        } else if b == v {
            a
        } else {
            continue;
        };
        if let Some(val) = bv_const_value(terms, other) {
            return Some(val);
        }
    }
    None
}

fn push_bv2nat_range(terms: &mut TermStore, out: &mut Vec<TermId>, bv: TermId, nat: TermId) {
    let Some(width) = bv_width(terms, bv) else {
        return;
    };
    push_bv2nat_width_bounds(terms, out, width, nat);
    push_bv2nat_congruence(terms, out, bv, nat, width);
    push_bv2nat_extract_link(terms, out, bv, nat);
}

/// `0 <= nat <= 2^width - 1` — the unsigned range of a width-`width` vector.
fn push_bv2nat_width_bounds(terms: &mut TermStore, out: &mut Vec<TermId>, width: u32, nat: TermId) {
    let zero = terms.mk_int(BigInt::zero());
    let max = terms.mk_int((BigInt::one() << width) - BigInt::one());
    out.push(terms.mk_ge(nat, zero));
    out.push(terms.mk_le(nat, max));
}

/// Link `bv2nat((_ extract h l) t)` to `bv2nat(t)` (#bv2nat-extract-link).
///
/// The range fact alone leaves an extracted slice's unsigned value FLOATING
/// with respect to its source: `bv2nat(x)` and `bv2nat((_ extract 31 31) x)`
/// were two independent Int variables constrained only by `[0, 2^32)` and
/// `[0, 2)`, so the arithmetic solver could pick `bv2nat(x) = 10` together with
/// `msb = 1` while the BV solver picked `x = 0x0000000a`. That combination
/// satisfies neither theory's view of the other, and the composite model
/// falsifies the very assertion that produced it — the case AY's independent
/// model gate catches as an INVALID model.
///
/// The fix is definitional. Splitting `t` at the slice boundaries,
///
/// ```text
///   bv2nat(t) = 2^(h+1) * bv2nat(t[W-1:h+1])   (omitted when h+1 = W)
///             + 2^l     * bv2nat(t[h:l])
///             +           bv2nat(t[l-1:0])     (omitted when l = 0)
/// ```
///
/// is the unique base-2 place-value decomposition of the unsigned value of `t`,
/// so it is entailed by `t`'s value under every assignment.
///
/// SOUNDNESS: an EXACT identity of `bv2nat`, not an approximation — it removes
/// no model (every true assignment satisfies it, with the high/low pieces taking
/// their actual slice values), so it can only turn a spurious SAT into the
/// correct verdict and can never manufacture an UNSAT. The two companion slices
/// are ordinary `bv2nat` terms and carry their own width bounds; they are NOT
/// re-linked recursively here, so the emitted set stays finite (a split only ever
/// introduces slices whose endpoints already bound the original one).
fn push_bv2nat_extract_link(terms: &mut TermStore, out: &mut Vec<TermId>, bv: TermId, nat: TermId) {
    let TermData::App(Symbol::Indexed(name, indices), args) = terms.get(bv).clone() else {
        return;
    };
    if name != "extract" || indices.len() != 2 || args.len() != 1 {
        return;
    }
    let (high, low) = (indices[0], indices[1]);
    if high < low {
        return;
    }
    let source = args[0];
    let Some(src_width) = bv_width(terms, source) else {
        return;
    };
    // A malformed slice carries no decomposition; a full-width slice is `source`
    // itself (already simplified away by `mk_bvextract`), so nothing to link.
    if high >= src_width || (low == 0 && high + 1 == src_width) {
        return;
    }
    let nat_src = terms.mk_bv2nat(source);
    push_bv2nat_width_bounds(terms, out, src_width, nat_src);

    let mut parts: Vec<TermId> = Vec::new();
    if high + 1 < src_width {
        let hi_slice = terms.mk_bvextract(src_width - 1, high + 1, source);
        let nat_hi = terms.mk_bv2nat(hi_slice);
        push_bv2nat_width_bounds(terms, out, src_width - high - 1, nat_hi);
        let scale = terms.mk_int(BigInt::one() << (high + 1));
        parts.push(terms.mk_mul(vec![scale, nat_hi]));
    }
    if low > 0 {
        let scale = terms.mk_int(BigInt::one() << low);
        parts.push(terms.mk_mul(vec![scale, nat]));
        let lo_slice = terms.mk_bvextract(low - 1, 0, source);
        let nat_lo = terms.mk_bv2nat(lo_slice);
        push_bv2nat_width_bounds(terms, out, low, nat_lo);
        parts.push(nat_lo);
    } else {
        parts.push(nat);
    }
    let sum = if parts.len() == 1 {
        parts[0]
    } else {
        terms.mk_add(parts)
    };
    let link = terms.mk_eq(nat_src, sum);
    out.push(link);
}

/// Assert the EXACT modular congruence relating `bv2nat(int2bv(s, w))` to its
/// integer source `s`, as a LIA equation with a fresh unconstrained Int slack:
///
/// ```text
///   nat = s - 2^w * k          (k a FRESH unconstrained Int = floor(s / 2^w))
/// ```
///
/// (the accompanying `0 <= nat <= 2^w - 1` bound is emitted by the caller in
/// `push_bv2nat_range`). Together these are the SMT-LIB definition of
/// `int2bv`/`bv2nat`: `nat` is the unique residue of `s` modulo `2^w`. This is
/// what lets the general LIA solver relate the residue back to the source under
/// ALL inputs, so the BV↔Int bridge can return UNSAT for wide widths that
/// enumeration cannot reach.
///
/// SOUNDNESS: the relation is asserted as an EQUALITY with an explicit `2^w * k`
/// slack where `k` is unconstrained (so any integer source `s` admits exactly
/// the residues it truly has). It is therefore EXACT — it never removes a model
/// that the true wrapping semantics admit — so it can only enable additional
/// valid UNSATs, never a false one. `k` must NOT be constrained.
fn push_bv2nat_congruence(
    terms: &mut TermStore,
    out: &mut Vec<TermId>,
    bv: TermId,
    nat: TermId,
    width: u32,
) {
    // Only `int2bv(s, w)` carries a recoverable integer source; a bare BV
    // variable's "source" is itself and the range fact already pins it.
    let TermData::App(Symbol::Indexed(name, indices), args) = terms.get(bv) else {
        return;
    };
    if name != "int2bv" || indices.len() != 1 || indices[0] != width || args.len() != 1 {
        return;
    }
    let source = args[0];
    if *terms.sort(source) != Sort::Int {
        return;
    }
    let modulus = terms.mk_int(BigInt::one() << width);
    let k = terms.mk_fresh_var(
        &format!("__ay_bv_lia_cong_k{}_w{}", source.0, width),
        Sort::Int,
    );
    // nat = source - 2^w * k
    let scaled_k = terms.mk_mul(vec![modulus, k]);
    let rhs = terms.mk_sub(vec![source, scaled_k]);
    let cong = terms.mk_eq(nat, rhs);
    out.push(cong);
}

fn push_unsigned_bv_cmp_bridge(
    terms: &mut TermStore,
    out: &mut Vec<TermId>,
    name: &str,
    lhs: TermId,
    rhs: TermId,
    positive: bool,
) {
    if !matches!(name, "bvult" | "bvule") {
        return;
    }

    if let Some(bound) = bv_const_value(terms, rhs) {
        let nat_lhs = terms.mk_bv2nat(lhs);
        push_bv2nat_range(terms, out, lhs, nat_lhs);
        let bound = terms.mk_int(bound);
        let bridge = match (name, positive) {
            ("bvult", true) => terms.mk_lt(nat_lhs, bound),
            ("bvult", false) => terms.mk_ge(nat_lhs, bound),
            ("bvule", true) => terms.mk_le(nat_lhs, bound),
            ("bvule", false) => terms.mk_gt(nat_lhs, bound),
            _ => return,
        };
        out.push(bridge);
    }

    if let Some(bound) = bv_const_value(terms, lhs) {
        let nat_rhs = terms.mk_bv2nat(rhs);
        push_bv2nat_range(terms, out, rhs, nat_rhs);
        let bound = terms.mk_int(bound);
        let bridge = match (name, positive) {
            ("bvult", true) => terms.mk_gt(nat_rhs, bound),
            ("bvult", false) => terms.mk_le(nat_rhs, bound),
            ("bvule", true) => terms.mk_ge(nat_rhs, bound),
            ("bvule", false) => terms.mk_lt(nat_rhs, bound),
            _ => return,
        };
        out.push(bridge);
    }

    // General (non-constant) unsigned comparison. When NEITHER side is a BV
    // constant, `bvult`/`bvule` is still EXACTLY the unsigned-value order
    // `bv2nat(lhs) ⋈ bv2nat(rhs)` — the definitional meaning of unsigned compare
    // on two equal-width vectors. This mirrors `push_signed_bv_cmp_bridge`, which
    // likewise reduces both operands with no constant-side requirement. It lets a
    // frame guard `bvult idx len` discharge when a SEPARATE fact pins
    // `bv2nat(len)` (e.g. `bv2nat(len) = old_len`) even though `len` is a
    // variable, which the constant-side arms above cannot reach.
    //
    // SOUNDNESS: `bvult(a,b) ⇔ bv2nat(a) < bv2nat(b)` and
    // `bvule(a,b) ⇔ bv2nat(a) ≤ bv2nat(b)` are exact equivalences (both sides
    // width-`W`, `bv2nat` the unsigned value in `[0,2^W)`), asserted here in the
    // atom's polarity together with the `0 ≤ bv2nat ≤ 2^W-1` range for each
    // operand. Adding an entailed equivalence removes no model: SAT stays SAT,
    // UNSAT stays sound.
    if bv_const_value(terms, lhs).is_none() && bv_const_value(terms, rhs).is_none() {
        let nat_lhs = terms.mk_bv2nat(lhs);
        let nat_rhs = terms.mk_bv2nat(rhs);
        push_bv2nat_range(terms, out, lhs, nat_lhs);
        push_bv2nat_range(terms, out, rhs, nat_rhs);
        let bridge = match (name, positive) {
            ("bvult", true) => terms.mk_lt(nat_lhs, nat_rhs),
            ("bvult", false) => terms.mk_ge(nat_lhs, nat_rhs),
            ("bvule", true) => terms.mk_le(nat_lhs, nat_rhs),
            ("bvule", false) => terms.mk_gt(nat_lhs, nat_rhs),
            _ => return,
        };
        out.push(bridge);
    }
}

/// Biconditional (polarity-free) unsigned-compare bridge.
///
/// When a `bvult`/`bvule` atom appears at INDETERMINATE polarity — inside a
/// disjunction, an `ite` condition, or otherwise mixed structure where its
/// truth is not fixed by the surrounding connective — the one-directional
/// [`push_unsigned_bv_cmp_bridge`] cannot fire (it needs the atom asserted true
/// or false). This reifies the atom's truth into LIA with the EXACT equivalence
///
/// ```text
///   atom  <->  (bv2nat(lhs) ⋈ bv2nat(rhs))       ⋈ ∈ {<, ≤}
/// ```
///
/// so the arithmetic solver can DECIDE the atom from pinned `bv2nat` values (and
/// vice versa). This is what discharges a frame guard `bvult idx len` sitting
/// inside the frame invariant's `(or (= …) (not (bvult idx len)))`: once
/// `bv2nat(len)` is pinned, the biconditional forces the guard's truth and
/// collapses the disjunction.
///
/// SOUNDNESS: `bvult(a,b) ⇔ bv2nat(a) < bv2nat(b)` and
/// `bvule(a,b) ⇔ bv2nat(a) ≤ bv2nat(b)` are exact equivalences over equal-width
/// vectors (`bv2nat` the unsigned value in `[0,2^W)`), asserted here together
/// with the `0 ≤ bv2nat ≤ 2^W-1` range for each operand. An exact equivalence
/// removes no model and adds none: SAT stays SAT, UNSAT stays sound. (SAT is
/// never promoted while a BV var occurs in a `bvult`/`bvule` atom — the
/// structural-realizability guard already blocks it — so the reified atom
/// cannot manufacture a false SAT either.)
fn push_unsigned_bv_cmp_biconditional(
    terms: &mut TermStore,
    out: &mut Vec<TermId>,
    atom: TermId,
    name: &str,
    lhs: TermId,
    rhs: TermId,
) {
    if !matches!(name, "bvult" | "bvule") {
        return;
    }
    // Skip zero-width vectors (no meaningful unsigned value).
    if !matches!(bv_width(terms, lhs), Some(w) if w > 0) {
        return;
    }
    let nat_lhs = terms.mk_bv2nat(lhs);
    let nat_rhs = terms.mk_bv2nat(rhs);
    push_bv2nat_range(terms, out, lhs, nat_lhs);
    push_bv2nat_range(terms, out, rhs, nat_rhs);
    let lia = match name {
        "bvult" => terms.mk_lt(nat_lhs, nat_rhs),
        "bvule" => terms.mk_le(nat_lhs, nat_rhs),
        _ => return,
    };
    // atom and lia are both Bool; mk_eq is the biconditional.
    let bicond = terms.mk_eq(atom, lia);
    out.push(bicond);
}

/// Biconditional (polarity-free) SIGNED-compare bridge — the signed counterpart
/// of [`push_unsigned_bv_cmp_biconditional`]. For an INDETERMINATE-polarity
/// `bvslt`/`bvsle` atom (inside a disjunction / `ite`, e.g. a per-element frame
/// obligation `(or (bvslt s_new[0] 0) (bvslt s_new[1] 0) …)`), reify its truth
/// as `atom <-> (bv2int(lhs) </≤ bv2int(rhs))` over the two's-complement
/// signed values, so the arithmetic side decides it once the operands' signs
/// are pinned. SOUNDNESS: `bv_signed_value` yields the exact two's-complement
/// value (`bv2nat - 2^W*msb`, with the `0≤msb≤1` and msb↔bv2nat-link facts),
/// so the equivalence removes no model.
fn push_signed_bv_cmp_biconditional(
    terms: &mut TermStore,
    out: &mut Vec<TermId>,
    atom: TermId,
    name: &str,
    lhs: TermId,
    rhs: TermId,
) {
    if !matches!(name, "bvslt" | "bvsle") {
        return;
    }
    let (Some(l), Some(r)) = (
        bv_signed_value(terms, out, lhs),
        bv_signed_value(terms, out, rhs),
    ) else {
        return;
    };
    let lia = match name {
        "bvslt" => terms.mk_lt(l, r),
        "bvsle" => terms.mk_le(l, r),
        _ => return,
    };
    let bicond = terms.mk_eq(atom, lia);
    out.push(bicond);
}

/// Signed value of a BV term as LIA: `bv2int(t) = bv2nat(t) - 2^W * msb(t)`,
/// where `msb(t) = bv2nat(extract W-1 W-1 t)` is the top bit, constrained to
/// `{0, 1}` by the 1-bit extract. This is exactly the two's-complement signed
/// interpretation, so it is entailed by `t`'s value and adds no unsound model.
/// Pushes the `0 <= msb <= 1` range into `out` and returns the signed-value
/// term, or `None` for a zero-width vector.
fn bv_signed_value(terms: &mut TermStore, out: &mut Vec<TermId>, t: TermId) -> Option<TermId> {
    let width = bv_width(terms, t)?;
    if width == 0 {
        return None;
    }
    let nat = terms.mk_bv2nat(t);
    let msb_bit = terms.mk_bvextract(width - 1, width - 1, t);
    let msb = terms.mk_bv2nat(msb_bit);
    // 0 <= msb <= 1 is implied by the 1-bit extract; assert it for AUFLIA.
    let zero = terms.mk_int(BigInt::zero());
    let one = terms.mk_int(BigInt::one());
    let ge0 = terms.mk_ge(msb, zero);
    let le1 = terms.mk_le(msb, one);
    out.push(ge0);
    out.push(le1);
    // LINK msb to bv2nat (#signed-msb-link): `msb` is the TOP bit, so the low
    // `W-1` bits are `nat - 2^(W-1)*msb` and must lie in `[0, 2^(W-1))`. Without
    // this, `nat` and `msb` float independently — a term pinned to a concrete
    // `bv2nat` value still admits either sign, so a signed compare on a
    // constant-valued term (e.g. a frame element read `s_new[i] = s[i] = 0x0a`,
    // then `bvslt s_new[i] 0`) is left undecidable. Definitional and exact
    // (`msb = floor(nat / 2^(W-1))` for `0 <= nat < 2^W`, `msb in {0,1}`): it
    // removes no model, only pins the sign from the magnitude and vice versa.
    let half = terms.mk_int(BigInt::one() << (width - 1));
    let scaled_msb = terms.mk_mul(vec![half, msb]);
    let low = terms.mk_sub(vec![nat, scaled_msb]);
    let low_ge0 = terms.mk_ge(low, zero);
    let low_lt_half = terms.mk_lt(low, half);
    out.push(low_ge0);
    out.push(low_lt_half);
    let modulus = terms.mk_int(BigInt::one() << width);
    let high = terms.mk_mul(vec![modulus, msb]);
    Some(terms.mk_sub(vec![nat, high]))
}

/// Mirror of [`push_unsigned_bv_cmp_bridge`] for signed `bvslt`/`bvsle` atoms.
/// Bridges a signed compare into LIA over the two's-complement signed value
/// `bv2int(t) = bv2nat(t) - 2^W * msb(t)`. Unlike the unsigned arm this does
/// not require a constant side: both operands are reduced to their signed-value
/// LIA forms, all entailed by the operands' definitions, so the resulting
/// inequality only shrinks the model set.
fn push_signed_bv_cmp_bridge(
    terms: &mut TermStore,
    out: &mut Vec<TermId>,
    name: &str,
    lhs: TermId,
    rhs: TermId,
    positive: bool,
) {
    if !matches!(name, "bvslt" | "bvsle") {
        return;
    }
    let (Some(l), Some(r)) = (
        bv_signed_value(terms, out, lhs),
        bv_signed_value(terms, out, rhs),
    ) else {
        return;
    };
    let bridge = match (name, positive) {
        ("bvslt", true) => terms.mk_lt(l, r),
        ("bvslt", false) => terms.mk_ge(l, r),
        ("bvsle", true) => terms.mk_le(l, r),
        ("bvsle", false) => terms.mk_gt(l, r),
        _ => return,
    };
    out.push(bridge);
}

fn collect_bv_lia_bridge_assertions(terms: &mut TermStore, roots: &[TermId]) -> Vec<TermId> {
    fn visit(
        terms: &mut TermStore,
        term: TermId,
        polarity: Option<bool>,
        visited: &mut HashSet<(TermId, Option<bool>)>,
        out: &mut Vec<TermId>,
    ) {
        if !visited.insert((term, polarity)) {
            return;
        }

        match terms.get(term).clone() {
            TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1 => {
                push_bv2nat_range(terms, out, args[0], term);
                visit_children(terms, &args, visited, out);
            }
            TermData::App(Symbol::Named(name), args)
                if (polarity == Some(true) && name == "and")
                    || (polarity == Some(false) && name == "or") =>
            {
                for arg in args {
                    visit(terms, arg, polarity, visited, out);
                }
            }
            TermData::App(Symbol::Named(name), args)
                if (polarity == Some(true) && name == "or")
                    || (polarity == Some(false) && name == "and") =>
            {
                visit_children(terms, &args, visited, out);
            }
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2 && matches!(name.as_str(), "bvult" | "bvule") =>
            {
                match polarity {
                    // Definite polarity: the tighter one-directional LIA
                    // consequence (uses a folded constant side when present).
                    Some(p) => {
                        push_unsigned_bv_cmp_bridge(terms, out, &name, args[0], args[1], p);
                    }
                    // Indeterminate polarity (inside a disjunction / ite / …):
                    // reify the atom's truth with the exact biconditional so the
                    // arithmetic side can decide it from pinned `bv2nat` values.
                    None => {
                        push_unsigned_bv_cmp_biconditional(
                            terms, out, term, &name, args[0], args[1],
                        );
                    }
                }
                visit_children(terms, &args, visited, out);
            }
            // Signed compare bridge: both operands reduced to their
            // two's-complement signed-value LIA forms (no constant-side
            // requirement). Definite polarity → the one-directional inequality;
            // indeterminate polarity (inside a disjunction / ite) → the exact
            // biconditional so the atom's truth is decided from the signed
            // values (mirrors the unsigned arm).
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2 && matches!(name.as_str(), "bvslt" | "bvsle") =>
            {
                match polarity {
                    Some(p) => {
                        push_signed_bv_cmp_bridge(terms, out, &name, args[0], args[1], p);
                    }
                    None => {
                        push_signed_bv_cmp_biconditional(terms, out, term, &name, args[0], args[1]);
                    }
                }
                visit_children(terms, &args, visited, out);
            }
            TermData::App(_, args) => visit_children(terms, &args, visited, out),
            TermData::Not(inner) => visit(terms, inner, polarity.map(|p| !p), visited, out),
            TermData::Ite(c, t, e) => {
                visit(terms, c, None, visited, out);
                visit(terms, t, None, visited, out);
                visit(terms, e, None, visited, out);
            }
            TermData::Let(bindings, body) => {
                for (_, bound) in bindings {
                    visit(terms, bound, None, visited, out);
                }
                visit(terms, body, polarity, visited, out);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                visit(terms, body, None, visited, out);
                for trigger in triggers {
                    visit_children(terms, &trigger, visited, out);
                }
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }

    fn visit_children(
        terms: &mut TermStore,
        args: &[TermId],
        visited: &mut HashSet<(TermId, Option<bool>)>,
        out: &mut Vec<TermId>,
    ) {
        for &arg in args {
            visit(terms, arg, None, visited, out);
        }
    }

    let mut out = Vec::new();
    let mut visited = HashSet::default();
    for &root in roots {
        visit(terms, root, Some(true), &mut visited, &mut out);
    }

    let true_term = terms.true_term();
    let existing: HashSet<TermId> = roots.iter().copied().collect();
    let mut seen = HashSet::default();
    out.retain(|term| *term != true_term && !existing.contains(term) && seen.insert(*term));
    out
}

fn bridge_supported_int_term(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(Constant::Int(_)) | TermData::Var(_, _) => *terms.sort(term) == Sort::Int,
        TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1 => true,
        // Allow the residue/signed-value linear combinations through the support
        // filter, e.g. `nat + 2^W * k` (Euclidean residue) and
        // `bv2nat(t) - 2^W * msb(t)` (signed value). Each operand must itself be
        // a bridge-supported Int term.
        TermData::App(Symbol::Named(name), args)
            if matches!(name.as_str(), "+" | "-" | "*")
                && !args.is_empty()
                && args.iter().all(|&a| bridge_supported_int_term(terms, a)) =>
        {
            true
        }
        _ => false,
    }
}

fn is_bv_lia_bridge_support_assertion(terms: &TermStore, term: TermId) -> bool {
    match terms.get(term) {
        TermData::Const(Constant::Bool(true)) => true,
        TermData::App(Symbol::Named(name), args)
            if matches!(name.as_str(), "=" | "<=" | "<" | ">=" | ">") && args.len() == 2 =>
        {
            bridge_supported_int_term(terms, args[0]) && bridge_supported_int_term(terms, args[1])
        }
        TermData::Not(inner) => is_bv_lia_bridge_support_assertion(terms, *inner),
        _ => false,
    }
}

fn collect_bv_lia_support_assertions(
    terms: &TermStore,
    roots: &[TermId],
    bridge_assertions: &[TermId],
) -> Vec<TermId> {
    let mut out = Vec::new();
    let mut seen = HashSet::default();
    for &root in roots {
        if is_bv_lia_bridge_support_assertion(terms, root) && seen.insert(root) {
            out.push(root);
        }
    }
    for &bridge in bridge_assertions {
        if seen.insert(bridge) {
            out.push(bridge);
        }
    }
    out
}

#[derive(Default)]
struct IntFactIndex {
    parent: HashMap<TermId, TermId>,
    lower: HashMap<TermId, BigInt>,
    upper: HashMap<TermId, BigInt>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct BvLiaResidueBinding {
    int_term: TermId,
    width: u32,
    bv_var: TermId,
}

#[derive(Clone, Debug)]
struct BvLiaEnumerationDomain {
    int_term: TermId,
    lower: BigInt,
    upper: BigInt,
}

#[derive(Clone, Debug, Default)]
struct IntIteDefinition {
    when_true: Option<BigInt>,
    when_false: Option<BigInt>,
}

const BV_LIA_BRIDGE_ENUMERATION_LIMIT: u64 = 1 << 16;

impl IntFactIndex {
    fn ensure(&mut self, term: TermId) {
        self.parent.entry(term).or_insert(term);
    }

    fn root(&self, term: TermId) -> TermId {
        let mut cur = term;
        while let Some(&next) = self.parent.get(&cur) {
            if next == cur {
                return cur;
            }
            cur = next;
        }
        term
    }

    fn union(&mut self, lhs: TermId, rhs: TermId) {
        self.ensure(lhs);
        self.ensure(rhs);
        let lhs_root = self.root(lhs);
        let rhs_root = self.root(rhs);
        if lhs_root == rhs_root {
            return;
        }

        self.parent.insert(rhs_root, lhs_root);
        let lower = match (self.lower.remove(&lhs_root), self.lower.remove(&rhs_root)) {
            (Some(a), Some(b)) => Some(a.max(b)),
            (Some(a), None) | (None, Some(a)) => Some(a),
            (None, None) => None,
        };
        if let Some(bound) = lower {
            self.lower.insert(lhs_root, bound);
        }

        let upper = match (self.upper.remove(&lhs_root), self.upper.remove(&rhs_root)) {
            (Some(a), Some(b)) => Some(a.min(b)),
            (Some(a), None) | (None, Some(a)) => Some(a),
            (None, None) => None,
        };
        if let Some(bound) = upper {
            self.upper.insert(lhs_root, bound);
        }
    }

    fn add_lower(&mut self, term: TermId, bound: BigInt) {
        self.ensure(term);
        let root = self.root(term);
        self.lower
            .entry(root)
            .and_modify(|old| {
                if bound > *old {
                    *old = bound.clone();
                }
            })
            .or_insert(bound);
    }

    fn add_upper(&mut self, term: TermId, bound: BigInt) {
        self.ensure(term);
        let root = self.root(term);
        self.upper
            .entry(root)
            .and_modify(|old| {
                if bound < *old {
                    *old = bound.clone();
                }
            })
            .or_insert(bound);
    }

    fn lower_bound(&self, term: TermId) -> Option<&BigInt> {
        self.lower.get(&self.root(term))
    }

    fn upper_bound(&self, term: TermId) -> Option<&BigInt> {
        self.upper.get(&self.root(term))
    }

    fn class_terms(&self, term: TermId) -> Vec<TermId> {
        let root = self.root(term);
        self.parent
            .keys()
            .copied()
            .filter(|candidate| self.root(*candidate) == root)
            .collect()
    }
}

fn int_const_value(terms: &TermStore, term: TermId) -> Option<BigInt> {
    match terms.get(term) {
        TermData::Const(Constant::Int(value)) => Some(value.clone()),
        _ => None,
    }
}

fn record_int_fact(terms: &TermStore, facts: &mut IntFactIndex, term: TermId) {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args)
            if name == "and" && *terms.sort(term) == Sort::Bool =>
        {
            for &arg in args {
                record_int_fact(terms, facts, arg);
            }
        }
        TermData::App(Symbol::Named(name), args)
            if name == "="
                && args.len() == 2
                && *terms.sort(args[0]) == Sort::Int
                && *terms.sort(args[1]) == Sort::Int =>
        {
            facts.union(args[0], args[1]);
        }
        TermData::App(Symbol::Named(name), args)
            if matches!(name.as_str(), "<=" | "<" | ">=" | ">") && args.len() == 2 =>
        {
            let lhs = args[0];
            let rhs = args[1];
            let lhs_const = int_const_value(terms, lhs);
            let rhs_const = int_const_value(terms, rhs);
            match (name.as_str(), lhs_const, rhs_const) {
                ("<=", Some(c), None) if *terms.sort(rhs) == Sort::Int => facts.add_lower(rhs, c),
                ("<=", None, Some(c)) if *terms.sort(lhs) == Sort::Int => facts.add_upper(lhs, c),
                ("<", Some(c), None) if *terms.sort(rhs) == Sort::Int => {
                    facts.add_lower(rhs, c + BigInt::one());
                }
                ("<", None, Some(c)) if *terms.sort(lhs) == Sort::Int => {
                    facts.add_upper(lhs, c - BigInt::one());
                }
                (">=", Some(c), None) if *terms.sort(rhs) == Sort::Int => facts.add_upper(rhs, c),
                (">=", None, Some(c)) if *terms.sort(lhs) == Sort::Int => facts.add_lower(lhs, c),
                (">", Some(c), None) if *terms.sort(rhs) == Sort::Int => {
                    facts.add_upper(rhs, c - BigInt::one());
                }
                (">", None, Some(c)) if *terms.sort(lhs) == Sort::Int => {
                    facts.add_lower(lhs, c + BigInt::one());
                }
                _ => {}
            }
        }
        _ => {}
    }
}

fn collect_int_facts(terms: &TermStore, roots: &[TermId]) -> IntFactIndex {
    let mut facts = IntFactIndex::default();
    for &root in roots {
        record_int_fact(terms, &mut facts, root);
    }
    facts
}

/// Collect candidate BV terms for the `#bv2nat-const-pin` conditional clauses:
/// every `bv2nat` argument and every operand of a `bvult`/`bvule`/`bvslt`/`bvsle`
/// atom reachable in `roots` (the terms the bridge takes — or will take — the
/// `bv2nat` of). Deduplicated, DAG-walk, visited-bounded.
fn collect_bv2nat_pin_candidate_terms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    fn visit(terms: &TermStore, term: TermId, seen: &mut HashSet<TermId>, out: &mut Vec<TermId>) {
        if !seen.insert(term) {
            return;
        }
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1 => {
                out.push(args[0]);
                visit(terms, args[0], seen, out);
            }
            TermData::App(Symbol::Named(name), args)
                if args.len() == 2
                    && matches!(name.as_str(), "bvult" | "bvule" | "bvslt" | "bvsle") =>
            {
                out.push(args[0]);
                out.push(args[1]);
                visit(terms, args[0], seen, out);
                visit(terms, args[1], seen, out);
            }
            // An `int2bv(w, s)` term is itself a bv2nat-pin candidate (#snd-bv-2):
            // when it is equated to a BV constant `c`, the const-pin clause
            // `(= int2bv_w(s) c) ⇒ bv2nat(int2bv_w(s)) = bv2nat(c)` links the
            // (definitional) `bv2nat(int2bv_w(s))` to a concrete Int, closing the
            // `s ≡ value(c) (mod 2^w)` loop that refutes/satisfies the goal.
            TermData::App(Symbol::Indexed(name, _), args)
                if name == "int2bv" && args.len() == 1 =>
            {
                out.push(term);
                visit(terms, args[0], seen, out);
            }
            TermData::App(_, args) => {
                for &a in args.clone().iter() {
                    visit(terms, a, seen, out);
                }
            }
            TermData::Not(inner) => visit(terms, *inner, seen, out),
            TermData::Ite(c, t, e) => {
                visit(terms, *c, seen, out);
                visit(terms, *t, seen, out);
                visit(terms, *e, seen, out);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings.clone().iter() {
                    visit(terms, *v, seen, out);
                }
                visit(terms, *body, seen, out);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                visit(terms, *body, seen, out);
            }
            _ => {}
        }
    }
    let mut seen = HashSet::default();
    let mut dedup = HashSet::default();
    let mut raw = Vec::new();
    for &root in roots {
        visit(terms, root, &mut seen, &mut raw);
    }
    raw.into_iter().filter(|t| dedup.insert(*t)).collect()
}

/// Collect the distinct bitvector CONSTANT leaves reachable in `roots`.
fn collect_bv_constant_leaves(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    fn visit(terms: &TermStore, term: TermId, seen: &mut HashSet<TermId>, out: &mut Vec<TermId>) {
        if !seen.insert(term) {
            return;
        }
        if matches!(terms.get(term), TermData::Const(_)) && bv_width(terms, term).is_some() {
            out.push(term);
            return;
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                for &a in args.clone().iter() {
                    visit(terms, a, seen, out);
                }
            }
            TermData::Not(inner) => visit(terms, *inner, seen, out),
            TermData::Ite(c, t, e) => {
                visit(terms, *c, seen, out);
                visit(terms, *t, seen, out);
                visit(terms, *e, seen, out);
            }
            TermData::Let(bindings, body) => {
                for (_, v) in bindings.clone().iter() {
                    visit(terms, *v, seen, out);
                }
                visit(terms, *body, seen, out);
            }
            TermData::Forall(_, body, _) | TermData::Exists(_, body, _) => {
                visit(terms, *body, seen, out);
            }
            _ => {}
        }
    }
    let mut seen = HashSet::default();
    let mut out = Vec::new();
    for &root in roots {
        visit(terms, root, &mut seen, &mut out);
    }
    out
}

fn bv2nat_arg(terms: &TermStore, term: TermId) -> Option<TermId> {
    match terms.get(term) {
        TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1 => {
            Some(args[0])
        }
        _ => None,
    }
}

/// If `term` is `int2bv(width, e)` of the given width, return its Int argument
/// `e`; otherwise `None`.
fn int2bv_arg(terms: &TermStore, term: TermId, width: u32) -> Option<TermId> {
    match terms.get(term) {
        TermData::App(Symbol::Indexed(name, indices), args)
            if name == "int2bv" && indices.len() == 1 && indices[0] == width && args.len() == 1 =>
        {
            Some(args[0])
        }
        _ => None,
    }
}

/// Collect every distinct `bv2nat` argument (the BV expression whose unsigned
/// Int value is taken) reachable from `roots`. These are exactly the BV terms
/// the residue bridge must tie back to their Int views.
fn collect_bv2nat_arg_subterms(terms: &TermStore, roots: &[TermId]) -> Vec<TermId> {
    fn visit(terms: &TermStore, term: TermId, seen: &mut HashSet<TermId>, out: &mut Vec<TermId>) {
        if !seen.insert(term) {
            return;
        }
        if let Some(arg) = bv2nat_arg(terms, term) {
            out.push(arg);
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                for &arg in args {
                    visit(terms, arg, seen, out);
                }
            }
            TermData::Not(inner) => visit(terms, *inner, seen, out),
            TermData::Ite(c, t, e) => {
                visit(terms, *c, seen, out);
                visit(terms, *t, seen, out);
                visit(terms, *e, seen, out);
            }
            TermData::Let(bindings, body) => {
                for (_, bound) in bindings {
                    visit(terms, *bound, seen, out);
                }
                visit(terms, *body, seen, out);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                visit(terms, *body, seen, out);
                for trigger in triggers {
                    for &t in trigger {
                        visit(terms, t, seen, out);
                    }
                }
            }
            _ => {}
        }
    }

    let mut seen = HashSet::default();
    let mut out = Vec::new();
    for &root in roots {
        visit(terms, root, &mut seen, &mut out);
    }
    out.sort_unstable_by_key(|t| t.0);
    out.dedup();
    out
}

/// Collect every distinct `int2bv(width, source)` subterm reachable from
/// `roots`, returned as `(int2bv_term, width, source)`. These are exactly the
/// concrete BV witnesses an `int2bv`-injectivity bridge can pin a `bv2nat`
/// argument onto.
fn collect_int2bv_terms(terms: &TermStore, roots: &[TermId]) -> Vec<(TermId, u32, TermId)> {
    fn visit(
        terms: &TermStore,
        term: TermId,
        seen: &mut HashSet<TermId>,
        out: &mut Vec<(TermId, u32, TermId)>,
    ) {
        if !seen.insert(term) {
            return;
        }
        if let TermData::App(Symbol::Indexed(name, indices), args) = terms.get(term) {
            if name == "int2bv" && indices.len() == 1 && args.len() == 1 {
                out.push((term, indices[0], args[0]));
            }
        }
        match terms.get(term) {
            TermData::App(_, args) => {
                for &arg in args {
                    visit(terms, arg, seen, out);
                }
            }
            TermData::Not(inner) => visit(terms, *inner, seen, out),
            TermData::Ite(c, t, e) => {
                visit(terms, *c, seen, out);
                visit(terms, *t, seen, out);
                visit(terms, *e, seen, out);
            }
            TermData::Let(bindings, body) => {
                for (_, bound) in bindings {
                    visit(terms, *bound, seen, out);
                }
                visit(terms, *body, seen, out);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                visit(terms, *body, seen, out);
                for trigger in triggers {
                    for &t in trigger {
                        visit(terms, t, seen, out);
                    }
                }
            }
            _ => {}
        }
    }

    let mut seen = HashSet::default();
    let mut out = Vec::new();
    for &root in roots {
        visit(terms, root, &mut seen, &mut out);
    }
    out.sort_unstable_by_key(|(t, w, s)| (t.0, *w, s.0));
    out.dedup();
    out
}

fn equivalent_bv2nat_args(terms: &TermStore, facts: &IntFactIndex, term: TermId) -> Vec<TermId> {
    let mut out = Vec::new();
    if let Some(arg) = bv2nat_arg(terms, term) {
        out.push(arg);
    }
    for candidate in facts.class_terms(term) {
        if candidate == term {
            continue;
        }
        if let Some(arg) = bv2nat_arg(terms, candidate) {
            out.push(arg);
        }
    }
    out.sort_unstable();
    out.dedup();
    out
}

fn collect_bv_nat_upper_bound_obligations(
    terms: &TermStore,
    facts: &IntFactIndex,
    root: TermId,
    out: &mut Vec<(TermId, BigInt)>,
) {
    match terms.get(root) {
        TermData::App(Symbol::Named(name), args) if name == "and" => {
            for &arg in args {
                collect_bv_nat_upper_bound_obligations(terms, facts, arg, out);
            }
        }
        TermData::Not(inner) => {
            if let TermData::App(Symbol::Named(name), args) = terms.get(*inner) {
                if name == "<=" && args.len() == 2 {
                    if let Some(bound) = int_const_value(terms, args[1]) {
                        for bv in equivalent_bv2nat_args(terms, facts, args[0]) {
                            out.push((bv, bound.clone()));
                        }
                    }
                }
            }
        }
        TermData::App(Symbol::Named(name), args) if name == ">" && args.len() == 2 => {
            if let Some(bound) = int_const_value(terms, args[1]) {
                for bv in equivalent_bv2nat_args(terms, facts, args[0]) {
                    out.push((bv, bound.clone()));
                }
            }
        }
        // Canonical form of `bv2nat(x) > C`: ay interns `mk_gt(a, b)` as
        // `mk_lt(b, a)` (arith_div_cmp.rs), so a `result@ > C` obligation (the
        // negation of a `result@ <= C` postcondition, e.g. popcount's
        // `result@ <= 8`) appears as `(< C x)` with the constant on the LEFT.
        // Recognize it as the same upper-bound obligation.
        TermData::App(Symbol::Named(name), args) if name == "<" && args.len() == 2 => {
            if let Some(bound) = int_const_value(terms, args[0]) {
                for bv in equivalent_bv2nat_args(terms, facts, args[1]) {
                    out.push((bv, bound.clone()));
                }
            }
        }
        _ => {}
    }
}

fn collect_bv_nat_int_equality_obligations(
    terms: &TermStore,
    facts: &IntFactIndex,
    root: TermId,
    out: &mut Vec<(TermId, TermId)>,
) {
    match terms.get(root) {
        TermData::App(Symbol::Named(name), args) if name == "and" => {
            for &arg in args {
                collect_bv_nat_int_equality_obligations(terms, facts, arg, out);
            }
        }
        TermData::Not(inner) => {
            if let TermData::App(Symbol::Named(name), args) = terms.get(*inner) {
                if name == "=" && args.len() == 2 {
                    for bv in equivalent_bv2nat_args(terms, facts, args[0]) {
                        out.push((bv, args[1]));
                    }
                    for bv in equivalent_bv2nat_args(terms, facts, args[1]) {
                        out.push((bv, args[0]));
                    }
                }
            }
        }
        _ => {}
    }
}

fn parse_int_var_const_eq(terms: &TermStore, term: TermId) -> Option<(TermId, BigInt)> {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return None;
    };
    if name != "=" || args.len() != 2 {
        return None;
    }
    match (
        int_const_value(terms, args[0]),
        int_const_value(terms, args[1]),
    ) {
        (Some(value), None) if *terms.sort(args[1]) == Sort::Int => Some((args[1], value)),
        (None, Some(value)) if *terms.sort(args[0]) == Sort::Int => Some((args[0], value)),
        _ => None,
    }
}

fn bool_literal_atom(terms: &TermStore, term: TermId) -> (TermId, bool) {
    match terms.get(term) {
        TermData::Not(inner) => (*inner, false),
        _ => (term, true),
    }
}

fn record_int_ite_definition_clause(
    terms: &TermStore,
    defs: &mut HashMap<(TermId, TermId), IntIteDefinition>,
    term: TermId,
) {
    let TermData::App(Symbol::Named(name), args) = terms.get(term) else {
        return;
    };
    if name != "or" || args.len() != 2 {
        return;
    }

    for (lit_term, eq_term) in [(args[0], args[1]), (args[1], args[0])] {
        let Some((var, value)) = parse_int_var_const_eq(terms, eq_term) else {
            continue;
        };
        let (cond, positive) = bool_literal_atom(terms, lit_term);
        let entry = defs.entry((var, cond)).or_default();
        if positive {
            entry.when_false = Some(value);
        } else {
            entry.when_true = Some(value);
        }
    }
}

fn collect_int_ite_definitions(
    terms: &TermStore,
    roots: &[TermId],
) -> HashMap<(TermId, TermId), IntIteDefinition> {
    fn visit(
        terms: &TermStore,
        term: TermId,
        defs: &mut HashMap<(TermId, TermId), IntIteDefinition>,
        seen: &mut HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        record_int_ite_definition_clause(terms, defs, term);
        match terms.get(term) {
            TermData::App(Symbol::Named(name), args) if name == "and" => {
                for &arg in args {
                    visit(terms, arg, defs, seen);
                }
            }
            _ => {}
        }
    }

    let mut defs = HashMap::default();
    let mut seen = HashSet::default();
    for &root in roots {
        visit(terms, root, &mut defs, &mut seen);
    }
    defs
}

struct BvLiaBitblastTranslator<'a> {
    terms: &'a mut TermStore,
    facts: &'a IntFactIndex,
    int_residue_vars: HashMap<(TermId, u32), TermId>,
    range_assertions: Vec<TermId>,
}

impl<'a> BvLiaBitblastTranslator<'a> {
    fn new(terms: &'a mut TermStore, facts: &'a IntFactIndex) -> Self {
        Self {
            terms,
            facts,
            int_residue_vars: HashMap::default(),
            range_assertions: Vec::new(),
        }
    }

    fn translate_bv(&mut self, term: TermId) -> Option<TermId> {
        match self.terms.get(term).clone() {
            TermData::Const(Constant::BitVec { .. }) | TermData::Var(_, _) => {
                if matches!(self.terms.sort(term), Sort::BitVec(_)) {
                    Some(term)
                } else {
                    None
                }
            }
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "bvand" => self
                    .translate_bv_args(&args)
                    .and_then(|args| self.fold_bvand(args)),
                "bvor" => self
                    .translate_bv_args(&args)
                    .and_then(|args| self.fold_bvor(args)),
                "bvxor" => self
                    .translate_bv_args(&args)
                    .and_then(|args| self.fold_bvxor(args)),
                "bvadd" => self
                    .translate_bv_args(&args)
                    .and_then(|args| self.fold_bvadd(args)),
                "bvsub" => self
                    .translate_bv_args(&args)
                    .and_then(|args| self.fold_bvsub(args)),
                // SMT-LIB shifts are width-preserving binary operations. Lift
                // both operands through the same exact residue translation as
                // the surrounding BV expression, then reconstruct the
                // identical operator in the pure-BV term consumed by the
                // existing bit-blast/enumeration gate. Requiring exact binary
                // arity keeps malformed internal terms fail-closed.
                "bvshl" if args.len() == 2 => {
                    let lhs = self.translate_bv(args[0])?;
                    let rhs = self.translate_bv(args[1])?;
                    Some(self.terms.mk_bvshl(vec![lhs, rhs]))
                }
                "bvlshr" if args.len() == 2 => {
                    let lhs = self.translate_bv(args[0])?;
                    let rhs = self.translate_bv(args[1])?;
                    Some(self.terms.mk_bvlshr(vec![lhs, rhs]))
                }
                "bvashr" if args.len() == 2 => {
                    let lhs = self.translate_bv(args[0])?;
                    let rhs = self.translate_bv(args[1])?;
                    Some(self.terms.mk_bvashr(vec![lhs, rhs]))
                }
                "bvnot" if args.len() == 1 => {
                    let arg = self.translate_bv(args[0])?;
                    Some(self.terms.mk_bvnot(arg))
                }
                "bvneg" if args.len() == 1 => {
                    let arg = self.translate_bv(args[0])?;
                    Some(self.terms.mk_bvneg(arg))
                }
                "concat" => self
                    .translate_bv_args(&args)
                    .map(|args| self.terms.mk_bvconcat(args)),
                _ => None,
            },
            TermData::App(Symbol::Indexed(name, indices), args)
                if name == "int2bv" && indices.len() == 1 && args.len() == 1 =>
            {
                self.translate_int_to_bv(args[0], indices[0])
            }
            TermData::App(Symbol::Indexed(name, indices), args)
                if name == "extract" && indices.len() == 2 && args.len() == 1 =>
            {
                let arg = self.translate_bv(args[0])?;
                Some(self.terms.mk_bvextract(indices[0], indices[1], arg))
            }
            TermData::App(Symbol::Indexed(name, indices), args)
                if name == "zero_extend" && indices.len() == 1 && args.len() == 1 =>
            {
                let arg = self.translate_bv(args[0])?;
                Some(self.terms.mk_bvzero_extend(indices[0], arg))
            }
            _ => None,
        }
    }

    fn translate_bv_args(&mut self, args: &[TermId]) -> Option<Vec<TermId>> {
        args.iter().map(|&arg| self.translate_bv(arg)).collect()
    }

    fn translate_int_to_bv(&mut self, term: TermId, width: u32) -> Option<TermId> {
        if let Some(value) = int_const_value(self.terms, term) {
            return Some(self.terms.mk_bitvec(value, width));
        }

        match self.terms.get(term).clone() {
            TermData::Var(_, _) if *self.terms.sort(term) == Sort::Int => {
                Some(self.int_residue_var(term, width))
            }
            TermData::App(Symbol::Named(name), args) if name == "bv2nat" && args.len() == 1 => {
                let bv = self.translate_bv(args[0])?;
                self.resize_bv(bv, width)
            }
            TermData::App(Symbol::Named(name), args) if name == "+" => {
                let translated: Option<Vec<_>> = args
                    .iter()
                    .map(|&arg| self.translate_int_to_bv(arg, width))
                    .collect();
                translated.and_then(|args| self.fold_bvadd(args))
            }
            TermData::App(Symbol::Named(name), args) if name == "-" => match args.as_slice() {
                [] => None,
                [arg] => {
                    let arg = self.translate_int_to_bv(*arg, width)?;
                    Some(self.terms.mk_bvneg(arg))
                }
                [first, rest @ ..] => {
                    let mut acc = self.translate_int_to_bv(*first, width)?;
                    for &arg in rest {
                        let rhs = self.translate_int_to_bv(arg, width)?;
                        acc = self.terms.mk_bvsub(vec![acc, rhs]);
                    }
                    Some(acc)
                }
            },
            _ => None,
        }
    }

    fn resize_bv(&mut self, term: TermId, width: u32) -> Option<TermId> {
        let source_width = bv_width(self.terms, term)?;
        if source_width == width {
            Some(term)
        } else if source_width < width {
            Some(self.terms.mk_bvzero_extend(width - source_width, term))
        } else if width == 0 {
            None
        } else {
            Some(self.terms.mk_bvextract(width - 1, 0, term))
        }
    }

    fn fold_bvadd(&mut self, args: Vec<TermId>) -> Option<TermId> {
        self.fold_bv_binary(args, |terms, lhs, rhs| terms.mk_bvadd(vec![lhs, rhs]))
    }

    fn fold_bvsub(&mut self, args: Vec<TermId>) -> Option<TermId> {
        self.fold_bv_binary(args, |terms, lhs, rhs| terms.mk_bvsub(vec![lhs, rhs]))
    }

    fn fold_bvand(&mut self, args: Vec<TermId>) -> Option<TermId> {
        self.fold_bv_binary(args, |terms, lhs, rhs| terms.mk_bvand(vec![lhs, rhs]))
    }

    fn fold_bvor(&mut self, args: Vec<TermId>) -> Option<TermId> {
        self.fold_bv_binary(args, |terms, lhs, rhs| terms.mk_bvor(vec![lhs, rhs]))
    }

    fn fold_bvxor(&mut self, args: Vec<TermId>) -> Option<TermId> {
        self.fold_bv_binary(args, |terms, lhs, rhs| terms.mk_bvxor(vec![lhs, rhs]))
    }

    fn fold_bv_binary(
        &mut self,
        args: Vec<TermId>,
        mut f: impl FnMut(&mut TermStore, TermId, TermId) -> TermId,
    ) -> Option<TermId> {
        let mut iter = args.into_iter();
        let mut acc = iter.next()?;
        for arg in iter {
            acc = f(self.terms, acc, arg);
        }
        Some(acc)
    }

    fn int_residue_var(&mut self, term: TermId, width: u32) -> TermId {
        if let Some(&existing) = self.int_residue_vars.get(&(term, width)) {
            return existing;
        }

        let var = self.terms.mk_fresh_var(
            &format!("__ay_bv_lia_i{}_w{}", term.0, width),
            Sort::bitvec(width),
        );
        self.int_residue_vars.insert((term, width), var);
        self.push_range_assertions(term, width, var);
        self.push_residue_congruence(term, width, var);
        var
    }

    /// Assert the EXACT modular congruence relating the fresh BV residue var
    /// (which stands for `int2bv(int_term, width)`) back to its integer source:
    ///
    /// ```text
    ///   bv2nat(bv_var) = int_term - 2^w * k     (k a FRESH unconstrained Int)
    ///   0 <= bv2nat(bv_var) <= 2^w - 1
    /// ```
    ///
    /// plus, when a signed view of the source is in play, the signed companion
    ///
    /// ```text
    ///   sbv2int(bv_var) = ite(msb(bv_var), bv2nat(bv_var) - 2^w, bv2nat(bv_var))
    /// ```
    ///
    /// which `mk_bv2int(.., is_signed=true)` builds verbatim. This is the SMT-LIB
    /// definition of int2bv/bv2nat: `bv2nat(bv_var)` is the unique residue of
    /// `int_term` modulo `2^w`. SOUNDNESS: asserted as an EQUALITY with an
    /// explicit `2^w * k` slack (k unconstrained) and the `0 <= . < 2^w` bound,
    /// so it is EXACT and can only enable MORE valid UNSATs, never a false one.
    fn push_residue_congruence(&mut self, int_term: TermId, width: u32, bv_var: TermId) {
        let nat = self.terms.mk_bv2nat(bv_var);
        // 0 <= bv2nat(bv_var) <= 2^w - 1
        let zero = self.terms.mk_int(BigInt::zero());
        let max = self.terms.mk_int((BigInt::one() << width) - BigInt::one());
        let lo = self.terms.mk_ge(nat, zero);
        let hi = self.terms.mk_le(nat, max);
        self.range_assertions.push(lo);
        self.range_assertions.push(hi);
        // bv2nat(bv_var) = int_term - 2^w * k   (k fresh, unconstrained)
        let modulus = self.terms.mk_int(BigInt::one() << width);
        let k = self.terms.mk_fresh_var(
            &format!("__ay_bv_lia_cong_k{}_w{}", int_term.0, width),
            Sort::Int,
        );
        let scaled_k = self.terms.mk_mul(vec![modulus, k]);
        let rhs = self.terms.mk_sub(vec![int_term, scaled_k]);
        let cong = self.terms.mk_eq(nat, rhs);
        self.range_assertions.push(cong);
        // Signed companion: relate the signed interpretation of the residue to
        // its two's-complement value (msb-conditional offset). `mk_bv2int` with
        // is_signed=true emits exactly `ite(msb, bv2nat - 2^w, bv2nat)`, so the
        // equation is a tautology that anchors `sbv2int(bv_var)` for the LIA
        // window when the source was encoded as a signed view.
        let signed = self.terms.mk_bv2int(bv_var, true);
        let signed_def_neg = {
            let m = self.terms.mk_int(BigInt::one() << width);
            self.terms.mk_sub(vec![nat, m])
        };
        let msb_set = {
            let zero_bv = self.terms.mk_bitvec(BigInt::zero(), width);
            self.terms.mk_bvslt(bv_var, zero_bv)
        };
        let signed_def = self.terms.mk_ite(msb_set, signed_def_neg, nat);
        let signed_cong = self.terms.mk_eq(signed, signed_def);
        self.range_assertions.push(signed_cong);
    }

    fn push_range_assertions(&mut self, int_term: TermId, width: u32, bv_var: TermId) {
        let max = (BigInt::one() << width) - BigInt::one();
        if let Some(lower) = self.facts.lower_bound(int_term) {
            if !lower.is_negative() && !lower.is_zero() && lower <= &max {
                let lower_bv = self.terms.mk_bitvec(lower.clone(), width);
                self.range_assertions
                    .push(self.terms.mk_bvuge(bv_var, lower_bv));
            }
        }
        if let Some(upper) = self.facts.upper_bound(int_term) {
            if !upper.is_negative() && upper < &max {
                let upper_bv = self.terms.mk_bitvec(upper.clone(), width);
                self.range_assertions
                    .push(self.terms.mk_bvule(bv_var, upper_bv));
            }
        }
    }

    fn into_range_assertions(self) -> Vec<TermId> {
        self.range_assertions
    }

    fn residue_bindings(&self) -> Vec<BvLiaResidueBinding> {
        let mut bindings: Vec<_> = self
            .int_residue_vars
            .iter()
            .map(|(&(int_term, width), &bv_var)| BvLiaResidueBinding {
                int_term,
                width,
                bv_var,
            })
            .collect();
        bindings
            .sort_unstable_by_key(|binding| (binding.int_term.0, binding.width, binding.bv_var.0));
        bindings
    }
}

impl Executor {
    fn assertion_contains_int_div_mod(&self, assertion: TermId) -> bool {
        crate::features::StaticFeatures::collect(&self.ctx.terms, &[assertion]).has_int_div_mod
    }

    fn select_mod_free_or_branches(
        &self,
        assertion: TermId,
        global_divisors: &HashSet<TermId>,
    ) -> Option<Vec<TermId>> {
        if !self.assertion_contains_int_div_mod(assertion) {
            return None;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
            return None;
        };
        if sym.name() != "or" {
            return None;
        }
        let mod_free_args: Vec<_> = args
            .iter()
            .copied()
            .filter(|&arg| !self.assertion_contains_int_div_mod(arg))
            .collect();
        let zero_divisor_branches: Vec<_> = mod_free_args
            .iter()
            .copied()
            .filter(|&arg| self.is_zero_equality_for_any(arg, global_divisors))
            .collect();
        if !zero_divisor_branches.is_empty() {
            return Some(zero_divisor_branches);
        }
        mod_free_args.first().copied().map(|branch| vec![branch])
    }

    fn int_div_mod_divisors(&self, assertion: TermId) -> HashSet<TermId> {
        let mut divisors = HashSet::default();
        let mut seen = HashSet::default();
        self.collect_int_div_mod_divisors(assertion, &mut divisors, &mut seen);
        divisors
    }

    fn collect_int_div_mod_divisors(
        &self,
        term: TermId,
        divisors: &mut HashSet<TermId>,
        seen: &mut HashSet<TermId>,
    ) {
        if !seen.insert(term) {
            return;
        }
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if matches!(sym.name(), "mod" | "div") && args.len() == 2 => {
                divisors.insert(args[1]);
                for &arg in args {
                    self.collect_int_div_mod_divisors(arg, divisors, seen);
                }
            }
            TermData::App(_, args) => {
                for &arg in args {
                    self.collect_int_div_mod_divisors(arg, divisors, seen);
                }
            }
            TermData::Not(inner) => self.collect_int_div_mod_divisors(*inner, divisors, seen),
            TermData::Ite(cond, then_term, else_term) => {
                self.collect_int_div_mod_divisors(*cond, divisors, seen);
                self.collect_int_div_mod_divisors(*then_term, divisors, seen);
                self.collect_int_div_mod_divisors(*else_term, divisors, seen);
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    self.collect_int_div_mod_divisors(*value, divisors, seen);
                }
                self.collect_int_div_mod_divisors(*body, divisors, seen);
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                self.collect_int_div_mod_divisors(*body, divisors, seen);
                for trigger in triggers.iter().flatten().copied() {
                    self.collect_int_div_mod_divisors(trigger, divisors, seen);
                }
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }

    fn is_zero_equality_for_any(&self, term: TermId, candidates: &HashSet<TermId>) -> bool {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return false;
        };
        sym.name() == "="
            && args.len() == 2
            && ((self.is_zero_int_term(args[0]) && candidates.contains(&args[1]))
                || (self.is_zero_int_term(args[1]) && candidates.contains(&args[0])))
    }

    fn is_zero_int_term(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.get(term), TermData::Const(Constant::Int(value)) if value.is_zero())
    }

    pub(in crate::executor) fn int_div_mod_terms_have_known_zero_or_constant_divisors(
        &self,
        assertions: &[TermId],
    ) -> bool {
        let zero_terms = self.zero_equal_terms(assertions);
        let mut saw_div_mod = false;
        let mut all_supported = true;
        let mut seen = HashSet::default();
        for &assertion in assertions {
            self.check_int_div_mod_divisors_supported(
                assertion,
                &zero_terms,
                &mut saw_div_mod,
                &mut all_supported,
                &mut seen,
            );
            if !all_supported {
                return false;
            }
        }
        saw_div_mod
    }

    fn assertion_window_int_div_mod_divisors(&self) -> HashSet<TermId> {
        let mut divisors = HashSet::default();
        for &assertion in &self.ctx.assertions {
            divisors.extend(self.int_div_mod_divisors(assertion));
        }
        divisors
    }

    fn assertion_window_has_quantifier_consumer_completion_marker(
        &self,
        assertions: &[TermId],
    ) -> bool {
        let mut seen = HashSet::default();
        assertions.iter().copied().any(|assertion| {
            self.term_has_quantifier_consumer_completion_marker(assertion, &mut seen)
        })
    }

    fn assertion_window_has_quantifier_consumer_singleton_prefix_array_ext_eq(
        &self,
        assertions: &[TermId],
    ) -> bool {
        let mut seen = HashSet::default();
        assertions.iter().copied().any(|assertion| {
            self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(assertion, &mut seen)
        })
    }

    fn term_has_quantifier_consumer_singleton_prefix_array_ext_eq(
        &self,
        term: TermId,
        seen: &mut HashSet<TermId>,
    ) -> bool {
        if !seen.insert(term) {
            return false;
        }
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "seq_array" && args.len() == 1 => {
                self.is_quantifier_consumer_singleton_prefix_concat(args[0])
            }
            TermData::App(_, args) => args.iter().copied().any(|arg| {
                self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(arg, seen)
            }),
            TermData::Not(inner) => {
                self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(*inner, seen)
            }
            TermData::Ite(cond, then_term, else_term) => {
                self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(*cond, seen)
                    || self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(
                        *then_term, seen,
                    )
                    || self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(
                        *else_term, seen,
                    )
            }
            TermData::Let(bindings, body) => {
                bindings.iter().any(|(_, value)| {
                    self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(*value, seen)
                }) || self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(*body, seen)
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(*body, seen)
                    || triggers.iter().flatten().copied().any(|pattern| {
                        self.term_has_quantifier_consumer_singleton_prefix_array_ext_eq(
                            pattern, seen,
                        )
                    })
            }
            TermData::Const(_) | TermData::Var(_, _) => false,
            _ => false,
        }
    }

    fn is_quantifier_consumer_singleton_prefix_concat(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if sym.name() == "seq_concat" && args.len() == 2 => {
                matches!(
                    self.ctx.terms.get(args[0]),
                    TermData::App(singleton_sym, singleton_args)
                        if singleton_sym.name() == "seq_singleton" && singleton_args.len() == 1
                )
            }
            _ => false,
        }
    }

    fn term_has_quantifier_consumer_completion_marker(
        &self,
        term: TermId,
        seen: &mut HashSet<TermId>,
    ) -> bool {
        if !seen.insert(term) {
            return false;
        }
        match self.ctx.terms.get(term) {
            TermData::Var(name, _) => is_quantifier_consumer_completion_marker_name(name),
            TermData::App(sym, args) => {
                is_quantifier_consumer_completion_marker_name(sym.name())
                    || args
                        .iter()
                        .copied()
                        .any(|arg| self.term_has_quantifier_consumer_completion_marker(arg, seen))
            }
            TermData::Not(inner) => {
                self.term_has_quantifier_consumer_completion_marker(*inner, seen)
            }
            TermData::Ite(cond, then_term, else_term) => {
                self.term_has_quantifier_consumer_completion_marker(*cond, seen)
                    || self.term_has_quantifier_consumer_completion_marker(*then_term, seen)
                    || self.term_has_quantifier_consumer_completion_marker(*else_term, seen)
            }
            TermData::Let(bindings, body) => {
                bindings.iter().any(|(_, value)| {
                    self.term_has_quantifier_consumer_completion_marker(*value, seen)
                }) || self.term_has_quantifier_consumer_completion_marker(*body, seen)
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                self.term_has_quantifier_consumer_completion_marker(*body, seen)
                    || triggers.iter().flatten().copied().any(|pattern| {
                        self.term_has_quantifier_consumer_completion_marker(pattern, seen)
                    })
            }
            TermData::Const(_) => false,
            _ => false,
        }
    }

    fn zero_equal_terms(&self, assertions: &[TermId]) -> HashSet<TermId> {
        let mut zero_terms = HashSet::default();
        for &assertion in assertions {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "=" || args.len() != 2 {
                continue;
            }
            if self.is_zero_int_term(args[0]) {
                zero_terms.insert(args[1]);
            }
            if self.is_zero_int_term(args[1]) {
                zero_terms.insert(args[0]);
            }
        }
        zero_terms
    }

    fn assertions_have_quantifier_consumer_restore_zero_divisor_contradiction(
        &self,
        assertions: &[TermId],
    ) -> bool {
        let zero_terms = self.zero_equal_terms(assertions);
        if zero_terms.is_empty() {
            return false;
        }

        let mut positives = Vec::new();
        let mut negatives = Vec::new();
        for &assertion in assertions {
            let Some((negated, value, seq, index)) =
                self.quantifier_consumer_restore_equality_from_assertion(assertion)
            else {
                continue;
            };
            if negated {
                negatives.push((value, seq, index));
            } else {
                positives.push((value, seq, index));
            }
        }

        positives.iter().any(|&(value, seq, index)| {
            negatives.iter().any(|&(neg_value, neg_seq, neg_index)| {
                value == neg_value
                    && seq == neg_seq
                    && self.restore_indices_equal_under_zero_mod(index, neg_index, &zero_terms)
            })
        })
    }

    fn quantifier_consumer_restore_equality_from_assertion(
        &self,
        assertion: TermId,
    ) -> Option<(bool, TermId, TermId, TermId)> {
        let (negated, equality) = match self.ctx.terms.get(assertion) {
            TermData::Not(inner) => (true, *inner),
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => (true, args[0]),
            _ => (false, assertion),
        };
        let TermData::App(sym, args) = self.ctx.terms.get(equality) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }
        self.quantifier_consumer_restore_equality_ordered(args[0], args[1])
            .or_else(|| self.quantifier_consumer_restore_equality_ordered(args[1], args[0]))
            .map(|(value, seq, index)| (negated, value, seq, index))
    }

    fn quantifier_consumer_restore_equality_ordered(
        &self,
        value: TermId,
        restore: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(restore) else {
            return None;
        };
        // `.then(..)` (lazy), NOT `.then_some(..)`: then_some evaluates its
        // argument EAGERLY, so `args[0]`/`args[1]` would panic for any App
        // with fewer than 2 args reaching this probe -- even when the guard
        // is false. (Latent since introduction; exposed by routing changes.)
        (sym.name().starts_with("__seq_index_restore_") && args.len() == 2)
            .then(|| (value, args[0], args[1]))
    }

    fn restore_indices_equal_under_zero_mod(
        &self,
        lhs: TermId,
        rhs: TermId,
        zero_terms: &HashSet<TermId>,
    ) -> bool {
        self.zero_mod_dividend(lhs, zero_terms)
            .is_some_and(|dividend| dividend == rhs)
            || self
                .zero_mod_dividend(rhs, zero_terms)
                .is_some_and(|dividend| dividend == lhs)
    }

    /// UNSOUND AS ORIGINALLY WRITTEN — kept only as a tombstone.
    ///
    /// This returned `Some(dividend)` for `(mod dividend d)` whenever `d` was
    /// known to be zero, i.e. it asserted the identity
    ///
    /// ```text
    /// (mod a 0) == a
    /// ```
    ///
    /// **That identity does not hold in SMT-LIB.** `(mod a 0)` is
    /// UNCONSTRAINED — it may take ANY integer value — which AY's own `mk_mod`
    /// documents and deliberately protects (`#div0-soundness`, it refuses to
    /// fold `x mod x`, `0 mod x` or a constant `mod` when the divisor may be 0).
    /// This function contradicted that.
    ///
    /// The consequence was a WRONG UNSAT, reached through
    /// `assertions_have_quantifier_consumer_restore_zero_divisor_contradiction`, which
    /// returns `SolveResult::unsat()` OUTRIGHT when a positive
    /// `v = restore(s, i)` meets a negative `v != restore(s, j)` and this
    /// function claimed `i` and `j` were equal. Reproducer (z3 4.15.4 answers
    /// `sat` and prints a witness):
    ///
    /// ```text
    /// (assert (not (= list_current (__seq_index_restore_List view dividend))))
    /// (assert (= list_current (__seq_index_restore_List view (mod dividend divisor))))
    /// (assert (or (= 0 p48) (= 0 divisor) ...))
    /// ```
    ///
    /// z3's model takes `divisor = 0`, `dividend = -1`, `mod(-1,0) = 0`, and
    /// `restore(view,-1) = (cons 5 nil)` while `restore(view,0) = nil`. The two
    /// restore calls have DIFFERENT indices, so there is no contradiction — the
    /// detector manufactured one.
    ///
    /// It was invisible because the pinning test asserted `expect_not_sat`,
    /// which ACCEPTS `unsat`: a one-sided assertion cannot catch a wrong answer
    /// on the side it permits.
    ///
    /// There is no repair. Two restore indices are equal only if their VALUES
    /// are equal, and `(mod a 0)` has no determined value, so no syntactic test
    /// can establish it. Returning `None` unconditionally makes the detector
    /// inert on this shape; a genuine contradiction with a non-zero divisor is
    /// still found by the ordinary solver path.
    fn zero_mod_dividend(&self, _term: TermId, _zero_terms: &HashSet<TermId>) -> Option<TermId> {
        None
    }

    fn check_int_div_mod_divisors_supported(
        &self,
        term: TermId,
        zero_terms: &HashSet<TermId>,
        saw_div_mod: &mut bool,
        all_supported: &mut bool,
        seen: &mut HashSet<TermId>,
    ) {
        if !*all_supported || !seen.insert(term) {
            return;
        }
        match self.ctx.terms.get(term) {
            TermData::App(sym, args) if matches!(sym.name(), "mod" | "div") && args.len() == 2 => {
                *saw_div_mod = true;
                if !matches!(
                    self.ctx.terms.get(args[1]),
                    TermData::Const(Constant::Int(_))
                ) && !zero_terms.contains(&args[1])
                {
                    *all_supported = false;
                    return;
                }
                for &arg in args {
                    self.check_int_div_mod_divisors_supported(
                        arg,
                        zero_terms,
                        saw_div_mod,
                        all_supported,
                        seen,
                    );
                }
            }
            TermData::App(_, args) => {
                for &arg in args {
                    self.check_int_div_mod_divisors_supported(
                        arg,
                        zero_terms,
                        saw_div_mod,
                        all_supported,
                        seen,
                    );
                }
            }
            TermData::Not(inner) => self.check_int_div_mod_divisors_supported(
                *inner,
                zero_terms,
                saw_div_mod,
                all_supported,
                seen,
            ),
            TermData::Ite(cond, then_term, else_term) => {
                self.check_int_div_mod_divisors_supported(
                    *cond,
                    zero_terms,
                    saw_div_mod,
                    all_supported,
                    seen,
                );
                self.check_int_div_mod_divisors_supported(
                    *then_term,
                    zero_terms,
                    saw_div_mod,
                    all_supported,
                    seen,
                );
                self.check_int_div_mod_divisors_supported(
                    *else_term,
                    zero_terms,
                    saw_div_mod,
                    all_supported,
                    seen,
                );
            }
            TermData::Let(bindings, body) => {
                for (_, value) in bindings {
                    self.check_int_div_mod_divisors_supported(
                        *value,
                        zero_terms,
                        saw_div_mod,
                        all_supported,
                        seen,
                    );
                }
                self.check_int_div_mod_divisors_supported(
                    *body,
                    zero_terms,
                    saw_div_mod,
                    all_supported,
                    seen,
                );
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                self.check_int_div_mod_divisors_supported(
                    *body,
                    zero_terms,
                    saw_div_mod,
                    all_supported,
                    seen,
                );
                for trigger in triggers.iter().flatten().copied() {
                    self.check_int_div_mod_divisors_supported(
                        trigger,
                        zero_terms,
                        saw_div_mod,
                        all_supported,
                        seen,
                    );
                }
            }
            TermData::Const(_) | TermData::Var(_, _) => {}
            _ => {}
        }
    }

    pub(in crate::executor) fn try_sat_via_mod_free_or_branch(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        if self.mod_div_or_branch_rescue_depth > 0 {
            return Ok(None);
        }
        // The OR-branch rescue solves a syntactically stronger formula and
        // accepts SAT through a validation shortcut. Keep native Seq formulas
        // on the normal theory route; Seq-sorted UF proxies are just EUF
        // carriers after logic detection narrows them away from Seq theory.
        if crate::features::StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions)
            .has_seq_ops
        {
            return Ok(None);
        }

        let mut changed = false;
        let mut candidate = Vec::with_capacity(self.ctx.assertions.len());
        let global_divisors = self.assertion_window_int_div_mod_divisors();
        for &assertion in &self.ctx.assertions {
            if let Some(branches) = self.select_mod_free_or_branches(assertion, &global_divisors) {
                candidate.extend(branches);
                changed = true;
            } else {
                candidate.push(assertion);
            }
        }
        if !changed {
            return Ok(None);
        }
        if self.assertions_have_quantifier_consumer_restore_zero_divisor_contradiction(&candidate) {
            return Ok(Some(SolveResult::unsat()));
        }
        let candidate_features =
            crate::features::StaticFeatures::collect(&self.ctx.terms, &candidate);
        if candidate_features.has_int_div_mod
            && !self.int_div_mod_terms_have_known_zero_or_constant_divisors(&candidate)
        {
            return Ok(None);
        }

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, candidate);
        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_result = self.last_result.clone();
        let saved_skip_model_eval = self.skip_model_eval;
        let saved_branch_validation = self.sat_validated_by_mod_div_or_branch;
        self.mod_div_or_branch_rescue_depth += 1;

        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        self.sat_validated_by_mod_div_or_branch = false;

        let result = self.solve_auf_lia();
        self.mod_div_or_branch_rescue_depth -= 1;
        self.ctx.assertions = saved_assertions;

        match result {
            Ok(result) if result.is_sat() => {
                self.last_model_validated = false;
                self.sat_validated_by_mod_div_or_branch = true;
                self.last_unknown_reason = None;
                Ok(Some(SolveResult::Sat))
            }
            Ok(_) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Ok(None)
            }
            Err(err) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Err(err)
            }
        }
    }

    pub(in crate::executor) fn try_unsat_via_mod_free_subset(
        &mut self,
        assertions: &[TermId],
    ) -> Result<Option<SolveResult>> {
        if self.mod_div_or_branch_rescue_depth > 0 {
            return Ok(None);
        }

        let mut mod_free_assertions: Vec<_> = assertions
            .iter()
            .copied()
            .filter(|&assertion| !self.assertion_contains_int_div_mod(assertion))
            .collect();
        if mod_free_assertions.is_empty() || mod_free_assertions.len() == assertions.len() {
            return Ok(None);
        }

        let mut seen: HashSet<TermId> = mod_free_assertions.iter().copied().collect();
        for derived in self.positive_divisor_mod_bound_assertions(assertions, &mod_free_assertions)
        {
            if seen.insert(derived) {
                mod_free_assertions.push(derived);
            }
        }
        for derived in self.mod_equality_substituted_assertions(assertions) {
            if !self.assertion_contains_int_div_mod(derived) && seen.insert(derived) {
                mod_free_assertions.push(derived);
            }
        }
        for derived in
            self.quantifier_consumer_resize_unit_interval_equalities(&mod_free_assertions)
        {
            if seen.insert(derived) {
                mod_free_assertions.push(derived);
            }
        }

        if assertion_window_has_syntactic_contradiction(&self.ctx.terms, &mod_free_assertions)
            || self.assertions_have_simple_int_contradiction(&mod_free_assertions)
        {
            return Ok(Some(SolveResult::unsat()));
        }
        if let Some(result) = self.try_unsat_via_ground_uf_lia_subset(&mod_free_assertions)? {
            return Ok(Some(result));
        }

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, mod_free_assertions);
        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_result = self.last_result.clone();
        let saved_skip_model_eval = self.skip_model_eval;
        let saved_branch_validation = self.sat_validated_by_mod_div_or_branch;
        self.mod_div_or_branch_rescue_depth += 1;

        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        self.sat_validated_by_mod_div_or_branch = false;

        let result = self.solve_auf_lia();
        self.mod_div_or_branch_rescue_depth -= 1;
        self.ctx.assertions = saved_assertions;

        match result {
            Ok(result) if result.is_unsat() => {
                self.last_unknown_reason = None;
                Ok(Some(result))
            }
            Ok(_) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Ok(None)
            }
            Err(err) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Err(err)
            }
        }
    }

    fn try_unsat_via_ground_uf_lia_subset(
        &mut self,
        assertions: &[TermId],
    ) -> Result<Option<SolveResult>> {
        let subset: Vec<_> = assertions
            .iter()
            .copied()
            .filter(|&assertion| self.ground_uf_lia_subset_assertion_supported(assertion))
            .collect();
        if subset.is_empty() {
            return Ok(None);
        }
        if assertion_window_has_syntactic_contradiction(&self.ctx.terms, &subset)
            || self.assertions_have_simple_int_contradiction(&subset)
        {
            return Ok(Some(SolveResult::unsat()));
        }

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, subset);
        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_result = self.last_result.clone();
        let saved_skip_model_eval = self.skip_model_eval;
        let saved_branch_validation = self.sat_validated_by_mod_div_or_branch;
        self.mod_div_or_branch_rescue_depth += 1;

        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        self.sat_validated_by_mod_div_or_branch = false;

        let result = self.solve_uf_lia();
        self.mod_div_or_branch_rescue_depth -= 1;
        self.ctx.assertions = saved_assertions;

        match result {
            Ok(result) if result.is_unsat() => {
                self.last_unknown_reason = None;
                Ok(Some(result))
            }
            Ok(_) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Ok(None)
            }
            Err(err) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Err(err)
            }
        }
    }

    fn ground_uf_lia_subset_assertion_supported(&self, assertion: TermId) -> bool {
        fn sort_supported(sort: &Sort) -> bool {
            matches!(
                sort,
                Sort::Bool | Sort::Int | Sort::Uninterpreted(_) | Sort::Datatype(_)
            )
        }

        fn visit(terms: &TermStore, term: TermId, seen: &mut HashSet<TermId>) -> bool {
            if !seen.insert(term) {
                return true;
            }
            if !sort_supported(terms.sort(term)) {
                return false;
            }
            match terms.get(term) {
                TermData::Const(Constant::Bool(_)) | TermData::Const(Constant::Int(_)) => true,
                TermData::Const(_) => false,
                TermData::Var(_, _) => true,
                TermData::App(sym, args) => {
                    if matches!(sym.name(), "div" | "mod" | "select" | "store") {
                        return false;
                    }
                    args.iter().copied().all(|arg| visit(terms, arg, seen))
                }
                TermData::Not(inner) => visit(terms, *inner, seen),
                TermData::Ite(cond, then_term, else_term) => {
                    visit(terms, *cond, seen)
                        && visit(terms, *then_term, seen)
                        && visit(terms, *else_term, seen)
                }
                TermData::Let(bindings, body) => {
                    bindings.iter().all(|(_, value)| visit(terms, *value, seen))
                        && visit(terms, *body, seen)
                }
                TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => false,
                _ => false,
            }
        }

        let mut seen = HashSet::default();
        visit(&self.ctx.terms, assertion, &mut seen)
    }

    fn quantifier_consumer_resize_unit_interval_equalities(
        &mut self,
        assertions: &[TermId],
    ) -> Vec<TermId> {
        let facts = collect_int_facts(&self.ctx.terms, assertions);
        let mut out = Vec::new();
        let mut seen = HashSet::default();

        for &assertion in assertions {
            let Some((bucket, upper, eq_lhs, eq_rhs)) =
                self.quantifier_consumer_positive_len_interval_diseq_branch(assertion, &facts)
            else {
                continue;
            };
            let Some(base) = self.base_plus_one_for(upper, assertions) else {
                continue;
            };
            if self
                .assertions_entail_negated_lt_from_diseq(assertions, bucket, base, eq_lhs, eq_rhs)
            {
                let eq = self.ctx.terms.mk_eq(bucket, base);
                if seen.insert(eq) {
                    out.push(eq);
                }
            }
        }

        out
    }

    fn quantifier_consumer_positive_len_interval_diseq_branch(
        &self,
        assertion: TermId,
        facts: &IntFactIndex,
    ) -> Option<(TermId, TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
            return None;
        };
        if sym.name() != "or" || args.len() < 2 {
            return None;
        }
        if !args
            .iter()
            .copied()
            .any(|arg| self.zero_equality_has_positive_other_side(arg, facts))
        {
            return None;
        }

        for &arg in args {
            let TermData::App(and_sym, and_args) = self.ctx.terms.get(arg) else {
                continue;
            };
            if and_sym.name() != "and" {
                continue;
            }
            let mut interval = None;
            let mut diseq = None;
            for &and_arg in and_args {
                if interval.is_none() {
                    interval = self.strict_lt_args(and_arg);
                }
                if diseq.is_none() {
                    diseq = self.negated_equality_args(and_arg);
                }
            }
            if let (Some((bucket, upper)), Some((eq_lhs, eq_rhs))) = (interval, diseq) {
                return Some((bucket, upper, eq_lhs, eq_rhs));
            }
        }

        None
    }

    fn zero_equality_has_positive_other_side(&self, term: TermId, facts: &IntFactIndex) -> bool {
        let Some([lhs, rhs]) = self.eq_args_for_completion(term) else {
            return false;
        };
        (self.is_zero_int_term(lhs) && self.term_known_positive_from_int_facts(rhs, facts))
            || (self.is_zero_int_term(rhs) && self.term_known_positive_from_int_facts(lhs, facts))
    }

    fn strict_lt_args(&self, term: TermId) -> Option<(TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() == "<" && args.len() == 2 {
            Some((args[0], args[1]))
        } else {
            None
        }
    }

    fn negated_equality_args(&self, term: TermId) -> Option<(TermId, TermId)> {
        match self.ctx.terms.get(term) {
            TermData::Not(inner) => {
                let [lhs, rhs] = self.eq_args_for_completion(*inner)?;
                Some([lhs, rhs].into())
            }
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => {
                let [lhs, rhs] = self.eq_args_for_completion(args[0])?;
                Some([lhs, rhs].into())
            }
            _ => None,
        }
    }

    fn base_plus_one_for(&self, upper: TermId, assertions: &[TermId]) -> Option<TermId> {
        if let Some(base) = self.term_base_plus_one(upper) {
            return Some(base);
        }
        for &assertion in assertions {
            let Some([lhs, rhs]) = self.eq_args_for_completion(assertion) else {
                continue;
            };
            if lhs == upper {
                if let Some(base) = self.term_base_plus_one(rhs) {
                    return Some(base);
                }
            }
            if rhs == upper {
                if let Some(base) = self.term_base_plus_one(lhs) {
                    return Some(base);
                }
            }
        }
        None
    }

    fn term_base_plus_one(&self, term: TermId) -> Option<TermId> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() != "+" || args.len() != 2 {
            return None;
        }
        if self.is_one_int_term(args[0]) {
            return Some(args[1]);
        }
        if self.is_one_int_term(args[1]) {
            return Some(args[0]);
        }
        None
    }

    fn is_one_int_term(&self, term: TermId) -> bool {
        matches!(self.ctx.terms.get(term), TermData::Const(Constant::Int(value)) if value.is_one())
    }

    fn assert_contains_equality_pair(&self, assertion: TermId, lhs: TermId, rhs: TermId) -> bool {
        self.eq_args_for_completion(assertion)
            .is_some_and(|[a, b]| Self::same_term_pair(a, b, lhs, rhs))
    }

    fn assert_contains_negated_lt_pair(&self, assertion: TermId, lhs: TermId, rhs: TermId) -> bool {
        let inner = match self.ctx.terms.get(assertion) {
            TermData::Not(inner) => *inner,
            TermData::App(sym, args) if sym.name() == "not" && args.len() == 1 => args[0],
            _ => return false,
        };
        self.strict_lt_args(inner)
            .is_some_and(|(a, b)| a == lhs && b == rhs)
    }

    fn assertions_entail_negated_lt_from_diseq(
        &self,
        assertions: &[TermId],
        lt_lhs: TermId,
        lt_rhs: TermId,
        eq_lhs: TermId,
        eq_rhs: TermId,
    ) -> bool {
        for &assertion in assertions {
            let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
                continue;
            };
            if sym.name() != "or" {
                continue;
            }
            let has_eq = args
                .iter()
                .copied()
                .any(|arg| self.assert_contains_equality_pair(arg, eq_lhs, eq_rhs));
            let has_negated_lt = args
                .iter()
                .copied()
                .any(|arg| self.assert_contains_negated_lt_pair(arg, lt_lhs, lt_rhs));
            if has_eq && has_negated_lt {
                return true;
            }
        }
        false
    }

    fn same_term_pair(a: TermId, b: TermId, lhs: TermId, rhs: TermId) -> bool {
        (a == lhs && b == rhs) || (a == rhs && b == lhs)
    }

    fn mod_equality_substituted_assertions(&mut self, assertions: &[TermId]) -> Vec<TermId> {
        let replacements: Vec<_> = assertions
            .iter()
            .copied()
            .filter_map(|assertion| self.mod_equality_value_mod_and_divisor(assertion))
            .map(|(value_term, mod_term, _)| (mod_term, value_term))
            .collect();
        if replacements.is_empty() {
            return Vec::new();
        }

        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for &assertion in assertions {
            for &(from, to) in &replacements {
                if let Some(rewritten) = self.replace_ground_term(assertion, from, to) {
                    if rewritten != assertion && seen.insert(rewritten) {
                        out.push(rewritten);
                    }
                }
            }
        }
        out
    }

    fn replace_ground_term(&mut self, term: TermId, from: TermId, to: TermId) -> Option<TermId> {
        if term == from {
            return Some(to);
        }

        match self.ctx.terms.get(term).clone() {
            TermData::App(sym, args) => {
                let mut changed = false;
                let rewritten_args: Vec<_> = args
                    .into_iter()
                    .map(|arg| {
                        if let Some(rewritten) = self.replace_ground_term(arg, from, to) {
                            changed = true;
                            rewritten
                        } else {
                            arg
                        }
                    })
                    .collect();
                if !changed {
                    return None;
                }
                let name = sym.name().to_string();
                Some(match name.as_str() {
                    "and" => self.ctx.terms.mk_and(rewritten_args),
                    "or" => self.ctx.terms.mk_or(rewritten_args),
                    "not" if rewritten_args.len() == 1 => self.ctx.terms.mk_not(rewritten_args[0]),
                    "=" if rewritten_args.len() == 2 => {
                        self.ctx.terms.mk_eq(rewritten_args[0], rewritten_args[1])
                    }
                    _ => {
                        let sort = self.ctx.terms.sort(term).clone();
                        self.ctx.terms.mk_app(sym, rewritten_args, sort)
                    }
                })
            }
            TermData::Not(inner) => self
                .replace_ground_term(inner, from, to)
                .map(|rewritten| self.ctx.terms.mk_not(rewritten)),
            TermData::Ite(cond, then_term, else_term) => {
                let rewritten_cond = self.replace_ground_term(cond, from, to);
                let rewritten_then = self.replace_ground_term(then_term, from, to);
                let rewritten_else = self.replace_ground_term(else_term, from, to);
                if rewritten_cond.is_none() && rewritten_then.is_none() && rewritten_else.is_none()
                {
                    None
                } else {
                    Some(self.ctx.terms.mk_ite(
                        rewritten_cond.unwrap_or(cond),
                        rewritten_then.unwrap_or(then_term),
                        rewritten_else.unwrap_or(else_term),
                    ))
                }
            }
            TermData::Let(bindings, body) => {
                let mut changed = false;
                let rewritten_bindings: Vec<_> = bindings
                    .into_iter()
                    .map(|(name, value)| {
                        if let Some(rewritten) = self.replace_ground_term(value, from, to) {
                            changed = true;
                            (name, rewritten)
                        } else {
                            (name, value)
                        }
                    })
                    .collect();
                let rewritten_body = self.replace_ground_term(body, from, to);
                if let Some(rewritten) = rewritten_body {
                    Some(self.ctx.terms.mk_let(rewritten_bindings, rewritten))
                } else if changed {
                    Some(self.ctx.terms.mk_let(rewritten_bindings, body))
                } else {
                    None
                }
            }
            TermData::Forall(_, _, _) | TermData::Exists(_, _, _) => None,
            TermData::Const(_) | TermData::Var(_, _) => None,
            _ => None,
        }
    }

    fn positive_divisor_mod_bound_assertions(
        &mut self,
        assertions: &[TermId],
        mod_free_assertions: &[TermId],
    ) -> Vec<TermId> {
        let facts = collect_int_facts(&self.ctx.terms, mod_free_assertions);
        let mut out = Vec::new();
        let mut seen = HashSet::default();

        for &assertion in assertions {
            let Some((value_term, _, divisor)) = self.mod_equality_value_mod_and_divisor(assertion)
            else {
                continue;
            };
            if !self.term_known_positive_from_int_facts(divisor, &facts) {
                continue;
            }

            let zero = self.ctx.terms.mk_int(BigInt::zero());
            let positive_divisor = self.ctx.terms.mk_lt(zero, divisor);
            let lower = self.ctx.terms.mk_le(zero, value_term);
            let upper = self.ctx.terms.mk_lt(value_term, divisor);
            for bound in [positive_divisor, lower, upper] {
                if seen.insert(bound) {
                    out.push(bound);
                }
            }
        }

        out
    }

    fn mod_equality_value_mod_and_divisor(
        &self,
        assertion: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        let TermData::App(sym, args) = self.ctx.terms.get(assertion) else {
            return None;
        };
        if sym.name() != "=" || args.len() != 2 {
            return None;
        }

        self.mod_equality_side(args[0], args[1])
            .or_else(|| self.mod_equality_side(args[1], args[0]))
    }

    fn mod_equality_side(
        &self,
        value_term: TermId,
        mod_term: TermId,
    ) -> Option<(TermId, TermId, TermId)> {
        if *self.ctx.terms.sort(value_term) != Sort::Int
            || self.assertion_contains_int_div_mod(value_term)
        {
            return None;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(mod_term) else {
            return None;
        };
        if sym.name() == "mod" && args.len() == 2 && *self.ctx.terms.sort(args[1]) == Sort::Int {
            Some((value_term, mod_term, args[1]))
        } else {
            None
        }
    }

    fn term_known_positive_from_int_facts(&self, term: TermId, facts: &IntFactIndex) -> bool {
        int_const_value(&self.ctx.terms, term).is_some_and(|value| value.is_positive())
            || facts.lower_bound(term).is_some_and(Signed::is_positive)
    }

    pub(in crate::executor) fn try_sat_via_known_divisor_preprocessing(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        if self.mod_div_or_branch_rescue_depth > 0 {
            return Ok(None);
        }
        // This rescue accepts SAT through the same mod/div shortcut validation
        // path as the OR-branch rescue. Native Seq formulas need the normal
        // theory route; Seq-sorted UF proxies can use the arithmetic rescue.
        if crate::features::StaticFeatures::collect(&self.ctx.terms, &self.ctx.assertions)
            .has_seq_ops
        {
            return Ok(None);
        }
        if !self.int_div_mod_terms_have_known_zero_or_constant_divisors(&self.ctx.assertions) {
            return Ok(None);
        }

        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_result = self.last_result.clone();
        let saved_skip_model_eval = self.skip_model_eval;
        let saved_branch_validation = self.sat_validated_by_mod_div_or_branch;
        self.mod_div_or_branch_rescue_depth += 1;

        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        self.sat_validated_by_mod_div_or_branch = false;

        if let Some(result) = self.try_unsat_via_quantifier_consumer_completion_preprocess()? {
            self.mod_div_or_branch_rescue_depth -= 1;
            return Ok(Some(result));
        }

        let result = self.solve_auf_lia();
        self.mod_div_or_branch_rescue_depth -= 1;

        match result {
            Ok(result) if result.is_sat() => {
                self.last_model_validated = false;
                self.sat_validated_by_mod_div_or_branch = true;
                self.last_unknown_reason = None;
                Ok(Some(SolveResult::Sat))
            }
            Ok(_) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Ok(None)
            }
            Err(err) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.skip_model_eval = saved_skip_model_eval;
                self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
                Err(err)
            }
        }
    }

    /// Run QuantifierConsumer-specific preprocessing only as a consequence-preserving
    /// refutation probe. Syntactic "completion support" is not a SAT
    /// certificate: it constructs no total interpretation and model/cost
    /// filtering may have omitted quantified instances.
    fn try_unsat_via_quantifier_consumer_completion_preprocess(
        &mut self,
    ) -> Result<Option<SolveResult>> {
        let (preprocessed_assertions, _, _) =
            self.preprocess_auflia_assertions_with_proof_provenance();
        if assertion_window_has_syntactic_contradiction(&self.ctx.terms, &preprocessed_assertions)
            || self.assertions_have_simple_int_contradiction(&preprocessed_assertions)
        {
            return Ok(None);
        }
        if self.assertion_window_has_completion_forced_false(&preprocessed_assertions) {
            return Ok(Some(SolveResult::unsat()));
        }
        Ok(None)
    }

    pub(in crate::executor) fn assertions_have_simple_int_contradiction(
        &self,
        assertions: &[TermId],
    ) -> bool {
        let mut parent: HashMap<TermId, TermId> = HashMap::default();
        let mut class_const: HashMap<TermId, BigInt> = HashMap::default();

        fn find(parent: &mut HashMap<TermId, TermId>, term: TermId) -> TermId {
            let p = parent.get(&term).copied().unwrap_or(term);
            if p == term {
                term
            } else {
                let root = find(parent, p);
                parent.insert(term, root);
                root
            }
        }

        fn union(parent: &mut HashMap<TermId, TermId>, lhs: TermId, rhs: TermId) -> TermId {
            let lhs_root = find(parent, lhs);
            let rhs_root = find(parent, rhs);
            if lhs_root == rhs_root {
                return lhs_root;
            }
            let (root, child) = if lhs_root.0 <= rhs_root.0 {
                (lhs_root, rhs_root)
            } else {
                (rhs_root, lhs_root)
            };
            parent.insert(child, root);
            root
        }

        for &assertion in assertions {
            let Some([lhs, rhs]) = self.eq_args_for_completion(assertion) else {
                continue;
            };
            let root = union(&mut parent, lhs, rhs);
            for side in [lhs, rhs] {
                if let Some(value) = self.int_const_value(side) {
                    let root = find(&mut parent, root);
                    match class_const.get(&root) {
                        Some(existing) if existing != &value => return true,
                        Some(_) => {}
                        None => {
                            class_const.insert(root, value);
                        }
                    }
                }
            }
        }

        let mut normalized_const = HashMap::default();
        for (term, value) in class_const {
            let root = find(&mut parent, term);
            match normalized_const.get(&root) {
                Some(existing) if existing != &value => return true,
                Some(_) => {}
                None => {
                    normalized_const.insert(root, value);
                }
            }
        }

        for &assertion in assertions {
            if self.negated_equality_for_same_completion_class(assertion, &mut parent) {
                return true;
            }
            if self.eval_simple_int_predicate(assertion, &mut parent, &normalized_const)
                == Some(false)
            {
                return true;
            }
        }

        false
    }

    fn eq_args_for_completion(&self, term: TermId) -> Option<[TermId; 2]> {
        let TermData::App(sym, args) = self.ctx.terms.get(term) else {
            return None;
        };
        if sym.name() == "=" && args.len() == 2 {
            Some([args[0], args[1]])
        } else {
            None
        }
    }

    fn negated_equality_for_same_completion_class(
        &self,
        term: TermId,
        parent: &mut HashMap<TermId, TermId>,
    ) -> bool {
        let TermData::Not(inner) = self.ctx.terms.get(term) else {
            return false;
        };
        let Some([lhs, rhs]) = self.eq_args_for_completion(*inner) else {
            return false;
        };
        fn find(parent: &mut HashMap<TermId, TermId>, term: TermId) -> TermId {
            let p = parent.get(&term).copied().unwrap_or(term);
            if p == term {
                term
            } else {
                let root = find(parent, p);
                parent.insert(term, root);
                root
            }
        }
        lhs == rhs || find(parent, lhs) == find(parent, rhs)
    }

    fn eval_simple_int_predicate(
        &self,
        term: TermId,
        parent: &mut HashMap<TermId, TermId>,
        class_const: &HashMap<TermId, BigInt>,
    ) -> Option<bool> {
        let mut negated = false;
        let mut predicate = term;
        if let TermData::Not(inner) = self.ctx.terms.get(term) {
            negated = true;
            predicate = *inner;
        }
        let TermData::App(sym, args) = self.ctx.terms.get(predicate) else {
            return None;
        };
        if !matches!(sym.name(), "<" | "<=" | ">" | ">=") || args.len() != 2 {
            return None;
        }
        let lhs = self.int_value_from_completion_class(args[0], parent, class_const)?;
        let rhs = self.int_value_from_completion_class(args[1], parent, class_const)?;
        let value = match sym.name() {
            "<" => lhs < rhs,
            "<=" => lhs <= rhs,
            ">" => lhs > rhs,
            ">=" => lhs >= rhs,
            _ => unreachable!(),
        };
        Some(if negated { !value } else { value })
    }

    fn int_value_from_completion_class(
        &self,
        term: TermId,
        parent: &mut HashMap<TermId, TermId>,
        class_const: &HashMap<TermId, BigInt>,
    ) -> Option<BigInt> {
        if let Some(value) = self.int_const_value(term) {
            return Some(value);
        }
        fn find(parent: &mut HashMap<TermId, TermId>, term: TermId) -> TermId {
            let p = parent.get(&term).copied().unwrap_or(term);
            if p == term {
                term
            } else {
                let root = find(parent, p);
                parent.insert(term, root);
                root
            }
        }
        class_const.get(&find(parent, term)).cloned()
    }

    fn int_const_value(&self, term: TermId) -> Option<BigInt> {
        match self.ctx.terms.get(term) {
            TermData::Const(Constant::Int(value)) => Some(value.clone()),
            _ => None,
        }
    }

    fn bv_lia_enumeration_domains(
        facts: &IntFactIndex,
        bindings: &[BvLiaResidueBinding],
    ) -> Option<Vec<BvLiaEnumerationDomain>> {
        let mut domains = Vec::new();
        let mut seen = HashSet::default();
        let mut total = 1u64;

        for binding in bindings {
            if !seen.insert(binding.int_term) {
                continue;
            }

            let lower = facts.lower_bound(binding.int_term)?.clone();
            let upper = facts.upper_bound(binding.int_term)?.clone();
            if upper < lower {
                return None;
            }

            let count = (&upper - &lower + BigInt::one()).to_u64()?;
            total = total.checked_mul(count)?;
            if total > BV_LIA_BRIDGE_ENUMERATION_LIMIT {
                return None;
            }

            domains.push(BvLiaEnumerationDomain {
                int_term: binding.int_term,
                lower,
                upper,
            });
        }

        Some(domains)
    }

    fn bv_lia_residue(value: &BigInt, width: u32) -> Option<BigInt> {
        if width == 0 {
            return None;
        }
        let modulus = BigInt::one() << width;
        let mut residue = value % &modulus;
        if residue.is_negative() {
            residue += modulus;
        }
        Some(residue)
    }

    fn prove_bv_nat_upper_bound_by_enumeration(
        &self,
        facts: &IntFactIndex,
        translated_bv: TermId,
        bound: &BigInt,
        bindings: &[BvLiaResidueBinding],
    ) -> Option<bool> {
        let domains = Self::bv_lia_enumeration_domains(facts, bindings)?;
        let mut int_values = HashMap::default();
        let mut bv_values = HashMap::default();

        fn visit(
            terms: &TermStore,
            translated_bv: TermId,
            bound: &BigInt,
            bindings: &[BvLiaResidueBinding],
            domains: &[BvLiaEnumerationDomain],
            index: usize,
            int_values: &mut HashMap<TermId, BigInt>,
            bv_values: &mut HashMap<TermId, BigInt>,
        ) -> Option<bool> {
            if index == domains.len() {
                for binding in bindings {
                    let int_value = int_values.get(&binding.int_term)?;
                    let residue = Executor::bv_lia_residue(int_value, binding.width)?;
                    bv_values.insert(binding.bv_var, residue);
                }

                let value = Executor::evaluate_bv_expr(terms, translated_bv, bv_values)?;
                return Some(&value <= bound);
            }

            let domain = &domains[index];
            let mut value = domain.lower.clone();
            while value <= domain.upper {
                int_values.insert(domain.int_term, value.clone());
                match visit(
                    terms,
                    translated_bv,
                    bound,
                    bindings,
                    domains,
                    index + 1,
                    int_values,
                    bv_values,
                ) {
                    Some(true) => {}
                    other => return other,
                }
                value += BigInt::one();
            }

            int_values.remove(&domain.int_term);
            Some(true)
        }

        visit(
            &self.ctx.terms,
            translated_bv,
            bound,
            bindings,
            &domains,
            0,
            &mut int_values,
            &mut bv_values,
        )
    }

    fn eval_bv_lia_int_term(
        terms: &TermStore,
        term: TermId,
        values: &HashMap<TermId, BigInt>,
    ) -> Option<BigInt> {
        match terms.get(term) {
            TermData::Const(Constant::Int(value)) => Some(value.clone()),
            TermData::Var(_, _) => values.get(&term).cloned(),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "+" => {
                    let mut sum = BigInt::zero();
                    for &arg in args {
                        sum += Self::eval_bv_lia_int_term(terms, arg, values)?;
                    }
                    Some(sum)
                }
                "-" => match args.as_slice() {
                    [] => None,
                    [arg] => Some(-Self::eval_bv_lia_int_term(terms, *arg, values)?),
                    [first, rest @ ..] => {
                        let mut acc = Self::eval_bv_lia_int_term(terms, *first, values)?;
                        for &arg in rest {
                            acc -= Self::eval_bv_lia_int_term(terms, arg, values)?;
                        }
                        Some(acc)
                    }
                },
                "*" => {
                    let mut product = BigInt::one();
                    for &arg in args {
                        product *= Self::eval_bv_lia_int_term(terms, arg, values)?;
                    }
                    Some(product)
                }
                "div" => {
                    if args.len() != 2 {
                        return None;
                    }
                    let lhs = Self::eval_bv_lia_int_term(terms, args[0], values)?;
                    let rhs = Self::eval_bv_lia_int_term(terms, args[1], values)?;
                    if rhs.is_zero() {
                        None
                    } else {
                        Some(lhs / rhs)
                    }
                }
                "mod" => {
                    if args.len() != 2 {
                        return None;
                    }
                    let lhs = Self::eval_bv_lia_int_term(terms, args[0], values)?;
                    let rhs = Self::eval_bv_lia_int_term(terms, args[1], values)?;
                    if rhs.is_zero() {
                        return None;
                    }
                    let mut rem = lhs % &rhs;
                    if rem.is_negative() {
                        rem += rhs.abs();
                    }
                    Some(rem)
                }
                "abs" => {
                    if args.len() != 1 {
                        return None;
                    }
                    Some(Self::eval_bv_lia_int_term(terms, args[0], values)?.abs())
                }
                _ => None,
            },
            TermData::Ite(cond, then_term, else_term) => {
                if Self::eval_bv_lia_bool_term(terms, *cond, values)? {
                    Self::eval_bv_lia_int_term(terms, *then_term, values)
                } else {
                    Self::eval_bv_lia_int_term(terms, *else_term, values)
                }
            }
            _ => None,
        }
    }

    fn eval_bv_lia_bool_term(
        terms: &TermStore,
        term: TermId,
        values: &HashMap<TermId, BigInt>,
    ) -> Option<bool> {
        match terms.get(term) {
            TermData::Const(Constant::Bool(value)) => Some(*value),
            TermData::Not(inner) => Some(!Self::eval_bv_lia_bool_term(terms, *inner, values)?),
            TermData::App(Symbol::Named(name), args) => match name.as_str() {
                "and" => {
                    for &arg in args {
                        if !Self::eval_bv_lia_bool_term(terms, arg, values)? {
                            return Some(false);
                        }
                    }
                    Some(true)
                }
                "or" => {
                    for &arg in args {
                        if Self::eval_bv_lia_bool_term(terms, arg, values)? {
                            return Some(true);
                        }
                    }
                    Some(false)
                }
                "=>" if args.len() == 2 => {
                    let lhs = Self::eval_bv_lia_bool_term(terms, args[0], values)?;
                    let rhs = Self::eval_bv_lia_bool_term(terms, args[1], values)?;
                    Some(!lhs || rhs)
                }
                "xor" if args.len() == 2 => {
                    let lhs = Self::eval_bv_lia_bool_term(terms, args[0], values)?;
                    let rhs = Self::eval_bv_lia_bool_term(terms, args[1], values)?;
                    Some(lhs ^ rhs)
                }
                "=" if args.len() == 2 && *terms.sort(args[0]) == Sort::Int => {
                    let lhs = Self::eval_bv_lia_int_term(terms, args[0], values)?;
                    let rhs = Self::eval_bv_lia_int_term(terms, args[1], values)?;
                    Some(lhs == rhs)
                }
                "<" | "<=" | ">" | ">=" if args.len() == 2 => {
                    let lhs = Self::eval_bv_lia_int_term(terms, args[0], values)?;
                    let rhs = Self::eval_bv_lia_int_term(terms, args[1], values)?;
                    match name.as_str() {
                        "<" => Some(lhs < rhs),
                        "<=" => Some(lhs <= rhs),
                        ">" => Some(lhs > rhs),
                        ">=" => Some(lhs >= rhs),
                        _ => None,
                    }
                }
                _ => None,
            },
            TermData::Ite(cond, then_term, else_term) => {
                if Self::eval_bv_lia_bool_term(terms, *cond, values)? {
                    Self::eval_bv_lia_bool_term(terms, *then_term, values)
                } else {
                    Self::eval_bv_lia_bool_term(terms, *else_term, values)
                }
            }
            _ => None,
        }
    }

    fn assign_bv_lia_ite_values(
        terms: &TermStore,
        defs: &HashMap<(TermId, TermId), IntIteDefinition>,
        values: &mut HashMap<TermId, BigInt>,
    ) -> Option<()> {
        for (&(var, cond), def) in defs {
            let Some(cond_value) = Self::eval_bv_lia_bool_term(terms, cond, values) else {
                continue;
            };
            let value = if cond_value {
                def.when_true.as_ref()
            } else {
                def.when_false.as_ref()
            };
            let Some(value) = value else {
                continue;
            };
            if let Some(existing) = values.get(&var) {
                if existing != value {
                    return None;
                }
            } else {
                values.insert(var, value.clone());
            }
        }
        Some(())
    }

    fn prove_bv_nat_int_equality_by_enumeration(
        &self,
        facts: &IntFactIndex,
        ite_defs: &HashMap<(TermId, TermId), IntIteDefinition>,
        translated_bv: TermId,
        int_term: TermId,
        bindings: &[BvLiaResidueBinding],
    ) -> Option<bool> {
        let domains = Self::bv_lia_enumeration_domains(facts, bindings)?;
        let mut int_values = HashMap::default();
        let mut bv_values = HashMap::default();

        fn visit(
            terms: &TermStore,
            facts: &IntFactIndex,
            ite_defs: &HashMap<(TermId, TermId), IntIteDefinition>,
            translated_bv: TermId,
            int_term: TermId,
            bindings: &[BvLiaResidueBinding],
            domains: &[BvLiaEnumerationDomain],
            index: usize,
            int_values: &mut HashMap<TermId, BigInt>,
            bv_values: &mut HashMap<TermId, BigInt>,
        ) -> Option<bool> {
            if index == domains.len() {
                let mut scoped_int_values = int_values.clone();
                Executor::assign_bv_lia_ite_values(terms, ite_defs, &mut scoped_int_values)?;

                for binding in bindings {
                    let int_value = scoped_int_values.get(&binding.int_term)?;
                    let residue = Executor::bv_lia_residue(int_value, binding.width)?;
                    bv_values.insert(binding.bv_var, residue);
                }

                let bv_value = Executor::evaluate_bv_expr(terms, translated_bv, bv_values)?;
                let int_value =
                    Executor::eval_bv_lia_int_term(terms, int_term, &scoped_int_values)?;
                return Some(bv_value == int_value);
            }

            let domain = &domains[index];
            let class_terms = facts.class_terms(domain.int_term);
            let mut value = domain.lower.clone();
            while value <= domain.upper {
                for term in &class_terms {
                    int_values.insert(*term, value.clone());
                }
                int_values.insert(domain.int_term, value.clone());
                match visit(
                    terms,
                    facts,
                    ite_defs,
                    translated_bv,
                    int_term,
                    bindings,
                    domains,
                    index + 1,
                    int_values,
                    bv_values,
                ) {
                    Some(true) => {}
                    other => return other,
                }
                value += BigInt::one();
            }

            for term in class_terms {
                int_values.remove(&term);
            }
            int_values.remove(&domain.int_term);
            Some(true)
        }

        visit(
            &self.ctx.terms,
            facts,
            ite_defs,
            translated_bv,
            int_term,
            bindings,
            &domains,
            0,
            &mut int_values,
            &mut bv_values,
        )
    }

    fn run_bv_lia_bitblast_probe(&mut self, probe_assertions: Vec<TermId>) -> Result<bool> {
        use crate::executor::theories::bv::BvSolveConfig;

        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, probe_assertions);
        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_result = self.last_result.clone();
        let saved_skip_model_eval = self.skip_model_eval;

        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;

        let result = self.solve_bv_core(BvSolveConfig::qf_bv(), &[]);

        self.ctx.assertions = saved_assertions;
        self.last_model = saved_model;
        self.last_model_validated = saved_model_validated;
        self.last_unknown_reason = saved_unknown_reason;
        self.last_result = saved_result;
        self.skip_model_eval = saved_skip_model_eval;

        result.map(|result| result.is_unsat())
    }

    fn prove_bv_nat_upper_bound_by_bitblast(
        &mut self,
        facts: &IntFactIndex,
        bv_term: TermId,
        bound: &BigInt,
    ) -> Result<Option<TermId>> {
        if bound.is_negative() {
            return Ok(None);
        }
        let Some(width) = bv_width(&self.ctx.terms, bv_term) else {
            return Ok(None);
        };
        let max = (BigInt::one() << width) - BigInt::one();
        if bound >= &max {
            let nat = self.ctx.terms.mk_bv2nat(bv_term);
            let bound = self.ctx.terms.mk_int(bound.clone());
            return Ok(Some(self.ctx.terms.mk_le(nat, bound)));
        }

        let (translated_bv, mut probe_assertions, residue_bindings) = {
            let mut translator = BvLiaBitblastTranslator::new(&mut self.ctx.terms, facts);
            let Some(translated_bv) = translator.translate_bv(bv_term) else {
                return Ok(None);
            };
            let residue_bindings = translator.residue_bindings();
            (
                translated_bv,
                translator.into_range_assertions(),
                residue_bindings,
            )
        };

        if matches!(
            self.prove_bv_nat_upper_bound_by_enumeration(
                facts,
                translated_bv,
                bound,
                &residue_bindings,
            ),
            Some(true)
        ) {
            let nat = self.ctx.terms.mk_bv2nat(bv_term);
            let bound = self.ctx.terms.mk_int(bound.clone());
            return Ok(Some(self.ctx.terms.mk_le(nat, bound)));
        }

        let bound_bv = self.ctx.terms.mk_bitvec(bound.clone(), width);
        let counterexample = self.ctx.terms.mk_bvugt(translated_bv, bound_bv);
        probe_assertions.push(counterexample);

        if self.run_bv_lia_bitblast_probe(probe_assertions)? {
            let nat = self.ctx.terms.mk_bv2nat(bv_term);
            let bound = self.ctx.terms.mk_int(bound.clone());
            Ok(Some(self.ctx.terms.mk_le(nat, bound)))
        } else {
            Ok(None)
        }
    }

    fn collect_bitblast_proven_bv_lia_bounds(&mut self, roots: &[TermId]) -> Result<Vec<TermId>> {
        let facts = collect_int_facts(&self.ctx.terms, roots);
        let mut obligations = Vec::new();
        for &root in roots {
            collect_bv_nat_upper_bound_obligations(&self.ctx.terms, &facts, root, &mut obligations);
        }
        obligations.sort_unstable_by(|(a_term, a_bound), (b_term, b_bound)| {
            (a_term.0, a_bound).cmp(&(b_term.0, b_bound))
        });
        obligations.dedup();

        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for (bv_term, bound) in obligations {
            if let Some(fact) =
                self.prove_bv_nat_upper_bound_by_bitblast(&facts, bv_term, &bound)?
            {
                if seen.insert(fact) {
                    out.push(fact);
                }
            }
        }
        Ok(out)
    }

    fn collect_enumeration_proven_bv_lia_equalities(
        &mut self,
        roots: &[TermId],
    ) -> Result<Vec<TermId>> {
        let facts = collect_int_facts(&self.ctx.terms, roots);
        let ite_defs = collect_int_ite_definitions(&self.ctx.terms, roots);
        let mut obligations = Vec::new();
        for &root in roots {
            collect_bv_nat_int_equality_obligations(
                &self.ctx.terms,
                &facts,
                root,
                &mut obligations,
            );
        }
        obligations.sort_unstable_by_key(|(bv_term, int_term)| (bv_term.0, int_term.0));
        obligations.dedup();

        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for (bv_term, int_term) in obligations {
            let (translated_bv, residue_bindings) = {
                let mut translator = BvLiaBitblastTranslator::new(&mut self.ctx.terms, &facts);
                let Some(translated_bv) = translator.translate_bv(bv_term) else {
                    continue;
                };
                (translated_bv, translator.residue_bindings())
            };

            if matches!(
                self.prove_bv_nat_int_equality_by_enumeration(
                    &facts,
                    &ite_defs,
                    translated_bv,
                    int_term,
                    &residue_bindings,
                ),
                Some(true)
            ) {
                let nat = self.ctx.terms.mk_bv2nat(bv_term);
                let fact = self.ctx.terms.mk_eq(nat, int_term);
                if seen.insert(fact) {
                    out.push(fact);
                }
            }
        }
        Ok(out)
    }

    /// BV<->LIA residue bridge routing: harvest the int<->bv residue congruences
    /// that the bitblast translator mints (and which otherwise live only inside
    /// the all-or-nothing enumeration/bitblast probes) and return them as
    /// Int-sorted LIA assertions so they can be added to the AUFLIA query that
    /// actually decides the mixed obligation in
    /// [`Self::solve_bv_lia_bridge_with_extra_roots`].
    ///
    /// The congruences are emitted directly on the *existing* formula terms so
    /// the AUFLIA solver — which treats `bv2nat(...)` as an uninterpreted Int —
    /// can relate them. For every `bv2nat(B)` reachable from `roots`:
    ///
    ///   * the universal range `0 <= bv2nat(B) <= 2^W - 1` is asserted, and
    ///   * when `B = int2bv(W, e)`, the residue congruence between
    ///     `bv2nat(int2bv(W, e))` and `e` is asserted (the tight form
    ///     `bv2nat(int2bv(W, e)) = e` when `facts` prove `0 <= e < 2^W`, else
    ///     the Euclidean form `e = bv2nat(int2bv(W, e)) + 2^W * k`).
    ///
    /// Each assertion is a theorem of the `bv2nat`/`int2bv` semantics, so adding
    /// them only shrinks the model set: SAT stays SAT, UNSAT stays sound.
    fn collect_bv_lia_residue_bridge_assertions(&mut self, roots: &[TermId]) -> Vec<TermId> {
        let facts = collect_int_facts(&self.ctx.terms, roots);

        // Collect (bv2nat-argument) BV terms reachable from the roots. These are
        // the BV expressions whose unsigned Int value the formula takes.
        let bv_args = collect_bv2nat_arg_subterms(&self.ctx.terms, roots);
        if bv_args.is_empty() {
            return Vec::new();
        }

        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for bv in bv_args {
            let Some(width) = bv_width(&self.ctx.terms, bv) else {
                continue;
            };
            if width == 0 {
                continue;
            }
            let nat = self.ctx.terms.mk_bv2nat(bv);

            // Universal unsigned range: 0 <= bv2nat(bv) <= 2^width - 1.
            let modulus = BigInt::one() << width;
            let max = &modulus - BigInt::one();
            let zero = self.ctx.terms.mk_int(BigInt::zero());
            let max_t = self.ctx.terms.mk_int(max);
            let ge0 = self.ctx.terms.mk_ge(nat, zero);
            let le_max = self.ctx.terms.mk_le(nat, max_t);
            if seen.insert(ge0) {
                out.push(ge0);
            }
            if seen.insert(le_max) {
                out.push(le_max);
            }

            // Residue congruence for the `bv2nat(int2bv(W, e))` shape, tying the
            // existing term back to its Int argument `e`.
            let Some(int_arg) = int2bv_arg(&self.ctx.terms, bv, width) else {
                continue;
            };
            let non_negative = facts
                .lower_bound(int_arg)
                .is_some_and(|lo| !lo.is_negative());
            let below_modulus = facts.upper_bound(int_arg).is_some_and(|hi| hi < &modulus);
            let congruence = if non_negative && below_modulus {
                // Tight form: bv2nat(int2bv(W, e)) = e on [0, 2^W).
                self.ctx.terms.mk_eq(nat, int_arg)
            } else {
                // Euclidean form: e = bv2nat(int2bv(W, e)) + 2^W * k.
                let k = self
                    .ctx
                    .terms
                    .mk_fresh_var(&format!("__ay_bv_lia_q{}_w{}", int_arg.0, width), Sort::Int);
                let modulus_t = self.ctx.terms.mk_int(modulus);
                let scaled = self.ctx.terms.mk_mul(vec![modulus_t, k]);
                let rhs = self.ctx.terms.mk_add(vec![nat, scaled]);
                self.ctx.terms.mk_eq(int_arg, rhs)
            };
            if seen.insert(congruence) {
                out.push(congruence);
            }
        }
        out
    }

    /// Sound int2bv/bv2nat **range-injectivity** bridge (forward direction).
    ///
    /// For every `bv2nat`-argument BV term `i` (width `w`) and every concrete
    /// witness `int2bv_w(n)` reachable from the same `roots`, emit the clause
    ///
    /// ```text
    ///   bv2nat(i) = n   ==>   i = int2bv_w(n)
    /// ```
    ///
    /// (interned as `(or (not (= (bv2nat i) n)) (= i (int2bv_w n)))`). This is
    /// the boundary-index PIN the deductive-checks heap-loop invariant needs: from the
    /// ground fact `bv2nat(i) = old_len` it derives `i = int2bv_w(old_len)`, so
    /// `select (store db (int2bv_w old_len) v) i` reads the just-pushed element.
    ///
    /// SOUNDNESS — this is the FORWARD half of range-injectivity and is a
    /// *theorem* of the SMT-LIB `int2bv`/`bv2nat` semantics with NO side
    /// condition:
    ///   * if `n` is in range (`0 <= n < 2^w`): `bv2nat(i) = n` and
    ///     `bv2nat(int2bv_w(n)) = n mod 2^w = n` give two width-`w` vectors with
    ///     equal `bv2nat`; `bv2nat` is injective on a fixed width, so
    ///     `i = int2bv_w(n)`.
    ///   * if `n` overflows (`n >= 2^w` or `n < 0`): the antecedent
    ///     `bv2nat(i) = n` is itself unsatisfiable (`bv2nat(i) in [0, 2^w)`), so
    ///     the implication holds vacuously.
    /// In both cases the clause is valid, so adding it removes no model: SAT stays
    /// SAT, UNSAT stays sound — it only lets the bridge derive MORE valid UNSATs.
    ///
    /// The BACKWARD direction `i = int2bv_w(n) ==> bv2nat(i) = n` is deliberately
    /// NOT emitted here: it is unsound for overflowing `n` (it would assert the
    /// bogus round-trip `bv2nat(int2bv_w(n)) = n` instead of the `mod 2^w` form).
    /// The exact `mod` form is already supplied by `push_bv2nat_congruence` /
    /// `collect_bv_lia_residue_bridge_assertions`.
    fn collect_int2bv_bv2nat_injectivity_assertions(&mut self, roots: &[TermId]) -> Vec<TermId> {
        let bv_args = collect_bv2nat_arg_subterms(&self.ctx.terms, roots);
        if bv_args.is_empty() {
            return Vec::new();
        }
        let int2bv_terms = collect_int2bv_terms(&self.ctx.terms, roots);
        if int2bv_terms.is_empty() {
            return Vec::new();
        }

        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for bv in bv_args {
            let Some(width) = bv_width(&self.ctx.terms, bv) else {
                continue;
            };
            if width == 0 {
                continue;
            }
            for &(int2bv_term, w, source) in &int2bv_terms {
                if w != width {
                    continue;
                }
                // A self-pin (`i` IS the witness) is a trivial tautology; skip it.
                if bv == int2bv_term {
                    continue;
                }
                // Antecedent: bv2nat(i) = source. Consequent: i = int2bv_w(source).
                let nat = self.ctx.terms.mk_bv2nat(bv);
                let nat_eq_source = self.ctx.terms.mk_eq(nat, source);
                let not_nat_eq = self.ctx.terms.mk_not(nat_eq_source);
                let i_eq_witness = self.ctx.terms.mk_eq(bv, int2bv_term);
                let clause = self.ctx.terms.mk_or(vec![not_nat_eq, i_eq_witness]);
                if seen.insert(clause) {
                    out.push(clause);
                }
            }
        }
        out
    }

    /// Sound bv2nat **inversion** clauses (#bv2nat-inv / F6 part i).
    ///
    /// `bv2nat` is a total BIJECTION of `(_ BitVec w)` onto `[0, 2^w)`, and
    /// `int2bv_w` is its two-sided inverse on that range: for EVERY width-`w`
    /// bitvector `x`, `x = int2bv_w(bv2nat(x))`. So whenever the LIA/EUF facts
    /// pin a `bv2nat(x)` argument to a concrete value `n` in `[0, 2^w)`, the BV
    /// IDENTITY of `x` is forced to the single bitvector `int2bv_w(n)`.
    ///
    /// This is the boundary conversion the forward injectivity clause
    /// ([`Self::collect_int2bv_bv2nat_injectivity_assertions`]) cannot supply on
    /// its own: that clause needs a syntactic `int2bv` WITNESS already present in
    /// the query (`collect_int2bv_terms`), whereas a goal like
    /// `2 = bv2nat(k) ∧ k ≠ 2` has none — the only way to refute it is to invert
    /// `bv2nat` directly (probe B1).
    ///
    /// For each `bv2nat(x)` argument `x` (non-constant, width `w > 0`) whose
    /// value is pinned to a concrete `n` by the LIA facts, and with
    /// `0 <= n < 2^w`, emit the CONDITIONAL congruence clause
    ///
    /// ```text
    ///   (= bv2nat(x) n)  ==>  (= x <bv const (n mod 2^w)>)
    /// ```
    ///
    /// SOUNDNESS: the clause is a TAUTOLOGY of mixed BV/Int semantics regardless
    /// of whether the pin is genuine — `int2bv_w(bv2nat(x)) = x` holds for all
    /// `x`, so the antecedent `bv2nat(x) = n` forces
    /// `x = int2bv_w(n) = <n mod 2^w>`. Adding an entailed lemma removes NO model
    /// (SAT stays SAT, UNSAT stays sound); it can only turn Unknown into a decided
    /// verdict, never flip a correct one. The antecedent literal reuses the exact
    /// `bv2nat(x)` term the query already carries, so the deciding AUFLIA/EUF
    /// layer discharges it by congruence the instant the pin is asserted. A value
    /// pinned OUTSIDE `[0, 2^w)` is skipped (the range axiom refutes it
    /// elsewhere); an unpinned argument is skipped (no guess).
    fn collect_bv2nat_inversion_assertions(&mut self, roots: &[TermId]) -> Vec<TermId> {
        let bv_args = collect_bv2nat_arg_subterms(&self.ctx.terms, roots);
        if bv_args.is_empty() {
            return Vec::new();
        }
        let facts = collect_int_facts(&self.ctx.terms, roots);
        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for bv in bv_args {
            if matches!(self.ctx.terms.get(bv), TermData::Const(_)) {
                continue;
            }
            let Some(width) = bv_width(&self.ctx.terms, bv) else {
                continue;
            };
            if width == 0 {
                continue;
            }
            let nat = self.ctx.terms.mk_bv2nat(bv);
            // Is `bv2nat(x)` pinned to a single concrete value by the LIA facts?
            // Either (a) its class contains an Int constant, or (b) its lower and
            // upper LIA bounds coincide.
            let pinned: Option<BigInt> = facts
                .class_terms(nat)
                .into_iter()
                .find_map(|t| int_const_value(&self.ctx.terms, t))
                .or_else(|| match (facts.lower_bound(nat), facts.upper_bound(nat)) {
                    (Some(lo), Some(hi)) if lo == hi => Some(lo.clone()),
                    _ => None,
                });
            let Some(n) = pinned else {
                continue;
            };
            // bv2nat is a bijection onto [0, 2^w); an out-of-range pin is already
            // refuted by the range axiom, so only invert an in-range value.
            let modulus = BigInt::one() << width as usize;
            if n < BigInt::zero() || n >= modulus {
                continue;
            }
            let n_term = self.ctx.terms.mk_int(n);
            // int2bv_w(n) folds to the concrete bitvector constant (mk_int2bv
            // wraps mod 2^w; n is already in range).
            let bv_const = self.ctx.terms.mk_int2bv(width, n_term);
            if bv_const == bv || !matches!(self.ctx.terms.get(bv_const), TermData::Const(_)) {
                continue;
            }
            // (= bv2nat(x) n) ==> (= x <bvconst>)  — a tautology; see doc.
            let nat_eq_n = self.ctx.terms.mk_eq(nat, n_term);
            let not_nat_eq = self.ctx.terms.mk_not(nat_eq_n);
            let x_eq_const = self.ctx.terms.mk_eq(bv, bv_const);
            let clause = self.ctx.terms.mk_or(vec![not_nat_eq, x_eq_const]);
            if seen.insert(clause) {
                out.push(clause);
            }
        }
        out
    }

    /// Sound int2bv **constant-source fold** (#int2bv-pin).
    ///
    /// For every `int2bv_w(source)` term reachable from `roots` whose Int
    /// `source` is pinned to a single concrete value `c` by the LIA facts
    /// (`lower_bound(source) == upper_bound(source) == c`), emit
    ///
    /// ```text
    ///   int2bv_w(source) = <bv const (c mod 2^w)>
    /// ```
    ///
    /// This is the boundary conversion the residue/injectivity facts do NOT
    /// reach: those relate a `bv2nat(int2bv(...))` residue or pin a `bv2nat`
    /// argument onto an int2bv WITNESS, but leave a bare `int2bv_w(len)` opaque
    /// even when `len` is fixed. DEDUCTIVE_CHECKS's frame / collection encoder bridges a
    /// fixed sequence length through exactly this shape, and — chained with the
    /// existing injectivity clause `bv2nat(i)=len ==> i=int2bv_w(len)` — this fold
    /// pins the boundary index `i` to a concrete bitvector so a `bvult idx i`
    /// frame guard becomes decidable.
    ///
    /// SOUNDNESS: `int2bv_w(source) = (source mod 2^w)` is definitional, and
    /// `source` is genuinely pinned to `c` by asserted LIA facts, so the equality
    /// is a theorem with no side condition — additive, it removes no model (SAT
    /// stays SAT, UNSAT stays sound), and only lets the bridge read the concrete
    /// BV value it already entails. A source that is not pinned to a single
    /// constant is skipped (no guess).
    fn collect_int2bv_pinned_source_assertions(&mut self, roots: &[TermId]) -> Vec<TermId> {
        let int2bv_terms = collect_int2bv_terms(&self.ctx.terms, roots);
        if int2bv_terms.is_empty() {
            return Vec::new();
        }
        let facts = collect_int_facts(&self.ctx.terms, roots);
        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for &(int2bv_term, width, source) in &int2bv_terms {
            if width == 0 {
                continue;
            }
            // `source` is pinned to a concrete `c` when either (a) its
            // equality class contains an Int constant (`(= len 3)` unions `len`
            // with the literal), or (b) its lower and upper LIA bounds coincide
            // (`len <= 3 ∧ len >= 3`).
            let pinned: Option<BigInt> = facts
                .class_terms(source)
                .into_iter()
                .find_map(|t| int_const_value(&self.ctx.terms, t))
                .or_else(
                    || match (facts.lower_bound(source), facts.upper_bound(source)) {
                        (Some(lo), Some(hi)) if lo == hi => Some(lo.clone()),
                        _ => None,
                    },
                );
            let Some(c) = pinned else {
                continue;
            };
            // Fold int2bv_w(c) to its bitvector constant (mk_int2bv wraps mod 2^w).
            let c_term = self.ctx.terms.mk_int(c);
            let bv_const = self.ctx.terms.mk_int2bv(width, c_term);
            // Only emit a genuine pin to a CONSTANT (never int2bv(t)=int2bv(t)).
            if bv_const == int2bv_term
                || !matches!(self.ctx.terms.get(bv_const), TermData::Const(_))
            {
                continue;
            }
            let eq = self.ctx.terms.mk_eq(int2bv_term, bv_const);
            if seen.insert(eq) {
                out.push(eq);
            }
        }
        out
    }

    /// Unconditional definitional axioms for EVERY `int2bv(w, s)` term reachable
    /// in `roots` (#snd-bv-2).
    ///
    /// The other bridge passes only relate a `bv2nat`/`int2bv` value to Int when
    /// a `bv2nat(...)` COMPANION already exists in the query (`push_bv2nat_range`
    /// is reached only from a `bv2nat` root, and `collect_bv_lia_bridge_assertions`
    /// visits `bv2nat` nodes). So a bare `int2bv(w, s)` fed straight into a BitVec
    /// `=`/`distinct` (e.g. `(= ((_ int2bv 4) x) (_ bv3 4))`) never links its Int
    /// source `s` to the arithmetic side and the mixed goal stalls at Unknown.
    ///
    /// For each such term we MATERIALIZE its `bv2nat` companion
    /// `n := bv2nat(int2bv_w(s))` and emit, via [`push_bv2nat_range`],
    ///
    /// ```text
    ///   0 <= n <= 2^w - 1         (bv2nat range)
    ///   n = s - 2^w * k           (k FRESH, unconstrained; the exact mod-2^w
    ///                              residue congruence)
    /// ```
    ///
    /// which is the SMT-LIB definition of `int2bv`/`bv2nat`. A downstream
    /// `bv2nat` constant-pin clause (see [`Self::collect_bv2nat_const_pin_assertions`],
    /// which now also treats `int2bv` terms as pin candidates) supplies the last
    /// link `int2bv_w(s) = c ⇒ n = bv2nat(c)` when the term is equated to a BV
    /// constant, closing the loop `s ≡ value(c) (mod 2^w)`.
    ///
    /// SOUNDNESS: `n` is a fresh Int-sorted quantity (introduced here) and the
    /// congruence is an EQUALITY with a fresh unconstrained slack `k`, so it is
    /// EXACT — it removes NO model of `s` (every true residue remains realizable)
    /// and only ADDS a defined value plus its range. It can therefore enable
    /// additional valid UNSATs but never a false one, and it never constrains any
    /// pre-existing variable except through the exact definition. Additive.
    fn collect_int2bv_definitional_assertions(&mut self, roots: &[TermId]) -> Vec<TermId> {
        let int2bv_terms = collect_int2bv_terms(&self.ctx.terms, roots);
        if int2bv_terms.is_empty() {
            return Vec::new();
        }
        let mut out = Vec::new();
        for &(int2bv_term, width, _source) in &int2bv_terms {
            if width == 0 {
                continue;
            }
            let nat = self.ctx.terms.mk_bv2nat(int2bv_term);
            push_bv2nat_range(&mut self.ctx.terms, &mut out, int2bv_term, nat);
        }
        let mut seen = HashSet::default();
        out.retain(|t| seen.insert(*t));
        out
    }

    /// Sound bv2nat **constant-pin** clauses (#bv2nat-const-pin).
    ///
    /// For each BV term `t` that is (or will be, via the signed/unsigned bridge)
    /// taken as a `bv2nat` argument — i.e. every `bv2nat` argument AND every
    /// operand of a `bvult`/`bvule`/`bvslt`/`bvsle` atom — and each bitvector
    /// CONSTANT `c` of the same width reachable in `roots`, emit the CONDITIONAL
    /// congruence clause
    ///
    /// ```text
    ///   (= t c)  ==>  (= bv2nat(t) <bv2nat(c)>)
    /// ```
    ///
    /// (`bv2nat(c)` folds to the concrete unsigned Int). The clause fires
    /// whenever `t = c` is established — including when it is DERIVED at solve
    /// time (a disjunction-guard collapse `(or (= x c) (not guard))`, or an array
    /// `select`-over-`store` chain `s_new[i] = s[i] = c`) — which a purely
    /// syntactic fold cannot see. Combined with the msb↔bv2nat link in
    /// [`bv_signed_value`], this pins the sign of a frame element read from a
    /// constant array cell so `bvslt s_new[i] 0` discharges.
    ///
    /// SOUNDNESS: `t = c ⇒ bv2nat(t) = bv2nat(c)` is an immediate congruence and
    /// `bv2nat(c)` is the definitional value — a valid implication, additive,
    /// removes no model (SAT stays SAT, UNSAT stays sound). Bounded to keep the
    /// clause count linear: skipped entirely past `MAX_BV2NAT_CONST_PIN_CLAUSES`.
    fn collect_bv2nat_const_pin_assertions(&mut self, roots: &[TermId]) -> Vec<TermId> {
        const MAX_BV2NAT_CONST_PIN_CLAUSES: usize = 256;
        let candidates = collect_bv2nat_pin_candidate_terms(&self.ctx.terms, roots);
        let consts = collect_bv_constant_leaves(&self.ctx.terms, roots);
        if candidates.is_empty() || consts.is_empty() {
            return Vec::new();
        }
        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for &t in &candidates {
            if matches!(self.ctx.terms.get(t), TermData::Const(_)) {
                continue;
            }
            let Some(tw) = bv_width(&self.ctx.terms, t) else {
                continue;
            };
            for &c in &consts {
                if bv_width(&self.ctx.terms, c) != Some(tw) {
                    continue;
                }
                let nat_c = self.ctx.terms.mk_bv2nat(c);
                if !matches!(self.ctx.terms.get(nat_c), TermData::Const(_)) {
                    continue;
                }
                let eq_tc = self.ctx.terms.mk_eq(t, c);
                let nat_t = self.ctx.terms.mk_bv2nat(t);
                let nat_eq = self.ctx.terms.mk_eq(nat_t, nat_c);
                let not_eq_tc = self.ctx.terms.mk_not(eq_tc);
                let clause = self.ctx.terms.mk_or(vec![not_eq_tc, nat_eq]);
                if seen.insert(clause) {
                    out.push(clause);
                    if out.len() >= MAX_BV2NAT_CONST_PIN_CLAUSES {
                        return out;
                    }
                }
            }
        }
        out
    }

    /// Sound modular bridge for `bv2nat(bvadd(a,b))` / `bv2nat(bvsub(a,b))`
    /// (#overflow-mod).
    ///
    /// The conservative bridge relates `bv2nat`, `int2bv`, and unsigned/signed
    /// compares to Int but leaves a `bvadd`/`bvsub` result opaque, so a no-wrap
    /// spec like `a < 100 && b < 100 ==> add(a,b) == a + b` cannot be proved:
    /// nothing relates `bv2nat(bvadd(a,b))` to `bv2nat(a) + bv2nat(b)`. This emits
    /// the definitional modular identity as a two-branch DISJUNCTION over the
    /// carry/borrow (there is at most one wrap), together with the result range:
    ///
    /// ```text
    ///   bvadd:  bv2nat(t) = bv2nat(a)+bv2nat(b)  OR  bv2nat(t) = bv2nat(a)+bv2nat(b) - 2^W
    ///   bvsub:  bv2nat(t) = bv2nat(a)-bv2nat(b)  OR  bv2nat(t) = bv2nat(a)-bv2nat(b) + 2^W
    ///   plus    0 <= bv2nat(t) <= 2^W - 1   (selects the in-range branch)
    /// ```
    ///
    /// SOUNDNESS: the sum of two width-`W` unsigned values lies in
    /// `[0, 2^(W+1)-2]`, so `bv2nat(bvadd(a,b)) = (bv2nat(a)+bv2nat(b)) mod 2^W`
    /// takes exactly one of the two listed values; the difference lies in
    /// `[-(2^W-1), 2^W-1]`, so `bvsub` likewise. Both are theorems of the
    /// mod-`2^W` semantics — additive, remove no model. A DISJUNCTION (not a
    /// `2^W * carry` product) is used deliberately: ay's LIA path decides the
    /// disjunctive form but returns `unknown` on the `const*var` product form once
    /// ≥2 `bv2nat` terms co-occur (verified: `h2` vs `h3` repros). Only binary
    /// `bvadd`/`bvsub` are handled; other arities are skipped.
    fn collect_bv2nat_add_sub_modular_assertions(&mut self, roots: &[TermId]) -> Vec<TermId> {
        let ops = collect_bv_add_sub_terms(&self.ctx.terms, roots);
        if ops.is_empty() {
            return Vec::new();
        }
        let mut out = Vec::new();
        let mut seen = HashSet::default();
        for (term, is_sub, a, b, width) in ops {
            if width == 0 {
                continue;
            }
            let modulus = BigInt::one() << width as usize;
            let nat_t = self.ctx.terms.mk_bv2nat(term);
            let nat_a = self.ctx.terms.mk_bv2nat(a);
            let nat_b = self.ctx.terms.mk_bv2nat(b);
            let modulus_t = self.ctx.terms.mk_int(modulus.clone());
            // no-wrap value and wrapped value (differ by exactly 2^W)
            let (base, wrapped) = if is_sub {
                let diff = self.ctx.terms.mk_sub(vec![nat_a, nat_b]);
                let wrapped = self.ctx.terms.mk_add(vec![diff, modulus_t]);
                (diff, wrapped)
            } else {
                let sum = self.ctx.terms.mk_add(vec![nat_a, nat_b]);
                let wrapped = self.ctx.terms.mk_sub(vec![sum, modulus_t]);
                (sum, wrapped)
            };
            let eq_base = self.ctx.terms.mk_eq(nat_t, base);
            let eq_wrapped = self.ctx.terms.mk_eq(nat_t, wrapped);
            let disj = self.ctx.terms.mk_or(vec![eq_base, eq_wrapped]);
            // The result range `0 <= bv2nat(t) < 2^W` selects the in-range branch;
            // definitional, so always sound to add (the residue collector only
            // emits it for int2bv-shaped args).
            let max_t = self.ctx.terms.mk_int(&modulus - BigInt::one());
            let zero = self.ctx.terms.mk_int(BigInt::zero());
            let t_ge0 = self.ctx.terms.mk_ge(nat_t, zero);
            let t_le_max = self.ctx.terms.mk_le(nat_t, max_t);
            for assertion in [disj, t_ge0, t_le_max] {
                if seen.insert(assertion) {
                    out.push(assertion);
                }
            }
        }
        out
    }

    fn last_unknown_is_unsupported_arithmetic(&self) -> bool {
        matches!(
            self.last_unknown_reason,
            Some(UnknownReason::UnsupportedArithmetic)
        )
    }

    /// Conservative BV-to-Int bridge for `_BV_LIA` formulas (#9065).
    ///
    /// The bridge derives LIA consequences of unsigned `bv2nat` and asserted
    /// `bvult`/`bvule` atoms with a BV-constant side, then asks AUFLIA to prove
    /// contradiction. It only returns UNSAT; SAT/Unknown from the arithmetic
    /// side remains Unknown because the bridge is intentionally incomplete.
    pub(in crate::executor) fn solve_bv_lia_bridge(&mut self) -> Result<SolveResult> {
        self.solve_bv_lia_bridge_with_extra_roots(&[])
    }

    /// Assumption-based version of [`Self::solve_bv_lia_bridge`].
    pub(in crate::executor) fn solve_bv_lia_bridge_with_assumptions(
        &mut self,
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        self.solve_bv_lia_bridge_with_extra_roots(assumptions)
    }

    fn solve_bv_lia_bridge_with_extra_roots(
        &mut self,
        extra_roots: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        let mut roots = self.ctx.assertions.clone();
        roots.extend_from_slice(extra_roots);
        let mut bridge_assertions = collect_bv_lia_bridge_assertions(&mut self.ctx.terms, &roots);
        let bitblast_proven_bounds = self.collect_bitblast_proven_bv_lia_bounds(&roots)?;
        let enumeration_proven_equalities =
            self.collect_enumeration_proven_bv_lia_equalities(&roots)?;
        if !bitblast_proven_bounds.is_empty() {
            if !extra_roots.is_empty() {
                self.last_assumption_core = Some(extra_roots.to_vec());
            }
            return Ok(SolveResult::unsat());
        }
        if !enumeration_proven_equalities.is_empty() {
            if !extra_roots.is_empty() {
                self.last_assumption_core = Some(extra_roots.to_vec());
            }
            return Ok(SolveResult::unsat());
        }
        bridge_assertions.extend(bitblast_proven_bounds);
        bridge_assertions.extend(enumeration_proven_equalities);
        // BV<->LIA residue bridge routing fix: the bitblast/enumeration probes
        // above are all-or-nothing and never expose the int<->bv residue
        // congruence to the deciding AUFLIA solver. Harvest those congruences
        // here so popcount/bits/rightmostbit obligations that blow the
        // enumeration domain (count32/count64) can still be refuted by AUFLIA.
        // These are Int-sorted LIA facts entailed by `residue = int2bv(W, int)`
        // and are routed into the same `bridge_assertions` set that feeds
        // `solve_auf_lia` below.
        let residue_bridge_assertions = self.collect_bv_lia_residue_bridge_assertions(&roots);
        bridge_assertions.extend(residue_bridge_assertions);
        // int2bv/bv2nat range-injectivity (forward): pin a `bv2nat` argument onto
        // its `int2bv_w(n)` witness from the ground fact `bv2nat(i) = n`. This is
        // the Int<->BV boundary conversion the residue/congruence facts above do
        // not reach (they relate the Int VALUE, not the BV IDENTITY). Sound,
        // additive, forward-only — see the method doc.
        let injectivity_assertions = self.collect_int2bv_bv2nat_injectivity_assertions(&roots);
        bridge_assertions.extend(injectivity_assertions);
        // bv2nat inversion (#bv2nat-inv / F6 part i): when a `bv2nat(x)` argument
        // is LIA-pinned to a concrete in-range value `n`, force `x` to the single
        // bitvector `int2bv_w(n)`. This is the boundary conversion the forward
        // injectivity clause above CANNOT reach without a syntactic `int2bv`
        // witness (probe B1: `2 = bv2nat(k) ∧ k ≠ 2`). Sound, additive,
        // tautological — see the method doc.
        let inversion_assertions = self.collect_bv2nat_inversion_assertions(&roots);
        bridge_assertions.extend(inversion_assertions);
        // int2bv constant-source fold (#int2bv-pin): pin a bare `int2bv_w(len)`
        // to its concrete bitvector when `len` is LIA-fixed. Chained with the
        // injectivity clause above this pins a bv2nat-bridged boundary index, so
        // a `bvult idx (int2bv len)` frame guard becomes decidable. Sound,
        // additive, definitional — see the method doc.
        let pinned_source_assertions = self.collect_int2bv_pinned_source_assertions(&roots);
        bridge_assertions.extend(pinned_source_assertions);
        // bv2nat constant-pin (#bv2nat-const-pin): pin `bv2nat(t)` to its concrete
        // value when `t` is asserted equal to a bitvector constant, so (by
        // congruence + the msb<->bv2nat link) a signed/unsigned compare on a
        // frame element read from a constant array cell is decided. Sound,
        // additive, definitional — see the method doc.
        let bv2nat_const_pin_assertions = self.collect_bv2nat_const_pin_assertions(&roots);
        bridge_assertions.extend(bv2nat_const_pin_assertions);
        // bvadd/bvsub modular bridge (#overflow-mod): relate bv2nat of a wrapping
        // add/sub to bv2nat of its operands via a two-branch carry/borrow
        // disjunction + result range, so no-wrap add/sub obligations become
        // decidable. Sound, additive, definitional — see the method doc.
        let add_sub_modular_assertions = self.collect_bv2nat_add_sub_modular_assertions(&roots);
        bridge_assertions.extend(add_sub_modular_assertions);
        // int2bv definitional axioms (#snd-bv-2): for EVERY `int2bv(w, s)` term
        // — including one fed straight into a BitVec `=`/`distinct` with no
        // `bv2nat` companion — materialize `bv2nat(int2bv_w(s))` and pin it to
        // `s mod 2^w` (range + exact residue congruence). Without this a bare
        // `int2bv` never links its Int source to the arithmetic side. Sound,
        // additive, definitional — see the method doc.
        let int2bv_definitional_assertions = self.collect_int2bv_definitional_assertions(&roots);
        bridge_assertions.extend(int2bv_definitional_assertions);
        if bridge_assertions.is_empty() {
            if self.bv_lia_bridge_relaxation_is_unsat(&roots)? {
                if !extra_roots.is_empty() {
                    self.last_assumption_core = Some(extra_roots.to_vec());
                }
                return Ok(SolveResult::unsat());
            }
            self.last_unknown_reason = Some(UnknownReason::Incomplete);
            return Ok(SolveResult::Unknown);
        }
        let mut seen = HashSet::default();
        bridge_assertions.retain(|term| seen.insert(*term));

        let support_assertions =
            collect_bv_lia_support_assertions(&self.ctx.terms, &roots, &bridge_assertions);
        if !support_assertions.is_empty() {
            let saved_assertions = std::mem::replace(&mut self.ctx.assertions, support_assertions);
            let support_result = self.solve_auf_lia();
            self.ctx.assertions = saved_assertions;
            if self.ite_uf_definition_recovery.ready() {
                return Ok(SolveResult::Unknown);
            }
            if matches!(support_result, Ok(ref result) if result.is_unsat()) {
                if !extra_roots.is_empty() {
                    self.last_assumption_core = Some(extra_roots.to_vec());
                }
                return Ok(SolveResult::unsat());
            }
        }

        let base_assertions_exact = self.ctx.assertions.clone();
        self.ctx.assertions.extend(bridge_assertions);
        let arithmetic_result = if extra_roots.is_empty() {
            self.solve_auf_lia()
        } else {
            let scoped_assertions = self.ctx.assertions.clone();
            self.solve_auf_lia_with_assumptions(&scoped_assertions, extra_roots)
        };
        self.ctx.assertions = base_assertions_exact;

        if self.ite_uf_definition_recovery.ready() {
            return Ok(SolveResult::Unknown);
        }

        match arithmetic_result? {
            SolveResult::Unsat(_) => Ok(SolveResult::unsat()),
            SolveResult::Sat => {
                // Sound UNSAT promotion via the pure-BV relaxation takes
                // PRIORITY over any SAT promotion: if the relaxation (which only
                // drops Int constraints) is UNSAT, the whole query is UNSAT
                // regardless of the AUFLIA SAT verdict. Never promote SAT over a
                // genuine UNSAT.
                if self.bv_lia_bridge_relaxation_is_unsat(&roots)? {
                    if !extra_roots.is_empty() {
                        self.last_assumption_core = Some(extra_roots.to_vec());
                    }
                    return Ok(SolveResult::unsat());
                }
                // STRUCTURAL REALIZABILITY GUARD (#9065 / B2). Promote the
                // AUFLIA SAT to a real SAT ONLY when BOTH hold:
                //   (b) every BitVec variable occurs solely as a bv2nat/int2bv
                //       bridge argument (no bvadd/bvult/concat/extract/BV `=`/…),
                //       so the range-checked opaque `bv2nat` value is realizable
                //       by `x = int2bv_w(v)` with no competing BV constraint; AND
                //   (a) the candidate AUFLIA model validates against the original
                //       roots (definite now that bv2nat(k) evaluates from the
                //       opaque LIA value — see eval_bv_structural.rs / Part 1).
                // If EITHER fails we keep the existing Unknown(Incomplete): a
                // too-loose guard would be a false SAT (a cardinal violation), so
                // when in doubt we do NOT promote. The guard scans ALL BitVec
                // occurrences across ALL roots (DAG walk, visited-bounded).
                if all_bitvec_vars_are_bridge_only(&self.ctx.terms, &roots) {
                    // WITNESS MATERIALIZATION FIRST (#9065 follow-up). Validating
                    // against the OPAQUE `bv2nat(k)` LIA value is enough to know
                    // the query is satisfiable, but it leaves `k` itself unpinned
                    // in the published model. Downstream the independent model
                    // gate re-evaluates `(= L (bv2nat k))` from the emitted
                    // assignment, where `k` has been completed to a default (0)
                    // that contradicts the pinned `L` — so a correct `sat` was
                    // being thrown away as `unknown`. Materialize every BV leaf
                    // from its companion (`k = int2bv_W(bv2nat(k))`) so the model
                    // we publish carries the realizing witness, exactly the
                    // `int2bv_w(v)` the bridge-only guard argues exists. Only a
                    // model that passes `validate_model` promotes, so this can
                    // only turn a MISSED sat into a checked sat.
                    if self.bridge_sat_materialize_and_validate(&roots) {
                        return Ok(SolveResult::Sat);
                    }
                    if self.bridge_sat_model_validates(&roots) {
                        return Ok(SolveResult::Sat);
                    }
                } else if collect_bv_leaf_vars(&self.ctx.terms, &roots).is_empty() {
                    // (Piece 3) NO FREE BitVec variable occurs anywhere in the
                    // query — a declared BV constant is a `TermData::Var`, so an
                    // empty `collect_bv_leaf_vars` means every BitVec-sorted term
                    // is a DETERMINED function of the (validated) non-BV model: a
                    // BV literal, or an `int2bv`/BV-op whose ultimate inputs are
                    // Int/literal. The candidate AUFLIA model therefore pins every
                    // BitVec value CONCRETELY (there is no free bit to realize), so
                    // `validate_model` — which recomputes each BV op from that
                    // model and checks every ORIGINAL root — is a DEFINITIVE
                    // arbiter: it returns Verified for every concretely-evaluable
                    // atom and Violated the instant one is false. Promote only on a
                    // passing validation. This is exactly the mixed `=` shape the
                    // bridge-only guard rejects (a BitVec `=` is a non-bridge op)
                    // yet which has no realizability gap, e.g.
                    // `(= ((_ int2bv 8) k) (_ bv200 8))` with `0 <= k < 256`.
                    //
                    // SOUNDNESS (never a false SAT): the only way to promote is a
                    // passing `validate_model` over the ORIGINAL roots. With no
                    // free BV var every BV atom is concretely (re)evaluated from
                    // the model, so a wrong assignment yields a Violated atom and
                    // is REJECTED (kept Unknown); the non-BV fragment is arbitrated
                    // by the same `validate_model` already trusted by the
                    // bridge-only branch above. The pure-BV UNSAT relaxation was
                    // already checked (line above), so SAT is never promoted over a
                    // genuine UNSAT.
                    if self.bridge_sat_model_validates(&roots) {
                        return Ok(SolveResult::Sat);
                    }
                } else if self.bridge_sat_materialize_and_validate(&roots) {
                    // (Piece 2) A BitVec var occurs inside a bvadd/bvsub/… so the
                    // bridge-only guard fails, but materializing each leaf from
                    // its bv2nat companion yields a concrete model that VALIDATES
                    // against the original roots — a genuine, checked SAT witness
                    // (e.g. the wrapping-overflow counterexample at a = 2^W - k).
                    return Ok(SolveResult::Sat);
                }
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
            SolveResult::Unknown => {
                if self.bv_lia_bridge_relaxation_is_unsat(&roots)? {
                    if !extra_roots.is_empty() {
                        self.last_assumption_core = Some(extra_roots.to_vec());
                    }
                    return Ok(SolveResult::unsat());
                }
                self.last_unknown_reason = Some(UnknownReason::Incomplete);
                Ok(SolveResult::Unknown)
            }
        }
    }

    /// Validate the candidate AUFLIA model (in `self.last_model`) against the
    /// ORIGINAL bridge `roots`, gating the BV<->LIA bridge SAT promotion: only a
    /// model that genuinely satisfies the original `bv2nat` query may promote to
    /// SAT.
    ///
    /// This is the (a) half of the structural realizability guard. It is
    /// read-only with respect to caller-visible solver state: `last_result` and
    /// the assertion view are saved and restored around `validate_model`, which
    /// itself takes `&self`. Returns `false` (conservative — keep Unknown) when
    /// no model is present. With the bv2nat eval fix in place, a genuine-SAT
    /// `(= L (bv2nat k))` companion validates definitely, while a decoupled /
    /// out-of-range model evaluates to a definite false and is rejected.
    ///
    /// SOUNDNESS: this only ever GATES a SAT promotion (it can turn an intended
    /// SAT into Unknown, never the reverse), and it never touches the UNSAT
    /// derivation. Combined with the structural guard (b), only a bridge-only,
    /// model-validating query promotes — and the promoted model is realizable.
    fn bridge_sat_model_validates(&mut self, roots: &[TermId]) -> bool {
        if self.last_model.is_none() {
            return false;
        }
        let saved_result = self.last_result.clone();
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, roots.to_vec());
        self.last_result = Some(SolveResult::Sat);
        let validated = self.validate_model().is_ok();
        self.ctx.assertions = saved_assertions;
        self.last_result = saved_result;
        validated
    }

    /// SAT-model promotion when NOT every BitVec var is bridge-only
    /// (#overflow-mod / Piece 2) — the wrapping-refutation counterpart of the
    /// bridge-only [`Self::bridge_sat_model_validates`].
    ///
    /// When a BitVec var occurs inside a `bvadd`/`bvsub`/… (so the bridge-only
    /// guard fails) but every BitVec LEAF var has a `bv2nat(var)` companion
    /// valued in the AUFLIA model, MATERIALIZE each `var = int2bv_W(bv2nat(var))`
    /// into the model completion slot and re-run `validate_model`. The modular
    /// bridge (`collect_bv2nat_add_sub_modular_assertions`) forces the AUFLIA
    /// model into the correct carry/borrow branch, so the materialized concrete
    /// assignment is exactly the wrap-region witness.
    ///
    /// SOUNDNESS (cardinal rule — never a false SAT): `validate_model` is the
    /// sole arbiter, and with concrete leaf bits it recomputes every BV op and
    /// its `bv2nat` from real bits (eval_bv_structural evaluates `bv2nat`'s
    /// argument as a BitVec FIRST, using the opaque lia value only when there is
    /// no bv value). So a decoupled / wrong-wrap AUFLIA model evaluates the query
    /// to a definite false and is REJECTED. A materialized value is the UNIQUE
    /// bitvector with that `bv2nat` (range `[0, 2^W)`), so it can never realize an
    /// impossible model. If ANY leaf lacks a companion the promotion is declined
    /// (kept `Unknown`) — worst case a MISSED sat, never a FALSE sat. The
    /// completion slot is restored on a failed validation so no state leaks.
    fn bridge_sat_materialize_and_validate(&mut self, roots: &[TermId]) -> bool {
        let bv_vars = collect_bv_leaf_vars(&self.ctx.terms, roots);
        if bv_vars.is_empty() {
            return false;
        }
        // `bv2nat(var)` companion TermIds (idempotent hash-cons; already present
        // whenever the leaf has an `as nat` reading in the query).
        let companions: Vec<(TermId, TermId, u32)> = bv_vars
            .iter()
            .map(|&(v, w)| (v, self.ctx.terms.mk_bv2nat(v), w))
            .collect();
        // Read each companion's value from the AUFLIA (LIA) model; bail if any
        // leaf var has no `bv2nat` companion value to materialize from.
        let materialized: Vec<(TermId, BigInt, u32)> = {
            let Some(model) = self.last_model.as_ref() else {
                return false;
            };
            let Some(lia) = model.lia_model.as_ref() else {
                return false;
            };
            let mut out = Vec::with_capacity(companions.len());
            for &(v, nat, w) in &companions {
                // Prefer the AUFLIA model's `bv2nat(leaf)` value; fall back to a
                // direct constant pin `(= v c)` in the roots when the solver
                // eliminated `v` via its pin and keyed `bv2nat(v)`'s value under a
                // substituted term (#snd-bv-1). Sound: `validate_model` arbitrates.
                let val = lia
                    .values
                    .get(&nat)
                    .cloned()
                    .or_else(|| bv_leaf_pinned_nat(&self.ctx.terms, roots, v));
                let Some(val) = val else {
                    return false;
                };
                let modulus = BigInt::one() << w as usize;
                // non-negative representative in [0, 2^W)
                let m = ((&val % &modulus) + &modulus) % &modulus;
                out.push((v, m, w));
            }
            out
        };
        let saved_completed = self
            .last_model
            .as_ref()
            .map(|m| m.completed_values.clone())
            .unwrap_or_default();
        if let Some(model) = self.last_model.as_mut() {
            for (v, m, w) in &materialized {
                model.completed_values.insert(
                    *v,
                    EvalValue::BitVec {
                        value: m.clone(),
                        width: *w,
                    },
                );
            }
        }
        let validated = self.bridge_sat_model_validates(roots);
        if !validated {
            if let Some(model) = self.last_model.as_mut() {
                model.completed_values = saved_completed;
            }
        }
        validated
    }

    /// Sound completeness fallback for the BV<->LIA bridge (#9065 gap 2).
    ///
    /// When the conservative bridge cannot find an Int-side contradiction, a
    /// `bvsub`-containing query may still be refutable purely in the BV theory
    /// (e.g. `bvult(bvsub(k,1), k)` under `bvugt(k,4)`, whose validity does not
    /// depend on the `bv2nat` linkage that stalls the bridge). Without this
    /// fallback the bridge returns `Unknown(Incomplete)` on such goals.
    ///
    /// We run the eager BV decision procedure on the SAME root set. `solve_bv`
    /// encodes the `bv2nat`/Int linkage to *no clauses* — `bitblast_predicate`
    /// only fires for `=` when both operands are BitVec-sorted, and Int (`=`,
    /// `<`, `<=`, …) and `bv2nat` predicates emit nothing — so it decides a
    /// pure-BV *relaxation* of the query with strictly FEWER constraints than
    /// the original. An UNSAT verdict on the relaxation therefore entails UNSAT
    /// of the original (adding back the dropped Int constraints can only
    /// preserve unsatisfiability), so promoting it is sound.
    ///
    /// SOUNDNESS (cardinal rule): we promote ONLY UNSAT. SAT/Unknown on the
    /// relaxation says nothing about the constrained original (a dropped Int
    /// constraint could be contradictory with the BV model), so those are never
    /// promoted — the bridge stays `Unknown`. `bvsub` (and every other BV op)
    /// keeps the exact mod-2^width wrapping semantics of the sound bit-blaster,
    /// so no wrong wrap can leak in. Net effect: decides strictly more valid
    /// UNSATs, never a false SAT or false UNSAT.
    fn bv_lia_bridge_relaxation_is_unsat(&mut self, roots: &[TermId]) -> Result<bool> {
        // Scope to exactly the documented gap: the bridge already relates
        // bv2nat / unsigned+signed compares to Int, so the relaxation only adds
        // decisions when an un-bridged wrapping op (bvsub) is present.
        if !roots_contain_bvsub(&self.ctx.terms, roots) {
            return Ok(false);
        }
        // `run_bv_lia_bitblast_probe` saves/restores all solver state and
        // returns `is_unsat()`. The `roots` slice already includes any
        // `extra_roots` (assumptions), so they are asserted as facts — correct
        // for an UNSAT probe.
        self.run_bv_lia_bitblast_probe(roots.to_vec())
    }

    /// Pre-configure the persistent SAT solver with Z3-style search tuning
    /// for the incremental split-loop pipeline (#4919 Phase 6).
    ///
    /// The old `solve_split_loop_pipeline!` applied these via `pre_solve` callbacks.
    /// The incremental macro creates the solver internally, so we pre-seed
    /// the IncrementalTheoryState with a configured solver that the macro
    /// will detect and reuse via `pipeline_incremental_setup!`.
    pub(in crate::executor) fn configure_sat_search_tuning(
        &mut self,
        geometric_initial: f64,
        geometric_factor: f64,
        random_var_freq: f64,
    ) {
        use ay_sat::Solver as SatSolver;
        let proof_enabled = self.produce_proofs_enabled();
        let random_seed = self.current_random_seed();
        let should_record_random_seed = self
            .incr_theory_state
            .as_ref()
            .is_none_or(|state| state.persistent_sat.is_none());
        if should_record_random_seed {
            self.record_applied_sat_random_seed_for_test(random_seed);
        }
        let state = self
            .incr_theory_state
            .get_or_insert_with(IncrementalTheoryState::new);
        if state.persistent_sat.is_none() {
            let mut sat = SatSolver::new(0);
            sat.set_random_seed(random_seed);
            sat.set_geometric_restarts(geometric_initial, geometric_factor);
            sat.set_random_var_freq(random_var_freq);
            if let Some(seed) = self.random_seed {
                sat.set_random_seed(seed);
            }
            if self.progress_enabled {
                sat.set_progress_enabled(true);
            }
            if let Some(path) = &self.progress_json_path {
                if let Ok(obs) = ay_sat::json_observer::JsonProgressObserver::new_append(path) {
                    sat.set_observer(Some(Box::new(obs)));
                }
            }
            if proof_enabled {
                sat.enable_clause_trace();
                sat.set_proof_bookkeeping_budget(Executor::search_proof_bookkeeping_budget_for(
                    &self.ctx,
                    self.proof_reconstruction_step_budget,
                ));
            }
            state.persistent_sat = Some(sat);
        }
    }

    /// Solve using combined EUF + LRA theory with disequality split support (#6129).
    ///
    /// Uses an isolated incremental split loop so disequality and model-equality
    /// continuations do not rebuild the SAT layer between iterations.
    pub(in crate::executor) fn solve_uf_lra(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        self.with_isolated_incremental_state(None, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "UFLRA",
                persistent_sat_field: persistent_sat,
                create_theory: {
                    let mut tc = TheoryCombiner::uf_lra(&this.ctx.terms);
                    tc.set_interrupt(this.solve_interrupt.clone());
                    tc.set_deadline(this.solve_deadline.get());
                    // Enable the D0 datatype clash/acyclicity final-check pass
                    // for datatype-bearing problems (no-op otherwise; stage-4
                    // review F1: every combiner-backed DT+X lane hosts the pass).
                    let dt_info: Vec<(String, Vec<String>)> = this
                        .ctx
                        .datatype_iter()
                        .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
                        .collect();
                    tc.register_datatypes(&dt_info);
                    tc
                },
                extract_models: |theory| {
                    theory.scope_euf_model_to_roots(&this.ctx.assertions);
                    let (euf, lra) = theory.extract_euf_lra_models();
                    theory.clear_euf_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        lra: Some(lra),
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LRA,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (vec![], Default::default(), Default::default())
                },
                // #5462 Packet 4: enable eager theory-SAT interleaving for UFLRA.
                // Combined check runs local-only during BCP; full Nelson-Oppen
                // fixpoint runs once after SAT via needs_final_check_after_sat().
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                }
            )
        })
    }

    /// Solve using combined EUF + NRA theory with disequality split support.
    ///
    /// Structurally identical to `solve_uf_lra`, substituting UfNraSolver for UfLraSolver.
    /// NraSolver wraps LraSolver internally with tangent plane and sign lemma refinement
    /// for nonlinear products. The Nelson-Oppen combination with EUF is identical.
    pub(in crate::executor) fn solve_uf_nra(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        self.with_isolated_incremental_state(None, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "UFNRA",
                persistent_sat_field: persistent_sat,
                create_theory: UfNraSolver::new(&this.ctx.terms),
                extract_models: |theory| {
                    let (euf, lra) = theory.extract_models();
                    TheoryModels {
                        euf: Some(euf),
                        lra: Some(lra),
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LRA,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (vec![], Default::default(), Default::default())
                },
                // #5462 Packet 4: enable eager theory-SAT interleaving for UFNRA.
                // Same two-stage pattern as UFLRA: local-only BCP checks, full
                // Nelson-Oppen fixpoint deferred to needs_final_check_after_sat().
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                }
            )
        })
    }

    /// #6812 sound relaxation: verify-before-accept for a post-CDCL-split UF+LIA
    /// UNSAT. Re-derives UNSAT of the ORIGINAL assertion `core` (invariant (a):
    /// the caller passes only original-clause terms) on a FRESH, isolated solve
    /// (invariant (b)): a brand-new `IncrementalTheoryState` (fresh persistent
    /// SAT + theory, NO carried-over learned/split clauses) running the full
    /// UF+LIA pipeline. Returns `true` (ACCEPT) iff that fresh solve reports
    /// `Unsat`. Non-optimistic: `Sat`/`Unknown`/error => `false` (escalate).
    ///
    /// The fresh solve sets `post_split_verify_depth`, so its own eager arm
    /// accepts a post-split UNSAT directly (tautological split clauses, §2) rather
    /// than recursing into another verify pass. That is sound because the fresh
    /// solve has no stale learned theory-conflict clauses — the only false-UNSAT
    /// vector the #6812 guard protected against. This structurally closes that
    /// vector: a clause valid only relative to an earlier iteration's theory
    /// state is absent from the fresh solve and cannot drive a spurious UNSAT.
    pub(in crate::executor) fn verify_post_split_unsat_via_fresh_solve(
        &mut self,
        core: &[TermId],
    ) -> bool {
        if core.is_empty() {
            return false;
        }
        // Depth guard: cap nesting (the fresh inner solve must not itself launch
        // another verify pass — it uses tautological accept — but guard anyway).
        if self.post_split_verify_depth >= 2 {
            return false;
        }
        let saved_model = self.last_model.take();
        let saved_model_validated = self.last_model_validated;
        let saved_unknown_reason = self.last_unknown_reason.take();
        let saved_result = self.last_result.take();
        let saved_skip_model_eval = self.skip_model_eval;
        let saved_proof_provenance = self.proof_problem_assertion_provenance.clone();
        let saved_statistics = std::mem::take(&mut self.last_statistics);

        // The verification solve is a verdict-only probe.  It must not consume
        // or overwrite proof state owned by the outer solve.  In particular,
        // an inner UNSAT calls `build_unsat_proof`, whose `take_proof()` drains
        // the active tracker.  Sharing that tracker used to discard already
        // certified array ROW lemmas; the outer proof then rebuilt the same
        // generated axioms as free `Assume` leaves.
        let proof_was_enabled = self.proof_tracker.is_enabled();
        let mut verifier_tracker = crate::proof_tracker::ProofTracker::new();
        if proof_was_enabled {
            verifier_tracker.enable();
        }
        let saved_proof_tracker = std::mem::replace(&mut self.proof_tracker, verifier_tracker);
        let saved_last_proof = self.last_proof.take();
        let saved_finite_enum_witness = self.last_finite_enum_pigeonhole.take();
        let saved_checked_finite_enum = self.last_checked_finite_enum_pigeonhole.take();
        let saved_proof_reconstruction_suppressed =
            std::mem::replace(&mut self.last_unsat_proof_reconstruction_suppressed, false);
        let saved_last_lrat_certificate = self.last_lrat_certificate.take();
        let saved_last_proof_term_overrides = self.last_proof_term_overrides.take();
        let saved_last_proof_quality = self.last_proof_quality.take();
        let saved_last_clause_trace = self.last_clause_trace.take();
        let saved_last_checked_sat_refutation = self.last_checked_sat_refutation.take();
        let saved_last_var_to_term = self.last_var_to_term.take();
        let saved_last_trail_provenance = self.last_trail_provenance.take();
        let saved_last_negations = self.last_negations.take();
        let saved_last_clausification_proofs = self.last_clausification_proofs.take();
        let saved_last_original_clause_theory_proofs =
            self.last_original_clause_theory_proofs.take();
        let saved_proof_check_result = self.proof_check_result.take();
        let saved_proof_check_ok = self.proof_check_ok;
        let saved_last_proof_rebuild_originals =
            std::mem::take(&mut self.last_proof_rebuild_originals);
        let saved_last_proof_raw_original_assertions =
            std::mem::take(&mut self.last_proof_raw_original_assertions);
        let saved_verify_depth = self.post_split_verify_depth;

        self.post_split_verify_depth = saved_verify_depth + 1;
        // Suppress model evaluation / counterexample work in the inner solve;
        // we only consume its SAT/UNSAT verdict.
        self.skip_model_eval = true;
        let core_assertions = core.to_vec();
        let result = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            self.with_isolated_incremental_state(Some(core_assertions), Self::solve_uf_lia)
        }));
        self.post_split_verify_depth = saved_verify_depth;

        // Restore caller-visible state regardless of the inner outcome: the verify
        // pass must be transparent to the outer solve's result/model/diagnostics.
        self.last_model = saved_model;
        self.last_model_validated = saved_model_validated;
        self.last_unknown_reason = saved_unknown_reason;
        self.last_result = saved_result;
        self.skip_model_eval = saved_skip_model_eval;
        self.proof_problem_assertion_provenance = saved_proof_provenance;
        self.last_statistics = saved_statistics;
        self.proof_tracker = saved_proof_tracker;
        self.last_proof = saved_last_proof;
        self.last_finite_enum_pigeonhole = saved_finite_enum_witness;
        self.last_checked_finite_enum_pigeonhole = saved_checked_finite_enum;
        self.last_unsat_proof_reconstruction_suppressed = saved_proof_reconstruction_suppressed;
        self.last_lrat_certificate = saved_last_lrat_certificate;
        self.last_proof_term_overrides = saved_last_proof_term_overrides;
        self.last_proof_quality = saved_last_proof_quality;
        self.last_clause_trace = saved_last_clause_trace;
        self.last_checked_sat_refutation = saved_last_checked_sat_refutation;
        self.last_var_to_term = saved_last_var_to_term;
        self.last_trail_provenance = saved_last_trail_provenance;
        self.last_negations = saved_last_negations;
        self.last_clausification_proofs = saved_last_clausification_proofs;
        self.last_original_clause_theory_proofs = saved_last_original_clause_theory_proofs;
        self.proof_check_result = saved_proof_check_result;
        self.proof_check_ok = saved_proof_check_ok;
        self.last_proof_rebuild_originals = saved_last_proof_rebuild_originals;
        self.last_proof_raw_original_assertions = saved_last_proof_raw_original_assertions;

        match result {
            Ok(result) => matches!(result, Ok(ref r) if r.is_unsat()),
            Err(payload) => std::panic::resume_unwind(payload),
        }
    }

    /// #relevancy-lazy-routing: whether the eager attempt's wander-abort
    /// trip-wire fired on the persistent UFLIA SAT solver (sticky; set by the
    /// solver's decision-checkpoint wander check, cleared on re-arm).
    fn uflia_wander_abort_tripped(&self) -> bool {
        self.incr_theory_state
            .as_ref()
            .and_then(|state| state.persistent_sat.as_ref())
            .is_some_and(|solver| solver.wander_abort_tripped())
    }

    /// Persistent-solver (conflicts, decisions) snapshot for the
    /// `AY_UFLIA_PHASE` timeline diagnostic and the #detour-snapshot-extend
    /// conflict-cap-untouched check.
    fn uflia_phase_counters(&self) -> (u64, u64) {
        self.incr_theory_state
            .as_ref()
            .and_then(|state| state.persistent_sat.as_ref())
            .map(|solver| (solver.num_conflicts(), solver.num_decisions()))
            .unwrap_or((0, 0))
    }

    /// Solve using combined EUF + LIA theory with Nelson-Oppen combination (#8778).
    ///
    /// Pure QF_UFLIA/UFLIA formulas do not need the array solver carried by the
    /// AUFLIA route. This keeps the existing LIA-family preprocessing and model
    /// recovery, but instantiates the lighter UF+LIA combiner.
    pub(in crate::executor) fn solve_uf_lia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }

        let original_assertions = self.ctx.assertions.clone();
        let (preprocessed_assertions, proof_provenance, var_subst) =
            self.preprocess_auflia_assertions_with_proof_provenance();

        if assertion_window_has_syntactic_contradiction(&self.ctx.terms, &preprocessed_assertions) {
            return Ok(SolveResult::unsat());
        }

        if var_subst.substitutions().is_empty() {
            let true_term = self.ctx.terms.true_term();
            if preprocessed_assertions.is_empty()
                || preprocessed_assertions.iter().all(|&a| a == true_term)
            {
                self.last_model = None;
                self.last_model_validated = true;
                return Ok(SolveResult::Sat);
            }
        }

        let post_preprocess_features =
            crate::features::StaticFeatures::collect(&self.ctx.terms, &preprocessed_assertions);
        if post_preprocess_features.has_int_div_mod {
            if let Some(result) = self.try_unsat_via_mod_free_subset(&preprocessed_assertions)? {
                return Ok(result);
            }
            if let Some(result) = self.try_sat_via_mod_free_or_branch()? {
                return Ok(result);
            }
            return self.solve_uf_nia();
        }

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        // #uflia-cong-repair-arm: mark this as a UFLIA combiner solve so the
        // independent gate records a UFLIA function-graph refutation
        // (cleared per solve at `check_sat_internal` entry, so the
        // `solve_uf_nia` int-div/mod fallback above — which returns before
        // here — never carries the marker).
        self.uflia_congruence_lane = true;
        // #relevancy-lazy-routing: defensive reset — an early `?`-return inside
        // a prior attempt's pipeline could have skipped the inline flag resets;
        // both flags are strictly per-attempt and must never leak into other
        // lanes' pipeline invocations (heuristic-only either way, but keep the
        // default path byte-identical).
        self.split_eager_wander_abort = false;
        self.split_eager_relevancy_hard = false;
        self.split_lazy_relevancy_hard = false;
        self.split_lazy_detour_conflict_budget = None;
        let result =
            self.with_deferred_postprocessing(preprocessed_assertions, proof_provenance, |this| {
                this.configure_sat_search_tuning(100.0, 1.1, 0.01);
                // #relevancy-lazy-routing: arm selection (see `UfliaSplitArm`).
                // Eager/Hybrid run the eager DPLL(T) arm first; Hybrid arms the
                // wander-abort trip-wire so a WANDERING eager attempt aborts
                // early (Unknown + sticky trip signal) instead of burning the
                // whole deadline, then runs a BOUNDED lazy detour (relevancy
                // HARD — the design prototype's regime for the branch-space-
                // bound Hash family) and, if that comes back undecided,
                // RESUMES the eager arm for the remainder of the budget.
                // #uflia-model-repair (route `eager`, the default): the ONE
                // targeted repair re-solve forces the eager arm as a single
                // full-window run — no wander-abort reroute, no detour, no
                // resume. On the model-rejection tail every rejected
                // candidate came from an eager-family arm while the detour
                // theory-spins its window, so the remnant budget goes to the
                // one arm that can re-find a (now trap-blocked) candidate.
                // The flag can only be `true` under `AY_UFLIA_MODEL_REPAIR=1`
                // and only for that single re-solve; default off is
                // byte-identical.
                // L2 (combined-theory-engine campaign): the lazy-DT-AUFLIA lane
                // under `AY_DT_LAZY_AUFLIA_EAGER` forces the EAGER arm — the
                // sparse on-demand DT axioms make the residual eager-tractable,
                // so the hybrid's lazy detour is pure wasted wall (see the field
                // doc). Same override shape as `uflia_repair_eager_direct`; both
                // only change trajectory, never a verdict.
                let _uflia_arm = if this.uflia_repair_eager_direct
                    || this.dt_lazy_auflia_eager_arm
                {
                    UfliaSplitArm::Eager
                } else {
                    uflia_split_arm()
                };
                // #demand-uflia-lazy-first: the M5 demand lane deliberately
                // presents the ground solver with a small, frontier-bounded
                // batch.  On that shape the eager UFLIA extension can return
                // `Unknown` only after spending essentially the whole solve
                // deadline, without tripping its wander/model-reject signals;
                // the lazy arm closes the same batch immediately.  Give an
                // ACTUALLY ARMED demand solve the existing bounded lazy detour
                // first, then fall back to the existing isolated eager attempt
                // if the detour is undecided.  This is scheduling only: both
                // arms retain their full UNSAT verification and SAT model gates.
                // The debug force-eager differential never arms the demand
                // lane, so its control solve remains byte-identical.
                // #uflia-model-repair: the ONE targeted repair re-solve
                // (`uflia_targeted_model_repair_resolve`) routes the hybrid
                // detour-direct — the eager first attempt's boolean re-wander
                // is the measured burn on the model-rejection tail, while the
                // relevancy-hard detour reaches the N-O accept points where
                // the armed congruence-repair scan / finite-domain rescue
                // run. Piggybacks the demand lane's existing lazy-first
                // scheduling seam (soundness note there applies verbatim).
                // The flag can only be `true` under `AY_UFLIA_MODEL_REPAIR=1`
                // and only for that single re-solve; default off is
                // byte-identical.
                let _uflia_demand_first = _uflia_arm == UfliaSplitArm::Hybrid
                    && (this.demand_lane_armed() || this.uflia_repair_detour_direct);
                // Single definition of the eager DPLL(T) attempt, stamped for
                // BOTH the first attempt and (hybrid only) the post-detour
                // eager RESUME so the two invocations can never drift apart.
                // `$exec` is the executor binding at the expansion site (the
                // resume runs inside a nested isolated-state closure, so it
                // cannot hygienically reuse the outer `this`). Whether the
                // wander-abort trip-wire is armed is governed by
                // `split_eager_wander_abort` at expansion time; the eager arm
                // re-applies relevancy/wander/budget settings per round.
                macro_rules! uflia_eager_attempt {
                    ($exec:ident) => {
                        solve_incremental_split_loop_pipeline!($exec,
                        tag: "UFLIA",
                        persistent_sat_field: persistent_sat,
                        create_theory: {
                            let mut tc = TheoryCombiner::uf_lia(&$exec.ctx.terms);
                            tc.set_interrupt($exec.solve_interrupt.clone());
                            tc.set_deadline($exec.solve_deadline.get());
                            // #uflia-cong-repair-arm: enable the accept-point scan
                            // only when the Executor armed a reactive re-solve.
                            tc.set_arm_uflia_congruence_repair(
                                $exec.arm_uflia_congruence_repair,
                            );
                            // Enable the D0 datatype clash/acyclicity final-check
                            // pass for datatype-bearing problems (no-op otherwise;
                            // stage-4 review F1: every combiner-backed DT+X lane
                            // hosts the pass — every hybrid arm included).
                            let dt_info: Vec<(String, Vec<String>)> = $exec
                                .ctx
                                .datatype_iter()
                                .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
                                .collect();
                            tc.register_datatypes(&dt_info);
                            tc
                        },
                        extract_models: |theory| extract_uflia_theory_models(
                            &$exec.ctx.terms,
                            &$exec.ctx.assertions,
                            &original_assertions,
                            &var_subst,
                            theory,
                        ),
                        max_splits: MAX_SPLITS_LIA,
                        pre_theory_import: |theory, lc, hc, ds| {
                            theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                            theory.import_dioph_state(std::mem::take(ds));
                        },
                        post_theory_export: |theory| {
                            let (lc, hc) = theory
                                .take_learned_state()
                                .unwrap_or_else(|| (Vec::new(), empty_hash_set()));
                            let ds = theory.take_dioph_state().unwrap_or_default();
                            (lc, hc, ds)
                        },
                        eager_extension: true,
                        pre_iter_check: |_s| {
                            solve_interrupt
                                .as_ref()
                                .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                                || solve_deadline.expired()
                        },
                        // #6812 sound relaxation: accept a post-CDCL-split propositional
                        // UNSAT ONLY when a FRESH UF+LIA combiner re-derives UNSAT from
                        // the ORIGINAL assertions (verify-before-accept). NOT the
                        // unverified `accept_unsat_after_splits` opt-in — the verify gate
                        // is non-optimistic and closes the stale-learned-conflict vector.
                        verify_unsat_after_splits: true,
                        skip_arith_triangle: true
                        )
                    };
                }
                // AY_UFLIA_PHASE timeline diagnostic (measurement-only).
                let _uflia_phase_t0 =
                    uflia_phase_debug().then(ay_core::time::Instant::now);
                macro_rules! uflia_phase {
                    ($exec:ident, $label:expr, $result:expr) => {
                        if let Some(t0) = _uflia_phase_t0 {
                            let (c, d) = $exec.uflia_phase_counters();
                            let verdict = match &$result {
                                Ok(r) if r.is_sat() => "sat",
                                Ok(r) if r.is_unsat() => "unsat",
                                Ok(_) => "unknown",
                                Err(_) => "err",
                            };
                            safe_eprintln!(
                                "[uflia-phase] {} elapsed={:.2}s result={} tripped={} conflicts={} decisions={}",
                                $label,
                                t0.elapsed().as_secs_f64(),
                                verdict,
                                $exec.uflia_wander_abort_tripped(),
                                c,
                                d
                            );
                            // Inc0-0b: synchronous per-arm LIA counter snapshot
                            // (non-draining; only when --lia-instrument is
                            // also set) — attributes the check-call totals to a
                            // specific arm via phase-edge deltas.
                            if let Some(lia_line) = ay_lia::instrument::snapshot_line() {
                                safe_eprintln!("[uflia-phase] {} {}", $label, lia_line);
                            }
                        }
                    };
                }
                // #model-reject-reroute: model-validation failures BEFORE the
                // eager attempt, so a strictly-increased counter after an
                // `unknown` identifies "the eager attempt FOUND a sat candidate
                // but a validation gate refuted the extracted model" — a
                // trajectory problem exactly like wander (the Hash tail's
                // Class-A reds give up here at ~1s of a 20s budget with
                // `tripped=false`, e.g. `hash_sat_04_13`: eager1 sat-candidate
                // rejected by the strict arithmetic oracle at 0.75s, final
                // verdict unknown, 19s unused). The counter resets at
                // check-sat entry, so the delta is attempt-scoped.
                let _uflia_mvf_before = this.last_statistics.model_validation_failures;
                let mut result: Result<SolveResult> = Ok(SolveResult::Unknown);
                if _uflia_arm != UfliaSplitArm::Lazy && !_uflia_demand_first {
                    this.split_eager_wander_abort = _uflia_arm == UfliaSplitArm::Hybrid;
                    result = uflia_eager_attempt!(this);
                    this.split_eager_wander_abort = false;
                    uflia_phase!(this, "eager1-done", result);
                }
                // Lazy-arm fallback: forced (`AY_UFLIA_ARM=lazy`, unbounded)
                // or the hybrid wander-abort fired with budget left (BOUNDED
                // detour). Sound: the lazy arm is a complete, independently
                // gate-validated solve path (AUFLIA / AUFLRA production
                // path); re-running the check-sat on it only changes the
                // search trajectory. The aborted eager attempt contributed
                // nothing but `unknown` + retained learned clauses (valid
                // implications of the same formula).
                //
                // #model-reject-reroute: an in-attempt MODEL REJECTION is a
                // second trip condition. Soundness-identical to the wander
                // trip (the re-route only changes which complete, gate-
                // validated pipeline consumes the remaining budget), and
                // green-neutral by construction: it only fires when the
                // attempt already returned `unknown` — a verdict the baseline
                // would have EMITTED as final while abandoning the rest of
                // the budget.
                let _uflia_model_rejected =
                    this.last_statistics.model_validation_failures > _uflia_mvf_before;
                let _uflia_hybrid_trip = _uflia_arm == UfliaSplitArm::Hybrid
                    && matches!(result, Ok(SolveResult::Unknown))
                    && !this.ite_uf_definition_recovery.ready()
                    && (_uflia_demand_first
                        || this.uflia_wander_abort_tripped()
                        || _uflia_model_rejected)
                    && !solve_deadline.expired()
                    && !solve_interrupt.as_ref().is_some_and(|flag| {
                        flag.load(std::sync::atomic::Ordering::Relaxed)
                    });
                if _uflia_arm == UfliaSplitArm::Lazy || _uflia_hybrid_trip {
                    // BOUNDED DETOUR (hybrid only; forced-lazy stays
                    // unbounded): the lazy re-run diverges on some
                    // trip-sensitive eager greens (wisas `xs_13_13`), so it
                    // must never be allowed to burn the rest of the budget.
                    // Primary bound: the solver's deterministic conflict
                    // budget (+32x decision companion), consumed by the lazy
                    // split-loop macro (machine-independent). Backstop: 40%
                    // of the REMAINING wall budget, polled per round and
                    // threaded into each round's combiner deadline.
                    let _uflia_detour_deadline: Option<ay_core::time::Instant> =
                        if _uflia_hybrid_trip {
                            this.solve_deadline.get().map(|dl| {
                                let now = ay_core::time::Instant::now();
                                now + dl.saturating_duration_since(now) * 2 / 5
                            })
                        } else {
                            None
                        };
                    // Snapshot the persistent solver's deterministic budgets:
                    // the detour caps must not leak into the eager resume or
                    // a later lane sharing the solver (the eager-persistent
                    // arm does not re-install budgets per round).
                    let _uflia_saved_budgets = this
                        .incr_theory_state
                        .as_ref()
                        .and_then(|state| state.persistent_sat.as_ref())
                        .map(|solver| (solver.conflict_budget(), solver.decision_budget()));
                    // #detour-snapshot-extend: conflict counter at detour
                    // entry, for the cap-untouched wall-kill classification.
                    let _uflia_detour_c0 = this.uflia_phase_counters().0;
                    this.split_lazy_detour_conflict_budget =
                        _uflia_hybrid_trip.then(uflia_detour_conflict_budget);
                    this.split_lazy_relevancy_hard = true;
                    // #probe-subset-cache: never let a subset proven under a
                    // previous attempt/check-sat seed this detour's probes.
                    ay_lia::reset_probe_subset_hint();
                    if let (Some(t0), Some(dl)) = (_uflia_phase_t0, _uflia_detour_deadline) {
                        safe_eprintln!(
                            "[uflia-phase] detour-start elapsed={:.2}s window={:.2}s conflict_cap={:?}",
                            t0.elapsed().as_secs_f64(),
                            dl.saturating_duration_since(ay_core::time::Instant::now())
                                .as_secs_f64(),
                            this.split_lazy_detour_conflict_budget
                        );
                    }
                    // #detour-snapshot-extend: NO state feed-forward into the
                    // continuation beyond the persistent SAT solver's warm
                    // VSIDS/phases/learned clauses. An earlier cut carried
                    // the baseline detour's exported lemma pile across via an
                    // in-loop tee (a periodic clone inside
                    // `post_theory_export`, armed in extension mode only) —
                    // MEASURED REJECTED: the clone's wall cost systematically
                    // shifted the baseline detour's wall-kill point
                    // (hash_sat_03_09: extension-mode detour cut at 0
                    // conflicts vs 1 with the extension disabled, 2/2 runs),
                    // which changes the harvest state the resume reads and
                    // flipped the fragile 3-conflict resume green into a
                    // wander. The primitive's core contract is that the
                    // BASELINE phases are byte-identical whether or not the
                    // extension is enabled; any speculative-phase
                    // optimization that costs baseline wall time violates it.
                    // Single definition of the bounded lazy detour, stamped
                    // for BOTH the baseline detour and (extension only) the
                    // #detour-snapshot-extend CONTINUATION so the two
                    // invocations can never drift apart. `$deadline` is the
                    // phase's wall deadline (`Option<Instant>`), threaded
                    // into each round's combiner budget and the per-round
                    // exit poll.
                    macro_rules! uflia_lazy_detour {
                        ($exec:ident, $deadline:expr) => {
                            solve_incremental_split_loop_pipeline!($exec,
                                tag: "UFLIA",
                                persistent_sat_field: persistent_sat,
                                create_theory: {
                                    let mut tc = TheoryCombiner::uf_lia(&$exec.ctx.terms);
                                    tc.set_interrupt($exec.solve_interrupt.clone());
                                    // Bounded detour: each round's combiner must
                                    // observe the DETOUR deadline (min with the outer
                                    // solve deadline), otherwise a single dense
                                    // theory round could outlive the detour window.
                                    tc.set_deadline(
                                        match ($exec.solve_deadline.get(), $deadline) {
                                            (Some(a), Some(b)) => Some(a.min(b)),
                                            (a, b) => a.or(b),
                                        },
                                    );
                                    // #uflia-cong-repair-arm: mirror the eager arm.
                                    tc.set_arm_uflia_congruence_repair(
                                        $exec.arm_uflia_congruence_repair,
                                    );
                                    // #probe-subset-cache: detour rounds opt in to the
                                    // cached-subset-first farkas probe (the eager arm
                                    // stays byte-identical). Converts wisas `xs_26_26`
                                    // (detour sat ~4s vs unknown at a 22s window);
                                    // scoped here because enabling it in the eager arm
                                    // measurably re-routes its trajectories both ways.
                                    tc.set_probe_subset_cache(true);
                                    // Enable the D0 datatype clash/acyclicity
                                    // final-check pass (no-op without datatypes;
                                    // stage-4 review F1 — every arm hosts it).
                                    let dt_info: Vec<(String, Vec<String>)> = $exec
                                        .ctx
                                        .datatype_iter()
                                        .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
                                        .collect();
                                    tc.register_datatypes(&dt_info);
                                    tc
                                },
                                extract_models: |theory| extract_uflia_theory_models(
                                    &$exec.ctx.terms,
                                    &$exec.ctx.assertions,
                                    &original_assertions,
                                    &var_subst,
                                    theory,
                                ),
                                max_splits: MAX_SPLITS_LIA,
                                pre_theory_import: |theory, lc, hc, ds| {
                                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                                    theory.import_dioph_state(std::mem::take(ds));
                                },
                                post_theory_export: |theory| {
                                    let (lc, hc) = theory
                                        .take_learned_state()
                                        .unwrap_or_else(|| (Vec::new(), empty_hash_set()));
                                    let ds = theory.take_dioph_state().unwrap_or_default();
                                    (lc, hc, ds)
                                },
                                pre_iter_check: |_s| {
                                    solve_interrupt
                                        .as_ref()
                                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                                        || solve_deadline.expired()
                                        || $deadline
                                            .is_some_and(|dl| ay_core::time::Instant::now() >= dl)
                                }
                            )
                        };
                    }
                    let lazy_result = uflia_lazy_detour!(this, _uflia_detour_deadline);
                    this.split_lazy_relevancy_hard = false;
                    this.split_lazy_detour_conflict_budget = None;
                    if _uflia_hybrid_trip {
                        if let Some(state) = this.incr_theory_state.as_mut() {
                            if let Some(solver) = state.persistent_sat.as_mut() {
                                let (cb, db) = _uflia_saved_budgets.unwrap_or((None, None));
                                solver.set_conflict_budget(cb);
                                solver.set_decision_budget(db);
                            }
                        }
                    }
                    result = lazy_result;
                    uflia_phase!(this, "detour-done", result);
                    // #detour-snapshot-extend: SPECULATIVE detour extension
                    // behind a state snapshot (the deterministic exact-replay
                    // primitive — see `uflia_detour_extend_quantum` for the
                    // full rationale and the measured evidence).
                    //
                    // Preconditions (all must hold; each keeps a measured
                    // failure class out):
                    //  - hybrid trip + undecided + budget left: extension is a
                    //    detour-phase concern only;
                    //  - WALL-KILLED at the soft window with the deterministic
                    //    conflict cap untouched: the converging-grind signature
                    //    (a cap-killed or self-terminated detour would not
                    //    benefit);
                    //  - THEORY-DOMINATED round profile (theory > 2x SAT,
                    //    measured separation 2.8x-25x converging vs <= 1.0x
                    //    diverging): the one-lemma-per-round grind class;
                    //  - wall slack covers the resume RESERVE plus a minimum
                    //    useful quantum: the resume-decided greens keep their
                    //    resume window regardless of `T`.
                    //
                    // The failed-speculation path RESTORES every harvest
                    // surface the later phases read — `ctx.terms` (the lazy
                    // rounds' split/negation atoms; the sanctioned faithful
                    // Clone), the ay-lia thread-local probe state (subset
                    // hint + scan-fail counters that steer the probe strategy
                    // switch), the `last_*` result/model/statistics fields,
                    // the #4535 conflict-verification memo, and — via the
                    // proof tracker's own #4534 scope machinery (push =
                    // watermark, pop = truncate steps + prune maps) — every
                    // proof step the continuation recorded, so a later
                    // phase's proof can never chain through steps whose
                    // terms the snapshot rolled back. The persistent SAT
                    // solver needs no restore for the RESUME (the resume
                    // runs on a nested fresh isolated state) and none for
                    // later check-sats either: `with_deferred_postprocessing`
                    // runs this whole closure on an isolated incremental
                    // state that is discarded at exit.
                    if _uflia_hybrid_trip
                        && matches!(result, Ok(SolveResult::Unknown))
                        && !solve_deadline.expired()
                        && !solve_interrupt.as_ref().is_some_and(|flag| {
                            flag.load(std::sync::atomic::Ordering::Relaxed)
                        })
                    {
                        if let (Some(quantum), Some(outer_dl), Some(detour_dl)) = (
                            uflia_detour_extend_quantum(),
                            this.solve_deadline.get(),
                            _uflia_detour_deadline,
                        ) {
                            let now = ay_core::time::Instant::now();
                            let wall_killed = now >= detour_dl;
                            let cap_untouched = this
                                .uflia_phase_counters()
                                .0
                                .saturating_sub(_uflia_detour_c0)
                                < uflia_detour_conflict_budget();
                            let sat_cum = this
                                .last_statistics
                                .get_float("time.dpll.sat_solve")
                                .unwrap_or(0.0);
                            let theory_cum = this
                                .last_statistics
                                .get_float("time.dpll.theory_check")
                                .unwrap_or(0.0);
                            let theory_dominated =
                                theory_cum > 0.0 && theory_cum > 2.0 * sat_cum;
                            let ext_budget = quantum.min(
                                outer_dl
                                    .saturating_duration_since(now)
                                    .saturating_sub(uflia_detour_resume_reserve()),
                            );
                            if wall_killed
                                && cap_untouched
                                && theory_dominated
                                && ext_budget >= UFLIA_DETOUR_EXTEND_MIN
                            {
                                // SNAPSHOT the harvest state (exact-replay
                                // contract: everything a later phase reads).
                                let _uflia_ext_snap_terms = this.ctx.terms.clone();
                                let _uflia_ext_snap_probe = ay_lia::save_probe_state();
                                let _uflia_ext_snap_unknown = this.last_unknown_reason;
                                let _uflia_ext_snap_result = this.last_result.clone();
                                let _uflia_ext_snap_model = this.last_model.clone();
                                let _uflia_ext_snap_model_validated =
                                    this.last_model_validated;
                                let _uflia_ext_snap_stats = this.last_statistics.clone();
                                let _uflia_ext_snap_memo =
                                    this.conflict_semantic_verify_memo.clone();
                                // #verify-memo: the prop-verification memo is
                                // TermId-keyed like the conflict memo; the
                                // term rollback below invalidates ids minted
                                // during speculation, so it joins the same
                                // save/restore contract.
                                let _uflia_ext_snap_prop_memo =
                                    this.prop_semantic_verify_memo.clone();
                                // Proof-step watermark (#4534 scope machinery):
                                // pop-on-failure truncates every step the
                                // continuation records; commit-on-win keeps
                                // them and just rebalances the scope stack.
                                crate::incremental_state::IncrementalSubsystem::push(
                                    &mut this.proof_tracker,
                                );
                                let _uflia_ext_deadline: Option<ay_core::time::Instant> =
                                    Some(now + ext_budget);
                                // Fresh deterministic caps for the continuation
                                // (the wall quantum is the binding bound).
                                this.split_lazy_detour_conflict_budget =
                                    Some(uflia_detour_conflict_budget());
                                this.split_lazy_relevancy_hard = true;
                                // NOTE: no `reset_probe_subset_hint()` here —
                                // the continuation deliberately KEEPS the
                                // baseline detour's probe state (it is the
                                // same grind continuing, and the failed path
                                // restores the snapshot anyway).
                                if let Some(t0) = _uflia_phase_t0 {
                                    safe_eprintln!(
                                        "[uflia-phase] extend-start elapsed={:.2}s window={:.2}s sat_cum={:.2}s theory_cum={:.2}s",
                                        t0.elapsed().as_secs_f64(),
                                        ext_budget.as_secs_f64(),
                                        sat_cum,
                                        theory_cum
                                    );
                                }
                                let ext_result = uflia_lazy_detour!(this, _uflia_ext_deadline);
                                this.split_lazy_relevancy_hard = false;
                                this.split_lazy_detour_conflict_budget = None;
                                if let Some(state) = this.incr_theory_state.as_mut() {
                                    if let Some(solver) = state.persistent_sat.as_mut() {
                                        let (cb, db) =
                                            _uflia_saved_budgets.unwrap_or((None, None));
                                        solver.set_conflict_budget(cb);
                                        solver.set_decision_budget(db);
                                    }
                                }
                                uflia_phase!(this, "extend-done", ext_result);
                                if matches!(ext_result, Ok(ref r) if r.is_sat() || r.is_unsat())
                                {
                                    // DECIDED: pure win. The verdict flows
                                    // through the unchanged validation gates
                                    // (deferred model validation for sat);
                                    // the continuation's term store stays
                                    // (its model/proof TermIds must remain
                                    // live), and so do its proof steps.
                                    this.proof_tracker.commit_speculative_scope();
                                    result = ext_result;
                                } else {
                                    // UNDECIDED (or errored): the speculation
                                    // must leave NO trace. Restore every
                                    // harvest surface so the eager resume
                                    // replays its baseline trajectory by
                                    // construction. An `Err` is also absorbed
                                    // into the restore: the baseline pipeline
                                    // never ran this phase, so propagating a
                                    // speculation-only error would itself be
                                    // a behavior change (panics still
                                    // propagate — fail loud on bugs).
                                    crate::incremental_state::IncrementalSubsystem::pop(
                                        &mut this.proof_tracker,
                                    );
                                    this.ctx.terms = _uflia_ext_snap_terms;
                                    ay_lia::restore_probe_state(_uflia_ext_snap_probe);
                                    this.last_unknown_reason = _uflia_ext_snap_unknown;
                                    this.last_result = _uflia_ext_snap_result;
                                    this.last_model = _uflia_ext_snap_model;
                                    this.last_model_validated =
                                        _uflia_ext_snap_model_validated;
                                    this.last_statistics = _uflia_ext_snap_stats;
                                    this.conflict_semantic_verify_memo =
                                        _uflia_ext_snap_memo;
                                    this.prop_semantic_verify_memo =
                                        _uflia_ext_snap_prop_memo;
                                }
                            }
                        }
                    }
                    // EAGER RESUME (both-arms-must-fail): if the bounded
                    // detour came back undecided and budget remains, fall
                    // back to the eager arm for the REMAINDER of the budget —
                    // this time WITHOUT the wander-abort trip-wire, so a
                    // trajectory-sensitive eager green (wisas `xs_13_13`:
                    // eager wanders early but converges by ~9.5s) is decided
                    // by eager's full run instead of being thrown away.
                    // `unknown` is now only possible when BOTH arms fail.
                    // Sound: same complete pipeline as the first attempt;
                    // only the search trajectory differs. The resume runs on
                    // a nested ISOLATED incremental state — a fresh-from-
                    // scratch eager restart — so NO detour solver state can
                    // leak into it (a direct same-solver lazy→eager resume
                    // tripped a stale clause-arena offset panic in the
                    // extension CDCL loop; isolation is the sanctioned clean
                    // re-run seam and sidesteps that entirely).
                    //
                    // Inc5 #fused-detour (`--uflia-fused-detour=1`, default
                    // off): the slot instead runs the FUSED arm — the same
                    // eager split-loop macro, but on the SHARED persistent
                    // solver (no `with_isolated_incremental_state`), RETAINING
                    // eager1's and the detour's learned clauses, with
                    // relevancy-HARD forced through the flag-respecting
                    // `split_eager_relevancy_hard` seam and the wander-abort
                    // disarmed for the fused arm only (`split_eager_wander_
                    // abort` stays false here, re-stamped per round by the
                    // macro). This is the z3-regime experiment: live theory
                    // propagation (eager1's half) + relevancy-hard decision
                    // restriction (the detour's half) in ONE arm. The
                    // ext→ext/plain→ext stale-arena hazard this re-enters is
                    // covered by the NO_REASON normalization, gated by the
                    // same-solver restart tests in ay-sat
                    // ext_restart_arena_rebuild.rs (brief question 1 CLEARED).
                    //
                    // Brief question 3 (counter insulation on the shared
                    // solver): yes, by construction — the eager macro
                    // re-installs the deterministic conflict/decision budgets
                    // EVERY round RELATIVE to the solver's live counters
                    // (`num_conflicts() + allowance`), so the conflicts and
                    // decisions eager1/the detour already consumed never
                    // shrink the fused arm's headroom; the wander trip-wire is
                    // re-armed/disarmed per round from the executor flag
                    // (false here), so stale trip baselines cannot fire; and
                    // the detour's caps were already restored above (the OUTER
                    // budget restore at detour/extension exit is kept). The
                    // saved-budget restore below re-stamps the outer values
                    // after the fused arm for the same hygiene. Nothing leaks
                    // to later check-sats either: this whole closure runs on
                    // `with_deferred_postprocessing`'s isolated incremental
                    // state, discarded at exit, and the unconditional
                    // post-attempt teardown resets every routing flag.
                    //
                    // Brief question 4: the fused arm's UNSAT path ALWAYS
                    // routes through `verify_unsat_after_splits` (the macro's
                    // cross-arm guard keys on the fused flag), so a
                    // propositional UNSAT leaning on prior-arm clauses is
                    // accepted only after a FRESH isolated re-derivation from
                    // the ORIGINAL assertions — the stale-clause backstop,
                    // unweakened.
                    //
                    // Soundness envelope (unchanged): the fused arm is the
                    // same complete, gate-validated eager pipeline; every SAT
                    // flows through the unchanged model-validation gates and
                    // every UNSAT through verify-before-accept, so flipping
                    // this flag can only move verdicts between `unknown` and a
                    // gate-validated decided verdict.
                    if _uflia_hybrid_trip
                        && matches!(result, Ok(SolveResult::Unknown))
                        && !solve_deadline.expired()
                        && !solve_interrupt.as_ref().is_some_and(|flag| {
                            flag.load(std::sync::atomic::Ordering::Relaxed)
                        })
                    {
                        this.split_eager_wander_abort = false;
                        if uflia_fused_detour_enabled() {
                            this.split_eager_relevancy_hard = true;
                            if let Some(t0) = _uflia_phase_t0 {
                                safe_eprintln!(
                                    "[uflia-phase] fused-start elapsed={:.2}s",
                                    t0.elapsed().as_secs_f64()
                                );
                            }
                            let fused_result = uflia_eager_attempt!(this);
                            this.split_eager_relevancy_hard = false;
                            // Mirror the detour/extension exits: re-stamp the
                            // attempt-entry deterministic budgets on the shared
                            // solver (outer budget restore kept — see brief
                            // question 3 above).
                            if let Some(state) = this.incr_theory_state.as_mut() {
                                if let Some(solver) = state.persistent_sat.as_mut() {
                                    let (cb, db) =
                                        _uflia_saved_budgets.unwrap_or((None, None));
                                    solver.set_conflict_budget(cb);
                                    solver.set_decision_budget(db);
                                }
                            }
                            uflia_phase!(this, "fused-done", fused_result);
                            result = fused_result;
                        } else {
                            result = this.with_isolated_incremental_state(None, |exec| {
                                let r = uflia_eager_attempt!(exec);
                                uflia_phase!(exec, "resume-done", r);
                                r
                            });
                        }
                    }
                }
                result
            });
        // #relevancy-lazy-routing: unconditional post-attempt reset (control
        // always returns here, even when the closure early-returned past its
        // inline resets) — the flags must never leak into other lanes.
        // Inc5 #fused-detour: `split_eager_relevancy_hard` joins the teardown
        // (brief seam table: post-attempt flag reset).
        self.split_eager_wander_abort = false;
        self.split_eager_relevancy_hard = false;
        self.split_lazy_relevancy_hard = false;
        self.split_lazy_detour_conflict_budget = None;
        // Also disarm the trip-wire on the shared persistent solver: the eager
        // and lazy arms re-arm/disarm it per round, but the eager-PERSISTENT
        // arm does neither, so a stale armed flag from this attempt could
        // spuriously abort a later lane's solve on the same solver.
        if let Some(state) = self.incr_theory_state.as_mut() {
            if let Some(solver) = state.persistent_sat.as_mut() {
                solver.arm_wander_abort(false);
                solver.set_relevancy_branching(false);
                solver.set_relevancy_hard(false);
            }
        }

        if matches!(result, Ok(SolveResult::Sat)) && !var_subst.substitutions().is_empty() {
            if let Some(ref full_model) = self.last_model {
                let lia_values = full_model
                    .lia_model
                    .as_ref()
                    .map(|m| &m.values)
                    .cloned()
                    .unwrap_or_default();
                let bool_overrides = super::lia::recover_substituted_bool_values(
                    &self.ctx.terms,
                    &var_subst,
                    &lia_values,
                );
                if !bool_overrides.is_empty() {
                    if let Some(ref mut full_model) = self.last_model {
                        full_model.bool_overrides.extend(bool_overrides);
                    }
                }
            }
        }

        result
    }

    /// Solve using combined EUF + NIA theory with Nelson-Oppen combination (#4525).
    ///
    /// Structurally identical to `solve_uf_nra`, substituting UfNiaSolver for UfNraSolver.
    /// NiaSolver wraps LiaSolver internally with sign lemma and tangent plane refinement
    /// for nonlinear integer products. The Nelson-Oppen combination with EUF is identical.
    ///
    /// Used for QF_UFNIA, QF_AUFNIRA, UFNIA, UFNIRA, AUFNIRA logics.
    /// NIA is incomplete (QF_NIA is undecidable — Hilbert's 10th Problem),
    /// so this solver may return Unknown on hard nonlinear instances.
    pub(in crate::executor) fn solve_uf_nia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // #nested-array-row: the EUF+NIA combination has no dedicated array
        // theory, so a determined UNSAT that requires read-over-write through a
        // named array variable (the SV-COMP UltimateAutomizer nested-memory
        // family) is missed. Attempt a sound, UNSAT-only store-flat refutation
        // BEFORE the main solve; it falls through (None) on anything but a
        // definitive UNSAT, so SAT instances are never perturbed.
        if let Some(result) = self.try_ufnia_store_flat_row_refutation()? {
            return Ok(result);
        }
        let (preprocessed_assertions, proof_provenance) =
            self.preprocess_ufnia_assertions_with_proof_provenance();
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        self.with_deferred_postprocessing(preprocessed_assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "UFNIA",
                persistent_sat_field: persistent_sat,
                create_theory: {
                    // Forward the outer deadline into the inner NIA refinement
                    // loop; polling only between theory checks permits a dense
                    // single check to overrun the caller's wall budget.
                    let mut theory = UfNiaSolver::new(&this.ctx.terms);
                    if let Some(deadline) = solve_deadline.get() {
                        theory.set_deadline(deadline);
                    }
                    theory
                },
                extract_models: |theory| {
                    let (euf, lia) = theory.extract_models();
                    TheoryModels {
                        euf: Some(euf),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LIA,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (vec![], Default::default(), Default::default())
                },
                eager_extension: true,
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                }
            )
        })
    }

    /// UNSAT-only read-over-write rescue for the array-of-array nested-memory
    /// family (`#nested-array-row`).
    ///
    /// `solve_uf_nia` has NO dedicated array theory: arrays are handled by EUF
    /// congruence plus the term rewriter's syntactic `select(store(a,i,v),i)→v`
    /// fold, which only fires when the store is SYNTACTICALLY the select's base.
    /// SV-COMP UltimateAutomizer memory scripts instead bind each SSA memory to
    /// a named array variable (`(= M1 (store M0 …))`, element sort itself an
    /// array) and read through the variable, so the fold never triggers and a
    /// determined UNSAT — a nested read forced by read-over-write to a value
    /// that a later arithmetic bound rules out — is returned as `unknown`.
    ///
    /// This inlines those single-definition `var = store(…)` equalities
    /// (`substitute_store_flat_equalities`; equisatisfiable, because a variable
    /// constrained by exactly one array-store definition and nothing else is
    /// purely definitional), which lets `mk_select`/`mk_store` collapse the
    /// nested read-over-write chains to their forced values as the assertions
    /// are rebuilt. When the fold eliminates EVERY array term, the residue is a
    /// pure Int problem the NIA solver decides directly.
    ///
    /// Soundness: only a definitive UNSAT of the equisatisfiable residue is
    /// promoted, and it is derived by exact ROW rewriting (not a validation
    /// gate). Any other outcome — including a genuinely-SAT nested read whose
    /// residue is satisfiable — returns `None` and the untouched normal solve
    /// runs, so this can never manufacture a wrong `unsat` nor perturb a `sat`.
    /// Runs on a PRIVATE copy of the assertion window with full executor-state
    /// save/restore (mirrors `try_unsat_via_arrays_to_lia_ackermann`), and bails
    /// in O(scan) when no store-flat definition inlines away every array term
    /// (e.g. the hundreds of partially-resolved reads in the full scripts).
    fn try_ufnia_store_flat_row_refutation(&mut self) -> Result<Option<SolveResult>> {
        if self.incremental_mode
            || self.original_problem_had_quantifiers
            || self.mod_div_or_branch_rescue_depth > 0
        {
            return Ok(None);
        }
        // Cheap gate: only array-carrying windows can benefit.
        if !self
            .ctx
            .assertions
            .iter()
            .any(|&a| assertion_contains_array_ops(&self.ctx.terms, a))
        {
            return Ok(None);
        }

        // Inline `var = store(…)` definitions on a PRIVATE copy so the rewriter
        // folds read-over-write through the nested store chains. ctx.assertions
        // is left untouched for the normal solve / model recovery.
        let mut folded = self.ctx.assertions.clone();
        super::solve_harness_helpers::substitute_store_flat_equalities(
            &mut self.ctx.terms,
            &mut folded,
        );
        if folded == self.ctx.assertions {
            return Ok(None); // no single-definition store-flat equality to inline
        }

        // Only proceed when the fold eliminated EVERY array term. A residue that
        // still mentions arrays is left to the normal pipeline (fail-open:
        // returns None), keeping this rescue O(scan) on the large scripts whose
        // hundreds of reads do not fully collapse.
        let reachable = crate::executor::theories::reachable_term_set(&self.ctx.terms, &folded);
        if reachable
            .iter()
            .any(|&t| matches!(self.ctx.terms.sort(t), Sort::Array(_)))
        {
            return Ok(None);
        }

        // ---- Solve the array-free residue, accept ONLY unsat ----------------
        // Equisatisfiable to the original window, so a residue UNSAT is a sound
        // UNSAT for the original. Full state save/restore; a non-unsat outcome
        // is discarded and the caller's normal solve runs unchanged.
        let proof_export_scope = self.proof_export_scope_assertions();
        let saved_assertions = std::mem::replace(&mut self.ctx.assertions, folded);
        let saved_model = self.last_model.clone();
        let saved_model_validated = self.last_model_validated;
        let saved_unknown_reason = self.last_unknown_reason;
        let saved_result = self.last_result.clone();
        let saved_skip_model_eval = self.skip_model_eval;
        let saved_read_pin_repair_done = self.read_pin_repair_done;
        let saved_branch_validation = self.sat_validated_by_mod_div_or_branch;
        let saved_proof_provenance = self.proof_problem_assertion_provenance.clone();
        let saved_statistics = std::mem::take(&mut self.last_statistics);

        // The private solve owns a fresh proof tracker and artifact set. A
        // discarded probe must not drain or overwrite proof state accumulated
        // by its caller, while an accepted proof must not inherit unrelated
        // outer steps.
        let proof_was_enabled = self.proof_tracker.is_enabled();
        let mut auxiliary_tracker = crate::proof_tracker::ProofTracker::new();
        if proof_was_enabled {
            auxiliary_tracker.enable();
        }
        let saved_proof_tracker = std::mem::replace(&mut self.proof_tracker, auxiliary_tracker);
        let saved_last_proof = self.last_proof.take();
        let saved_finite_enum_witness = self.last_finite_enum_pigeonhole.take();
        let saved_checked_finite_enum = self.last_checked_finite_enum_pigeonhole.take();
        let saved_proof_reconstruction_suppressed =
            std::mem::replace(&mut self.last_unsat_proof_reconstruction_suppressed, false);
        let saved_last_lrat_certificate = self.last_lrat_certificate.take();
        let saved_last_proof_term_overrides = self.last_proof_term_overrides.take();
        let saved_last_proof_quality = self.last_proof_quality.take();
        let saved_last_clause_trace = self.last_clause_trace.take();
        let saved_last_checked_sat_refutation = self.last_checked_sat_refutation.take();
        let saved_last_var_to_term = self.last_var_to_term.take();
        let saved_last_trail_provenance = self.last_trail_provenance.take();
        let saved_last_negations = self.last_negations.take();
        let saved_last_clausification_proofs = self.last_clausification_proofs.take();
        let saved_last_original_clause_theory_proofs =
            self.last_original_clause_theory_proofs.take();
        let saved_proof_check_result = self.proof_check_result.take();
        let saved_proof_check_ok = self.proof_check_ok;
        let saved_last_proof_rebuild_originals =
            std::mem::take(&mut self.last_proof_rebuild_originals);
        let saved_last_proof_raw_original_assertions =
            std::mem::take(&mut self.last_proof_raw_original_assertions);
        let saved_quant_expansion_records = std::mem::take(&mut self.quant_expansion_records);
        let saved_consequence_replay_state = self.take_consequence_replay_state();

        // Give solve_nia the folded window without ever promoting folded terms
        // to authored premises. Unchanged originals retain their identity;
        // reduced-only assumptions remain derived and are demoted on export.
        let folded_proof_provenance =
            ProofProblemAssertionProvenance::passthrough(&saved_assertions, &self.ctx.assertions)
                .preserving_authority_from(saved_proof_provenance.as_ref());
        self.proof_problem_assertion_provenance = Some(folded_proof_provenance);
        self.mod_div_or_branch_rescue_depth += 1;

        self.last_model = None;
        self.last_model_validated = false;
        self.last_unknown_reason = None;
        self.last_result = None;
        self.skip_model_eval = false;
        self.read_pin_repair_done = false;
        self.sat_validated_by_mod_div_or_branch = false;

        let result = self.solve_nia();

        self.mod_div_or_branch_rescue_depth -= 1;
        self.ctx.assertions = saved_assertions;
        self.last_statistics = saved_statistics;
        self.skip_model_eval = saved_skip_model_eval;
        self.read_pin_repair_done = saved_read_pin_repair_done;
        self.sat_validated_by_mod_div_or_branch = saved_branch_validation;
        self.proof_tracker = saved_proof_tracker;

        match result {
            Ok(r) if r.is_unsat() => {
                self.last_unknown_reason = None;
                // The retained proof was built over the folded residue. Keep
                // only genuine outer-scope assumptions and render every
                // reduced-only/trust leaf as an attributed Hole. The reduced
                // SAT trace and LRAT bytes certify a different CNF, so they
                // cannot accompany the original problem artifact.
                self.rescope_store_flat_row_proof_to_problem(&proof_export_scope);
                self.clear_finite_enum_proof_state();
                self.last_lrat_certificate = None;
                self.last_proof_quality = None;
                self.last_clause_trace = None;
                self.last_checked_sat_refutation = None;
                self.last_var_to_term = None;
                self.last_trail_provenance = None;
                self.last_negations = None;
                self.last_clausification_proofs = None;
                self.last_original_clause_theory_proofs = None;
                self.proof_check_result = None;
                self.proof_check_ok = false;
                self.last_proof_rebuild_originals = saved_last_proof_rebuild_originals;
                self.last_proof_raw_original_assertions = saved_last_proof_raw_original_assertions;
                self.quant_expansion_records = saved_quant_expansion_records;
                self.restore_consequence_replay_state(saved_consequence_replay_state);
                self.proof_problem_assertion_provenance = saved_proof_provenance;
                // Mark this UNSAT as the trust-free array-free-residue reduction
                // so the nested-array quarantine boundary accepts it.
                self.nested_array_row_reduction_unsat = true;
                Ok(Some(r))
            }
            Ok(_) => {
                // Restore caller-visible state; fall through to normal solve.
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.proof_problem_assertion_provenance = saved_proof_provenance;
                self.last_proof = saved_last_proof;
                self.last_finite_enum_pigeonhole = saved_finite_enum_witness;
                self.last_checked_finite_enum_pigeonhole = saved_checked_finite_enum;
                self.last_unsat_proof_reconstruction_suppressed =
                    saved_proof_reconstruction_suppressed;
                self.last_lrat_certificate = saved_last_lrat_certificate;
                self.last_proof_term_overrides = saved_last_proof_term_overrides;
                self.last_proof_quality = saved_last_proof_quality;
                self.last_clause_trace = saved_last_clause_trace;
                self.last_checked_sat_refutation = saved_last_checked_sat_refutation;
                self.last_var_to_term = saved_last_var_to_term;
                self.last_trail_provenance = saved_last_trail_provenance;
                self.last_negations = saved_last_negations;
                self.last_clausification_proofs = saved_last_clausification_proofs;
                self.last_original_clause_theory_proofs = saved_last_original_clause_theory_proofs;
                self.proof_check_result = saved_proof_check_result;
                self.proof_check_ok = saved_proof_check_ok;
                self.last_proof_rebuild_originals = saved_last_proof_rebuild_originals;
                self.last_proof_raw_original_assertions = saved_last_proof_raw_original_assertions;
                self.quant_expansion_records = saved_quant_expansion_records;
                self.restore_consequence_replay_state(saved_consequence_replay_state);
                Ok(None)
            }
            Err(err) => {
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
                self.proof_problem_assertion_provenance = saved_proof_provenance;
                self.last_proof = saved_last_proof;
                self.last_finite_enum_pigeonhole = saved_finite_enum_witness;
                self.last_checked_finite_enum_pigeonhole = saved_checked_finite_enum;
                self.last_unsat_proof_reconstruction_suppressed =
                    saved_proof_reconstruction_suppressed;
                self.last_lrat_certificate = saved_last_lrat_certificate;
                self.last_proof_term_overrides = saved_last_proof_term_overrides;
                self.last_proof_quality = saved_last_proof_quality;
                self.last_clause_trace = saved_last_clause_trace;
                self.last_checked_sat_refutation = saved_last_checked_sat_refutation;
                self.last_var_to_term = saved_last_var_to_term;
                self.last_trail_provenance = saved_last_trail_provenance;
                self.last_negations = saved_last_negations;
                self.last_clausification_proofs = saved_last_clausification_proofs;
                self.last_original_clause_theory_proofs = saved_last_original_clause_theory_proofs;
                self.proof_check_result = saved_proof_check_result;
                self.proof_check_ok = saved_proof_check_ok;
                self.last_proof_rebuild_originals = saved_last_proof_rebuild_originals;
                self.last_proof_raw_original_assertions = saved_last_proof_raw_original_assertions;
                self.quant_expansion_records = saved_quant_expansion_records;
                self.restore_consequence_replay_state(saved_consequence_replay_state);
                Err(err)
            }
        }
    }

    /// Whether `term` is AY's set-cardinality bridge axiom, `(<= 0 (set.card s))`.
    ///
    /// Recognized EXACTLY, mirroring the strict checker's schema
    /// (`ay_proof::checker::set_axiom`): the bound must be the literal `0` on the
    /// left and the bounded term a unary `set.card`. A looser match here would
    /// promote some other injected assertion into a certified lemma, which is a
    /// forging surface -- `(<= 5 (set.card s))` is false for the empty set.
    /// Whether `term` is the membership cardinality lower bound,
    /// `(ite (member x s) (<= 1 (set.card s)) (<= 0 (set.card s)))`.
    ///
    /// Mirrors the strict checker's schema exactly, including the identity of
    /// the set under the membership test and under both cardinality bounds --
    /// without it this would licence `x in s => |t| >= 1` for an unrelated `t`.
    pub(in crate::executor) fn is_set_card_member_lower_bound_axiom(
        terms: &TermStore,
        term: TermId,
    ) -> bool {
        use ay_core::{Constant, TermData};

        fn membership_set(terms: &TermStore, term: TermId) -> Option<TermId> {
            let TermData::App(operator, args) = terms.get(term) else {
                return None;
            };
            match (operator.name(), args.len()) {
                ("select", 2) => Some(args[0]),
                ("set.member", 2) => Some(args[1]),
                _ => None,
            }
        }

        fn card_bounded_by(terms: &TermStore, term: TermId, bound: i64) -> Option<TermId> {
            let TermData::App(comparison, comparison_args) = terms.get(term) else {
                return None;
            };
            if comparison.name() != "<=" || comparison_args.len() != 2 {
                return None;
            }
            match terms.get(comparison_args[0]) {
                TermData::Const(Constant::Int(value)) if *value == bound.into() => {}
                _ => return None,
            }
            let TermData::App(operator, operator_args) = terms.get(comparison_args[1]) else {
                return None;
            };
            (operator.name() == "set.card" && operator_args.len() == 1).then(|| operator_args[0])
        }

        let TermData::Ite(condition, then_branch, else_branch) = terms.get(term) else {
            return false;
        };
        let (Some(tested), Some(when_member), Some(otherwise)) = (
            membership_set(terms, *condition),
            card_bounded_by(terms, *then_branch, 1),
            card_bounded_by(terms, *else_branch, 0),
        ) else {
            return false;
        };
        tested == when_member && tested == otherwise
    }

    /// Whether `term` is `(= (set.card e) 0)` for a SYNTACTICALLY empty `e`.
    ///
    /// Mirrors the strict checker's schema, including that a `const-array`
    /// fill must be `false`: a `true` fill is the UNIVERSAL set, whose
    /// cardinality is the index sort's size.
    pub(in crate::executor) fn is_set_card_empty_axiom(terms: &TermStore, term: TermId) -> bool {
        use ay_core::{Constant, TermData};

        fn syntactically_empty(terms: &TermStore, term: TermId) -> bool {
            let TermData::App(operator, args) = terms.get(term) else {
                return false;
            };
            match operator.name() {
                "set.empty" => args.is_empty(),
                "const-array" => matches!(
                    args.as_slice(),
                    [fill] if matches!(terms.get(*fill), TermData::Const(Constant::Bool(false)))
                ),
                _ => false,
            }
        }

        let TermData::App(equality, equality_args) = terms.get(term) else {
            return false;
        };
        if equality.name() != "=" || equality_args.len() != 2 {
            return false;
        }
        if !matches!(
            terms.get(equality_args[1]),
            TermData::Const(Constant::Int(value)) if *value == 0.into()
        ) {
            return false;
        }
        let TermData::App(operator, operator_args) = terms.get(equality_args[0]) else {
            return false;
        };
        operator.name() == "set.card"
            && operator_args.len() == 1
            && syntactically_empty(terms, operator_args[0])
    }

    /// Whether `term` is the counted-membership cardinality bound: an `ite`
    /// tree over membership tests whose leaves bound `set.card` below by the
    /// number of memberships holding on the path.
    ///
    /// Mirrors the strict checker's schema, INCLUDING that every index be a
    /// distinct integer literal -- two variable indices could denote the same
    /// element, so counting them separately would licence a bound the set does
    /// not have.
    pub(in crate::executor) fn is_set_card_member_count_axiom(
        terms: &TermStore,
        term: TermId,
    ) -> bool {
        use ay_core::{Constant, TermData};

        fn member_index(terms: &TermStore, term: TermId) -> Option<(TermId, TermId)> {
            let TermData::App(operator, args) = terms.get(term) else {
                return None;
            };
            match (operator.name(), args.len()) {
                ("select", 2) => Some((args[0], args[1])),
                ("set.member", 2) => Some((args[1], args[0])),
                _ => None,
            }
        }

        fn leaf_bound(terms: &TermStore, term: TermId, count: usize) -> Option<TermId> {
            let TermData::App(comparison, comparison_args) = terms.get(term) else {
                return None;
            };
            if comparison.name() != "<=" || comparison_args.len() != 2 {
                return None;
            }
            if !matches!(
                terms.get(comparison_args[0]),
                TermData::Const(Constant::Int(v)) if *v == count.into()
            ) {
                return None;
            }
            let TermData::App(operator, operator_args) = terms.get(comparison_args[1]) else {
                return None;
            };
            (operator.name() == "set.card" && operator_args.len() == 1)
                .then_some(comparison_args[1])
        }

        fn walk(
            terms: &TermStore,
            node: TermId,
            set: TermId,
            card: &mut Option<TermId>,
            path: &mut Vec<BigInt>,
        ) -> bool {
            let TermData::Ite(condition, then_branch, else_branch) = terms.get(node) else {
                let Some(bounded) = leaf_bound(terms, node, path.len()) else {
                    return false;
                };
                return *card.get_or_insert(bounded) == bounded;
            };
            let Some((tested, index)) = member_index(terms, *condition) else {
                return false;
            };
            if tested != set {
                return false;
            }
            let TermData::Const(Constant::Int(value)) = terms.get(index) else {
                return false;
            };
            if path.contains(value) {
                return false;
            }
            path.push(value.clone());
            let then_ok = walk(terms, *then_branch, set, card, path);
            path.pop();
            then_ok && walk(terms, *else_branch, set, card, path)
        }

        let TermData::Ite(condition, ..) = terms.get(term) else {
            return false;
        };
        let Some((set, _)) = member_index(terms, *condition) else {
            return false;
        };
        let mut card = None;
        let mut path = Vec::new();
        walk(terms, term, set, &mut card, &mut path)
            && card.is_some_and(|c| {
                matches!(terms.get(c), TermData::App(op, a)
                    if op.name() == "set.card" && a.len() == 1 && a[0] == set)
            })
    }

    /// Whether `term` is `(= (set.card s) 0)` for ANY set term `s`.
    ///
    /// Deliberately shape-only. Whether the problem actually forces `s` empty
    /// is the CHECKER's business, decided against a registry built from the
    /// problem's top-level asserted equalities; classifying here merely routes
    /// the step to that check instead of leaving it an unexaminable `Trust`.
    pub(in crate::executor) fn is_set_card_zero_axiom(terms: &TermStore, term: TermId) -> bool {
        use ay_core::{Constant, TermData};

        let TermData::App(equality, equality_args) = terms.get(term) else {
            return false;
        };
        if equality.name() != "=" || equality_args.len() != 2 {
            return false;
        }
        if !matches!(
            terms.get(equality_args[1]),
            TermData::Const(Constant::Int(value)) if *value == 0.into()
        ) {
            return false;
        }
        matches!(
            terms.get(equality_args[0]),
            TermData::App(operator, args) if operator.name() == "set.card" && args.len() == 1
        )
    }

    pub(in crate::executor) fn is_set_card_non_negative_axiom(
        terms: &TermStore,
        term: TermId,
    ) -> bool {
        use ay_core::{Constant, Symbol, TermData};

        let TermData::App(Symbol::Named(comparison), comparison_args) = terms.get(term) else {
            return false;
        };
        if comparison != "<=" || comparison_args.len() != 2 {
            return false;
        }
        let (bound, cardinality) = (comparison_args[0], comparison_args[1]);
        if !matches!(terms.get(bound), TermData::Const(Constant::Int(value)) if *value == 0.into())
        {
            return false;
        }
        matches!(
            terms.get(cardinality),
            TermData::App(Symbol::Named(operator), operator_args)
                if operator == "set.card" && operator_args.len() == 1
        )
    }

    /// Re-scope a store-flat auxiliary refutation to the caller's authored
    /// assertion window.
    ///
    /// Store-flat folding introduces no fresh symbols, so unlike arrays-to-LIA
    /// this needs no term substitution. It only prevents the folded residue
    /// from escaping as free `Assume`/`trust` authority.
    fn rescope_store_flat_row_proof_to_problem(&mut self, problem_assertions: &[TermId]) {
        use ay_core::{AletheRule, ProofStep, TheoryLemmaKind};

        self.clear_finite_enum_proof_state();
        let Some(mut proof) = self.last_proof.take() else {
            return;
        };
        let problem_set: HashSet<TermId> = problem_assertions.iter().copied().collect();

        for step in &mut proof.steps {
            match step {
                // A solver-injected bridge axiom is not an authored premise, so
                // it cannot stay an `Assume` -- but when its schema is
                // independently checkable it need not become a `hole` either.
                // `(<= 0 (set.card s))` holds for every set, and demoting it
                // left EVERY `set.card` refutation externally uncheckable
                // although the rest of the proof (`la_generic`, `ite_pos2`,
                // resolution) already checked.
                ProofStep::Assume(term)
                    if !problem_set.contains(term)
                        && Self::is_set_card_non_negative_axiom(&self.ctx.terms, *term) =>
                {
                    *step = ProofStep::TheoryLemma {
                        theory: "sets".to_string(),
                        clause: vec![*term],
                        farkas: None,
                        kind: TheoryLemmaKind::SetCardNonNegative,
                        lia: None,
                    };
                }
                ProofStep::Assume(term) if !problem_set.contains(term) => {
                    *step = ProofStep::Step {
                        rule: AletheRule::Hole,
                        clause: vec![*term],
                        premises: Vec::new(),
                        args: Vec::new(),
                    };
                }
                ProofStep::TheoryLemma {
                    clause,
                    kind: TheoryLemmaKind::Generic,
                    ..
                } => {
                    *step = ProofStep::Step {
                        rule: AletheRule::Hole,
                        clause: std::mem::take(clause),
                        premises: Vec::new(),
                        args: Vec::new(),
                    };
                }
                ProofStep::Step { rule, .. } if matches!(rule, AletheRule::Trust) => {
                    *rule = AletheRule::Hole;
                }
                _ => {}
            }
        }

        self.last_proof = Some(proof);
    }
    /// Solve using combined Arrays + EUF + LIA theory
    ///
    /// This handles both integer branch-and-bound splits (NeedSplit) and
    /// disequality splits (NeedDisequalitySplit) for integer variables.
    pub(in crate::executor) fn solve_auf_lia(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Keep the pre-substitution equalities for model recovery. The solve
        // closure sees the preprocessed assertion window, where a definition
        // such as `x = default(a)` may have eliminated `x`; the original
        // companion constraint `x = 5` is then the only exact source for the
        // symbolic array default's value.
        let original_assertions = self.ctx.assertions.clone();
        let original_features =
            crate::features::StaticFeatures::collect(&self.ctx.terms, &original_assertions);
        if original_features.has_arrays
            && original_features.has_int_div_mod
            && !self.int_div_mod_terms_have_known_zero_or_constant_divisors(&self.ctx.assertions)
            && !self
                .assertion_window_has_quantifier_consumer_completion_marker(&self.ctx.assertions)
        {
            self.record_arithmetic_unsupported_fragment_diagnostics();
            self.last_unknown_reason = Some(UnknownReason::UnsupportedArithmetic);
            return Ok(SolveResult::Unknown);
        }
        if original_features.has_arrays
            && self.assertion_window_has_quantifier_consumer_singleton_prefix_array_ext_eq(
                &self.ctx.assertions,
            )
            && !assertion_window_has_top_level_not(&self.ctx.terms, &self.ctx.assertions)
        {
            if let Some(result) = self.try_unsat_via_quantifier_consumer_completion_preprocess()? {
                return Ok(result);
            }
        }
        // Fast path: if the formula has no substantive integer arithmetic
        // constraints (no comparisons, no +/-/*/mod/div, no integer constants),
        // delegate to Array+EUF which avoids the expensive N-O combination
        // with LIA. This handles QF_AUFLIA formulas where Int is used only
        // as the Array index/value sort with no arithmetic reasoning (#6546).
        //
        // In incremental mode, keep pure-UF/Int formulas on the rebuilding
        // AUFLIA path instead of the persistent ArrayEUF fast path. Reusing the
        // no-split incremental state across a pop()+re-push contradiction cycle
        // can retain stale scoped reasoning and produce a false SAT model
        // (#6813). Rebuilding the combined solver each check-sat preserves
        // soundness while we keep the pure fast path for non-incremental solves.
        if !self.incremental_mode
            && (ay_core::misc_cli_flags().force_array_euf
                || !crate::term_helpers::has_substantive_int_constraints(
                    &self.ctx.terms,
                    &self.ctx.assertions,
                ))
        {
            // Only route to Array+EUF if at least one assertion actually
            // involves array operations (select/store/array-sorted terms).
            // When all assertions simplified away their array content (e.g.,
            // mk_select constant folding reduced select(store(a,i,v),i) to v),
            // the TermStore still contains residual array terms. Routing to
            // solve_array_euf would let the TheoryExtension scan those
            // unreachable terms and generate spurious NeedModelEquality
            // requests, causing false Unknown.
            let has_array_ops = self
                .ctx
                .assertions
                .iter()
                .any(|&a| assertion_contains_array_ops(&self.ctx.terms, a));
            if has_array_ops {
                return self.solve_array_euf();
            }
            // No array ops — use EUF solver which handles equalities without
            // the overhead of the combined AUFLIA pipeline (preprocessing,
            // deferred postprocessing, Nelson-Oppen combination). This avoids
            // false Unknown from the AUFLIA pipeline on trivial formulas like
            // (= x 42) where mk_select folding removed all array content.
            return self.solve_euf();
        }

        let (preprocessed_assertions, proof_provenance, var_subst) =
            self.preprocess_auflia_assertions_with_proof_provenance();
        // The AUFLIA legacy array fixpoint runs inside preprocessing and may
        // synthesize nested array-valued equalities. Exact finite closure must
        // therefore run on this final surface, not on the authored store-flat
        // aliases seen by the route-independent dispatcher.
        let preprocessed_assertions =
            self.close_finite_arrays_in_owned_assertion_window(preprocessed_assertions, &[]);

        if assertion_window_has_syntactic_contradiction(&self.ctx.terms, &preprocessed_assertions) {
            return Ok(SolveResult::unsat());
        }

        // Fast path: when AUFLIA preprocessing (PropagateValues, array axiom
        // fixpoint) reduced all assertions to true or empty, skip the full
        // solve+deferred-validation pipeline. This handles formulas where
        // mk_select constant-folding + PropagateValues eliminates all content
        // (e.g., select(store(a,0,42),0)=42 becomes (= x 42) after term
        // construction, then PropagateValues substitutes x->42 leaving true).
        // Going through with_deferred_postprocessing would restore original
        // assertions for model validation, but the model lacks values for
        // PropagateValues-eliminated variables, causing false Unknown.
        //
        // #7890: Skip the fast path if VariableSubstitution produced
        // substitutions. Original assertions reference substituted variables
        // (e.g., (= x 10)) but the fast path returns without building a model,
        // so outer validation has no value for x. Fall through to the normal
        // solve path which handles model recovery via
        // recover_substituted_lia_values.
        if var_subst.substitutions().is_empty() {
            let true_term = self.ctx.terms.true_term();
            if preprocessed_assertions.is_empty()
                || preprocessed_assertions.iter().all(|&a| a == true_term)
            {
                self.last_model = None;
                self.last_model_validated = true;
                return Ok(SolveResult::Sat);
            }
        }

        let post_preprocess_features =
            crate::features::StaticFeatures::collect(&self.ctx.terms, &preprocessed_assertions);
        if post_preprocess_features.has_int_div_mod {
            if let Some(result) = self.try_unsat_via_mod_free_subset(&preprocessed_assertions)? {
                return Ok(result);
            }
            if let Some(result) = self.try_sat_via_mod_free_or_branch()? {
                return Ok(result);
            }
            if let Some(result) = self.try_unsat_via_quantifier_consumer_completion_preprocess()? {
                return Ok(result);
            }
            // #symbolic-mod-uf-empty-model — LAST RESORT, on the bail only.
            //
            // Everything above has declined and the next statement publishes
            // `unknown (unsupported arithmetic)`. A symbolic-divisor window is
            // decidable, just not on this route: `preprocess_auflia_*` runs only
            // `eliminate_int_mod_div_by_constant`, whereas `solve_uf_nia` runs
            // `eliminate_int_mod_div` with `symbolic_divisors = true` — the
            // guarded Euclidean axioms, exact SMT-LIB with `d = 0` left
            // unconstrained — and extracts a real EUF+LIA model. `solve_uf_lia`
            // already routes this case to NIA; AUFLIA simply lacked the branch.
            // Measured on the byte-identical formula under `(set-logic
            // QF_UFNIA)`: `sat` with full `f`/`g` interpretations and
            // `:model_check_gate.result "confirmed-sat"`.
            //
            // PLACED HERE, AFTER EVERY RUNG, ON PURPOSE. Re-routing earlier
            // pre-empts `try_unsat_via_mod_free_subset`, which is what refutes
            // `(> d 0) /\ (= (f k2) (mod (g k2) d)) /\ (>= (f k2) d)` by
            // injecting the remainder bound axioms. Losing that would turn a
            // correct `unsat` into a `sat` — a wrong answer, not a slower one.
            // Reaching this point means the alternative is `unknown`, so the
            // only verdicts at risk are ones nothing else could produce.
            //
            // THEORY GUARD IS LOAD-BEARING. `solve_uf_nia` carries EUF+NIA and
            // NOTHING else, while `solve_auf_lia` is reachable with arrays,
            // reals, BV, strings, Seq and FP. Handing it any of those would let
            // them be abstracted to opaque literals — a wrong-SAT mechanism. So
            // the guard is `has_only_uf_lia_theories` in every dimension EXCEPT
            // the div/mod flag that sent us here; `!has_arrays` alone is not
            // enough (a sibling attempt guarded that way and its probe fired
            // with `strings` and `bv` live).
            //
            // SAT ONLY. An `unsat` from this lane would be a NEW refutation
            // resting on the symbolic division axioms; that deserves its own
            // measured campaign, so it falls through to today's `unknown`.
            // The `Sat` still faces the unmodified mandatory gate.
            let nia_routable = !post_preprocess_features.has_arrays
                && !post_preprocess_features.has_real
                && !post_preprocess_features.has_bv
                && !post_preprocess_features.has_strings
                && !post_preprocess_features.has_seq_ops
                && !post_preprocess_features.has_fpa
                && !original_features.has_arrays;
            if nia_routable
                && self.mod_div_or_branch_rescue_depth == 0
                && crate::executor::mod_div_elim::contains_symbolic_int_mod_div(
                    &self.ctx.terms,
                    &preprocessed_assertions,
                )
            {
                let saved_assertions = self.ctx.assertions.clone();
                let saved_model = self.last_model.clone();
                let saved_model_validated = self.last_model_validated;
                let saved_unknown_reason = self.last_unknown_reason;
                let saved_result = self.last_result.clone();
                self.mod_div_or_branch_rescue_depth += 1;
                let nia = self.solve_uf_nia();
                self.mod_div_or_branch_rescue_depth -= 1;
                if matches!(nia, Ok(ref r) if r.is_sat()) {
                    return Ok(SolveResult::Sat);
                }
                self.ctx.assertions = saved_assertions;
                self.last_model = saved_model;
                self.last_model_validated = saved_model_validated;
                self.last_unknown_reason = saved_unknown_reason;
                self.last_result = saved_result;
            }
            self.record_arithmetic_unsupported_fragment_diagnostics();
            self.last_unknown_reason = Some(UnknownReason::UnsupportedArithmetic);
            return Ok(SolveResult::Unknown);
        }

        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        // #6367: Persistent per-pair rescue counter. Owned by the pipeline
        // state so it survives TheoryCombiner recreations across outer
        // refinement iterations (see RescuePairCounter doc).
        let rescue_pair_counter: crate::executor::theories::split_incremental::SharedRescuePairCounter =
            std::sync::Arc::new(std::sync::Mutex::new(
                crate::executor::theories::split_incremental::RescuePairCounter::new(),
            ));
        let rescue_pair_counter_for_theory = rescue_pair_counter;
        // #8785/#8594: AUFLIA uses the lazy split loop, which still creates a
        // fresh TheoryCombiner after each model-equality refinement. Carry the
        // array solver's request dedup sets across those fresh instances, just
        // as the ArrayEUF path does, so repeated outer rounds do not reopen an
        // identical array model/interface equality obligation.
        let mut persistent_array_interface_eqs: ay_core::kani_compat::DetHashSet<(TermId, TermId)> =
            ay_core::kani_compat::DetHashSet::default();
        let mut persistent_array_model_eqs: ay_core::kani_compat::DetHashSet<(TermId, TermId)> =
            ay_core::kani_compat::DetHashSet::default();
        let mut persistent_array_exact_select_model_eqs: ay_core::kani_compat::DetHashSet<
            ExactSelectModelEqKey,
        > = ay_core::kani_compat::DetHashSet::default();
        let mut persistent_euf_array_notify_edges = EufArrayNotifyReplayState::default();
        let mut persistent_array_equality_replays: Vec<ArrayPropagatedEqualityReplay> = Vec::new();
        let mut persistent_cross_theory_equality_replays: Vec<CrossTheoryEqualityReplay> =
            Vec::new();
        #[cfg(debug_assertions)]
        let mut a2_shadow_engaged_rounds: u64 = 0;
        #[cfg(debug_assertions)]
        let mut a2_shadow_skipped_rounds: u64 = 0;
        #[cfg(debug_assertions)]
        let mut a2_shadow_verdict_disagree: u64 = 0;
        #[cfg(debug_assertions)]
        let mut a2_shadow_verdict_kind_differ: u64 = 0;
        #[cfg(debug_assertions)]
        let mut a2_shadow_reasonset_disagree: u64 = 0;
        #[cfg(debug_assertions)]
        let mut a2_shadow_warm_resets: u64 = 0;
        #[cfg(debug_assertions)]
        let mut a2_shadow_first_divergence: Option<String> = None;
        let result =
            self.with_deferred_postprocessing(preprocessed_assertions, proof_provenance, |this| {
                this.configure_sat_search_tuning(100.0, 1.5, 0.02);
                // M-A2 SHADOW setup (debug-only). The persistent combiner borrows
                // stores OWNED BY A STABLE ARENA, NEVER `this.ctx.terms`, so it
                // cannot conflict with the loop's `&mut this.ctx.terms` reborrows
                // and cannot perturb any authoritative state. Each engaged round
                // the shadow re-clones the CURRENT (append-only) `ctx.terms` into
                // the arena and `rebind_terms` the live combiner onto that
                // superset clone (see `a2_shadow_run_round`) — so the persistent
                // combiner now FOLLOWS the terms the fresh path mints and engages
                // EVERY round, exercising a real `soft_reset_warm` each time. This
                // resolves the executor-borrow blocker that previously froze the
                // shadow to a loop-start snapshot (round-0-only engagement).
                //
                // The arena is declared BEFORE the combiner so it outlives it
                // (drop = reverse declaration order); the combiner's `&'arena`
                // handle stays valid across the whole split loop.
                #[cfg(debug_assertions)]
                let a2_shadow_armed = this.auflia_persistent_shadow_active();
                #[cfg(debug_assertions)]
                let a2_shadow_arena = ay_lra::ShadowTermStoreArena::new();
                #[cfg(debug_assertions)]
                let a2_shadow_interrupt = this.solve_interrupt.clone();
                #[cfg(debug_assertions)]
                let a2_shadow_deadline = this.solve_deadline.get();
                // Private rescue counter — NEVER the authoritative shared one, so
                // the shadow cannot influence the fresh path's rescue budget.
                #[cfg(debug_assertions)]
                let a2_shadow_rescue_counter: crate::executor::theories::split_incremental::SharedRescuePairCounter =
                    std::sync::Arc::new(std::sync::Mutex::new(
                        crate::executor::theories::split_incremental::RescuePairCounter::new(),
                    ));
                // The create-once persistent combiner (None until first engaged
                // round; warm-reset every engaged round thereafter).
                #[cfg(debug_assertions)]
                let mut a2_shadow_combiner: Option<TheoryCombiner<'_>> = None;
                solve_incremental_split_loop_pipeline!(this,
                    tag: "AUFLIA",
                    persistent_sat_field: persistent_sat,
                    create_theory: {
                        let mut tc = TheoryCombiner::auf_lia(&this.ctx.terms);
                        tc.set_interrupt(this.solve_interrupt.clone());
                        tc.set_deadline(this.solve_deadline.get());
                        tc.set_rescue_pair_counter(Some(rescue_pair_counter_for_theory.clone()));
                        // #read-congruence-quantified-scope (#7956 tseitin
                        // regression): inside the quantifier pipeline the
                        // store-carrying read-congruence pair obligations send
                        // the ground search wandering; disable them there.
                        tc.set_read_congruence_pairs_enabled(!this.quantifier_pipeline_engaged);
                        // Enable the D0 datatype clash/acyclicity final-check
                        // pass for datatype-bearing problems (no-op otherwise;
                        // stage-4 review F1).
                        let dt_info: Vec<(String, Vec<String>)> = this
                            .ctx
                            .datatype_iter()
                            .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
                            .collect();
                        tc.register_datatypes(&dt_info);
                        tc
                    },
                    extract_models: |theory| {
                        let mut model_roots: Vec<TermId> = this
                            .ctx
                            .assertions
                            .iter()
                            .copied()
                            // Preprocessing can eliminate the original fact
                            // that supplies a model anchor or protects a
                            // disequality-constrained tableau value.
                            .chain(original_assertions.iter().copied())
                            .collect();
                        model_roots.sort_by_key(|term| term.index());
                        model_roots.dedup();
                        theory.scope_euf_model_to_roots(&model_roots);
                        // #A1/#8373: run model recovery + reconciliation BEFORE
                        // LIA values are merged into the EUF term-value map and
                        // before the array model is extracted, so array
                        // interpretation index/value strings reflect the FINAL
                        // variable assignment.
                        let _fixup_protected =
                            collect_active_arith_diseq_vars(&this.ctx.terms, model_roots.iter().copied());
                        let _fixup_assertions = original_assertions.clone();
                        let (euf, arr, lia) =
                            theory.extract_all_models_auflia_with_lia_fixup(
                                &model_roots,
                                |terms, euf_model, lia| {
                                    let _bf_assertions = _fixup_assertions.clone();
                                    let Some(model) = lia.as_mut() else { return };
                                    let dbg_fix = ay_core::misc_cli_flags().debug_fixup;
                                    if dbg_fix {
                                        eprintln!(
                                            "[fixup-dbg] main pre: t12={:?} t13={:?}",
                                            model.values.get(&TermId(14)),
                                            model.values.get(&TermId(15))
                                        );
                                    }
                                    // Recover direct ORIGINAL equalities before
                                    // substitution replay. In particular,
                                    // `x = 5` first pins an eliminated `x`, then
                                    // `x = default(a)` transfers that exact value
                                    // to the opaque array observation. Replaying
                                    // `x -> default(a)` only after both steps
                                    // prevents the generic unconstrained-leaf
                                    // fallback from seeding a conflicting zero.
                                    super::lia::recover_lia_equalities_from_assertions(
                                        terms, &_bf_assertions, model,
                                    );
                                    super::lia::backfill_opaque_app_values_from_equalities(
                                        terms, &_bf_assertions, model,
                                    );
                                    // #7890: Recover substituted Int values
                                    // eliminated by VariableSubstitution during
                                    // AUFLIA preprocessing; diseq-fact vars keep
                                    // their tableau values
                                    // (#qf-auflia-subst-clobber).
                                    super::lia::recover_substituted_lia_values_protecting(
                                        terms, &var_subst, model, &_fixup_protected,
                                    );
                                    if dbg_fix {
                                        eprintln!(
                                            "[fixup-dbg] main post-recover: t12={:?} t13={:?}",
                                            model.values.get(&TermId(14)),
                                            model.values.get(&TermId(15))
                                        );
                                    }
                                    // #A1: Recompute Int composites that the EUF
                                    // model covered with speculative class values
                                    // (array store/select index terms), then
                                    // restore read congruence among opaque select
                                    // terms (pre- vs post-substitution forms of
                                    // the same array read). FIXPOINT (mirrors the
                                    // read-pin repair in validation/pipeline.rs):
                                    // `reconcile` can move an opaque select's
                                    // value AFTER `recover` already derived a
                                    // substituted var from it (A1 chain shape:
                                    // `H := eval(select Q G)` ran before the
                                    // congruence pass pulled the solved-form read
                                    // value onto that select, leaving H stale and
                                    // the candidate self-refuting). Iterate until
                                    // stable (bounded).
                                    let composite_candidates: Vec<TermId> =
                                        euf_model.term_values.keys().copied().collect();
                                    for _ in 0..4 {
                                        let before_iter = model.values.clone();
                                        super::lia::recompute_composite_int_values(
                                            terms, &composite_candidates, model,
                                        );
                                        super::lia::reconcile_lia_select_congruence(
                                            terms, &var_subst, model, Some(euf_model),
                                        );
                                        super::lia::recover_substituted_lia_values_protecting(
                                            terms, &var_subst, model, &_fixup_protected,
                                        );
                                        if model.values == before_iter {
                                            break;
                                        }
                                    }
                                },
                            );
                        theory.clear_euf_model_scope();
                        TheoryModels {
                            euf: Some(euf),
                            array: Some(arr),
                            lia,
                            ..TheoryModels::default()
                        }
                    },
                    max_splits: MAX_SPLITS_LIA,
                    pre_theory_import: |theory, lc, hc, ds| {
                        theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                        theory.import_dioph_state(std::mem::take(ds));
                        theory.import_array_requested_interface_eqs(&persistent_array_interface_eqs);
                        theory.import_array_requested_model_eqs(&persistent_array_model_eqs);
                        theory.import_array_exact_select_model_eq_keys(
                            &persistent_array_exact_select_model_eqs,
                        );
                        theory.import_array_equality_replays(&persistent_array_equality_replays);
                        theory.import_cross_theory_equality_replays(
                            &persistent_cross_theory_equality_replays,
                        );
                        theory.import_euf_array_notify_replay_state(
                            &persistent_euf_array_notify_edges,
                        );
                    },
                    post_theory_export: |theory| {
                        persistent_array_interface_eqs =
                            theory.export_array_requested_interface_eqs();
                        persistent_array_model_eqs = theory.export_array_requested_model_eqs();
                        persistent_array_exact_select_model_eqs =
                            theory.export_array_exact_select_model_eq_keys();
                        theory.prune_current_euf_array_notify_replay_edges(
                            &mut persistent_euf_array_notify_edges,
                        );
                        theory.prune_current_array_equality_replays(
                            &mut persistent_array_equality_replays,
                        );
                        theory.prune_current_cross_theory_equality_replays(
                            &mut persistent_cross_theory_equality_replays,
                        );
                        theory.append_current_euf_array_notify_replay_edges(
                            &mut persistent_euf_array_notify_edges,
                        );
                        theory.append_current_array_equality_replays(
                            &mut persistent_array_equality_replays,
                        );
                        theory
                            .append_current_cross_theory_equality_replays(
                                &mut persistent_cross_theory_equality_replays,
                            );
                        let (lc, hc) = theory
                            .take_learned_state()
                            .unwrap_or_else(|| (Vec::new(), empty_hash_set()));
                        let ds = theory.take_dioph_state().unwrap_or_default();
                        (lc, hc, ds)
                    },
                    // #6846: Use lazy path for AUFLIA. The eager extension drops
                    // theory conflicts when model equality terms lack SAT variable
                    // mappings (_ext_partial > 0), causing Unknown on formulas that
                    // need N-O model equalities (add5, add6, read7).
                    pre_iter_check: |_s| {
                        solve_interrupt
                            .as_ref()
                            .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                            || solve_deadline.expired()
                    },
                    per_round_shadow: |shadow_result, shadow_lits, shadow_atoms, shadow_lemmas| {
                        if a2_shadow_armed {
                            a2_shadow_run_round(
                                &a2_shadow_arena,
                                &this.ctx.terms,
                                &mut a2_shadow_combiner,
                                &a2_shadow_interrupt,
                                a2_shadow_deadline,
                                &a2_shadow_rescue_counter,
                                shadow_result,
                                shadow_lits,
                                shadow_atoms,
                                shadow_lemmas,
                                &mut a2_shadow_engaged_rounds,
                                &mut a2_shadow_skipped_rounds,
                                &mut a2_shadow_warm_resets,
                                &mut a2_shadow_verdict_disagree,
                                &mut a2_shadow_verdict_kind_differ,
                                &mut a2_shadow_reasonset_disagree,
                                &mut a2_shadow_first_divergence,
                            );
                        }
                    }
                )
            });

        #[cfg(debug_assertions)]
        {
            self.last_statistics
                .set_int("auflia.shadow.engaged_rounds", a2_shadow_engaged_rounds);
            self.last_statistics
                .set_int("auflia.shadow.skipped_rounds", a2_shadow_skipped_rounds);
            self.last_statistics
                .set_int("auflia.shadow.warm_resets", a2_shadow_warm_resets);
            self.last_statistics
                .set_int("auflia.shadow.verdict_disagree", a2_shadow_verdict_disagree);
            self.last_statistics.set_int(
                "auflia.shadow.verdict_kind_differ",
                a2_shadow_verdict_kind_differ,
            );
            self.last_statistics.set_int(
                "auflia.shadow.reasonset_disagree",
                a2_shadow_reasonset_disagree,
            );
            if let Some(divergence) = &a2_shadow_first_divergence {
                self.last_statistics
                    .set_string("auflia.shadow.first_divergence", divergence.clone());
            }
        }

        // #7890: Recover Bool variables eliminated by VariableSubstitution.
        // E.g., (= p (> x 0)) substitutes p -> (> x 0); the SAT model has no
        // assignment for p, so model validation of the original assertion
        // fails. Evaluate the substitution RHS against the recovered LIA
        // model to compute p's Bool value. Mirrors the LIA path
        // (solve_lia_incremental).
        if matches!(result, Ok(SolveResult::Sat)) && !var_subst.substitutions().is_empty() {
            if let Some(ref full_model) = self.last_model {
                let lia_values = full_model
                    .lia_model
                    .as_ref()
                    .map(|m| &m.values)
                    .cloned()
                    .unwrap_or_default();
                let bool_overrides = super::lia::recover_substituted_bool_values(
                    &self.ctx.terms,
                    &var_subst,
                    &lia_values,
                );
                if !bool_overrides.is_empty() {
                    if let Some(ref mut full_model) = self.last_model {
                        full_model.bool_overrides.extend(bool_overrides);
                    }
                }
            }
        }

        result
    }

    /// Solve using combined Arrays + EUF + LIA theory with assumptions.
    ///
    /// This is the assumption-based version of [`Self::solve_auf_lia`], enabling
    /// `check-sat-assuming` for DT+arithmetic formulas that require integer splits.
    /// Fixes #1771: check-sat-assuming now handles NeedSplit like regular check-sat.
    ///
    /// # Arguments
    /// * `assertions` - Base assertions (including DT axioms)
    /// * `assumptions` - Assumption terms to activate
    ///
    /// # Returns
    /// * `SolveResult::Sat` - satisfiable under assumptions
    /// * `SolveResult::Unsat` - unsatisfiable (core stored in `last_assumption_core`)
    /// * `SolveResult::Unknown` - could not determine (e.g., split limit reached)
    pub(in crate::executor) fn solve_auf_lia_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // Preprocess assertions and assumptions through the full LIA normalization
        // family: variable substitution, SOM, ITE lifting, mod/div elimination (#6737).
        let artifacts = self.preprocess_mixed_arith_assumptions(assertions, assumptions);
        // #array-deadline-forward phase-boundary poll: the ITE-lifting pass
        // above runs through ay-core term rewriting that polls no deadline
        // (measured 10+s on QF_AX swap shapes). Honor an expired budget at
        // the phase boundary instead of paying the (also unpolled) eager
        // array-axiom fixpoint + encode next.
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let var_subst = artifacts.var_subst;
        let final_assumptions = artifacts.assumptions;

        // Preserve original assertions for fill-only equality recovery on SAT.
        let original_assertions: Vec<TermId> = assertions.to_vec();
        let original_problem_assertions = original_assertions.clone();
        let mut original_model_equalities = original_assertions.clone();
        original_model_equalities.extend_from_slice(assumptions);

        // Eager array axioms for soundness (#4304, #5086, #6282).
        // Include assumption terms in the reachable set so assumption-only
        // array operations get axioms in incremental mode (#6736).
        let assumption_terms: Vec<TermId> = final_assumptions.iter().map(|(t, _)| *t).collect();
        let mut final_assertions = artifacts.assertions;
        {
            // Run the legacy fixpoint on the exact preprocessed window it will
            // feed to the solver, not on the authored context prefix. Activate
            // finite coverage first so generic Skolem extensionality can skip
            // only equalities that genuinely have a live exact biconditional.
            // The authored assertion vector is restored byte-for-byte below.
            let saved_assertions = std::mem::replace(&mut self.ctx.assertions, final_assertions);
            let _ = self.add_finite_index_array_closure_with_roots(&assumption_terms);
            let axiom_start = self.ctx.assertions.len();
            self.run_array_axiom_full_fixpoint_at_with_roots(axiom_start, &assumption_terms);
            let generated_axioms: Vec<_> = self.ctx.assertions.drain(axiom_start..).collect();
            final_assertions = std::mem::replace(&mut self.ctx.assertions, saved_assertions);
            let generated_axioms = self.ctx.terms.expand_select_store_all(&generated_axioms);
            final_assertions.extend(generated_axioms);
        }
        // Final boundary after ROW/fixpoint synthesis and select-store
        // expansion. This reuses the active pre-fixpoint axioms without
        // recharging them and closes any newly exposed array-valued cells.
        final_assertions =
            self.close_finite_arrays_in_owned_assertion_window(final_assertions, &assumption_terms);
        // #array-deadline-forward phase-boundary poll (see above): the eager
        // array-axiom fixpoint can be dense on deep store chains.
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        let proof_provenance = ProofProblemAssertionProvenance::from_sources(
            original_problem_assertions,
            &final_assertions,
            artifacts.assertion_sources,
        );

        // Use isolated incremental state with the new incremental assumption
        // split-loop macro (#6689 Packet 4). The persistent SAT solver keeps
        // learned clauses + LIA state across split iterations directly — no
        // manual preservation needed.
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        // #6367: Persistent per-pair rescue counter (see solve_auf_lia).
        let rescue_pair_counter: crate::executor::theories::split_incremental::SharedRescuePairCounter =
            std::sync::Arc::new(std::sync::Mutex::new(
                crate::executor::theories::split_incremental::RescuePairCounter::new(),
            ));
        let rescue_pair_counter_for_theory = rescue_pair_counter;
        self.with_deferred_postprocessing(final_assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.5, 0.02);
            solve_incremental_assume_split_loop_pipeline!(this,
                tag: "AUFLIA-ASSUME",
                persistent_sat_field: persistent_sat,
                assumptions: &final_assumptions,
                create_theory: {
                    let mut tc = TheoryCombiner::auf_lia(&this.ctx.terms);
                    tc.set_interrupt(this.solve_interrupt.clone());
                    tc.set_deadline(this.solve_deadline.get());
                    tc.set_rescue_pair_counter(Some(rescue_pair_counter_for_theory.clone()));
                    // #read-congruence-quantified-scope: see solve_auf_lia.
                    tc.set_read_congruence_pairs_enabled(!this.quantifier_pipeline_engaged);
                    // Enable the D0 datatype clash/acyclicity final-check pass
                    // for datatype-bearing problems (no-op otherwise; stage-4
                    // review F1).
                    let dt_info: Vec<(String, Vec<String>)> = this
                        .ctx
                        .datatype_iter()
                        .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
                        .collect();
                    tc.register_datatypes(&dt_info);
                    tc
                },
                extract_models: |theory| {
                    let mut model_roots: Vec<TermId> = this
                        .ctx
                        .assertions
                        .iter()
                        .copied()
                        .chain(final_assumptions.iter().map(|(term, _)| *term))
                        // `with_deferred_postprocessing` installs the
                        // preprocessed assertion window in `ctx.assertions`;
                        // retain eliminated original base facts as model roots
                        // just as we retain original assumptions below.
                        .chain(original_assertions.iter().copied())
                        // Keep original assumption roots too: preprocessing may
                        // rewrite/eliminate the very disequality whose tableau
                        // value must remain authoritative during class reunify.
                        .chain(assumptions.iter().copied())
                        .collect();
                    model_roots.sort_by_key(|term| term.index());
                    model_roots.dedup();
                    theory.scope_euf_model_to_roots(&model_roots);
                    // #A1/#8373: recovery + reconciliation run BEFORE the LIA
                    // values are merged into the EUF term-value map and before
                    // array model extraction (see the check-sat variant above).
                    let _fixup_protected = collect_active_arith_diseq_vars(
                        &this.ctx.terms,
                        model_roots.iter().copied(),
                    );
                    let (euf, arr, lia) = theory.extract_all_models_auflia_with_lia_fixup(
                        &model_roots,
                        |terms, euf_model, lia| {
                            let Some(model) = lia.as_mut() else { return };
                            let dbg_fix = ay_core::misc_cli_flags().debug_fixup;
                            let dump = |model: &LiaModel, tag: &str| {
                                if dbg_fix {
                                    eprintln!(
                                        "[fixup-dbg] {tag}: t12={:?} t13={:?}",
                                        model.values.get(&TermId(14)),
                                        model.values.get(&TermId(15))
                                    );
                                }
                            };
                            dump(model, "pre");
                            // Match the check-sat recovery order: exact original
                            // equalities first, then transfer a variable value
                            // onto its opaque select/default partner, and only
                            // then replay substitutions. Include assumptions so
                            // assumption-only pins are not lost.
                            super::lia::recover_lia_equalities_from_assertions(
                                terms, &original_model_equalities, model,
                            );
                            super::lia::backfill_opaque_app_values_from_equalities(
                                terms,
                                &original_model_equalities,
                                model,
                            );
                            super::lia::recover_substituted_lia_values_protecting(
                                terms, &var_subst, model, &_fixup_protected,
                            );
                            dump(model, "post-recover-subst");
                            // FIXPOINT over recompute/reconcile/recover — see
                            // the check-sat variant above (#A1 chain shape).
                            let composite_candidates: Vec<TermId> =
                                euf_model.term_values.keys().copied().collect();
                            for _ in 0..4 {
                                let before_iter = model.values.clone();
                                super::lia::recompute_composite_int_values(
                                    terms, &composite_candidates, model,
                                );
                                super::lia::reconcile_lia_select_congruence(
                                    terms, &var_subst, model, Some(euf_model),
                                );
                                super::lia::recover_substituted_lia_values_protecting(
                                    terms, &var_subst, model, &_fixup_protected,
                                );
                                if model.values == before_iter {
                                    break;
                                }
                            }
                            dump(model, "final");
                        },
                    );
                    theory.clear_euf_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        lia,
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LIA,
                pre_theory_import: |theory, lc, hc, ds| {
                    theory.import_learned_state(std::mem::take(lc), std::mem::take(hc));
                    theory.import_dioph_state(std::mem::take(ds));
                },
                post_theory_export: |theory| {
                    let (lc, hc) = theory
                        .take_learned_state()
                        .unwrap_or_else(|| (Vec::new(), empty_hash_set()));
                    let ds = theory.take_dioph_state().unwrap_or_default();
                    (lc, hc, ds)
                },
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                }
            )
        })
    }

    /// Solve using combined Arrays + EUF + LRA theory with disequality split support (#6129).
    ///
    /// Uses the incremental split-loop pipeline so `NeedDisequalitySplit` from LRA
    /// disequalities can be handled via SAT-level case splits while reusing
    /// incremental SAT state across iterations.
    pub(in crate::executor) fn solve_auf_lra(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        // NOTE: expand_select_store is NOT applied here because solve_auf_lra
        // does not have ITE lifting. The ITEs from expansion would not be properly
        // handled by the Tseitin encoder without lifting. See solve_auf_lia for
        // the full AUFLIA pipeline with expansion + ITE lifting (#6282).

        // Eager array axioms for AUFLRA (#4304, #5086, #6282).
        // Unlike AUFLIA, AUFLRA keeps eager ROW because the lazy ArraySolver
        // cannot derive index disequalities that require LRA reasoning
        // (e.g., y = x + 0.5 ⇒ x ≠ y). The eager ROW encoding puts the
        // disjunction (i = j ∨ ROW2-consequence) into SAT where LRA resolves it.
        //
        // Drain generated axioms to prevent phantom accumulation in push/pop (#6733).
        let original_assertions = self.ctx.assertions.clone();
        // AUFLRA has no destructive array preprocessing before this point, so
        // activate exact coverage directly on the route-owned authored window
        // before generic extensionality. A second closure below covers every
        // equality synthesized by the fixpoint.
        let _ = self.add_finite_index_array_closure();
        let axiom_start = self.ctx.assertions.len();
        self.run_array_axiom_full_fixpoint();
        // The full fixpoint runs with dedup_protect = 0 (it deduplicates the
        // WHOLE assertion vector), so the vector can come back SHORTER than
        // the pre-fixpoint watermark — clamp before draining or the range
        // panics (pre-existing crash on e.g. AUFLIRA `forall ((x Real)) ...`
        // inputs routed here; the CLI masked it as a caught-panic `unknown`).
        // When clamped, `generated_axioms` is empty and every surviving
        // assertion stays in place for the solve below — nothing is lost.
        let axiom_start = axiom_start.min(self.ctx.assertions.len());
        let generated_axioms: Vec<_> = self.ctx.assertions.drain(axiom_start..).collect();

        let mut assertions = self.ctx.assertions.clone();
        assertions.extend(generated_axioms);
        let assertions = self.close_finite_arrays_in_owned_assertion_window(assertions, &[]);
        let proof_provenance =
            ProofProblemAssertionProvenance::passthrough(&original_assertions, &assertions);
        let solve_interrupt = self.solve_interrupt.clone();
        let solve_deadline = self.solve_deadline.clone();
        // #6367: Persistent per-pair rescue counter (see solve_auf_lia).
        let rescue_pair_counter: crate::executor::theories::split_incremental::SharedRescuePairCounter =
            std::sync::Arc::new(std::sync::Mutex::new(
                crate::executor::theories::split_incremental::RescuePairCounter::new(),
            ));
        let rescue_pair_counter_for_theory = rescue_pair_counter;
        self.with_deferred_postprocessing(assertions, proof_provenance, |this| {
            this.configure_sat_search_tuning(100.0, 1.1, 0.01);
            solve_incremental_split_loop_pipeline!(this,
                tag: "AUFLRA",
                persistent_sat_field: persistent_sat,
                create_theory: {
                    let mut tc = TheoryCombiner::auf_lra(&this.ctx.terms);
                    tc.set_interrupt(this.solve_interrupt.clone());
                    tc.set_deadline(this.solve_deadline.get());
                    tc.set_rescue_pair_counter(Some(rescue_pair_counter_for_theory.clone()));
                    // Enable the D0 datatype clash/acyclicity final-check pass
                    // for datatype-bearing problems (no-op otherwise; stage-4
                    // review F1).
                    let dt_info: Vec<(String, Vec<String>)> = this
                        .ctx
                        .datatype_iter()
                        .map(|(name, ctors)| (name.to_owned(), ctors.to_vec()))
                        .collect();
                    tc.register_datatypes(&dt_info);
                    tc
                },
                extract_models: |theory| {
                    theory.scope_euf_model_to_roots(&this.ctx.assertions);
                    let (euf, arr, lra) = theory.extract_all_models_auflra();
                    theory.clear_euf_model_scope();
                    TheoryModels {
                        euf: Some(euf),
                        array: Some(arr),
                        lra: Some(lra),
                        ..TheoryModels::default()
                    }
                },
                max_splits: MAX_SPLITS_LRA,
                pre_theory_import: |_theory, _lc, _hc, _ds| {},
                post_theory_export: |_theory| {
                    (Vec::new(), empty_hash_set(), ay_lia::DiophState::default())
                },
                pre_iter_check: |_s| {
                    solve_interrupt
                        .as_ref()
                        .is_some_and(|flag| flag.load(std::sync::atomic::Ordering::Relaxed))
                        || solve_deadline.expired()
                }
            )
        })
    }

    /// Solve mixed BV + LIA formulas where the two theories are independent (#5356).
    ///
    /// Strategy: try the BV solver first (which handles `extract`, `concat`, etc.
    /// via eager bit-blasting). If it returns UNSAT, the result is correct (BV
    /// constraints alone are contradictory). If it returns SAT, cross-check with
    /// AUFLIA to verify integer arithmetic constraints (#7077). The BV solver
    /// ignores integer arithmetic semantics, so a BV-SAT model may violate
    /// integer constraints (e.g., `1 + size(t) <= size(t)`).
    ///
    /// Cross-check logic on BV-SAT:
    /// - AUFLIA-UNSAT => return UNSAT (Int constraints violated, #7077)
    /// - AUFLIA-SAT => return SAT (both theories agree)
    /// - AUFLIA-Unknown => return SAT (BV model validated; AUFLIA is incomplete
    ///   for BV operations like extract/concat, #5356)
    pub(in crate::executor) fn solve_bv_lia_indep(&mut self) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        if self.active_assertions_contain_symbolic_int_div_mod() {
            self.record_arithmetic_unsupported_fragment_diagnostics();
            self.last_unknown_reason = Some(UnknownReason::UnsupportedArithmetic);
            self.last_result = Some(SolveResult::Unknown);
            return Ok(SolveResult::Unknown);
        }
        use crate::executor::theories::bv::BvSolveConfig;
        use crate::executor_types::ExecutorError;

        // Try BV solver first — it can evaluate extract/concat/etc.
        let bv_result = match self.solve_bv_core(BvSolveConfig::qf_bv(), &[]) {
            Ok(result) => result,
            Err(ExecutorError::ModelValidation(_)) => {
                // BV found SAT but model validation failed (Int constraints violated
                // by the BV model). Cross-check with AUFLIA:
                // - AUFLIA-UNSAT: Int constraints are contradictory → UNSAT (#7077)
                // - AUFLIA-SAT: both theories agree → SAT
                // - AUFLIA-Unknown: AUFLIA can't decide (incomplete for BV ops like
                //   extract/concat) → trust BV-SAT since BV ops were satisfied (#5356)
                return match self.solve_auf_lia()? {
                    SolveResult::Unsat(proof) => Ok(SolveResult::Unsat(proof)),
                    SolveResult::Sat => Ok(SolveResult::Sat),
                    SolveResult::Unknown => {
                        if self.last_unknown_is_unsupported_arithmetic() {
                            return Ok(SolveResult::Unknown);
                        }
                        // AUFLIA can't decide — trust BV-SAT. Skip model eval since
                        // the BV model failed Int validation and AUFLIA has no model.
                        // Boolean skeleton check in finalize_sat_model_validation will
                        // still verify SAT-level consistency (#7912).
                        self.skip_model_eval = true;
                        Ok(SolveResult::Sat)
                    }
                };
            }
            Err(e) => return Err(e),
        };

        match bv_result {
            SolveResult::Sat => {
                // BV solver found SAT with a validated model. Cross-check with AUFLIA
                // to verify Int constraints (#7077). AUFLIA treats BV terms as
                // uninterpreted, so:
                // - AUFLIA-UNSAT: Int constraints are violated → UNSAT
                // - AUFLIA-SAT: both theories agree → SAT (restore BV model)
                // - AUFLIA-Unknown: AUFLIA can't decide (incomplete for BV ops like
                //   extract/concat) → trust validated BV model (#5356)
                //
                // Save the BV model before calling AUFLIA — AUFLIA overwrites
                // last_model with its own (incomplete for BV terms) (#5356).
                let bv_model = self.last_model.clone();
                let bv_model_validated = self.last_model_validated;
                let auflia_check = self.solve_auf_lia()?;
                match auflia_check {
                    SolveResult::Unsat(proof) => Ok(SolveResult::Unsat(proof)),
                    SolveResult::Sat => {
                        // AUFLIA agrees. Restore the BV model (validated by the
                        // BV solver), grafting the arithmetic components the BV
                        // lane never produces (#bv-lia-indep-model-graft).
                        let roots = self.ctx.assertions.clone();
                        self.restore_indep_bv_model_with_arith_graft(
                            bv_model,
                            bv_model_validated,
                            &roots,
                        );
                        Ok(SolveResult::Sat)
                    }
                    SolveResult::Unknown => {
                        if self.last_unknown_is_unsupported_arithmetic() {
                            Ok(SolveResult::Unknown)
                        } else {
                            // AUFLIA can't decide because of BV operations like
                            // extract/concat. Restore the validated BV model.
                            self.last_model = bv_model;
                            self.last_model_validated = bv_model_validated;
                            Ok(SolveResult::Sat)
                        }
                    }
                }
            }
            SolveResult::Unsat(_) => Ok(SolveResult::unsat()),
            SolveResult::Unknown => {
                // BV solver couldn't decide. Fall back to AUFLIA.
                self.solve_auf_lia()
            }
        }
    }

    fn active_assertions_contain_symbolic_int_div_mod(&self) -> bool {
        self.ctx
            .assertions
            .iter()
            .copied()
            .any(|assertion| self.term_contains_symbolic_int_div_mod(assertion))
    }

    fn term_contains_symbolic_int_div_mod(&self, term: TermId) -> bool {
        match self.ctx.terms.get(term) {
            TermData::Const(_) | TermData::Var(_, _) => false,
            TermData::App(sym, args) => {
                let is_symbolic_int_div_mod = matches!(sym.name(), "div" | "mod" | "rem")
                    && matches!(self.ctx.terms.sort(term), Sort::Int)
                    && args.get(1).is_some_and(|&divisor| {
                        !matches!(
                            self.ctx.terms.get(divisor),
                            TermData::Const(Constant::Int(_))
                        )
                    });
                is_symbolic_int_div_mod
                    || args
                        .iter()
                        .copied()
                        .any(|arg| self.term_contains_symbolic_int_div_mod(arg))
            }
            TermData::Not(inner) => self.term_contains_symbolic_int_div_mod(*inner),
            TermData::Ite(cond, then_term, else_term) => {
                self.term_contains_symbolic_int_div_mod(*cond)
                    || self.term_contains_symbolic_int_div_mod(*then_term)
                    || self.term_contains_symbolic_int_div_mod(*else_term)
            }
            TermData::Let(bindings, body) => {
                bindings
                    .iter()
                    .any(|(_, value)| self.term_contains_symbolic_int_div_mod(*value))
                    || self.term_contains_symbolic_int_div_mod(*body)
            }
            TermData::Forall(_, body, triggers) | TermData::Exists(_, body, triggers) => {
                self.term_contains_symbolic_int_div_mod(*body)
                    || triggers
                        .iter()
                        .flatten()
                        .copied()
                        .any(|trigger| self.term_contains_symbolic_int_div_mod(trigger))
            }
            _ => false,
        }
    }

    /// Assumption-based version of [`solve_bv_lia_indep`] for `check-sat-assuming`.
    pub(in crate::executor) fn solve_bv_lia_indep_with_assumptions(
        &mut self,
        assertions: &[TermId],
        assumptions: &[TermId],
    ) -> Result<SolveResult> {
        if self.should_abort_theory_loop() {
            return Ok(SolveResult::Unknown);
        }
        if assertions
            .iter()
            .chain(assumptions.iter())
            .copied()
            .any(|term| self.term_contains_symbolic_int_div_mod(term))
        {
            self.record_arithmetic_unsupported_fragment_diagnostics();
            self.last_unknown_reason = Some(UnknownReason::UnsupportedArithmetic);
            self.last_result = Some(SolveResult::Unknown);
            return Ok(SolveResult::Unknown);
        }
        use crate::executor::theories::bv::BvSolveConfig;
        use crate::executor_types::ExecutorError;

        let bv_result = match self.solve_bv_core(BvSolveConfig::qf_bv(), assumptions) {
            Ok(result) => result,
            Err(ExecutorError::ModelValidation(_)) => {
                // BV-SAT with failed model validation. Cross-check with AUFLIA (#7077, #5356).
                return match self.solve_auf_lia_with_assumptions(assertions, assumptions)? {
                    SolveResult::Unsat(proof) => Ok(SolveResult::Unsat(proof)),
                    SolveResult::Sat => Ok(SolveResult::Sat),
                    SolveResult::Unknown => {
                        if self.last_unknown_is_unsupported_arithmetic() {
                            return Ok(SolveResult::Unknown);
                        }
                        self.skip_model_eval = true;
                        Ok(SolveResult::Sat)
                    }
                };
            }
            Err(e) => return Err(e),
        };

        match bv_result {
            SolveResult::Sat => {
                // Cross-check with AUFLIA for Int constraints (#7077).
                // Save BV model before AUFLIA overwrites it.
                let bv_model = self.last_model.clone();
                let bv_model_validated = self.last_model_validated;
                match self.solve_auf_lia_with_assumptions(assertions, assumptions)? {
                    SolveResult::Unsat(proof) => Ok(SolveResult::Unsat(proof)),
                    SolveResult::Sat => {
                        let mut roots = assertions.to_vec();
                        roots.extend_from_slice(assumptions);
                        self.restore_indep_bv_model_with_arith_graft(
                            bv_model,
                            bv_model_validated,
                            &roots,
                        );
                        Ok(SolveResult::Sat)
                    }
                    SolveResult::Unknown => {
                        if self.last_unknown_is_unsupported_arithmetic() {
                            Ok(SolveResult::Unknown)
                        } else {
                            self.last_model = bv_model;
                            self.last_model_validated = bv_model_validated;
                            Ok(SolveResult::Sat)
                        }
                    }
                }
            }
            SolveResult::Unsat(_) => Ok(SolveResult::unsat()),
            SolveResult::Unknown => self.solve_auf_lia_with_assumptions(assertions, assumptions),
        }
    }

    /// Restore the saved BV-lane model after a SAT AUFLIA cross-check, grafting
    /// (FILL-ONLY) the theory components the BV lane never produces from the
    /// AUFLIA model that is currently installed in `last_model`
    /// (#bv-lia-indep-model-graft).
    ///
    /// In the `_BV_LIA_INDEP` category the two lanes solve DISJOINT theory
    /// slices of the same assertion set: the BV lane bitblasts the BitVec
    /// atoms and treats arithmetic atoms as opaque Booleans (its model carries
    /// NO Int/Real assignment), while the AUFLIA lane decides the arithmetic
    /// (its model carries no bit-accurate BV assignment). The old blind
    /// restore kept only the BV model, so a declared Int constant pinned by an
    /// arithmetic assertion (`(= len 3)`) evaluated from the 0-defaulted
    /// completion instead — the final model validation then correctly refuted
    /// the witness and the pipeline fail-closed a genuine SAT to Unknown
    /// (verifier slice/collection VCs: `len == N` frame facts alongside pure-BV
    /// element constraints).
    ///
    /// Fill-only means a component the BV model ALREADY has always wins; the
    /// graft only adds what the BV lane structurally cannot know. Soundness is
    /// unchanged either way: the merged witness still faces the same strict,
    /// fail-closed model validation as before, so a graft that does not fit
    /// (e.g. a cross-theory Boolean-skeleton disagreement between the lanes)
    /// degrades to exactly the previous Unknown — never a wrong verdict. The
    /// merge also invalidates the saved validation evidence (the witness
    /// changed), forcing that re-validation.
    ///
    /// STRICTLY ARITHMETIC-ONLY: the AUFLIA lane's `euf_model`/`array_model`
    /// are NOT grafted even when the BV model lacks those components. The BV
    /// lane carries its array/UF content as term-level bit assignments with
    /// `array_model: None`, so "fill-only at the component level" is not
    /// fill-only at the VALUE level there — a grafted AUFLIA array component
    /// would materialize printed cells from the AUFLIA lane's opaque tokens
    /// while validation evaluates the same reads from the BV lane's term
    /// values, printing a witness inconsistent with the one validated (the
    /// mv-printer/census divergence class). `lia_model`/`lra_model` cannot
    /// collide this way: the BV lane never assigns an Int/Real-sorted term.
    ///
    /// SELF-CHECKED: the two lanes may satisfy a MIXED disjunction through
    /// DIFFERENT branches (`(or (and (= x 0) bv0) (and (= x 1) bv1))` — the
    /// BV lane commits its bits to branch 0, AUFLIA picks x = 1), in which
    /// case the merge is definitively refutable even though each lane's model
    /// is fine. Grafting there would REGRESS a case the old blind restore
    /// solved (the 0-default completion happened to land on the BV lane's
    /// branch). So the merge is kept only when NO root evaluates to a
    /// definite `false` under it; otherwise the old restore runs unchanged.
    /// An undecided (unassigned-leaf) evaluation is not a rejection — the
    /// completion + strict validation passes downstream keep deciding those
    /// exactly as before, fail-closed.
    fn restore_indep_bv_model_with_arith_graft(
        &mut self,
        bv_model: Option<Model>,
        bv_model_validated: bool,
        roots: &[TermId],
    ) {
        let auflia_model = self.last_model.take();
        let mut merged = bv_model.clone();
        let mut grafted = false;
        if let (Some(m), Some(a)) = (merged.as_mut(), auflia_model) {
            if m.lia_model.is_none() && a.lia_model.is_some() {
                m.lia_model = a.lia_model.clone();
                grafted = true;
            }
            if m.lra_model.is_none() && a.lra_model.is_some() {
                m.lra_model = a.lra_model.clone();
                grafted = true;
            }
        }
        if grafted {
            let merged_ref = merged.as_ref().expect("grafted implies a model");
            let refuted = roots.iter().any(|&root| {
                matches!(self.evaluate_term(merged_ref, root), EvalValue::Bool(false))
            });
            if refuted {
                // Cross-lane branch disagreement: keep the old behavior.
                self.last_model = bv_model;
                self.last_model_validated = bv_model_validated;
                return;
            }
        }
        self.last_model = merged;
        // A mutated witness invalidates prior validation evidence; the
        // finalize pass re-validates it fail-closed.
        self.last_model_validated = bv_model_validated && !grafted;
    }
}

#[cfg(test)]
mod nested_row_refutation_state_tests {
    use super::*;
    use ay_core::{ProofStep, TheoryLemmaKind};

    #[test]
    fn discarded_auxiliary_solve_cannot_authorize_outer_sat() {
        let mut exec = Executor::new();
        let array_sort = Sort::array(Sort::Int, Sort::Int);
        let a0 = exec.ctx.terms.mk_var("a0", array_sort.clone());
        let a1 = exec.ctx.terms.mk_var("a1", array_sort);
        let zero = exec.ctx.terms.mk_int(BigInt::from(0));
        let one = exec.ctx.terms.mk_int(BigInt::from(1));
        let stored = exec.ctx.terms.mk_store(a0, zero, one);
        let store_definition = exec.ctx.terms.mk_eq(a1, stored);

        // Symbolic division arms the NIA path's SAT-only validation bypass
        // before the auxiliary outcome is known. This residue is satisfiable,
        // so the probe must discard that authorization with its result.
        let x = exec.ctx.terms.mk_var("x", Sort::Int);
        let y = exec.ctx.terms.mk_var("y", Sort::Int);
        let z = exec.ctx.terms.mk_var("z", Sort::Int);
        let quotient = exec.ctx.terms.mk_intdiv(x, z);
        let div_equality = exec.ctx.terms.mk_eq(quotient, y);
        exec.ctx.assertions = vec![store_definition, div_equality];
        let original_assertions = exec.ctx.assertions.clone();

        exec.proof_tracker.enable();
        let outer_lemma = exec.ctx.terms.mk_var("outer_nested_row_lemma", Sort::Bool);
        exec.proof_tracker
            .add_theory_lemma_with_kind(
                vec![outer_lemma],
                TheoryLemmaKind::ArraySelectStore { index_eq: true },
            )
            .expect("proof tracking is enabled");
        exec.last_unsat_proof_reconstruction_suppressed = true;

        assert!(!exec.sat_validated_by_mod_div_or_branch);
        let result = exec
            .try_ufnia_store_flat_row_refutation()
            .expect("the auxiliary NIA solve should not fail");

        assert!(result.is_none(), "a satisfiable residue must be discarded");
        assert_eq!(exec.ctx.assertions, original_assertions);
        assert!(
            !exec.sat_validated_by_mod_div_or_branch,
            "a discarded private solve must not authorize the outer SAT path"
        );
        assert!(
            exec.last_unsat_proof_reconstruction_suppressed,
            "a discarded private solve must restore the outer proof-authority marker"
        );
        assert_eq!(
            exec.proof_tracker.num_steps(),
            1,
            "a discarded private solve must not drain or extend the outer proof tracker"
        );
        let proof = exec.proof_tracker.take_proof();
        assert!(matches!(
            proof.steps.as_slice(),
            [ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
                ..
            }] if clause == &[outer_lemma]
        ));
    }
}

#[cfg(test)]
mod post_split_verify_tests {
    use super::*;
    use ay_core::{ProofStep, TheoryLemmaKind};

    #[test]
    fn fresh_post_split_verifier_preserves_outer_proof_tracker() {
        let mut exec = Executor::new();
        exec.proof_tracker.enable();
        let outer_lemma = exec.ctx.terms.mk_var("outer_row_lemma", Sort::Bool);
        exec.proof_tracker
            .add_theory_lemma_with_kind(
                vec![outer_lemma],
                TheoryLemmaKind::ArraySelectStore { index_eq: true },
            )
            .expect("proof tracking is enabled");
        let outer_negation = exec.ctx.terms.mk_not(outer_lemma);
        let mut outer_negations = HashMap::default();
        outer_negations.insert(outer_lemma, outer_negation);
        exec.last_negations = Some(outer_negations.clone());
        exec.last_unsat_proof_reconstruction_suppressed = true;
        let contradiction = exec.ctx.terms.false_term();

        assert!(
            exec.verify_post_split_unsat_via_fresh_solve(&[contradiction]),
            "the isolated verification core must re-derive UNSAT"
        );
        assert_eq!(
            exec.proof_tracker.num_steps(),
            1,
            "the nested verifier must not drain the outer proof tracker"
        );
        assert_eq!(
            exec.last_negations,
            Some(outer_negations),
            "the nested verifier must not consume the outer SAT negation map"
        );
        assert!(
            exec.last_unsat_proof_reconstruction_suppressed,
            "the nested verifier must restore the outer proof-authority marker"
        );
        let proof = exec.proof_tracker.take_proof();
        assert!(matches!(
            proof.steps.as_slice(),
            [ProofStep::TheoryLemma {
                clause,
                kind: TheoryLemmaKind::ArraySelectStore { index_eq: true },
                ..
            }] if clause == &[outer_lemma]
        ));
    }
}

#[cfg(test)]
mod bridge_guard_tests {
    //! Direct unit coverage for the BV<->LIA bridge SAT-promotion structural
    //! realizability guard (`all_bitvec_vars_are_bridge_only`). These test the
    //! guard predicate on hand-built term DAGs, independent of solver routing —
    //! the most granular check on the false-SAT hazard: a BitVec variable with
    //! ANY un-bridged occurrence must make the predicate return `false`.
    use super::*;

    fn bv8(terms: &mut TermStore, name: &str) -> TermId {
        terms.mk_var(name, Sort::bitvec(8))
    }

    #[test]
    fn active_disequality_protection_includes_assumption_roots() {
        let mut terms = TermStore::new();
        let x = terms.mk_var("x", Sort::Int);
        let y = terms.mk_var("y", Sort::Int);
        let assumption = terms.mk_distinct(vec![x, y]);

        let protected = collect_active_arith_diseq_vars(&terms, [assumption]);

        assert!(protected.contains(&x));
        assert!(protected.contains(&y));
    }

    /// `(= L (bv2nat k))` — k ONLY under bv2nat: bridge-only.
    #[test]
    fn guard_accepts_bare_companion() {
        let mut t = TermStore::new();
        let k = bv8(&mut t, "k");
        let l = t.mk_var("L", Sort::Int);
        let nat = t.mk_bv2nat(k);
        let eq = t.mk_eq(l, nat);
        assert!(all_bitvec_vars_are_bridge_only(&t, &[eq]));
    }

    /// `(= S (+ (bv2nat k) (bv2nat m)))` — two vars, each only under bv2nat.
    #[test]
    fn guard_accepts_two_bridged_vars() {
        let mut t = TermStore::new();
        let k = bv8(&mut t, "k");
        let m = bv8(&mut t, "m");
        let s = t.mk_var("S", Sort::Int);
        let nk = t.mk_bv2nat(k);
        let nm = t.mk_bv2nat(m);
        let sum = t.mk_add(vec![nk, nm]);
        let eq = t.mk_eq(s, sum);
        assert!(all_bitvec_vars_are_bridge_only(&t, &[eq]));
    }

    /// `bv2nat(int2bv(8, s))` — int2bv permitted as a bv2nat argument.
    #[test]
    fn guard_accepts_int2bv_under_bv2nat() {
        let mut t = TermStore::new();
        let s = t.mk_var("s", Sort::Int);
        let l = t.mk_var("L", Sort::Int);
        let ib = t.mk_int2bv(8, s);
        let nat = t.mk_bv2nat(ib);
        let eq = t.mk_eq(l, nat);
        assert!(all_bitvec_vars_are_bridge_only(&t, &[eq]));
    }

    /// `bv2nat(bvadd(k, 1))` — k under bvadd: NOT bridge-only.
    #[test]
    fn guard_rejects_bvadd() {
        let mut t = TermStore::new();
        let k = bv8(&mut t, "k");
        let one = t.mk_bitvec(BigInt::one(), 8);
        let add = t.mk_bvadd(vec![k, one]);
        let l = t.mk_var("L", Sort::Int);
        let nat = t.mk_bv2nat(add);
        let eq = t.mk_eq(l, nat);
        assert!(!all_bitvec_vars_are_bridge_only(&t, &[eq]));
    }

    /// `bvult(k, 5)` — k under bvult: NOT bridge-only.
    #[test]
    fn guard_rejects_bvult() {
        let mut t = TermStore::new();
        let k = bv8(&mut t, "k");
        let five = t.mk_bitvec(BigInt::from(5), 8);
        let cmp = t.mk_bvult(k, five);
        assert!(!all_bitvec_vars_are_bridge_only(&t, &[cmp]));
    }

    /// `bv2nat(concat(k, 0))` — k under concat: NOT bridge-only.
    #[test]
    fn guard_rejects_concat() {
        let mut t = TermStore::new();
        let k = bv8(&mut t, "k");
        let z = t.mk_bitvec(BigInt::zero(), 8);
        let cc = t.mk_bvconcat(vec![k, z]);
        let l = t.mk_var("L", Sort::Int);
        let nat = t.mk_bv2nat(cc);
        let eq = t.mk_eq(l, nat);
        assert!(!all_bitvec_vars_are_bridge_only(&t, &[eq]));
    }

    /// `bv2nat(extract(3,0,k))` — k under extract: NOT bridge-only.
    #[test]
    fn guard_rejects_extract() {
        let mut t = TermStore::new();
        let k = bv8(&mut t, "k");
        let ex = t.mk_bvextract(3, 0, k);
        let l = t.mk_var("L", Sort::Int);
        let nat = t.mk_bv2nat(ex);
        let eq = t.mk_eq(l, nat);
        assert!(!all_bitvec_vars_are_bridge_only(&t, &[eq]));
    }

    /// `(= k m)` — BitVec equality: NOT bridge-only.
    #[test]
    fn guard_rejects_bv_equality() {
        let mut t = TermStore::new();
        let k = bv8(&mut t, "k");
        let m = bv8(&mut t, "m");
        let eq = t.mk_eq(k, m);
        assert!(!all_bitvec_vars_are_bridge_only(&t, &[eq]));
    }

    /// `(distinct k m)` — BitVec distinct: NOT bridge-only.
    #[test]
    fn guard_rejects_bv_distinct() {
        let mut t = TermStore::new();
        let k = bv8(&mut t, "k");
        let m = bv8(&mut t, "m");
        let d = t.mk_distinct(vec![k, m]);
        assert!(!all_bitvec_vars_are_bridge_only(&t, &[d]));
    }

    /// `bv2nat(bvand(k, 0x0F))` alongside a clean companion — the bvand
    /// occurrence disqualifies the whole query (every occurrence is scanned).
    #[test]
    fn guard_rejects_bvand_even_with_clean_companion() {
        let mut t = TermStore::new();
        let k = bv8(&mut t, "k");
        // clean companion: (= L (bv2nat k))
        let l = t.mk_var("L", Sort::Int);
        let nk = t.mk_bv2nat(k);
        let clean = t.mk_eq(l, nk);
        // dirty: (= M (bv2nat (bvand k 0x0F)))
        let mask = t.mk_bitvec(BigInt::from(15), 8);
        let band = t.mk_bvand(vec![k, mask]);
        let mm = t.mk_var("M", Sort::Int);
        let nb = t.mk_bv2nat(band);
        let dirty = t.mk_eq(mm, nb);
        assert!(
            !all_bitvec_vars_are_bridge_only(&t, &[clean, dirty]),
            "a single un-bridged (bvand) occurrence must reject the whole query"
        );
    }

    /// A query with NO BitVec at all is vacuously bridge-only.
    #[test]
    fn guard_accepts_no_bitvec() {
        let mut t = TermStore::new();
        let a = t.mk_var("a", Sort::Int);
        let b = t.mk_var("b", Sort::Int);
        let eq = t.mk_eq(a, b);
        assert!(all_bitvec_vars_are_bridge_only(&t, &[eq]));
    }
}
