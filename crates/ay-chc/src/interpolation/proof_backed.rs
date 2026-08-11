// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Proof-derived Craig interpolation via the ay-dpll `api::Solver` (rank-4 inc-3).
//!
//! When `A ∧ B` is UNSAT over the QF_LIA(+Bool) fragment, this module runs ONE
//! proof-producing solve on the ay-dpll API solver (proof mode is scoped to
//! exactly that interpolation query — no other query in the process pays the
//! proof-production cost), extracts a Craig interpolant from the reconstructed
//! resolution proof (`Solver::get_interpolant_with_strength`), converts it back
//! to `ChcExpr`, and verifies it with the EXISTING Craig validation
//! (`is_valid_interpolant_until`: A ⊨ I, I ∧ B UNSAT, shared-vars locality).
//!
//! SOUNDNESS COVENANT: every proof-derived candidate is verified before use,
//! exactly like the existing cascade's candidate validation. ANY failure —
//! unsupported fragment, parse error, solver panic, non-UNSAT proof solve,
//! malformed proof / Trust holes (surface as extraction failure), timeout, or
//! Craig validation failure — falls back silently to the unchanged syntactic
//! cascade (`interpolating_sat_constraints`). The default path is unchanged:
//! the proof attempt only runs when explicitly requested by the caller
//! (engine opt-in or the `AY_PROOF_INTERPOLANTS` env gate).
//!
//! BUDGET: the proof-mode solve + extraction + validation are bounded by the
//! caller-provided budget (IMC passes its per-query timeout), so the proof
//! attempt never exceeds the cascade's own budget for the same query.

use super::fallback::is_valid_interpolant_until;
use super::proof_eq_diffvar;
use super::{
    interpolating_sat_constraints, interpolating_sat_constraints_until, InterpolatingSatResult,
};
use crate::pdr::model::InvariantModel;
use crate::smt::executor_adapter::{quote_symbol, sort_to_smtlib};
use crate::{ChcExpr, ChcOp, ChcSort, ChcVar};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use ay_core::time::Instant;
use ay_dpll::api::{InterpolantStrength, Logic, Solver, Term as DpllTerm, TermKind};
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::OnceLock;
use std::time::Duration;

/// Caps keeping the opt-in proof attempt cheap relative to the cascade.
const MAX_PROOF_ITP_CONSTRAINTS: usize = 4096;
/// Applicability-scan node budget across all constraints.
const MAX_PROOF_ITP_SCAN_NODES: usize = 200_000;
/// Interpolant term -> ChcExpr conversion node budget.
const MAX_PROOF_ITP_CONVERT_NODES: usize = 50_000;

// ---------------------------------------------------------------------------
// Gate + stats
// ---------------------------------------------------------------------------

// NOTE (inc-16 S2): the process-wide `AY_PROOF_INTERPOLANTS` gate (inc-3,
// default OFF) moved into the IMC route's own resolution
// (`imc::imc_route_proof_interpolants_enabled`, default ON for IMC only,
// kill switch `AY_IMC_PROOF_ITP=0`). Non-IMC consumers opt in explicitly via
// the `proof_budget` parameter; there is no other process-wide default.

fn proof_itp_stats_enabled() -> bool {
    static FLAG: OnceLock<bool> = OnceLock::new();
    *FLAG.get_or_init(|| {
        std::env::var("AY_PROOF_ITP_STATS")
            .is_ok_and(|v| v == "1" || v.eq_ignore_ascii_case("true"))
    })
}

/// Verified proof-derived interpolants served to a consumer.
static PROOF_ITP_SERVED: AtomicUsize = AtomicUsize::new(0);
/// Attempts that reached the proof solve but fell back to the cascade
/// (non-UNSAT proof solve, extraction failure, validation failure, timeout).
static PROOF_ITP_FALLBACKS: AtomicUsize = AtomicUsize::new(0);
/// Attempts rejected before the proof solve (fragment/size gates).
static PROOF_ITP_NOT_APPLICABLE: AtomicUsize = AtomicUsize::new(0);
/// Proof attempts that panicked inside the ay-dpll solver (caught; fallback).
static PROOF_ITP_PANICS: AtomicUsize = AtomicUsize::new(0);
/// Proof solves that consumed their whole budget without an UNSAT verdict
/// (inc-16): the shape is hostile to the proof-mode solver configuration
/// (e.g. lustre guarded-eq networks — EqDiffVar is disabled under proof
/// production), so retrying every iteration only taxes the engine. Callers
/// use this to stop attempting after repeated timeouts.
static PROOF_ITP_SOLVE_TIMEOUTS: AtomicUsize = AtomicUsize::new(0);

/// Count of proof solves that hit their deadline without UNSAT (inc-16).
pub(crate) fn proof_itp_solve_timeouts() -> usize {
    PROOF_ITP_SOLVE_TIMEOUTS.load(Ordering::Relaxed)
}

/// Snapshot (served, fallbacks, not_applicable, panics) counters.
pub(crate) fn proof_interpolant_stats() -> (usize, usize, usize, usize) {
    (
        PROOF_ITP_SERVED.load(Ordering::Relaxed),
        PROOF_ITP_FALLBACKS.load(Ordering::Relaxed),
        PROOF_ITP_NOT_APPLICABLE.load(Ordering::Relaxed),
        PROOF_ITP_PANICS.load(Ordering::Relaxed),
    )
}

fn trace_event(event: &str) {
    let (served, fallbacks, na, panics) = proof_interpolant_stats();
    tracing::info!(
        event = "chc_proof_interpolation",
        kind = event,
        served,
        fallbacks,
        not_applicable = na,
        panics,
        "proof-derived interpolation event",
    );
    if proof_itp_stats_enabled() {
        safe_eprintln!(
            "[PROOF-ITP] {event}: served={served} fallbacks={fallbacks} not_applicable={na} panics={panics}"
        );
    }
}

// ---------------------------------------------------------------------------
// Entry points
// ---------------------------------------------------------------------------

/// Cascade entry with an optional proof-derived first attempt, reporting
/// provenance: the bool is `true` iff the returned interpolant came from the
/// proof path, i.e. it ALREADY passed the full Craig validation gate
/// (`is_valid_interpolant_until` — the same `is_valid_interpolant_with_check_sat`
/// checks on the same `and_all(a)`/`and_all(b)`/shared-vars inputs the engine
/// would re-run). Callers may use the flag to skip a byte-identical duplicate
/// validation; they must NOT skip validation for `false` (cascade) results
/// unless they validate themselves (rank-4 inc-7 attribution finding: the
/// duplicate validation was ~40% of IMC's per-iteration cost).
///
/// Proof mode also bounds the cascade fallback with a fresh `proof_budget`
/// deadline: the unbudgeted cascade can stall for minutes on deep-unrolling
/// queries (observed wedging IMC's loop for the rest of the engine budget).
///
/// Inc-16 S1a: `cascade_budget` independently bounds the cascade when proof
/// mode is OFF (`proof_budget = None`). The IMC loop always passes its
/// per-query budget here: without it the cascade's strategy legs (dual-MBP
/// AllSAT enumeration, UNSAT-core solve) issue `check_sat` calls with
/// `timeout=None` that can wedge the engine thread for the rest of the wall.
/// Both `None` keeps the legacy unbounded cascade byte-for-byte (non-IMC
/// callers are unchanged).
pub(crate) fn interpolating_sat_constraints_with_proof_provenance(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    proof_budget: Option<Duration>,
    cascade_budget: Option<Duration>,
) -> (InterpolatingSatResult, bool) {
    if let Some(budget) = proof_budget {
        if let Some(interpolant) =
            try_proof_derived_interpolant(a_constraints, b_constraints, shared_vars, budget)
        {
            return (InterpolatingSatResult::Unsat(interpolant), true);
        }
        // Fresh window (not the proof attempt's leftover): the cascade keeps
        // its own full per-query budget, so proof-solve cost never starves it.
        let cascade_deadline = Instant::now() + cascade_budget.unwrap_or(budget);
        return (
            interpolating_sat_constraints_until(
                a_constraints,
                b_constraints,
                shared_vars,
                cascade_deadline,
            ),
            false,
        );
    }
    if let Some(budget) = cascade_budget {
        let cascade_deadline = Instant::now() + budget;
        return (
            interpolating_sat_constraints_until(
                a_constraints,
                b_constraints,
                shared_vars,
                cascade_deadline,
            ),
            false,
        );
    }
    (
        interpolating_sat_constraints(a_constraints, b_constraints, shared_vars),
        false,
    )
}

/// Attempt ONE proof-producing solve and extract a VERIFIED Craig interpolant.
///
/// Returns `Some(I)` only when `I` passed the existing Craig validation
/// (`A ⊨ I`, `I ∧ B` UNSAT, vars(I) ⊆ shared). Returns `None` on any failure;
/// the caller falls back to the cascade.
pub(crate) fn try_proof_derived_interpolant(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    shared_vars: &FxHashSet<String>,
    budget: Duration,
) -> Option<ChcExpr> {
    let deadline = Instant::now() + budget;

    if a_constraints.is_empty()
        || b_constraints.is_empty()
        || a_constraints.len() + b_constraints.len() > MAX_PROOF_ITP_CONSTRAINTS
    {
        PROOF_ITP_NOT_APPLICABLE.fetch_add(1, Ordering::Relaxed);
        trace_event("not_applicable_size");
        return None;
    }

    // Fragment gate: QF_LIA with Bool/Int variables only. Anything outside the
    // fragment (arrays, reals, BV, datatypes, div/mod, predicate apps, ...)
    // falls back to the cascade, which has dedicated strategies for them.
    let mut scan_budget = MAX_PROOF_ITP_SCAN_NODES;
    let mut var_sorts: FxHashMap<String, ChcSort> = FxHashMap::default();
    for constraint in a_constraints.iter().chain(b_constraints.iter()) {
        if !collect_supported_vars(constraint, &mut var_sorts, &mut scan_budget) {
            PROOF_ITP_NOT_APPLICABLE.fetch_add(1, Ordering::Relaxed);
            trace_event("not_applicable_fragment");
            return None;
        }
    }
    if var_sorts.is_empty() {
        PROOF_ITP_NOT_APPLICABLE.fetch_add(1, Ordering::Relaxed);
        trace_event("not_applicable_no_vars");
        return None;
    }

    // Script-level EqDiffVar reduction (inc-17): the in-solver pass is
    // disabled under proof production, which made guarded-eq-network
    // unrollings time out inside the proof solve (inc-16's named blocker).
    // Rewriting the A/B constraint lists BEFORE the script keeps every proof
    // leaf traceable to a script assert; the produced interpolant is
    // back-substituted (`d := lin`) before the locality pre-filter and the
    // mandatory Craig validation against the ORIGINAL constraints, so any
    // defect here degrades to a cascade fallback, never a wrong answer.
    let dv_rewrite = if proof_eq_diffvar::eq_diffvar_proof_enabled() {
        proof_eq_diffvar::apply_for_proof_script(a_constraints, b_constraints, &var_sorts)
    } else {
        None
    };
    let mut var_sorts = var_sorts;
    let (script_a, script_b): (&[ChcExpr], &[ChcExpr]) = match dv_rewrite.as_ref() {
        Some(rw) => {
            for name in rw.subst.keys() {
                var_sorts.insert(name.clone(), ChcSort::Int);
            }
            if proof_itp_stats_enabled() {
                safe_eprintln!(
                    "[PROOF-ITP] eq-diffvar: {} constraints rewritten over {} difference vars",
                    rw.rewritten_constraints,
                    rw.diff_vars
                );
            }
            (&rw.a_constraints, &rw.b_constraints)
        }
        None => (a_constraints, b_constraints),
    };
    let dv_subst = dv_rewrite.as_ref().map(|rw| &rw.subst);

    // Build the SMT-LIB script for the scoped proof-producing solve.
    let script = build_qf_lia_script(script_a, script_b, &var_sorts);

    // Attribution hook (rank-4 inc-5): AY_PROOF_ITP_DUMP=<dir> writes each
    // proof-solve script to <dir>/proof_itp_<n>.smt2 for offline replay.
    // Debug-only side channel; never affects the solve or its result.
    if let Ok(dir) = std::env::var("AY_PROOF_ITP_DUMP") {
        if !dir.is_empty() {
            static DUMP_SEQ: AtomicUsize = AtomicUsize::new(0);
            let n = DUMP_SEQ.fetch_add(1, Ordering::Relaxed);
            let path = std::path::Path::new(&dir).join(format!(
                "proof_itp_{n}_a{}_b{}.smt2",
                script_a.len(),
                script_b.len()
            ));
            let _ = std::fs::write(path, &script);
        }
    }

    // The ay-dpll solver may debug_assert/panic on adversarial inputs; this is
    // an opt-in side path, so ANY panic inside the proof solve is caught and
    // mapped to a cascade fallback (the panic is counted + logged, never
    // hidden). Validation happens OUTSIDE the panic boundary so a verified
    // result can never be conflated with a swallowed failure.
    let candidates = match catch_unwind(AssertUnwindSafe(|| {
        proof_solve_and_extract(
            &script,
            script_a.len(),
            script_b.len(),
            shared_vars,
            &var_sorts,
            dv_subst,
            deadline,
        )
    })) {
        Ok(candidates) => candidates,
        Err(payload) => {
            PROOF_ITP_PANICS.fetch_add(1, Ordering::Relaxed);
            let reason = ay_core::panic_payload_to_string(&*payload);
            tracing::warn!(
                event = "chc_proof_interpolation_panic",
                reason = %reason,
                "proof-derived interpolation panicked; falling back to cascade",
            );
            trace_event("panic");
            Vec::new()
        }
    };

    // THE existing validation gate (A ⊨ I, I ∧ B UNSAT, locality), identical
    // to the cascade's own candidate validation. First verified candidate wins.
    for (idx, candidate) in candidates.into_iter().enumerate() {
        if Instant::now() >= deadline {
            break;
        }
        if is_valid_interpolant_until(
            a_constraints,
            b_constraints,
            &candidate,
            shared_vars,
            Some(deadline),
        ) {
            PROOF_ITP_SERVED.fetch_add(1, Ordering::Relaxed);
            trace_event("served");
            return Some(candidate);
        }
        // Attribution-only diagnosis of the failing validation leg (rank-4
        // inc-5). Stats-gated: re-runs the validation checks, so it must
        // never run on the default path.
        if proof_itp_stats_enabled() {
            let why = super::fallback::diagnose_interpolant_failure(
                a_constraints,
                b_constraints,
                &candidate,
                shared_vars,
                Some(deadline),
            );
            safe_eprintln!("[PROOF-ITP] candidate {idx} failed validation: {why}");
        }
    }

    PROOF_ITP_FALLBACKS.fetch_add(1, Ordering::Relaxed);
    trace_event("fallback");
    None
}

// ---------------------------------------------------------------------------
// Proof solve + extraction
// ---------------------------------------------------------------------------

/// Run the scoped proof-producing solve and return UNVALIDATED interpolant
/// candidates (one per strength variant that extracted + converted cleanly).
///
/// `dv_subst` is the EqDiffVar back-substitution map (inc-17): when the
/// script was built from rewritten constraints, every extracted candidate is
/// rewritten `d := lin` BEFORE the trivial-constant/locality pre-filters so
/// the candidates the caller validates are over the ORIGINAL signature.
/// Candidates that still mention a definitional variable after substitution
/// (node-budget bail inside the substitution) are dropped.
///
/// The caller MUST validate every candidate with the existing Craig
/// validation before use.
#[allow(clippy::too_many_arguments)]
fn proof_solve_and_extract(
    script: &str,
    a_count: usize,
    b_count: usize,
    shared_vars: &FxHashSet<String>,
    var_sorts: &FxHashMap<String, ChcSort>,
    dv_subst: Option<&FxHashMap<String, ChcExpr>>,
    deadline: Instant,
) -> Vec<ChcExpr> {
    let Some(remaining) = deadline.checked_duration_since(Instant::now()) else {
        return Vec::new();
    };
    if remaining.is_zero() {
        return Vec::new();
    }

    // Build with the script's OWN `(set-logic …)` when it declares one, and
    // strip that command. `Solver::try_new` dispatches a `set-logic` itself, so
    // leaving one in the script makes it the SECOND — which the elaborator
    // rejects (z3 parity, `118630ef6`). `parse_smtlib2` would then fail and
    // this function would silently return no interpolants at all.
    let (logic, script) =
        crate::smt::executor_adapter::split_leading_set_logic(script, Logic::QfLia);
    let Ok(mut solver) = Solver::try_new(logic) else {
        return Vec::new();
    };
    // Proof mode is scoped to THIS solver instance / THIS query only.
    solver.set_produce_proofs(true);
    // Preprocessing variable substitution detaches proof leaves from the
    // original assertions (everything collapses to Trust steps); disable it
    // for this solver only — same knob as the interpolation spike.
    solver.set_option(":ay-proof-no-varsubst", "true");
    solver.set_timeout(Some(remaining));

    let stats = proof_itp_stats_enabled();
    let Ok(asserts) = solver.parse_smtlib2(&script) else {
        if stats {
            safe_eprintln!("[PROOF-ITP] solve: script parse failed");
        }
        return Vec::new();
    };
    if asserts.len() != a_count + b_count {
        if stats {
            safe_eprintln!(
                "[PROOF-ITP] solve: assert split mismatch ({} != {}+{})",
                asserts.len(),
                a_count,
                b_count
            );
        }
        return Vec::new();
    }
    let (a_terms, b_terms) = asserts.split_at(a_count);
    let a_terms = a_terms.to_vec();
    let b_terms = b_terms.to_vec();

    // The ONE proof-producing solve (the cascade pays >= 1 solve for its own
    // candidate generation + 2 validation checks per candidate, so this stays
    // within the cascade's budget shape).
    let t_solve = Instant::now();
    let solve_result = solver.check_sat();
    if stats {
        safe_eprintln!(
            "[PROOF-ITP] solve: result_unsat={} dt={:.3}s a={} b={}",
            solve_result.is_unsat(),
            t_solve.elapsed().as_secs_f64(),
            a_count,
            b_count
        );
    }
    if !solve_result.is_unsat() {
        // Distinguish a budget-exhausted solve (hostile shape; the caller
        // should stop retrying) from a fast non-UNSAT outcome.
        if Instant::now() >= deadline {
            PROOF_ITP_SOLVE_TIMEOUTS.fetch_add(1, Ordering::Relaxed);
        }
        return Vec::new();
    }

    // Extract candidates, balanced first: Pudlak, then McMillan (strongest),
    // then McMillan' (weakest). Malformed proofs and Trust holes surface as
    // extraction failures (None) here; conversion failures are skipped.
    let mut candidates = Vec::new();
    for strength in [
        InterpolantStrength::Default,
        InterpolantStrength::Strongest,
        InterpolantStrength::Weakest,
    ] {
        if Instant::now() >= deadline {
            if stats {
                safe_eprintln!("[PROOF-ITP] extract: deadline before {strength:?}");
            }
            break;
        }
        let Some(result) = solver.get_interpolant_with_strength(&a_terms, &b_terms, strength)
        else {
            if stats {
                safe_eprintln!("[PROOF-ITP] extract: {strength:?} -> extraction failed");
            }
            continue;
        };
        let mut convert_budget = MAX_PROOF_ITP_CONVERT_NODES;
        let Some(candidate) = dpll_term_to_chc_expr(
            &solver,
            result.interpolant(),
            var_sorts,
            &mut convert_budget,
        ) else {
            if stats {
                safe_eprintln!("[PROOF-ITP] extract: {strength:?} -> conversion failed");
            }
            continue;
        };
        // EqDiffVar back-substitution (inc-17): replace each definitional
        // variable by its exact linear form so the candidate is over the
        // ORIGINAL signature. A leftover definitional var (substitution
        // node-budget bail) disqualifies the candidate.
        let candidate = match dv_subst {
            Some(subst) if !subst.is_empty() => {
                let substituted = candidate.substitute_name_map(subst);
                if substituted
                    .vars()
                    .iter()
                    .any(|v| subst.contains_key(&v.name))
                {
                    if stats {
                        safe_eprintln!(
                            "[PROOF-ITP] extract: {strength:?} -> leftover eq-diffvar after back-substitution"
                        );
                    }
                    continue;
                }
                substituted
            }
            _ => candidate,
        };
        // Cheap structural locality pre-filter (validation re-checks this);
        // trivial constants can't satisfy both Craig checks on a
        // non-degenerate split, so skip them without burning solver calls.
        if matches!(candidate, ChcExpr::Bool(_)) {
            if stats {
                safe_eprintln!("[PROOF-ITP] extract: {strength:?} -> trivial constant");
            }
            continue;
        }
        if !candidate
            .vars()
            .into_iter()
            .all(|v| shared_vars.contains(&v.name))
        {
            if stats {
                safe_eprintln!("[PROOF-ITP] extract: {strength:?} -> locality pre-filter");
            }
            continue;
        }
        if !candidates.contains(&candidate) {
            candidates.push(candidate);
        }
    }
    candidates
}

// ---------------------------------------------------------------------------
// ChcExpr -> SMT-LIB script (QF_LIA fragment)
// ---------------------------------------------------------------------------

/// Collect variables, enforcing the supported QF_LIA(+Bool) fragment.
///
/// Returns false (unsupported) on: non-Int/Bool variable sorts, the same name
/// with two different sorts, Real/BitVec literals, div/mod, array/BV ops,
/// predicate/function applications, const arrays, or scan-budget exhaustion.
fn collect_supported_vars(
    expr: &ChcExpr,
    var_sorts: &mut FxHashMap<String, ChcSort>,
    budget: &mut usize,
) -> bool {
    crate::expr::maybe_grow_expr_stack(|| {
        if *budget == 0 {
            return false;
        }
        *budget -= 1;
        match expr {
            ChcExpr::Bool(_) | ChcExpr::Int(_) => true,
            ChcExpr::Real(..)
            | ChcExpr::BitVec(..)
            | ChcExpr::ConstArrayMarker(_)
            | ChcExpr::IsTesterMarker(_)
            | ChcExpr::ConstArray(..)
            | ChcExpr::PredicateApp(..)
            | ChcExpr::FuncApp(..) => false,
            ChcExpr::Var(v) => {
                if !matches!(v.sort, ChcSort::Int | ChcSort::Bool) {
                    return false;
                }
                match var_sorts.get(&v.name) {
                    Some(sort) => *sort == v.sort,
                    None => {
                        var_sorts.insert(v.name.clone(), v.sort.clone());
                        true
                    }
                }
            }
            ChcExpr::Op(op, args) => {
                let supported_op = matches!(
                    op,
                    ChcOp::Not
                        | ChcOp::And
                        | ChcOp::Or
                        | ChcOp::Implies
                        | ChcOp::Iff
                        | ChcOp::Add
                        | ChcOp::Sub
                        | ChcOp::Mul
                        | ChcOp::Neg
                        | ChcOp::Eq
                        | ChcOp::Ne
                        | ChcOp::Lt
                        | ChcOp::Le
                        | ChcOp::Gt
                        | ChcOp::Ge
                        | ChcOp::Ite
                );
                supported_op
                    && args
                        .iter()
                        .all(|a| collect_supported_vars(a, var_sorts, budget))
            }
        }
    })
}

/// Render the scoped interpolation query as an SMT-LIB script: declarations,
/// then the A-partition asserts, then the B-partition asserts (in order, so
/// the parsed assert handles split at `a_constraints.len()`).
fn build_qf_lia_script(
    a_constraints: &[ChcExpr],
    b_constraints: &[ChcExpr],
    var_sorts: &FxHashMap<String, ChcSort>,
) -> String {
    let mut names: Vec<&String> = var_sorts.keys().collect();
    names.sort();

    let mut script = String::with_capacity(1024);
    script.push_str("(set-logic QF_LIA)\n");
    for name in names {
        let sort = &var_sorts[name];
        script.push_str(&format!(
            "(declare-const {} {})\n",
            quote_symbol(name),
            sort_to_smtlib(sort)
        ));
    }
    for constraint in a_constraints.iter().chain(b_constraints.iter()) {
        script.push_str(&format!(
            "(assert {})\n",
            InvariantModel::expr_to_smtlib(constraint)
        ));
    }
    script
}

// ---------------------------------------------------------------------------
// ay-dpll Term -> ChcExpr (QF_LIA fragment, conservative)
// ---------------------------------------------------------------------------

/// Convert an interpolant term from the ay-dpll solver back to `ChcExpr`.
///
/// Conservative: anything outside the QF_LIA(+Bool) fragment, any variable
/// not declared by the script (sort recovered via `var_sorts`), or budget
/// exhaustion returns `None` (cascade fallback).
///
/// DAG-aware since inc-19: proof-derived interpolants are hash-consed DAGs
/// (Pudlak roots on executor proofs share subterms heavily — the SYNAPSE k=2
/// roots format to multi-MB TREES but are small DAGs); the tree-walk burned
/// the node budget exponentially and every non-trivial root was dropped as
/// "conversion failed". Memoizing on the term handle visits each unique node
/// once; the produced `ChcExpr` shares converted children the same way.
fn dpll_term_to_chc_expr(
    solver: &Solver,
    term: DpllTerm,
    var_sorts: &FxHashMap<String, ChcSort>,
    budget: &mut usize,
) -> Option<ChcExpr> {
    let mut memo: FxHashMap<DpllTerm, ChcExpr> = FxHashMap::default();
    dpll_term_to_chc_expr_memo(solver, term, var_sorts, budget, &mut memo)
}

fn dpll_term_to_chc_expr_memo(
    solver: &Solver,
    term: DpllTerm,
    var_sorts: &FxHashMap<String, ChcSort>,
    budget: &mut usize,
    memo: &mut FxHashMap<DpllTerm, ChcExpr>,
) -> Option<ChcExpr> {
    if let Some(cached) = memo.get(&term) {
        return Some(cached.clone());
    }
    let result = crate::expr::maybe_grow_expr_stack(|| {
        if *budget == 0 {
            return None;
        }
        *budget -= 1;
        match solver.term_kind(term) {
            TermKind::Var { name } => {
                let sort = var_sorts.get(&name)?;
                Some(ChcExpr::var(ChcVar::new(name, sort.clone())))
            }
            TermKind::Const => parse_const_text(&solver.format_term(term)),
            TermKind::Not => {
                let children = solver.term_children(term);
                if children.len() != 1 {
                    return None;
                }
                Some(ChcExpr::not(dpll_term_to_chc_expr_memo(
                    solver,
                    children[0],
                    var_sorts,
                    budget,
                    memo,
                )?))
            }
            TermKind::Ite => {
                let children = solver.term_children(term);
                if children.len() != 3 {
                    return None;
                }
                let c = dpll_term_to_chc_expr_memo(solver, children[0], var_sorts, budget, memo)?;
                let t = dpll_term_to_chc_expr_memo(solver, children[1], var_sorts, budget, memo)?;
                let e = dpll_term_to_chc_expr_memo(solver, children[2], var_sorts, budget, memo)?;
                Some(ChcExpr::ite(c, t, e))
            }
            TermKind::App { name, .. } => {
                let children = solver.term_children(term);
                let mut args = Vec::with_capacity(children.len());
                for child in children {
                    args.push(dpll_term_to_chc_expr_memo(
                        solver, child, var_sorts, budget, memo,
                    )?);
                }
                app_to_chc_expr(&name, args)
            }
            // Quantifiers/lets are outside the fragment; `TermKind` is
            // non-exhaustive, so future variants conservatively bail too.
            _ => None,
        }
    });
    if let Some(expr) = &result {
        memo.insert(term, expr.clone());
    }
    result
}

fn app_to_chc_expr(name: &str, mut args: Vec<ChcExpr>) -> Option<ChcExpr> {
    let binary = |args: &mut Vec<ChcExpr>| -> Option<(ChcExpr, ChcExpr)> {
        if args.len() != 2 {
            return None;
        }
        let rhs = args.pop()?;
        let lhs = args.pop()?;
        Some((lhs, rhs))
    };
    match name {
        "and" => args.into_iter().reduce(ChcExpr::and),
        "or" => args.into_iter().reduce(ChcExpr::or),
        "not" => {
            if args.len() != 1 {
                return None;
            }
            Some(ChcExpr::not(args.pop()?))
        }
        "=>" => {
            let (lhs, rhs) = binary(&mut args)?;
            Some(ChcExpr::implies(lhs, rhs))
        }
        "=" => {
            let (lhs, rhs) = binary(&mut args)?;
            Some(ChcExpr::eq(lhs, rhs))
        }
        "distinct" => {
            let (lhs, rhs) = binary(&mut args)?;
            Some(ChcExpr::ne(lhs, rhs))
        }
        "<" => {
            let (lhs, rhs) = binary(&mut args)?;
            Some(ChcExpr::lt(lhs, rhs))
        }
        "<=" => {
            let (lhs, rhs) = binary(&mut args)?;
            Some(ChcExpr::le(lhs, rhs))
        }
        ">" => {
            let (lhs, rhs) = binary(&mut args)?;
            Some(ChcExpr::gt(lhs, rhs))
        }
        ">=" => {
            let (lhs, rhs) = binary(&mut args)?;
            Some(ChcExpr::ge(lhs, rhs))
        }
        "+" => args.into_iter().reduce(ChcExpr::add),
        "-" => {
            if args.is_empty() {
                return None;
            }
            if args.len() == 1 {
                return Some(ChcExpr::neg(args.pop()?));
            }
            args.into_iter().reduce(ChcExpr::sub)
        }
        "*" => {
            let (lhs, rhs) = binary(&mut args)?;
            Some(ChcExpr::mul(lhs, rhs))
        }
        _ => None,
    }
}

/// Parse a formatted constant term: `true`, `false`, `N`, or `(- N)`.
fn parse_const_text(text: &str) -> Option<ChcExpr> {
    let t = text.trim();
    match t {
        "true" => return Some(ChcExpr::Bool(true)),
        "false" => return Some(ChcExpr::Bool(false)),
        _ => {}
    }
    if let Ok(n) = t.parse::<i128>() {
        return Some(ChcExpr::Int(n));
    }
    let inner = t.strip_prefix("(-")?.strip_suffix(')')?.trim();
    let n: i128 = inner.parse().ok()?;
    n.checked_neg().map(ChcExpr::Int)
}

#[allow(clippy::unwrap_used, clippy::panic)]
#[cfg(test)]
#[path = "proof_backed_tests.rs"]
mod tests;
