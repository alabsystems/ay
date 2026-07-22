// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::{ChcExpr, ChcOp, ChcSort, FxHashMap, Lemma, PdrSolver, PredicateId, SmtResult};
use crate::farkas::{parse_linear_constraint, LiaFarkasTemplateKind};
use num_rational::Rational64;

pub(super) fn add_discovered_invariant(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: ChcExpr,
    level: usize,
) -> bool {
    add_discovered_invariant_impl(solver, pred, formula, level, false)
}

pub(super) fn add_discovered_invariant_algebraic(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: ChcExpr,
    level: usize,
) -> bool {
    add_discovered_invariant_impl(solver, pred, formula, level, true)
}

pub(super) fn add_discovered_invariant_impl(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: ChcExpr,
    level: usize,
    algebraically_verified: bool,
) -> bool {
    let lia_farkas_template = start_lia_farkas_template_admission(solver, &formula);

    if formula.contains_array_ops() && !formula.is_bool_sorted_top_level() {
        return finish_lia_farkas_template_admission(solver, lia_farkas_template, false, true);
    }

    // #8675: Reject array equalities like `(= arr (store ...))` or
    // `(= arr (const 0))`. These pin the entire array to its initial
    // value, which is almost never inductive for transitions that modify
    // the array. The self-inductiveness SMT check can return false UNSAT
    // for complex array formulas, allowing non-inductive array equalities
    // to slip into frames and produce false SAFE results.
    //
    // D1 exception (LIA-Lin-Arrays): a pure variable-variable array equality
    // `(= a1 a2)` between two Array-sorted predicate-argument VARIABLES is
    // admitted as a candidate. Unlike the store/const shapes above it does
    // not pin an array to a syntactic snapshot — it is the llreve relational
    // "lockstep" invariant. All downstream gates still run (init-validity,
    // SCC joint check, entry-inductiveness, self-inductiveness with the
    // executor false-UNSAT cross-check), and every gate rejects on Unknown.
    if contains_array_equality(&formula) && !is_var_var_array_equality(&formula) {
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: Rejecting array equality invariant for pred {} (#8675): {}",
                pred.index(),
                formula
            );
        }
        return finish_lia_farkas_template_admission(solver, lia_farkas_template, false, true);
    }

    if !algebraically_verified
        && solver
            .rejected_invariants
            .contains(&(pred, formula.clone()))
    {
        return finish_lia_farkas_template_admission(solver, lia_farkas_template, false, false);
    }

    let target_level = level.min(solver.frames.len().saturating_sub(1)).max(1);

    if solver.frames[target_level].contains_lemma(pred, &formula) {
        if algebraically_verified {
            solver.frames[target_level].add_lemma(
                Lemma::new(pred, formula, target_level).with_algebraically_verified(true),
            );
        }
        return finish_lia_farkas_template_admission(solver, lia_farkas_template, true, false);
    }

    if !algebraically_verified {
        if let Some((parity_var, k, c)) = solver.extract_simple_parity_equality(pred, &formula) {
            if !solver.is_parity_preserved_by_transitions(pred, &parity_var, k, c) {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Rejecting discovered parity invariant for pred {} (not transition-preserved): {}",
                        pred.index(),
                        formula
                    );
                }
                cache_rejected_invariant(solver, pred, &formula);
                return finish_lia_farkas_template_admission(
                    solver,
                    lia_farkas_template,
                    false,
                    true,
                );
            }
        }
    }

    if solver.predicate_has_facts(pred) && !algebraically_verified {
        let blocking = ChcExpr::not(formula.clone());
        if !solver.blocks_initial_states(pred, &blocking) {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Rejecting non-init-valid discovered invariant for pred {}: {}",
                    pred.index(),
                    formula
                );
            }
            cache_rejected_invariant(solver, pred, &formula);
            return finish_lia_farkas_template_admission(solver, lia_farkas_template, false, true);
        }
    } else if !solver.has_any_incoming_inter_predicate_transitions(pred) {
        let init_values = solver.get_init_values(pred);
        if !init_values.is_empty() {
            if let Some(init_constraint) =
                solver.build_init_constraint_from_bounds(pred, &init_values)
            {
                let query = ChcExpr::and(init_constraint, formula.clone());
                solver.smt.reset();
                if matches!(
                    solver.smt.check_sat(&query),
                    SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
                ) {
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: Rejecting non-init-valid invariant for pred {} (propagated bounds): {}",
                            pred.index(),
                            formula
                        );
                    }
                    cache_rejected_invariant(solver, pred, &formula);
                    return finish_lia_farkas_template_admission(
                        solver,
                        lia_farkas_template,
                        false,
                        true,
                    );
                }
            }
        }
    }

    if solver.is_cancelled() {
        return finish_lia_farkas_template_admission(solver, lia_farkas_template, false, false);
    }

    if let Some(&scc_idx) = solver.scc_info.predicate_to_scc.get(&pred) {
        let scc = &solver.scc_info.sccs[scc_idx];
        if scc.is_cyclic && scc.predicates.len() > 1 {
            let mut invariants: FxHashMap<PredicateId, ChcExpr> = FxHashMap::default();
            let scc_predicates = scc.predicates.clone();
            let mut translation_failed = false;
            for scc_pred in &scc_predicates {
                if *scc_pred == pred {
                    invariants.insert(pred, formula.clone());
                } else if let Some(translated) = solver.translate_lemma(&formula, pred, *scc_pred) {
                    invariants.insert(*scc_pred, translated);
                } else {
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: Cannot translate discovered invariant to SCC pred {} (skipping joint SCC check): {}",
                            scc_pred.index(),
                            formula
                        );
                    }
                    translation_failed = true;
                    break;
                }
            }

            if !translation_failed && !solver.verify_scc_lemmas(&scc_predicates, &invariants, level)
            {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Rejecting non-inductive discovered invariant for SCC pred {}: {}",
                        pred.index(),
                        formula
                    );
                }
                cache_rejected_invariant(solver, pred, &formula);
                return finish_lia_farkas_template_admission(
                    solver,
                    lia_farkas_template,
                    false,
                    true,
                );
            }
        }
    }

    if solver.has_any_incoming_inter_predicate_transitions(pred)
        && !solver.is_entry_inductive(&formula, pred, target_level)
    {
        if is_equality_formula(&formula) {
            let strengthened =
                solver.try_strengthen_predecessors_for_entry(pred, &formula, target_level);
            if strengthened && solver.is_entry_inductive(&formula, pred, target_level) {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Entry-inductiveness succeeded after predecessor strengthening for pred {}: {}",
                        pred.index(),
                        formula
                    );
                }
            } else {
                if strengthened && solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Predecessor strengthening insufficient for pred {}: {}",
                        pred.index(),
                        formula
                    );
                }
                let mut any_weakened_added = false;
                let mut failed_weakened = Vec::new();
                if let Some(weakened) = try_weaken_equality_to_inequality(&formula) {
                    for weak_formula in weakened {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: Equality {} failed entry-inductiveness, trying weakened: {}",
                                formula,
                                weak_formula
                            );
                        }
                        if add_discovered_invariant_impl(
                            solver,
                            pred,
                            weak_formula.clone(),
                            level,
                            algebraically_verified,
                        ) {
                            any_weakened_added = true;
                        } else {
                            failed_weakened.push(weak_formula);
                        }
                    }
                }
                if !failed_weakened.is_empty() && solver.deferred_entry_invariants.len() < 64 {
                    for weak_formula in failed_weakened {
                        if !solver.frames[target_level].contains_lemma(pred, &weak_formula) {
                            solver.deferred_entry_invariants.push((
                                pred,
                                weak_formula,
                                target_level,
                                0,
                            ));
                        }
                    }
                }
                if any_weakened_added {
                    finish_lia_farkas_template_admission(solver, lia_farkas_template, true, false);
                    return true;
                }
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Rejecting discovered invariant for pred {} (not entry-inductive): {}",
                        pred.index(),
                        formula
                    );
                }
                return finish_lia_farkas_template_admission(
                    solver,
                    lia_farkas_template,
                    false,
                    true,
                );
            }
        } else {
            if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Rejecting discovered invariant for pred {} (not entry-inductive): {}",
                    pred.index(),
                    formula
                );
            }
            return finish_lia_farkas_template_admission(solver, lia_farkas_template, false, true);
        }
    }

    if !algebraically_verified {
        let blocking_formula = ChcExpr::not(formula.clone());
        let passes_self_inductive = if solver.predicate_has_facts(pred) {
            solver.is_self_inductive_blocking(&blocking_formula, pred)
        } else if let Some(entry_domain) = solver.entry_domain_constraint(pred, target_level) {
            solver.is_self_inductive_blocking_with_entry_domain(
                &blocking_formula,
                pred,
                Some(&entry_domain),
            )
        } else {
            solver.is_self_inductive_blocking(&blocking_formula, pred)
        };

        if !passes_self_inductive {
            // Disequality->strict literal-swap repair (AY_CHC_DISEQ_SWAP): a
            // safety lemma with a disequality disjunct `a != b` (= a<b OR a>b) is
            // often too weak to be self-inductive; the strict `a<b`/`a>b` variant
            // may be. Re-validate each strict candidate through the SAME unchanged
            // admission oracle (init + entry + self-inductive, all reject on
            // Unknown), so this can only admit a genuinely inductive lemma. The
            // strict variants contain no disequality disjunct, so the recursive
            // call cannot re-trigger the swap (terminates immediately).
            if crate::pdr::solver::diseq_swap::diseq_swap_enabled() {
                for candidate in
                    crate::pdr::solver::diseq_swap::strict_disequality_repairs(&formula)
                {
                    if candidate == formula {
                        continue;
                    }
                    if add_discovered_invariant_impl(solver, pred, candidate, target_level, false) {
                        if solver.config.verbose {
                            safe_eprintln!(
                                "PDR: diseq-swap repair admitted a strict variant for pred {} from non-self-inductive: {}",
                                pred.index(),
                                formula
                            );
                        }
                        return finish_lia_farkas_template_admission(
                            solver,
                            lia_farkas_template,
                            true,
                            false,
                        );
                    }
                }
            }
            if solver.deferred_self_inductive_invariants.len() < 64 {
                if !solver.frames[target_level].contains_lemma(pred, &formula) {
                    solver.deferred_self_inductive_invariants.push((
                        pred,
                        formula.clone(),
                        target_level,
                        0,
                    ));
                    if solver.config.verbose {
                        safe_eprintln!(
                            "PDR: Deferring discovered invariant for pred {} (not self-inductive, will retry with frame): {}",
                            pred.index(),
                            formula
                        );
                    }
                }
            } else if solver.config.verbose {
                safe_eprintln!(
                    "PDR: Rejecting discovered invariant for pred {} (not self-inductive, defer queue full): {}",
                    pred.index(),
                    formula
                );
            }
            cache_rejected_invariant(solver, pred, &formula);
            return finish_lia_farkas_template_admission(solver, lia_farkas_template, false, true);
        }
    } else if solver.config.verbose {
        safe_eprintln!(
            "PDR: Accepting algebraically-verified invariant for pred {} (bypassing SMT check): {}",
            pred.index(),
            formula
        );
    }

    solver.add_lemma_to_frame(
        Lemma::new(pred, formula, target_level).with_algebraically_verified(algebraically_verified),
        target_level,
    );
    finish_lia_farkas_template_admission(solver, lia_farkas_template, true, false);
    true
}

fn start_lia_farkas_template_admission(
    solver: &mut PdrSolver,
    formula: &ChcExpr,
) -> Option<LiaFarkasTemplateKind> {
    if !solver.config.is_lia_farkas_profile() {
        return None;
    }
    let kind = classify_lia_farkas_template(formula)?;
    solver
        .telemetry
        .lia_farkas_templates
        .record_template_candidate(kind);
    Some(kind)
}

fn finish_lia_farkas_template_admission(
    solver: &mut PdrSolver,
    kind: Option<LiaFarkasTemplateKind>,
    accepted: bool,
    validation_failure: bool,
) -> bool {
    if kind.is_some() {
        if accepted {
            solver
                .telemetry
                .lia_farkas_templates
                .record_template_accept();
        } else {
            solver
                .telemetry
                .lia_farkas_templates
                .record_template_reject(validation_failure);
        }
    }
    accepted
}

fn classify_lia_farkas_template(formula: &ChcExpr) -> Option<LiaFarkasTemplateKind> {
    match formula {
        ChcExpr::Op(ChcOp::And, args) => args
            .iter()
            .find_map(|arg| classify_lia_farkas_template(arg.as_ref())),
        ChcExpr::Op(ChcOp::Eq, args)
            if args.len() == 2 && parse_linear_constraint(formula).is_some() =>
        {
            Some(LiaFarkasTemplateKind::AffineEquality)
        }
        ChcExpr::Op(ChcOp::Le | ChcOp::Lt | ChcOp::Ge | ChcOp::Gt, args) if args.len() == 2 => {
            classify_linear_template_constraint(formula)
        }
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            classify_linear_template_constraint(formula)
        }
        _ => None,
    }
}

fn classify_linear_template_constraint(formula: &ChcExpr) -> Option<LiaFarkasTemplateKind> {
    let constraint = parse_linear_constraint(formula)?;
    match constraint.coeffs.len() {
        0 | 1 => Some(LiaFarkasTemplateKind::Interval),
        2 if constraint.coeffs.values().all(|coeff| {
            *coeff == Rational64::from_integer(1) || *coeff == Rational64::from_integer(-1)
        }) =>
        {
            Some(LiaFarkasTemplateKind::DifferenceBound)
        }
        _ => Some(LiaFarkasTemplateKind::ScaledLinearCombination),
    }
}

pub(super) fn try_weaken_equality_to_inequality(formula: &ChcExpr) -> Option<Vec<ChcExpr>> {
    if let ChcExpr::Op(ChcOp::Eq, args) = formula {
        if args.len() == 2 {
            let lhs = args[0].as_ref().clone();
            let rhs = args[1].as_ref().clone();
            if matches!(lhs.sort(), ChcSort::Int) && matches!(rhs.sort(), ChcSort::Int) {
                return Some(vec![
                    ChcExpr::ge(lhs.clone(), rhs.clone()),
                    ChcExpr::le(lhs, rhs),
                ]);
            }
            // #8660: BV weakening — for `(= a b)` with equal-width BV sort,
            // emit both `(bvule a b)` and `(bvule b a)` (either direction may
            // be the true invariant). The select value coming from a
            // monotonic counter typically yields the `bvule c (select arr 0)`
            // direction.
            if let (ChcSort::BitVec(w1), ChcSort::BitVec(w2)) = (lhs.sort(), rhs.sort()) {
                if w1 == w2 {
                    return Some(vec![
                        ChcExpr::bv_ule(lhs.clone(), rhs.clone()),
                        ChcExpr::bv_ule(rhs, lhs),
                    ]);
                }
            }
        }
    }
    None
}

/// Check if a formula is `(= (select arr idx) val)` or `(= val (select arr idx))`.
///
/// Such select-based equalities are common invariant candidates for fact-clause
/// conjuncts in array programs (#8660). The equality form is rarely inductive
/// when the transition may store to `arr[idx]`, but the weakened `>=` / `<=`
/// form often is. Weakening is safe here even for single-predicate self-loops,
/// because both weakened forms are strictly weaker than the equality — the
/// normal entry-inductiveness / self-inductiveness checks in
/// `add_discovered_invariant_impl` still gate admission.
pub(super) fn is_select_based_equality(formula: &ChcExpr) -> bool {
    let ChcExpr::Op(ChcOp::Eq, args) = formula else {
        return false;
    };
    if args.len() != 2 {
        return false;
    }
    let is_select =
        |e: &ChcExpr| matches!(e, ChcExpr::Op(ChcOp::Select, inner) if inner.len() == 2);
    is_select(args[0].as_ref()) || is_select(args[1].as_ref())
}

pub(super) fn add_discovered_invariant_with_weakening(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: ChcExpr,
    level: usize,
) -> bool {
    if solver.add_discovered_invariant(pred, formula.clone(), level) {
        return true;
    }

    // Normally weakening is only tried when the predicate has an incoming
    // inter-predicate transition (the historical motivating pattern). For
    // select-based equalities, we also allow weakening on single-predicate
    // self-loops (#8660): the array-select equality is rarely inductive by
    // itself (the transition can store to `arr[idx]`), but the weakened
    // `(select arr idx) >= c` form typically is, and all downstream gates
    // (entry-inductiveness, self-inductiveness, SCC translation) still run
    // via `add_discovered_invariant_impl`.
    if !solver.has_any_incoming_inter_predicate_transitions(pred)
        && !is_select_based_equality(&formula)
    {
        return false;
    }

    if let Some(weakened_forms) = try_weaken_equality_to_inequality(&formula) {
        if solver.config.verbose {
            safe_eprintln!(
                "PDR: Equality {} failed for pred {}, trying weakened forms",
                formula,
                pred.index()
            );
        }

        for weakened in weakened_forms {
            if solver.add_discovered_invariant(pred, weakened.clone(), level) {
                if solver.config.verbose {
                    safe_eprintln!(
                        "PDR: Weakened equality to {} for pred {}",
                        weakened,
                        pred.index()
                    );
                }
                return true;
            }
        }
    }

    false
}

pub(super) fn is_equality_formula(formula: &ChcExpr) -> bool {
    if let ChcExpr::Op(ChcOp::Eq, args) = formula {
        if args.len() == 2 {
            return matches!(args[0].sort(), ChcSort::Int)
                && matches!(args[1].sort(), ChcSort::Int);
        }
    }
    false
}

pub(super) fn cache_rejected_invariant(
    solver: &mut PdrSolver,
    pred: PredicateId,
    formula: &ChcExpr,
) {
    if solver.rejected_invariants.len() < 512 {
        solver.rejected_invariants.insert((pred, formula.clone()));
    }
}

/// Check if a formula is exactly `(= a1 a2)` for two Array-sorted variables
/// of the same sort (D1, LIA-Lin-Arrays).
///
/// This is the only array-equality shape exempt from the #8675 rejection in
/// `add_discovered_invariant_impl`. Both sides must be plain `ChcExpr::Var`s;
/// any `store`/`select`/`const-array` structure keeps the #8675 rejection.
fn is_var_var_array_equality(formula: &ChcExpr) -> bool {
    if let ChcExpr::Op(ChcOp::Eq, args) = formula {
        if args.len() == 2 {
            if let (ChcExpr::Var(v1), ChcExpr::Var(v2)) = (args[0].as_ref(), args[1].as_ref()) {
                return matches!(&v1.sort, ChcSort::Array(_, _)) && v1.sort == v2.sort;
            }
        }
    }
    false
}

/// Check if a formula contains an equality between array-sorted expressions.
///
/// Array equalities like `(= arr (store ...))` pin the entire array to its
/// initial value, which is almost never inductive for transitions that modify
/// the array. Including them in invariants can lead to false SAFE results
/// (#8675) because the SMT self-inductiveness check may return incorrect UNSAT
/// for complex array formulas.
///
/// This recursively checks conjunctions, so `And(scalar_eq, array_eq)` is
/// caught even though the top-level formula is not an array equality.
fn contains_array_equality(formula: &ChcExpr) -> bool {
    match formula {
        ChcExpr::Op(ChcOp::Eq, args) => {
            if args.len() == 2 {
                if matches!(args[0].sort(), ChcSort::Array(_, _))
                    || matches!(args[1].sort(), ChcSort::Array(_, _))
                {
                    return true;
                }
            }
            false
        }
        ChcExpr::Op(ChcOp::And, args) => args.iter().any(|a| contains_array_equality(a)),
        // Check for negated-OR encoding of conjunction: not(or(not(a), not(b)))
        // which is how build_conjunctive_fact_clause_lemma encodes conjunctions
        // for non-LIA problems.
        ChcExpr::Op(ChcOp::Not, args) if args.len() == 1 => {
            if let ChcExpr::Op(ChcOp::Or, or_args) = args[0].as_ref() {
                or_args.iter().any(|a| {
                    if let ChcExpr::Op(ChcOp::Not, inner) = a.as_ref() {
                        if inner.len() == 1 {
                            return contains_array_equality(inner[0].as_ref());
                        }
                    }
                    false
                })
            } else {
                false
            }
        }
        _ => false,
    }
}
