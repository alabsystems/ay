// Copyright 2026 Andrew Yates
// SPDX-License-Identifier: Apache-2.0

use super::conjoin;
use super::polynomial::{derive_conserved_quantity, eval_conserved_at_entry};
use super::transfer_entry::{
    apply_source_invariant_to_entry, compute_source_constants, resolve_entry_value,
};
use super::validate::AlgebraicValidationStats;
use crate::pdr::cube::is_trivial_contradiction;
use crate::pdr::model::InvariantModel;
use crate::recurrence::{analyze_transition, ClosedForm};
use crate::smt::{SmtContext, SmtResult};
use crate::{
    ChcExpr, ChcOp, ChcProblem, ChcSort, ChcVar, ClauseHead, HornClause, Predicate, PredicateId,
};
use ay_core::kani_compat::{DetHashMap as FxHashMap, DetHashSet as FxHashSet};
use std::sync::Arc;
use std::time::Duration;

const ZERO_ARITY_TRANSFER_TIMEOUT: Duration = Duration::from_millis(75);
const ZERO_ARITY_TRIANGULAR_MAX_COUNTER_UPPER: i128 = 1_000_000;

/// Derive invariant for a predicate without a fact clause, using conserved
/// quantities from the predicate's own self-loop combined with entry
/// conditions from a solved predecessor.
///
/// This handles multi-predicate problems like s_multipl_25 where:
/// - inv1 has polynomial closed forms and concrete init values → solved
/// - inv2 has polynomial closed forms but no fact clause → needs this
///
/// The approach: for each polynomial variable X with counter N in inv2's
/// self-loop, `LCD*X + correction(N)` is conserved. We evaluate this at
/// entry (from the transfer clause + inv1's invariant) to get the constant,
/// producing invariants like `2*B = F*(F+1) - A*(A+1)`.
pub(super) fn derive_conserved_invariant(
    problem: &ChcProblem,
    pred: &Predicate,
    model: &InvariantModel,
    solved_preds: &FxHashSet<PredicateId>,
    verbose: bool,
) -> Option<ChcExpr> {
    // Step 1: Find self-loop and analyze its transition
    let self_loop = problem.clauses().iter().find(|c| {
        c.head.predicate_id() == Some(pred.id)
            && c.body.predicates.len() == 1
            && c.body.predicates[0].0 == pred.id
    })?;

    let (pre_vars, transition) = super::extract_normalized_transition(self_loop)?;
    let system = analyze_transition(&transition, &pre_vars)?;

    // Find counter (ConstantDelta with non-zero delta)
    let (n_var_name, _n_delta) = system.solutions.iter().find_map(|(name, cf)| {
        if let ClosedForm::ConstantDelta { delta } = cf {
            if *delta != 0 {
                return Some((name.clone(), *delta));
            }
        }
        None
    })?;

    // Need at least one polynomial variable
    let has_polynomial = system
        .solutions
        .values()
        .any(|cf| matches!(cf, ClosedForm::Polynomial { .. }));
    if !has_polynomial {
        return None;
    }

    if verbose {
        safe_eprintln!(
            "Algebraic conserved: pred {} has polynomial closed forms, counter={}",
            pred.name,
            n_var_name
        );
    }

    // Step 2: Find transfer clause from a solved predecessor
    let trans_clause = problem.clauses().iter().find(|c| {
        c.head.predicate_id() == Some(pred.id)
            && c.body.predicates.len() == 1
            && c.body.predicates[0].0 != pred.id
            && solved_preds.contains(&c.body.predicates[0].0)
    })?;

    let source_pred_id = trans_clause.body.predicates[0].0;
    let source_args = &trans_clause.body.predicates[0].1;
    let head_args = match &trans_clause.head {
        ClauseHead::Predicate(_, args) => args,
        ClauseHead::False => return None,
    };

    let source_interp = model.get(&source_pred_id)?;

    // Step 3: Build mapping from target pre_vars to transfer clause expressions
    // target_pre_var[i] → head_args[i] in transfer clause vars
    let mut target_to_transfer: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for (i, pre_var) in pre_vars.iter().enumerate() {
        if let Some(ha) = head_args.get(i) {
            target_to_transfer.insert(pre_var.clone(), ha.clone());
        }
    }

    // Step 4: Build mapping from transfer clause vars → source pred entry values
    // source_subst: source formal vars → source actual args (transfer body)
    let source_subst: Vec<(ChcVar, ChcExpr)> = source_interp
        .vars
        .iter()
        .zip(source_args.iter())
        .map(|(v, a)| (v.clone(), a.clone()))
        .collect();

    // Extract constraint variable definitions
    let constraint = trans_clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));
    let mut var_defs: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for conj in constraint.conjuncts() {
        if let ChcExpr::Op(ChcOp::Eq, args) = conj {
            if args.len() == 2 {
                if let ChcExpr::Var(v) = &*args[0] {
                    var_defs.insert(v.name.clone(), (*args[1]).clone());
                }
                if let ChcExpr::Var(v) = &*args[1] {
                    if !var_defs.contains_key(&v.name) {
                        var_defs.insert(v.name.clone(), (*args[0]).clone());
                    }
                }
            }
        }
    }

    // Step 5: For the source pred, analyze its self-loop to find which
    // source variables are constant (ConstantDelta(0) with known init)
    let source_constant_values = compute_source_constants(problem, source_pred_id, verbose);

    // Step 6: Compute entry values for each target pre_var
    // For ConstantDelta(0) vars in target: entry = current (use pre_var name)
    // For others: resolve through transfer clause
    let constant_target_vars: FxHashSet<String> = system
        .solutions
        .iter()
        .filter(|(_, cf)| matches!(cf, ClosedForm::ConstantDelta { delta: 0 }))
        .map(|(name, _)| name.clone())
        .collect();

    if verbose {
        safe_eprintln!(
            "Algebraic conserved: constant target vars: {:?}",
            constant_target_vars
        );
    }

    // Step 7: For each polynomial variable, derive conserved quantity invariant
    let mut invariants: Vec<ChcExpr> = Vec::new();

    for (var_name, closed_form) in &system.solutions {
        let coeffs = match closed_form {
            ClosedForm::Polynomial { coeffs } => coeffs,
            _ => continue,
        };

        let (lcd, cq_expr) = match derive_conserved_quantity(var_name, coeffs, &n_var_name) {
            Some(v) => v,
            None => continue,
        };

        if verbose {
            safe_eprintln!(
                "Algebraic conserved: CQ for {} = {:?} (lcd={})",
                var_name,
                cq_expr,
                lcd
            );
        }

        // Compute entry value of X (the polynomial variable)
        let x_entry = resolve_entry_value(
            var_name,
            &target_to_transfer,
            &var_defs,
            &source_subst,
            &source_interp.vars,
            model,
            &source_pred_id,
            &source_constant_values,
            &constant_target_vars,
            &pre_vars,
        );

        // Compute entry value of N (the counter)
        let n_entry = resolve_entry_value(
            &n_var_name,
            &target_to_transfer,
            &var_defs,
            &source_subst,
            &source_interp.vars,
            model,
            &source_pred_id,
            &source_constant_values,
            &constant_target_vars,
            &pre_vars,
        );

        if verbose {
            safe_eprintln!(
                "Algebraic conserved: {} entry={:?}, {} entry={:?}",
                var_name,
                x_entry,
                n_var_name,
                n_entry
            );
        }

        let (x_entry, n_entry) = match (x_entry, n_entry) {
            (Some(x), Some(n)) => (x, n),
            _ => continue,
        };

        // CQ(X_entry, N_entry) = constant
        let cq_at_entry = eval_conserved_at_entry(lcd, &x_entry, &n_var_name, &n_entry, coeffs);

        if verbose {
            safe_eprintln!(
                "Algebraic conserved: CQ_entry for {} = {:?}",
                var_name,
                cq_at_entry
            );
        }

        // Now apply the source invariant to simplify cq_at_entry.
        // The entry value of X may be constrained by the source invariant.
        // Substitute source invariant equalities into the entry expression.
        let simplified = apply_source_invariant_to_entry(
            &cq_at_entry,
            model,
            &source_pred_id,
            &source_subst,
            &constant_target_vars,
            &pre_vars,
            &target_to_transfer,
            verbose,
        );

        let rhs = simplified.unwrap_or(cq_at_entry);

        // Invariant: CQ(X, N) = rhs (simplified entry constant)
        invariants.push(ChcExpr::eq(cq_expr, rhs));
    }

    if invariants.is_empty() {
        return None;
    }

    if verbose {
        safe_eprintln!(
            "Algebraic conserved: derived {} invariant(s) for pred {}",
            invariants.len(),
            pred.name
        );
        for inv in &invariants {
            safe_eprintln!("Algebraic conserved:   {:?}", inv);
        }
    }

    Some(conjoin(invariants))
}

pub(super) fn derive_transferred_invariant_from_incoming(
    problem: &ChcProblem,
    pred: &Predicate,
    incoming: &[&HornClause],
    model: &InvariantModel,
    solved_preds: &FxHashSet<PredicateId>,
    solved_invariants: &FxHashMap<PredicateId, Vec<ChcExpr>>,
    mut synthesis_stats: Option<&mut AlgebraicValidationStats>,
    verbose: bool,
) -> Option<ChcExpr> {
    if verbose {
        safe_eprintln!(
            "Algebraic: trying transferred invariant for pred {}",
            pred.name
        );
    }

    if pred.arg_sorts.is_empty() {
        return derive_zero_arity_false_invariant(
            problem,
            pred,
            incoming,
            model,
            solved_preds,
            verbose,
        );
    }

    let mut saw_incoming = false;
    let mut branch_formulas = Vec::new();
    let target_has_self_loop = problem
        .clauses()
        .iter()
        .any(|clause| is_self_loop_clause(clause, pred.id));
    let target_loop = target_constant_delta_loop(problem, pred);
    let has_non_self_incoming = incoming
        .iter()
        .copied()
        .any(|clause| !is_self_loop_clause(clause, pred.id));
    if !has_non_self_incoming {
        if verbose {
            safe_eprintln!(
                "Algebraic: pred {} has no non-self incoming clauses; using false invariant",
                pred.name
            );
        }
        return Some(ChcExpr::Bool(false));
    }

    for trans_clause in incoming
        .iter()
        .copied()
        .filter(|c| !is_self_loop_clause(c, pred.id) && !c.body.predicates.is_empty())
    {
        saw_incoming = true;
        if trans_clause.body.predicates.len() != 1 {
            if verbose {
                safe_eprintln!(
                    "Algebraic: unsupported multi-body transfer into pred {}",
                    pred.name
                );
            }
            return None;
        }

        let source_pred_id = trans_clause.body.predicates[0].0;
        if source_pred_id == pred.id {
            continue;
        }
        if !solved_preds.contains(&source_pred_id) {
            if verbose {
                safe_eprintln!(
                    "Algebraic: source pred {:?} for {} is not solved yet",
                    source_pred_id,
                    pred.name
                );
            }
            return None;
        }

        let branch =
            transferred_branch_formula(trans_clause, pred, model, solved_invariants, verbose)?;
        let branch = if let Some(target_loop) = &target_loop {
            match close_transferred_branch_under_constant_delta(
                &branch,
                target_loop,
                synthesis_stats.as_deref_mut(),
                verbose,
            ) {
                Some(closed) => closed,
                None => {
                    if verbose {
                        safe_eprintln!(
                            "Algebraic: transfer branch into {} has no affine self-loop closure",
                            pred.name
                        );
                    }
                    return None;
                }
            }
        } else if target_has_self_loop {
            if verbose {
                safe_eprintln!(
                    "Algebraic: self-loop transfer into {} has no non-trivial constant-delta closure",
                    pred.name
                );
            }
            return None;
        } else {
            branch
        };
        branch_formulas.push(branch);
    }

    if !saw_incoming {
        if verbose {
            safe_eprintln!(
                "Algebraic: no inter-predicate transition for pred {}",
                pred.name
            );
        }
        return None;
    }

    let formula = ChcExpr::or_all(branch_formulas).simplify_constants();
    if matches!(formula, ChcExpr::Bool(true)) {
        return None;
    }
    Some(formula)
}

fn transferred_branch_formula(
    trans_clause: &HornClause,
    pred: &Predicate,
    model: &InvariantModel,
    solved_invariants: &FxHashMap<PredicateId, Vec<ChcExpr>>,
    verbose: bool,
) -> Option<ChcExpr> {
    let source_pred_id = trans_clause.body.predicates[0].0;
    let source_args = &trans_clause.body.predicates[0].1;
    let head_args = match &trans_clause.head {
        ClauseHead::Predicate(_, args) => args,
        ClauseHead::False => return None,
    };

    let source_interp = model.get(&source_pred_id)?;
    let source_invs = solved_invariants.get(&source_pred_id)?;
    let constraint = trans_clause
        .body
        .constraint
        .clone()
        .unwrap_or(ChcExpr::Bool(true));

    // Substitution: source pred formal vars -> actual body call args
    let source_subst: Vec<(ChcVar, ChcExpr)> = source_interp
        .vars
        .iter()
        .zip(source_args.iter())
        .map(|(v, a)| (v.clone(), a.clone()))
        .collect();

    let var_defs = extract_var_defs(&constraint);

    let target_formals: Vec<ChcVar> = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
        .collect();
    let target_var_set: FxHashSet<ChcVar> = target_formals.iter().cloned().collect();

    let mut head_to_formal = head_to_formal_substitution(head_args, &var_defs, &target_formals);
    extend_head_to_formal_with_source_equalities(
        source_invs,
        &source_subst,
        &mut head_to_formal,
        &target_var_set,
    );

    let mut transferred: Vec<ChcExpr> = Vec::new();

    for (i, head_arg) in head_args.iter().enumerate() {
        let Some(formal) = target_formals.get(i).cloned() else {
            continue;
        };
        let arg_in_target_vars = head_arg.substitute(&head_to_formal);
        if arg_in_target_vars
            .vars()
            .iter()
            .all(|var| target_var_set.contains(var))
        {
            if let Some(expr) = transferable_target_formula(
                ChcExpr::eq(ChcExpr::var(formal), arg_in_target_vars),
                &target_var_set,
            ) {
                transferred.push(expr);
            }
        }
    }

    for inv in source_invs {
        let inv_body = inv.substitute(&source_subst);
        let in_target_vars = inv_body.substitute(&head_to_formal);
        if let Some(expr) = transferable_target_formula(in_target_vars, &target_var_set) {
            transferred.push(expr);
        }
    }

    for conj in constraint.conjuncts() {
        let in_target_vars = conj.substitute(&head_to_formal);
        if let Some(expr) = transferable_target_formula(in_target_vars, &target_var_set) {
            transferred.push(expr);
        }
    }

    if transferred.is_empty() {
        if verbose {
            safe_eprintln!(
                "Algebraic: transfer branch into {} has no target facts",
                pred.name
            );
        }
        return Some(ChcExpr::Bool(true));
    }

    Some(conjoin(transferred).simplify_constants())
}

fn extend_head_to_formal_with_source_equalities(
    source_invs: &[ChcExpr],
    source_subst: &[(ChcVar, ChcExpr)],
    head_to_formal: &mut Vec<(ChcVar, ChcExpr)>,
    target_var_set: &FxHashSet<ChcVar>,
) {
    for _ in 0..source_invs.len().saturating_add(1) {
        let mut changed = false;
        for inv in source_invs {
            for conjunct in inv.conjuncts() {
                let equality = conjunct.substitute(source_subst).substitute(head_to_formal);
                let ChcExpr::Op(ChcOp::Eq, args) = &equality else {
                    continue;
                };
                if args.len() != 2 {
                    continue;
                }
                changed |=
                    maybe_add_transfer_alias(&args[0], &args[1], head_to_formal, target_var_set);
                changed |=
                    maybe_add_transfer_alias(&args[1], &args[0], head_to_formal, target_var_set);
            }
        }
        if !changed {
            break;
        }
    }
}

fn maybe_add_transfer_alias(
    candidate_var: &ChcExpr,
    candidate_expr: &ChcExpr,
    head_to_formal: &mut Vec<(ChcVar, ChcExpr)>,
    target_var_set: &FxHashSet<ChcVar>,
) -> bool {
    let ChcExpr::Var(var) = candidate_var else {
        return false;
    };
    if target_var_set.contains(var) || head_to_formal.iter().any(|(existing, _)| existing == var) {
        return false;
    }
    if !candidate_expr
        .vars()
        .iter()
        .all(|expr_var| target_var_set.contains(expr_var))
    {
        return false;
    }
    head_to_formal.push((var.clone(), candidate_expr.clone()));
    true
}

#[derive(Clone)]
struct TargetConstantDeltaLoop {
    formals: Vec<ChcVar>,
    deltas: Vec<i128>,
    guard_invariants: Vec<ChcExpr>,
}

fn target_constant_delta_loop(
    problem: &ChcProblem,
    pred: &Predicate,
) -> Option<TargetConstantDeltaLoop> {
    let self_loop = problem
        .clauses()
        .iter()
        .find(|clause| is_self_loop_clause(clause, pred.id))?;
    let normalized = super::extract_normalized_self_loop(self_loop)?;
    let body_args = &self_loop.body.predicates[0].1;
    if body_args.len() != pred.arg_sorts.len() || normalized.pre_vars.len() != pred.arg_sorts.len()
    {
        return None;
    }

    let deltas_by_pre_var = super::extract_constant_deltas(&normalized.updates);
    let formals: Vec<ChcVar> = pred
        .arg_sorts
        .iter()
        .enumerate()
        .map(|(i, sort)| ChcVar::new(format!("x{i}"), sort.clone()))
        .collect();
    let mut deltas = Vec::with_capacity(formals.len());
    let mut pre_to_formal = Vec::with_capacity(formals.len());

    for (idx, body_arg) in body_args.iter().enumerate() {
        let ChcExpr::Var(pre_var) = body_arg else {
            return None;
        };
        let delta = *deltas_by_pre_var.get(&pre_var.name)?;
        deltas.push(delta);
        pre_to_formal.push((pre_var.clone(), ChcExpr::var(formals[idx].clone())));
    }
    if deltas.iter().all(|delta| *delta == 0) {
        return None;
    }

    let unchanged_vars: FxHashSet<String> = deltas_by_pre_var
        .iter()
        .filter_map(|(name, delta)| (*delta == 0).then_some(name.clone()))
        .collect();
    let target_var_set: FxHashSet<ChcVar> = formals.iter().cloned().collect();
    let mut guard_invariants = Vec::new();
    for guard in normalized.constraint.conjuncts() {
        let Some(inv) =
            super::derive_guard_bridge_invariant(guard, &deltas_by_pre_var, &unchanged_vars)
        else {
            continue;
        };
        let inv = inv.substitute(&pre_to_formal).simplify_constants();
        if inv.vars().iter().all(|var| target_var_set.contains(var)) {
            guard_invariants.push(inv);
        }
    }

    Some(TargetConstantDeltaLoop {
        formals,
        deltas,
        guard_invariants,
    })
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum LinearAtomKind {
    Eq,
    Le,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearExpr {
    coeffs: Vec<i128>,
    constant: i128,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct LinearAtom {
    expr: LinearExpr,
    kind: LinearAtomKind,
}

fn close_transferred_branch_under_constant_delta(
    branch: &ChcExpr,
    target_loop: &TargetConstantDeltaLoop,
    synthesis_stats: Option<&mut AlgebraicValidationStats>,
    verbose: bool,
) -> Option<ChcExpr> {
    let vars_by_name: FxHashMap<String, usize> = target_loop
        .formals
        .iter()
        .enumerate()
        .map(|(idx, var)| (var.name.clone(), idx))
        .collect();

    let mut entry_atoms = Vec::new();
    let mut preserved_extra_exprs = Vec::new();
    for conjunct in branch.conjuncts() {
        if let Some(atom) = parse_linear_atom(conjunct, &vars_by_name) {
            entry_atoms.push(atom);
        } else if let Some(expr) =
            preserved_modulo_atom(conjunct, &vars_by_name, &target_loop.deltas)
        {
            preserved_extra_exprs.push(expr);
        }
    }

    let mut closed_atoms = Vec::new();
    let mut seen_atoms: FxHashSet<String> = FxHashSet::default();
    for atom in &entry_atoms {
        let drift = linear_drift(&atom.expr, &target_loop.deltas);
        if drift == 0 || (atom.kind == LinearAtomKind::Le && drift < 0) {
            push_closed_atom(&mut closed_atoms, &mut seen_atoms, atom.clone());
        }
    }

    derive_closed_equalities(
        &entry_atoms,
        &target_loop.deltas,
        &mut closed_atoms,
        &mut seen_atoms,
    );
    derive_closed_inequalities(
        &entry_atoms,
        &target_loop.deltas,
        &mut closed_atoms,
        &mut seen_atoms,
    );

    let mut closed_exprs: Vec<ChcExpr> = closed_atoms
        .iter()
        .filter_map(|atom| linear_atom_to_expr(atom, &target_loop.formals))
        .collect();

    for expr in
        synthesize_modular_chain_summary_candidates(&entry_atoms, target_loop, synthesis_stats)
    {
        if !closed_exprs.iter().any(|existing| existing == &expr) {
            closed_exprs.push(expr);
        }
    }

    for expr in preserved_extra_exprs {
        if !closed_exprs.iter().any(|existing| existing == &expr) {
            closed_exprs.push(expr);
        }
    }

    for guard_inv in &target_loop.guard_invariants {
        if !closed_exprs.iter().any(|expr| expr == guard_inv) {
            closed_exprs.push(guard_inv.clone());
        }
    }

    if closed_exprs.is_empty() {
        return None;
    }

    let closed = conjoin(closed_exprs).simplify_constants();
    if verbose {
        safe_eprintln!("Algebraic: closed transferred branch {:?}", closed);
    }
    Some(closed)
}

fn synthesize_modular_chain_summary_candidates(
    atoms: &[LinearAtom],
    target_loop: &TargetConstantDeltaLoop,
    mut synthesis_stats: Option<&mut AlgebraicValidationStats>,
) -> Vec<ChcExpr> {
    let mut candidates = Vec::new();
    let mut seen: FxHashSet<String> = FxHashSet::default();

    for atom in atoms {
        if atom.kind != LinearAtomKind::Eq {
            continue;
        }

        let mut normalized_atom = atom.clone();
        normalize_linear_atom(&mut normalized_atom);
        let drift = linear_drift(&normalized_atom.expr, &target_loop.deltas);
        let Some(modulus) = drift.checked_abs() else {
            continue;
        };
        if modulus <= 1 {
            continue;
        }

        let term = linear_expr_to_chc(&normalized_atom.expr, &target_loop.formals);
        let candidate = ChcExpr::eq(
            ChcExpr::mod_op(term, ChcExpr::int(modulus)),
            ChcExpr::int(0),
        )
        .simplify_constants();
        let key = format!("{candidate:?}");
        if seen.insert(key) {
            if let Some(stats) = synthesis_stats.as_deref_mut() {
                stats.record_accelerated_summary_modular_chain_summary_candidate();
            }
            candidates.push(candidate);
        }
    }

    candidates
}

fn derive_closed_equalities(
    atoms: &[LinearAtom],
    deltas: &[i128],
    out: &mut Vec<LinearAtom>,
    seen: &mut FxHashSet<String>,
) {
    let equalities: Vec<&LinearAtom> = atoms
        .iter()
        .filter(|atom| atom.kind == LinearAtomKind::Eq)
        .collect();
    for i in 0..equalities.len() {
        let first = equalities[i];
        let first_drift = linear_drift(&first.expr, deltas);
        if first_drift == 0 {
            continue;
        }
        for second in equalities.iter().copied().skip(i + 1) {
            let second_drift = linear_drift(&second.expr, deltas);
            if second_drift == 0 {
                continue;
            }
            let gcd = gcd_i128(first_drift.abs(), second_drift.abs());
            if gcd == 0 {
                continue;
            }
            let combined = linear_add(
                &linear_scale(&first.expr, second_drift / gcd),
                &linear_scale(&second.expr, -first_drift / gcd),
            );
            push_closed_atom(
                out,
                seen,
                LinearAtom {
                    expr: combined,
                    kind: LinearAtomKind::Eq,
                },
            );
        }
    }
}

fn derive_closed_inequalities(
    atoms: &[LinearAtom],
    deltas: &[i128],
    out: &mut Vec<LinearAtom>,
    seen: &mut FxHashSet<String>,
) {
    let equalities: Vec<&LinearAtom> = atoms
        .iter()
        .filter(|atom| atom.kind == LinearAtomKind::Eq)
        .collect();
    let inequalities: Vec<&LinearAtom> = atoms
        .iter()
        .filter(|atom| atom.kind == LinearAtomKind::Le)
        .collect();

    for inequality in &inequalities {
        let inequality_drift = linear_drift(&inequality.expr, deltas);
        if inequality_drift == 0 {
            continue;
        }
        for equality in &equalities {
            let equality_drift = linear_drift(&equality.expr, deltas);
            if equality_drift == 0 {
                continue;
            }
            let gcd = gcd_i128(inequality_drift.abs(), equality_drift.abs());
            if gcd == 0 {
                continue;
            }
            let inequality_scale = equality_drift.abs() / gcd;
            let numerator = -inequality_scale * inequality_drift;
            if numerator % equality_drift != 0 {
                continue;
            }
            let equality_scale = numerator / equality_drift;
            let combined = linear_add(
                &linear_scale(&inequality.expr, inequality_scale),
                &linear_scale(&equality.expr, equality_scale),
            );
            push_closed_atom(
                out,
                seen,
                LinearAtom {
                    expr: combined,
                    kind: LinearAtomKind::Le,
                },
            );
        }
    }
}

fn push_closed_atom(out: &mut Vec<LinearAtom>, seen: &mut FxHashSet<String>, mut atom: LinearAtom) {
    normalize_linear_atom(&mut atom);
    if linear_atom_is_trivial(&atom) {
        return;
    }
    let key = format!(
        "{:?}:{:?}:{}",
        atom.kind, atom.expr.coeffs, atom.expr.constant
    );
    if seen.insert(key) {
        out.push(atom);
    }
}

fn parse_linear_atom(
    expr: &ChcExpr,
    vars_by_name: &FxHashMap<String, usize>,
) -> Option<LinearAtom> {
    let ChcExpr::Op(op, args) = expr else {
        return None;
    };
    if args.len() == 2 {
        let lhs = parse_linear_expr(&args[0], vars_by_name)?;
        let rhs = parse_linear_expr(&args[1], vars_by_name)?;
        return linear_atom_from_comparison(*op, lhs, rhs);
    }
    if !matches!(op, ChcOp::Not) || args.len() != 1 {
        return None;
    }
    let ChcExpr::Op(inner_op, inner_args) = args[0].as_ref() else {
        return None;
    };
    if inner_args.len() != 2 {
        return None;
    }
    let lhs = parse_linear_expr(&inner_args[0], vars_by_name)?;
    let rhs = parse_linear_expr(&inner_args[1], vars_by_name)?;
    linear_atom_from_negated_comparison(*inner_op, lhs, rhs)
}

fn preserved_modulo_atom(
    expr: &ChcExpr,
    vars_by_name: &FxHashMap<String, usize>,
    deltas: &[i128],
) -> Option<ChcExpr> {
    let ChcExpr::Op(ChcOp::Eq, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let (mod_args, residue_expr) = match (&*args[0], &*args[1]) {
        (ChcExpr::Op(ChcOp::Mod, mod_args), ChcExpr::Int(_)) if mod_args.len() == 2 => {
            (mod_args, &*args[1])
        }
        (ChcExpr::Int(_), ChcExpr::Op(ChcOp::Mod, mod_args)) if mod_args.len() == 2 => {
            (mod_args, &*args[0])
        }
        _ => return None,
    };
    let ChcExpr::Int(modulus) = &*mod_args[1] else {
        return None;
    };
    if *modulus <= 0 || !matches!(residue_expr, ChcExpr::Int(_)) {
        return None;
    }
    let term = parse_linear_expr(&mod_args[0], vars_by_name)?;
    if linear_drift(&term, deltas) % *modulus == 0 {
        Some(expr.clone())
    } else {
        None
    }
}

fn linear_atom_from_comparison(op: ChcOp, lhs: LinearExpr, rhs: LinearExpr) -> Option<LinearAtom> {
    match op {
        ChcOp::Eq => Some(LinearAtom {
            expr: linear_sub(&lhs, &rhs),
            kind: LinearAtomKind::Eq,
        }),
        ChcOp::Le => Some(LinearAtom {
            expr: linear_sub(&lhs, &rhs),
            kind: LinearAtomKind::Le,
        }),
        ChcOp::Ge => Some(LinearAtom {
            expr: linear_sub(&rhs, &lhs),
            kind: LinearAtomKind::Le,
        }),
        ChcOp::Lt => Some(LinearAtom {
            expr: linear_add_constant(&linear_sub(&lhs, &rhs), 1),
            kind: LinearAtomKind::Le,
        }),
        ChcOp::Gt => Some(LinearAtom {
            expr: linear_add_constant(&linear_sub(&rhs, &lhs), 1),
            kind: LinearAtomKind::Le,
        }),
        _ => None,
    }
}

fn linear_atom_from_negated_comparison(
    op: ChcOp,
    lhs: LinearExpr,
    rhs: LinearExpr,
) -> Option<LinearAtom> {
    match op {
        ChcOp::Le => linear_atom_from_comparison(ChcOp::Gt, lhs, rhs),
        ChcOp::Ge => linear_atom_from_comparison(ChcOp::Lt, lhs, rhs),
        ChcOp::Lt => linear_atom_from_comparison(ChcOp::Ge, lhs, rhs),
        ChcOp::Gt => linear_atom_from_comparison(ChcOp::Le, lhs, rhs),
        _ => None,
    }
}

fn parse_linear_expr(
    expr: &ChcExpr,
    vars_by_name: &FxHashMap<String, usize>,
) -> Option<LinearExpr> {
    match expr {
        ChcExpr::Int(value) => Some(LinearExpr {
            coeffs: vec![0; vars_by_name.len()],
            constant: *value,
        }),
        ChcExpr::Var(var) => {
            let idx = *vars_by_name.get(&var.name)?;
            let mut coeffs = vec![0; vars_by_name.len()];
            coeffs[idx] = 1;
            Some(LinearExpr {
                coeffs,
                constant: 0,
            })
        }
        ChcExpr::Op(ChcOp::Add, args) => {
            let mut result = LinearExpr {
                coeffs: vec![0; vars_by_name.len()],
                constant: 0,
            };
            for arg in args {
                result = linear_add(&result, &parse_linear_expr(arg, vars_by_name)?);
            }
            Some(result)
        }
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let lhs = parse_linear_expr(&args[0], vars_by_name)?;
            let rhs = parse_linear_expr(&args[1], vars_by_name)?;
            Some(linear_sub(&lhs, &rhs))
        }
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            parse_linear_expr(&args[0], vars_by_name).map(|expr| linear_scale(&expr, -1))
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => match (&*args[0], &*args[1]) {
            (ChcExpr::Int(coeff), expr) | (expr, ChcExpr::Int(coeff)) => {
                parse_linear_expr(expr, vars_by_name).map(|expr| linear_scale(&expr, *coeff))
            }
            _ => None,
        },
        _ => None,
    }
}

fn linear_atom_to_expr(atom: &LinearAtom, formals: &[ChcVar]) -> Option<ChcExpr> {
    let mut atom = atom.clone();
    normalize_linear_atom(&mut atom);
    if linear_atom_is_trivial(&atom) {
        return None;
    }
    let expr = linear_expr_to_chc(&atom.expr, formals).simplify_constants();
    Some(match atom.kind {
        LinearAtomKind::Eq => ChcExpr::eq(expr, ChcExpr::int(0)).simplify_constants(),
        LinearAtomKind::Le => ChcExpr::le(expr, ChcExpr::int(0)).simplify_constants(),
    })
}

fn linear_expr_to_chc(expr: &LinearExpr, formals: &[ChcVar]) -> ChcExpr {
    let mut terms = Vec::new();
    for (coeff, var) in expr.coeffs.iter().zip(formals.iter()) {
        if *coeff == 0 {
            continue;
        }
        terms.push(scale_chc_linear_term(*coeff, ChcExpr::var(var.clone())));
    }
    if expr.constant != 0 || terms.is_empty() {
        terms.push(ChcExpr::int(expr.constant));
    }
    terms
        .into_iter()
        .reduce(ChcExpr::add)
        .unwrap_or_else(|| ChcExpr::int(0))
        .simplify_constants()
}

fn scale_chc_linear_term(coeff: i128, expr: ChcExpr) -> ChcExpr {
    match coeff {
        0 => ChcExpr::int(0),
        1 => expr,
        -1 => ChcExpr::neg(expr),
        n => ChcExpr::mul(ChcExpr::int(n), expr),
    }
    .simplify_constants()
}

fn linear_drift(expr: &LinearExpr, deltas: &[i128]) -> i128 {
    expr.coeffs
        .iter()
        .zip(deltas.iter())
        .map(|(coeff, delta)| coeff.saturating_mul(*delta))
        .sum()
}

fn linear_add(lhs: &LinearExpr, rhs: &LinearExpr) -> LinearExpr {
    let coeffs = lhs
        .coeffs
        .iter()
        .zip(rhs.coeffs.iter())
        .map(|(a, b)| a.saturating_add(*b))
        .collect();
    LinearExpr {
        coeffs,
        constant: lhs.constant.saturating_add(rhs.constant),
    }
}

fn linear_sub(lhs: &LinearExpr, rhs: &LinearExpr) -> LinearExpr {
    linear_add(lhs, &linear_scale(rhs, -1))
}

fn linear_scale(expr: &LinearExpr, scale: i128) -> LinearExpr {
    LinearExpr {
        coeffs: expr
            .coeffs
            .iter()
            .map(|coeff| coeff.saturating_mul(scale))
            .collect(),
        constant: expr.constant.saturating_mul(scale),
    }
}

fn linear_add_constant(expr: &LinearExpr, constant: i128) -> LinearExpr {
    LinearExpr {
        coeffs: expr.coeffs.clone(),
        constant: expr.constant.saturating_add(constant),
    }
}

fn normalize_linear_atom(atom: &mut LinearAtom) {
    let mut divisor = atom.expr.constant.abs();
    for coeff in &atom.expr.coeffs {
        divisor = gcd_i128(divisor, coeff.abs());
    }
    if divisor > 1 {
        for coeff in &mut atom.expr.coeffs {
            *coeff /= divisor;
        }
        atom.expr.constant /= divisor;
    }

    if atom.kind == LinearAtomKind::Eq {
        let sign = atom
            .expr
            .coeffs
            .iter()
            .copied()
            .find(|coeff| *coeff != 0)
            .or_else(|| (atom.expr.constant != 0).then_some(atom.expr.constant))
            .map(i128::signum)
            .unwrap_or(1);
        if sign < 0 {
            atom.expr = linear_scale(&atom.expr, -1);
        }
    }
}

fn linear_atom_is_trivial(atom: &LinearAtom) -> bool {
    if atom.expr.coeffs.iter().any(|coeff| *coeff != 0) {
        return false;
    }
    match atom.kind {
        LinearAtomKind::Eq => atom.expr.constant == 0,
        LinearAtomKind::Le => atom.expr.constant <= 0,
    }
}

fn gcd_i128(mut a: i128, mut b: i128) -> i128 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a.abs()
}

fn derive_zero_arity_false_invariant(
    problem: &ChcProblem,
    pred: &Predicate,
    incoming: &[&HornClause],
    model: &InvariantModel,
    solved_preds: &FxHashSet<PredicateId>,
    verbose: bool,
) -> Option<ChcExpr> {
    if incoming.is_empty() {
        if verbose {
            safe_eprintln!(
                "Algebraic: zero-arity pred {} has no incoming rules; deriving false",
                pred.name
            );
        }
        return Some(ChcExpr::Bool(false));
    }

    let mut smt = problem.make_smt_context();
    for (idx, clause) in incoming.iter().enumerate() {
        let ClauseHead::Predicate(_, head_args) = &clause.head else {
            continue;
        };
        if !head_args.is_empty() {
            return None;
        }
        let body = zero_arity_clause_body_under_candidate(clause, pred.id, model, solved_preds)?;
        let proof_body = zero_arity_linear_unsat_projection(&body).unwrap_or_else(|| body.clone());
        match prove_formula_unsat(&mut smt, &proof_body) {
            FormulaUnsatProof::Unsat => {}
            reason => {
                if verbose {
                    let source_preds: Vec<PredicateId> = clause
                        .body
                        .predicates
                        .iter()
                        .map(|(pred, _)| *pred)
                        .collect();
                    safe_eprintln!(
                        "Algebraic: zero-arity pred {} incoming #{idx} from {:?} not proved unreachable ({:?})",
                        pred.name,
                        source_preds,
                        reason
                    );
                }
                return None;
            }
        }
    }

    if verbose {
        safe_eprintln!(
            "Algebraic: zero-arity pred {} proved unreachable; deriving false",
            pred.name
        );
    }
    Some(ChcExpr::Bool(false))
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
struct LinearInterval {
    lower: Option<i128>,
    upper: Option<i128>,
}

impl LinearInterval {
    fn top() -> Self {
        Self {
            lower: None,
            upper: None,
        }
    }

    fn exact(value: i128) -> Self {
        Self {
            lower: Some(value),
            upper: Some(value),
        }
    }

    fn lower(value: i128) -> Self {
        Self {
            lower: Some(value),
            upper: None,
        }
    }

    fn upper(value: i128) -> Self {
        Self {
            lower: None,
            upper: Some(value),
        }
    }

    fn is_empty(self) -> bool {
        matches!((self.lower, self.upper), (Some(lower), Some(upper)) if lower > upper)
    }

    fn intersect(self, other: Self) -> Self {
        Self {
            lower: match (self.lower, other.lower) {
                (Some(a), Some(b)) => Some(a.max(b)),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            },
            upper: match (self.upper, other.upper) {
                (Some(a), Some(b)) => Some(a.min(b)),
                (Some(a), None) | (None, Some(a)) => Some(a),
                (None, None) => None,
            },
        }
    }

    fn checked_add(self, other: Self) -> Self {
        Self {
            lower: match (self.lower, other.lower) {
                (Some(a), Some(b)) => a.checked_add(b),
                _ => None,
            },
            upper: match (self.upper, other.upper) {
                (Some(a), Some(b)) => a.checked_add(b),
                _ => None,
            },
        }
    }

    fn checked_neg(self) -> Self {
        Self {
            lower: self.upper.and_then(i128::checked_neg),
            upper: self.lower.and_then(i128::checked_neg),
        }
    }

    fn checked_sub(self, other: Self) -> Self {
        self.checked_add(other.checked_neg())
    }

    fn checked_scale(self, factor: i128) -> Self {
        if factor == 0 {
            return Self::exact(0);
        }
        let lower = self.lower.and_then(|value| value.checked_mul(factor));
        let upper = self.upper.and_then(|value| value.checked_mul(factor));
        if factor > 0 {
            Self { lower, upper }
        } else {
            Self {
                lower: upper,
                upper: lower,
            }
        }
    }
}

fn zero_arity_linear_unsat_projection(body: &ChcExpr) -> Option<ChcExpr> {
    let simplified = body.simplify_constants();
    let conjuncts: Vec<ChcExpr> = simplified.conjuncts().into_iter().cloned().collect();
    let mut env = FxHashMap::default();
    if !collect_zero_arity_interval_bounds(&conjuncts, &mut env) {
        return Some(ChcExpr::Bool(false));
    }

    let mut remove = vec![false; conjuncts.len()];
    let mut derived = Vec::new();
    for (idx, conjunct) in conjuncts.iter().enumerate() {
        let Some((sum_var, counter_var)) = triangular_accumulator_identity(conjunct) else {
            continue;
        };
        let Some(counter_interval) = env.get(&counter_var.name).copied() else {
            continue;
        };
        let (Some(counter_lower), Some(counter_upper)) =
            (counter_interval.lower, counter_interval.upper)
        else {
            continue;
        };
        if counter_lower < 0
            || !(0..=ZERO_ARITY_TRIANGULAR_MAX_COUNTER_UPPER).contains(&counter_upper)
        {
            continue;
        }
        let Some(sum_upper) = triangular_bound(counter_upper, false) else {
            continue;
        };
        let Some(sum_plus_counter_upper) = triangular_bound(counter_upper, true) else {
            continue;
        };

        let sum = ChcExpr::var(sum_var);
        let counter = ChcExpr::var(counter_var);
        derived.push(ChcExpr::ge(sum.clone(), ChcExpr::int(0)));
        derived.push(ChcExpr::le(sum.clone(), ChcExpr::int(sum_upper)));
        derived.push(ChcExpr::le(
            ChcExpr::add(sum, counter).simplify_constants(),
            ChcExpr::int(sum_plus_counter_upper),
        ));
        remove[idx] = true;
    }

    if derived.is_empty() {
        return None;
    }

    let mut projection = Vec::with_capacity(conjuncts.len() + derived.len());
    for (idx, conjunct) in conjuncts.into_iter().enumerate() {
        if !remove[idx] {
            projection.push(conjunct);
        }
    }
    projection.extend(derived);

    let mut env = FxHashMap::default();
    if !collect_zero_arity_interval_bounds(&projection, &mut env) {
        return Some(ChcExpr::Bool(false));
    }
    let simplified = projection
        .into_iter()
        .map(|expr| simplify_zero_arity_interval_expr(&expr, &env))
        .collect::<Vec<_>>();
    Some(ChcExpr::and_all(simplified).simplify_constants())
}

fn triangular_bound(counter_upper: i128, include_counter: bool) -> Option<i128> {
    let rhs = if include_counter {
        counter_upper.checked_add(1)?
    } else {
        counter_upper.checked_sub(1)?
    };
    Some(counter_upper.checked_mul(rhs)? / 2)
}

fn collect_zero_arity_interval_bounds(
    conjuncts: &[ChcExpr],
    env: &mut FxHashMap<String, LinearInterval>,
) -> bool {
    let max_rounds = conjuncts.len().saturating_add(4).clamp(1, 32);
    for _ in 0..max_rounds {
        let before = env.clone();
        for conjunct in conjuncts {
            if !collect_zero_arity_interval_bound(conjunct, env) {
                return false;
            }
        }
        for conjunct in conjuncts {
            if !propagate_zero_arity_var_bound(conjunct, env) {
                return false;
            }
        }
        if *env == before {
            return true;
        }
    }
    true
}

fn collect_zero_arity_interval_bound(
    conjunct: &ChcExpr,
    env: &mut FxHashMap<String, LinearInterval>,
) -> bool {
    let simplified = conjunct.simplify_constants();
    if let Some((op, lhs, rhs)) = interval_atom(&simplified) {
        return collect_zero_arity_direct_bound(op, lhs, rhs, env);
    }
    if let ChcExpr::Op(ChcOp::Not, args) = &simplified {
        if args.len() == 1 {
            if let Some((op, lhs, rhs)) = interval_atom(args[0].as_ref()) {
                return collect_zero_arity_direct_bound(negated_comparison(op), lhs, rhs, env);
            }
        }
    }
    true
}

fn collect_zero_arity_direct_bound(
    op: ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    env: &mut FxHashMap<String, LinearInterval>,
) -> bool {
    match op {
        ChcOp::Eq => {
            if let (Some(name), Some(value)) = (int_var_name(lhs), rhs.as_i128()) {
                return add_zero_arity_interval(env, name, LinearInterval::exact(value));
            }
            if let (Some(value), Some(name)) = (lhs.as_i128(), int_var_name(rhs)) {
                return add_zero_arity_interval(env, name, LinearInterval::exact(value));
            }
        }
        ChcOp::Le => {
            if let (Some(name), Some(value)) = (int_var_name(lhs), rhs.as_i128()) {
                return add_zero_arity_interval(env, name, LinearInterval::upper(value));
            }
            if let (Some(value), Some(name)) = (lhs.as_i128(), int_var_name(rhs)) {
                return add_zero_arity_interval(env, name, LinearInterval::lower(value));
            }
        }
        ChcOp::Lt => {
            if let (Some(name), Some(value)) = (int_var_name(lhs), rhs.as_i128()) {
                return value.checked_sub(1).is_some_and(|upper| {
                    add_zero_arity_interval(env, name, LinearInterval::upper(upper))
                });
            }
            if let (Some(value), Some(name)) = (lhs.as_i128(), int_var_name(rhs)) {
                return value.checked_add(1).is_some_and(|lower| {
                    add_zero_arity_interval(env, name, LinearInterval::lower(lower))
                });
            }
        }
        ChcOp::Ge => return collect_zero_arity_direct_bound(ChcOp::Le, rhs, lhs, env),
        ChcOp::Gt => return collect_zero_arity_direct_bound(ChcOp::Lt, rhs, lhs, env),
        _ => {}
    }
    true
}

fn propagate_zero_arity_var_bound(
    conjunct: &ChcExpr,
    env: &mut FxHashMap<String, LinearInterval>,
) -> bool {
    let simplified = conjunct.simplify_constants();
    let Some((op, lhs, rhs)) = interval_atom(&simplified) else {
        return true;
    };
    propagate_zero_arity_var_bound_atom(op, lhs, rhs, env)
}

fn propagate_zero_arity_var_bound_atom(
    op: ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    env: &mut FxHashMap<String, LinearInterval>,
) -> bool {
    match op {
        ChcOp::Le | ChcOp::Lt => {
            let (Some(lhs_name), Some(rhs_name)) = (int_var_name(lhs), int_var_name(rhs)) else {
                return true;
            };
            let strict = matches!(op, ChcOp::Lt);
            if let Some(rhs_upper) = env.get(rhs_name).and_then(|interval| interval.upper) {
                let Some(lhs_upper) = (if strict {
                    rhs_upper.checked_sub(1)
                } else {
                    Some(rhs_upper)
                }) else {
                    return false;
                };
                if !add_zero_arity_interval(env, lhs_name, LinearInterval::upper(lhs_upper)) {
                    return false;
                }
            }
            if let Some(lhs_lower) = env.get(lhs_name).and_then(|interval| interval.lower) {
                let Some(rhs_lower) = (if strict {
                    lhs_lower.checked_add(1)
                } else {
                    Some(lhs_lower)
                }) else {
                    return false;
                };
                if !add_zero_arity_interval(env, rhs_name, LinearInterval::lower(rhs_lower)) {
                    return false;
                }
            }
            true
        }
        ChcOp::Ge => propagate_zero_arity_var_bound_atom(ChcOp::Le, rhs, lhs, env),
        ChcOp::Gt => propagate_zero_arity_var_bound_atom(ChcOp::Lt, rhs, lhs, env),
        _ => true,
    }
}

fn add_zero_arity_interval(
    env: &mut FxHashMap<String, LinearInterval>,
    name: &str,
    interval: LinearInterval,
) -> bool {
    let merged = env
        .get(name)
        .copied()
        .map_or(interval, |current| current.intersect(interval));
    if merged.is_empty() {
        return false;
    }
    env.insert(name.to_string(), merged);
    true
}

fn simplify_zero_arity_interval_expr(
    expr: &ChcExpr,
    env: &FxHashMap<String, LinearInterval>,
) -> ChcExpr {
    match expr {
        ChcExpr::Op(op, args) => {
            let simplified_args: Vec<_> = args
                .iter()
                .map(|arg| simplify_zero_arity_interval_expr(arg.as_ref(), env))
                .collect();
            match op {
                ChcOp::Not if simplified_args.len() == 1 => match &simplified_args[0] {
                    ChcExpr::Bool(value) => ChcExpr::Bool(!value),
                    ChcExpr::Op(ChcOp::Not, inner) if inner.len() == 1 => inner[0].as_ref().clone(),
                    other => ChcExpr::not(other.clone()).simplify_constants(),
                },
                ChcOp::And => ChcExpr::and_all(simplified_args),
                ChcOp::Or => ChcExpr::or_all(simplified_args),
                ChcOp::Implies if simplified_args.len() == 2 => ChcExpr::or(
                    ChcExpr::not(simplified_args[0].clone()),
                    simplified_args[1].clone(),
                )
                .simplify_constants(),
                ChcOp::Eq if simplified_args.len() == 2 => {
                    if let Some(result) = interval_compare_result(
                        ChcOp::Eq,
                        &simplified_args[0],
                        &simplified_args[1],
                        env,
                    ) {
                        return ChcExpr::Bool(result);
                    }
                    simplify_bool_equality(
                        simplified_args[0].clone(),
                        simplified_args[1].clone(),
                        false,
                    )
                }
                ChcOp::Ne if simplified_args.len() == 2 => {
                    if let Some(result) = interval_compare_result(
                        ChcOp::Ne,
                        &simplified_args[0],
                        &simplified_args[1],
                        env,
                    ) {
                        return ChcExpr::Bool(result);
                    }
                    simplify_bool_equality(
                        simplified_args[0].clone(),
                        simplified_args[1].clone(),
                        true,
                    )
                }
                ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge if simplified_args.len() == 2 => {
                    if let Some(result) =
                        interval_compare_result(*op, &simplified_args[0], &simplified_args[1], env)
                    {
                        ChcExpr::Bool(result)
                    } else {
                        ChcExpr::Op(*op, simplified_args.into_iter().map(Arc::new).collect())
                            .simplify_constants()
                    }
                }
                ChcOp::Ite if simplified_args.len() == 3 => match &simplified_args[0] {
                    ChcExpr::Bool(true) => simplified_args[1].clone(),
                    ChcExpr::Bool(false) => simplified_args[2].clone(),
                    _ => ChcExpr::Op(*op, simplified_args.into_iter().map(Arc::new).collect())
                        .simplify_constants(),
                },
                _ => ChcExpr::Op(*op, simplified_args.into_iter().map(Arc::new).collect())
                    .simplify_constants(),
            }
        }
        ChcExpr::PredicateApp(name, pred, args) => ChcExpr::PredicateApp(
            name.clone(),
            *pred,
            args.iter()
                .map(|arg| Arc::new(simplify_zero_arity_interval_expr(arg.as_ref(), env)))
                .collect(),
        ),
        ChcExpr::FuncApp(name, sort, args) => ChcExpr::FuncApp(
            name.clone(),
            sort.clone(),
            args.iter()
                .map(|arg| Arc::new(simplify_zero_arity_interval_expr(arg.as_ref(), env)))
                .collect(),
        ),
        ChcExpr::ConstArray(key_sort, value) => ChcExpr::ConstArray(
            key_sort.clone(),
            Arc::new(simplify_zero_arity_interval_expr(value.as_ref(), env)),
        ),
        other => other.clone(),
    }
}

fn simplify_bool_equality(lhs: ChcExpr, rhs: ChcExpr, negated: bool) -> ChcExpr {
    let result = match (lhs, rhs) {
        (ChcExpr::Bool(a), ChcExpr::Bool(b)) => ChcExpr::Bool(a == b),
        (ChcExpr::Bool(true), other) | (other, ChcExpr::Bool(true)) => other,
        (ChcExpr::Bool(false), other) | (other, ChcExpr::Bool(false)) => ChcExpr::not(other),
        (a, b) => ChcExpr::eq(a, b).simplify_constants(),
    };
    if negated {
        ChcExpr::not(result).simplify_constants()
    } else {
        result.simplify_constants()
    }
}

fn interval_compare_result(
    op: ChcOp,
    lhs: &ChcExpr,
    rhs: &ChcExpr,
    env: &FxHashMap<String, LinearInterval>,
) -> Option<bool> {
    let lhs_interval = expr_linear_interval(lhs, env)?;
    let rhs_interval = expr_linear_interval(rhs, env)?;
    match op {
        ChcOp::Lt => {
            if lhs_interval.upper? < rhs_interval.lower? {
                Some(true)
            } else if lhs_interval.lower? >= rhs_interval.upper? {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Le => {
            if lhs_interval.upper? <= rhs_interval.lower? {
                Some(true)
            } else if lhs_interval.lower? > rhs_interval.upper? {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Gt => {
            if lhs_interval.lower? > rhs_interval.upper? {
                Some(true)
            } else if lhs_interval.upper? <= rhs_interval.lower? {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Ge => {
            if lhs_interval.lower? >= rhs_interval.upper? {
                Some(true)
            } else if lhs_interval.upper? < rhs_interval.lower? {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Eq => {
            if lhs_interval.lower == lhs_interval.upper
                && lhs_interval.lower == rhs_interval.lower
                && rhs_interval.lower == rhs_interval.upper
            {
                Some(true)
            } else if lhs_interval.upper? < rhs_interval.lower?
                || rhs_interval.upper? < lhs_interval.lower?
            {
                Some(false)
            } else {
                None
            }
        }
        ChcOp::Ne => {
            if lhs_interval.lower == lhs_interval.upper
                && lhs_interval.lower == rhs_interval.lower
                && rhs_interval.lower == rhs_interval.upper
            {
                Some(false)
            } else if lhs_interval.upper? < rhs_interval.lower?
                || rhs_interval.upper? < lhs_interval.lower?
            {
                Some(true)
            } else {
                None
            }
        }
        _ => None,
    }
}

fn expr_linear_interval(
    expr: &ChcExpr,
    env: &FxHashMap<String, LinearInterval>,
) -> Option<LinearInterval> {
    match expr {
        ChcExpr::Int(value) => Some(LinearInterval::exact(*value)),
        ChcExpr::Var(var) if var.sort == ChcSort::Int => Some(
            env.get(&var.name)
                .copied()
                .unwrap_or_else(LinearInterval::top),
        ),
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => {
            Some(expr_linear_interval(args[0].as_ref(), env)?.checked_neg())
        }
        ChcExpr::Op(ChcOp::Add, args) if !args.is_empty() => {
            let mut interval = LinearInterval::exact(0);
            for arg in args {
                interval = interval.checked_add(expr_linear_interval(arg.as_ref(), env)?);
            }
            Some(interval)
        }
        ChcExpr::Op(ChcOp::Sub, args) if !args.is_empty() => {
            let mut iter = args.iter();
            let first = expr_linear_interval(iter.next()?.as_ref(), env)?;
            if args.len() == 1 {
                return Some(first.checked_neg());
            }
            let mut interval = first;
            for arg in iter {
                interval = interval.checked_sub(expr_linear_interval(arg.as_ref(), env)?);
            }
            Some(interval)
        }
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            if let Some(factor) = args[0].as_i128() {
                return Some(expr_linear_interval(args[1].as_ref(), env)?.checked_scale(factor));
            }
            if let Some(factor) = args[1].as_i128() {
                return Some(expr_linear_interval(args[0].as_ref(), env)?.checked_scale(factor));
            }
            Some(LinearInterval::top())
        }
        _ if matches!(expr.sort(), ChcSort::Int) => Some(LinearInterval::top()),
        _ => None,
    }
}

fn interval_atom(expr: &ChcExpr) -> Option<(ChcOp, &ChcExpr, &ChcExpr)> {
    let ChcExpr::Op(op @ (ChcOp::Eq | ChcOp::Lt | ChcOp::Le | ChcOp::Gt | ChcOp::Ge), args) = expr
    else {
        return None;
    };
    if args.len() == 2 {
        Some((*op, args[0].as_ref(), args[1].as_ref()))
    } else {
        None
    }
}

fn negated_comparison(op: ChcOp) -> ChcOp {
    match op {
        ChcOp::Lt => ChcOp::Ge,
        ChcOp::Le => ChcOp::Gt,
        ChcOp::Gt => ChcOp::Le,
        ChcOp::Ge => ChcOp::Lt,
        ChcOp::Eq => ChcOp::Ne,
        other => other,
    }
}

fn int_var_name(expr: &ChcExpr) -> Option<&str> {
    match expr {
        ChcExpr::Var(var) if var.sort == ChcSort::Int => Some(var.name.as_str()),
        _ => None,
    }
}

fn triangular_accumulator_identity(expr: &ChcExpr) -> Option<(ChcVar, ChcVar)> {
    let simplified = expr.simplify_constants();
    let ChcExpr::Op(ChcOp::Eq, args) = &simplified else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    triangular_accumulator_identity_sides(args[0].as_ref(), args[1].as_ref())
        .or_else(|| triangular_accumulator_identity_sides(args[1].as_ref(), args[0].as_ref()))
}

fn triangular_accumulator_identity_sides(lhs: &ChcExpr, rhs: &ChcExpr) -> Option<(ChcVar, ChcVar)> {
    let sum_var = twice_int_var(lhs)?;
    let counter_var = triangular_counter_expr(rhs)?;
    (sum_var.sort == ChcSort::Int && counter_var.sort == ChcSort::Int)
        .then_some((sum_var, counter_var))
}

fn twice_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    let ChcExpr::Op(ChcOp::Mul, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    match (args[0].as_ref(), args[1].as_ref()) {
        (ChcExpr::Int(2), ChcExpr::Var(var)) | (ChcExpr::Var(var), ChcExpr::Int(2))
            if var.sort == ChcSort::Int =>
        {
            Some(var.clone())
        }
        _ => None,
    }
}

fn triangular_counter_expr(expr: &ChcExpr) -> Option<ChcVar> {
    if let Some(var) = triangular_counter_product(expr) {
        return Some(var);
    }

    match expr {
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            let square_var = square_int_var(args[0].as_ref())?;
            let minus_var = plain_int_var(args[1].as_ref())?;
            (square_var == minus_var).then_some(square_var)
        }
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            triangular_counter_square_minus_var(args[0].as_ref(), args[1].as_ref())
                .or_else(|| triangular_counter_square_minus_var(args[1].as_ref(), args[0].as_ref()))
        }
        _ => None,
    }
}

fn triangular_counter_square_minus_var(square: &ChcExpr, minus: &ChcExpr) -> Option<ChcVar> {
    let square_var = square_int_var(square)?;
    let minus_var = negated_int_var(minus)?;
    (square_var == minus_var).then_some(square_var)
}

fn triangular_counter_product(expr: &ChcExpr) -> Option<ChcVar> {
    let ChcExpr::Op(ChcOp::Mul, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    product_counter_minus_one(args[0].as_ref(), args[1].as_ref())
        .or_else(|| product_counter_minus_one(args[1].as_ref(), args[0].as_ref()))
}

fn product_counter_minus_one(counter: &ChcExpr, dec: &ChcExpr) -> Option<ChcVar> {
    let counter_var = plain_int_var(counter)?;
    let dec_var = decrement_int_var(dec)?;
    (counter_var == dec_var).then_some(counter_var)
}

fn square_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    let ChcExpr::Op(ChcOp::Mul, args) = expr else {
        return None;
    };
    if args.len() != 2 {
        return None;
    }
    let lhs = plain_int_var(args[0].as_ref())?;
    let rhs = plain_int_var(args[1].as_ref())?;
    (lhs == rhs).then_some(lhs)
}

fn plain_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Var(var) if var.sort == ChcSort::Int => Some(var.clone()),
        _ => None,
    }
}

fn negated_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Op(ChcOp::Neg, args) if args.len() == 1 => plain_int_var(args[0].as_ref()),
        ChcExpr::Op(ChcOp::Mul, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Int(-1), ChcExpr::Var(var)) | (ChcExpr::Var(var), ChcExpr::Int(-1))
                    if var.sort == ChcSort::Int =>
                {
                    Some(var.clone())
                }
                _ => None,
            }
        }
        _ => None,
    }
}

fn decrement_int_var(expr: &ChcExpr) -> Option<ChcVar> {
    match expr {
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 && args[1].as_i64() == Some(1) => {
            plain_int_var(args[0].as_ref())
        }
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            if args[0].as_i64() == Some(-1) {
                return plain_int_var(args[1].as_ref());
            }
            if args[1].as_i64() == Some(-1) {
                return plain_int_var(args[0].as_ref());
            }
            None
        }
        _ => None,
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum FormulaUnsatProof {
    Unsat,
    ContainsUnsupportedTheory,
    SatOrUnknown,
}

fn prove_formula_unsat(smt: &mut SmtContext, formula: &ChcExpr) -> FormulaUnsatProof {
    let formula = formula.simplify_constants();
    if matches!(formula, ChcExpr::Bool(false)) || is_trivial_contradiction(&formula) {
        return FormulaUnsatProof::Unsat;
    }

    if formula.contains_mod_or_div() || formula.contains_array_ops() {
        return FormulaUnsatProof::ContainsUnsupportedTheory;
    }

    smt.reset();
    if matches!(
        smt.check_sat_with_timeout(&formula, ZERO_ARITY_TRANSFER_TIMEOUT),
        SmtResult::Unsat | SmtResult::UnsatWithCore(_) | SmtResult::UnsatWithFarkas(_)
    ) {
        FormulaUnsatProof::Unsat
    } else {
        FormulaUnsatProof::SatOrUnknown
    }
}

fn zero_arity_clause_body_under_candidate(
    clause: &HornClause,
    target_pred: PredicateId,
    model: &InvariantModel,
    solved_preds: &FxHashSet<PredicateId>,
) -> Option<ChcExpr> {
    let mut conjuncts = Vec::new();
    for (body_pred, args) in &clause.body.predicates {
        if *body_pred == target_pred {
            conjuncts.push(ChcExpr::Bool(false));
            continue;
        }
        if !solved_preds.contains(body_pred) {
            return None;
        }
        let interp = model.get(body_pred)?;
        let substitution: Vec<(ChcVar, ChcExpr)> = interp
            .vars
            .iter()
            .zip(args.iter())
            .map(|(v, a)| (v.clone(), a.clone()))
            .collect();
        conjuncts.push(interp.formula.substitute(&substitution));
    }
    if let Some(constraint) = &clause.body.constraint {
        conjuncts.push(constraint.clone());
    }
    Some(conjoin(conjuncts).simplify_constants())
}

fn extract_var_defs(constraint: &ChcExpr) -> FxHashMap<String, ChcExpr> {
    let mut var_defs: FxHashMap<String, ChcExpr> = FxHashMap::default();
    for conj in constraint.conjuncts() {
        if let ChcExpr::Op(ChcOp::Eq, args) = conj {
            if args.len() == 2 {
                if let ChcExpr::Var(v) = &*args[0] {
                    var_defs.insert(v.name.clone(), (*args[1]).clone());
                }
                if let ChcExpr::Var(v) = &*args[1] {
                    if !var_defs.contains_key(&v.name) {
                        var_defs.insert(v.name.clone(), (*args[0]).clone());
                    }
                }
            }
        }
    }
    var_defs
}

fn is_self_loop_clause(clause: &HornClause, pred_id: PredicateId) -> bool {
    clause.head.predicate_id() == Some(pred_id)
        && clause.body.predicates.len() == 1
        && clause.body.predicates[0].0 == pred_id
}

fn head_to_formal_substitution(
    head_args: &[ChcExpr],
    var_defs: &FxHashMap<String, ChcExpr>,
    target_formals: &[ChcVar],
) -> Vec<(ChcVar, ChcExpr)> {
    let mut subst = Vec::new();
    for (i, ha) in head_args.iter().enumerate() {
        let Some(formal) = target_formals.get(i).cloned() else {
            continue;
        };
        let formal_expr = ChcExpr::var(formal.clone());
        let ChcExpr::Var(hv) = ha else {
            continue;
        };

        push_subst_once(&mut subst, hv.clone(), formal_expr.clone());
        if let Some(def) = var_defs.get(&hv.name) {
            match def {
                ChcExpr::Var(body_var) => {
                    push_subst_once(&mut subst, body_var.clone(), formal_expr);
                }
                ChcExpr::Op(ChcOp::Add, add_args)
                    if add_args.len() == 2 && matches!(&formal.sort, ChcSort::Int) =>
                {
                    match (&*add_args[0], &*add_args[1]) {
                        (ChcExpr::Int(c), ChcExpr::Var(bv))
                        | (ChcExpr::Var(bv), ChcExpr::Int(c)) => {
                            push_subst_once(
                                &mut subst,
                                bv.clone(),
                                ChcExpr::add(ChcExpr::var(formal), ChcExpr::int(-c))
                                    .simplify_constants(),
                            );
                        }
                        _ => {}
                    }
                }
                ChcExpr::Op(ChcOp::Sub, sub_args)
                    if sub_args.len() == 2 && matches!(&formal.sort, ChcSort::Int) =>
                {
                    if let (ChcExpr::Var(bv), ChcExpr::Int(c)) = (&*sub_args[0], &*sub_args[1]) {
                        push_subst_once(
                            &mut subst,
                            bv.clone(),
                            ChcExpr::add(ChcExpr::var(formal), ChcExpr::int(*c))
                                .simplify_constants(),
                        );
                    }
                }
                _ => {}
            }
        }
    }
    subst
}

fn push_subst_once(subst: &mut Vec<(ChcVar, ChcExpr)>, var: ChcVar, expr: ChcExpr) {
    if !subst.iter().any(|(existing, _)| existing == &var) {
        subst.push((var, expr));
    }
}

fn transferable_target_formula(
    expr: ChcExpr,
    target_var_set: &FxHashSet<ChcVar>,
) -> Option<ChcExpr> {
    let expr = expr.simplify_constants();
    if matches!(expr, ChcExpr::Bool(true)) {
        return None;
    }
    if expr.vars().iter().all(|var| target_var_set.contains(var)) && expr.sort() == ChcSort::Bool {
        Some(expr)
    } else {
        None
    }
}
