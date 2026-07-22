// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

use super::*;

impl PdrSolver {
    /// Propagate bound invariants to predicates without fact clauses.
    /// For each predicate without facts, check if bound invariants from source predicates
    /// are enforced by incoming transitions and preserved by self-transitions.
    pub(in crate::pdr::solver) fn propagate_bound_invariants(&mut self) {
        let predicates: Vec<_> = self.problem.predicates().to_vec();

        // Phase 0: Direct bound discovery for predicates without facts using init values
        // This handles computed expressions in head arguments (e.g., C = A + 128)
        for pred in &predicates {
            if self.predicate_has_facts(pred.id) {
                continue;
            }
            if !self.predicate_is_reachable(pred.id) {
                continue;
            }
            // For no-facts predicates reached from sources that also have transition
            // clauses, get_init_values() is fact-seeded and can over-constrain the
            // entry domain. Phase-0 bounds from that data can be unsound.
            if self.has_transitioning_source_predicate(pred.id) {
                if self.config.verbose {
                    safe_eprintln!(
                        "PDR: skipping phase-0 no-facts bounds for pred {} (incoming source has transitions)",
                        pred.id.index()
                    );
                }
                continue;
            }

            let canonical_vars = match self.canonical_vars(pred.id) {
                Some(v) => v.to_vec(),
                None => continue,
            };

            // Get init values for this predicate (handles computed expressions)
            let init_values = self.get_init_values(pred.id);

            for var in &canonical_vars {
                if !matches!(var.sort, ChcSort::Int) {
                    continue;
                }

                let init_bounds = match init_values.get(&var.name) {
                    Some(bounds) if bounds.is_valid() => bounds,
                    _ => continue,
                };

                // Check if bounds are constant (min == max)
                if init_bounds.min == init_bounds.max {
                    let init_val = init_bounds.min;

                    // Check if variable is monotonically non-decreasing
                    if self.is_var_non_decreasing(pred.id, var, init_val) {
                        let bound_invariant =
                            ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(init_val));

                        let already_known = self.frames.len() > 1
                            && self.frames[1]
                                .lemmas
                                .iter()
                                .any(|l| l.predicate == pred.id && l.formula == bound_invariant);

                        if !already_known {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered lower bound invariant for pred {} (no facts): {} >= {}",
                                    pred.id.index(),
                                    var.name,
                                    init_val
                                );
                            }

                            self.add_discovered_invariant(pred.id, bound_invariant, 1);
                        }
                    }

                    // Check if variable is monotonically non-increasing
                    if self.is_var_non_increasing(pred.id, var, init_val) {
                        let bound_invariant =
                            ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(init_val));

                        let already_known = self.frames.len() > 1
                            && self.frames[1]
                                .lemmas
                                .iter()
                                .any(|l| l.predicate == pred.id && l.formula == bound_invariant);

                        if !already_known {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered upper bound invariant for pred {} (no facts): {} <= {}",
                                    pred.id.index(),
                                    var.name,
                                    init_val
                                );
                            }

                            self.add_discovered_invariant(pred.id, bound_invariant, 1);
                        }
                    }
                } else {
                    // Range bounds
                    if init_bounds.min > i128::MIN
                        && self.is_var_non_decreasing(pred.id, var, init_bounds.min)
                    {
                        let bound_invariant =
                            ChcExpr::ge(ChcExpr::var(var.clone()), ChcExpr::Int(init_bounds.min));

                        let already_known = self.frames.len() > 1
                            && self.frames[1]
                                .lemmas
                                .iter()
                                .any(|l| l.predicate == pred.id && l.formula == bound_invariant);

                        if !already_known {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered range lower bound invariant for pred {} (no facts): {} >= {}",
                                    pred.id.index(),
                                    var.name,
                                    init_bounds.min
                                );
                            }

                            self.add_discovered_invariant(pred.id, bound_invariant, 1);
                        }
                    }

                    if init_bounds.max < i128::MAX
                        && self.is_var_non_increasing(pred.id, var, init_bounds.max)
                    {
                        let bound_invariant =
                            ChcExpr::le(ChcExpr::var(var.clone()), ChcExpr::Int(init_bounds.max));

                        let already_known = self.frames.len() > 1
                            && self.frames[1]
                                .lemmas
                                .iter()
                                .any(|l| l.predicate == pred.id && l.formula == bound_invariant);

                        if !already_known {
                            if self.config.verbose {
                                safe_eprintln!(
                                    "PDR: Discovered range upper bound invariant for pred {} (no facts): {} <= {}",
                                    pred.id.index(),
                                    var.name,
                                    init_bounds.max
                                );
                            }

                            self.add_discovered_invariant(pred.id, bound_invariant, 1);
                        }
                    }
                }
            }
        }

        // Phase 1: Propagate bounds to a fixpoint across predicate chains.
        //
        // Single-pass propagation only reaches direct successors of predicates with facts, but
        // phase-chain benchmarks (e.g. gj2007) require multi-hop propagation: inv → inv2 → … → inv5.
        // We therefore treat each discovered bound as a work item and keep propagating until
        // no new bounds are added to frame 1.
        if self.frames.len() <= 1 {
            return;
        }

        let mut worklist: VecDeque<(PredicateId, usize, i128, bool)> = VecDeque::new(); // (pred, var_idx, bound, is_lower)
                                                                                        // Track which work items have been enqueued/processed. This prevents reprocessing a bound
                                                                                        // lemma once it's part of frame 1 (but still allows retrying candidates that were rejected).
        let mut seen_work: FxHashSet<(PredicateId, usize, i128, bool)> = FxHashSet::default();

        let mut enqueue_work_item =
            |pred: PredicateId, var_name: &str, bound: i128, is_lower: bool| {
                let canonical_vars = match self.canonical_vars(pred) {
                    Some(vars) => vars,
                    None => return,
                };
                let Some(idx) = canonical_vars.iter().position(|cv| cv.name == var_name) else {
                    return;
                };
                if !matches!(canonical_vars[idx].sort, ChcSort::Int) {
                    return;
                }

                let item = (pred, idx, bound, is_lower);
                if seen_work.insert(item) {
                    worklist.push_back(item);
                }
            };

        for lemma in &self.frames[1].lemmas {
            extract_bounds_from_formula(&lemma.formula, lemma.predicate, &mut enqueue_work_item);
        }

        if self.config.verbose && !worklist.is_empty() {
            safe_eprintln!(
                "PDR: propagate_bound_invariants Phase 1: {} worklist items",
                worklist.len()
            );
        }

        if worklist.is_empty() {
            return;
        }

        // Precompute argument passthrough adjacency with optional affine shift:
        // (body_pred, body_arg_idx) -> [(head_pred, head_arg_idx, shift), ...]
        //
        // A shift of 0 means direct passthrough (body_var == head_var).
        // A nonzero shift means the clause constraint defines head_var = body_var + shift,
        // so bound `body_var >= b` becomes `head_var >= b + shift`.
        //
        // This avoids rescanning all predicates/clauses for every work item.
        let mut adjacency: FxHashMap<(PredicateId, usize), Vec<(PredicateId, usize, i128)>> =
            FxHashMap::default();
        let mut adjacency_seen: FxHashSet<(PredicateId, usize, PredicateId, usize)> =
            FxHashSet::default();

        for pred in &predicates {
            // Only propagate *to* predicates without facts.
            if self.predicate_has_facts(pred.id) {
                continue;
            }
            if !self.predicate_is_reachable(pred.id) {
                continue;
            }

            let Some(target_vars) = self.canonical_vars(pred.id) else {
                continue;
            };

            for clause in self.problem.clauses_defining(pred.id) {
                if clause.body.predicates.len() != 1 {
                    continue;
                }
                let (body_pred, body_args) = &clause.body.predicates[0];

                let head_args = match &clause.head {
                    crate::ClauseHead::Predicate(_, args) => args,
                    crate::ClauseHead::False => continue,
                };

                let Some(source_vars) = self.canonical_vars(*body_pred) else {
                    continue;
                };

                if body_args.len() != source_vars.len() || head_args.len() != target_vars.len() {
                    continue;
                }

                for (body_idx, body_arg) in body_args.iter().enumerate() {
                    let ChcExpr::Var(body_var) = body_arg else {
                        continue;
                    };
                    if !matches!(source_vars[body_idx].sort, ChcSort::Int) {
                        continue;
                    }

                    for (head_idx, head_arg) in head_args.iter().enumerate() {
                        if !matches!(target_vars[head_idx].sort, ChcSort::Int) {
                            continue;
                        }

                        // Case 1: Direct passthrough (head_var == body_var)
                        if let ChcExpr::Var(head_var) = head_arg {
                            if head_var.name == body_var.name {
                                let edge = (*body_pred, body_idx, pred.id, head_idx);
                                if adjacency_seen.insert(edge) {
                                    adjacency
                                        .entry((*body_pred, body_idx))
                                        .or_default()
                                        .push((pred.id, head_idx, 0));
                                }
                                continue;
                            }

                            // Case 2: head_var defined by constraint as body_var + k
                            // Look for equality `head_var = body_var + k` in clause constraint
                            if let Some(constraint) = &clause.body.constraint {
                                let shift_result = extract_affine_shift(
                                    constraint,
                                    head_var.name.as_str(),
                                    body_var.name.as_str(),
                                );
                                if let Some(shift) = shift_result {
                                    let edge = (*body_pred, body_idx, pred.id, head_idx);
                                    if adjacency_seen.insert(edge) {
                                        adjacency
                                            .entry((*body_pred, body_idx))
                                            .or_default()
                                            .push((pred.id, head_idx, shift));
                                    }
                                }
                            }
                        }

                        // Case 3: head_arg is an inlined expression like body_var + k
                        // The parser may inline constraint equalities into head args,
                        // producing e.g. head_arg = (+ 1 A) instead of Var("B") with
                        // constraint B = A + 1. Extract the shift directly from the
                        // head expression structure.
                        if let Some(shift) =
                            extract_expr_affine_shift(head_arg, body_var.name.as_str())
                        {
                            let edge = (*body_pred, body_idx, pred.id, head_idx);
                            if adjacency_seen.insert(edge) {
                                adjacency
                                    .entry((*body_pred, body_idx))
                                    .or_default()
                                    .push((pred.id, head_idx, shift));
                            }
                        }
                    }
                }
            }
        }

        drop(adjacency_seen);

        if self.config.verbose {
            let total_edges: usize = adjacency.values().map(|v| v.len()).sum();
            safe_eprintln!(
                "PDR: propagate_bound_invariants Phase 1: {} adjacency edges",
                total_edges
            );
            for ((src_pred, src_idx), targets) in &adjacency {
                for (tgt_pred, tgt_idx, shift) in targets {
                    safe_eprintln!(
                        "PDR:   edge: pred {}.arg{} -> pred {}.arg{} (shift={})",
                        src_pred.index(),
                        src_idx,
                        tgt_pred.index(),
                        tgt_idx,
                        shift
                    );
                }
            }
        }

        while let Some((source_pred, source_idx, bound, is_lower)) = worklist.pop_front() {
            let Some(targets) = adjacency.get(&(source_pred, source_idx)) else {
                continue;
            };

            for &(target_pred, target_idx, shift) in targets {
                let target_var = match self
                    .canonical_vars(target_pred)
                    .and_then(|vars| vars.get(target_idx))
                {
                    Some(v) => v.clone(),
                    None => continue,
                };

                // Apply affine shift: if body_var >= b and head = body + shift,
                // then head >= b + shift (for lower bounds).
                // For upper bounds: body_var <= b => head <= b + shift.
                let shifted_bound = match bound.checked_add(shift) {
                    Some(sb) => sb,
                    None => continue,
                };

                let item = (target_pred, target_idx, shifted_bound, is_lower);
                if seen_work.contains(&item) {
                    continue;
                }

                let bound_formula = if is_lower {
                    ChcExpr::ge(
                        ChcExpr::var(target_var.clone()),
                        ChcExpr::Int(shifted_bound),
                    )
                } else {
                    ChcExpr::le(
                        ChcExpr::var(target_var.clone()),
                        ChcExpr::Int(shifted_bound),
                    )
                };

                let already_known = self.frames[1].contains_lemma(target_pred, &bound_formula);
                if already_known {
                    // This can happen if a lemma was added by some other phase but wasn't parsed
                    // above; still treat it as a propagation source.
                    seen_work.insert(item);
                    worklist.push_back(item);
                    continue;
                }

                let preserved = if is_lower {
                    self.is_var_non_decreasing(target_pred, &target_var, shifted_bound)
                } else {
                    self.is_var_non_increasing(target_pred, &target_var, shifted_bound)
                };

                if preserved && self.add_discovered_invariant(target_pred, bound_formula.clone(), 1)
                {
                    if self.config.verbose {
                        let bound_type = if is_lower { ">=" } else { "<=" };
                        safe_eprintln!(
                            "PDR: Propagated bound invariant to pred {}: {} {} {} (shift={})",
                            target_pred.index(),
                            target_var.name,
                            bound_type,
                            shifted_bound,
                            shift,
                        );
                    }
                    seen_work.insert(item);
                    worklist.push_back(item);
                }
            }
        }
    }
}

/// Recursively extract bound constraints from a formula, handling conjunctions.
///
/// Parses lemmas of form:
/// - `(>= var const)` => lower bound
/// - `(<= var const)` => upper bound
/// - `(>= const var)` => upper bound (swapped)
/// - `(<= const var)` => lower bound (swapped)
/// - `(= var const)` => both bounds
/// - `(and ...)` => recurse into conjuncts
fn extract_bounds_from_formula(
    formula: &ChcExpr,
    pred: PredicateId,
    enqueue: &mut impl FnMut(PredicateId, &str, i128, bool),
) {
    match formula {
        ChcExpr::Op(ChcOp::Ge, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(bound)) => {
                    enqueue(pred, v.name.as_str(), *bound, true);
                }
                (ChcExpr::Int(bound), ChcExpr::Var(v)) => {
                    enqueue(pred, v.name.as_str(), *bound, false);
                }
                _ => {}
            }
        }
        ChcExpr::Op(ChcOp::Le, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(bound)) => {
                    enqueue(pred, v.name.as_str(), *bound, false);
                }
                (ChcExpr::Int(bound), ChcExpr::Var(v)) => {
                    enqueue(pred, v.name.as_str(), *bound, true);
                }
                _ => {}
            }
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(bound)) | (ChcExpr::Int(bound), ChcExpr::Var(v)) => {
                    enqueue(pred, v.name.as_str(), *bound, true);
                    enqueue(pred, v.name.as_str(), *bound, false);
                }
                _ => {}
            }
        }
        ChcExpr::Op(ChcOp::And, conjuncts) => {
            for conj in conjuncts.iter() {
                extract_bounds_from_formula(conj, pred, enqueue);
            }
        }
        _ => {}
    }
}

/// Extract affine shift from a constraint expression.
///
/// Given a constraint (possibly an `and` of equalities), look for
/// `head_var = body_var + k` or `head_var = body_var - k` (equivalently,
/// `body_var + k`). Returns `Some(k)` if found.
///
/// This handles common CHC patterns like `(= B (+ 1 A))` meaning B = A + 1,
/// so shift = 1 (head = body + 1).
fn extract_affine_shift(constraint: &ChcExpr, head_var: &str, body_var: &str) -> Option<i128> {
    match constraint {
        ChcExpr::Op(ChcOp::And, conjuncts) => {
            for conj in conjuncts.iter() {
                if let Some(shift) = extract_affine_shift(conj, head_var, body_var) {
                    return Some(shift);
                }
            }
            None
        }
        ChcExpr::Op(ChcOp::Eq, args) if args.len() == 2 => {
            // Try head_var = body_var + k  (both orderings)
            try_extract_shift(&args[0], &args[1], head_var, body_var)
                .or_else(|| try_extract_shift(&args[1], &args[0], head_var, body_var))
        }
        _ => None,
    }
}

/// Check if `lhs` is `head_var` and `rhs` is `body_var + k`.
fn try_extract_shift(lhs: &ChcExpr, rhs: &ChcExpr, head_var: &str, body_var: &str) -> Option<i128> {
    // lhs must be the head variable
    let ChcExpr::Var(v) = lhs else { return None };
    if v.name.as_str() != head_var {
        return None;
    }

    // rhs must be body_var + k, body_var - k, or just body_var (shift=0)
    match rhs {
        ChcExpr::Var(v2) if v2.name.as_str() == body_var => Some(0),
        ChcExpr::Op(ChcOp::Add, add_args) if add_args.len() == 2 => {
            // (+ body_var k) or (+ k body_var)
            match (add_args[0].as_ref(), add_args[1].as_ref()) {
                (ChcExpr::Var(v2), ChcExpr::Int(k)) if v2.name.as_str() == body_var => Some(*k),
                (ChcExpr::Int(k), ChcExpr::Var(v2)) if v2.name.as_str() == body_var => Some(*k),
                _ => None,
            }
        }
        ChcExpr::Op(ChcOp::Sub, sub_args) if sub_args.len() == 2 => {
            // (- body_var k)
            match (sub_args[0].as_ref(), sub_args[1].as_ref()) {
                (ChcExpr::Var(v2), ChcExpr::Int(k)) if v2.name.as_str() == body_var => {
                    k.checked_neg()
                }
                _ => None,
            }
        }
        _ => None,
    }
}

/// Extract affine shift directly from a head argument expression.
///
/// When the CHC parser inlines constraint equalities into head args,
/// the head arg for position i may be `body_var + k` (or `k + body_var`)
/// instead of a simple variable. This function checks if `expr` has the
/// form `body_var`, `body_var + k`, `k + body_var`, or `body_var - k`
/// and returns the corresponding shift.
fn extract_expr_affine_shift(expr: &ChcExpr, body_var: &str) -> Option<i128> {
    match expr {
        // Direct: head_arg is body_var itself (shift=0)
        // This is already handled by Case 1, but included for completeness
        ChcExpr::Var(v) if v.name.as_str() == body_var => Some(0),
        // (+ body_var k) or (+ k body_var)
        ChcExpr::Op(ChcOp::Add, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(k)) if v.name.as_str() == body_var => Some(*k),
                (ChcExpr::Int(k), ChcExpr::Var(v)) if v.name.as_str() == body_var => Some(*k),
                _ => None,
            }
        }
        // (- body_var k)
        ChcExpr::Op(ChcOp::Sub, args) if args.len() == 2 => {
            match (args[0].as_ref(), args[1].as_ref()) {
                (ChcExpr::Var(v), ChcExpr::Int(k)) if v.name.as_str() == body_var => {
                    k.checked_neg()
                }
                _ => None,
            }
        }
        _ => None,
    }
}
