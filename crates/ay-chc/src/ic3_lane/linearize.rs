// Copyright 2026 Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Existing CFG elimination, with one caller-owned terminal control.

use super::*;

pub(super) fn linearize_to_single_loop(
    problem: &ChcProblem,
    control: &Control<'_>,
) -> Option<(ChcProblem, PredicateId)> {
    control.poll()?;
    let result = linearize_inner(problem, control)?;
    control.poll()?;
    Some(result)
}

fn linearize_inner(
    problem: &ChcProblem,
    control: &Control<'_>,
) -> Option<(ChcProblem, PredicateId)> {
    let mut clauses: Vec<WClause> = problem
        .clauses()
        .iter()
        .map(|c| {
            control.poll()?;
            Some(WClause {
                body: c.body.predicates.clone(),
                constraint: c.body.constraint.clone(),
                head: c.head.clone(),
            })
        })
        .collect::<Option<Vec<_>>>()?;

    // Protect the loop header(s) so the *header* survives each loop SCC (its
    // invariant is the one stated at the loop head, e.g. `acc <=> count[0]`). A
    // header is a recursive predicate with an in-edge from outside its SCC
    // (the entry edge); if an SCC has no such member, its lowest-id member is
    // protected. Computed once over the original call graph; ids are stable
    // until the final rebuild.
    let protected = protected_headers(&clauses, control)?;

    let mut suffix_ctr: usize = 0;
    loop {
        control.poll()?;
        // Pick any still-referenced predicate that is not *directly* self-
        // recursive and not a protected header. Eliminating it preserves the
        // loop structure: when the penultimate SCC member is removed, the
        // resolvent makes the protected header self-recursive, so exactly one
        // recursive predicate per loop remains.
        let referenced = collect_referenced(&clauses, control)?;
        let mut candidate = None;
        for q in referenced.iter().copied() {
            control.poll()?;
            if !is_self_recursive(&clauses, q, control)? && !protected.contains(&q) {
                candidate = Some(q);
                break;
            }
        }
        let Some(q) = candidate else { break };
        eliminate(&mut clauses, q, &mut suffix_ctr, control)?;
    }

    // All survivors must now be directly self-recursive; require exactly one.
    let referenced = collect_referenced(&clauses, control)?;
    if referenced.len() != 1 {
        return None;
    }
    let r = referenced[0];

    // Rebuild a single-predicate problem; remap the survivor to its fresh id.
    let r_pred = problem.get_predicate(r)?;
    let mut out = ChcProblem::new();
    let new_pid = out.declare_predicate(r_pred.name.clone(), r_pred.arg_sorts.clone());

    for wc in clauses {
        control.poll()?;
        let mut body = Vec::with_capacity(wc.body.len());
        for (p, args) in wc.body {
            control.poll()?;
            if p != r {
                return None; // a non-survivor predicate leaked: unsupported
            }
            body.push((new_pid, args));
        }
        let head = match wc.head {
            ClauseHead::Predicate(h, args) => {
                if h != r {
                    return None;
                }
                ClauseHead::Predicate(new_pid, args)
            }
            ClauseHead::False => ClauseHead::False,
        };
        out.add_clause(HornClause::new(ClauseBody::new(body, wc.constraint), head));
    }
    Some((out, r))
}

/// Predicates that appear in any clause head or body, first-seen order.
fn collect_referenced(clauses: &[WClause], control: &Control<'_>) -> Option<Vec<PredicateId>> {
    let mut seen = Vec::new();
    let mut membership = HashSet::new();
    for c in clauses {
        control.poll()?;
        for (p, _) in &c.body {
            control.poll()?;
            if membership.insert(*p) {
                seen.push(*p);
            }
        }
        if let ClauseHead::Predicate(h, _) = &c.head {
            if membership.insert(*h) {
                seen.push(*h);
            }
        }
    }
    control.poll()?;
    Some(seen)
}

/// Whether q appears in its own defining body, retaining short-circuit order.
fn is_self_recursive(clauses: &[WClause], q: PredicateId, control: &Control<'_>) -> Option<bool> {
    for c in clauses {
        control.poll()?;
        if matches!(&c.head, ClauseHead::Predicate(h, _) if *h == q) {
            for (p, _) in &c.body {
                control.poll()?;
                if *p == q {
                    return Some(true);
                }
            }
        }
    }
    Some(false)
}

/// Loop headers to protect from elimination: one representative per nontrivial
/// SCC of the predicate call graph (preferring a member with an external
/// predecessor — the natural loop head). Eliminating everything else collapses
/// each loop SCC onto its header, whose invariant is the loop-head invariant.
fn protected_headers(clauses: &[WClause], control: &Control<'_>) -> Option<HashSet<PredicateId>> {
    // Call-graph adjacency: body predicate `q` -> head predicate `h`.
    let mut adj: HashMap<PredicateId, HashSet<PredicateId>> = HashMap::new();
    let mut nodes: HashSet<PredicateId> = HashSet::new();
    for c in clauses {
        control.poll()?;
        for (q, _) in &c.body {
            control.poll()?;
            nodes.insert(*q);
        }
        if let ClauseHead::Predicate(h, _) = &c.head {
            nodes.insert(*h);
            for (q, _) in &c.body {
                control.poll()?;
                adj.entry(*q).or_default().insert(*h);
            }
        }
    }

    // Forward reachability per node (transitive closure via DFS).
    let mut reach_of: HashMap<PredicateId, HashSet<PredicateId>> = HashMap::new();
    for &start in &nodes {
        control.poll()?;
        reach_of.insert(start, reach_from(start, &adj, control)?);
    }

    let recursive = |p: PredicateId| reach_of[&p].contains(&p);
    let same_scc =
        |p: PredicateId, q: PredicateId| reach_of[&p].contains(&q) && reach_of[&q].contains(&p);

    let mut protected: HashSet<PredicateId> = HashSet::new();
    // Headers: recursive predicate with a predecessor outside its SCC.
    for c in clauses {
        control.poll()?;
        if let ClauseHead::Predicate(h, _) = &c.head {
            if recursive(*h) {
                for (q, _) in &c.body {
                    control.poll()?;
                    if !same_scc(*h, *q) {
                        protected.insert(*h);
                        break;
                    }
                }
            }
        }
    }
    // Ensure every nontrivial SCC has a protected member (fallback: lowest id).
    let mut recs = Vec::new();
    for &p in &nodes {
        control.poll()?;
        if recursive(p) {
            recs.push(p);
        }
    }
    for &p in &recs {
        control.poll()?;
        let mut minimum: Option<PredicateId> = None;
        let mut has_protected = false;
        for &q in &recs {
            control.poll()?;
            if same_scc(p, q) {
                has_protected |= protected.contains(&q);
                if minimum.is_none_or(|m| q.index() < m.index()) {
                    minimum = Some(q);
                }
            }
        }
        if !has_protected {
            if let Some(m) = minimum {
                protected.insert(m);
            }
        }
    }
    Some(protected)
}

fn reach_from(
    start: PredicateId,
    adj: &HashMap<PredicateId, HashSet<PredicateId>>,
    control: &Control<'_>,
) -> Option<HashSet<PredicateId>> {
    let mut seen = HashSet::new();
    let mut stack = vec![start];
    while let Some(n) = stack.pop() {
        control.poll()?;
        if let Some(succ) = adj.get(&n) {
            for &m in succ {
                control.poll()?;
                if seen.insert(m) {
                    stack.push(m);
                }
            }
        }
    }
    Some(seen)
}

/// Resolve away predicate `q`: replace every use of `q` in a body with each of
/// `q`'s definitions, then drop `q`'s defining clauses. `q` must not be directly
/// self-recursive (guaranteed by the caller).
fn eliminate(
    clauses: &mut Vec<WClause>,
    q: PredicateId,
    ctr: &mut usize,
    control: &Control<'_>,
) -> Option<()> {
    let mut defs = Vec::new();
    for c in clauses.iter() {
        control.poll()?;
        if matches!(&c.head, ClauseHead::Predicate(h, _) if *h == q) {
            defs.push(c.clone());
        }
    }

    let mut out = Vec::new();
    for c in std::mem::take(clauses) {
        control.poll()?;
        if matches!(&c.head, ClauseHead::Predicate(h, _) if *h == q) {
            continue; // a definition of q: consumed by resolution
        }
        let mut occ = Vec::new();
        for (index, (p, _)) in c.body.iter().enumerate() {
            control.poll()?;
            if *p == q {
                occ.push(index);
            }
        }
        match occ.len() {
            0 => out.push(c),
            1 => {
                let j = occ[0];
                if defs.is_empty() {
                    // q is unconstrained (no definition): treat as `true` and
                    // drop the body occurrence (sound over-approximation; a
                    // missed candidate at worst).
                    let mut cc = c.clone();
                    cc.body.remove(j);
                    out.push(cc);
                } else {
                    for d in &defs {
                        control.poll()?;
                        *ctr = ctr.checked_add(1)?;
                        out.push(resolve(&c, j, d, q, *ctr, control)?);
                    }
                }
            }
            _ => return None, // same predicate twice in one body: unsupported
        }
    }
    *clauses = out;
    Some(())
}

/// Resolvent of use-clause `u` (body slot `j` is `q(s)`) against definition `d`
/// (head `q(t)`), by SUBSTITUTION (proper Gaussian/unfold elimination): the use
/// arguments `s` must be distinct simple variables, so unifying `q(s)` with the
/// definition's `q(t)` is the substitution `σ = {s_k ↦ t_k}`. `σ` is applied to
/// the rest of `u` (its other body predicates, constraint, and head); `d`'s body
/// and constraint (variables renamed fresh to avoid capture) are spliced in.
///
/// Substitution (rather than introducing equalities) keeps the data-flow
/// (e.g. `count + 1`) inside the resulting *head arguments* as explicit
/// expressions, leaving the residual constraint a PURE GUARD over current-state
/// variables. That separation lets the transition be lowered with a stuttering
/// guard (a total transition that never constrains the current state) instead of
/// a hard current-state assertion that would hide states from the model checker.
fn resolve(
    u: &WClause,
    j: usize,
    d: &WClause,
    q: PredicateId,
    ctr: usize,
    control: &Control<'_>,
) -> Option<WClause> {
    control.poll()?;
    // Use arguments must be distinct simple variables for substitution.
    let s = &u.body[j].1;
    let mut names: Vec<String> = Vec::with_capacity(s.len());
    for a in s {
        control.poll()?;
        match a {
            ChcExpr::Var(v) => {
                if names.contains(&v.name) {
                    return None; // repeated argument variable: unsupported
                }
                names.push(v.name.clone());
            }
            _ => return None, // non-variable argument: unsupported
        }
    }

    let suf = format!("$e{ctr}");
    let d_body: Vec<(PredicateId, Vec<ChcExpr>)> = d
        .body
        .iter()
        .map(|(p, args)| {
            control.poll()?;
            Some((
                *p,
                args.iter()
                    .map(|a| rename_expr(a, &suf, control))
                    .collect::<Option<Vec<_>>>()?,
            ))
        })
        .collect::<Option<Vec<_>>>()?;
    let d_constraint = match d.constraint.as_ref() {
        Some(c) => Some(rename_expr(c, &suf, control)?),
        None => None,
    };
    let t: Vec<ChcExpr> = match &d.head {
        ClauseHead::Predicate(h, args) if *h == q => args
            .iter()
            .map(|a| rename_expr(a, &suf, control))
            .collect::<Option<Vec<_>>>()?,
        _ => return None,
    };
    if t.len() != names.len() {
        return None;
    }
    let sigma: HashMap<String, ChcExpr> = names.into_iter().zip(t).collect();

    let mut body = Vec::with_capacity(u.body.len() - 1 + d_body.len());
    for (k, (p, args)) in u.body.iter().enumerate() {
        control.poll()?;
        if k == j {
            continue;
        }
        body.push((
            *p,
            args.iter()
                .map(|a| subst_expr(a, &sigma, control))
                .collect::<Option<Vec<_>>>()?,
        ));
    }
    body.extend(d_body);

    let mut conj = Vec::new();
    if let Some(c) = &u.constraint {
        conj.push(subst_expr(c, &sigma, control)?);
    }
    if let Some(c) = d_constraint {
        conj.push(c);
    }

    let head = match &u.head {
        ClauseHead::Predicate(h, args) => ClauseHead::Predicate(
            *h,
            args.iter()
                .map(|a| subst_expr(a, &sigma, control))
                .collect::<Option<Vec<_>>>()?,
        ),
        ClauseHead::False => ClauseHead::False,
    };

    Some(WClause {
        body,
        constraint: and_of(conj),
        head,
    })
}

/// Substitute variables by name with their mapped expressions.
fn subst_expr(
    e: &ChcExpr,
    sigma: &HashMap<String, ChcExpr>,
    control: &Control<'_>,
) -> Option<ChcExpr> {
    control.poll()?;
    let result = match e {
        ChcExpr::Var(v) => sigma.get(&v.name).cloned().unwrap_or_else(|| e.clone()),
        ChcExpr::Op(op, args) => ChcExpr::Op(
            *op,
            args.iter()
                .map(|a| subst_expr(a, sigma, control).map(Arc::new))
                .collect::<Option<Vec<_>>>()?,
        ),
        other => other.clone(),
    };
    control.poll()?;
    Some(result)
}

/// Conjoin a list of constraints (`None` for the empty conjunction = `true`).
fn and_of(mut conj: Vec<ChcExpr>) -> Option<ChcExpr> {
    match conj.len() {
        0 => None,
        1 => conj.pop(),
        _ => Some(ChcExpr::Op(
            ChcOp::And,
            conj.into_iter().map(Arc::new).collect(),
        )),
    }
}

/// Rename every variable in `e` by appending `suf` (avoids capture when a
/// definition clause is spliced into a use clause). Only `Var`/`Op` carry
/// variables in linearized constraints; other leaves are cloned unchanged.
fn rename_expr(e: &ChcExpr, suf: &str, control: &Control<'_>) -> Option<ChcExpr> {
    control.poll()?;
    let result = match e {
        ChcExpr::Var(v) => ChcExpr::Var(ChcVar::new(format!("{}{}", v.name, suf), v.sort.clone())),
        ChcExpr::Op(op, args) => ChcExpr::Op(
            *op,
            args.iter()
                .map(|a| rename_expr(a, suf, control).map(Arc::new))
                .collect::<Option<Vec<_>>>()?,
        ),
        other => other.clone(),
    };
    control.poll()?;
    Some(result)
}
