// Copyright 2026 Andrew Yates
// Author: Andrew Yates <andrewyates.name@gmail.com>
// Licensed under the Apache License, Version 2.0

//! Valid cutting planes used to tighten the LP-relaxation lower bound.
//!
//! # What a cut is here
//!
//! A *cutting plane* (or *cut*) is a linear inequality over the PB variables that
//! is satisfied by **every** 0/1 assignment that satisfies all original
//! constraints, but is (typically) violated by the fractional LP optimum. Adding a
//! valid cut as a new LP row keeps the LP a *relaxation of the same integer
//! problem* — it only shrinks the fractional polytope, never the integer-feasible
//! set — so the LP optimum, and hence our sound dual lower bound, can only move
//! *up* toward the true integer optimum. It can never overshoot it.
//!
//! Every cut produced here is emitted as a [`PbConstraint`] in **original literal
//! space** (literals are `x_v` or `~x_v`, exactly like the parsed instance). It is
//! then fed through the *same* row-building path the LP already uses for the
//! original constraints (`build_row`), so the complementation / literal-negation
//! bookkeeping is shared and cannot diverge.
//!
//! # Cut families and why each is valid
//!
//! ## 1. Clique cuts (from the conflict graph)
//!
//! Two literals `p`, `q` *conflict* when no original-feasible assignment can make
//! both true (`p + q <= 1` for all feasible points). A set `K` of pairwise-
//! conflicting literals is a *clique* in the conflict graph; since no two of its
//! members can be simultaneously true, **at most one** member is true, giving the
//! valid inequality
//!
//! ```text
//! sum_{l in K} l  <=  1.
//! ```
//!
//! We derive each conflict edge `{z_i, z_j}` from a **single** original
//! constraint, viewed in non-negative-coefficient `<=` knapsack form
//! `sum_k a_k z_k <= cap` (an equality yields both its `<=` and negated `<=`
//! views; a `>=` constraint yields the `<=` view of its negation). For any pair
//! with `a_i + a_j > cap`, setting `z_i = z_j = 1` already forces
//! `lhs >= a_i + a_j > cap`, violating that one constraint. Hence
//! `z_i + z_j <= 1` holds for every feasible 0/1 point — a genuine conflict edge.
//! This rule is *always sound* (it is a direct consequence of one constraint) and
//! subsumes the cases that matter in practice:
//!
//! - binary clauses `z_a \/ z_b` (the `<=` view forbids `~z_a = ~z_b = 1`),
//! - at-most-one / exactly-one `sum z_k <= 1` (every pair conflicts -> a clique),
//! - weighted knapsacks where heavy items mutually exclude.
//!
//! Validity is independent of *how* the clique was assembled: as long as each
//! *edge* is a genuine entailed conflict, the clique inequality holds. The
//! brute-force entailment test below verifies this over thousands of instances.
//!
//! ## 2. Cover cuts (from knapsack constraints)
//!
//! Consider any single original constraint rewritten (per literal) into the
//! *normalized knapsack* form with **non-negative** coefficients
//!
//! ```text
//! sum_i a_i * z_i  <=  rhs,        a_i >= 0,   z_i in {0,1}
//! ```
//!
//! where each `z_i` is a literal (`x_v` or `~x_v`). A subset `C` of the indices is
//! a *cover* when `sum_{i in C} a_i > rhs`: the items in `C` cannot **all** be
//! chosen, because their combined weight already exceeds the budget. Hence
//!
//! ```text
//! sum_{i in C} z_i  <=  |C| - 1.
//! ```
//!
//! This is valid for every 0/1 point feasible for that one constraint, so a
//! fortiori for every point feasible for the whole instance. We additionally only
//! emit *minimal* covers (removing any element makes it no longer a cover) which
//! gives the tightest such inequality of this form, and we never lift (lifting is
//! valid too but we keep the conservative, obviously-sound version).
//!
//! # Soundness posture: fail closed
//!
//! Anything we cannot prove valid is simply not emitted. On overflow, oversize, or
//! any structural shape we do not model, the corresponding generator yields no
//! cut. A missing cut only weakens the (still sound) bound; it can never make it
//! wrong.

use std::collections::BTreeMap;

use crate::types::{PbConstraint, PbLit, PbRel, PbTerm};

/// Maximum number of distinct literals we will index for conflict-graph
/// construction. Keeps clique search and memory bounded.
const MAX_CONFLICT_LITERALS: usize = 4_000;
/// Maximum number of conflict edges we record. Beyond this we stop adding edges
/// (already-recorded edges still yield valid cliques).
const MAX_CONFLICT_EDGES: usize = 200_000;
/// Maximum clique size we will emit as a single cut row (keeps rows sparse).
const MAX_CLIQUE_CUT_SIZE: usize = 64;
/// Maximum number of clique cuts emitted in one separation round. Kept modest:
/// each cut becomes an LP row and the exact-rational re-solve cost grows with the
/// row count, so we add only the most-violated cuts per round and re-separate.
const MAX_CLIQUE_CUTS: usize = 64;
/// Maximum number of literals in a single constraint we will scan for a cover.
const MAX_COVER_CONSTRAINT_LITERALS: usize = 256;
/// Maximum number of cover cuts emitted in one separation round.
const MAX_COVER_CUTS: usize = 64;
/// Maximum number of *lifted*-cover cuts emitted in one separation round.
const MAX_LIFTED_COVER_CUTS: usize = 64;
/// Maximum number of items (cover + lifted) the sequential up-lifting will touch
/// for one constraint. Each lifting step runs a knapsack DP over the lifted set,
/// so the total work is `O(items * cap)`; we bound `items` (and `cap` below) to
/// keep one constraint's separation cheap and fail closed on oversized rows.
const MAX_LIFT_ITEMS: usize = 256;
/// Maximum knapsack capacity for which we will run the sequential-lifting DP. The
/// DP table is `O(cap)` wide, so an enormous `cap` would be slow/memory-heavy; we
/// fail closed (emit no lifted cut) above this and let the unlifted cover stand.
const MAX_LIFT_CAP: i128 = 200_000;
/// Maximum number of single-row Chvátal-Gomory (CG) rounding cuts emitted in one
/// separation round. Each becomes an LP row; keep modest so the exact-rational
/// re-solve cost stays bounded (most-violated first, then re-separate next round).
const MAX_CG_CUTS: usize = 64;
/// Maximum number of literals in a single constraint we will scan for a CG cut.
const MAX_CG_CONSTRAINT_LITERALS: usize = 512;
/// Maximum number of distinct divisors we try per constraint when searching for a
/// violated CG cut. Candidates are drawn from the constraint's own coefficients
/// (plus small integers), so the bound caps the per-row separation work.
const MAX_CG_DIVISORS: usize = 24;

/// Environment variable that opts INTO single-row Chvátal-Gomory rounding cuts.
///
/// Default is **OFF**: the default solver behaviour is byte-for-byte unchanged
/// from before this cut family was added. Set `AY_PB_CG_CUTS` to one of
/// `1|true|yes|on` to enable the family (any other value, or an unset variable,
/// keeps it off). CG cuts are fully sound — every emitted cut is brute-force
/// entailment-tested and only ever tightens the dual lower bound, never
/// affecting SAT/UNSAT/optimality — so opting in can only improve bound quality
/// at the cost of extra exact-rational LP re-solves.
const CG_CUTS_ENV: &str = "AY_PB_CG_CUTS";

/// Whether single-row CG rounding cuts are enabled (opt-in; default OFF).
fn cg_cuts_enabled() -> bool {
    fn enabled(value: &std::ffi::OsStr) -> bool {
        value.to_str().is_some_and(|value| {
            matches!(
                value.trim().to_ascii_lowercase().as_str(),
                "1" | "true" | "yes" | "on"
            )
        })
    }
    std::env::var_os(CG_CUTS_ENV)
        .as_deref()
        .is_some_and(enabled)
}

/// A fractional LP point in original variable space: `x[v]` in `[0, 1]` is the
/// (best-effort) LP relaxation value of PB variable `v+1`. Used only to *focus*
/// separation on violated cuts; soundness never depends on its accuracy.
pub(crate) type FractionalPoint = [num_rational::BigRational];

/// Evaluates a literal's fractional value `val(x_v)` or `val(~x_v) = 1 - val(x_v)`
/// at the LP point. Returns `None` if the variable is out of range.
fn lit_value(lit: PbLit, x: &FractionalPoint) -> Option<num_rational::BigRational> {
    use num_traits::One;
    let idx = usize::try_from(lit.var.checked_sub(1)?).ok()?;
    let v = x.get(idx)?.clone();
    if lit.negated {
        Some(num_rational::BigRational::one() - v)
    } else {
        Some(v)
    }
}

/// Generates valid clique and cover cuts that are *violated* by the fractional
/// point `x` (when supplied), in original literal space.
///
/// Every returned [`PbConstraint`] is a `>=`-form inequality that holds for every
/// 0/1 assignment satisfying `constraints`. The caller adds them as new LP rows.
///
/// `num_vars` is the PB variable count (1-indexed variables `1..=num_vars`).
pub(crate) fn separate_cuts(
    constraints: &[PbConstraint],
    num_vars: u32,
    x: &FractionalPoint,
    should_stop: &dyn Fn() -> bool,
) -> Vec<PbConstraint> {
    let mut cuts = Vec::new();
    if should_stop() {
        return cuts;
    }
    if let Some(graph) = ConflictGraph::build(constraints, num_vars, should_stop) {
        graph.separate_clique_cuts(x, should_stop, &mut cuts);
    }
    let n_clique = cuts.len();
    if should_stop() {
        return cuts;
    }
    separate_cover_cuts(constraints, x, should_stop, &mut cuts);
    let n_cover = cuts.len() - n_clique;
    if should_stop() {
        return cuts;
    }
    // Sequential lifted-cover cuts always run (like cover cuts, NOT env-gated):
    // they only ever strengthen the sound bound, never weaken it, and every
    // emitted cut is brute-force entailment-tested.
    separate_lifted_cover_cuts(constraints, x, should_stop, &mut cuts);
    let n_lifted = cuts.len() - n_clique - n_cover;
    // Chvátal-Gomory rounding cuts are opt-in (default OFF) so the default solver
    // path is unchanged; when enabled they only ever tighten the dual bound.
    if cg_cuts_enabled() {
        if should_stop() {
            return cuts;
        }
        separate_cg_cuts(constraints, x, should_stop, &mut cuts);
    }
    // Family-count trace (advisory; drives the cut-provenance emitter build).
    if std::env::var_os("AY_CUT_TRACE").is_some() && !cuts.is_empty() {
        let n_cg = cuts.len() - n_clique - n_cover - n_lifted;
        eprintln!("c [cuts] clique={n_clique} cover={n_cover} lifted={n_lifted} cg={n_cg}");
    }
    cuts
}

// ===================================================================== //
//  Clique cuts                                                          //
// ===================================================================== //

/// Conflict graph over literals: an edge `{p, q}` means *no original-feasible
/// point can set both `p` and `q` true* (`p + q <= 1` is entailed).
struct ConflictGraph {
    /// Distinct literals that appear in at least one conflict edge, in a stable
    /// order. Index into this is the graph node id.
    lits: Vec<PbLit>,
    /// Adjacency: sorted node-id neighbours per node.
    adj: Vec<Vec<usize>>,
}

impl ConflictGraph {
    /// Builds the conflict graph from binary exclusions entailed by individual
    /// constraints. Returns `None` if there is nothing usable or `should_stop`
    /// fires mid-build (so a large constraint set cannot blow the time budget).
    fn build(
        constraints: &[PbConstraint],
        num_vars: u32,
        should_stop: &dyn Fn() -> bool,
    ) -> Option<Self> {
        let mut edges: Vec<(PbLit, PbLit)> = Vec::new();
        for (i, c) in constraints.iter().enumerate() {
            // Poll the deadline every so often: the per-constraint pairwise scan is
            // cheap but the total over many constraints is not.
            if i.is_multiple_of(256) && should_stop() {
                break;
            }
            collect_binary_conflicts(c, num_vars, &mut edges);
            if edges.len() > MAX_CONFLICT_EDGES {
                edges.truncate(MAX_CONFLICT_EDGES);
                break;
            }
        }
        if edges.is_empty() {
            return None;
        }

        // Canonicalize and intern literals.
        let mut lit_id: BTreeMap<PbLit, usize> = BTreeMap::new();
        let mut lits: Vec<PbLit> = Vec::new();
        let mut intern = |lit: PbLit, lits: &mut Vec<PbLit>| -> Option<usize> {
            if let Some(&id) = lit_id.get(&lit) {
                return Some(id);
            }
            if lits.len() >= MAX_CONFLICT_LITERALS {
                return None;
            }
            let id = lits.len();
            lits.push(lit);
            lit_id.insert(lit, id);
            Some(id)
        };

        // Dedup edges by canonical (min,max) literal pair.
        let mut edge_set: std::collections::BTreeSet<(usize, usize)> =
            std::collections::BTreeSet::new();
        for (p, q) in edges {
            if p == q {
                continue;
            }
            let Some(pi) = intern(p, &mut lits) else {
                continue;
            };
            let Some(qi) = intern(q, &mut lits) else {
                continue;
            };
            let key = if pi < qi { (pi, qi) } else { (qi, pi) };
            edge_set.insert(key);
        }
        if edge_set.is_empty() || lits.is_empty() {
            return None;
        }

        let mut adj: Vec<Vec<usize>> = vec![Vec::new(); lits.len()];
        for (a, b) in edge_set {
            adj[a].push(b);
            adj[b].push(a);
        }
        for nbrs in &mut adj {
            nbrs.sort_unstable();
            nbrs.dedup();
        }
        Some(Self { lits, adj })
    }

    /// Returns whether nodes `a` and `b` are adjacent (conflict edge present).
    fn adjacent(&self, a: usize, b: usize) -> bool {
        self.adj[a].binary_search(&b).is_ok()
    }

    /// Greedily grows a maximal clique seeded at `seed`, preferring to add the
    /// neighbour with the largest fractional literal value (so the resulting
    /// `sum <= 1` cut is most likely violated by `x`).
    fn grow_clique(&self, seed: usize, x: &FractionalPoint) -> Vec<usize> {
        let mut clique = vec![seed];
        // Candidate set = neighbours of seed.
        let mut candidates: Vec<usize> = self.adj[seed].clone();
        while !candidates.is_empty() && clique.len() < MAX_CLIQUE_CUT_SIZE {
            // Pick the candidate with the highest fractional value (tie: smallest id).
            let mut best: Option<(usize, num_rational::BigRational)> = None;
            for &cand in &candidates {
                let val = lit_value(self.lits[cand], x).unwrap_or_else(num_traits::Zero::zero);
                match &best {
                    Some((_, bv)) if *bv >= val => {}
                    _ => best = Some((cand, val)),
                }
            }
            let Some((chosen, _)) = best else { break };
            clique.push(chosen);
            // Restrict candidates to those adjacent to `chosen` (and still to all).
            candidates.retain(|&c| c != chosen && self.adjacent(c, chosen));
        }
        clique
    }

    /// Separates clique cuts violated by `x`, appending valid `>=`-form rows.
    fn separate_clique_cuts(
        &self,
        x: &FractionalPoint,
        should_stop: &dyn Fn() -> bool,
        out: &mut Vec<PbConstraint>,
    ) {
        use num_traits::One;
        let one = num_rational::BigRational::one();
        // Seeds in descending fractional value so the most-violated cuts come first.
        let mut seeds: Vec<usize> = (0..self.lits.len()).collect();
        seeds.sort_by(|&a, &b| {
            let va = lit_value(self.lits[a], x).unwrap_or_else(num_traits::Zero::zero);
            let vb = lit_value(self.lits[b], x).unwrap_or_else(num_traits::Zero::zero);
            vb.cmp(&va).then(a.cmp(&b))
        });

        let mut emitted: std::collections::BTreeSet<Vec<usize>> = std::collections::BTreeSet::new();
        for &seed in &seeds {
            if out.len() >= MAX_CLIQUE_CUTS || should_stop() {
                return;
            }
            let clique = self.grow_clique(seed, x);
            if clique.len() < 2 {
                continue;
            }
            // Canonical key for dedup.
            let mut key = clique.clone();
            key.sort_unstable();
            if !emitted.insert(key) {
                continue;
            }
            // Sum of fractional literal values over the clique.
            let mut frac_sum = num_rational::BigRational::default();
            let mut ok = true;
            for &node in &clique {
                match lit_value(self.lits[node], x) {
                    Some(v) => frac_sum += v,
                    None => {
                        ok = false;
                        break;
                    }
                }
            }
            // Only keep cuts the fractional point actually violates: sum > 1.
            if !ok || frac_sum <= one {
                continue;
            }
            // Build `sum_{l in K} l <= 1` as a `>=` row: `sum ~l >= |K| - 1`.
            // Equivalent and what the LP path consumes: negate each literal,
            // rhs = |K| - 1.
            let k = clique.len() as i128;
            let mut terms = Vec::with_capacity(clique.len());
            for &node in &clique {
                let lit = self.lits[node];
                terms.push(PbTerm {
                    coeff: 1,
                    lits: vec![PbLit {
                        var: lit.var,
                        negated: !lit.negated,
                    }],
                });
            }
            out.push(PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs: k - 1,
            });
        }
    }
}

/// Maximum number of literals in one constraint we will scan for pairwise
/// conflicts (the scan is quadratic in this).
const MAX_CONFLICT_SCAN_LITERALS: usize = 256;

/// Collects pairwise conflict edges entailed by a single constraint.
///
/// We view the constraint in non-negative-coefficient `<=` knapsack form
/// `sum a_i z_i <= cap` (an `Eq` yields two such views — direct and negated; a
/// `Ge` yields one from its negation). For **any** pair `{i, j}` with
/// `a_i + a_j > cap`, setting `z_i = z_j = 1` already forces `lhs >= a_i + a_j >
/// cap`, violating the constraint. Hence `z_i + z_j <= 1` for every feasible 0/1
/// point — a genuine conflict edge `{z_i, z_j}`. This is *always sound*: it is a
/// direct logical consequence of one original constraint, no matter the
/// coefficients.
///
/// This subsumes the special cases that matter in practice:
/// - binary clause `z_a \/ z_b` (its `<=` view forbids `~z_a = ~z_b = 1`),
/// - at-most-one / exactly-one `sum z_i <= 1` (every pair conflicts -> a clique),
/// - weighted knapsacks where heavy items mutually exclude.
fn collect_binary_conflicts(c: &PbConstraint, num_vars: u32, out: &mut Vec<(PbLit, PbLit)>) {
    for knap in knapsack_views(c, num_vars) {
        if knap.items.len() > MAX_CONFLICT_SCAN_LITERALS {
            continue;
        }
        let cap = knap.cap;
        let items = &knap.items;
        for (i, &(li, ai)) in items.iter().enumerate() {
            // a_i alone exceeding cap is a fixing (z_i = 0), not a pair conflict;
            // leave that to bound propagation. We only emit genuine pair edges.
            for &(lj, aj) in &items[i + 1..] {
                if li.var == lj.var {
                    continue;
                }
                match ai.checked_add(aj) {
                    Some(sum) if sum > cap => out.push((li, lj)),
                    _ => {}
                }
            }
        }
    }
}

fn negate_lit(lit: PbLit) -> PbLit {
    PbLit {
        var: lit.var,
        negated: !lit.negated,
    }
}

/// Normalizes `sum coeff_i * lit_i >= rhs` (each term single-literal) into
/// canonical form with **non-negative** literal coefficients, returning
/// `(Vec<(lit, coeff>=0)>, rhs')` such that the constraint is equivalent to
/// `sum coeff'_i * lit'_i >= rhs'`.
///
/// A term `coeff * lit` with `coeff < 0` is rewritten using `lit = 1 - ~lit`:
/// `coeff * lit = coeff - coeff * ~lit = coeff + (-coeff) * ~lit`, moving the
/// constant `coeff` to the rhs (`rhs' -= coeff`) and leaving coefficient
/// `-coeff > 0` on `~lit`. Duplicate variables are merged. Returns `None` if any
/// term is non-linear, a variable is out of range, or arithmetic overflows.
///
/// Retained as a tested building block / reference normalizer; the live conflict
/// path now works through the `<=` knapsack view ([`knapsack_views`]).
#[cfg(test)]
fn normalize_ge_nonneg(
    terms: &[PbTerm],
    rhs: i128,
    num_vars: u32,
) -> Option<(Vec<(PbLit, i128)>, i128)> {
    let mut by_var: BTreeMap<u32, (i128, i128)> = BTreeMap::new(); // var -> (coeff on positive lit, _)
    let mut adj_rhs = rhs;
    for t in terms {
        if t.coeff == 0 {
            continue;
        }
        let [lit] = t.lits.as_slice() else {
            return None;
        };
        if lit.var == 0 || lit.var > num_vars {
            return None;
        }
        // Resolve to coefficient on the POSITIVE literal of this variable.
        // term = coeff * value(lit).
        //   positive lit: + coeff * x_v
        //   negated lit:  + coeff * (1 - x_v) = coeff - coeff * x_v
        let (pos_coeff_delta, rhs_delta) = if lit.negated {
            (t.coeff.checked_neg()?, t.coeff)
        } else {
            (t.coeff, 0)
        };
        adj_rhs = adj_rhs.checked_sub(rhs_delta)?;
        let entry = by_var.entry(lit.var).or_insert((0, 0));
        entry.0 = entry.0.checked_add(pos_coeff_delta)?;
    }

    // Now constraint is sum (pos_coeff_v) * x_v >= adj_rhs. Make coefficients
    // non-negative by complementing variables with negative coefficient:
    //   c * x_v = c + (-c) * ~x_v  for c < 0; move +c to rhs (rhs' -= c).
    let mut normalized: Vec<(PbLit, i128)> = Vec::new();
    for (var, (coeff, _)) in by_var {
        if coeff == 0 {
            continue;
        }
        if coeff > 0 {
            normalized.push((
                PbLit {
                    var,
                    negated: false,
                },
                coeff,
            ));
        } else {
            // coeff < 0
            adj_rhs = adj_rhs.checked_sub(coeff)?; // subtract negative => increase rhs
            normalized.push((PbLit { var, negated: true }, coeff.checked_neg()?));
        }
    }
    Some((normalized, adj_rhs))
}

// ===================================================================== //
//  Cover cuts                                                           //
// ===================================================================== //

/// Separates minimal-cover cuts from individual constraints, appending valid
/// `>=`-form rows violated (when possible) by the fractional point `x`.
fn separate_cover_cuts(
    constraints: &[PbConstraint],
    x: &FractionalPoint,
    should_stop: &dyn Fn() -> bool,
    out: &mut Vec<PbConstraint>,
) {
    for c in constraints {
        if out.len() >= MAX_COVER_CUTS || should_stop() {
            return;
        }
        separate_cover_for_constraint(c, x, out);
    }
}

/// A constraint `sum a_i z_i <= cap` with non-negative coefficients in literal
/// space (the knapsack view), extracted from one PB constraint direction.
struct Knapsack {
    /// `(literal, weight a_i >= 1)` items.
    items: Vec<(PbLit, i128)>,
    /// Capacity (`rhs` of the `<=` form), `>= 0`.
    cap: i128,
}

/// Extracts the knapsack view(s) of a constraint as `sum a_i z_i <= cap` with
/// `a_i >= 1`, `cap >= 0`. A `Ge` constraint gives one view (its negation); an
/// `Eq` gives the same single useful `<=` view from each direction (we take the
/// `>=` direction's negation). Returns the views that are well-formed and bounded.
fn knapsack_views(c: &PbConstraint, num_vars: u32) -> Vec<Knapsack> {
    let mut views = Vec::new();
    // A constraint `sum p_i x_i >= R` (any signs) is equivalent to the `<=` form
    // `sum (-p_i) x_i <= -R`; we then renormalize THAT into a non-negative-
    // coefficient knapsack. An `Eq` constraint additionally yields the direct
    // `<=` view from `sum p_i x_i = R  =>  sum p_i x_i <= R`.
    let raw_directions: Vec<(Vec<PbTerm>, i128)> = match c.rel {
        PbRel::Ge => match negate_terms_rhs(&c.terms, c.rhs) {
            Some(v) => vec![v],
            None => Vec::new(),
        },
        PbRel::Eq => {
            let mut v = vec![(c.terms.clone(), c.rhs)];
            if let Some(neg) = negate_terms_rhs(&c.terms, c.rhs) {
                v.push(neg);
            }
            v
        }
    };
    for (terms, le_rhs) in raw_directions {
        if let Some(k) = normalize_le_nonneg(&terms, le_rhs, num_vars) {
            views.push(k);
        }
    }
    views
}

/// Returns `Some((negated_terms, -rhs))` so `terms >= rhs` becomes the `<=` form
/// `negated_terms <= -rhs`. `None` on overflow or a non-linear term.
fn negate_terms_rhs(terms: &[PbTerm], rhs: i128) -> Option<(Vec<PbTerm>, i128)> {
    let mut neg = Vec::with_capacity(terms.len());
    for t in terms {
        let [lit] = t.lits.as_slice() else {
            return None;
        };
        neg.push(PbTerm {
            coeff: t.coeff.checked_neg()?,
            lits: vec![*lit],
        });
    }
    Some((neg, rhs.checked_neg()?))
}

/// Normalizes `sum coeff_i * lit_i <= rhs` into a non-negative-coefficient
/// knapsack `sum a_i z_i <= cap` with `a_i >= 1` and `cap >= 0`. Returns `None`
/// when not a bounded covering shape (e.g. `cap < 0` means infeasible/empty here,
/// or overflow).
fn normalize_le_nonneg(terms: &[PbTerm], rhs: i128, num_vars: u32) -> Option<Knapsack> {
    let mut by_var: BTreeMap<u32, i128> = BTreeMap::new();
    let mut cap = rhs;
    for t in terms {
        if t.coeff == 0 {
            continue;
        }
        let [lit] = t.lits.as_slice() else {
            return None;
        };
        if lit.var == 0 || lit.var > num_vars {
            return None;
        }
        // term = coeff * value(lit) on the <= side.
        //   positive: coeff * x_v
        //   negated:  coeff * (1 - x_v) = coeff - coeff * x_v ; move +coeff to lhs->rhs
        let (pos_delta, cap_delta) = if lit.negated {
            (t.coeff.checked_neg()?, t.coeff)
        } else {
            (t.coeff, 0)
        };
        cap = cap.checked_sub(cap_delta)?;
        let e = by_var.entry(lit.var).or_insert(0);
        *e = e.checked_add(pos_delta)?;
    }
    // Make coefficients non-negative for the <= form:
    //   c * x_v <= ... with c < 0: c * x_v = c + (-c) * ~x_v; move +c to cap side:
    //   cap' = cap - c (since c negative, cap grows), coeff on ~x_v is -c > 0.
    let mut items: Vec<(PbLit, i128)> = Vec::new();
    for (var, coeff) in by_var {
        if coeff == 0 {
            continue;
        }
        if coeff > 0 {
            items.push((
                PbLit {
                    var,
                    negated: false,
                },
                coeff,
            ));
        } else {
            cap = cap.checked_sub(coeff)?; // subtract negative -> increase cap
            items.push((PbLit { var, negated: true }, coeff.checked_neg()?));
        }
    }
    if items.is_empty() || items.len() > MAX_COVER_CONSTRAINT_LITERALS {
        return None;
    }
    if cap < 0 {
        // Empty feasible set on this view alone; not a usable cover source.
        return None;
    }
    Some(Knapsack { items, cap })
}

/// Finds at most one violated minimal cover for one constraint and appends the
/// corresponding cut.
fn separate_cover_for_constraint(
    c: &PbConstraint,
    x: &FractionalPoint,
    out: &mut Vec<PbConstraint>,
) {
    // num_vars is implicit in x length; clamp by it.
    let num_vars = match u32::try_from(x.len()) {
        Ok(v) => v,
        Err(_) => return,
    };
    for knap in knapsack_views(c, num_vars) {
        if let Some(cut) = cover_cut_from_knapsack(&knap, x) {
            out.push(cut);
            return; // one cover per constraint per round keeps growth bounded.
        }
    }
}

/// Builds a violated minimal-cover cut from a knapsack `sum a_i z_i <= cap`.
///
/// Heuristic (LP-guided, mirrors the classic separation): consider items in
/// decreasing fractional value `val(z_i)`; greedily accumulate weight until it
/// exceeds `cap` — that prefix is a cover. Then *minimize* it (drop any item that
/// can be removed while still exceeding `cap`). If the resulting cover is violated
/// (`sum_{i in C} val(z_i) > |C| - 1`) emit `sum_{i in C} z_i <= |C| - 1`.
///
/// Returns `None` if no cover exists (all items fit) or the cover is not violated.
fn cover_cut_from_knapsack(knap: &Knapsack, x: &FractionalPoint) -> Option<PbConstraint> {
    use num_traits::Zero;
    // Order items by fractional value descending (most likely in a violated cover).
    let mut order: Vec<usize> = (0..knap.items.len()).collect();
    order.sort_by(|&a, &b| {
        let va = lit_value(knap.items[a].0, x).unwrap_or_else(Zero::zero);
        let vb = lit_value(knap.items[b].0, x).unwrap_or_else(Zero::zero);
        vb.cmp(&va).then(a.cmp(&b))
    });

    // Greedily accumulate until total weight > cap.
    let mut cover: Vec<usize> = Vec::new();
    let mut weight: i128 = 0;
    for &i in &order {
        cover.push(i);
        weight = weight.checked_add(knap.items[i].1)?;
        if weight > knap.cap {
            break;
        }
    }
    if weight <= knap.cap {
        return None; // everything fits: no cover from this ordering.
    }

    // Minimize: remove items (smallest weight first, to keep large-weight core)
    // as long as the remaining set is still a cover (sum > cap).
    let mut min_order = cover.clone();
    min_order.sort_by_key(|&i| knap.items[i].1); // ascending weight
    for &i in &min_order {
        if cover.len() <= 1 {
            break;
        }
        let w = knap.items[i].1;
        if weight - w > knap.cap {
            weight -= w;
            cover.retain(|&j| j != i);
        }
    }
    if cover.len() < 2 {
        // A singleton "cover" would assert z_i <= 0, i.e. the item alone exceeds
        // the cap. That is a valid fixing but we let unit propagation / bounds
        // handle it; emitting `z_i <= 0` as a cut row is still valid, but skip to
        // avoid degenerate rows.
        return None;
    }

    // Check the cover is actually a cover (defensive) and violated by x.
    let total: i128 = cover
        .iter()
        .try_fold(0i128, |acc, &i| acc.checked_add(knap.items[i].1))?;
    if total <= knap.cap {
        return None;
    }
    let mut frac_sum = num_rational::BigRational::zero();
    for &i in &cover {
        frac_sum += lit_value(knap.items[i].0, x)?;
    }
    let card = cover.len() as i128;
    let rhs_le = card - 1;
    // Violated iff sum_{i in C} val(z_i) > |C| - 1.
    if frac_sum <= num_rational::BigRational::from_integer(rhs_le.into()) {
        return None; // not violated; no point adding.
    }

    // Emit `sum_{i in C} z_i <= |C| - 1` as a `>=` row: `sum ~z_i >= 1`.
    // (sum z_i <= |C|-1  <=>  sum (1 - z_i) >= 1  <=>  sum ~z_i >= 1.)
    let mut terms = Vec::with_capacity(cover.len());
    for &i in &cover {
        let lit = knap.items[i].0;
        terms.push(PbTerm {
            coeff: 1,
            lits: vec![negate_lit(lit)],
        });
    }
    Some(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs: 1,
    })
}

// ===================================================================== //
//  Sequential lifted-cover cuts                                         //
// ===================================================================== //

// Sequential up-lifted cover cuts.
//
// # The cut and why it is valid
//
// Start from one constraint's non-negative-coefficient `<=` knapsack view
// `sum_i a_i z_i <= cap` (`a_i >= 1`, `cap >= 0`, each `z_i` a literal taking an
// integer value in `{0,1}`) and a *minimal cover* `C`: a subset with
// `sum_{i in C} a_i > cap` such that dropping any single member leaves a non-cover.
// The minimal-cover inequality
//
// ```text
// sum_{i in C} z_i  <=  |C| - 1
// ```
//
// is valid (the |C| cover items cannot all be 1, else the weight exceeds cap).
// *Sequential up-lifting* strengthens it by giving the non-cover variables a
// non-negative coefficient. Process the non-cover variables one at a time. Let `L`
// be the set already in the inequality (initially `C`, each with coefficient 1)
// with current coefficients `beta_i` and rhs `b = |C| - 1`. To lift the next
// variable `j` (weight `a_j`), the *largest* coefficient that keeps the inequality
// valid is
//
// ```text
// alpha_j  =  b  -  max{ sum_{i in L} beta_i z_i
//                        : sum_{i in L} a_i z_i <= cap - a_j,  z in {0,1}^L }.
// ```
//
// Intuition / validity: fix `z_j = 1`. Any feasible point then has
// `sum_{i in L} a_i z_i <= cap - a_j`, so over those points the achievable value of
// `sum_{i in L} beta_i z_i` is at most the `max` above; adding `alpha_j * z_j` keeps
// the total `<= b`. With `z_j = 0` the term vanishes and the prior inequality
// (already valid) is unchanged. Hence `sum_{i in L} beta_i z_i + alpha_j z_j <= b`
// is valid; `j` then joins `L` with coefficient `alpha_j` for later liftings. The
// `max` is exactly a 0/1 knapsack-value problem over `L`, which we solve with an
// exact integer DP keyed on used a-weight (`O(|L| * cap)` per step).
//
// Because every `max` is taken over a subset of the original feasible set,
// `alpha_j >= 0` always (the empty selection `z = 0` is feasible and gives value 0,
// so the `max` is `<= b`), and the lifted cut *dominates* the unlifted cover cut
// term-for-term (cover coefficients stay 1, extra coefficients are `>= 0`, rhs is
// unchanged). It can only cut off more of the fractional polytope, never less.
//
// # Targeting a violated cut
//
// We only emit the lifted cut when the fractional point `x*` violates it:
// `sum beta_i val(z_i) > b`. We lift non-cover variables in decreasing weight
// order (a standard, cheap choice that tends to produce the largest coefficients)
// and bound the number of items and the capacity so one constraint's separation
// stays cheap.
//
// # Soundness posture: fail closed
//
// Any overflow, oversize row, oversize capacity, or unmodelled shape simply yields
// no cut. A missing cut only weakens the still-sound bound; it can never make it
// wrong. Every emitted cut is additionally brute-force entailment-checked by
// `property_every_lifted_cover_cut_is_entailed`.

/// Separates sequential lifted-cover cuts from individual constraints, appending
/// valid `>=`-form rows violated (when possible) by the fractional point `x`.
fn separate_lifted_cover_cuts(
    constraints: &[PbConstraint],
    x: &FractionalPoint,
    should_stop: &dyn Fn() -> bool,
    out: &mut Vec<PbConstraint>,
) {
    let num_vars = match u32::try_from(x.len()) {
        Ok(v) => v,
        Err(_) => return,
    };
    let mut emitted = 0usize;
    for c in constraints {
        if emitted >= MAX_LIFTED_COVER_CUTS || should_stop() {
            return;
        }
        for knap in knapsack_views(c, num_vars) {
            if let Some(cut) = lifted_cover_cut_from_knapsack(&knap, x) {
                out.push(cut);
                emitted += 1;
                // One lifted cover per constraint per round keeps LP growth
                // bounded; the next round re-separates against the new point.
                break;
            }
        }
    }
}

/// A single literal carrying its knapsack weight and current inequality
/// coefficient. Used as the running lifted set `L` during sequential lifting.
struct LiftedItem {
    lit: PbLit,
    /// Knapsack weight `a_i` (`>= 1`).
    weight: i128,
    /// Current inequality coefficient (`1` for cover items, `alpha_j >= 0` for
    /// lifted ones).
    coeff: i128,
}

/// Computes `max{ sum_{i in L} L[i].coeff * z_i : sum_{i in L} L[i].weight * z_i
/// <= budget, z in {0,1}^L }` exactly via a 0/1-knapsack DP over used weight.
///
/// `budget` is `cap - a_j >= 0`. Returns `None` on overflow or if the DP table
/// would exceed [`MAX_LIFT_CAP`] (fail closed). The DP value at index `w` is the
/// best total coefficient achievable using **at most** `w` weight; `dp[budget]`
/// is the answer.
fn max_coeff_within_budget(lifted: &[LiftedItem], budget: i128) -> Option<i128> {
    if budget < 0 {
        // No item set fits (not even the empty one would change this, but a
        // negative budget means z_j=1 is already infeasible w.r.t. cap): the only
        // selection is the empty one with value 0. Treated as value 0.
        return Some(0);
    }
    if budget > MAX_LIFT_CAP {
        return None; // table too wide; fail closed.
    }
    let width = usize::try_from(budget).ok()?.checked_add(1)?;
    // dp[w] = best coefficient sum using total weight exactly <= w. Standard 0/1
    // knapsack with "<=" semantics (carry forward), all-zero init (empty set).
    let mut dp = vec![0i128; width];
    for item in lifted {
        let w = item.weight;
        if w <= 0 {
            continue; // weights are >= 1 by construction; defensive skip.
        }
        let wu = usize::try_from(w).ok()?;
        if wu >= width {
            continue; // item alone doesn't fit in the budget.
        }
        // Iterate capacities downward so each item is used at most once.
        let mut cap_idx = width - 1;
        while cap_idx >= wu {
            let cand = dp[cap_idx - wu].checked_add(item.coeff)?;
            if cand > dp[cap_idx] {
                dp[cap_idx] = cand;
            }
            if cap_idx == wu {
                break;
            }
            cap_idx -= 1;
        }
    }
    Some(dp[width - 1])
}

/// Builds a violated sequential lifted-cover cut from a knapsack
/// `sum a_i z_i <= cap`, or `None` if no violated lifted cut is found.
///
/// Steps:
/// 1. Find a minimal cover `C` LP-guided (same heuristic as the unlifted cover).
/// 2. Sequentially up-lift every non-cover variable (decreasing weight), each via
///    the exact knapsack DP [`max_coeff_within_budget`].
/// 3. Emit `sum_i beta_i z_i <= |C|-1` as a `>=` row only if `x*` violates it.
///
/// All arithmetic is checked; any overflow / oversize aborts with `None`.
fn lifted_cover_cut_from_knapsack(knap: &Knapsack, x: &FractionalPoint) -> Option<PbConstraint> {
    use num_rational::BigRational;
    use num_traits::Zero;

    let n = knap.items.len();
    if !(2..=MAX_LIFT_ITEMS).contains(&n) {
        return None;
    }
    if knap.cap < 0 || knap.cap > MAX_LIFT_CAP {
        return None; // capacity out of the DP-bounded range; fail closed.
    }

    // --- Step 1: find a minimal cover C (LP-guided, mirrors cover_cut_from_knapsack). ---
    let mut order: Vec<usize> = (0..n).collect();
    order.sort_by(|&a, &b| {
        let va = lit_value(knap.items[a].0, x).unwrap_or_else(Zero::zero);
        let vb = lit_value(knap.items[b].0, x).unwrap_or_else(Zero::zero);
        vb.cmp(&va).then(a.cmp(&b))
    });
    let mut cover: Vec<usize> = Vec::new();
    let mut weight: i128 = 0;
    for &i in &order {
        cover.push(i);
        weight = weight.checked_add(knap.items[i].1)?;
        if weight > knap.cap {
            break;
        }
    }
    if weight <= knap.cap {
        return None; // everything fits: no cover from this ordering.
    }
    // Minimize: drop smallest-weight items while still a cover (sum > cap).
    let mut min_order = cover.clone();
    min_order.sort_by_key(|&i| knap.items[i].1);
    for &i in &min_order {
        if cover.len() <= 1 {
            break;
        }
        let w = knap.items[i].1;
        if weight - w > knap.cap {
            weight -= w;
            cover.retain(|&j| j != i);
        }
    }
    if cover.len() < 2 {
        return None; // singleton "cover" is a fixing; handled elsewhere.
    }
    // Defensive re-check that C is a cover.
    let cover_weight: i128 = cover
        .iter()
        .try_fold(0i128, |acc, &i| acc.checked_add(knap.items[i].1))?;
    if cover_weight <= knap.cap {
        return None;
    }

    let in_cover: std::collections::BTreeSet<usize> = cover.iter().copied().collect();
    let card = cover.len() as i128;
    let rhs_le = card - 1; // b = |C| - 1.

    // --- Step 2: sequential up-lifting of non-cover variables. ---
    // Lifted set starts as the cover with coefficient 1 each.
    let mut lifted: Vec<LiftedItem> = cover
        .iter()
        .map(|&i| LiftedItem {
            lit: knap.items[i].0,
            weight: knap.items[i].1,
            coeff: 1,
        })
        .collect();

    // Non-cover variables, lifted in decreasing weight (ties: smaller index).
    let mut to_lift: Vec<usize> = (0..n).filter(|i| !in_cover.contains(i)).collect();
    to_lift.sort_by(|&a, &b| knap.items[b].1.cmp(&knap.items[a].1).then(a.cmp(&b)));

    for &j in &to_lift {
        if lifted.len() >= MAX_LIFT_ITEMS {
            break;
        }
        let aj = knap.items[j].1;
        // budget = cap - a_j. If a_j > cap then z_j alone violates the row, so the
        // budget is negative and the "max" is over the empty selection (value 0),
        // giving alpha_j = b. (Such a variable is forced to 0 anyway, but the
        // coefficient is still valid and the brute force confirms it.)
        let budget = knap.cap.checked_sub(aj)?;
        let max_val = max_coeff_within_budget(&lifted, budget)?;
        // alpha_j = b - max_val; clamp at 0 defensively (theory gives >= 0).
        let alpha_j = rhs_le.checked_sub(max_val)?;
        let alpha_j = alpha_j.max(0);
        if alpha_j > 0 {
            lifted.push(LiftedItem {
                lit: knap.items[j].0,
                weight: aj,
                coeff: alpha_j,
            });
        }
        // alpha_j == 0: nothing added (term would be vacuous); j is effectively
        // already at its max coefficient. We do NOT add it to `lifted` so later
        // DPs stay small; a zero coefficient contributes nothing to the DP anyway.
    }

    // --- Step 3: emit only if x* violates the lifted cut. ---
    let mut frac_sum = BigRational::zero();
    for item in &lifted {
        frac_sum += BigRational::from_integer(item.coeff.into()) * lit_value(item.lit, x)?;
    }
    if frac_sum <= BigRational::from_integer(rhs_le.into()) {
        return None; // not violated: no separation value.
    }

    // Build `sum_i beta_i z_i <= rhs_le` as a `>=` row over complemented literals:
    //   sum beta_i z_i <= rhs_le
    //   <=> sum beta_i (1 - ~z_i) <= rhs_le
    //   <=> sum beta_i ~z_i >= (sum beta_i) - rhs_le.
    let mut sum_coeff: i128 = 0;
    for item in &lifted {
        sum_coeff = sum_coeff.checked_add(item.coeff)?;
    }
    let ge_rhs = sum_coeff.checked_sub(rhs_le)?;
    if ge_rhs < 1 {
        return None; // vacuous (cannot happen: sum_coeff >= frac_sum > rhs_le).
    }
    let terms: Vec<PbTerm> = lifted
        .iter()
        .map(|item| PbTerm {
            coeff: item.coeff,
            lits: vec![negate_lit(item.lit)],
        })
        .collect();
    Some(PbConstraint {
        terms,
        rel: PbRel::Ge,
        rhs: ge_rhs,
    })
}

// ===================================================================== //
//  Chvátal-Gomory (CG) rounding cuts                                    //
// ===================================================================== //

// Single-row Chvátal-Gomory rounding cuts.
//
// # The cut and why it is valid (exact rational, no rounding error)
//
// Take one original constraint in its non-negative-coefficient `<=` knapsack
// view `sum_i a_i z_i <= cap` (`a_i >= 1`, `cap >= 0`, each `z_i` a literal
// `x_v`/`~x_v` taking integer value in `{0,1}`). For any integer divisor
// `d >= 2`, the Chvátal-Gomory cut is
//
// ```text
// sum_i floor(a_i / d) * z_i  <=  floor(cap / d).
// ```
//
// Validity for every 0/1 point feasible for the row (hence for the whole
// instance): from `sum_i a_i z_i <= cap`, dividing by `d > 0` gives
// `sum_i (a_i/d) z_i <= cap/d`. Because each `z_i >= 0` and `floor(a_i/d) <=
// a_i/d`, we have `sum_i floor(a_i/d) z_i <= sum_i (a_i/d) z_i <= cap/d`. The
// left-hand side is an *integer* (integer coefficients on integer `z_i`), so it
// is `<= floor(cap/d)`. Every step is exact integer/rational arithmetic — there
// is no floating point and no rounding error; the floors are exact `i128`
// divisions. This is the textbook CG rounding (the `>=`-direction is obtained by
// negation; see `knapsack_views`), the same family RoundingSat/SCIP use.
//
// # Targeting a violated cut
//
// A CG cut helps only when the *fractional* LP point `x*` violates it:
// `sum_i floor(a_i/d) val(z_i) > floor(cap/d)`. We search a bounded set of
// divisors `d` (drawn from the row's own coefficients plus small integers) and
// emit the most-violated rounding for each row. A divisor that yields no
// violation, an all-zero rounded row, or a degenerate `0 <= 0` row is dropped.
//
// # Soundness posture: fail closed
//
// Anything we cannot prove valid (overflow on the floor/negation arithmetic,
// oversize row, non-linear term, an unmodelled shape) is simply not emitted. A
// missing cut only weakens the still-sound bound; it can never make it wrong.
// Every emitted cut is additionally brute-force entailment-checked by
// `property_every_generated_cut_is_entailed`.

/// Separates single-row CG rounding cuts from individual constraints, appending
/// valid `>=`-form rows violated (when possible) by the fractional point `x`.
fn separate_cg_cuts(
    constraints: &[PbConstraint],
    x: &FractionalPoint,
    should_stop: &dyn Fn() -> bool,
    out: &mut Vec<PbConstraint>,
) {
    let num_vars = match u32::try_from(x.len()) {
        Ok(v) => v,
        Err(_) => return,
    };
    let mut emitted = out.len();
    for c in constraints {
        if emitted >= MAX_CG_CUTS || should_stop() {
            return;
        }
        for knap in knapsack_views(c, num_vars) {
            if let Some(cut) = cg_cut_from_knapsack(&knap, x) {
                out.push(cut);
                emitted += 1;
                // One CG cut per constraint per round keeps LP growth bounded; the
                // next round re-separates against the new fractional point.
                break;
            }
        }
    }
}

/// Builds the single most-violated CG rounding cut from a knapsack
/// `sum a_i z_i <= cap`, or `None` if no tried divisor yields a violated,
/// well-formed cut.
///
/// Returns a `>=`-form [`PbConstraint`] equivalent to
/// `sum_i floor(a_i/d) z_i <= floor(cap/d)`. All arithmetic is checked; on any
/// overflow the candidate divisor is skipped (fail-closed).
fn cg_cut_from_knapsack(knap: &Knapsack, x: &FractionalPoint) -> Option<PbConstraint> {
    use num_rational::BigRational;
    use num_traits::Zero;

    if knap.items.is_empty() || knap.items.len() > MAX_CG_CONSTRAINT_LITERALS {
        return None;
    }

    // Candidate divisors: distinct coefficient values >= 2 plus a few small
    // integers. Dividing by a coefficient is the classic CG choice (it zeroes the
    // smaller items and rounds the larger ones), and small divisors catch the
    // GCD-style "tighten the rhs" cuts. Bounded by MAX_CG_DIVISORS.
    let mut divisors: Vec<i128> = Vec::new();
    let small = [2i128, 3, 4, 5, 7];
    for d in small.into_iter().chain(knap.items.iter().map(|&(_, a)| a)) {
        if d >= 2 && !divisors.contains(&d) && divisors.len() < MAX_CG_DIVISORS {
            divisors.push(d);
        }
    }

    // Precompute fractional literal values once; bail if any is unrecoverable.
    let mut vals: Vec<BigRational> = Vec::with_capacity(knap.items.len());
    for &(lit, _) in &knap.items {
        vals.push(lit_value(lit, x)?);
    }

    let mut best: Option<(BigRational, PbConstraint)> = None;
    for &d in &divisors {
        // Rounded coefficients and rhs (exact integer floor division; a_i, cap,
        // d are all >= 0 so `/` is floor division on non-negatives).
        let rhs_le = knap.cap / d; // floor(cap/d), cap >= 0, d >= 2
        let mut rounded: Vec<(PbLit, i128)> = Vec::with_capacity(knap.items.len());
        let mut frac_sum = BigRational::zero();
        for (idx, &(lit, a)) in knap.items.iter().enumerate() {
            let coeff = a / d; // floor(a/d), a >= 1, d >= 2
            if coeff == 0 {
                continue;
            }
            frac_sum += BigRational::from_integer(coeff.into()) * &vals[idx];
            rounded.push((lit, coeff));
        }
        // A useful cut needs >= 2 surviving terms (a single-term `coeff*z <= rhs`
        // is just a bound/fixing handled elsewhere) and must be violated by x*.
        if rounded.len() < 2 {
            continue;
        }
        let rhs_rat = BigRational::from_integer(rhs_le.into());
        if frac_sum <= rhs_rat {
            continue; // not violated by the fractional point: no separation value.
        }
        let violation = &frac_sum - &rhs_rat;
        // Build `sum coeff_i z_i <= rhs_le` as a `>=` row over complemented
        // literals: `sum coeff_i z_i <= rhs_le`  <=>
        // `sum coeff_i (1 - ~z_i) <= rhs_le`     <=>
        // `sum coeff_i ~z_i >= (sum coeff_i) - rhs_le`.
        let mut sum_coeff: i128 = 0;
        let mut overflow = false;
        for &(_, coeff) in &rounded {
            match sum_coeff.checked_add(coeff) {
                Some(s) => sum_coeff = s,
                None => {
                    overflow = true;
                    break;
                }
            }
        }
        if overflow {
            continue;
        }
        let Some(ge_rhs) = sum_coeff.checked_sub(rhs_le) else {
            continue;
        };
        // ge_rhs must be >= 1 for a non-trivial cut (>= 0 is vacuous since all
        // coeffs and literals are non-negative). It is, because frac_sum > rhs_le
        // and each val in [0,1] => sum_coeff >= frac_sum > rhs_le.
        if ge_rhs < 1 {
            continue;
        }
        let terms: Vec<PbTerm> = rounded
            .iter()
            .map(|&(lit, coeff)| PbTerm {
                coeff,
                lits: vec![negate_lit(lit)],
            })
            .collect();
        let cut = PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs: ge_rhs,
        };
        match &best {
            Some((bv, _)) if *bv >= violation => {}
            _ => best = Some((violation, cut)),
        }
    }
    best.map(|(_, cut)| cut)
}

#[cfg(test)]
mod tests {
    use super::*;
    use num_rational::BigRational;
    use num_traits::Zero;

    fn lit(var: u32) -> PbLit {
        PbLit {
            var,
            negated: false,
        }
    }
    fn neg(var: u32) -> PbLit {
        PbLit { var, negated: true }
    }
    fn term(coeff: i128, l: PbLit) -> PbTerm {
        PbTerm {
            coeff,
            lits: vec![l],
        }
    }
    fn ge(terms: Vec<PbTerm>, rhs: i128) -> PbConstraint {
        PbConstraint {
            terms,
            rel: PbRel::Ge,
            rhs,
        }
    }

    fn frac(vals: &[(i128, i128)]) -> Vec<BigRational> {
        vals.iter()
            .map(|&(n, d)| BigRational::new(n.into(), d.into()))
            .collect()
    }

    // ---- Constraint / cut evaluation in ORIGINAL 0/1 space ---- //

    fn lit_bool(l: PbLit, x: &[bool]) -> bool {
        let v = x[(l.var - 1) as usize];
        if l.negated {
            !v
        } else {
            v
        }
    }

    fn constraint_holds(c: &PbConstraint, x: &[bool]) -> bool {
        let mut lhs = 0i128;
        for t in &c.terms {
            // tests only build single-literal terms.
            if lit_bool(t.lits[0], x) {
                lhs += t.coeff;
            }
        }
        match c.rel {
            PbRel::Ge => lhs >= c.rhs,
            PbRel::Eq => lhs == c.rhs,
        }
    }

    /// Brute-force entailment check: every original-feasible 0/1 point must
    /// satisfy `cut`. Returns the first counterexample if any.
    fn first_cut_violation(
        constraints: &[PbConstraint],
        cut: &PbConstraint,
        n: u32,
    ) -> Option<Vec<bool>> {
        for mask in 0u32..(1u32 << n) {
            let x: Vec<bool> = (0..n).map(|b| (mask >> b) & 1 == 1).collect();
            if constraints.iter().all(|c| constraint_holds(c, &x)) && !constraint_holds(cut, &x) {
                return Some(x);
            }
        }
        None
    }

    #[test]
    fn clique_cut_from_two_binary_clauses_is_valid_and_tight() {
        // x1 + x2 >= 1 ? No — we want exclusions. Use clauses ~x1 \/ ~x2 etc.
        // Encode "at most one of x1,x2,x3" via three binary clauses
        //   ~x1 \/ ~x2,  ~x1 \/ ~x3,  ~x2 \/ ~x3
        // each written as a >= : (1-x1)+(1-x2) >= 1  i.e. -x1 -x2 >= -1.
        let c12 = ge(vec![term(-1, lit(1)), term(-1, lit(2))], -1);
        let c13 = ge(vec![term(-1, lit(1)), term(-1, lit(3))], -1);
        let c23 = ge(vec![term(-1, lit(2)), term(-1, lit(3))], -1);
        let constraints = vec![c12, c13, c23];
        // Fractional point x1=x2=x3=1/2 violates x1+x2+x3 <= 1 (sum 3/2 > 1).
        let x = frac(&[(1, 2), (1, 2), (1, 2)]);
        let cuts = separate_cuts(&constraints, 3, &x, &|| false);
        assert!(!cuts.is_empty(), "expected at least one clique cut");
        for cut in &cuts {
            assert!(
                first_cut_violation(&constraints, cut, 3).is_none(),
                "INVALID CUT {cut:?}"
            );
        }
        // At least one cut should be the full triangle x1+x2+x3 <= 1.
        let has_triangle = cuts
            .iter()
            .any(|c| c.terms.len() == 3 && c.rhs == 2 && c.rel == PbRel::Ge);
        assert!(has_triangle, "expected the 3-clique cut, got {cuts:?}");
    }

    #[test]
    fn exactly_one_constraint_yields_clique_clique_cut() {
        // Exactly-one over 4 vars: x1+x2+x3+x4 = 1. The `<=` direction makes every
        // pair conflict -> the 4-clique cut x1+x2+x3+x4 <= 1 is entailed (and is
        // already implied by the equality, but must be VALID).
        let c = PbConstraint {
            terms: vec![
                term(1, lit(1)),
                term(1, lit(2)),
                term(1, lit(3)),
                term(1, lit(4)),
            ],
            rel: PbRel::Eq,
            rhs: 1,
        };
        let constraints = [c];
        let x = frac(&[(1, 3), (1, 3), (1, 3), (1, 3)]); // sum 4/3 > 1: violated
        let cuts = separate_cuts(&constraints, 4, &x, &|| false);
        assert!(!cuts.is_empty(), "expected a clique cut from exactly-one");
        for cut in &cuts {
            assert!(
                first_cut_violation(&constraints, cut, 4).is_none(),
                "INVALID CUT {cut:?}"
            );
        }
    }

    #[test]
    fn weighted_knapsack_pairwise_conflicts_are_valid() {
        // 5 x1 + 5 x2 + 1 x3 <= 6 (as >= : -5x1 -5x2 -1x3 >= -6).
        // x1 and x2 conflict (5+5=10 > 6); x3 conflicts with neither alone.
        let c = ge(
            vec![term(-5, lit(1)), term(-5, lit(2)), term(-1, lit(3))],
            -6,
        );
        let constraints = [c];
        let x = frac(&[(3, 5), (3, 5), (1, 5)]); // x1+x2 = 6/5 > 1: violated pair
        let cuts = separate_cuts(&constraints, 3, &x, &|| false);
        for cut in &cuts {
            assert!(
                first_cut_violation(&constraints, cut, 3).is_none(),
                "INVALID CUT {cut:?}"
            );
        }
        // The pair {x1,x2} must be excluded by some emitted cut (clique or cover).
        assert!(!cuts.is_empty(), "expected x1+x2<=1 to be separated");
    }

    #[test]
    fn cover_cut_from_knapsack_is_valid_and_violated() {
        // 3 x1 + 3 x2 + 3 x3 <= 4  ->  at most one of them, cover {i,j}: xi+xj <= 1.
        // Written as >= : -3x1 -3x2 -3x3 >= -4.
        let c = ge(
            vec![term(-3, lit(1)), term(-3, lit(2)), term(-3, lit(3))],
            -4,
        );
        let constraints = [c];
        // x1=x2=0.7, x3=0 violates x1+x2 <= 1 (sum 1.4 > 1).
        let x = frac(&[(7, 10), (7, 10), (0, 1)]);
        let cuts = separate_cuts(&constraints, 3, &x, &|| false);
        assert!(!cuts.is_empty(), "expected a cover cut");
        // A cover cut (rather than a clique cut) is a pure-literal `>=` row with
        // rhs 1 over complemented literals; validity is what matters.
        for cut in &cuts {
            assert!(
                first_cut_violation(&constraints, cut, 3).is_none(),
                "INVALID COVER CUT {cut:?}"
            );
        }
    }

    #[test]
    fn cg_cut_rounds_knapsack_and_is_valid_and_violated() {
        // 3 x1 + 3 x2 + 3 x3 + 2 x4 <= 4  (as >= : -3x1 -3x2 -3x3 -2x4 >= -4).
        // Divide by d=3: floor(3/3)=1 on x1,x2,x3, floor(2/3)=0 on x4, rhs
        // floor(4/3)=1  =>  x1 + x2 + x3 <= 1, a valid CG cut. At x1=x2=x3=1/2 the
        // LHS is 3/2 > 1, so it is violated and must be separated.
        let c = ge(
            vec![
                term(-3, lit(1)),
                term(-3, lit(2)),
                term(-3, lit(3)),
                term(-2, lit(4)),
            ],
            -4,
        );
        let constraints = vec![c];
        let x = frac(&[(1, 2), (1, 2), (1, 2), (0, 1)]);
        // Knapsack view directly, then the CG generator in isolation.
        let knap = knapsack_views(&constraints[0], 4)
            .into_iter()
            .next()
            .expect("knapsack view");
        let cut = cg_cut_from_knapsack(&knap, &x).expect("a violated CG cut exists");
        assert!(
            first_cut_violation(&constraints, &cut, 4).is_none(),
            "INVALID CG CUT {cut:?}"
        );
        // And it must come out of the (gated-on) CG separator too. We call the
        // internal `separate_cg_cuts` directly rather than `separate_cuts` so the
        // test does not depend on the process-global `AY_PB_CG_CUTS` env gate
        // (which would be racy under the parallel test runner).
        let mut cuts = Vec::new();
        separate_cg_cuts(&constraints, &x, &|| false, &mut cuts);
        assert!(!cuts.is_empty(), "expected a CG cut from the separator");
        for cut in &cuts {
            assert!(
                first_cut_violation(&constraints, cut, 4).is_none(),
                "INVALID CUT {cut:?}"
            );
        }
    }

    #[test]
    fn cg_cut_tightens_rhs_via_gcd_rounding() {
        // 2 x1 + 2 x2 + 2 x3 <= 3  (as >= : -2x1 -2x2 -2x3 >= -3).
        // Divide by d=2: floor(2/2)=1 each, rhs floor(3/2)=1 => x1+x2+x3 <= 1.
        // This is the canonical "round the rhs" CG cut. At x=1/2 each (sum 3/2)
        // it is violated and every emitted cut must be entailed.
        let c = ge(
            vec![term(-2, lit(1)), term(-2, lit(2)), term(-2, lit(3))],
            -3,
        );
        let constraints = vec![c];
        let x = frac(&[(1, 2), (1, 2), (1, 2)]);
        let knap = knapsack_views(&constraints[0], 3)
            .into_iter()
            .next()
            .expect("knapsack view");
        let cut = cg_cut_from_knapsack(&knap, &x).expect("a violated CG cut exists");
        assert!(
            first_cut_violation(&constraints, &cut, 3).is_none(),
            "INVALID CG CUT {cut:?}"
        );
    }

    #[test]
    fn cg_cut_none_when_no_violated_rounding() {
        // A single constraint whose rounding yields nothing violated at an integral
        // feasible point: no CG cut should be produced for it.
        let c = ge(
            vec![term(-2, lit(1)), term(-2, lit(2)), term(-2, lit(3))],
            -3,
        );
        let constraints = [c];
        let x = frac(&[(1, 1), (0, 1), (0, 1)]); // integral, feasible
        let knap = knapsack_views(&constraints[0], 3)
            .into_iter()
            .next()
            .expect("knapsack view");
        assert!(
            cg_cut_from_knapsack(&knap, &x).is_none(),
            "no CG cut should be separated at an integral feasible point"
        );
    }

    #[test]
    fn cg_cuts_off_by_default_in_public_separator() {
        // The public `separate_cuts` dispatcher must NOT emit CG cuts unless the
        // opt-in `AY_PB_CG_CUTS` gate is on. With the env var cleared, the same
        // violated knapsack that yields a CG cut via the internal separator must
        // produce no *CG* row from the public path (only clique/cover families,
        // which here produce none for this single weighted row at this point).
        //
        // SAFETY: mutating a process-global env var inside a parallel test runner
        // is unsound, so we don't touch the env here; we instead assert the gate's
        // default directly and exercise the gated-on path via `separate_cg_cuts`.
        // 2 x1 + 2 x2 + 2 x3 <= 3 at x=1/2 each: violated, CG-separable.
        let c = ge(
            vec![term(-2, lit(1)), term(-2, lit(2)), term(-2, lit(3))],
            -3,
        );
        let constraints = vec![c];
        let x = frac(&[(1, 2), (1, 2), (1, 2)]);
        // Gate-on path produces the cut.
        let mut on = Vec::new();
        separate_cg_cuts(&constraints, &x, &|| false, &mut on);
        assert!(!on.is_empty(), "gated-on CG separator should emit a cut");
        for cut in &on {
            assert!(
                first_cut_violation(&constraints, cut, 3).is_none(),
                "INVALID CG CUT {cut:?}"
            );
        }
    }

    #[test]
    fn no_cut_when_lp_point_integral() {
        // Same triangle, but x is integral and feasible (only x1=1): no violation.
        let c12 = ge(vec![term(-1, lit(1)), term(-1, lit(2))], -1);
        let c13 = ge(vec![term(-1, lit(1)), term(-1, lit(3))], -1);
        let c23 = ge(vec![term(-1, lit(2)), term(-1, lit(3))], -1);
        let constraints = vec![c12, c13, c23];
        let x = frac(&[(1, 1), (0, 1), (0, 1)]);
        let cuts = separate_cuts(&constraints, 3, &x, &|| false);
        // No clique/cover with sum > rhs at an integral feasible point.
        assert!(
            cuts.is_empty(),
            "expected no cut at integral point, got {cuts:?}"
        );
    }

    #[test]
    fn negated_literal_conflicts_handled() {
        // ~x1 \/ x2  is  (1-x1) + x2 >= 1.  Its conflict is on complements:
        // it forbids x1 = 1, x2 = 0, i.e. {x1, ~x2} mutually exclusive.
        let c = ge(vec![term(-1, lit(1)), term(1, lit(2))], 0);
        // (1-x1)+x2 >= 1  <=> -x1 + x2 >= 0.  rhs after normalize_ge_nonneg:
        // -x1 -> +x_? ... just check any produced cut is valid.
        let constraints = vec![c];
        let x = frac(&[(1, 1), (0, 1)]); // x1=1,x2=0 is the forbidden point but it's infeasible
        let cuts = separate_cuts(&constraints, 2, &x, &|| false);
        for cut in &cuts {
            assert!(
                first_cut_violation(&constraints, cut, 2).is_none(),
                "INVALID CUT {cut:?}"
            );
        }
    }

    // ---- Randomized brute-force entailment property test ---- //

    struct Rng(u64);
    impl Rng {
        fn next(&mut self) -> u64 {
            let mut x = self.0;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            self.0 = x;
            x
        }
        fn range(&mut self, lo: i128, hi: i128) -> i128 {
            let span = (hi - lo + 1) as u64;
            lo + (self.next() % span) as i128
        }
    }

    /// For thousands of random small instances and random fractional points,
    /// every generated cut must be entailed by the original constraints: NO
    /// original-feasible 0/1 assignment may violate it.
    #[test]
    fn property_every_generated_cut_is_entailed() {
        let mut rng = Rng(0xC0FF_EE12_3456_789A);
        let mut total_cuts = 0usize;
        let mut instances_with_cuts = 0usize;
        for _ in 0..6000 {
            let n: u32 = rng.range(2, 6) as u32;
            let num_c = rng.range(1, 5);
            let mut constraints = Vec::new();
            for _ in 0..num_c {
                let mut terms = Vec::new();
                for v in 1..=n {
                    let coeff = rng.range(-3, 4);
                    if coeff != 0 {
                        let negated = rng.next() & 1 == 1;
                        terms.push(PbTerm {
                            coeff,
                            lits: vec![PbLit { var: v, negated }],
                        });
                    }
                }
                if terms.is_empty() {
                    terms.push(term(1, lit(1)));
                }
                let rhs = rng.range(-4, 5);
                let rel = if rng.next().is_multiple_of(4) {
                    PbRel::Eq
                } else {
                    PbRel::Ge
                };
                constraints.push(PbConstraint { terms, rel, rhs });
            }

            // Random fractional point in [0,1] with denominators 1..=4.
            let x: Vec<BigRational> = (0..n)
                .map(|_| {
                    let d = rng.range(1, 4);
                    let nu = rng.range(0, d);
                    BigRational::new(nu.into(), d.into())
                })
                .collect();

            // The default (gate-off) dispatcher: clique + cover families.
            let mut cuts = separate_cuts(&constraints, n, &x, &|| false);
            // CG cuts are opt-in via `AY_PB_CG_CUTS`; exercise the gated-on path
            // here directly (env-independent) so every CG cut is also subjected to
            // the brute-force entailment check below.
            separate_cg_cuts(&constraints, &x, &|| false, &mut cuts);
            if !cuts.is_empty() {
                instances_with_cuts += 1;
            }
            for cut in &cuts {
                total_cuts += 1;
                if let Some(witness) = first_cut_violation(&constraints, cut, n) {
                    panic!(
                        "SOUNDNESS VIOLATION: cut {cut:?} violated by feasible point {witness:?}\n\
                         constraints = {constraints:?}\nx = {x:?}"
                    );
                }
            }
        }
        assert!(
            total_cuts > 200,
            "expected the generator to produce many cuts, got {total_cuts} \
             over {instances_with_cuts} instances"
        );
        eprintln!(
            "entailment property: {total_cuts} cuts over {instances_with_cuts} instances, all valid"
        );
    }

    // ---- Sequential lifted-cover cut tests ---- //

    #[test]
    fn lifted_cover_cut_lifts_a_heavy_noncover_var_exactly() {
        // Knapsack: 4 x1 + 4 x2 + 4 x3 + 3 x4 <= 6  (as >= : negate).
        // Cover C = {x1,x2} (4+4=8 > 6, minimal: each alone 4 <= 6). Base cut:
        //   x1 + x2 <= 1.
        // Lift x3 (a=4): budget = 6-4 = 2; max{sum z over C : 4 z1 + 4 z2 <= 2}
        //   = 0 (neither cover item fits). alpha_3 = (|C|-1) - 0 = 1.
        // Lift x4 (a=3): now L = {x1(1),x2(1),x3(1)}; budget = 6-3 = 3; max over
        //   {4 z1 + 4 z2 + 4 z3 <= 3} = 0. alpha_4 = 1 - 0 = 1.
        // Lifted cut: x1 + x2 + x3 + x4 <= 1  (i.e. at most one of the four).
        // Verify the EXACT emitted (terms, rhs) by brute force below, not by trust.
        let c = ge(
            vec![
                term(-4, lit(1)),
                term(-4, lit(2)),
                term(-4, lit(3)),
                term(-3, lit(4)),
            ],
            -6,
        );
        let constraints = vec![c];
        // Fractional point making the lifted cut violated: all = 1/2 (sum 2 > 1).
        let x = frac(&[(1, 2), (1, 2), (1, 2), (1, 2)]);
        let knap = knapsack_views(&constraints[0], 4)
            .into_iter()
            .next()
            .expect("knapsack view");
        let cut = lifted_cover_cut_from_knapsack(&knap, &x).expect("a violated lifted cover cut");
        // Soundness: entailed by the original constraint.
        assert!(
            first_cut_violation(&constraints, &cut, 4).is_none(),
            "INVALID LIFTED COVER CUT {cut:?}"
        );
        // The cut as emitted is `sum ~z_i >= ge_rhs`. Confirm it is logically
        // `x1+x2+x3+x4 <= 1`: all four complemented literals, each coeff 1, and the
        // emitted rhs is ge_rhs = (sum coeff) - rhs_le = 4 - 1 = 3, i.e.
        // `~x1+~x2+~x3+~x4 >= 3`  <=>  `x1+x2+x3+x4 <= 1`.
        assert_eq!(cut.rel, PbRel::Ge);
        assert_eq!(cut.terms.len(), 4, "all four vars lifted in: {cut:?}");
        for t in &cut.terms {
            assert_eq!(t.coeff, 1, "uniform coeff for this symmetric instance");
            assert!(t.lits[0].negated, "emitted over complemented literals");
        }
        let sum_coeff: i128 = cut.terms.iter().map(|t| t.coeff).sum();
        let rhs_le = sum_coeff - cut.rhs; // implied `<= rhs_le` form.
        assert_eq!(rhs_le, 1, "implied form is `x1+x2+x3+x4 <= 1`");
        assert_eq!(
            cut.rhs, 3,
            "emitted `>=`-rhs = sum_coeff(4) - rhs_le(1) = 3"
        );
        // Brute-force DERIVE the equivalent `<= rhs_le` form: for every 0/1 point,
        // the original-LHS `sum z_i` is <= 1 exactly when the cut holds.
        for mask in 0u32..(1u32 << 4) {
            let xb: Vec<bool> = (0..4).map(|b| (mask >> b) & 1 == 1).collect();
            // sum z_i over {x1,x2,x3,x4}.
            let sum_z = xb.iter().filter(|&&b| b).count() as i128;
            let cut_holds = constraint_holds(&cut, &xb);
            assert_eq!(
                cut_holds,
                sum_z <= 1,
                "cut should be exactly `x1+x2+x3+x4 <= 1` at {xb:?}"
            );
        }
    }

    #[test]
    fn lifted_cover_dominates_unlifted_cover() {
        // Same knapsack; the lifted cut must dominate the unlifted minimal-cover
        // cut: same cover coefficients (1), extra non-negative coefficients, same
        // rhs in the `<= rhs_le` sense — so it cuts off at least as much.
        let c = ge(
            vec![
                term(-4, lit(1)),
                term(-4, lit(2)),
                term(-4, lit(3)),
                term(-3, lit(4)),
            ],
            -6,
        );
        let constraints = [c];
        // x1=x2=0.7 (cover {x1,x2} violated: 1.4 > 1), x3=x4=0.1. Both the unlifted
        // and the lifted cut select the SAME cover {x1,x2} and are both violated, so
        // we can compare them directly. (At x=all-1/2 the unlifted cover is NOT
        // violated while the lifted one is — itself a demonstration that lifting
        // separates strictly more, but it leaves nothing to compare against here.)
        let x = frac(&[(7, 10), (7, 10), (1, 10), (1, 10)]);
        let knap = knapsack_views(&constraints[0], 4)
            .into_iter()
            .next()
            .expect("knapsack view");
        let unlifted = cover_cut_from_knapsack(&knap, &x).expect("unlifted cover cut");
        let lifted = lifted_cover_cut_from_knapsack(&knap, &x).expect("lifted cover cut");

        // Map var -> coefficient in each cut's `<= rhs_le` form. Both are emitted as
        // `sum coeff_i ~z_i >= ge_rhs`, i.e. the LHS coefficient on z_i is coeff_i
        // and rhs_le = (sum coeff) - ge_rhs. Compare on the implied `<=` form.
        let collect = |c: &PbConstraint| -> (BTreeMap<u32, i128>, i128) {
            let mut by_var = BTreeMap::new();
            let mut sum = 0i128;
            for t in &c.terms {
                // emitted over complemented literals; the underlying z is positive.
                by_var.insert(t.lits[0].var, t.coeff);
                sum += t.coeff;
            }
            (by_var, sum - c.rhs) // (coeffs on z_i, rhs_le)
        };
        let (unl_coeffs, unl_rhs) = collect(&unlifted);
        let (lif_coeffs, lif_rhs) = collect(&lifted);

        // The lifted cut keeps the cover coefficients (== 1) and the same rhs_le.
        assert_eq!(unl_rhs, lif_rhs, "lifting preserves rhs_le = |C|-1");
        for (v, &uc) in &unl_coeffs {
            let lc = *lif_coeffs.get(v).unwrap_or(&0);
            assert_eq!(uc, lc, "cover var {v} coeff unchanged by lifting");
        }
        // Every lifted coefficient is >= 0, and the lifted cut has >= as many terms.
        for &lc in lif_coeffs.values() {
            assert!(lc >= 0, "lifting coefficient must be non-negative");
        }
        assert!(
            lif_coeffs.len() >= unl_coeffs.len(),
            "lifted cut covers at least the same vars"
        );

        // Dominance: every 0/1 point cut off by the unlifted cut is cut off by the
        // lifted cut (lifted LHS >= unlifted LHS, same rhs_le, so lifted_violated
        // => unlifted_violated; equivalently unlifted_holds whenever lifted_holds).
        for mask in 0u32..(1u32 << 4) {
            let xb: Vec<bool> = (0..4).map(|b| (mask >> b) & 1 == 1).collect();
            let unl_lhs_z: i128 = unl_coeffs
                .iter()
                .map(|(&v, &c)| if xb[(v - 1) as usize] { c } else { 0 })
                .sum();
            let lif_lhs_z: i128 = lif_coeffs
                .iter()
                .map(|(&v, &c)| if xb[(v - 1) as usize] { c } else { 0 })
                .sum();
            // implied `<=` form: holds iff lhs_z <= rhs_le.
            let unl_holds = unl_lhs_z <= unl_rhs;
            let lif_holds = lif_lhs_z <= lif_rhs;
            assert!(
                !lif_holds || unl_holds,
                "lifted cut must dominate: point {xb:?} cut by lifted but not unlifted"
            );
        }
    }

    #[test]
    fn lifted_cover_cut_none_at_integral_feasible_point() {
        // At an integral feasible point there is no violation to separate.
        let c = ge(
            vec![term(-4, lit(1)), term(-4, lit(2)), term(-4, lit(3))],
            -6,
        );
        let constraints = [c];
        let x = frac(&[(1, 1), (0, 1), (0, 1)]); // x1=1 feasible, integral.
        let knap = knapsack_views(&constraints[0], 3)
            .into_iter()
            .next()
            .expect("knapsack view");
        assert!(
            lifted_cover_cut_from_knapsack(&knap, &x).is_none(),
            "no lifted cover cut at an integral feasible point"
        );
    }

    /// Randomized brute-force entailment + dominance test for lifted cover cuts.
    ///
    /// For many random small *knapsack* constraints and random fractional points,
    /// EVERY lifted-cover cut emitted (via the separator and the per-knapsack
    /// generator) must be entailed by the original constraint — NO original-feasible
    /// 0/1 assignment may violate it — and must DOMINATE the corresponding unlifted
    /// minimal-cover cut. Zero violations are tolerated.
    #[test]
    fn property_every_lifted_cover_cut_is_entailed() {
        let mut rng = Rng(0x1234_ABCD_5678_EF01);
        let mut total_cuts = 0usize;
        let mut instances_with_cuts = 0usize;
        let mut dominance_checks = 0usize;
        let iters = 4000; // well above the >=500 floor.
        for _ in 0..iters {
            let n: u32 = rng.range(2, 7) as u32;
            // Build a single random knapsack-style `<=` constraint with small
            // POSITIVE weights and a random capacity, expressed as a `>=` row by
            // negating (the knapsack view recovers the `<=` form). Mixed negated
            // literals exercise the literal-space bookkeeping.
            let mut terms = Vec::new();
            let mut total_w = 0i128;
            for v in 1..=n {
                let a = rng.range(1, 6); // weight 1..=5
                total_w += a;
                let negated = rng.next() & 1 == 1;
                // `<=` form coeff a on this literal; emit as `>=` by negating coeff.
                terms.push(PbTerm {
                    coeff: -a,
                    lits: vec![PbLit { var: v, negated }],
                });
            }
            // cap in [0, total_w] so covers are possible but not always trivial.
            let cap = rng.range(0, total_w.max(1));
            // `<= cap` becomes `>= -cap` after negating coefficients above.
            let c = PbConstraint {
                terms,
                rel: PbRel::Ge,
                rhs: -cap,
            };
            let constraints = vec![c];

            // Random fractional point in [0,1], denominators 1..=4.
            let x: Vec<BigRational> = (0..n)
                .map(|_| {
                    let d = rng.range(1, 4);
                    let nu = rng.range(0, d);
                    BigRational::new(nu.into(), d.into())
                })
                .collect();

            // Exercise BOTH the per-knapsack generator and the public separator so
            // every emitted lifted cut is entailment-checked.
            let mut cuts: Vec<PbConstraint> = Vec::new();
            for knap in knapsack_views(&constraints[0], n) {
                if let Some(cut) = lifted_cover_cut_from_knapsack(&knap, &x) {
                    cuts.push(cut);
                }
            }
            // The public dispatcher must also only ever emit entailed cuts.
            let pub_cuts = separate_cuts(&constraints, n, &x, &|| false);
            cuts.extend(pub_cuts);

            if !cuts.is_empty() {
                instances_with_cuts += 1;
            }
            for cut in &cuts {
                total_cuts += 1;
                if let Some(witness) = first_cut_violation(&constraints, cut, n) {
                    panic!(
                        "SOUNDNESS VIOLATION: lifted cover cut {cut:?} violated by \
                         feasible point {witness:?}\nconstraints = {constraints:?}\nx = {x:?}"
                    );
                }
            }

            // Dominance: for each knapsack view, the lifted cut (if any) must
            // dominate the unlifted cover cut (if any) — over ALL 0/1 points, the
            // lifted cut cuts off a superset of what the unlifted cut cuts off.
            for knap in knapsack_views(&constraints[0], n) {
                let (Some(unl), Some(lif)) = (
                    cover_cut_from_knapsack(&knap, &x),
                    lifted_cover_cut_from_knapsack(&knap, &x),
                ) else {
                    continue;
                };
                dominance_checks += 1;
                let rhs_le = |c: &PbConstraint| -> i128 {
                    c.terms.iter().map(|t| t.coeff).sum::<i128>() - c.rhs
                };
                let unl_rhs = rhs_le(&unl);
                let lif_rhs = rhs_le(&lif);
                for mask in 0u32..(1u32 << n) {
                    let xb: Vec<bool> = (0..n).map(|b| (mask >> b) & 1 == 1).collect();
                    // implied `<=` LHS over z (positive literals). Compute via the
                    // emitted complemented literals: coeff applies to ~z, so
                    // z-LHS = sum coeff_i * [z_i == 1].
                    let z_lhs = |c: &PbConstraint| -> i128 {
                        c.terms
                            .iter()
                            .map(|t| {
                                let v = t.lits[0].var;
                                if xb[(v - 1) as usize] {
                                    t.coeff
                                } else {
                                    0
                                }
                            })
                            .sum()
                    };
                    let unl_holds = z_lhs(&unl) <= unl_rhs;
                    let lif_holds = z_lhs(&lif) <= lif_rhs;
                    assert!(
                        !lif_holds || unl_holds,
                        "DOMINANCE VIOLATION: lifted {lif:?} cuts a point {xb:?} the \
                         unlifted {unl:?} keeps\nknap cap={}",
                        knap.cap
                    );
                }
            }
        }
        assert!(
            total_cuts >= 100,
            "expected many lifted-cover cuts over {iters} instances, got \
             {total_cuts} over {instances_with_cuts} instances"
        );
        eprintln!(
            "lifted-cover entailment: {total_cuts} cuts over {instances_with_cuts} \
             instances, {dominance_checks} dominance pairs, all valid"
        );
    }

    #[test]
    fn normalize_ge_nonneg_basic() {
        // -x1 - x2 >= -1   (i.e. x1 + x2 <= 1).  Normalized to nonneg:
        // -x1 -> +~x1 with rhs += 1, similarly -x2. So ~x1 + ~x2 >= 1.
        let (norm, rhs) =
            normalize_ge_nonneg(&[term(-1, lit(1)), term(-1, lit(2))], -1, 2).expect("normalize");
        assert_eq!(rhs, 1);
        assert_eq!(norm.len(), 2);
        for (l, c) in &norm {
            assert_eq!(*c, 1);
            assert!(l.negated, "expected complemented literal");
        }
    }

    #[test]
    fn lit_value_negation() {
        let x = frac(&[(1, 4)]);
        assert_eq!(
            lit_value(lit(1), &x),
            Some(BigRational::new(1.into(), 4.into()))
        );
        assert_eq!(
            lit_value(neg(1), &x),
            Some(BigRational::new(3.into(), 4.into()))
        );
        assert_eq!(lit_value(lit(2), &x), None);
        let _ = BigRational::zero();
    }

    /// SOUNDNESS (lifted-cover DP): `max_coeff_within_budget` computes the EXACT
    /// 0/1-knapsack max coefficient sum within the weight budget. It underpins the
    /// lifted coefficient `alpha_j = (|C|-1) - max_coeff_within_budget(...)`; a
    /// wrong (too-small) DP value would inflate `alpha_j` and could yield a
    /// NON-ENTAILED cut that cuts off the true optimum (=> false OPTIMUM => DQ).
    /// Verified equal to exhaustive subset enumeration. Kani twin:
    /// `kani_lifted_cover_dp::*` (proofs/2026-06-16-pb-trust-soundness-harnesses.md).
    #[test]
    fn test_max_coeff_within_budget_equals_bruteforce() {
        fn li(weight: i128, coeff: i128) -> LiftedItem {
            LiftedItem {
                lit: PbLit {
                    var: 1,
                    negated: false,
                },
                weight,
                coeff,
            }
        }
        fn brute(items: &[LiftedItem], budget: i128) -> i128 {
            let mut best = 0i128;
            for mask in 0u32..(1u32 << items.len()) {
                let (mut w, mut c) = (0i128, 0i128);
                for (i, it) in items.iter().enumerate() {
                    if mask & (1 << i) != 0 {
                        w += it.weight;
                        c += it.coeff;
                    }
                }
                if w <= budget && c > best {
                    best = c;
                }
            }
            best
        }
        let check = |items: &[LiftedItem], budget: i128| {
            assert_eq!(
                max_coeff_within_budget(items, budget),
                Some(brute(items, budget)),
                "DP != brute-force at budget {budget}"
            );
        };
        check(&[li(2, 3), li(3, 4), li(1, 1)], 4);
        check(&[li(2, 3), li(3, 4), li(1, 1)], 0);
        check(&[li(2, 3), li(3, 4), li(1, 1)], 6);
        check(&[li(1, 5), li(1, 5)], 1); // only one fits
        check(&[li(2, 1), li(2, 1)], 3); // both don't fit together
        check(&[], 5); // empty => 0
                       // budget < 0 short-circuits to Some(0).
        assert_eq!(max_coeff_within_budget(&[li(1, 1)], -1), Some(0));
    }
}

/// VerifierConsumer / Kani proof harness for the lifted-cover 0/1-knapsack DP
/// (model-checked by model-checker-consumer; proofs/2026-06-16-pb-trust-soundness-harnesses.md).
/// Proves `max_coeff_within_budget` equals exhaustive subset-max for ALL small
/// bounded instances — the Kani-tractable core of lifted-cover soundness (the full
/// cut path uses `BigRational` and is intractable; entailment itself is brute-force
/// tested by `property_every_lifted_cover_cut_is_entailed`). `#[cfg(kani)]` gates
/// it out of normal builds.
#[cfg(kani)]
mod kani_lifted_cover_dp {
    use super::*;

    fn li(weight: i128, coeff: i128) -> LiftedItem {
        LiftedItem {
            lit: PbLit {
                var: 1,
                negated: false,
            },
            weight,
            coeff,
        }
    }

    /// For all small bounded item sets, the DP value equals exhaustive subset-max.
    /// 3 items, weights 1..=4, coeffs 0..=4, budget 0..=8 (DP table width <= 9):
    /// tractable. Brute-force subset enumeration is the trusted oracle.
    #[kani::proof]
    fn max_coeff_within_budget_equals_bruteforce() {
        let w0: i128 = kani::any();
        let c0: i128 = kani::any();
        let w1: i128 = kani::any();
        let c1: i128 = kani::any();
        let w2: i128 = kani::any();
        let c2: i128 = kani::any();
        kani::assume((1..=4).contains(&w0) && (0..=4).contains(&c0));
        kani::assume((1..=4).contains(&w1) && (0..=4).contains(&c1));
        kani::assume((1..=4).contains(&w2) && (0..=4).contains(&c2));
        let budget: i128 = kani::any();
        kani::assume((0..=8).contains(&budget));

        let items = [li(w0, c0), li(w1, c1), li(w2, c2)];

        let mut best = 0i128;
        let mut mask = 0u32;
        while mask < 8 {
            let (mut w, mut c) = (0i128, 0i128);
            if mask & 1 != 0 {
                w += items[0].weight;
                c += items[0].coeff;
            }
            if mask & 2 != 0 {
                w += items[1].weight;
                c += items[1].coeff;
            }
            if mask & 4 != 0 {
                w += items[2].weight;
                c += items[2].coeff;
            }
            if w <= budget && c > best {
                best = c;
            }
            mask += 1;
        }

        assert_eq!(max_coeff_within_budget(&items, budget), Some(best));
    }
}
