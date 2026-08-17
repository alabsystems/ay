// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! E+G preprocessing: equivalence-literal merging (sspp `MergeAdjEquivs`)
//! and B+E definability elimination on simplicial variables (sspp
//! `EliminateDefSimplicial`). Spec: `prep-lever-spec.md` (with sspp
//! `preprocessor.cpp` citations).
//!
//! * **E** is equivalence-preserving over the same variable set (the oracle
//!   proves `F ⊨ (y ≡ x)`; rewriting plus linking clauses keeps the model
//!   set 1:1) — valid for all tracks.
//! * **G** is count-preserving but NOT model-preserving: a Padoa-defined
//!   variable has exactly one extension per model of `∃v.F`, so DP
//!   resolution elimination plus a pin unit `{+v}` preserves the count.
//!   Unweighted, unprojected only (a defined var still carries per-model
//!   weights; projection support is future work).
//! * Every oracle verdict used is an UNSAT proof from `ay-sat`
//!   (fail-closed: Unknown/timeout ⇒ no transformation).

use std::time::{Duration, Instant};

use rustc_hash::{FxHashMap, FxHashSet};

/// Result of an E pass.
pub struct EResult {
    /// Rewritten clauses (with linking clauses appended) — logically
    /// equivalent to the input over the same variables.
    pub clauses: Vec<Vec<i32>>,
    /// Number of literal classes merged.
    pub merged: usize,
}

/// Result of a G pass.
pub struct GResult {
    /// Transformed clauses (resolvents + pins).
    pub clauses: Vec<Vec<i32>>,
    /// Variables eliminated (pinned true).
    pub pinned: Vec<i32>,
}

fn to_sat_lit(l: i32) -> ay_sat::Literal {
    let var = ay_sat::Variable::new(l.unsigned_abs() - 1);
    if l > 0 {
        ay_sat::Literal::positive(var)
    } else {
        ay_sat::Literal::negative(var)
    }
}

/// Oracle wrapper: an incremental ay-sat solver over the residual formula
/// with a small model cache for filtering equivalence candidates.
struct Oracle {
    solver: ay_sat::Solver,
    models: Vec<Vec<bool>>,
    deadline: Instant,
    per_call: Duration,
}

impl Oracle {
    fn new(
        num_vars: usize,
        clauses: &[Vec<i32>],
        deadline: Instant,
        per_call: Duration,
    ) -> Option<Self> {
        let mut solver = ay_sat::Solver::new(num_vars);
        for c in clauses {
            if !solver.add_clause(c.iter().map(|&l| to_sat_lit(l)).collect()) {
                return None; // formula unsat at oracle level; caller's BCP handles
            }
        }
        Some(Self {
            solver,
            models: Vec::new(),
            deadline,
            per_call,
        })
    }

    fn over_budget(&self) -> bool {
        Instant::now() >= self.deadline
    }

    /// Solve under assumptions with wall caps. Returns Some(true)=SAT,
    /// Some(false)=UNSAT, None=unknown/budget.
    fn solve(&mut self, assumptions: &[i32]) -> Option<bool> {
        if self.over_budget() {
            return None;
        }
        let call_deadline = (Instant::now() + self.per_call).min(self.deadline);
        let lits: Vec<ay_sat::Literal> = assumptions.iter().map(|&l| to_sat_lit(l)).collect();
        let result = self
            .solver
            .solve_with_assumptions_interruptible(&lits, || Instant::now() >= call_deadline);
        match result.result() {
            ay_sat::AssumeResult::Sat(m) => {
                if self.models.len() < 8 {
                    self.models.push(m.clone());
                }
                Some(true)
            }
            ay_sat::AssumeResult::Unsat(..) => Some(false),
            _ => None,
        }
    }
}

/// E — merge adjacent equivalent literals (sspp preprocessor.cpp:402-475).
///
/// `num_vars` is the DIMACS variable count; only variables occurring in
/// `clauses` are considered.
pub fn merge_adjacent_equivalences(
    num_vars: usize,
    clauses: &[Vec<i32>],
    budget: Duration,
) -> Option<EResult> {
    let deadline = Instant::now() + budget;
    let occurring: FxHashSet<u32> = clauses.iter().flatten().map(|l| l.unsigned_abs()).collect();
    if occurring.len() > 30_000 {
        return None;
    }
    // E1: adjacent pairs.
    let mut pairs: FxHashSet<(u32, u32)> = FxHashSet::default();
    for c in clauses {
        if c.len() > 32 {
            continue;
        }
        for (i, &a) in c.iter().enumerate() {
            for &b in &c[i + 1..] {
                let (x, y) = (a.unsigned_abs(), b.unsigned_abs());
                if x != y {
                    pairs.insert(if x < y { (x, y) } else { (y, x) });
                }
            }
        }
    }
    let mut oracle = Oracle::new(num_vars, clauses, deadline, Duration::from_millis(300))?;
    // Seed the model cache.
    let _ = oracle.solve(&[]);

    // E2: pair tests with model-cache filtering.
    // eq_edges: (lit_a, lit_b) meaning a ≡ b (as literals, sign-aware).
    let mut eq_edges: Vec<(i32, i32)> = Vec::new();
    'pairs: for &(x, y) in &pairs {
        if oracle.over_budget() {
            break;
        }
        // Filter: candidate same-polarity equivalence requires agreement in
        // all cached models; anti-equivalence requires disagreement in all.
        let mut may_eq = true;
        let mut may_anti = true;
        for m in &oracle.models {
            let mx = m.get(x as usize - 1).copied().unwrap_or(false);
            let my = m.get(y as usize - 1).copied().unwrap_or(false);
            if mx != my {
                may_eq = false;
            } else {
                may_anti = false;
            }
            if !may_eq && !may_anti {
                continue 'pairs;
            }
        }
        if may_anti {
            // x ≡ ¬y iff (x∧y) unsat and (¬x∧¬y) unsat.
            match oracle.solve(&[x as i32, y as i32]) {
                Some(false) => {}
                _ => {
                    may_anti = false;
                }
            }
            if may_anti {
                if let Some(false) = oracle.solve(&[-(x as i32), -(y as i32)]) {
                    eq_edges.push((x as i32, -(y as i32)));
                    continue 'pairs;
                }
            }
        }
        if may_eq {
            // x ≡ y iff (x∧¬y) unsat and (¬x∧y) unsat.
            if oracle.solve(&[x as i32, -(y as i32)]) == Some(false)
                && oracle.solve(&[-(x as i32), y as i32]) == Some(false)
            {
                eq_edges.push((x as i32, y as i32));
            }
        }
    }
    if eq_edges.is_empty() {
        return None;
    }

    // E3: literal-class closure with eqc[¬l] = ¬eqc[l]; representative =
    // smallest literal code. Union-find over literal codes.
    let code = |l: i32| -> usize { ((l.unsigned_abs() - 1) * 2 + u32::from(l < 0)) as usize };
    let decode = |c: usize| -> i32 {
        let v = (c / 2) as i32 + 1;
        if c % 2 == 1 {
            -v
        } else {
            v
        }
    };
    let mut parent: Vec<usize> = (0..num_vars * 2).collect();
    fn find(parent: &mut [usize], x: usize) -> usize {
        let mut r = x;
        while parent[r] != r {
            r = parent[r];
        }
        let mut c = x;
        while parent[c] != r {
            let next = parent[c];
            parent[c] = r;
            c = next;
        }
        r
    }
    for &(a, b) in &eq_edges {
        // union a≡b and ¬a≡¬b
        for (p, q) in [(a, b), (-a, -b)] {
            let (rp, rq) = (find(&mut parent, code(p)), find(&mut parent, code(q)));
            if rp != rq {
                // Attach larger to smaller so the smallest code is root.
                if rp < rq {
                    parent[rq] = rp;
                } else {
                    parent[rp] = rq;
                }
            }
        }
    }
    // Sanity: a class must not contain both l and ¬l (would mean UNSAT was
    // provable; bail conservatively).
    for v in 0..num_vars {
        let p = find(&mut parent, v * 2);
        let n = find(&mut parent, v * 2 + 1);
        if p == n {
            return None;
        }
    }

    // E4: rewrite.
    let mut merged = 0usize;
    let mut out: Vec<Vec<i32>> = Vec::with_capacity(clauses.len());
    for c in clauses {
        let mut nc: Vec<i32> = c
            .iter()
            .map(|&l| decode(find(&mut parent, code(l))))
            .collect();
        nc.sort_unstable_by_key(|l| (l.unsigned_abs(), *l < 0));
        nc.dedup();
        let taut = nc
            .windows(2)
            .any(|w| w[0].unsigned_abs() == w[1].unsigned_abs());
        if !taut {
            out.push(nc);
        }
    }
    // E5: linking clauses (keep merged vars determined, not free).
    for v in 1..=num_vars as i32 {
        let rep = decode(find(&mut parent, code(v)));
        if rep != v {
            merged += 1;
            out.push(vec![v, -rep]);
            out.push(vec![-v, rep]);
        }
    }
    if merged == 0 {
        return None;
    }
    Some(EResult {
        clauses: out,
        merged,
    })
}

/// G — definability elimination on simplicial variables
/// (sspp preprocessor.cpp:477-648). Unweighted, unprojected callers only.
pub fn eliminate_defined_simplicial(
    num_vars: usize,
    clauses: &[Vec<i32>],
    budget: Duration,
) -> Option<GResult> {
    let deadline = Instant::now() + budget;
    let mut current: Vec<Vec<i32>> = clauses.to_vec();
    let mut all_pinned: Vec<i32> = Vec::new();

    // G7: waves until fixpoint or budget.
    loop {
        if Instant::now() >= deadline {
            break;
        }
        let occurring: FxHashSet<u32> =
            current.iter().flatten().map(|l| l.unsigned_abs()).collect();
        if occurring.len() > 50_000 {
            break;
        }
        // G1: candidates — simplicial neighborhood + min occurrence ≤ 4.
        let mut pos_occ: FxHashMap<u32, u32> = FxHashMap::default();
        let mut neg_occ: FxHashMap<u32, u32> = FxHashMap::default();
        for c in &current {
            for &a in c.iter() {
                let va = a.unsigned_abs();
                if a > 0 {
                    *pos_occ.entry(va).or_default() += 1;
                } else {
                    *neg_occ.entry(va).or_default() += 1;
                }
            }
        }
        let pinned_set: FxHashSet<u32> = all_pinned.iter().map(|l| l.unsigned_abs()).collect();
        // Candidacy is growth-bounded (arjun-style BVE gate) rather than
        // simplicial (sspp): resolvent count pos*neg must not exceed the
        // removed clause count plus slack. Soundness never depends on the
        // gate — only on the Padoa proof — so a looser gate finds more
        // defined vars (e.g. XOR outputs embedded in larger graphs, which
        // are almost never simplicial).
        let mut candidates: Vec<u32> = occurring
            .iter()
            .copied()
            .filter(|v| {
                if pinned_set.contains(v) {
                    return false; // already eliminated+pinned: re-eliminating
                                  // would churn forever (pin stays a unit)
                }
                let p = pos_occ.get(v).copied().unwrap_or(0);
                let n = neg_occ.get(v).copied().unwrap_or(0);
                p.min(n) <= 6 && p * n <= p + n + 16
            })
            .collect();
        candidates.sort_unstable();
        // Cap the wave size (oracle vars = num_vars + 2k).
        candidates.truncate(512);
        if candidates.is_empty() {
            break;
        }

        // G2: Padoa oracle — shared non-candidates, copies + selectors for
        // candidates.
        let k = candidates.len();
        let copy_var = |i: usize| (num_vars + i) as i32 + 1;
        let sel_var = |i: usize| (num_vars + k + i) as i32 + 1;
        let cand_index: FxHashMap<u32, usize> = candidates
            .iter()
            .enumerate()
            .map(|(i, &v)| (v, i))
            .collect();
        let mut oracle_clauses: Vec<Vec<i32>> = current.clone();
        for c in &current {
            if c.iter().any(|l| cand_index.contains_key(&l.unsigned_abs())) {
                let shadow: Vec<i32> = c
                    .iter()
                    .map(|&l| match cand_index.get(&l.unsigned_abs()) {
                        Some(&i) => {
                            let cv = copy_var(i);
                            if l > 0 {
                                cv
                            } else {
                                -cv
                            }
                        }
                        None => l,
                    })
                    .collect();
                oracle_clauses.push(shadow);
            }
        }
        for (i, &v) in candidates.iter().enumerate() {
            // sel -> (v ≡ copy(v))
            oracle_clauses.push(vec![v as i32, -copy_var(i), -sel_var(i)]);
            oracle_clauses.push(vec![-(v as i32), copy_var(i), -sel_var(i)]);
        }
        let mut oracle = Oracle::new(
            num_vars + 2 * k,
            &oracle_clauses,
            deadline,
            Duration::from_millis(400),
        )?;

        // G3: definability queries with the circularity guard.
        let mut defined = vec![false; k];
        for i in 0..k {
            if oracle.over_budget() {
                break;
            }
            let mut assumptions: Vec<i32> = vec![candidates[i] as i32, -copy_var(i)];
            for (t, &def_t) in defined.iter().enumerate() {
                if t != i && !def_t {
                    assumptions.push(sel_var(t));
                }
            }
            if oracle.solve(&assumptions) == Some(false) {
                defined[i] = true;
            }
        }
        let any_defined = defined.iter().any(|&d| d);
        if !any_defined {
            break;
        }

        // G4+G6: DP-eliminate each defined var, pin it true.
        let mut wave_pinned: Vec<i32> = Vec::new();
        for (i, &v) in candidates.iter().enumerate() {
            if !defined[i] {
                continue;
            }
            let vi = v as i32;
            let mut pos: Vec<Vec<i32>> = Vec::new();
            let mut neg: Vec<Vec<i32>> = Vec::new();
            let mut rest: Vec<Vec<i32>> = Vec::new();
            for c in current.drain(..) {
                if c.contains(&vi) {
                    pos.push(c);
                } else if c.contains(&-vi) {
                    neg.push(c);
                } else {
                    rest.push(c);
                }
            }
            // Resolvent blowup guards: count (candidacy may be stale after
            // earlier same-wave eliminations) and SIZE (resolving two long
            // parents makes primal-graph monsters that poison both the tree
            // decomposition and the search — arjun bounds this too).
            const MAX_RESOLVENT_LEN: usize = 32;
            let mut resolvents: Vec<Vec<i32>> = Vec::new();
            let mut abort = pos.len() * neg.len() > 64 + pos.len() + neg.len();
            if !abort {
                'build: for p in &pos {
                    'resolve: for q in &neg {
                        let mut r: Vec<i32> = p
                            .iter()
                            .chain(q.iter())
                            .copied()
                            .filter(|&l| l != vi && l != -vi)
                            .collect();
                        r.sort_unstable_by_key(|l| (l.unsigned_abs(), *l < 0));
                        r.dedup();
                        for w in r.windows(2) {
                            if w[0].unsigned_abs() == w[1].unsigned_abs() {
                                continue 'resolve; // tautology
                            }
                        }
                        if r.len() > MAX_RESOLVENT_LEN {
                            abort = true;
                            break 'build;
                        }
                        resolvents.push(r);
                    }
                }
            }
            if abort {
                // Undo the partition and skip this var.
                current = rest;
                current.extend(pos);
                current.extend(neg);
                continue;
            }
            rest.extend(resolvents);
            rest.push(vec![vi]); // pin
            wave_pinned.push(vi);
            current = rest;
        }
        if wave_pinned.is_empty() {
            break;
        }
        all_pinned.extend(wave_pinned);
    }

    if all_pinned.is_empty() {
        return None;
    }
    Some(GResult {
        clauses: current,
        pinned: all_pinned,
    })
}

/// Compute a (non-minimal, greedily minimized) independent support: a set
/// `S` of variables such that every variable outside `S` is Padoa-defined by
/// `S` (transitively — the greedy order gives the same layering argument as
/// G: each removed var is defined by the support at its removal time, whose
/// later-removed members are themselves defined by smaller supports).
///
/// For UNWEIGHTED, UNPROJECTED counting, `#F = pmc(F, S)`: every projected
/// model extends uniquely. Callers pass `S` as the projection set so the
/// engine branches only on `S` and resolves the defined remainder with SAT
/// checks.
///
/// Returns `None` when nothing was removed (support = all vars) or on
/// budget/oracle failure.
pub fn independent_support(
    num_vars: usize,
    clauses: &[Vec<i32>],
    budget: Duration,
    min_occurring: usize,
) -> Option<Vec<u32>> {
    let deadline = Instant::now() + budget;
    // Removal candidates: vars of NON-UNIT clauses that are not themselves
    // unit-fixed. Unit-fixed vars are already determined (and would bloat
    // the Padoa oracle by thousands of copies); vars outside the candidate
    // set stay shared between the two copies, which equates them — exactly
    // the "in the support" semantics.
    let mut unit_fixed: FxHashSet<u32> = FxHashSet::default();
    for c in clauses {
        if c.len() == 1 {
            unit_fixed.insert(c[0].unsigned_abs());
        }
    }
    let occurring: FxHashSet<u32> = clauses
        .iter()
        .filter(|c| c.len() > 1)
        .flatten()
        .map(|l| l.unsigned_abs())
        .filter(|v| !unit_fixed.contains(v))
        .collect();
    if occurring.len() < min_occurring {
        // Below the caller's floor: tiny instances solve instantly anyway;
        // skip the oracle cost.
        return None;
    }
    if occurring.is_empty() || occurring.len() > 1_000 {
        // Greedy Padoa costs one oracle call per candidate; past ~1000 the
        // budget dies mid-scan and yields a barely-shrunk support that
        // switches the engine into projected mode for no benefit (observed:
        // 2832-of-3025 support on mc2026_track1_013 = strict regression).
        return None;
    }
    let mut vars: Vec<u32> = occurring.iter().copied().collect();
    vars.sort_unstable();
    let k = vars.len();
    // Padoa oracle over vars + (copy, selector) per occurring var.
    let var_index: FxHashMap<u32, usize> = vars.iter().enumerate().map(|(i, &v)| (v, i)).collect();
    let copy_var = |i: usize| (num_vars + i) as i32 + 1;
    let sel_var = |i: usize| (num_vars + k + i) as i32 + 1;
    let mut oracle_clauses: Vec<Vec<i32>> = clauses.to_vec();
    for c in clauses {
        if !c.iter().any(|l| var_index.contains_key(&l.unsigned_abs())) {
            continue; // no candidate vars: shadow would duplicate the clause
        }
        let shadow: Vec<i32> = c
            .iter()
            .map(|&l| match var_index.get(&l.unsigned_abs()) {
                Some(&i) => {
                    let cv = copy_var(i);
                    if l > 0 {
                        cv
                    } else {
                        -cv
                    }
                }
                None => l,
            })
            .collect();
        oracle_clauses.push(shadow);
    }
    for (i, &v) in vars.iter().enumerate() {
        oracle_clauses.push(vec![v as i32, -copy_var(i), -sel_var(i)]);
        oracle_clauses.push(vec![-(v as i32), copy_var(i), -sel_var(i)]);
    }
    let mut oracle = Oracle::new(
        num_vars + 2 * k,
        &oracle_clauses,
        deadline,
        Duration::from_millis(300),
    )?;
    // Greedy removal: in_support[i] tracks membership.
    let mut in_support = vec![true; k];
    let mut removed = 0usize;
    for i in 0..k {
        if oracle.over_budget() {
            break;
        }
        // Even removing every remaining candidate cannot reach the 50%
        // acceptance floor below: stop paying the oracle — the result
        // would be discarded anyway.
        if (removed + (k - i)) * 2 < k {
            return None;
        }
        // Query: is vars[i] defined by the current support minus itself?
        // Equate (via selectors) every OTHER var still in the support.
        let mut assumptions: Vec<i32> = vec![vars[i] as i32, -copy_var(i)];
        for (t, &in_s) in in_support.iter().enumerate() {
            if t != i && in_s {
                assumptions.push(sel_var(t));
            }
        }
        if oracle.solve(&assumptions) == Some(false) {
            in_support[i] = false;
            removed += 1;
        }
    }
    if std::env::var_os("--count-debug").is_some() {
        eprintln!("c o [debug] indep support: removed {removed} of {k} candidates");
    }
    // Accept only a SUBSTANTIAL support reduction: the one corpus win
    // (track1_009's residual) removes 58.6% of candidates; the observed
    // losses (013: 27.8%; 015) sit below. A near-threshold support flips
    // the engine into projected mode (SAT-checked leaves, branching
    // restricted to the support) for marginal gain — require >= 50%.
    // Strict `<`: the xor-chain unit test sits exactly at 50% and must
    // stay accepted.
    if removed * 2 < k {
        return None;
    }
    // Support = every variable except the removed candidates. Free
    // (non-occurring) vars MUST stay in the support to keep their ×2
    // factors; unit-fixed vars are assigned so their status is moot.
    let removed_set: FxHashSet<u32> = vars
        .iter()
        .zip(&in_support)
        .filter(|(_, &s)| !s)
        .map(|(&v, _)| v)
        .collect();
    let support: Vec<u32> = (1..=num_vars as u32)
        .filter(|v| !removed_set.contains(v))
        .collect();
    Some(support)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::{Engine, EngineConfig};
    use crate::value::WeightTable;
    use num_bigint::BigUint;

    fn count(num_vars: usize, clauses: &[Vec<i32>]) -> BigUint {
        let mut e: Engine<BigUint> = Engine::new(
            num_vars,
            clauses,
            WeightTable::unweighted(),
            None,
            EngineConfig::default(),
        );
        e.count().unwrap()
    }

    const SECS: Duration = Duration::from_secs(10);

    #[test]
    fn independent_support_keeps_free_vars_projected() {
        // x2 ≡ x1 (removable); x3 never occurs (FREE: contributes ×2).
        // Full count = 4. A support that drops x3 would count 2.
        let clauses = vec![vec![1, -2], vec![-1, 2]];
        let before = count(3, &clauses);
        assert_eq!(before, BigUint::from(4u32));
        if let Some(s) = independent_support(3, &clauses, SECS, 0) {
            assert!(s.contains(&3), "free var must stay in the support: {s:?}");
            let mut e: Engine<BigUint> = Engine::new(
                3,
                &clauses,
                WeightTable::unweighted(),
                Some(&s),
                EngineConfig::default(),
            );
            assert_eq!(e.count().unwrap(), before);
        }
    }

    #[test]
    fn independent_support_xor_chain() {
        // x3 = x1 XOR x2; x4 = x3 XOR x1. Support {x1,x2} suffices: count
        // over support = 4 = full count.
        let clauses = vec![
            vec![-3, 1, 2],
            vec![-3, -1, -2],
            vec![3, -1, 2],
            vec![3, 1, -2],
            vec![-4, 3, 1],
            vec![-4, -3, -1],
            vec![4, -3, 1],
            vec![4, 3, -1],
        ];
        let before = count(4, &clauses);
        assert_eq!(before, BigUint::from(4u32));
        let s = independent_support(4, &clauses, SECS, 0).expect("shrinks");
        assert!(s.len() < 4, "support: {s:?}");
        // Count with the support as projection must equal the full count.
        let mut e: Engine<BigUint> = Engine::new(
            4,
            &clauses,
            WeightTable::unweighted(),
            Some(&s),
            EngineConfig::default(),
        );
        assert_eq!(e.count().unwrap(), before);
    }

    #[test]
    fn t1_e_positive_equivalence() {
        let clauses = vec![vec![1, -2], vec![-1, 2], vec![1, 3]];
        let before = count(3, &clauses);
        assert_eq!(before, BigUint::from(3u32));
        let r = merge_adjacent_equivalences(3, &clauses, SECS).expect("merges");
        assert!(r.merged >= 1);
        assert_eq!(count(3, &r.clauses), before);
    }

    #[test]
    fn t2_e_anti_equivalence() {
        let clauses = vec![vec![1, 2], vec![-1, -2], vec![2, 3]];
        let before = count(3, &clauses);
        assert_eq!(before, BigUint::from(3u32));
        let r = merge_adjacent_equivalences(3, &clauses, SECS).expect("merges");
        assert!(r.merged >= 1);
        assert_eq!(count(3, &r.clauses), before);
    }

    #[test]
    fn t3_g_xor_defined_output() {
        // x3 <-> x1 XOR x2. x3 defined; resolvents all tautologies.
        let clauses = vec![
            vec![-3, 1, 2],
            vec![-3, -1, -2],
            vec![3, -1, 2],
            vec![3, 1, -2],
        ];
        let before = count(3, &clauses);
        assert_eq!(before, BigUint::from(4u32));
        let r = eliminate_defined_simplicial(3, &clauses, SECS).expect("eliminates");
        // In an XOR every variable is defined by the others; any single
        // elimination is sound — the count is the invariant that matters.
        assert!(!r.pinned.is_empty(), "pinned: {:?}", r.pinned);
        assert_eq!(count(3, &r.clauses), before);
    }

    #[test]
    fn t4_g_mini_xor_system() {
        // x1^x2^x3=1 and x3^x4^x5=0 over 5 vars: count 2^3 = 8.
        let clauses = vec![
            vec![1, 2, 3],
            vec![1, -2, -3],
            vec![-1, 2, -3],
            vec![-1, -2, 3],
            vec![-3, -4, -5],
            vec![-3, 4, 5],
            vec![3, -4, 5],
            vec![3, 4, -5],
        ];
        let before = count(5, &clauses);
        assert_eq!(before, BigUint::from(8u32));
        let r = eliminate_defined_simplicial(5, &clauses, SECS).expect("eliminates");
        assert!(!r.pinned.is_empty());
        assert_eq!(count(5, &r.clauses), before);
    }

    #[test]
    fn t5_g_circularity_guard() {
        // x1 ≡ x2: both simplicial; a buggy mutual elimination returns 1.
        let clauses = vec![vec![1, -2], vec![-1, 2]];
        let before = count(2, &clauses);
        assert_eq!(before, BigUint::from(2u32));
        if let Some(r) = eliminate_defined_simplicial(2, &clauses, SECS) {
            assert_eq!(
                count(2, &r.clauses),
                before,
                "circularity guard failed: pinned {:?} clauses {:?}",
                r.pinned,
                r.clauses
            );
            assert!(
                r.pinned.len() <= 1,
                "must not eliminate both: {:?}",
                r.pinned
            );
        }
    }

    #[test]
    fn randomized_eg_roundtrip_with_planted_structure() {
        let mut state = 0x5eed5eed5eed5eedu64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for trial in 0..25 {
            let base_vars = 4 + (next() % 5) as usize; // 4..8
            let num_vars = base_vars + 2; // + one equiv var + one xor output
            let mut clauses = Vec::new();
            for _ in 0..(3 + (next() % 12) as usize) {
                let len = 1 + (next() % 3) as usize;
                let mut cl = Vec::new();
                for _ in 0..len {
                    let v = 1 + (next() % base_vars as u64) as i32;
                    cl.push(if next() % 2 == 0 { v } else { -v });
                }
                clauses.push(cl);
            }
            // Plant: var base+1 ≡ var 1; var base+2 = XOR(var 1, var 2).
            let e = (base_vars + 1) as i32;
            let g = (base_vars + 2) as i32;
            clauses.push(vec![e, -1]);
            clauses.push(vec![-e, 1]);
            clauses.push(vec![-g, 1, 2]);
            clauses.push(vec![-g, -1, -2]);
            clauses.push(vec![g, -1, 2]);
            clauses.push(vec![g, 1, -2]);
            let before = count(num_vars, &clauses);
            let mut cur = clauses.clone();
            if let Some(r) = merge_adjacent_equivalences(num_vars, &cur, SECS) {
                cur = r.clauses;
                assert_eq!(count(num_vars, &cur), before, "E broke trial {trial}");
            }
            if let Some(r) = eliminate_defined_simplicial(num_vars, &cur, SECS) {
                cur = r.clauses;
                assert_eq!(count(num_vars, &cur), before, "G broke trial {trial}");
            }
        }
    }
}
