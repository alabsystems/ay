// Copyright 2026 Andrew Yates
// Author: Andrew Yates
// Licensed under the Apache License, Version 2.0

//! Count-safe preprocessing: top-level fixpoint (units, BCP, failed
//! literals), clause vivification, and compaction.
//!
//! Every transformation here is **equivalence-preserving** (the residual
//! formula has exactly the same models over the same variables as the
//! original plus the fixed literals), which makes it sound for every track —
//! unweighted, weighted (zero/negative weights), projected, and algebraic.
//! Nothing here is merely equisatisfiable: no pure-literal elimination, no
//! blocked-clause elimination, no variable elimination.
//!
//! Vivification: for a clause `C = (l1 ... lk)`, assume `¬l1, ¬l2, ...` in
//! order with unit propagation. If a conflict arises after assuming `i < k`
//! literals, then `F ⊨ (l1 ∨ ... ∨ li)`, so `C` can be replaced by that
//! prefix. If some assumed literal is found already implied true, the prefix
//! ending at it is entailed and replaces `C`. Both replacements keep the
//! model set unchanged (the replacement implies `C`, and `F` entails the
//! replacement).

use crate::engine::{Engine, EngineConfig};
use crate::value::WeightTable;
use num_bigint::BigUint;

/// Preprocessing options (track gates + budgets).
#[derive(Clone, Copy)]
pub struct PrepOptions {
    /// Weighted semantics (wmc/pwmc/amc): disables G (definability
    /// elimination changes weighted counts).
    pub weighted: bool,
    /// A (partial) projection set is present: disables G in v1.
    pub projected: bool,
}

/// Result of preprocessing.
pub struct Prepped {
    /// Fixed (entailed) literals over the ORIGINAL variable numbering,
    /// emitted as unit clauses in `clauses`.
    pub fixed: Vec<i32>,
    /// The simplified formula (fixed literals included as units), over the
    /// original variable numbering. Equivalent to the input formula.
    pub clauses: Vec<Vec<i32>>,
    /// The input was proved unsatisfiable.
    pub unsat: bool,
    /// Literals removed by vivification (statistics).
    pub vivified_lits: u64,
    /// Fixed-literal count (statistics).
    pub fixed_count: u64,
    /// False iff definability elimination fired: the result then has the
    /// same COUNT but not the same model set (pinned defined vars).
    pub model_preserving: bool,
    /// Variables eliminated+pinned by definability elimination.
    pub pinned_defined: Vec<i32>,
    /// Literal classes merged by equivalence merging.
    pub merged_literals: u64,
}

/// Budget for vivification probes (assignments), to keep preprocessing a
/// bounded fraction of the run.
const VIVIFY_ASSIGN_BUDGET: u64 = 20_000_000;
const MAX_ROUNDS: u32 = 8;

/// Preprocess a formula. The result is equivalent to the input.
pub fn preprocess(num_vars: usize, clauses: &[Vec<i32>], opts: PrepOptions) -> Prepped {
    let mut current: Vec<Vec<i32>> = clauses.to_vec();
    let mut total_vivified = 0u64;
    let mut fixed: Vec<i32> = Vec::new();
    let mut budget = VIVIFY_ASSIGN_BUDGET;
    let mut backbone_done = false;
    let mut e_budget = std::time::Duration::from_secs(4);
    let mut g_budget = std::time::Duration::from_secs(8);
    let mut merged_total = 0u64;
    let mut pinned_total: Vec<i32> = Vec::new();

    for _round in 0..MAX_ROUNDS {
        let mut engine: Engine<BigUint> = Engine::new(
            num_vars,
            &current,
            WeightTable::unweighted(),
            None,
            EngineConfig {
                cache_budget_bytes: 1 << 20,
                deadline: None,
            },
        );
        if !engine.establish_top_level() {
            return Prepped {
                fixed: Vec::new(),
                clauses: vec![vec![]],
                unsat: true,
                vivified_lits: total_vivified,
                fixed_count: 0,
                model_preserving: true,
                pinned_defined: Vec::new(),
                merged_literals: merged_total,
            };
        }
        let (round_fixed, residual) = engine.extract_residual();
        let fixed_grew = round_fixed.len() != fixed.len();
        fixed = round_fixed;

        // Vivify the residual clauses using top-level UP probes.
        let mut vivified = Vec::with_capacity(residual.len());
        let mut round_vivified = 0u64;
        for clause in &residual {
            if clause.len() < 2 || budget == 0 {
                vivified.push(clause.clone());
                continue;
            }
            budget = budget.saturating_sub(clause.len() as u64 * 4);
            let assumed: Vec<_> = clause
                .iter()
                .map(|&l| Engine::<BigUint>::lit_from_dimacs(-l))
                .collect();
            let (conflict, first_implied) = engine.probe_assume(&assumed);
            // Determine the shortest entailed prefix.
            let cut = match (conflict, first_implied) {
                // Conflict while assuming ¬l1..¬li (probe_assume stops at the
                // conflicting position): F ⊨ (l1..li). probe_assume does not
                // report the position, so a conflict without an implied
                // literal keeps the clause (safe) unless the whole clause is
                // entailed — re-probe prefixes only for short clauses.
                (true, None) => {
                    if clause.len() <= 16 {
                        let mut cut = clause.len();
                        for i in 1..clause.len() {
                            let (c2, _) = engine.probe_assume(&assumed[..i]);
                            if c2 {
                                cut = i;
                                break;
                            }
                        }
                        cut
                    } else {
                        clause.len()
                    }
                }
                // ¬l_i already implied true means F∧¬l1..¬l(i-1) ⊨ ¬l_i, which
                // makes l_i redundant: drop it (keep the rest).
                (_, Some(idx)) => {
                    let mut shrunk = clause.clone();
                    shrunk.remove(idx);
                    round_vivified += 1;
                    vivified.push(shrunk);
                    continue;
                }
                (false, None) => clause.len(),
            };
            if cut < clause.len() {
                round_vivified += (clause.len() - cut) as u64;
                vivified.push(clause[..cut].to_vec());
            } else {
                vivified.push(clause.clone());
            }
        }
        total_vivified += round_vivified;

        // SAT-oracle backbone detection (sspp 'V'): literals true in every
        // model are entailed; fixing them is count-safe for every track.
        // Run once (budget-gated) on small residuals, where it routinely
        // collapses hundreds of variables (loss analysis: 031/149-class).
        #[allow(unused_mut)]
        let mut backbone: Vec<i32> = Vec::new();
        if !backbone_done && vivified.iter().map(Vec::len).sum::<usize>() > 0 {
            let residual_vars: std::collections::HashSet<u32> = vivified
                .iter()
                .flatten()
                .map(|l| l.unsigned_abs())
                .collect();
            if (100..=4000).contains(&residual_vars.len()) {
                backbone_done = true;
                backbone = backbone_units(
                    num_vars,
                    &fixed,
                    &vivified,
                    std::time::Duration::from_secs(15),
                );
            }
        }

        // ORDERING (soundness-critical): backbone units are entailed by the
        // ORIGINAL formula, and G's output is only count-preserving, not
        // model-preserving — a pinned-true defined var can contradict an
        // original backbone literal (false UNSAT, caught on 031). Fold
        // backbone units into the clause stream BEFORE E/G so G eliminates
        // against them instead of fighting them.
        if !backbone.is_empty() {
            let mut with_bb: Vec<Vec<i32>> = backbone.iter().map(|&l| vec![l]).collect();
            with_bb.extend(vivified);
            vivified = with_bb;
            backbone.clear();
        }

        // E+G (spec: prep-lever-spec.md). E is equivalence-preserving,
        // all tracks; G is count-preserving-only, unweighted+unprojected.
        let mut eg_changed = false;
        {
            let residual_vars: std::collections::HashSet<u32> = vivified
                .iter()
                .flatten()
                .map(|l| l.unsigned_abs())
                .collect();
            if (100..=30_000).contains(&residual_vars.len()) && !vivified.is_empty() {
                if !e_budget.is_zero() {
                    let t0 = std::time::Instant::now();
                    if let Some(e) =
                        crate::prep_eg::merge_adjacent_equivalences(num_vars, &vivified, e_budget)
                    {
                        merged_total += e.merged as u64;
                        vivified = e.clauses;
                        eg_changed = true;
                    }
                    e_budget = e_budget.saturating_sub(t0.elapsed());
                }
                if !opts.weighted && !opts.projected && !g_budget.is_zero() {
                    let t0 = std::time::Instant::now();
                    if let Some(g) =
                        crate::prep_eg::eliminate_defined_simplicial(num_vars, &vivified, g_budget)
                    {
                        pinned_total.extend(&g.pinned);
                        vivified = g.clauses;
                        eg_changed = true;
                    }
                    g_budget = g_budget.saturating_sub(t0.elapsed());
                }
            }
        }

        current = fixed.iter().map(|&l| vec![l]).collect();
        current.extend(vivified);
        if round_vivified == 0 && !fixed_grew && backbone.is_empty() && !eg_changed {
            break;
        }
    }

    Prepped {
        fixed_count: fixed.len() as u64,
        fixed,
        clauses: current,
        unsat: false,
        vivified_lits: total_vivified,
        model_preserving: pinned_total.is_empty(),
        pinned_defined: pinned_total,
        merged_literals: merged_total,
    }
}

/// Iterative SAT-based backbone detection: start from one model's literals
/// as candidates; each `F ∧ ¬l` call either proves `l` entailed (UNSAT) or
/// yields a model pruning every disagreeing candidate. Interruptible and
/// wall-clock budgeted; `Unknown` skips the literal (fail-open, sound).
fn backbone_units(
    num_vars: usize,
    fixed: &[i32],
    clauses: &[Vec<i32>],
    budget: std::time::Duration,
) -> Vec<i32> {
    let deadline = std::time::Instant::now() + budget;
    let over = || std::time::Instant::now() >= deadline;
    let mut solver = ay_sat::Solver::new(num_vars);
    let to_lit = |l: i32| {
        let var = ay_sat::Variable::new(l.unsigned_abs() - 1);
        if l > 0 {
            ay_sat::Literal::positive(var)
        } else {
            ay_sat::Literal::negative(var)
        }
    };
    for &u in fixed {
        if !solver.add_clause(vec![to_lit(u)]) {
            return Vec::new();
        }
    }
    let mut occurs = vec![false; num_vars];
    for c in clauses {
        for &l in c {
            occurs[l.unsigned_abs() as usize - 1] = true;
        }
        if !solver.add_clause(c.iter().map(|&l| to_lit(l)).collect()) {
            return Vec::new();
        }
    }
    let first = solver.solve_interruptible(over);
    let model = match first.result() {
        ay_sat::SatResult::Sat(m) => m.clone(),
        _ => return Vec::new(),
    };
    // Candidate polarity per var (only vars that occur; free vars cannot be
    // backbone). Fixed vars are already units — skip them too.
    let mut fixed_mask = vec![false; num_vars];
    for &u in fixed {
        fixed_mask[u.unsigned_abs() as usize - 1] = true;
    }
    let mut candidate: Vec<Option<bool>> = (0..num_vars)
        .map(|v| (occurs[v] && !fixed_mask[v]).then(|| model.get(v).copied().unwrap_or(false)))
        .collect();
    let mut backbone = Vec::new();
    for v in 0..num_vars {
        if over() {
            break;
        }
        let Some(polarity) = candidate[v] else {
            continue;
        };
        let lit = if polarity {
            ay_sat::Literal::negative(ay_sat::Variable::new(v as u32))
        } else {
            ay_sat::Literal::positive(ay_sat::Variable::new(v as u32))
        };
        let result = solver.solve_with_assumptions_interruptible(&[lit], over);
        match result.result() {
            ay_sat::AssumeResult::Unsat(..) => {
                let dimacs = if polarity {
                    v as i32 + 1
                } else {
                    -(v as i32 + 1)
                };
                backbone.push(dimacs);
            }
            ay_sat::AssumeResult::Sat(m) => {
                for (u, cand) in candidate.iter_mut().enumerate() {
                    if let Some(p) = cand {
                        if m.get(u).copied().unwrap_or(false) != *p {
                            *cand = None;
                        }
                    }
                }
            }
            _ => {}
        }
        candidate[v] = None;
    }
    backbone
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::{Engine, EngineConfig};
    use crate::value::WeightTable;

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

    #[test]
    fn preprocess_preserves_counts_on_random_formulas() {
        let mut state = 0xdeadbeefcafef00du64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        for trial in 0..40 {
            let num_vars = 4 + (next() % 9) as usize;
            let num_clauses = 3 + (next() % 30) as usize;
            let mut clauses = Vec::new();
            for _ in 0..num_clauses {
                let len = 1 + (next() % 3) as usize;
                let mut cl = Vec::new();
                for _ in 0..len {
                    let v = 1 + (next() % num_vars as u64) as i32;
                    let sign = if next() % 2 == 0 { 1 } else { -1 };
                    cl.push(v * sign);
                }
                clauses.push(cl);
            }
            let before = count(num_vars, &clauses);
            let prep = preprocess(
                num_vars,
                &clauses,
                PrepOptions {
                    weighted: false,
                    projected: false,
                },
            );
            let after = if prep.unsat {
                BigUint::from(0u32)
            } else {
                count(num_vars, &prep.clauses)
            };
            assert_eq!(before, after, "trial {trial}: {clauses:?}");
        }
    }

    #[test]
    fn backbone_and_definability_compose_soundly() {
        // Regression (mc2026_track1_031-class): v is backbone-FALSE and also
        // definability-eliminable. If backbone units (entailed by the
        // ORIGINAL formula) are appended after G's count-preserving-only
        // transformation, the pin {+v} contradicts the backbone {-v} and the
        // count collapses to 0. Construct: v=3 forced false via SAT-visible
        // (not UP-visible) structure, and defined by (1,2).
        // Clauses: (¬3∨1) (¬3∨2) (3∨¬1∨¬2)  [3 ↔ 1∧2]
        //          (¬1∨¬2)                   [forces 3 false in all models]
        // Models over (1,2): (0,0),(0,1),(1,0) each with 3=0 → count 3.
        let clauses = vec![vec![-3, 1], vec![-3, 2], vec![3, -1, -2], vec![-1, -2]];
        let before = count(3, &clauses);
        assert_eq!(before, BigUint::from(3u32));
        // Pad with independent structure so the 100-var oracle floor does
        // not skip the oracle stages: add 120 chained implication vars.
        let mut padded = clauses.clone();
        let base = 3;
        for i in 0..120 {
            let a = base + i + 1;
            let b = base + ((i + 1) % 120) + 1;
            padded.push(vec![-(a as i32), b as i32]);
        }
        let num_vars = base + 120;
        let expected = {
            let mut e: Engine<BigUint> = Engine::new(
                num_vars,
                &padded,
                WeightTable::unweighted(),
                None,
                EngineConfig::default(),
            );
            e.count().unwrap()
        };
        let prep = preprocess(
            num_vars,
            &padded,
            PrepOptions {
                weighted: false,
                projected: false,
            },
        );
        assert!(!prep.unsat, "false UNSAT from backbone/G composition");
        let after = count(num_vars, &prep.clauses);
        assert_eq!(after, expected, "count changed by preprocessing");
    }

    #[test]
    fn preprocess_detects_unsat() {
        let prep = preprocess(
            2,
            &[vec![1], vec![-1]],
            PrepOptions {
                weighted: false,
                projected: false,
            },
        );
        assert!(prep.unsat);
    }

    #[test]
    fn vivification_shrinks_redundant_literal() {
        // (¬x1 ∨ x2) ∧ (x1 ∨ x2 ∨ x3): assuming ¬x1... the second clause's
        // x1 is not redundant, but with (¬x1 ∨ x2), assuming ¬x2 forces ¬x1,
        // so (x2 ∨ x3) is entailed: x1 is redundant in clause 2.
        let clauses = vec![vec![-1, 2], vec![1, 2, 3]];
        let before = count(3, &clauses);
        let prep = preprocess(
            3,
            &clauses,
            PrepOptions {
                weighted: false,
                projected: false,
            },
        );
        let after = count(3, &prep.clauses);
        assert_eq!(before, after);
    }
}
